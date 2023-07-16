use std::{any::Any, convert::TryFrom, fmt::Display};

use crate::{
    protocol::TLSProtocolBehavior,
    tls::rustls::{
        error::Error,
        hash_hs::HandshakeHash,
        key::Certificate,
        msgs::{
            alert::AlertMessagePayload,
            base::Payload,
            ccs::ChangeCipherSpecPayload,
            enums::{AlertDescription, AlertLevel, ContentType, HandshakeType, ProtocolVersion},
            handshake::HandshakeMessagePayload,
            heartbeat::HeartbeatPayload,
        },
    },
};
use puffin::{
    codec::{encode_vec_u8, encode_vec_vec_u8, Codec, Reader},
    protocol::AnyProtocolMessage,
    variable_data::VariableData,
};
use serde::{Deserialize, Serialize};

use super::{
    enums::{CipherSuite, Compression, NamedGroup, SignatureScheme},
    handshake::{
        CertReqExtension, CertificateEntry, CertificateExtension, ClientExtension,
        HelloRetryExtension, NewSessionTicketExtension, OCSPCertificateStatusRequest,
        PresharedKeyIdentity, Random, ServerExtension, SessionID,
    },
};

#[derive(Debug, Clone)]
pub enum MessagePayload {
    Alert(AlertMessagePayload),
    Handshake(HandshakeMessagePayload),
    // this type is for TLS 1.2 encrypted handshake messages
    TLS12EncryptedHandshake(Payload),
    ChangeCipherSpec(ChangeCipherSpecPayload),
    ApplicationData(Payload),
    Heartbeat(HeartbeatPayload),
}

impl MessagePayload {
    pub fn encode(&self, bytes: &mut Vec<u8>) {
        match *self {
            Self::Alert(ref x) => x.encode(bytes),
            Self::Handshake(ref x) => x.encode(bytes),
            Self::TLS12EncryptedHandshake(ref x) => x.encode(bytes),
            Self::ChangeCipherSpec(ref x) => x.encode(bytes),
            Self::ApplicationData(ref x) => x.encode(bytes),
            Self::Heartbeat(ref x) => x.encode(bytes),
        }
    }

    pub fn new(typ: ContentType, vers: ProtocolVersion, payload: Payload) -> Result<Self, Error> {
        let fallback_payload = payload.clone();
        let mut r = Reader::init(&payload.0);
        let parsed = match typ {
            ContentType::ApplicationData => return Ok(Self::ApplicationData(payload)),
            ContentType::Alert => AlertMessagePayload::read(&mut r).map(MessagePayload::Alert),
            ContentType::Handshake => {
                HandshakeMessagePayload::read_version(&mut r, vers)
                    .map(MessagePayload::Handshake)
                    // this type is for TLS 1.2 encrypted handshake messages
                    .or(Some(MessagePayload::TLS12EncryptedHandshake(
                        fallback_payload,
                    )))
            }
            ContentType::ChangeCipherSpec => {
                ChangeCipherSpecPayload::read(&mut r).map(MessagePayload::ChangeCipherSpec)
            }
            ContentType::Heartbeat => HeartbeatPayload::read(&mut r).map(MessagePayload::Heartbeat),
            _ => None,
        };

        parsed.ok_or(Error::corrupt_message(typ))
        /*        parsed
        .filter(|_| !r.any_left())
        .ok_or_else(|| Error::corrupt_message(typ))*/
    }

    pub fn content_type(&self) -> ContentType {
        match self {
            Self::Alert(_) => ContentType::Alert,
            Self::Handshake(_) => ContentType::Handshake,
            Self::TLS12EncryptedHandshake(_) => ContentType::Handshake,
            Self::ChangeCipherSpec(_) => ContentType::ChangeCipherSpec,
            Self::ApplicationData(_) => ContentType::ApplicationData,
            Self::Heartbeat(_) => ContentType::Heartbeat,
        }
    }
}

/// A TLS frame, named TLSPlaintext in the standard.
///
/// This type owns all memory for its interior parts. It is used to read/write from/to I/O
/// buffers as well as for fragmenting, joining and encryption/decryption. It can be converted
/// into a `Message` by decoding the payload.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Hash, Eq)]
pub struct OpaqueMessage {
    pub typ: ContentType,
    pub version: ProtocolVersion,
    pub payload: Payload,
}

impl Display for OpaqueMessage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "opaque message : {:?}", self.typ)
    }
}

impl Codec for OpaqueMessage {
    fn encode(&self, bytes: &mut Vec<u8>) {
        bytes.extend_from_slice(&OpaqueMessage::encode(self.clone()));
    }

    fn read(reader: &mut Reader) -> Option<Self> {
        Self::read(reader).ok()
    }
}

impl OpaqueMessage {
    /// `MessageError` allows callers to distinguish between valid prefixes (might
    /// become valid if we read more data) and invalid data.
    pub fn read(r: &mut Reader) -> Result<Self, MessageError> {
        let typ = ContentType::read(r).ok_or(MessageError::TooShortForHeader)?;
        let version = ProtocolVersion::read(r).ok_or(MessageError::TooShortForHeader)?;
        let len = u16::read(r).ok_or(MessageError::TooShortForHeader)?;

        // Reject undersize messages
        //  implemented per section 5.1 of RFC8446 (TLSv1.3)
        //              per section 6.2.1 of RFC5246 (TLSv1.2)
        if typ != ContentType::ApplicationData && len == 0 {
            return Err(MessageError::IllegalLength);
        }

        // Reject oversize messages
        if len >= Self::MAX_PAYLOAD {
            return Err(MessageError::IllegalLength);
        }

        // Don't accept any new content-types.
        if let ContentType::Unknown(_) = typ {
            return Err(MessageError::IllegalContentType);
        }

        // Accept only versions 0x03XX for any XX.
        match version {
            ProtocolVersion::Unknown(ref v) if (v & 0xff00) != 0x0300 => {
                return Err(MessageError::IllegalProtocolVersion);
            }
            _ => {}
        };

        let mut sub = r.sub(len as usize).ok_or(MessageError::TooShortForLength)?;
        let payload = Payload::read(&mut sub);

        Ok(Self {
            typ,
            version,
            payload,
        })
    }

    pub fn encode(self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.typ.encode(&mut buf);
        self.version.encode(&mut buf);
        (self.payload.0.len() as u16).encode(&mut buf);
        self.payload.encode(&mut buf);
        buf
    }

    /// Force conversion into a plaintext message.
    ///
    /// This should only be used for messages that are known to be in plaintext. Otherwise, the
    /// `OpaqueMessage` should be decrypted into a `PlainMessage` using a `MessageDecrypter`.
    pub fn into_plain_message(self) -> PlainMessage {
        PlainMessage {
            version: self.version,
            typ: self.typ,
            payload: self.payload,
        }
    }

    /// This is the maximum on-the-wire size of a TLSCiphertext.
    /// That's 2^14 payload bytes, a header, and a 2KB allowance
    /// for ciphertext overheads.
    const MAX_PAYLOAD: u16 = 16384 + 2048;

    /// Content type, version and size.
    const HEADER_SIZE: u16 = 1 + 2 + 2;

    /// Maximum on-wire message size.
    pub const MAX_WIRE_SIZE: usize = (Self::MAX_PAYLOAD + Self::HEADER_SIZE) as usize;
}

impl From<Message> for PlainMessage {
    fn from(msg: Message) -> Self {
        let typ = msg.payload.content_type();
        let payload = match msg.payload {
            MessagePayload::ApplicationData(payload) => payload,
            _ => {
                let mut buf = Vec::new();
                msg.payload.encode(&mut buf);
                Payload(buf)
            }
        };

        Self {
            typ,
            version: msg.version,
            payload,
        }
    }
}

/// A decrypted TLS frame
///
/// This type owns all memory for its interior parts. It can be decrypted from an OpaqueMessage
/// or encrypted into an OpaqueMessage, and it is also used for joining and fragmenting.
#[derive(Clone, Debug)]
pub struct PlainMessage {
    pub typ: ContentType,
    pub version: ProtocolVersion,
    pub payload: Payload,
}

impl PlainMessage {
    pub fn into_unencrypted_opaque(self) -> OpaqueMessage {
        OpaqueMessage {
            version: self.version,
            typ: self.typ,
            payload: self.payload,
        }
    }

    pub fn borrow(&self) -> BorrowedPlainMessage<'_> {
        BorrowedPlainMessage {
            version: self.version,
            typ: self.typ,
            payload: &self.payload.0,
        }
    }
}

/// A message with decoded payload
#[derive(Debug, Clone)]
pub struct Message {
    pub version: ProtocolVersion,
    pub payload: MessagePayload,
}

impl Codec for Message {
    fn encode(&self, bytes: &mut Vec<u8>) {
        self.payload.encode(bytes);
    }

    fn read(reader: &mut Reader) -> Option<Self> {
        Self::read(reader)
    }
}

impl Message {
    pub fn is_handshake_type(&self, hstyp: HandshakeType) -> bool {
        // Bit of a layering violation, but OK.
        if let MessagePayload::Handshake(ref hsp) = self.payload {
            hsp.typ == hstyp
        } else {
            false
        }
    }

    pub fn build_alert(level: AlertLevel, desc: AlertDescription) -> Self {
        Self {
            version: ProtocolVersion::TLSv1_2,
            payload: MessagePayload::Alert(AlertMessagePayload {
                level,
                description: desc,
            }),
        }
    }

    pub fn build_key_update_notify() -> Self {
        Self {
            version: ProtocolVersion::TLSv1_3,
            payload: MessagePayload::Handshake(HandshakeMessagePayload::build_key_update_notify()),
        }
    }
}

/// Parses a plaintext message into a well-typed [`Message`].
///
/// A [`PlainMessage`] must contain plaintext content. Encrypted content should be stored in an
/// [`OpaqueMessage`] and decrypted before being stored into a [`PlainMessage`].
impl TryFrom<PlainMessage> for Message {
    type Error = Error;

    fn try_from(plain: PlainMessage) -> Result<Self, Self::Error> {
        Ok(Self {
            version: plain.version,
            payload: MessagePayload::new(plain.typ, plain.version, plain.payload)?,
        })
    }
}

impl TryFrom<OpaqueMessage> for Message {
    type Error = Error;

    fn try_from(value: OpaqueMessage) -> Result<Self, Self::Error> {
        Message::try_from(value.into_plain_message())
    }
}

/// A TLS frame, named TLSPlaintext in the standard.
///
/// This type differs from `OpaqueMessage` because it borrows
/// its payload.  You can make a `OpaqueMessage` from an
/// `BorrowMessage`, but this involves a copy.
///
/// This type also cannot decode its internals and
/// cannot be read/encoded; only `OpaqueMessage` can do that.
pub struct BorrowedPlainMessage<'a> {
    pub typ: ContentType,
    pub version: ProtocolVersion,
    pub payload: &'a [u8],
}

#[derive(Debug)]
pub enum MessageError {
    TooShortForHeader,
    TooShortForLength,
    IllegalLength,
    IllegalContentType,
    IllegalProtocolVersion,
}

#[derive(Debug, Clone)]
pub enum AnyMessage {
    Message(Message),
    OpaqueMessage(OpaqueMessage),

    Bitstring(Vec<u8>),
    Bitstringstring(Vec<Vec<u8>>),
    Constant64(u64),

    CertificateEntry(CertificateEntry),
    VecCertificateEntry(Vec<CertificateEntry>),
    ClientExtension(ClientExtension),
    VecClientExtension(Vec<ClientExtension>),
    ServerExtension(ServerExtension),
    VecServerExtension(Vec<ServerExtension>),
    HelloRetryExtension(HelloRetryExtension),
    VecHelloRetryExtension(Vec<HelloRetryExtension>),
    CertReqExtension(CertReqExtension),
    VecCertReqExtension(Vec<CertReqExtension>),
    CertificateExtension(CertificateExtension),
    VecCertificateExtension(Vec<CertificateExtension>),
    NewSessionTicketExtension(NewSessionTicketExtension),
    VecNewSessionTicketExtension(Vec<NewSessionTicketExtension>),
    PresharedKey(PresharedKeyIdentity),
    VecPresharedKey(Vec<PresharedKeyIdentity>),
    CipherSuite(CipherSuite),
    VecCipherSuite(Vec<CipherSuite>),
    Certificate(Certificate),
    VecCertificate(Vec<Certificate>),
    Compression(Compression),
    VecCompression(Vec<Compression>),

    SignatureScheme(SignatureScheme),
    OCSPCertificateStatusRequest(OCSPCertificateStatusRequest),
    NamedGroup(NamedGroup),
    ProtocolVersion(ProtocolVersion),
    SessionID(SessionID),
    Random(Random),
}

impl Codec for AnyMessage {
    fn encode(&self, bytes: &mut Vec<u8>) {
        match self {
            AnyMessage::Message(msg) => msg.encode(bytes),
            AnyMessage::OpaqueMessage(msg) => msg.encode(bytes),

            AnyMessage::Bitstring(v) => bytes.extend_from_slice(v),
            AnyMessage::Bitstringstring(vv) => encode_vec_vec_u8(bytes, vv),
            AnyMessage::Constant64(n) => n.encode(bytes),

            AnyMessage::CertificateEntry(ce) => ce.encode(bytes),
            AnyMessage::VecCertificateEntry(vce) => encode_vec_u8(bytes, &vce),

            AnyMessage::ClientExtension(ce) => ce.encode(bytes),
            AnyMessage::VecClientExtension(vce) => encode_vec_u8(bytes, &vce),

            AnyMessage::ServerExtension(se) => se.encode(bytes),
            AnyMessage::VecServerExtension(vse) => encode_vec_u8(bytes, &vse),

            AnyMessage::HelloRetryExtension(re) => re.encode(bytes),
            AnyMessage::VecHelloRetryExtension(vre) => encode_vec_u8(bytes, &vre),

            AnyMessage::CertReqExtension(cre) => cre.encode(bytes),
            AnyMessage::VecCertReqExtension(vcre) => encode_vec_u8(bytes, &vcre),

            AnyMessage::CertificateExtension(ce) => ce.encode(bytes),
            AnyMessage::VecCertificateExtension(vce) => encode_vec_u8(bytes, &vce),

            AnyMessage::NewSessionTicketExtension(nste) => nste.encode(bytes),
            AnyMessage::VecNewSessionTicketExtension(vnste) => encode_vec_u8(bytes, &vnste),

            AnyMessage::PresharedKey(psk) => psk.encode(bytes),
            AnyMessage::VecPresharedKey(vpsk) => encode_vec_u8(bytes, &vpsk),

            AnyMessage::CipherSuite(cs) => cs.encode(bytes),
            AnyMessage::VecCipherSuite(vcs) => encode_vec_u8(bytes, &vcs),

            AnyMessage::Certificate(c) => c.encode(bytes),
            AnyMessage::VecCertificate(vc) => encode_vec_u8(bytes, &vc),

            AnyMessage::Compression(c) => c.encode(bytes),
            AnyMessage::VecCompression(vc) => encode_vec_u8(bytes, &vc),

            AnyMessage::SignatureScheme(sc) => sc.encode(bytes),
            AnyMessage::OCSPCertificateStatusRequest(ocsp) => ocsp.encode(bytes),
            AnyMessage::NamedGroup(ng) => ng.encode(bytes),
            AnyMessage::ProtocolVersion(pv) => pv.encode(bytes),
            AnyMessage::SessionID(id) => id.encode(bytes),
            AnyMessage::Random(r) => r.encode(bytes),
        }
    }

    fn read(_: &mut Reader) -> Option<Self> {
        panic!("not needed")
    }
}

impl AnyProtocolMessage for AnyMessage {
    fn downcast(boxed: Box<dyn std::any::Any>) -> Option<Self> {
        if let Some(message) = boxed.as_ref().downcast_ref::<Message>() {
            Some(AnyMessage::Message(message.clone()))
        } else if let Some(opaque_message) = boxed.as_ref().downcast_ref::<OpaqueMessage>() {
            Some(AnyMessage::OpaqueMessage(opaque_message.clone()))
        } else if let Some(v) = boxed.as_ref().downcast_ref::<Vec<u8>>() {
            Some(AnyMessage::Bitstring(v.clone()))
        } else if let Some(v) = boxed.as_ref().downcast_ref::<Option<Vec<u8>>>() {
            match v {
                Some(v) => Some(AnyMessage::Bitstring(v.clone())),
                None => None,
            }
        } else if let Some(v) = boxed.as_ref().downcast_ref::<Vec<Vec<u8>>>() {
            Some(AnyMessage::Bitstringstring(v.clone()))
        } else if let Some(n) = boxed.as_ref().downcast_ref::<u64>() {
            Some(AnyMessage::Constant64(n.clone()))
        } else if let Some(c) = boxed.as_ref().downcast_ref::<Certificate>() {
            Some(AnyMessage::Certificate(c.clone()))
        } else if let Some(vc) = boxed.as_ref().downcast_ref::<Vec<Certificate>>() {
            Some(AnyMessage::VecCertificate(vc.clone()))
        } else if let Some(ce) = boxed.as_ref().downcast_ref::<CertificateEntry>() {
            Some(AnyMessage::CertificateEntry(ce.clone()))
        } else if let Some(vce) = boxed.as_ref().downcast_ref::<Vec<CertificateEntry>>() {
            Some(AnyMessage::VecCertificateEntry(vce.clone()))
        } else if let Some(ce) = boxed.as_ref().downcast_ref::<ClientExtension>() {
            Some(AnyMessage::ClientExtension(ce.clone()))
        } else if let Some(vce) = boxed.as_ref().downcast_ref::<Vec<ClientExtension>>() {
            Some(AnyMessage::VecClientExtension(vce.clone()))
        } else if let Some(se) = boxed.as_ref().downcast_ref::<ServerExtension>() {
            Some(AnyMessage::ServerExtension(se.clone()))
        } else if let Some(vse) = boxed.as_ref().downcast_ref::<Vec<ServerExtension>>() {
            Some(AnyMessage::VecServerExtension(vse.clone()))
        } else if let Some(re) = boxed.as_ref().downcast_ref::<HelloRetryExtension>() {
            Some(AnyMessage::HelloRetryExtension(re.clone()))
        } else if let Some(vre) = boxed.as_ref().downcast_ref::<Vec<HelloRetryExtension>>() {
            Some(AnyMessage::VecHelloRetryExtension(vre.clone()))
        } else if let Some(cre) = boxed.as_ref().downcast_ref::<CertReqExtension>() {
            Some(AnyMessage::CertReqExtension(cre.clone()))
        } else if let Some(vcre) = boxed.as_ref().downcast_ref::<Vec<CertReqExtension>>() {
            Some(AnyMessage::VecCertReqExtension(vcre.clone()))
        } else if let Some(ce) = boxed.as_ref().downcast_ref::<CertificateExtension>() {
            Some(AnyMessage::CertificateExtension(ce.clone()))
        } else if let Some(vce) = boxed.as_ref().downcast_ref::<Vec<CertificateExtension>>() {
            Some(AnyMessage::VecCertificateExtension(vce.clone()))
        } else if let Some(nste) = boxed.as_ref().downcast_ref::<NewSessionTicketExtension>() {
            Some(AnyMessage::NewSessionTicketExtension(nste.clone()))
        } else if let Some(vnste) = boxed
            .as_ref()
            .downcast_ref::<Vec<NewSessionTicketExtension>>()
        {
            Some(AnyMessage::VecNewSessionTicketExtension(vnste.clone()))
        } else if let Some(psk) = boxed.as_ref().downcast_ref::<PresharedKeyIdentity>() {
            Some(AnyMessage::PresharedKey(psk.clone()))
        } else if let Some(vpsk) = boxed.as_ref().downcast_ref::<Vec<PresharedKeyIdentity>>() {
            Some(AnyMessage::VecPresharedKey(vpsk.clone()))
        } else if let Some(cs) = boxed.as_ref().downcast_ref::<CipherSuite>() {
            Some(AnyMessage::CipherSuite(cs.clone()))
        } else if let Some(vcs) = boxed.as_ref().downcast_ref::<Vec<CipherSuite>>() {
            Some(AnyMessage::VecCipherSuite(vcs.clone()))
        } else if let Some(c) = boxed.as_ref().downcast_ref::<Compression>() {
            Some(AnyMessage::Compression(c.clone()))
        } else if let Some(vc) = boxed.as_ref().downcast_ref::<Vec<Compression>>() {
            Some(AnyMessage::VecCompression(vc.clone()))
        } else if let Some(sc) = boxed.as_ref().downcast_ref::<SignatureScheme>() {
            Some(AnyMessage::SignatureScheme(sc.clone()))
        } else if let Some(ocsp) = boxed
            .as_ref()
            .downcast_ref::<OCSPCertificateStatusRequest>()
        {
            Some(AnyMessage::OCSPCertificateStatusRequest(ocsp.clone()))
        } else if let Some(ng) = boxed.as_ref().downcast_ref::<NamedGroup>() {
            Some(AnyMessage::NamedGroup(ng.clone()))
        } else if let Some(pv) = boxed.as_ref().downcast_ref::<ProtocolVersion>() {
            Some(AnyMessage::ProtocolVersion(pv.clone()))
        } else if let Some(id) = boxed.as_ref().downcast_ref::<SessionID>() {
            Some(AnyMessage::SessionID(id.clone()))
        } else if let Some(r) = boxed.as_ref().downcast_ref::<Random>() {
            Some(AnyMessage::Random(r.clone()))
        } else {
            None
        }
    }

    fn unwrap(&self) -> Box<dyn Any> {
        match self {
            AnyMessage::Message(m) => m.boxed_any(),
            AnyMessage::OpaqueMessage(m) => m.boxed_any(),

            AnyMessage::Bitstring(m) => m.boxed_any(),
            AnyMessage::Bitstringstring(m) => m.boxed_any(),
            AnyMessage::Constant64(m) => m.boxed_any(),

            AnyMessage::CertificateEntry(m) => m.boxed_any(),
            AnyMessage::VecCertificateEntry(m) => m.boxed_any(),
            AnyMessage::ClientExtension(m) => m.boxed_any(),
            AnyMessage::VecClientExtension(m) => m.boxed_any(),
            AnyMessage::ServerExtension(m) => m.boxed_any(),
            AnyMessage::VecServerExtension(m) => m.boxed_any(),
            AnyMessage::HelloRetryExtension(m) => m.boxed_any(),
            AnyMessage::VecHelloRetryExtension(m) => m.boxed_any(),
            AnyMessage::CertReqExtension(m) => m.boxed_any(),
            AnyMessage::VecCertReqExtension(m) => m.boxed_any(),
            AnyMessage::CertificateExtension(m) => m.boxed_any(),
            AnyMessage::VecCertificateExtension(m) => m.boxed_any(),
            AnyMessage::NewSessionTicketExtension(m) => m.boxed_any(),
            AnyMessage::VecNewSessionTicketExtension(m) => m.boxed_any(),
            AnyMessage::PresharedKey(m) => m.boxed_any(),
            AnyMessage::VecPresharedKey(m) => m.boxed_any(),
            AnyMessage::CipherSuite(m) => m.boxed_any(),
            AnyMessage::VecCipherSuite(m) => m.boxed_any(),
            AnyMessage::Certificate(m) => m.boxed_any(),
            AnyMessage::VecCertificate(m) => m.boxed_any(),
            AnyMessage::Compression(m) => m.boxed_any(),
            AnyMessage::VecCompression(m) => m.boxed_any(),

            AnyMessage::SignatureScheme(m) => m.boxed_any(),
            AnyMessage::OCSPCertificateStatusRequest(m) => m.boxed_any(),
            AnyMessage::NamedGroup(m) => m.boxed_any(),
            AnyMessage::ProtocolVersion(m) => m.boxed_any(),
            AnyMessage::SessionID(m) => m.boxed_any(),
            AnyMessage::Random(m) => m.boxed_any(),
        }
    }
}
