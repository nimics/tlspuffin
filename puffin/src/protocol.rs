use std::{
    any::Any,
    fmt::{Debug, Display},
    hash::Hash,
};

use libafl::prelude::HasBytesVec;
use serde::{de::DeserializeOwned, Deserialize, Serialize};

use crate::{
    algebra::{signature::Signature, Matcher},
    claims::{Claim, SecurityViolationPolicy},
    codec::Codec,
    error::Error,
    put_registry::PutRegistry,
    trace::Trace,
    variable_data::VariableData,
};

/// A structured message. This type defines how all possible messages of a protocol.
/// Usually this is implemented using an `enum`.
/// micol : added trait HasBytesVec
pub trait ProtocolMessage<O: OpaqueProtocolMessage>: Clone + Debug + Codec {
    fn create_opaque(&self) -> O;
    fn debug(&self, info: &str);
    fn extract_knowledge(&self) -> Result<Vec<Box<dyn VariableData>>, Error>;
}

/// A non-structured version of [`ProtocolMessage`]. This can be used for example for encrypted messages
/// which do not have a structure.
/// micol : added trait HasBytesVec
pub trait OpaqueProtocolMessage: Clone + Debug + Codec + HasBytesVec {
    fn debug(&self, info: &str);
    fn extract_knowledge(&self) -> Result<Vec<Box<dyn VariableData>>, Error>;
}
/* impl<T: OpaqueProtocolMessage> Display for T {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.debug("this is a message"))
    }
} */

/// Deframes a stream of bytes into distinct [OpaqueProtocolMessages](OpaqueProtocolMessage).
/// A deframer is usually state-ful. This means it produces as many messages from the input bytes
/// and stores them.
pub trait ProtocolMessageDeframer {
    type OpaqueProtocolMessage: OpaqueProtocolMessage;

    fn pop_frame(&mut self) -> Option<Self::OpaqueProtocolMessage>;
    fn read(&mut self, rd: &mut dyn std::io::Read) -> std::io::Result<usize>;
}

/// Defines the protocol which is being tested.
/// The fuzzer is generally abstract over the used protocol. We assume that protocols have
/// [opaque messages](OpaqueMessage), [structured messages](Message),
/// and a way to [deframe](MessageDeframer) an arbitrary stream of bytes into messages.
///
/// Also the library allows the definition of a type for [claims](Claim) and a
/// (security policy)[SecurityViolationPolicy] over
/// sequences of them. Finally, there is a [matcher](Matcher) which allows traces to include
/// queries for [knowledge](crate::trace::Knowledge).
///

pub trait ProtocolBehavior: 'static + Clone + Hash + Serialize + DeserializeOwned {
    type Claim: Claim;
    type SecurityViolationPolicy: SecurityViolationPolicy<Self::Claim>;

    type ProtocolMessage: ProtocolMessage<Self::OpaqueProtocolMessage>;
    type OpaqueProtocolMessage: OpaqueProtocolMessage;
    type AnyProtocolMessage: AnyProtocolMessage; // this contains all possible messages

    type Matcher: Matcher
        + for<'a> TryFrom<&'a MessageResult<Self::ProtocolMessage, Self::OpaqueProtocolMessage>>;

    /// Get the signature which is used in the protocol
    fn signature() -> &'static Signature;

    /// Gets the registry for concrete programs-under-test.
    fn registry() -> &'static PutRegistry<Self>
    where
        Self: Sized;

    /// Creates a sane initial seed corpus.
    fn create_corpus() -> Vec<(Trace<Self::Matcher, Self>, &'static str)>;
}

pub struct MessageResult<M: ProtocolMessage<O>, O: OpaqueProtocolMessage>(pub Option<M>, pub O);

impl<M: ProtocolMessage<O>, O: OpaqueProtocolMessage> MessageResult<M, O> {
    /// Extracts as much data from the message as possible. Depending on the protocol,
    /// the extraction can be more fine-grained to more coarse.
    pub fn extract_knowledge(&self) -> Result<Vec<Box<dyn VariableData>>, Error> {
        let opaque_knowledge = self.1.extract_knowledge();

        if let Some(message) = &self.0 {
            if let Ok(opaque_knowledge) = opaque_knowledge {
                message.extract_knowledge().map(|mut knowledge| {
                    knowledge.extend(opaque_knowledge);
                    knowledge
                })
            } else {
                message.extract_knowledge()
            }
        } else {
            opaque_knowledge
        }
    }

    pub fn create_matcher<PB: ProtocolBehavior>(&self) -> Option<PB::Matcher>
    where
        PB: ProtocolBehavior<OpaqueProtocolMessage = O, ProtocolMessage = M>,
    {
        // TODO: Should we return here or use None?
        <<PB as ProtocolBehavior>::Matcher as TryFrom<&MessageResult<M, O>>>::try_from(self).ok()
    }
}

pub trait AnyProtocolMessage: Codec + VariableData {
    fn downcast(boxed: Box<dyn Any>) -> Option<Self>;
    fn upcast(&self) -> Box<dyn Any>;
    fn give_payload(&self, bytes: Vec<Vec<u8>>) -> Self;
    fn get_havoc_encoding(&self) -> Vec<Vec<u8>>;
}
