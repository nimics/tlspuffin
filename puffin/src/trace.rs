//! This module contains [`Trace`]s consisting of several [`Step`]s, of which each has either an
//! [`OutputAction`] or [`InputAction`]. This is a declarative way of modeling communication between
//! [`Agent`]s. The [`TraceContext`] holds data, also known as [`VariableData`], which is created by
//! [`Agent`]s during the concrete execution of the Trace. It also holds the [`Agent`]s with
//! the references to concrete PUT.
//!
//! ### Serializability of Traces
//!
//! Each trace is serializable to JSON or even binary data. This helps at reproducing discovered
//! security vulnerabilities during fuzzing. If a trace triggers a security vulnerability we can
//! store it on disk and replay it when investigating the case.
//! As traces depend on concrete implementations as discussed in the next section we need to link
//! serialized data like strings or numerical IDs to functions implemented in Rust.
//!

use core::fmt;
use std::{
    any::{Any, TypeId},
    collections::HashMap,
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
};

use libafl::prelude::*; //micol
use log::{debug, trace, warn};
use serde::{Deserialize, Serialize};

#[allow(unused)] // used in docs
use crate::stream::Channel;
use crate::{
    agent::{Agent, AgentDescriptor, AgentName},
    algebra::{dynamic_function::TypeShape, error::FnError, remove_prefix, Matcher, Term},
    claims::{Claim, GlobalClaimList, SecurityViolationPolicy},
    error::Error,
    protocol::{MessageResult, OpaqueProtocolMessage, ProtocolBehavior, ProtocolMessage},
    put::{PutDescriptor, PutOptions},
    put_registry::{Factory, PutRegistry},
    variable_data::VariableData,
};

/// When adding some (sub-)message m to ϕ, puffin and tlspuffin
/// also stores from which agent it originates, the kind
/// of message it is, and its internal Rust type
/// The attacker can use queries to access its knowledge in place of variables in attacker terms and traces
#[derive(Debug, Deserialize, Serialize, Clone, Copy, Hash, Eq, PartialEq)]
pub struct Query<M> {
    pub agent_name: AgentName,
    pub matcher: Option<M>,
    pub counter: u16, // in case an agent sends multiple messages of the same type
}

impl<M: Matcher> fmt::Display for Query<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({}, {})[{:?}]",
            self.agent_name, self.counter, self.matcher
        )
    }
}

impl<M: Matcher> Knowledge<M> {
    pub fn specificity(&self) -> u32 {
        self.matcher.specificity()
    }
}

/// [Knowledge] describes an atomic piece of knowledge inferred
/// by the [`crate::variable_data::extract_knowledge`] function
/// [Knowledge] is made of the data, the agent that produced the output, the TLS message type and the internal type.
pub struct Knowledge<M: Matcher> {
    pub agent_name: AgentName, // agent that produced the output
    pub matcher: Option<M>,
    pub data: Box<dyn VariableData>,
}

impl<M: Matcher> Knowledge<M> {
    pub fn debug_print<PB>(&self, ctx: &TraceContext<PB>, agent_name: &AgentName)
    where
        PB: ProtocolBehavior<Matcher = M>,
    {
        let data_type_id = self.data.as_ref().type_id();
        debug!(
            "New knowledge {}: {}  (counter: {})",
            &self,
            remove_prefix(self.data.type_name()),
            ctx.number_matching_message(*agent_name, data_type_id, &self.matcher)
        );
        trace!("Knowledge data: {:?}", self.data);
    }
}
impl<M: Matcher> fmt::Display for Knowledge<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({})/{:?}", self.agent_name, self.matcher)
    }
}

/// The [`TraceContext`] contains a list of [`VariableData`], which is known as the knowledge
/// of the attacker. [`VariableData`] can contain data of various types like for example
/// client and server extensions, cipher suits or session ID. It also holds the concrete
/// references to the [`Agent`]s and the underlying streams, which contain the messages
/// which have need exchanged and are not yet processed by an output step.
pub struct TraceContext<PB: ProtocolBehavior + 'static> {
    /// The knowledge of the attacker
    knowledge: Vec<Knowledge<PB::Matcher>>,
    agents: Vec<Agent<PB>>,
    claims: GlobalClaimList<PB::Claim>,

    put_registry: &'static PutRegistry<PB>,
    deterministic_put: bool,
    default_put_options: PutOptions,
    non_default_put_descriptors: HashMap<AgentName, PutDescriptor>,

    phantom: PhantomData<PB>,
}

impl<PB: ProtocolBehavior> TraceContext<PB> {
    pub fn new(put_registry: &'static PutRegistry<PB>, default_put_options: PutOptions) -> Self {
        // We keep a global list of all claims throughout the execution. Each claim is identified
        // by the AgentName. A rename of an Agent does not interfere with this.
        let claims = GlobalClaimList::new();

        Self {
            knowledge: vec![],
            agents: vec![],
            claims,
            non_default_put_descriptors: Default::default(),
            put_registry,
            deterministic_put: false,
            phantom: Default::default(),
            default_put_options,
        }
    }

    pub fn put_registry(&self) -> &PutRegistry<PB> {
        self.put_registry
    }

    pub fn claims(&self) -> &GlobalClaimList<PB::Claim> {
        &self.claims
    }

    // this is specific to the PUT protocol
    pub fn verify_security_violations(&self) -> Result<(), Error> {
        let claims = self.claims.deref_borrow();
        if let Some(msg) = PB::SecurityViolationPolicy::check_violation(claims.slice()) {
            return Err(Error::SecurityClaim(msg));
        }
        Ok(())
    }

    pub fn add_knowledge(&mut self, knowledge: Knowledge<PB::Matcher>) {
        self.knowledge.push(knowledge)
    }

    /// Count the number of sub-messages of type [type_id] in the output message [in_step_id]
    /// matches on the agent name, the type of the tls message and the internal rust type
    pub fn number_matching_message(
        &self,
        agent: AgentName,
        type_id: TypeId,
        tls_message_type: &Option<PB::Matcher>,
    ) -> usize {
        self.knowledge
            .iter()
            .filter(|knowledge| {
                knowledge.agent_name == agent
                    && knowledge.matcher == *tls_message_type
                    && knowledge.data.as_ref().type_id() == type_id
            })
            .count()
    }

    pub fn find_claim(
        &self,
        agent_name: AgentName,
        query_type_shape: TypeShape,
    ) -> Option<Box<dyn Any>> {
        self.claims
            .deref_borrow()
            .find_last_claim(agent_name, query_type_shape) // why last ?
            .map(|claim| claim.inner())
    }

    /// Returns the variable which matches best -> highest specificity
    /// makes a query
    /// If we want a variable with lower specificity, then we can just query less specific
    pub fn find_variable(
        &self,
        query_type_shape: TypeShape,
        query: &Query<PB::Matcher>,
    ) -> Option<&(dyn VariableData)> {
        let query_type_id: TypeId = query_type_shape.into();

        let mut possibilities: Vec<&Knowledge<PB::Matcher>> = Vec::new();

        for knowledge in &self.knowledge {
            let data: &dyn VariableData = knowledge.data.as_ref(); // variable data

            if query_type_id == data.type_id() // internal type
                && query.agent_name == knowledge.agent_name // agent
                && knowledge.matcher.matches(&query.matcher)
            // TLS type
            {
                possibilities.push(knowledge);
            }
        } // gets all possibilities

        possibilities.sort_by_key(|a| a.specificity()); // sorts from most interesting to least

        possibilities
            .get(query.counter as usize)
            .map(|possibility| possibility.data.as_ref())
    }

    /// Adds data to the inbound [`Channel`] of the [`Agent`] referenced by the parameter "agent"
    /// data here is the parameter "message"
    pub fn add_to_inbound(
        &mut self,
        agent_name: AgentName,
        message: &PB::OpaqueProtocolMessage,
    ) -> Result<(), Error> {
        self.find_agent_mut(agent_name)
            .map(|agent| agent.put_mut().add_to_inbound(message))
    }

    pub fn next_state(&mut self, agent_name: AgentName) -> Result<(), Error> {
        let agent = self.find_agent_mut(agent_name)?;
        agent.put_mut().progress(&agent_name) // harness makes execution of the PUT progress
    }

    /// Takes data from the outbound [`Channel`] of the [`Agent`] referenced by the parameter "agent".
    /// again, data is a message
    /// See [`MemoryStream::take_message_from_outbound`]
    pub fn take_message_from_outbound(
        &mut self,
        agent_name: AgentName,
    ) -> Result<Option<MessageResult<PB::ProtocolMessage, PB::OpaqueProtocolMessage>>, Error> {
        let agent = self.find_agent_mut(agent_name)?; // finds the channel
        agent.put_mut().take_message_from_outbound() // note : depends on the PUT protocol
    }

    // harness adds a channel for each agent (in agents)
    fn add_agent(&mut self, agent: Agent<PB>) -> AgentName {
        let name = agent.name();
        self.agents.push(agent);
        name
    }

    pub fn new_agent(&mut self, descriptor: &AgentDescriptor) -> Result<AgentName, Error> {
        let agent_name = self.add_agent(Agent::new(self, descriptor)?);
        Ok(agent_name)
    }

    pub fn find_agent_mut(&mut self, name: AgentName) -> Result<&mut Agent<PB>, Error> {
        let mut iter = self.agents.iter_mut();

        iter.find(|agent| agent.name() == name).ok_or_else(|| {
            Error::Agent(format!(
                "Could not find agent {}. Did you forget to call spawn_agents?",
                name
            ))
        })
    }

    pub fn find_agent(&self, name: AgentName) -> Result<&Agent<PB>, Error> {
        let mut iter = self.agents.iter();
        iter.find(|agent| agent.name() == name).ok_or_else(|| {
            Error::Agent(format!(
                "Could not find agent {}. Did you forget to call spawn_agents?",
                name
            ))
        })
    }

    /// Gets the PUT descriptor which should be used for all agents
    pub fn put_descriptor(&self, agent_descriptor: &AgentDescriptor) -> PutDescriptor {
        self.non_default_put_descriptors
            .get(&agent_descriptor.name)
            .cloned()
            .unwrap_or_else(|| self.default_put_descriptor())
    }

    fn default_put_descriptor(&self) -> PutDescriptor {
        let factory = (self.put_registry.default)();
        PutDescriptor {
            name: factory.name(),
            options: self.default_put_options.clone(),
        }
    }

    /// Makes agents use the non-default PUT
    pub fn set_non_default_put(&mut self, agent_name: AgentName, put_descriptor: PutDescriptor) {
        self.non_default_put_descriptors
            .insert(agent_name, put_descriptor);
    }

    pub fn set_non_default_puts(&mut self, descriptors: &[(AgentName, PutDescriptor)]) {
        self.non_default_put_descriptors
            .extend(descriptors.iter().cloned());
    }

    pub fn reset_agents(&mut self) -> Result<(), Error> {
        for agent in &mut self.agents {
            agent.reset(agent.name())?;
        }
        Ok(())
    }

    pub fn agents_successful(&self) -> bool {
        self.agents
            .iter()
            .all(|agent| agent.put().is_state_successful())
    }

    pub fn set_deterministic(&mut self, deterministic: bool) {
        self.deterministic_put = deterministic;
    }
}

#[derive(Clone, Deserialize, Serialize, Hash)]
#[serde(bound = "M: Matcher")]
pub struct Trace<M: Matcher, PB: ProtocolBehavior> {
    pub descriptors: Vec<AgentDescriptor>,
    pub steps: Vec<Step<M, PB>>,
    pub prior_traces: Vec<Trace<M, PB>>,
}

/// A [`Trace`] consists of several [`Step`]s. Each has either a [`OutputAction`] or an [`InputAction`].
/// Each [`Step`]s references an [`Agent`] by name. Furthermore, a trace also has a list of
/// *AgentDescriptors* which act like a blueprint to spawn [`Agent`]s with a corresponding server
/// or client role and a specific TLs version. Essentially they are an [`Agent`] without a stream.
impl<M: Matcher, PB: ProtocolBehavior> Trace<M, PB> {
    // puts agents in Trace into TraceContext.agents
    fn spawn_agents(&self, ctx: &mut TraceContext<PB>) -> Result<(), Error> {
        for descriptor in &self.descriptors {
            let name = if let Some(reusable) = ctx
                .agents
                .iter_mut()
                .find(|existing| existing.put().is_reusable_with(descriptor))
            // check if it is reusable
            {
                // rename if it already exists and we want to reuse
                reusable.rename(descriptor.name)?;
                descriptor.name
            } else {
                // only spawn completely new if not yet existing
                ctx.new_agent(descriptor)? // adds new agent
            };

            if ctx.deterministic_put {
                if let Ok(agent) = ctx.find_agent_mut(name) {
                    if let Err(err) = agent.put_mut().set_deterministic() {
                        warn!("Unable to make agent {} deterministic: {}", name, err)
                    }
                }
            }
        }

        Ok(())
    }

    pub fn execute(&self, ctx: &mut TraceContext<PB>) -> Result<(), Error>
    where
        PB: ProtocolBehavior<Matcher = M>,
    {
        for trace in &self.prior_traces {
            trace.spawn_agents(ctx)?;
            trace.execute(ctx)?;
            ctx.reset_agents()?;
        }
        self.spawn_agents(ctx)?;
        let steps = &self.steps;
        for (i, step) in steps.iter().enumerate() {
            debug!("Executing step #{}", i);
            step.action.execute(step, ctx)?;

            match step.action {
                Action::Input(_) => {
                    let output_step = &OutputAction::<M, PB>::new_step(step.agent);

                    output_step.action.execute(output_step, ctx)?;
                }
                Action::Output(_) => {}
            }

            ctx.claims.deref_borrow().log();

            ctx.verify_security_violations()?;
        }

        Ok(())
    }

    pub fn execute_deterministic(
        &self,
        put_registry: &'static PutRegistry<PB>,
        default_put_options: PutOptions,
    ) -> Result<TraceContext<PB>, Error>
    where
        PB: ProtocolBehavior<Matcher = M>,
    {
        let mut ctx = TraceContext::new(put_registry, default_put_options);
        ctx.set_deterministic(true);
        self.execute(&mut ctx)?;
        Ok(ctx)
    }

    pub fn execute_with_non_default_puts(
        &self,
        put_registry: &'static PutRegistry<PB>,
        descriptors: &[(AgentName, PutDescriptor)],
    ) -> Result<TraceContext<PB>, Error>
    where
        PB: ProtocolBehavior<Matcher = M>,
    {
        let mut ctx = TraceContext::new(put_registry, PutOptions::default());

        ctx.set_non_default_puts(descriptors);

        self.execute(&mut ctx)?;
        Ok(ctx)
    }

    pub fn serialize_postcard(&self) -> Result<Vec<u8>, postcard::Error> {
        postcard::to_allocvec(&self)
    }

    pub fn deserialize_postcard(slice: &[u8]) -> Result<Trace<M, PB>, postcard::Error> {
        postcard::from_bytes::<Trace<M, PB>>(slice)
    }

    /* pub fn gather_bitstring_vec(&self) -> Vec<u8> {
        // initialize an empty vector
        let mut bitstrings = Vec::new();
        for step in &self.steps {
            match &step.action {
                Action::Input(input) => {
                    // in depth search
                    let mut q = vec![&input.recipe];
                    while !q.is_empty() {
                        let term = q.pop().unwrap();
                        match &term {
                            Term::Application(_, subterms) => q.extend(subterms.iter().clone()),
                            Term::Variable(_) => {}
                            Term::Message(m) => bitstrings.extend(m.payload.iter()),
                        }
                    }
                }
                Action::Output(_) => {}
            }
        }
        bitstrings
    } */
}

impl<M: Matcher, PB: ProtocolBehavior> fmt::Debug for Trace<M, PB> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Trace with {} steps", self.steps.len())
    }
}

impl<M: Matcher, PB: ProtocolBehavior> fmt::Display for Trace<M, PB> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Trace:")?;
        for step in &self.steps {
            write!(f, "\n{} -> {}", step.agent, step.action)?;
        }
        Ok(())
    }
}

#[derive(Serialize, Deserialize, Clone, Debug, Hash)]
#[serde(bound = "M: Matcher")]
pub struct Step<M: Matcher, PB: ProtocolBehavior> {
    pub agent: AgentName,
    pub action: Action<M, PB>,
}

/// There are two action types [`OutputAction`] and [`InputAction`] differ.
/// Both actions drive the internal state machine of an [`Agent`] forward by calling `next_state()`.
/// The [`OutputAction`] first forwards the state machine and then extracts knowledge from the
/// TLS messages produced by the underlying stream by calling  `take_message_from_outbound(...)`.
/// The [`InputAction`] evaluates the recipe term and injects the newly produced message
/// into the *inbound channel* of the [`Agent`] referenced through the corresponding [`Step`]s
/// by calling `add_to_inbound(...)` and then drives the state machine forward.
/// Therefore, the difference is that one step *increases* the knowledge of the attacker,
/// whereas the other action *uses* the available knowledge.
#[derive(Serialize, Deserialize, Clone, Debug, Hash)]
#[serde(bound = "M: Matcher")]
pub enum Action<M: Matcher, PB: ProtocolBehavior> {
    Input(InputAction<M>),
    Output(OutputAction<M, PB>),
}

impl<M: Matcher, PB: ProtocolBehavior> Action<M, PB> {
    fn execute(&self, step: &Step<M, PB>, ctx: &mut TraceContext<PB>) -> Result<(), Error>
    where
        PB: ProtocolBehavior<Matcher = M>,
    {
        match self {
            Action::Input(input) => input.input(step, ctx),
            Action::Output(output) => output.output(step, ctx),
        }
    }
}

impl<M: Matcher, PB: ProtocolBehavior> fmt::Display for Action<M, PB> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Action::Input(input) => write!(f, "{}", input),
            Action::Output(output) => write!(f, "{}", output),
        }
    }
}

/// The [`OutputAction`] first forwards the state machine and then extracts knowledge from the
/// TLS messages produced by the underlying stream by calling  `take_message_from_outbound(...)`.
/// An output action is automatically called after each input step.
#[derive(Serialize, Deserialize, Clone, Debug, Hash)]
pub struct OutputAction<M, PB> {
    phantom_m: PhantomData<M>,
    phantom_pb: PhantomData<PB>,
}

impl<M: Matcher, PB: ProtocolBehavior> OutputAction<M, PB> {
    pub fn new_step(agent: AgentName) -> Step<M, PB> {
        Step {
            agent,
            action: Action::Output(OutputAction {
                phantom_m: Default::default(),
                phantom_pb: Default::default(),
            }),
        }
    }

    // called when you want to execute an action (output)
    // micol : PB is okay here ?
    fn output(&self, step: &Step<M, PB>, ctx: &mut TraceContext<PB>) -> Result<(), Error>
    where
        PB: ProtocolBehavior<Matcher = M>,
    {
        ctx.next_state(step.agent)?; // forwards the state machine

        while let Some(message_result) = ctx.take_message_from_outbound(step.agent)? {
            // reads message
            let matcher = message_result.create_matcher::<PB>();

            let MessageResult(message, opaque_message) = message_result;

            let knowledge = message
                .and_then(|message| message.extract_knowledge().ok())
                .unwrap_or_default();
            let opaque_knowledge = opaque_message.extract_knowledge()?;

            debug!(
                "Knowledge increased by {:?}",
                knowledge.len() + opaque_knowledge.len()
            ); // +1 because of the OpaqueMessage below

            for variable in knowledge {
                let knowledge = Knowledge::<M> {
                    agent_name: step.agent,
                    matcher: matcher.clone(),
                    data: variable,
                };

                knowledge.debug_print(ctx, &step.agent);
                ctx.add_knowledge(knowledge)
            }

            for variable in opaque_knowledge {
                let knowledge = Knowledge::<M> {
                    agent_name: step.agent,
                    matcher: None, // none because we can not trust the decoding of tls_message_type, because the message could be encrypted like in TLS 1.2
                    data: variable,
                };

                knowledge.debug_print(ctx, &step.agent);
                ctx.add_knowledge(knowledge)
            }
        }
        Ok(())
    }
}

impl<M: Matcher, PB: ProtocolBehavior> fmt::Display for OutputAction<M, PB> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "OutputAction")
    }
}

/// The [`InputAction`] evaluates the recipe term and injects the newly produced message
/// into the *inbound channel* of the [`Agent`] referenced through the corresponding [`Step`]s
/// by calling `add_to_inbound(...)` and then drives the state machine forward.
#[derive(Serialize, Deserialize, Clone, Debug, Hash)]
#[serde(bound = "M: Matcher")]
pub struct InputAction<M: Matcher> {
    pub recipe: Term<M>,
    // pub phantom_pb: PhantomData<PB>,
}

/// Processes messages in the inbound channel. Uses the recipe field to evaluate to a rustls Message
/// or a MultiMessage.
impl<M: Matcher> InputAction<M> {
    pub fn new_step<PB: ProtocolBehavior>(agent: AgentName, recipe: Term<M>) -> Step<M, PB> {
        Step {
            agent,
            action: Action::Input(InputAction {
                recipe,
                // phantom_pb: Default::default(),
            }),
        }
    }

    fn input<PB: ProtocolBehavior>(
        &self,
        step: &Step<M, PB>,
        ctx: &mut TraceContext<PB>,
    ) -> Result<(), Error>
    where
        PB: ProtocolBehavior<Matcher = M>,
    {
        // message controlled by the attacker
        let evaluated = self.clone().recipe.evaluate(ctx)?; // reads term

        if let Some(msg) = evaluated.as_ref().downcast_ref::<PB::ProtocolMessage>() {
            msg.debug("Input message");

            ctx.add_to_inbound(step.agent, &msg.create_opaque())?; // adds message to inbound channel
        } else if let Some(opaque_message) = evaluated
            .as_ref()
            .downcast_ref::<PB::OpaqueProtocolMessage>()
        {
            opaque_message.debug("Input opaque message");
            ctx.add_to_inbound(step.agent, opaque_message)?;
        } else {
            return Err(FnError::Unknown(String::from(
                "Recipe is not a `ProtocolMessage`, `OpaqueProtocolMessage`!",
            ))
            .into());
        }

        ctx.next_state(step.agent) // forwards state machine
    }
}

impl<M: Matcher> fmt::Display for InputAction<M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "InputAction:\n{}", self.recipe)
    }
}
