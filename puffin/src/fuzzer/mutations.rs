use libafl::prelude::*;
use util::{Choosable, *};

use crate::{
    algebra::{
        atoms::{ByteMessage, Function},
        signature::Signature,
        Matcher, Subterms, Term,
    },
    codec::Codec,
    fuzzer::harness::default_put_options,
    fuzzer::term_zoo::TermZoo,
    protocol::{AnyProtocolMessage, ProtocolBehavior},
    trace::{Action, Trace, TraceContext},
};
use libafl::mutators::Mutator;

// returns list of mutations
pub fn trace_mutations<S, M: Matcher>(
    min_trace_length: usize,
    max_trace_length: usize,
    constraints: TermConstraints,
    fresh_zoo_after: u64,
    signature: &'static Signature,
) -> tuple_list_type!(
       RepeatMutator<S>,
       SkipMutator<S>,
       ReplaceReuseMutator<S>,
       ReplaceMatchMutator<S>,
       RemoveAndLiftMutator<S>,
       GenerateMutator<S, M>,
       SwapMutator<S>,
       MakeMessage<S>,
       BitFlip<S>,
       ByteAdd<S>,
       ByteDec<S>,
       ByteFlip<S>,
       ByteInc<S>,
       ByteInteresting<S>,
       ByteNeg<S>,
       ByteRand<S>,
       BytesCopy<S>,
       BytesDelete<S>,
       BytesExpand<S>,
       BytesInsertCopy<S>,
       BytesInsert<S>,
       BytesRandInsert<S>,
       BytesRandSet<S>,
       BytesSet<S>,
       DwordAdd<S>,
       DwordInteresting<S>,
       QwordAdd<S>,
       WordAdd<S>,
       WordInteresting<S>,
   )
where
    S: HasCorpus + HasMetadata + HasMaxSize + HasRand,
{
    tuple_list!(
        RepeatMutator::new(max_trace_length),
        SkipMutator::new(min_trace_length),
        ReplaceReuseMutator::new(constraints),
        ReplaceMatchMutator::new(constraints, signature),
        RemoveAndLiftMutator::new(constraints),
        GenerateMutator::new(0, fresh_zoo_after, constraints, None, signature), // Refresh zoo after 100000M mutations
        SwapMutator::new(constraints),
        MakeMessage::new(constraints),
        BitFlip::new(),
        ByteAdd::new(),
        ByteDec::new(),
        ByteFlip::new(),
        ByteInc::new(),
        ByteInteresting::new(),
        ByteNeg::new(),
        ByteRand::new(),
        BytesCopy::new(),
        BytesDelete::new(),
        BytesExpand::new(),
        BytesInsertCopy::new(),
        BytesInsert::new(),
        BytesRandInsert::new(),
        BytesRandSet::new(),
        BytesSet::new(),
        DwordAdd::new(),
        DwordInteresting::new(),
        QwordAdd::new(),
        WordAdd::new(),
        WordInteresting::new(),
    )
}
/// SWAP: Swaps a sub-term with a different sub-term which is part of the trace

/// (such that types match).
pub struct SwapMutator<S>
where
    S: HasRand,
{
    constraints: TermConstraints,
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> SwapMutator<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new(constraints: TermConstraints) -> Self {
        Self {
            constraints,
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior> Mutator<Trace<M, PB>, S> for SwapMutator<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        _stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some((term_a, trace_path_a)) = choose(trace, self.constraints, rand) {
            if let Some(trace_path_b) = choose_term_path_filtered(
                trace,
                |term: &Term<M>| term.get_type_shape() == term_a.get_type_shape(),
                self.constraints,
                rand,
            ) {
                let term_a_cloned = term_a.clone();
                if let Some(term_b_mut) = find_term_mut(trace, &trace_path_b) {
                    let term_b_cloned = term_b_mut.clone(); // swaps
                    term_b_mut.mutate(term_a_cloned);
                    if let Some(trace_a_mut) = find_term_mut(trace, &trace_path_a) {
                        trace_a_mut.mutate(term_b_cloned);
                    }
                    return Ok(MutationResult::Mutated);
                }
            }
        }
        Ok(MutationResult::Skipped)
    }
}

impl<S> Named for SwapMutator<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<SwapMutator<S>>()
    }
}

/// REMOVE AND LIFT: Removes a sub-term from a term and attaches orphaned children to the parent

/// (such that types match). This only works if there is only a single child.
pub struct RemoveAndLiftMutator<S>
where
    S: HasRand,
{
    constraints: TermConstraints,
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> RemoveAndLiftMutator<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new(constraints: TermConstraints) -> Self {
        Self {
            constraints,
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior> Mutator<Trace<M, PB>, S> for RemoveAndLiftMutator<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        _stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        let filter = |term: &Term<M>| match term {
            Term::Application(_, subterms) => subterms
                .find_subterm(|subterm| match subterm {
                    Term::Application(_, grand_subterms) => {
                        grand_subterms.find_subterm_same_shape(subterm).is_some()
                    }
                    _ => false,
                })
                .is_some(),
            _ => false,
        };
        if let Some(mut to_mutate) = choose_term_filtered_mut(trace, filter, self.constraints, rand)
        {
            match &mut to_mutate {
                Term::Application(_, ref mut subterms) => {
                    if let Some(((subterm_index, _), grand_subterm)) = choose_iter(
                        subterms.filter_grand_subterms(|subterm, grand_subterm| {
                            subterm.get_type_shape() == grand_subterm.get_type_shape()
                        }),
                        rand,
                    ) {
                        let grand_subterm_cloned = grand_subterm.clone();
                        subterms.push(grand_subterm_cloned);
                        subterms.swap_remove(subterm_index);
                        return Ok(MutationResult::Mutated);
                    }
                    Ok(MutationResult::Skipped)
                }
                _ => Ok(MutationResult::Skipped),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}

impl<S> Named for RemoveAndLiftMutator<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<RemoveAndLiftMutator<S>>()
    }
}

/// REPLACE-MATCH: Replaces a function symbol with a different one (such that types match).

/// An example would be to replace a constant with another constant or the binary function

/// fn_add with fn_sub.

/// It can also replace any variable with a constant.
pub struct ReplaceMatchMutator<S>
where
    S: HasRand,
{
    constraints: TermConstraints,
    signature: &'static Signature,
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> ReplaceMatchMutator<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new(constraints: TermConstraints, signature: &'static Signature) -> Self {
        Self {
            constraints,
            signature,
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior> Mutator<Trace<M, PB>, S> for ReplaceMatchMutator<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        _stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(mut to_mutate) = choose_term_mut(trace, self.constraints, rand) {
            match &mut to_mutate {
                Term::Variable(variable) => {
                    // choose a random constant function
                    if let Some((shape, dynamic_fn)) = self.signature.functions.choose_filtered(
                        |(shape, _)| variable.typ == shape.return_type && shape.is_constant(),
                        rand,
                    ) {
                        // replaces variable with the chosen constant
                        to_mutate.mutate(Term::Application(
                            Function::new(shape.clone(), dynamic_fn.clone()),
                            Vec::new(),
                        ));
                        Ok(MutationResult::Mutated)
                    } else {
                        Ok(MutationResult::Skipped)
                    }
                }
                Term::Application(func_mut, _) => {
                    // chooses a random function w same number of arguments, same argument types
                    if let Some((shape, dynamic_fn)) = self.signature.functions.choose_filtered(
                        |(shape, _)| {
                            func_mut.shape() != shape
                                && func_mut.shape().return_type == shape.return_type
                                && func_mut.shape().argument_types == shape.argument_types
                        },
                        rand,
                    ) {
                        // replaces term with chosen function, keeps the same arguments
                        func_mut.change_function(shape.clone(), dynamic_fn.clone());
                        Ok(MutationResult::Mutated)
                    } else {
                        Ok(MutationResult::Skipped)
                    }
                }
                Term::Message(_) => Ok(MutationResult::Skipped),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}

impl<S> Named for ReplaceMatchMutator<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<ReplaceMatchMutator<S>>()
    }
}

/// REPLACE-REUSE: Replaces a sub-term with a different sub-term which is part of the trace

/// (such that types match). The new sub-term could come from another step which has a different recipe term.
pub struct ReplaceReuseMutator<S>
where
    S: HasRand,
{
    constraints: TermConstraints,
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> ReplaceReuseMutator<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new(constraints: TermConstraints) -> Self {
        Self {
            constraints,
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior> Mutator<Trace<M, PB>, S> for ReplaceReuseMutator<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        _stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(replacement) = choose_term(trace, self.constraints, rand).cloned() {
            if let Some(to_replace) = choose_term_filtered_mut(
                trace,
                |term: &Term<M>| term.get_type_shape() == replacement.get_type_shape(),
                self.constraints,
                rand,
            ) {
                to_replace.mutate(replacement);
                return Ok(MutationResult::Mutated);
            }
        }
        Ok(MutationResult::Skipped)
    }
}

impl<S> Named for ReplaceReuseMutator<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<ReplaceReuseMutator<S>>()
    }
}

/// SKIP:  Removes an input step
pub struct SkipMutator<S>
where
    S: HasRand,
{
    min_trace_length: usize,
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> SkipMutator<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new(min_trace_length: usize) -> Self {
        Self {
            min_trace_length,
            phantom_s: std::marker::PhantomData,
        }
    }
}
impl<S, M: Matcher, PB: ProtocolBehavior> Mutator<Trace<M, PB>, S> for SkipMutator<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        _stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let steps = &mut trace.steps;
        let length = steps.len();
        if length <= self.min_trace_length {
            return Ok(MutationResult::Skipped);
        }
        if length == 0 {
            return Ok(MutationResult::Skipped);
        }
        let remove_index = state.rand_mut().between(0, (length - 1) as u64) as usize;
        steps.remove(remove_index);
        Ok(MutationResult::Mutated)
    }
}
impl<S> Named for SkipMutator<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<SkipMutator<S>>()
    }
}

/// REPEAT: Repeats an input which is already part of the trace
pub struct RepeatMutator<S>
where
    S: HasRand,
{
    max_trace_length: usize,
    phantom_s: std::marker::PhantomData<S>,
}
impl<S> RepeatMutator<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new(max_trace_length: usize) -> Self {
        Self {
            max_trace_length,
            phantom_s: std::marker::PhantomData,
        }
    }
}
impl<S, M: Matcher, PB: ProtocolBehavior> Mutator<Trace<M, PB>, S> for RepeatMutator<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        _stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let steps = &trace.steps;
        let length = steps.len();
        if length >= self.max_trace_length {
            return Ok(MutationResult::Skipped);
        }
        if length == 0 {
            return Ok(MutationResult::Skipped);
        }
        let insert_index = state.rand_mut().between(0, length as u64) as usize;
        let step = state.rand_mut().choose(steps).clone();
        trace.steps.insert(insert_index, step);
        Ok(MutationResult::Mutated)
    }
}
impl<S> Named for RepeatMutator<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<RepeatMutator<S>>()
    }
}

/// GENERATE: Generates a previously-unseen term using a term zoo
/// and replaces a term with the generated one
pub struct GenerateMutator<S, M: Matcher>
where
    S: HasRand,
{
    mutation_counter: u64,
    refresh_zoo_after: u64,
    constraints: TermConstraints,
    zoo: Option<TermZoo<M>>,
    signature: &'static Signature,
    phantom_s: std::marker::PhantomData<S>,
}

impl<S, M: Matcher> GenerateMutator<S, M>
where
    S: HasRand,
{
    #[must_use]
    pub fn new(
        mutation_counter: u64,
        refresh_zoo_after: u64,
        constraints: TermConstraints,
        zoo: Option<TermZoo<M>>,
        signature: &'static Signature,
    ) -> Self {
        Self {
            mutation_counter,
            refresh_zoo_after,
            constraints,
            zoo,
            signature,
            phantom_s: std::marker::PhantomData,
        }
    }
}
impl<S, M: Matcher, PB: ProtocolBehavior> Mutator<Trace<M, PB>, S> for GenerateMutator<S, M>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        _stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_mut(trace, self.constraints, rand) {
            self.mutation_counter += 1;
            let zoo = if self.mutation_counter % self.refresh_zoo_after == 0 {
                self.zoo.insert(TermZoo::generate(self.signature, rand))
            } else {
                self.zoo
                    .get_or_insert_with(|| TermZoo::generate(self.signature, rand))
            };
            if let Some(term) = zoo.choose_filtered(
                |term| to_mutate.get_type_shape() == term.get_type_shape(),
                rand,
            ) {
                to_mutate.mutate(term.clone());
                Ok(MutationResult::Mutated)
            } else {
                Ok(MutationResult::Skipped)
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S, M: Matcher> Named for GenerateMutator<S, M>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<GenerateMutator<S, M>>()
    }
}

// ******************************************************************************************************
// Start Havoc Mutations

/// MAKE MESSAGE : transforms a sub term into a message which can then be mutated using havoc
pub struct MakeMessage<S>
where
    S: HasRand,
{
    constraints: TermConstraints,
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> MakeMessage<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new(constraints: TermConstraints) -> Self {
        Self {
            constraints,
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for MakeMessage<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        _stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        //choose a random sub tree
        if let Some((to_mutate, (step_index, term_path))) =
            choose(&trace.clone(), self.constraints, rand)
        /* choose random sub tree (bias for nodes with smaller height)
        if let Some((to_mutate, (step_index, term_path))) =
            choose_with_weights(&trace.clone(), self.constraints, rand) */
        {
            // shorten runtime of the PUT by cutting useless steps (new trace = trace[0..step_index])
            let mut new_trace = trace.clone();
            let mut steps = Vec::new();
            for i in 0..step_index {
                steps.push(new_trace.steps[i].clone());
            }
            new_trace.steps = steps;
            // execute the PUT on the steps and recuperate the context
            let mut ctx = TraceContext::new(PB::registry(), default_put_options().clone());
            let result = new_trace.execute(&mut ctx);
            if result.is_ok() {
                // turn term into a message
                if let Ok(evaluated) = to_mutate.evaluate(&ctx) {
                    match PB::AnyProtocolMessage::downcast(evaluated) {
                        Some(any_message) => {
                            //replace term in tree
                            replace(
                                trace,
                                step_index,
                                term_path,
                                Term::Message(ByteMessage::new(
                                    Box::new(to_mutate.clone()),
                                    any_message.get_havoc_encoding(),
                                )),
                            );
                            Ok(MutationResult::Mutated)
                        }
                        None => Ok(MutationResult::Skipped),
                    }
                } else {
                    // println!("failed to evaluate");
                    Ok(MutationResult::Skipped)
                }
            } else {
                match result {
                    Ok(_) => panic!(),
                    Err(error) => {
                        // println!("failed to execute trace : {}", error);
                        Ok(MutationResult::Skipped)
                    }
                }
            }
        } else {
            // println!("failed to choose term");
            Ok(MutationResult::Skipped)
        }
    }
}

impl<S> Named for MakeMessage<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<MakeMessage<S>>()
    }
}

/// BitFlip : bit flip mutations

pub struct BitFlip<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> BitFlip<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for BitFlip<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        BitFlipMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}

impl<S> Named for BitFlip<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<BitFlip<S>>()
    }
}

/// ByteAddMutator : Adds or subtracts a random value up to ARITH_MAX to a [<$size>] at a random place in the Vec,
/// in random byte order.

pub struct ByteAdd<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> ByteAdd<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for ByteAdd<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        ByteAddMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}

impl<S> Named for ByteAdd<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<ByteAdd<S>>()
    }
}

/// ByteDecMutator : Byte decrement mutation

pub struct ByteDec<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> ByteDec<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for ByteDec<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        ByteDecMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}

impl<S> Named for ByteDec<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<ByteDec<S>>()
    }
}

///  ByteFlipMutator : Byteflip mutation

pub struct ByteFlip<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> ByteFlip<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for ByteFlip<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        ByteFlipMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for ByteFlip<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<ByteFlip<S>>()
    }
}

/// ByteInc : Byte increment mutation

pub struct ByteInc<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> ByteInc<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for ByteInc<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        ByteIncMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}

impl<S> Named for ByteInc<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<ByteInc<S>>()
    }
}

/// ByteInterestingMutator : Inserts an interesting value at a random place in the input vector

pub struct ByteInteresting<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> ByteInteresting<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S>
    for ByteInteresting<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        ByteInterestingMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for ByteInteresting<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<ByteInteresting<S>>()
    }
}

/// ByteNegMutator : Byte negate mutation

pub struct ByteNeg<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> ByteNeg<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for ByteNeg<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        ByteInterestingMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for ByteNeg<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<ByteNeg<S>>()
    }
}

/// ByteRandMutator : Byte random mutation

pub struct ByteRand<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> ByteRand<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for ByteRand<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        ByteRandMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for ByteRand<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<ByteRand<S>>()
    }
}

/// BytesCopyMutator : Bytes copy mutation

pub struct BytesCopy<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> BytesCopy<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for BytesCopy<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        BytesCopyMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for BytesCopy<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<BytesCopy<S>>()
    }
}

/// BytesDeleteMutator : Bytes delete mutation

pub struct BytesDelete<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> BytesDelete<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for BytesDelete<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        BytesDeleteMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for BytesDelete<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<BytesCopy<S>>()
    }
}

/// BytesExpandMutator : Bytes expand mutation

pub struct BytesExpand<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> BytesExpand<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for BytesExpand<S>
where
    S: HasRand + HasMaxSize,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        BytesExpandMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for BytesExpand<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<BytesExpand<S>>()
    }
}

/// BytesInsertCopyMutator : Bytes insert and self copy mutation

pub struct BytesInsertCopy<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> BytesInsertCopy<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S>
    for BytesInsertCopy<S>
where
    S: HasRand + HasMaxSize,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        mutations::BytesInsertCopyMutator::default().mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for BytesInsertCopy<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<BytesInsertCopy<S>>()
    }
}

/// BytesInsertMutator : Bytes insert mutation

pub struct BytesInsert<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> BytesInsert<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for BytesInsert<S>
where
    S: HasRand + HasMaxSize,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        BytesInsertMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for BytesInsert<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<BytesInsert<S>>()
    }
}

/// BytesRandInsertMutator : Bytes random insert mutation

pub struct BytesRandInsert<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> BytesRandInsert<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S>
    for BytesRandInsert<S>
where
    S: HasRand + HasMaxSize,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        BytesRandInsertMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for BytesRandInsert<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<BytesRandInsert<S>>()
    }
}

/// BytesRandSetMutator : Bytes random set mutation

pub struct BytesRandSet<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> BytesRandSet<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for BytesRandSet<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        BytesRandSetMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for BytesRandSet<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<BytesRandSet<S>>()
    }
}

/// BytesSetMutator : Bytes set mutation

pub struct BytesSet<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> BytesSet<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for BytesSet<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        BytesSetMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for BytesSet<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<BytesSet<S>>()
    }
}

/*
/// BytesSwapMutator : Bytes swap mutation for inputs with a bytes vector

pub struct BytesSwap<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

pub struct Bitstring(Vec<u8>);

impl Bitstring {
    pub fn new(data: Vec<u8>) -> Bitstring {
        Bitstring(data)
    }
}

impl HasBytesVec for Bitstring {
    fn bytes(&self) -> &[u8] {
        &self.0
    }

    fn bytes_mut(&mut self) -> &mut Vec<u8> {
        &mut self.0
    }
}

impl<S> BytesSwap<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for BytesSwap<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        // make a vector with all the payloads of messages
        let mut bitstring = Bitstring::new(trace.gather_bitstring_vec());
        match BytesSwapMutator::default().mutate(state, &mut bitstring, stage_idx) {
            Ok(MutationResult::Mutated) => {
                for step_index in 0..trace.steps.len() {
                    match &mut trace.steps[step_index].action {
                        Action::Input(input) => replace_payloads(&mut input.recipe, &mut bitstring),
                        Action::Output(_) => {}
                    }
                }
                Ok(MutationResult::Mutated)
            }
            Ok(MutationResult::Skipped) => Ok(MutationResult::Skipped),
            Err(error) => Err(error), // shouldn't happen
        }
    }
}

pub fn replace_payloads<M: Matcher>(term: &mut Term<M>, bitstring: &mut Bitstring) {
    let mut q = vec![term];
    while !q.is_empty() {
        let term = q.pop().unwrap();
        match term {
            Term::Application(_, subterms) => {
                for subterm in subterms {
                    q.push(subterm)
                }
            }
            Term::Message(m) => {
                let mut new_payload = Vec::new();
                for _ in 0..new_payload.len() {
                    new_payload.push(bitstring.0.pop().unwrap())
                }
                m.payload = new_payload;
            }
            _ => {}
        }
    }
}

impl<S> Named for BytesSwap<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<BytesSwap<S>>()
    }
}
*/

/// DwordAddMutator : Adds or subtracts a random value up to ARITH_MAX to a [<$size>]
/// at a random place in the Vec, in random byte order.

pub struct DwordAdd<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> DwordAdd<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for DwordAdd<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        DwordAddMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for DwordAdd<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<DwordAdd<S>>()
    }
}

/// DwordInterestingMutator : Inserts an interesting value at a random place in the input vector

pub struct DwordInteresting<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> DwordInteresting<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S>
    for DwordInteresting<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        DwordInterestingMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for DwordInteresting<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<DwordInteresting<S>>()
    }
}

/// QwordAddMutator : Adds or subtracts a random value up to ARITH_MAX to a [<$size>]
/// at a random place in the Vec, in random byte order.

pub struct QwordAdd<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> QwordAdd<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for QwordAdd<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        QwordAddMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for QwordAdd<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<QwordAdd<S>>()
    }
}

/*
/// SpliceMutator : Splice mutation

pub struct Splice<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> Splice<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for Splice<S>
where
    S: HasRand + HasCorpus,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => SpliceMutator.mutate(state, msg, stage_idx), // stage ?
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for Splice<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<Splice<S>>()
    }
}
*/

/// WordAddMutator : Adds or subtracts a random value up to ARITH_MAX to a [<$size>]
/// at a random place in the Vec, in random byte order.

pub struct WordAdd<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> WordAdd<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S> for WordAdd<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        WordAddMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for WordAdd<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<WordAdd<S>>()
    }
}

/// WordInterestingMutator : Inserts an interesting value at a random place in the input vector

pub struct WordInteresting<S>
where
    S: HasRand,
{
    phantom_s: std::marker::PhantomData<S>,
}

impl<S> WordInteresting<S>
where
    S: HasRand,
{
    #[must_use]
    pub fn new() -> Self {
        Self {
            phantom_s: std::marker::PhantomData,
        }
    }
}

impl<S, M: Matcher, PB: ProtocolBehavior<Matcher = M>> Mutator<Trace<M, PB>, S>
    for WordInteresting<S>
where
    S: HasRand,
{
    fn mutate(
        &mut self,
        state: &mut S,
        trace: &mut Trace<M, PB>,
        stage_idx: i32,
    ) -> Result<MutationResult, Error> {
        let rand = state.rand_mut();
        if let Some(to_mutate) = choose_term_filtered_mut(
            trace,
            |x| match x {
                Term::Message(_) => true,
                _ => false,
            },
            TermConstraints::default(),
            rand,
        ) {
            match to_mutate {
                Term::Message(msg) => {
                    if msg.payload.len() == 0 {
                        Ok(MutationResult::Skipped)
                    } else {
                        msg.index = rand
                            .below(msg.payload.len().try_into().unwrap())
                            .try_into()
                            .unwrap();
                        WordInterestingMutator.mutate(state, msg, stage_idx)
                    }
                }
                _ => panic!("this shouldn't happen !"),
            }
        } else {
            Ok(MutationResult::Skipped)
        }
    }
}
impl<S> Named for WordInteresting<S>
where
    S: HasRand,
{
    fn name(&self) -> &str {
        std::any::type_name::<WordInteresting<S>>()
    }
}

// *******************************************************************************************************

pub mod util {

    use libafl::bolts::rands::Rand;

    use crate::{
        algebra::{Matcher, Term},
        protocol::ProtocolBehavior,
        trace::{Action, InputAction, Step, Trace},
    };

    #[derive(Copy, Clone, Debug)]
    pub struct TermConstraints {
        pub min_term_size: usize,
        pub max_term_size: usize,
    }

    /// Default values which represent no constraint
    impl Default for TermConstraints {
        fn default() -> Self {
            Self {
                min_term_size: 0,
                max_term_size: 9000,
            }
        }
    }

    pub trait Choosable<T, R: Rand> {
        fn choose_filtered<P>(&self, filter: P, rand: &mut R) -> Option<&T>
        where
            P: FnMut(&&T) -> bool;
        fn choose(&self, rand: &mut R) -> Option<&T>;
    }

    impl<T, R: Rand> Choosable<T, R> for Vec<T> {
        fn choose_filtered<P>(&self, filter: P, rand: &mut R) -> Option<&T>
        where
            P: FnMut(&&T) -> bool,
        {
            let filtered = self.iter().filter(filter).collect::<Vec<&T>>();
            let length = filtered.len();

            if length == 0 {
                None
            } else {
                let index = rand.below(length as u64) as usize;
                filtered.into_iter().nth(index)
            }
        }

        fn choose(&self, rand: &mut R) -> Option<&T> {
            let length = self.len();

            if length == 0 {
                None
            } else {
                let index = rand.below(length as u64) as usize;
                self.get(index)
            }
        }
    }

    pub fn choose_iter<I, E, T, R: Rand>(from: I, rand: &mut R) -> Option<T>
    where
        I: IntoIterator<Item = T, IntoIter = E>,
        E: ExactSizeIterator + Iterator<Item = T>,
    {
        // create iterator
        let mut iter = from.into_iter();
        let length = iter.len();

        if length == 0 {
            None
        } else {
            // pick a random, valid index
            let index = rand.below(length as u64) as usize;

            // return the item chosen
            iter.nth(index)
        }
    }

    pub type StepIndex = usize;
    pub type TermPath = Vec<usize>;
    pub type TracePath = (StepIndex, TermPath);

    /// https://en.wikipedia.org/wiki/Reservoir_sampling#Simple_algorithm
    // chooses a random sample, used in function choose, used in mutations
    fn reservoir_sample<
        'a,
        R: Rand,
        M: Matcher,
        PB: ProtocolBehavior,
        P: Fn(&Term<M>) -> bool + Copy,
    >(
        trace: &'a Trace<M, PB>,
        filter: P,
        constraints: TermConstraints,
        rand: &mut R,
    ) -> Option<(&'a Term<M>, TracePath)> {
        let mut reservoir: Option<(&'a Term<M>, TracePath)> = None;
        let mut visited = 0;

        for (step_index, step) in trace.steps.iter().enumerate() {
            match &step.action {
                Action::Input(input) => {
                    let term = &input.recipe;

                    let size = term.size();
                    if size <= constraints.min_term_size || size >= constraints.max_term_size {
                        continue;
                    }

                    let mut stack: Vec<(&Term<M>, TracePath)> =
                        vec![(term, (step_index, Vec::new()))];

                    while let Some((term, path)) = stack.pop() {
                        // push next terms onto stack
                        match term {
                            Term::Application(_, subterms) => {
                                // inner node, recursively continue
                                for (path_index, subterm) in subterms.iter().enumerate() {
                                    let mut new_path = path.clone();
                                    new_path.1.push(path_index); // invert because of .iter().rev()
                                    stack.push((subterm, new_path));
                                }
                            }
                            _ => {
                                // reached leaf
                            }
                        }

                        // sample
                        if filter(term) {
                            visited += 1;

                            // consider in sampling
                            if reservoir.is_none() {
                                // fill initial reservoir
                                reservoir = Some((term, path));
                            } else {
                                // `1/visited` chance of overwriting
                                // replace elements with gradually decreasing probability
                                if rand.between(1, visited) == 1 {
                                    reservoir = Some((term, path));
                                }
                            }
                        }
                    }
                }
                Action::Output(_) => {
                    // no term -> skip
                }
            }
        }

        reservoir
    }

    // Algorithm A Chao here https://en.wikipedia.org/wiki/Reservoir_sampling#Simple_algorithm
    fn weighted_reservoir<'a, R: Rand, M: Matcher, PB: ProtocolBehavior>(
        trace: &'a Trace<M, PB>,
        constraints: TermConstraints,
        rand: &mut R,
    ) -> Option<(&'a Term<M>, TracePath)> {
        let mut reservoir: Option<(&'a Term<M>, TracePath)> = None;
        let mut totalweight: u64 = 0;

        // calculate max tree height amongst the input steps
        let mut max_height = 1;
        for step in &trace.steps {
            match &step.action {
                Action::Input(input) => {
                    let term = &input.recipe;
                    let height = term.height();
                    if height > max_height {
                        max_height = height;
                    }
                }
                Action::Output(_) => {}
            }
        }

        for (step_index, step) in trace.steps.iter().enumerate() {
            match &step.action {
                Action::Input(input) => {
                    let term = &input.recipe;

                    let size = term.size();
                    if size <= constraints.min_term_size || size >= constraints.max_term_size {
                        continue;
                    }

                    // calculate the height of each sub tree
                    // then execute the algo A Chao

                    // queue for a classic DFS
                    let mut q: Vec<(&Term<M>, TermPath)> = vec![(term, Vec::new())];

                    while !q.is_empty() {
                        let term = q.pop().unwrap();
                        match term.0 {
                            Term::Application(_, ref subterms) => {
                                // add future nodes to explore
                                for (path_index, t) in subterms.iter().enumerate() {
                                    let mut new_path = term.1.clone();
                                    new_path.push(path_index);
                                    q.push((t, new_path))
                                }

                                // calculate height of current term
                                let height = term.0.height();
                                //we have the height, apply A Chao

                                let weight: u64 = (2 as u64).pow((max_height - height) as u32);
                                totalweight += weight;
                                if reservoir.is_none() {
                                    reservoir = Some((term.0, (step_index, term.1)))
                                } else {
                                    if rand.between(1, totalweight) < weight + 1 {
                                        reservoir = Some((term.0, (step_index, term.1)))
                                    }
                                }
                            }
                            _ => {
                                // Apply A Chao with height = 1
                                let weight = (2 as u64).pow(max_height as u32);
                                totalweight += weight;
                                if reservoir.is_none() {
                                    reservoir = Some((term.0, (step_index, term.1)))
                                } else {
                                    if rand.between(1, totalweight) < weight + 1 {
                                        reservoir = Some((term.0, (step_index, term.1)))
                                    };
                                }
                            }
                        }
                    }
                }
                Action::Output(_) => {}
            }
        }
        reservoir
    }

    fn find_term_by_term_path_mut<'a, M: Matcher>(
        term: &'a mut Term<M>,
        term_path: &mut TermPath,
    ) -> Option<&'a mut Term<M>> {
        if term_path.is_empty() {
            return Some(term);
        }

        let subterm_index = term_path.remove(0);

        match term {
            Term::Application(_, subterms) => {
                if let Some(subterm) = subterms.get_mut(subterm_index) {
                    find_term_by_term_path_mut(subterm, term_path)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn find_term_mut<'a, M: Matcher, PB: ProtocolBehavior>(
        trace: &'a mut Trace<M, PB>,
        trace_path: &TracePath,
    ) -> Option<&'a mut Term<M>> {
        let (step_index, term_path) = trace_path;

        let step: Option<&mut Step<M, PB>> = trace.steps.get_mut(*step_index);
        if let Some(step) = step {
            match &mut step.action {
                Action::Input(input) => {
                    find_term_by_term_path_mut(&mut input.recipe, &mut term_path.clone())
                }
                Action::Output(_) => None,
            }
        } else {
            None
        }
    }

    // maybe optimize with for loop
    pub fn replace_in_term<'a, M: Matcher>(
        term: &'a mut Term<M>,
        term_path: &mut TermPath,
        message: Term<M>,
    ) -> Option<()> {
        // term_path is never empty
        let subterm_index = term_path.remove(0);

        if term_path.is_empty() {
            // replace sub term by message
            match term {
                Term::Application(_, subterms) => {
                    subterms[subterm_index] = message;
                    Some(())
                }
                _ => None,
            }
        } else {
            match term {
                Term::Application(_, subterms) => {
                    if let Some(subterm) = subterms.get_mut(subterm_index) {
                        replace_in_term(subterm, term_path, message)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
    }

    pub fn replace<'a, M: Matcher, PB: ProtocolBehavior>(
        trace: &'a mut Trace<M, PB>,
        step_index: StepIndex,
        term_path: TermPath,
        message: Term<M>,
    ) -> Option<&'a mut Trace<M, PB>> {
        let step: Option<&mut Step<M, PB>> = trace.steps.get_mut(step_index);
        if let Some(step) = step {
            match &mut step.action {
                Action::Input(input) => {
                    if term_path.is_empty() {
                        step.action = Action::Input(InputAction { recipe: message });
                        return Some(trace);
                    } else {
                        replace_in_term(&mut input.recipe, &mut term_path.clone(), message);
                        return Some(trace);
                    }
                }
                Action::Output(_) => None,
            }
        } else {
            None
        }
    }

    pub fn choose<'a, R: Rand, M: Matcher, PB: ProtocolBehavior>(
        trace: &'a Trace<M, PB>,
        constraints: TermConstraints,
        rand: &mut R,
    ) -> Option<(&'a Term<M>, (usize, TermPath))> {
        reservoir_sample(trace, |_| true, constraints, rand)
    }

    pub fn choose_mut<'a, R: Rand, M: Matcher, PB: ProtocolBehavior>(
        trace: &'a mut Trace<M, PB>,
        constraints: TermConstraints,
        rand: &mut R,
    ) -> Option<(&'a mut Term<M>, (usize, TermPath))> {
        if let Some(trace_path) = choose_term_path_filtered(trace, |_| true, constraints, rand) {
            if let Some(term) = find_term_mut(trace, &trace_path) {
                Some((term, trace_path))
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn choose_term<'a, R: Rand, M: Matcher, PB: ProtocolBehavior>(
        trace: &'a Trace<M, PB>,
        constraints: TermConstraints,
        rand: &mut R,
    ) -> Option<&'a Term<M>> {
        reservoir_sample(trace, |_| true, constraints, rand).map(|ret| ret.0)
    }

    pub fn choose_term_withfilter<
        'a,
        R: Rand,
        M: Matcher,
        PB: ProtocolBehavior,
        P: Fn(&Term<M>) -> bool + Copy,
    >(
        trace: &'a Trace<M, PB>,
        filter: P,
        constraints: TermConstraints,
        rand: &mut R,
    ) -> Option<(&'a Term<M>, (usize, TermPath))> {
        reservoir_sample(trace, filter, constraints, rand)
    }

    pub fn choose_term_mut<'a, R: Rand, M: Matcher, PB: ProtocolBehavior>(
        trace: &'a mut Trace<M, PB>,
        constraints: TermConstraints,
        rand: &mut R,
    ) -> Option<&'a mut Term<M>> {
        if let Some(trace_path) = choose_term_path_filtered(trace, |_| true, constraints, rand) {
            find_term_mut(trace, &trace_path)
        } else {
            None
        }
    }

    pub fn choose_term_filtered_mut<
        'a,
        R: Rand,
        M: Matcher,
        PB: ProtocolBehavior,
        P: Fn(&Term<M>) -> bool + Copy,
    >(
        trace: &'a mut Trace<M, PB>,
        filter: P,
        constraints: TermConstraints,
        rand: &mut R,
    ) -> Option<&'a mut Term<M>> {
        if let Some(trace_path) = choose_term_path_filtered(trace, filter, constraints, rand) {
            find_term_mut(trace, &trace_path)
        } else {
            None
        }
    }

    pub fn choose_term_path<R: Rand, M: Matcher, PB: ProtocolBehavior>(
        trace: &Trace<M, PB>,
        constraints: TermConstraints,
        rand: &mut R,
    ) -> Option<TracePath> {
        choose_term_path_filtered(trace, |_| true, constraints, rand)
    }

    pub fn choose_term_path_filtered<
        R: Rand,
        M: Matcher,
        PB: ProtocolBehavior,
        P: Fn(&Term<M>) -> bool + Copy,
    >(
        trace: &Trace<M, PB>,
        filter: P,
        constraints: TermConstraints,
        rand: &mut R,
    ) -> Option<TracePath> {
        reservoir_sample(trace, filter, constraints, rand).map(|ret| ret.1)
    }

    pub fn choose_with_weights<'a, R: Rand, M: Matcher, PB: ProtocolBehavior>(
        trace: &'a Trace<M, PB>,
        constraints: TermConstraints,
        rand: &mut R,
    ) -> Option<(&'a Term<M>, TracePath)> {
        weighted_reservoir(trace, constraints, rand)
    }
}

/// ***********************************************************************************************

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use libafl::{
        bolts::rands::{RomuDuoJrRand, StdRand},
        corpus::InMemoryCorpus,
        mutators::{MutationResult, Mutator},
        state::StdState,
    };

    use super::*;
    use crate::{
        agent::AgentName,
        algebra::{
            dynamic_function::DescribableFunction,
            test_signature::{TestTrace, *},
            AnyMatcher, Term,
        },
        trace::{Action, Step},
    };

    fn create_state(
    ) -> StdState<TestTrace, InMemoryCorpus<TestTrace>, RomuDuoJrRand, InMemoryCorpus<TestTrace>>
    {
        let rand = StdRand::with_seed(1235);
        let corpus: InMemoryCorpus<TestTrace> = InMemoryCorpus::new();
        StdState::new(rand, corpus, InMemoryCorpus::new(), &mut (), &mut ()).unwrap()
    }

    /// Checks whether repeat can repeat the last step
    #[test]
    fn test_repeat_mutator() {
        let mut state = create_state();

        let mut mutator = RepeatMutator::new(15);

        fn check_is_encrypt12(step: &Step<AnyMatcher, TestProtocolBehavior>) -> bool {
            if let Action::Input(input) = &step.action {
                if input.recipe.name() == fn_encrypt12.name() {
                    return true;
                }
            }
            false
        }

        loop {
            let mut trace = setup_simple_trace();
            mutator.mutate(&mut state, &mut trace, 0).unwrap();

            let length = trace.steps.len();
            if let Some(last) = trace.steps.get(length - 1) {
                if check_is_encrypt12(last) {
                    if let Some(step) = trace.steps.get(length - 2) {
                        if check_is_encrypt12(step) {
                            break;
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_replace_match_mutator() {
        let _server = AgentName::first();
        let mut state = create_state();
        let mut mutator = ReplaceMatchMutator::new(TermConstraints::default(), &TEST_SIGNATURE);

        loop {
            let mut trace = setup_simple_trace();
            mutator.mutate(&mut state, &mut trace, 0).unwrap();

            if let Some(last) = trace.steps.iter().last() {
                match &last.action {
                    Action::Input(input) => match &input.recipe {
                        Term::Application(_, subterms) => {
                            if let Some(last_subterm) = subterms.iter().last() {
                                if last_subterm.name() == fn_seq_1.name() {
                                    break;
                                }
                            }
                        }
                        _ => {}
                    },
                    Action::Output(_) => {}
                }
            }
        }
    }

    #[test]
    fn test_remove_lift_mutator() {
        // Should remove an extension
        let mut state = create_state();
        let _server = AgentName::first();
        let mut mutator = RemoveAndLiftMutator::new(TermConstraints::default());

        // Returns the amount of extensions in the trace
        fn sum_extension_appends(trace: &TestTrace) -> usize {
            trace.count_functions_by_name(fn_client_extensions_append.name())
        }

        loop {
            let mut trace = setup_simple_trace();
            let before_mutation = sum_extension_appends(&trace);
            let result = mutator.mutate(&mut state, &mut trace, 0).unwrap();

            if let MutationResult::Mutated = result {
                let after_mutation = sum_extension_appends(&trace);
                if after_mutation < before_mutation {
                    // extension removed
                    break;
                }
            }
        }
    }

    #[test]
    fn test_replace_reuse_mutator() {
        let mut state = create_state();
        let _server = AgentName::first();
        let mut mutator = ReplaceReuseMutator::new(TermConstraints::default());

        fn count_client_hello(trace: &TestTrace) -> usize {
            trace.count_functions_by_name(fn_client_hello.name())
        }

        fn count_finished(trace: &TestTrace) -> usize {
            trace.count_functions_by_name(fn_finished.name())
        }

        loop {
            let mut trace = setup_simple_trace();
            let result = mutator.mutate(&mut state, &mut trace, 0).unwrap();

            if let MutationResult::Mutated = result {
                let client_hellos = count_client_hello(&trace);
                let finishes = count_finished(&trace);
                if client_hellos == 2 && finishes == 0 {
                    // finished replaced by client_hello
                    break;
                }
            }
        }
    }

    #[test]
    fn test_skip_mutator() {
        let mut state = create_state();
        let _server = AgentName::first();
        let mut mutator = SkipMutator::new(2);

        loop {
            let mut trace = setup_simple_trace();
            let before_len = trace.steps.len();
            mutator.mutate(&mut state, &mut trace, 0).unwrap();

            if before_len - 1 == trace.steps.len() {
                break;
            }
        }
    }

    #[test]
    fn test_swap_mutator() {
        let mut state = create_state();
        let mut mutator = SwapMutator::new(TermConstraints::default());

        loop {
            let mut trace = setup_simple_trace();
            mutator.mutate(&mut state, &mut trace, 0).unwrap();

            let is_first_not_ch = if let Some(first) = trace.steps.get(0) {
                match &first.action {
                    Action::Input(input) => Some(input.recipe.name() != fn_client_hello.name()),
                    Action::Output(_) => None,
                }
            } else {
                None
            };

            let is_next_not_fn_client_key_exchange = if let Some(next) = trace.steps.get(1) {
                match &next.action {
                    Action::Input(input) => {
                        Some(input.recipe.name() != fn_client_key_exchange.name())
                    }
                    Action::Output(_) => None,
                }
            } else {
                None
            };

            if let Some(first) = is_first_not_ch {
                if let Some(second) = is_next_not_fn_client_key_exchange {
                    if first && second {
                        break;
                    }
                }
            }
        }
    }

    #[test]
    fn test_find_term() {
        let mut rand = StdRand::with_seed(45);
        let mut trace = setup_simple_trace();
        let term_size = trace.count_functions();

        let mut stats: HashSet<TracePath> = HashSet::new();

        for _ in 0..10000 {
            let path = choose_term_path(&trace, TermConstraints::default(), &mut rand).unwrap();
            find_term_mut(&mut trace, &path).unwrap();
            stats.insert(path);
        }

        assert_eq!(term_size, stats.len());
    }

    #[test]
    fn test_reservoir_sample_randomness() {
        /// https://rust-lang-nursery.github.io/rust-cookbook/science/mathematics/statistics.html#standard-deviation
        fn std_deviation(data: &[u32]) -> Option<f32> {
            fn mean(data: &[u32]) -> Option<f32> {
                let sum = data.iter().sum::<u32>() as f32;
                let count = data.len();

                match count {
                    positive if positive > 0 => Some(sum / count as f32),
                    _ => None,
                }
            }

            match (mean(data), data.len()) {
                (Some(data_mean), count) if count > 0 => {
                    let variance = data
                        .iter()
                        .map(|value| {
                            let diff = data_mean - (*value as f32);

                            diff * diff
                        })
                        .sum::<f32>()
                        / count as f32;

                    Some(variance.sqrt())
                }
                _ => None,
            }
        }

        let trace = setup_simple_trace();
        let term_size = trace.count_functions();

        let mut rand = StdRand::with_seed(45);
        let mut stats: HashMap<u32, u32> = HashMap::new();

        for _ in 0..10000 {
            let term = choose(&trace, TermConstraints::default(), &mut rand).unwrap();

            let id = term.0.resistant_id();

            let count: u32 = *stats.get(&id).unwrap_or(&0);
            stats.insert(id, count + 1);
        }

        let std_dev =
            std_deviation(stats.values().cloned().collect::<Vec<u32>>().as_slice()).unwrap();
        /*        println!("{:?}", std_dev);
        println!("{:?}", stats);*/

        assert!(std_dev < 30.0);
        assert_eq!(term_size, stats.len());
    }

    #[test]
    fn test_weightedreservoir_sample_randomness() {
        /// https://rust-lang-nursery.github.io/rust-cookbook/science/mathematics/statistics.html#standard-deviation
        fn std_deviation(data: &[u32]) -> Option<f32> {
            fn mean(data: &[u32]) -> Option<f32> {
                let sum = data.iter().sum::<u32>() as f32;
                let count = data.len();

                match count {
                    positive if positive > 0 => Some(sum / count as f32),
                    _ => None,
                }
            }

            match (mean(data), data.len()) {
                (Some(data_mean), count) if count > 0 => {
                    let variance = data
                        .iter()
                        .map(|value| {
                            let diff = data_mean - (*value as f32);

                            diff * diff
                        })
                        .sum::<f32>()
                        / count as f32;

                    Some(variance.sqrt())
                }
                _ => None,
            }
        }

        let wanted_height = 2;

        let trace = setup_simple_trace();
        let term_size = trace.count_functions();

        let mut rand = StdRand::with_seed(45);
        let mut stats: HashMap<u32, u32> = HashMap::new();

        for _ in 0..10000 {
            let term = choose_with_weights(&trace, TermConstraints::default(), &mut rand).unwrap();

            if term.0.height() == wanted_height {
                let id = term.0.resistant_id();

                let count: u32 = *stats.get(&id).unwrap_or(&0);
                stats.insert(id, count + 1);
            }
        }

        let std_dev =
            std_deviation(stats.values().cloned().collect::<Vec<u32>>().as_slice()).unwrap();
        /*        println!("{:?}", std_dev);
        println!("{:?}", stats);*/

        assert!(std_dev < 30.0);
        // assert_eq!(term_size, stats.len());
    }

    #[test]
    fn test_weightedreservoir() {
        let trace = setup_simple_trace();
        let mut gather_heights: HashMap<u32, u32> = HashMap::new();
        for step in &trace.steps {
            match &step.action {
                Action::Input(inp) => {
                    let mut q = vec![&inp.recipe];
                    while !q.is_empty() {
                        let term = q.pop().unwrap();
                        match term {
                            Term::Application(_, subterms) => q.extend(subterms.iter().clone()),
                            _ => {}
                        }
                        let h = term.height() as u32;
                        let count: u32 = *gather_heights.get(&h).unwrap_or(&0);
                        gather_heights.insert(h, count + 1);
                    }
                }
                Action::Output(_) => {}
            }
        }
        let mut rand = StdRand::with_seed(45);
        let mut stats: HashMap<(u32, u32), u32> = HashMap::new();
        for _ in 0..10000 {
            let (term, _) =
                choose_with_weights(&trace, TermConstraints::default(), &mut rand).unwrap();
            let l = term.height() as u32;
            let id = term.resistant_id();
            let count: u32 = *stats.get(&(id, l)).unwrap_or(&0);
            stats.insert((id, l), count + 1);
        }
        println!("{:?}", gather_heights);
        for ((id, h), count) in stats {
            println!("{} of height {} visited {} times \n", id, h, count);
        }
    }
}
