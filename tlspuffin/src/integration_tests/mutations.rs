use std::fmt::Display;

use libafl::state::HasRand;
use puffin::{
    agent::AgentName,
    algebra::{dynamic_function::DescribableFunction, Term},
    fuzzer::{
        harness::{default_put_options, set_default_put_options},
        mutations::{
            util::{choose, choose_term, TermConstraints},
            BitFlip, MakeMessage, RemoveAndLiftMutator, RepeatMutator, ReplaceMatchMutator,
            ReplaceReuseMutator,
        },
    },
    libafl::{
        bolts::rands::{RomuDuoJrRand, StdRand},
        corpus::InMemoryCorpus,
        mutators::{MutationResult, Mutator},
        state::StdState,
    },
    protocol::ProtocolBehavior,
    put::PutOptions,
    term,
    trace::{Action, InputAction, Step, Trace, TraceContext},
};

use crate::{
    protocol::TLSProtocolBehavior,
    put_registry::TLS_PUT_REGISTRY,
    query::TlsQueryMatcher,
    test_utils::expect_crash,
    tls::{
        fn_impl::{
            fn_client_hello, fn_encrypt12, fn_seq_0, fn_seq_1, fn_sign_transcript,
            fn_signature_algorithm_extension, fn_support_group_extension,
        },
        seeds::_seed_client_attacker12,
        TLS_SIGNATURE,
    },
};

fn create_state() -> StdState<
    Trace<TlsQueryMatcher, TLSProtocolBehavior>,
    InMemoryCorpus<Trace<TlsQueryMatcher, TLSProtocolBehavior>>,
    RomuDuoJrRand,
    InMemoryCorpus<Trace<TlsQueryMatcher, TLSProtocolBehavior>>,
> {
    let rand = StdRand::with_seed(1235);
    let corpus: InMemoryCorpus<Trace<_, _>> = InMemoryCorpus::new();
    StdState::new(rand, corpus, InMemoryCorpus::new(), &mut (), &mut ()).unwrap()
}

#[test]
#[ignore]
fn test_mutate_seed_cve_2021_3449() {
    let mut state = create_state();
    let _server = AgentName::first();

    expect_crash(move || {
        for _i in 0..5 {
            let mut attempts = 0;

            let (mut trace, _) = _seed_client_attacker12(AgentName::first());

            // Check if we can append another encrypted message

            let mut mutator = RepeatMutator::new(15);

            fn check_is_encrypt12(step: &Step<TlsQueryMatcher, TLSProtocolBehavior>) -> bool {
                if let Action::Input(input) = &step.action {
                    if input.recipe.name() == fn_encrypt12.name() {
                        return true;
                    }
                }
                false
            }

            loop {
                attempts += 1;
                let mut mutate = trace.clone();
                mutator.mutate(&mut state, &mut mutate, 0).unwrap();

                let length = mutate.steps.len();
                if let Some(last) = mutate.steps.get(length - 1) {
                    if check_is_encrypt12(last) {
                        if let Some(step) = mutate.steps.get(length - 2) {
                            if check_is_encrypt12(step) {
                                trace = mutate;
                                break;
                            }
                        }
                    }
                }
            }
            println!("attempts 1: {}", attempts);
            attempts = 0;

            // Check if we have a client hello in last encrypted one

            let constraints = TermConstraints {
                min_term_size: 0,
                max_term_size: 300,
            };
            let mut mutator = ReplaceReuseMutator::new(constraints);

            loop {
                attempts += 1;
                let mut mutate = trace.clone();
                mutator.mutate(&mut state, &mut mutate, 0).unwrap();

                if let Some(last) = mutate.steps.iter().last() {
                    match &last.action {
                        Action::Input(input) => match &input.recipe {
                            Term::Application(_, subterms) => {
                                if let Some(first_subterm) = subterms.iter().next() {
                                    if first_subterm.name() == fn_client_hello.name() {
                                        trace = mutate;
                                        break;
                                    }
                                }
                            }
                            _ => {} // invalidates ???
                        },
                        Action::Output(_) => {}
                    }
                }
            }
            println!("attempts 2: {}", attempts);
            attempts = 0;

            // Test if we can replace the sequence number

            let mut mutator = ReplaceMatchMutator::new(constraints, &TLS_SIGNATURE);

            loop {
                attempts += 1;
                let mut mutate = trace.clone();
                mutator.mutate(&mut state, &mut mutate, 0).unwrap();

                if let Some(last) = mutate.steps.iter().last() {
                    match &last.action {
                        Action::Input(input) => match &input.recipe {
                            Term::Application(_, subterms) => {
                                if let Some(last_subterm) = subterms.iter().last() {
                                    if last_subterm.name() == fn_seq_1.name() {
                                        trace = mutate;
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
            println!("attempts 3: {}", attempts);
            attempts = 0;

            // Remove sig algo

            let mut mutator = RemoveAndLiftMutator::new(constraints);

            loop {
                attempts += 1;
                let mut mutate = trace.clone();
                let result = mutator.mutate(&mut state, &mut mutate, 0).unwrap();

                if let MutationResult::Mutated = result {
                    if let Some(last) = mutate.steps.iter().last() {
                        match &last.action {
                            Action::Input(input) => match &input.recipe {
                                Term::Application(_, subterms) => {
                                    if let Some(first_subterm) = subterms.iter().next() {
                                        let sig_alg_extensions = first_subterm
                                            .count_functions_by_name(
                                                fn_signature_algorithm_extension.name(),
                                            );
                                        let support_groups_extensions = first_subterm
                                            .count_functions_by_name(
                                                fn_support_group_extension.name(),
                                            );
                                        if sig_alg_extensions == 0 && support_groups_extensions == 1
                                        {
                                            trace = mutate;
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
            println!("attempts 4: {}", attempts);
            attempts = 0;

            // Sucessfully renegotiate

            let mut mutator = ReplaceReuseMutator::new(constraints);

            loop {
                attempts += 1;
                let mut mutate = trace.clone();
                mutator.mutate(&mut state, &mut mutate, 0).unwrap();

                if let Some(last) = mutate.steps.iter().last() {
                    match &last.action {
                        Action::Input(input) => match &input.recipe {
                            Term::Application(_, subterms) => {
                                if let Some(first_subterm) = subterms.iter().next() {
                                    let signatures = first_subterm
                                        .count_functions_by_name(fn_sign_transcript.name());
                                    if signatures == 1 {
                                        trace = mutate;
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
            println!("attempts 5: {}", attempts);
            attempts = 0;

            let mut context = TraceContext::new(&TLS_PUT_REGISTRY, PutOptions::default());
            let _ = trace.execute(&mut context);
            println!("try");
        }
    });
}

#[test]
fn test_execute() {
    let mut state = create_state();
    let (mut trace, _) = _seed_client_attacker12(AgentName::first());
    let mut mutator = RemoveAndLiftMutator::new(TermConstraints::default());
    mutator.mutate(&mut state, &mut trace, 0);
    let mut ctx = TraceContext::new(ProtocolBehavior::registry(), default_put_options().clone());
    match trace.execute(&mut ctx) {
        Ok(_) => {}
        Err(error) => panic!("failed execution : {}", error),
    }
}

#[test]
fn test_makemessage() {
    let mut state = create_state();
    let _server = AgentName::first();
    let mut options: Vec<(String, String)> = Vec::new();
    set_default_put_options(PutOptions::new(options)).expect("failed to set default PUT options");
    let mut mutator = MakeMessage::new(TermConstraints::default());

    for _ in 0..100 {
        let (mut trace, _) = _seed_client_attacker12(AgentName::first());
        mutator.mutate(&mut state, &mut trace, 0);
    }

    /*let mut a = false;
    while !a {
        match mutator.mutate(&mut state, &mut trace, 0) {
            Ok(MutationResult::Mutated) => a = true,
            Ok(MutationResult::Skipped) => a = false,
            Err(error) => panic!("mutation failed : {}", error),
        }
    }

    //check to see if there is a Message now
    let mut a = false;

    for step in trace.steps.clone() {
        match step.action {
            Action::Input(input) => {
                let term = input.recipe;
                let mut q = vec![term];
                while !q.is_empty() {
                    if let Some(term) = q.pop() {
                        match term {
                            Term::Message(_) => {
                                a = true;
                                println!("i found a message !")
                            }
                            Term::Application(_, subterms) => {
                                for t in subterms {
                                    q.push(t);
                                }
                            }
                            _ => {}
                        }
                    } else {
                        panic!("q is empty")
                    }
                }
            }
            Action::Output(_) => {}
        }
    }

    if a == false {
        panic!("No message created")
    }

    let mut mutator = BitFlip::new();

    match mutator.mutate(&mut state, &mut trace, 1) {
        Ok(result) => {
            if result == MutationResult::Skipped {
                panic!("there was a message, but it skipped")
            }
        }
        Err(error) => panic!("Failed BitFlip mutation : {}", error),
    }*/
}
