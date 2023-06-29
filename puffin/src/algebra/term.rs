//! This module provides[`Term`]sas well as iterators over them.

use std::{any::Any, fmt, fmt::Formatter, slice};

use itertools::Itertools;
use serde::{Deserialize, Serialize};

use super::atoms::{Function, Message, Variable};
use crate::{
    algebra::{dynamic_function::TypeShape, error::FnError, Matcher},
    error::Error,
    fuzzer::mutations::util::{TermPath, TracePath},
    protocol::ProtocolBehavior,
    trace::{Action, Knowledge, Step, Trace, TraceContext},
    variable_data::VariableData,
};

/// A first-order term: either a [`Variable`] or an application of an [`Function`].
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, Hash)]
#[serde(bound = "M: Matcher")]
pub enum Term<M: Matcher, PB: ProtocolBehavior> {
    /// A concrete but unspecified `Term` (e.g. `x`, `y`).
    /// See [`Variable`] for more information.
    ///
    Variable(Variable<M>),
    /// An [`Function`] applied to zero or more `Term`s (e.g. `f(x, y)`, `g()`).
    ///
    /// A `Term` that is an application of an [`Function`] with arity 0 applied to 0 `Term`s can be considered a constant.
    ///
    Application(Function, Vec<Term<M, PB>>),
    ///An opaque message
    Message(Message<PB>),
}

impl<M: Matcher, PB: ProtocolBehavior> fmt::Display for Term<M, PB> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_at_depth(0))
    }
}

impl<M: Matcher, PB: ProtocolBehavior> Term<M, PB> {
    pub fn resistant_id(&self) -> u32 {
        match self {
            Term::Variable(v) => v.resistant_id,
            Term::Application(f, _) => f.resistant_id,
            Term::Message(m) => m.resistant_id,
        }
    }

    pub fn size(&self) -> usize {
        match self {
            Term::Application(_, ref subterms) => {
                subterms.iter().map(|subterm| subterm.size()).sum::<usize>() + 1
            }
            _ => 1,
        }
    }

    pub fn is_leaf(&self) -> bool {
        match self {
            Term::Application(_, ref subterms) => {
                subterms.is_empty() // constant
            }
            _ => true,
        }
    }

    pub fn get_type_shape(&self) -> &TypeShape {
        match self {
            Term::Variable(v) => &v.typ,
            Term::Application(function, _) => &function.shape().return_type,
            Term::Message(m) => &m.typ,
        }
    }

    pub fn name(&self) -> &str {
        match self {
            Term::Variable(v) => v.typ.name,
            Term::Application(function, _) => function.name(),
            // micol : would like to change next line to know it is a message
            Term::Message(m) => m.typ.name,
        }
    }

    pub fn mutate(&mut self, other: Term<M, PB>) {
        *self = other;
    }

    fn display_at_depth(&self, depth: usize) -> String {
        let tabs = "\t".repeat(depth);
        match self {
            Term::Variable(ref v) => format!("Variable {}{}", tabs, v),
            Term::Application(ref func, ref args) => {
                let op_str = remove_prefix(func.name());
                let return_type = remove_prefix(func.shape().return_type.name);
                if args.is_empty() {
                    format!("{}{} -> {}", tabs, op_str, return_type)
                } else {
                    let args_str = args
                        .iter()
                        .map(|arg| arg.display_at_depth(depth + 1))
                        .join(",\n");
                    format!(
                        "{}{}(\n{}\n{}) -> {}",
                        tabs, op_str, args_str, tabs, return_type
                    )
                }
            }
            Term::Message(ref m) => format!("Message {}{}", tabs, m),
        }
    }

    /* pub fn follow_termpath(
            &self,
            path: TermPath,
            new_term: Term<M, PB>,
        ) -> Term<M, PB> {
            match self {
                Term::Variable(_) => new_term,
                Term::Application(f, terms) => {
                    if let n = path.pop{
                        if path.is_empty(){
                            terms[]
                        }
                    } else {
                        panic!()
                    }
                }
            }
        }

         // replaces sub-term in tree with a message
        pub fn replace(
            &self,
            trace: Trace<M>,
            path: TermPath,
            msg: <PB as ProtocolBehavior>::ProtocolMessage,
        ) -> Term<M, PB> {
            match trace.steps[path.0].action {
                Action::Output(_) => panic!("reservoir sample chose an output ?"),
                Action::Input(term) => {
                    let term = term.recipe;
                    let new_term = Message(Message {
                        unique_id: term.unique_id_term(),
                        resistant_id: term.resistant_id(),
                        message: msg,
                    });
                    term.follow_termpath(path, new_term)
                }
            }
        }

        // replaces sub-term in tree with an opaque message
        pub fn replace_opaque(
            &self,
            trace: Trace<M>,
            path: TracePath,
            msg: <PB as ProtocolBehavior>::ProtocolMessage,
        ) -> Term<M, PB> {
        }
    */
    pub fn evaluate<P: ProtocolBehavior>(
        &self,
        context: &TraceContext<P>,
    ) -> Result<Box<dyn Any>, Error>
    where
        P: ProtocolBehavior<Matcher = M>,
    {
        match self {
            Term::Variable(variable) => context
                .find_variable(variable.typ, &variable.query)
                .map(|data| data.boxed_any())
                .or_else(|| context.find_claim(variable.query.agent_name, variable.typ))
                .ok_or_else(|| Error::Term(format!("Unable to find variable {}!", variable))),
            Term::Application(func, args) => {
                let mut dynamic_args: Vec<Box<dyn Any>> = Vec::new();
                for term in args {
                    match term.evaluate(context) {
                        Ok(data) => {
                            dynamic_args.push(data);
                        }
                        Err(e) => {
                            return Err(e);
                        }
                    }
                }
                let dynamic_fn = &func.dynamic_fn();
                let result: Result<Box<dyn Any>, FnError> = dynamic_fn(&dynamic_args);
                result.map_err(Error::Fn)
            }
            Term::Message(msg) => Ok(msg.message.boxed_any()),
        }
    }
}

fn append<'a, M: Matcher, PB: ProtocolBehavior>(
    term: &'a Term<M, PB>,
    v: &mut Vec<&'a Term<M, PB>>,
) {
    match *term {
        Term::Application(_, ref subterms) => {
            for subterm in subterms {
                append(subterm, v);
            }
        }
        _ => {} // ?
    }

    v.push(term);
}

/// Having the same mutator for &'a mut Term is not possible in Rust:
/// * https://stackoverflow.com/questions/49057270/is-there-a-way-to-iterate-over-a-mutable-tree-to-get-a-random-node
/// * https://sachanganesh.com/programming/graph-tree-traversals-in-rust/
impl<'a, M: Matcher, PB: ProtocolBehavior> IntoIterator for &'a Term<M, PB> {
    type Item = &'a Term<M, PB>;
    type IntoIter = std::vec::IntoIter<&'a Term<M, PB>>;

    fn into_iter(self) -> Self::IntoIter {
        let mut result = vec![];
        append::<M, PB>(self, &mut result);
        result.into_iter()
    }
}

pub trait Subterms<M: Matcher, PB: ProtocolBehavior> {
    fn find_subterm_same_shape(&self, term: &Term<M, PB>) -> Option<&Term<M, PB>>;

    fn find_subterm<P: Fn(&&Term<M, PB>) -> bool + Copy>(&self, filter: P) -> Option<&Term<M, PB>>;

    fn filter_grand_subterms<P: Fn(&Term<M, PB>, &Term<M, PB>) -> bool + Copy>(
        &self,
        predicate: P,
    ) -> Vec<((usize, &Term<M, PB>), &Term<M, PB>)>;
}

impl<M: Matcher, PB: ProtocolBehavior> Subterms<M, PB> for Vec<Term<M, PB>> {
    /// Finds a subterm with the same type as `term`
    fn find_subterm_same_shape(&self, term: &Term<M, PB>) -> Option<&Term<M, PB>> {
        self.find_subterm(|subterm| term.get_type_shape() == subterm.get_type_shape())
    }

    /// Finds a subterm in this vector
    fn find_subterm<P: Fn(&&Term<M, PB>) -> bool + Copy>(
        &self,
        predicate: P,
    ) -> Option<&Term<M, PB>> {
        self.iter().find(predicate)
    }

    /// Finds all grand children/subterms which match the predicate.
    ///
    /// A grand subterm is defined as a subterm of a term in `self`.
    ///
    /// Each grand subterm is returned together with its parent and the index of the parent in `self`.
    fn filter_grand_subterms<P: Fn(&Term<M, PB>, &Term<M, PB>) -> bool + Copy>(
        &self,
        predicate: P,
    ) -> Vec<((usize, &Term<M, PB>), &Term<M, PB>)> {
        let mut found_grand_subterms = vec![];

        for (i, subterm) in self.iter().enumerate() {
            match &subterm {
                Term::Application(_, grand_subterms) => {
                    found_grand_subterms.extend(
                        grand_subterms
                            .iter()
                            .filter(|grand_subterm| predicate(subterm, grand_subterm))
                            .map(|grand_subterm| ((i, subterm), grand_subterm)),
                    );
                }
                _ => {}
            };
        }

        found_grand_subterms
    }
}

/// `tlspuffin::term::op_impl::op_protocol_version` -> `op_protocol_version`
/// `alloc::Vec<rustls::msgs::handshake::ServerExtension>` -> `Vec<rustls::msgs::handshake::ServerExtension>`
pub(crate) fn remove_prefix(str: &str) -> String {
    let split: Option<(&str, &str)> = str.split('<').collect_tuple();

    if let Some((non_generic, generic)) = split {
        let generic = &generic[0..generic.len() - 1];

        if let Some(pos) = non_generic.rfind("::") {
            non_generic[pos + 2..].to_string() + "<" + &remove_prefix(generic) + ">"
        } else {
            non_generic.to_string() + "<" + &remove_prefix(generic) + ">"
        }
    } else if let Some(pos) = str.rfind("::") {
        str[pos + 2..].to_string()
    } else {
        str.to_string()
    }
}

pub(crate) fn remove_fn_prefix(str: &str) -> String {
    str.replace("fn_", "")
}

#[cfg(test)]
mod tests {
    use crate::algebra::remove_prefix;

    #[test]
    fn test_normal() {
        assert_eq!(remove_prefix("test::test::Test"), "Test");
    }

    #[test]
    fn test_generic() {
        assert_eq!(remove_prefix("test::test::Test<Asdf>"), "Test<Asdf>");
    }

    #[test]
    fn test_generic_recursive() {
        assert_eq!(remove_prefix("test::test::Test<asdf::Asdf>"), "Test<Asdf>");
    }
}
