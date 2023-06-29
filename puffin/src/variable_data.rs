//! Definition of the VariableData trait. A VariableData can contain any data which has a `'static`
//! type.

use std::{
    any::{Any, TypeId},
    fmt::Debug,
    hash::{Hash, Hasher},
};

use serde::{Deserialize, Serialize};

// use libafl::inputs::HasBytesVec;

// use crate::algebra::{atoms::Variable, Matcher};

#[typetag::serde(tag = "type")]
pub trait VariableData: Debug {
    fn boxed(&self) -> Box<dyn VariableData>;
    fn boxed_any(&self) -> Box<dyn Any>;
    fn type_id(&self) -> TypeId;
    fn type_name(&self) -> &'static str;
}

/// A VariableData is cloneable and has a `'static` type. This data type is used throughout
/// tlspuffin to handle data of dynamic size.

#[typetag::serde]
impl<T: 'static> VariableData for T
where
    T: Debug + Serialize + Deserialize,
{
    fn boxed(&self) -> Box<dyn VariableData> {
        Box::new(self.clone())
    }

    fn boxed_any(&self) -> Box<dyn Any> {
        Box::new(self.clone())
    }

    fn type_id(&self) -> TypeId {
        Any::type_id(self)
    }

    fn type_name(&self) -> &'static str {
        std::any::type_name::<T>()
    }
}

// implementations for box

#[derive(Debug, Serialize, Deserialize)]
pub struct GlobalVariableData(pub Box<dyn VariableData>);

/* impl GlobalVariableData {
    pub fn new(data: dyn VariableData) -> GlobalVariableData {
        GlobalVariableData(Box::new(data))
    }
} */

impl Clone for GlobalVariableData {
    fn clone(&self) -> Self {
        self.clone()
    }
}

impl Hash for GlobalVariableData {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash(state)
    }
}
impl GlobalVariableData {
    pub fn as_ref(&self) -> &dyn VariableData {
        self.0.as_ref()
    }

    pub fn type_name(&self) -> &'static str {
        self.0.type_name()
    }
}
