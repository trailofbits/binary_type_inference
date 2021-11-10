use std::vec::Vec;

#[derive(Debug, Clone)]
pub struct TypeVariable {
    name: String,
}

pub struct VariableManager {
    curr_id: u64,
}

impl VariableManager {
    pub fn new() -> VariableManager {
        VariableManager { curr_id: 0 }
    }

    pub fn fresh(&mut self) -> TypeVariable {
        let next_name = format!("τ{}", self.curr_id.to_string());
        self.curr_id += 1;
        TypeVariable { name: next_name }
    }
}

impl Default for VariableManager {
    fn default() -> Self {
        VariableManager::new()
    }
}

#[derive(Debug, Clone)]
pub struct Deref {
    offset: i64,
    size: u64,
}

#[derive(Debug, Clone)]
pub struct In {
    param_index: u32,
}

#[derive(Debug, Clone)]
pub enum FieldLabel {
    Load,
    Store,
    In(In),
    Out,
    Deref(Deref),
}

#[derive(Debug, Clone)]
pub struct DerivedTypeVar {
    var: TypeVariable,
    labels: Vec<FieldLabel>,
}

#[derive(Debug, Clone)]
pub struct SubtypeConstraint {
    lhs: DerivedTypeVar,
    rhs: DerivedTypeVar,
}
