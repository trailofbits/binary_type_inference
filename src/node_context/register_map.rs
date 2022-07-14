use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use std::fmt::Display;
use std::ops::Deref;
use std::rc::Rc;

use cwe_checker_lib::abstract_domain::DomainMap;
use cwe_checker_lib::analysis::graph::{Graph, Node};
use cwe_checker_lib::analysis::interprocedural_fixpoint_generic::NodeValue;
use cwe_checker_lib::intermediate_representation::{Program, Project, Term, Variable};
use petgraph::graph::NodeIndex;
use petgraph::EdgeDirection::Incoming;

use crate::analysis;
use crate::analysis::reaching_definitions::{
    self, Context, Definition, ImplicitBottomMappingDomain, TermSet,
};
use crate::constraint_generation::{self, NodeContextMapping, RegisterMapping};
use crate::constraints::TypeVariable;

use cwe_checker_lib::analysis::forward_interprocedural_fixpoint;
use cwe_checker_lib::intermediate_representation::Def;

/// The context of register definitions for a given program ICFG node.
#[derive(Clone)]
pub struct RegisterContext {
    mapping: BTreeMap<Variable, TermSet>,
    program: Rc<Term<Program>>,
}

impl Display for RegisterContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (v, tset) in self.mapping.iter() {
            writeln!(f, "{}: {}", v.name, tset)?;
        }
        Ok(())
    }
}

impl RegisterContext {
    /// Creates a new register context that can answer register access queries from a reaching definitions [NodeValue].
    pub fn new(
        mapping: BTreeMap<Variable, TermSet>,
        program: &Rc<Term<Program>>,
    ) -> RegisterContext {
        RegisterContext {
            mapping,
            program: program.clone(),
        }
    }

    fn generate_multi_def_constraint(
        defined_var: &Variable,
        defs: &TermSet,
    ) -> BTreeSet<TypeVariable> {
        defs.0
            .iter()
            .map(|def| RegisterContext::type_variable_from_def(def, defined_var))
            .collect::<BTreeSet<TypeVariable>>()
    }

    fn type_variable_from_def(def: &Definition, defined_variable: &Variable) -> TypeVariable {
        match def {
            Definition::Normal(tid) => {
                constraint_generation::tid_indexed_by_variable(tid, defined_variable)
            }
            Definition::ActualRet(tid, _i) => {
                constraint_generation::tid_indexed_by_variable(tid, defined_variable)
            }
            &Definition::EntryFresh(i) => TypeVariable::new(format!("entry_fresh_definition{}", i)),
        }
    }

    /// Gets the underyling mapping for this context, mapping a variable to a set of terms.
    pub fn get_register_context(&self) -> &BTreeMap<Variable, TermSet> {
        &self.mapping
    }
}

impl NodeContextMapping for RegisterContext {
    fn apply_def(&self, term: &cwe_checker_lib::intermediate_representation::Term<Def>) -> Self {
        let new_mapping = analysis::reaching_definitions::apply_def(
            ImplicitBottomMappingDomain(DomainMap::from(self.mapping.clone())),
            term,
        );

        RegisterContext {
            mapping: new_mapping.deref().deref().clone(),
            program: self.program.clone(),
        }
    }

    fn apply_return_node(
        &self,
        call_term: &cwe_checker_lib::intermediate_representation::Term<
            cwe_checker_lib::intermediate_representation::Jmp,
        >,
        _return_term: &cwe_checker_lib::intermediate_representation::Term<
            cwe_checker_lib::intermediate_representation::Jmp,
        >,
    ) -> Self {
        let new_mapping = reaching_definitions::apply_return(
            Some(&ImplicitBottomMappingDomain(DomainMap::from(
                self.mapping.clone(),
            ))),
            call_term,
            &self.program,
        );

        RegisterContext {
            mapping: new_mapping.deref().deref().clone(),
            program: self.program.clone(),
        }
    }
}

impl RegisterMapping for RegisterContext {
    fn access(&self, var: &Variable) -> BTreeSet<crate::constraints::TypeVariable> {
        let ts = self.mapping.get(var);

        ts.map(|x| Self::generate_multi_def_constraint(var, x))
            .unwrap_or_default()
    }
}

fn generate_fresh_definition(proj: &Project, curr_id: &mut usize) -> BTreeMap<Variable, TermSet> {
    let mut bottom_btree = BTreeMap::new();
    for reg in proj.register_set.iter() {
        let mut st = TermSet::new();
        st.insert(Definition::EntryFresh(*curr_id));
        bottom_btree.insert(reg.clone(), st);
        *curr_id += 1;
    }

    bottom_btree
}

/// Runs reaching definitions on the project and produces a mapping from node index to the Register Context.
/// The register context can be queried to determine the representing type variable for an accessed register
pub fn run_analysis(proj: &Project, graph: &Graph) -> HashMap<NodeIndex, RegisterContext> {
    let cont = Context::new(proj, graph, &proj.program.term.extern_symbols);
    let mut computation = forward_interprocedural_fixpoint::create_computation(cont, None);

    let entry_sub_to_entry_node_map =
        cwe_checker_lib::analysis::graph::get_entry_nodes_of_subs(graph);

    let speculative_points = graph
        .node_indices()
        .filter(|nd_idx| graph.edges_directed(*nd_idx, Incoming).count() == 0);

    let mut curr_id = 0;

    let entry_points = entry_sub_to_entry_node_map
        .into_iter()
        .map(|(_sub_tid, ndidx)| ndidx)
        .chain(speculative_points)
        .collect::<HashSet<_>>();
    for start_node_index in entry_points.iter() {
        computation.set_node_value(
            *start_node_index,
            cwe_checker_lib::analysis::interprocedural_fixpoint_generic::NodeValue::Value(
                ImplicitBottomMappingDomain(DomainMap::from(generate_fresh_definition(
                    proj,
                    &mut curr_id,
                ))),
            ),
        );
    }

    computation.compute();
    let prog = Rc::new(proj.program.clone());
    computation
        .node_values()
        .iter()
        .filter_map(|(ind, dom_map)| match dom_map {
            NodeValue::CallFlowCombinator {
                call_stub,
                interprocedural_flow,
            } => (if interprocedural_flow.is_some() {
                interprocedural_flow
            } else {
                call_stub
            })
            .as_ref()
            .map(|v| (*ind, RegisterContext::new(v.deref().deref().clone(), &prog))),
            NodeValue::Value(v) => {
                Some((*ind, RegisterContext::new(v.deref().deref().clone(), &prog)))
            }
        })
        .collect()
}
