use std::collections::{BTreeMap, BTreeSet, HashMap};

use std::fmt::Display;
use std::ops::Deref;

use cwe_checker_lib::abstract_domain::DomainMap;
use cwe_checker_lib::analysis::graph::Graph;
use cwe_checker_lib::analysis::interprocedural_fixpoint_generic::NodeValue;
use cwe_checker_lib::intermediate_representation::{Project, Variable};
use petgraph::graph::NodeIndex;
use petgraph::EdgeDirection::Incoming;

use crate::analysis;
use crate::analysis::reaching_definitions::{Context, Definition, TermSet};
use crate::constraint_generation::{self, NodeContextMapping, RegisterMapping};
use crate::constraints::TypeVariable;

use cwe_checker_lib::analysis::forward_interprocedural_fixpoint;
use cwe_checker_lib::intermediate_representation::Def;

/// The context of register definitions for a given program ICFG node.
#[derive(Clone)]
pub struct RegisterContext {
    mapping: BTreeMap<Variable, TermSet>,
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
    pub fn new(mapping: BTreeMap<Variable, TermSet>) -> RegisterContext {
        RegisterContext { mapping }
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
        let new_mapping =
            analysis::reaching_definitions::apply_def(DomainMap::from(self.mapping.clone()), term);

        RegisterContext {
            mapping: new_mapping.deref().clone(),
        }
    }
}

impl RegisterMapping for RegisterContext {
    fn access(&self, var: &Variable) -> BTreeSet<crate::constraints::TypeVariable> {
        let ts = self.mapping.get(var);

        ts.map(|x| Self::generate_multi_def_constraint(var, x))
            .unwrap_or(BTreeSet::new())
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
    for start_node_index in entry_sub_to_entry_node_map
        .into_iter()
        .map(|(_sub_tid, ndidx)| ndidx)
        .chain(speculative_points)
    {
        computation.set_node_value(
            start_node_index,
            cwe_checker_lib::analysis::interprocedural_fixpoint_generic::NodeValue::Value(
                DomainMap::from(generate_fresh_definition(proj, &mut curr_id)),
            ),
        );
    }

    computation.compute();
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
            .map(|v| (*ind, RegisterContext::new(v.deref().clone()))),
            NodeValue::Value(v) => Some((*ind, RegisterContext::new(v.deref().clone()))),
        })
        .collect()
}

#[cfg(test)]
mod test {

    /*
    use super::run_analysis;

    fn test_data_dir<P: AsRef<Path>>(pth: P) -> String {
        let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        d.push("test_data");
        d.push(pth);
        d.to_string_lossy().into_owned()
    }

    #[test]
    fn regression_test_for_actual_return_definition() {
        let bin = InferenceJob::parse_binary(&test_data_dir("mooosl")).expect("Couldnt get binary");
        let proj = InferenceJob::parse_project(&test_data_dir("mooosl.json"), &bin)
            .expect("Couldnt get project");
        let grph = InferenceJob::graph_from_project(&proj);
        let reaching_defs = run_analysis(&proj, &grph);

        let (target_idx, nd) = grph
            .node_references()
            .find(|(_, nd)| match nd {
                cwe_checker_lib::analysis::graph::Node::BlkStart(_, _) => false,
                cwe_checker_lib::analysis::graph::Node::BlkEnd(_, _) => false,
                cwe_checker_lib::analysis::graph::Node::CallReturn { call, return_ } => {
                    call.1.tid.address == "001012ed" && return_.1.tid.address == "0010128f"
                }
                cwe_checker_lib::analysis::graph::Node::CallSource { .. } => false,
            })
            .expect("couldnt find tartget node");

        let defs = reaching_defs.get(&target_idx).expect("expected_context");
        let defs = defs
            .mapping
            .get(&Variable {
                name: "RAX".to_owned(),
                size: ByteSize::new(8),
                is_temp: false,
            })
            .expect("couldnt get precondition of context");

        assert!(defs.contains(&Definition::ActualRet(
            Tid::create("instr_001012d2_2".to_owned(), "001012d2".to_owned()),
            0
        )));
    }
    */
}
