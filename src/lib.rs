//! # Type Constraint Generation by Abstract Interpretation
//!
//! Utilizes the [CWE checker pointer analysis](cwe_checker_lib::analysis::pointer_inference), reaching definitions, and parameter analysis from ghidra
//! to generate subtyping constraints of the form used in [retypd](https://github.com/GrammaTech/retypd).
#![warn(missing_docs)]
mod analysis;

/// Generates constraints as specified in [constraints] from an IR [Project](cwe_checker_lib::intermediate_representation::Project)
pub mod constraint_generation;

/// Our model of subtyping constraints
pub mod constraints;

/// Node contexts handle flow/context sensitive information for a given node's type constraints.
pub mod node_context;

#[cfg(test)]
pub(crate) mod test_utils;

/// Contains utility functions for transforming json into the project IR
pub mod util;

/// Contains an implementation of constraint solving, type sketch generation, and c type generation.
pub mod solver;

/// custom petagraph algos, specifically dense path expression from (FAST ALGORITHMS FOR SOLVING PATH PROBLEMS)[http://i.stanford.edu/pub/cstr/reports/cs/tr/79/734/CS-TR-79-734.pdf]
pub mod graph_algos;

/// Takes a sketch graph of types and lowers this type information to ctypes, using datalog defined heurisitics.
pub mod lowering;

/// Protobuf ctypes
pub mod ctypes {
    include!(concat!(env!("OUT_DIR"), "/ctypes.rs"));
}

/// Protobuf constraints
pub mod pb_constraints {
    include!(concat!(env!("OUT_DIR"), "/constraints.rs"));
}

/// Parses a context of file inputs into an inference job which can be run to retrieve generated constraints,
/// simplified constraints, and lowered types.
pub mod inference_job;

// Integration tests
#[cfg(test)]
mod tests {
    use std::{
        collections::{BTreeSet, HashMap},
        iter::FromIterator,
        path::{Path, PathBuf},
    };

    use crate::{
        constraints::DerivedTypeVar,
        solver::{type_lattice::CustomLatticeElement, type_sketch::SketchGraph},
    };
    use crate::{
        constraints::{ConstraintSet, SubtypeConstraint, TyConstraint},
        inference_job::{InferenceJob, JobDefinition, JsonDef},
        lowering::CType,
        solver::type_sketch::LatticeBounds,
    };
    use cwe_checker_lib::intermediate_representation::Tid;
    use petgraph::graph::NodeIndex;
    use pretty_assertions::assert_eq;
    use std::convert::TryFrom;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    struct ExpectedOutputFiles {
        constraint_gen: Option<String>,
        constraint_simplification: Option<String>,
        ctype_mapping: Option<String>,
        sketch_properties: Vec<Box<dyn Fn(&SketchGraph<LatticeBounds<CustomLatticeElement>>)>>,
    }

    fn parse_constraint_set_test(fname: &str) -> anyhow::Result<ConstraintSet> {
        let f = std::fs::File::open(fname)?;
        let v: Vec<SubtypeConstraint> = serde_json::from_reader(f)?;
        Ok(ConstraintSet::from(BTreeSet::from_iter(
            v.into_iter().map(|x| TyConstraint::SubTy(x)),
        )))
    }

    use serde::{Deserialize, Serialize};
    #[derive(Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord, Debug)]
    struct DeserSCCCons {
        scc: Vec<Tid>,
        constraints: Vec<SubtypeConstraint>,
    }

    fn normalize_cons(cons: &mut Vec<DeserSCCCons>) {
        cons.iter_mut().for_each(|c| {
            c.scc.sort();
            c.constraints.sort();
        });
        cons.sort();
    }

    fn parse_scc_constraints(fname: &str) -> anyhow::Result<Vec<DeserSCCCons>> {
        let f = std::fs::File::open(fname)?;

        let mut v: Vec<DeserSCCCons> = serde_json::from_reader(f)?;
        normalize_cons(&mut v);
        Ok(v)
    }

    fn parse_ctype_mapping(fname: &str) -> anyhow::Result<HashMap<NodeIndex, CType>> {
        let f = std::fs::File::open(fname)?;
        let content: HashMap<NodeIndex, CType> = serde_json::from_reader(f)?;
        Ok(content)
    }

    struct ExpectedOutputs {
        constraint_gen: Option<Vec<DeserSCCCons>>,
        constraint_simplification: Option<ConstraintSet>,
        ctype_mapping: Option<HashMap<NodeIndex, CType>>,
        sketch_properties: Vec<Box<dyn Fn(&SketchGraph<LatticeBounds<CustomLatticeElement>>)>>,
    }

    impl TryFrom<ExpectedOutputFiles> for ExpectedOutputs {
        type Error = anyhow::Error;

        fn try_from(value: ExpectedOutputFiles) -> Result<Self, Self::Error> {
            let expected_gen = value
                .constraint_gen
                .map_or(Ok(None), |op| parse_scc_constraints(&op).map(Some))?;

            let constrain_simpl_expec = value
                .constraint_simplification
                .map_or(Ok(None), |op| parse_constraint_set_test(&op).map(Some))?;

            let ctype_mapping = value
                .ctype_mapping
                .map_or(Ok(None), |op| parse_ctype_mapping(&op).map(Some))?;

            Ok(ExpectedOutputs {
                constraint_gen: expected_gen,
                constraint_simplification: constrain_simpl_expec,
                ctype_mapping,
                sketch_properties: value.sketch_properties,
            })
        }
    }

    struct TestCase {
        pub job_def: JobDefinition,
        pub expected_outputs: ExpectedOutputFiles,
    }

    fn assert_eq_if_available<T: std::cmp::PartialEq + std::fmt::Debug>(
        actual: T,
        expected: Option<T>,
    ) {
        expected.map(|exected_avail| assert_eq!(actual, exected_avail));
    }

    fn test_equivalence(expected: Option<&Vec<DeserSCCCons>>, actual: &Vec<DeserSCCCons>) {
        expected.map(|expected_v| {
            let mp = actual
                .iter()
                .map(|scc| (scc.scc.clone(), scc.constraints.clone()))
                .collect::<HashMap<_, _>>();

            for grp in expected_v.iter() {
                assert!(
                    mp.contains_key(&grp.scc),
                    "The generated constraints do not contain the scc {:#?}",
                    grp.scc
                );

                let scc_cons = mp.get(&grp.scc).unwrap();

                assert_eq!(
                    &grp.constraints, scc_cons,
                    "Left actual constraints did not equal right for scc: {:#?}",
                    grp.scc
                )
            }
        });
    }

    fn run_test_case(tc: TestCase) {
        init();
        let mut job =
            InferenceJob::parse::<JsonDef>(&tc.job_def, std::env::var("BTI_DEBUG_DIR").ok())
                .unwrap();
        job.recover_additional_shared_returns();

        let expected_values = ExpectedOutputs::try_from(tc.expected_outputs)
            .expect("could not open expected outputs");
        let genned_cons = job
            .get_simplified_constraints()
            .expect("could not get constraints");

        let mut normalized = genned_cons
            .iter()
            .map(|c| DeserSCCCons {
                scc: c.scc.clone(),
                constraints: c
                    .constraints
                    .iter()
                    .filter_map(|x| {
                        if let TyConstraint::SubTy(s) = x {
                            Some(s.clone())
                        } else {
                            None
                        }
                    })
                    .collect(),
            })
            .collect::<Vec<_>>();

        normalize_cons(&mut normalized);

        test_equivalence(expected_values.constraint_gen.as_ref(), &normalized);

        let labeled_graph = job
            .get_labeled_sketch_graph(genned_cons)
            .expect("Creating the sketch graph should not fail");

        for prop in expected_values.sketch_properties.iter() {
            prop(&labeled_graph);
        }

        println!("{}", labeled_graph);
        for (dtv, idx) in labeled_graph.get_graph().get_node_mapping().iter() {
            println!("Dtv: {} Group: {}", dtv, idx.index());
        }

        let lowered = job
            .lower_labeled_sketch_graph(&labeled_graph)
            .expect("Should be able to lower graph");

        let _tid_map = job
            .get_interesting_tids()
            .iter()
            .filter_map(|x| {
                let tvar = crate::constraint_generation::tid_to_tvar(x);

                if let Some(idx) =
                    labeled_graph.get_node_index_for_variable(&DerivedTypeVar::new(tvar))
                {
                    Some((x.clone(), idx))
                } else {
                    None
                }
            })
            .collect::<HashMap<_, _>>();

        assert_eq_if_available(&lowered, expected_values.ctype_mapping.as_ref());
    }

    #[derive(Default)]
    struct TestCaseBuilder {
        binary_path: Option<String>,
        ir_json_path: Option<String>,
        lattice_json: Option<String>,
        additional_constraints: Option<String>,
        interesting_tids_file: Option<String>,
        expec_constraint_gen: Option<String>,
        expec_constraint_simplification: Option<String>,
        expec_ctype_mapping: Option<String>,
        sketch_properties: Vec<Box<dyn Fn(&SketchGraph<LatticeBounds<CustomLatticeElement>>)>>,
    }

    impl TestCaseBuilder {
        fn test_data_dir<P: AsRef<Path>>(pth: P) -> String {
            let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            d.push("test_data");
            d.push(pth);
            d.to_string_lossy().into_owned()
        }

        fn expected_data_dir<P: AsRef<Path>>(pth: P) -> String {
            let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            d.push("expected_output");
            d.push(pth);
            d.to_string_lossy().into_owned()
        }

        pub fn new() -> TestCaseBuilder {
            Default::default()
        }

        fn set_binary_path(&mut self, v: String) -> &mut Self {
            self.binary_path = Some(v);
            self
        }

        fn set_ir_json_path(&mut self, v: String) -> &mut Self {
            self.ir_json_path = Some(v);
            self
        }

        fn add_sketch_property(
            &mut self,
            t: Box<dyn Fn(&SketchGraph<LatticeBounds<CustomLatticeElement>>)>,
        ) -> &mut Self {
            self.sketch_properties.push(t);
            self
        }

        fn set_lattice_json(&mut self, v: String) -> &mut Self {
            self.lattice_json = Some(v);
            self
        }

        fn set_expec_constraint_gen(&mut self, v: String) -> &mut Self {
            self.expec_constraint_gen = Some(v);
            self
        }

        fn set_additional_constraints(&mut self, v: String) -> &mut Self {
            self.additional_constraints = Some(v);
            self
        }

        fn set_expec_constraint_simplification(&mut self, v: String) -> &mut Self {
            self.expec_constraint_simplification = Some(v);
            self
        }

        fn set_expec_ctype_mapping(&mut self, v: String) -> &mut Self {
            self.expec_ctype_mapping = Some(v);
            self
        }

        fn set_interesting_tids_file(&mut self, v: String) -> &mut Self {
            self.interesting_tids_file = Some(v);
            self
        }

        pub fn build(self) -> TestCase {
            TestCase {
                job_def: JobDefinition {
                    binary_path: Self::test_data_dir(self.binary_path.expect("Need binary path")),
                    ir_json_path: Self::test_data_dir(self.ir_json_path.expect("need ir json")),
                    lattice_json: Self::test_data_dir(
                        self.lattice_json.expect("need lattice json"),
                    ),
                    additional_constraints_file: Self::test_data_dir(
                        self.additional_constraints
                            .expect("need additional_constraints"),
                    ),
                    interesting_tids: Self::test_data_dir(
                        self.interesting_tids_file.expect("need initeresting tids"),
                    ),
                },
                expected_outputs: ExpectedOutputFiles {
                    constraint_gen: self
                        .expec_constraint_gen
                        .map(|x| Self::expected_data_dir(x)),
                    constraint_simplification: self
                        .expec_constraint_simplification
                        .map(|x| Self::expected_data_dir(x)),
                    ctype_mapping: self.expec_ctype_mapping.map(|x| Self::expected_data_dir(x)),
                    sketch_properties: self.sketch_properties,
                },
            }
        }
    }

    #[test]
    fn simple_list_tc() {
        let mut bldr = TestCaseBuilder::new();
        bldr.set_binary_path("list_test.o".to_owned())
            .set_ir_json_path("list_test.json".to_owned())
            .set_additional_constraints("list_test_additional_constraints.json".to_owned())
            .set_lattice_json("list_test_lattice.json".to_owned())
            .set_interesting_tids_file("list_test_interesting_tids.json".to_owned())
            .set_expec_constraint_simplification("list_test_expected_simplified.json".to_string());
        // TODO(ian): comaprisons on types arent actually useful since ordering can change .set_expec_ctype_mapping("list_test_expected_types.json".to_string());
        run_test_case(bldr.build());
    }

    #[test]
    fn test_mooosl_full_constraint_gen() {
        let mut bldr = TestCaseBuilder::new();
        bldr.set_binary_path("new_moosl_bin".to_owned())
            .set_ir_json_path("new_moosl.json".to_owned())
            .set_additional_constraints("new_moosl_additional_constraints.json".to_owned())
            .set_lattice_json("new_moosl_lattice.json".to_owned())
            .set_interesting_tids_file("full_mooosl_tid_list.json".to_owned())
            .set_expec_constraint_gen("complete_mooosl_expected.json".to_owned());
        run_test_case(bldr.build());
    }

    #[test]
    fn test_mooosl_globals() {
        let mut bldr = TestCaseBuilder::new();
        bldr.set_binary_path("mooosl".to_owned())
            .set_ir_json_path("mooosl.json".to_owned())
            .set_additional_constraints("new_moosl_additional_constraints.json".to_owned())
            .set_lattice_json("mooosl_test_lattice.json".to_owned())
            .set_interesting_tids_file("full_mooosl_tid_list.json".to_owned());
        run_test_case(bldr.build());
    }

    #[test]
    fn test_composite_params_and_return() {
        let mut bldr = TestCaseBuilder::new();
        bldr.set_binary_path("composite_return/composite_return.so".to_owned())
            .set_ir_json_path("composite_return/composite_return.json".to_owned())
            .set_additional_constraints("composite_return/additional_cons.json".to_owned())
            .set_lattice_json("composite_return/lattice.json".to_owned())
            .set_interesting_tids_file("composite_return/interesting_tids.json".to_owned());
        run_test_case(bldr.build());
    }
}
