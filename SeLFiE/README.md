# SeLFiE

This directory contains SeLFiE.
Note that SeLFiE is still work in progress.
It is not ready for use yet.

### Pre-processing in Unique_Node and Term_Table
0. remove `HOL.Trueprop`
1. attaching pretty-printing of each sub-tree to each node
2. un-currying multi-arity functions
3. folding of meta-implications and meta-conjunction
4. attaching a path from the root to each node
5. transform a syntax tree to a look-up table that maps a path from the root to a node
6. analyze how each constant is defined in the relevant context and attach semantic information to it for the atomic assertion “Pattern” described in 

### Interpreter
1. evals for each type of term occurrence: `bool`, `node`, `number`, and `unode`.
2. `Eval_Print.ML`: evals for each type of term: `print` (which includes the handling of modifiers).
3. `Eval_Path.ML`: evals for `path` (`inner_path` and `outer_path`).
4. `Eval_Parameter.ML`:evals for parameter without bool.
5. `Eval_Parameter_With_Bool.ML`: evals for assert (= parameter with bool).
6. `Eval_Unary.ML`: bound variables, dive_in, quantifier, at once.
7. `Eval_Multi_Arity.ML`: evals for uncurried lambda expression.
8. `Eval_Variable.ML`: introduce variable names.
9. `Eval_Surface.ML`: "flattened" datatype `assert` for readability.
10. `Eval_Syntactic_Sugar.ML`: syntactic sugars.

- [X]  remove most of things from `SeLFiEsrc/Preprocessor/Pattern.ML` except for `get_command`.
- [X] `qtyp_to_qdomain` in `Quantifier_Domain.ML`.
- [X] `mk_all_numbers` in `Quantifier_Domain.ML`. -> `pst_n_trm_to_numb_domain`.
- [X] `unode_to_depth` in `Eval_Unode.ML`.
- [X] `outer_literal_to_simp_rules` in `From_Multiple_To_Deep.ML`. -> rename to `outer_literal_to_definitions`.
- [X] `inner_literal_to_simp_rules` in `From_Multiple_To_Deep.ML`. -> rename to `inner_literal_to_definitions`.
- [X] `trm_n_pst_to_path_to_unode_table` in `Make_Eval_Path.ML`.
- [X] `inner_path1_is_an_arg_of_inner_path2` in `Path_To_Unode.ML`. -> This should be defined as a syntactic sugar after `Eval_Deep`.
- [X] `inner_path1_is_nth_arg_of_inner_path2` in `Path_To_Unode.ML`. -> This should be defined as a syntactic sugar after `Eval_Deep`.
- [X] `inner_path_to_unode_table_to_lowest_fvars` in `Path_To_Unode.ML`. -> This should be defined as a syntactic sugar after `Eval_Deep`.
- [X] `inner_path_to_ancestor_inner_paths` in `Path_To_Unode.ML`. -> This should be defined as a syntactic sugar after `Eval_Deep`.
- [X] `inner_path_to_descendent_inner_paths` in `Path_To_Unode.ML`. -> This should be defined as a syntactic sugar after `Eval_Deep`.
- [X] develop `is_nth_child (unode, number)` in `Eval_Unode` in `Unique_Unode.ML` and `Eval_Unode.ML`.
      You will  need this when developing the aforementioned syntactic sugars.
- [X] syntactic sugar for Some_Term_Occurrence_Of_Term.
- [X] develop a structure to assert properties about `full-path`. -> No need for that.
   - Maybe it is enough to improve `Eval_Inner/Outer_Path` in `Path_To_Unode.ML`? -> Yes.
- [ ] `suffix_for_inductive_set` in `Pattern.ML`.
- [X] `mk_pattern_matrix` in `Pattern.ML`. Probably, I should remove this.
- [X] `helper` in `Unique_Node.ML`
- [X] `eavl` in `Eval_Surface.ML`.
- [X] `command_to_definitions` in `From_Multiple_To_Deep.ML`.
- [X] define `parameter` and `assert` in `Preprocessor/Util.ML` and use them in many modules.
- [X] `Eval_Syntactic_Sugar.ML`
- [X] develop the user-interface.
  - [X] develop an Isar interface
  - [X] create many combinations of induction arguements up to a certain limit (1000 for example)
  - [X] apply SeLFiE assertions to examine each of the combinations.

# TODOs to polish my draft

- [ ] measure execution time to compute induction heuristics only
- [ ] write one example for deep-dive
- [ ] compute the correlation between the coincidence rates and the proportions of induct tactics with generalisation.
- [ ] compute the correaltion between execution times and term sizes
- [ ] add a section about implementation
   - [ ] evaluation strategy
   - [ ] caching results
