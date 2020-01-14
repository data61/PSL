# SeLFiE

This directory contains SeLFiE.
Note that SeLFiE is still work in progress.
It is not ready for use yet.

## The bootstrapping

### Pre-processing in Unique_Node and Term_Table
1. attaching pretty-printing of each sub-tree to each node
2. un-currying multi-arity functions
3. folding of meta-implications and meta-conjunction
4. attaching a path from the root to each node
5. transform a syntax tree to a look-up table that maps a path from the root to a node
6. analyze how each constant is defined in the relevant context and attach semantic information to it for the atomic assertion “Pattern” described in 

### Interpreter
1. evals for each type of term occurrence: `bool`, `node`, `number`, and `unode`.
2. evals for `path` (`inner_path` and `outer_path`).
3. evals for each type of term: `print`, and `induct_argument`.
4. evals for parameter without bool.
5. evals for assert (= parameter with bool).
6. evals for lambda expression (with bound variable).
7. evals for lambda expression (with named variable).
8. evals for lambda expression (with quantifiers).
9. evals for uncurried lambda expression.
10. eval for the semantic-aware logical feature extractor (= SeLFiE's core language).
11. eval for the surface language.
12. eval for the sytnax sugars.

### TODOs
- [X]  remove most of things from `SeLFiEsrc/Preprocessor/Pattern.ML` except for `get_command`.
- [X] `qtyp_to_qdomain` in `Quantifier_Domain.ML`.
- [X] `mk_all_numbers` in `Quantifier_Domain.ML`. -> `pst_n_trm_to_numb_domain`.
- [X] `unode_to_depth` in `Eval_Unode.ML`.
- [X] `outer_literal_to_simp_rules` in `From_Multiple_To_Deep.ML`. -> rename to `outer_literal_to_definitions`.
- [X] `inner_literal_to_simp_rules` in `From_Multiple_To_Deep.ML`. -> rename to `inner_literal_to_definitions`.
- [X] `trm_n_pst_to_path_to_unode_table` in `Make_Eval_Path.ML`.
- [ ] `inner_path1_is_an_arg_of_inner_path2` in `Path_To_Unode.ML`. -> This should be defined as a syntactic sugar after `Eval_Deep`.
- [ ] `inner_path1_is_nth_arg_of_inner_path2` in `Path_To_Unode.ML`. -> This should be defined as a syntactic sugar after `Eval_Deep`.
- [ ] `inner_path_to_unode_table_to_lowest_fvars` in `Path_To_Unode.ML`. -> This should be defined as a syntactic sugar after `Eval_Deep`.
- [ ] `inner_path_to_ancestor_inner_paths` in `Path_To_Unode.ML`. -> This should be defined as a syntactic sugar after `Eval_Deep`.
- [ ] `inner_path_to_descendent_inner_paths` in `Path_To_Unode.ML`. -> This should be defined as a syntactic sugar after `Eval_Deep`.
- [X] develop `is_nth_child (unode, number)` in `Eval_Unode` in `Unique_Unode.ML` and `Eval_Unode.ML`.
      You will  need this when developing the aforementioned syntactic sugars.
- [X] develop a structure to assert properties about `full-path`. -> No need for that.
   - Maybe it is enough to improve `Eval_Inner/Outer_Path` in `Path_To_Unode.ML`? -> Yes.
- [ ] `suffix_for_inductive_set` in `Pattern.ML`.
- [X] `mk_pattern_matrix` in `Pattern.ML`. Probably, I should remove this.
- [X] `helper` in `Unique_Node.ML`
- [X] `eavl` in `Eval_Surface.ML`.
- [ ] `command_to_definitions` in `From_Multiple_To_Deep.ML`.
- [ ] define `parameter` and `assert` in `SeLFiE_Util.ML` and use them in many modules.
- [ ] `Eval_Syntactic_Sugar.ML`
- [ ] develop the user-interface.
  - [ ] develop an Isar interface
  - [ ] create many combinations of induction arguements up to a certain limit (1000 for example)
  - [ ] apply SeLFiE assertions to examine each of the combinations.
