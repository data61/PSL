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
- TODO

### TODOs
- [X]  remove most of things from `SeLFiEsrc/Preprocessor/Pattern.ML` except for `get_command`.
- [X] `qtyp_to_qdomain` in `Quantifier_Domain.ML`.
- [X] `mk_all_numbers` in `Quantifier_Domain.ML`. -> `pst_n_trm_to_numb_domain`.
- [X] `unode_to_depth` in `Eval_Unode.ML`.
- [X] `outer_literal_to_simp_rules` in `From_Multiple_To_Deep.ML`. -> rename to `outer_literal_to_definitions`.
- [X] `inner_literal_to_simp_rules` in `From_Multiple_To_Deep.ML`. -> rename to `inner_literal_to_definitions`.
- [X] `trm_n_pst_to_path_to_unode_table` in `Make_Eval_Path.ML`.
- [ ] `inner_path1_is_an_arg_of_inner_path2` in `Path_To_Unode.ML`.
- [ ] `inner_path1_is_nth_arg_of_inner_path2` in `Path_To_Unode.ML`.
- [ ] `suffix_for_inductive_set` in `Pattern.ML`.
- [ ] `mk_pattern_matrix` in `Pattern.ML`. Probably, I should remove this.
- [ ] `helper` in `Unique_Node.ML`
- [ ] `eavl` in `Eval_Surface.ML`.
- [ ] `pst_n_term_n_path_to_cname` in `Make_Eval_Path.ML`.
- [ ] `command_to_definion` in `From_Multiple_To_Deep.ML`.
- [ ] `inner_path_to_unode_table_to_lowest_fvars` in `Path_To_Unode.ML`.
- [ ] `inner_path_to_ancestor_inner_paths` in `Path_To_Unode.ML`.
- [ ] `inner_path_to_descendent_inner_paths` in `Path_To_Unode.ML`.