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
- [ ]  remove most of things from `SeLFiEsrc/Preprocessor/Pattern.ML` except for `get_command`.
- [ ] `qtyp_to_qdomain` in `Quantifier_Domain.ML`.
- [ ] `mk_all_numbers` in `Quantifier_Domain.ML`.
- [ ] `unode_to_depth` in `Eval_Unode.ML`.
- [ ] `outer_literal_to_simp_rules` in `From_Multiple_To_Deep.ML`.
- [ ] `inner_literal_to_simp_rules` in `From_Multiple_To_Deep.ML`.
- [ ] `trm_n_pst_to_path_to_unode_table` in `Make_Eval_Path.ML`.
- [ ] `inner_path1_is_an_arg_of_inner_path2` in `Path_To_Unode.ML`.
- [ ] `inner_path1_is_nth_arg_of_inner_path2` in `Path_To_Unode.ML`.
- [ ] `suffix_for_inductive_set` in `Pattern.ML`.
- [ ] `mk_pattern_matrix` in `Pattern.ML`. Probably, I should remove this.
- [ ] `helper` in `Unique_Node.ML`
- [ ] `eavl` in `Eval_Surface.ML`.
