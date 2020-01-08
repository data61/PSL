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
- [ ] remove most of things from `SeLFiEsrc/Preprocessor/Pattern.ML` except for `get_command`.
- [ ] `qtyp_to_qdomain` in `Quantifier_Domain.ML`.
- [ ] `mk_all_numbers` in `Quantifier_Domain.ML`.
- [ ] `unode_to_depth` in `Eval_Unode.ML`.

- [ ] `eavl` in `Eval_Surface.ML`.
