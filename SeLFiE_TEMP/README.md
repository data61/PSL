# SeLFiE

This directory contains SeLFiE.
Note that SeLFiE is still work in progress.

## The bootstrapping

### Pre-processing in Unique_Node and Term_Table
1. attaching pretty-printing of each sub-tree to each node
2. un-currying multi-arity functions
3. folding of meta-implications and meta-conjunction
4. attaching a path from the root to each node
5. transform a syntax tree to a look-up table that maps a path from the root to a node
6. analyze how each constant is defined in the relevant context and attach semantic information to it for the atomic assertion “Pattern” described in 

### Interpreter
- connective in Eval_Connective
- node in Eval_Node
- unode in Eval_Unode
- fpunode_to_unode: fpunode_to_unode in Full_Path_To_FPUnode
   - TODO: Probably this file is a misnomer
- fpunode in Eval_FPUnode
- full_path_to_fpunode_table_to_print_to_paths_table: full_path_to_fpunode_table -> print_to_full_paths_table in Print_To_Full_Paths
- print in Eval_Print
- number in Eval_Number
- full_path in Eval_Full_Path
   - we identify all sub-term occurrences (node, unode, fpunode(, and a bit of print)) uniquely using full_path
- primitive (connective, full_path, print, number) in Eval_Primitive
- parameter (primitive without parameters) in Eval_Parameter
   - TODO: Probably "parameter" is a misnomer. It should be something like "parametrized".
   - parameters are connective, full_path, print, string, number, and int
- de-Bruijn style of lambda-abstraction in Eval_Bound
- named variables in Eval_Var
- all and some in Eval_Quantifier
- modifier in Eval_Modifier
- TODO: pattern
   - maybe before modifier
- surface in Eval_Surface
