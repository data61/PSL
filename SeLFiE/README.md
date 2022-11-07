# SeLFiE

## Installation (of SeLFiE)
1. Install [Isabelle2022](https://isabelle.in.tum.de).
2. Download or clone this repository (git clone https://github.com/data61/PSL.git).
3. Open Isabelle/jEdit with PSL and all that. You can do this by opening Isabelle/jEdit as following:
   * `(path-to-the-Isabelle-binary)isabelle jedit -d (path-to-the-directory-that-contains-this-README-file) -l SeLFiE`
   * If you are a MacOS user and your current directory is this one with this README.md, probably you should type something like this in Terminal:
   * `/Applications/Isabelle2020.app/Isabelle/bin/isabelle jedit -d . -l SeLFiE`
4. Then, open `Test_SeLFiE.thy` to check if SeLFiE works as expected. You can also see some example heuristics in `SeLFiE_Assertion.thy`.

## Pre-processing in Unique_Node and Term_Table
0. remove `HOL.Trueprop`
1. attaching pretty-printing of each sub-tree to each node
2. un-currying multi-arity functions
3. folding of meta-implications and meta-conjunction
4. adding tags to indicate where each node is in terms of meta-implication and meta-conjunction
5. attaching a path from the root to each node
6. transform a syntax tree to a look-up table that maps a path from the root to a node
7. analyze how each constant is defined in the relevant context and attach semantic information to it for the atomic assertion “Pattern” described in 

## Interpreter
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
