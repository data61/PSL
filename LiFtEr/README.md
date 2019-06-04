# LiFtEr

LiFtEr is a domain-specific language developed to extract features of promising applications of induction in Isabelle/HOL.

## Contents
- `Concrete_Semantics`  example theories from the book "Concrete Semantics" written by Tobias Nipkow and Gerwin Klein.
- `Deep_Learning`       example theories from an arcticle in the AFP.
- `TIP_To_Test_LiFtEr`  example theories from the TIP benchmark.
- `src`                 the source code of LiFtEr.
- `LiFtEr.thy`          imports necessary ML files.ML_file in `src`.
- `assertion.md`        contains induction heuristics that are mostly about the syntax trees of proof obligations.
- `assertion2.md`       contains "advanced" induction heuristics.
- `Matrix_*.ML`         handles matrices.
- `LiFtEr_Util_*.ML`    provides utility functions.
- `Pattern_*.ML`        patterns for each constant.
- `Unique_Node_*.ML`    transforms each node of syntax tree.
- `Term_Table_*.ML`     transforms each proof obligation.
- `DInduct_*.ML`        similar to the one for PSL.
- `LiFtEr_*.ML`         interpreter of our domain specific language `LiFtEr`
- `Apply_LiFtEr_*.ML`   how to apply LiFtEr assertions.
- `README.md`           this file.
- `Concrete_Semantics`  example files from the book "Concrete Semantics" written by Nipkow et.al.
- `TIP_To_Test_LiFtEr`  TIP problems in Isabelle/HOL.
