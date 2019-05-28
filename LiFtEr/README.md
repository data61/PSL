# LiFtEr

LiFtEr is a domain specific language developed to extract features of induction in Isabelle/HOL.

## Contents
- `MeLoId_LiFtEr.thy` imports necessary ML files.ML_file "Matrix_Sig.ML"
- `Matrix_*.ML`         handles matrices.
- `LiFtEr_Util_*.ML`    provides utility functions.
- `Pattern_*.ML`        patterns for each constant.
- `Unique_Node_*.ML`    transforms each node of syntax tree.
- `Term_Table_*.ML`     transforms each proof obligation.
- `DInduct_*.ML`        similar to the one for PSL.
- `LiFtEr_*.ML`         interpreter of our domain specific language `LiFtEr`
- `Apply_LiFtEr_*.ML`   how to apply LiFtEr assertions.