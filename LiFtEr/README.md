**Message to APLAS2019 reviewers: the following two files contain the examples presented in our paper submitted at APLAS2019:**
- LiFtEr/Concrete_Semantics/Induction_Demo.thy, and
- LiFtEr/Concrete_Semantics/ASM.thy

# LiFtEr

LiFtEr is a domain-specific language developed to extract features of promising applications of induction in Isabelle/HOL.

## Installation
1. Install [Isabelle](https://isabelle.in.tum.de/).
2. Download or clone this repository (git clone https://github.com/data61/PSL.git).
3. Build Isabelle/HOL with PaMpeR from Terminal or Command Prompt using the following two commands:
   - move the current directory to the directory containing this README.md file.
      - `cd (this directory)`
   - open Isabelle/jEdit with LiFtEr.
      - `path_to_where_you_have_isabelle_in_your_system/Isabelle/bin/isabelle jedit -d . -l LiFtEr`

## Contents
- `Concrete_Semantics`  example theories from the book "Concrete Semantics" written by Tobias Nipkow and Gerwin Klein.
- `Deep_Learning`       example theories from an arcticle in the AFP.
- `TIP_To_Test_LiFtEr`  example theories from the TIP benchmark.
- `src`                 the source code of LiFtEr.
- `LiFtEr.thy`          imports necessary ML files.ML_file in `src`.
- `assertion.md`        contains induction heuristics that are mostly about the syntax trees of proof obligations.
- `assertion2.md`       contains "advanced" induction heuristics.
- `README.md`           this file.
