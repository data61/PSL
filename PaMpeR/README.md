# PaMpeR (Proof Method Recommendation system)

## Installation
1. Install [Isabelle](https://isabelle.in.tum.de/).
2. Download or clone this repository (git clone https://github.com/data61/PSL.git).
3. Move to the PaMpeR branch (https://github.com/data61/PSL/tree/PaMpeR).
4. Then, Users can install PaMpeR by importing *.PaMpeR/PaMpeR.thy* to their theory files
   with the Isabelle keyword, **imports**.
   
## Three PaMpeR Commands
- The keyword **which_method** lists the 15 most promising proof methods for the current given proof state as well as the numerical expectation for each of them.
![Screenshot](./image/which_method.png)
- The keyword **why_method** takes a name of proof method and tells why PaMpeR recommends the proof method for the current given proof state.
![Screenshot](./image/why_method.png)
- The keyword **rank_method** shows the rank of a given proof method to the current proof state in comparison to other proof methods.
![Screenshot](./image/rank_method.png)

## Preliminary Evaluation
- The details of preliminary evaluation is presented in PSL/PaMpeR/Evaluation/README.md
