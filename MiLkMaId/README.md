# MiLkMaId (Machine Learning Mathematical Induction)

This directory contains the experimental implementation of our recommendation system for mathematical induction in Isabelle/HOL.

## List of Heuristics

- [ ] 1. Apply induction on (an) argument(s) of an innermost constant.
- [ ] 2. If the first sub-goal contains a constant _c_ defined with the _fun_ keyword, use _c.induct_.
- [ ] 3. If one uses _bla.induct_ rule and _bla.induct_'s conclusion has _n_ arguemnts in the uncurried form, 
         he/she should specify _n_ variables to which the induct method should apply induction on.
         And these arguements should be just variables and they also should be arguements of _bla_.
- [ ] 4. If the first sub-goal involves a meta-implication and terms of types that are defined with the _datatype_ keyword 
         in the conclusion of the meta-implication, one should apply induction on the term 
         that has a type defined with the _datatype_ keyword.
- [ ] 5. (Heuristics from Section 3.2 of the old Isabelle tutorial.[1]) _Do induction on argument number i
         if the function is defined by recursion in argument number i._
- [ ] 6. If the first sub-goal appearing after applying a mathematical induction can easily imply the original sub-goal,
         this mathematical induction is not useful. 
         I expect that this assertion helps MiLkMaId to discard inductions that do not alter goals meaningfully.
- [ ] 7. If the first sub-goal appearing after applying a mathematical induction involves fewer constants than the ofiginal
         sub-goal, this mathematical induction is not useful.
         I expect that this heuristics helps MiLkMaId detect mathematical inductions that are destroy provability.
         
## List of Heuristics that are not relevant to the current implementation of _PSL_.
- [ ] If one does induction on (a) sub-term(s) more complicated than (a) variable(s), 
      generalize free variables appearing in the sub-term(s).

[1] Tobias Nipkow, Lawrence C. Paulson, Markus Wenzel: Isabelle/HOL - A Proof Assistant for Higher-Order Logic. 
Lecture Notes in Computer Science 2283, Springer 2002, ISBN 3-540-43376-7
