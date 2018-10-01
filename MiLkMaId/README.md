# MiLkMaId (Machine Learning Mathematical Induction)

This directory contains the experimental implementation of our recommendation system for mathematical induction in Isabelle/HOL.

## List of Heuristics

Note that these heuristics take the form of assertions. When we feed the results of these assertions to machine
learning algorithms, the results should be treated as _dummy variables_, which map `SOME true` to `1.0`, 
`SOME false` to `-1.0`, and `NONE` to `0.0`.

- [X] 1. Check if at least one argument of induction is an argument of an innermost constant that is a function.
- [X] 2. Check if the `induct` method uses `c.induct` in case the first sub-goal contains (a) constant(s) defined with 
         the `fun` keyword as an innermost function.
- [ ] 3. Check if
   - the `induct` method uses an `.induct` rule, say `bla.induct`,
     where `bla` is an innermost function that is applied to (a) variable(s),
   - the `induct` method has `n` arguments in the uncurried form where
     n is the number of arguments in the conclusion of `bla.induct` in the uncurried form,
   - the arguments to the `induct` method are the arguments to `bla` in the proof obligation, and
   - the order of arguments of the `induct` method is consistent with the order of the arguments to 
     `bla` in the proof obligation.
- [ ] 4. If the first sub-goal involves a meta-implication and terms of types that are defined with the `datatype` keyword 
         in the conclusion of the meta-implication, one should apply induction on the term 
         that has a type defined with the `datatype` keyword.
- [ ] 5. (Heuristics from Section 3.2 of the old Isabelle tutorial.[1]) _Do induction on argument number `i`
         if the function is defined by recursion in argument number `i`._
         More precisely, this assertion checks if
   - all arguments to the `induct` method are arguments to the same function, say `f`,
   - `f` is the common parent (immediate ancestor) of these arguments in the uncurried syntax tree
     representing the first sub-goal, and 
   - for any argument to the `induct` method, say `x`, `x` appears as the `n`th argument to `f` 
     in the proof obligation at least once where
     pattern-matching is complete for the `n`th parameter in the definition of `f`.
- [X] 6. If the first sub-goal appearing after applying a mathematical induction is alpha equivalent to
         the original sub-goal, this mathematical induction is not useful. (Use `Term.aconv`)
         I expect that this assertion helps MiLkMaId to discard inductions that do not alter goals meaningfully.
- [ ] 7. If the first sub-goal appearing after applying a mathematical induction involves fewer constants than the original
         sub-goal, this mathematical induction is not useful.
         I expect that this heuristics helps MiLkMaId detect mathematical inductions that destroy provability.
- [ ] 8. If multiple recursively defined constants appear at the same level in the syntax tree of 
         the uncurried version of the first sub-goal, do induction on the argument(s) of constants that are defined outside
         `HOL/Main.thy`.
- [ ] 9. Check if 
   - the `induct` method uses an `.induct` rule, say `c.induct`, and
   - there is no constants with an associated `.induct` rule that appear below the lowest `c`
     in the uncurried syntax tree of the first sub-goal.
     (`Isaplanner/TIP_prop_01.thy`)
- [ ] 10. If the first sub-goal contains multiple constants with associated `.induct` theorems, 
          use the `c.induct` that has the associated `c` that appears always in the position of argument number `i`
          where the pattern-matching of the corresponding ancestral constant is complete on argument number `i`.
          (`Isaplanner/TIP_prop_01.thy`)
- [ ] 11. If the underlying context has a simplification rule applicable to 
          all sub-goals that appear after applying mathematical induction, the mathematical induction tends to be promising.
- [X] 12. If the same variable (or sub-term) appears as the induction variable and generalized variable, 
          this mathematical induction is less promising.
- [X] 13. If the mathematical induction under consideration uses more than one rules,
          probably this induction is not very promising
- [X] 14. All arguments of induction are arguments of the same innermost constant that are free variables.
- [ ] 15. The first sub-goal appearing after applying a mathematical induction involves meta-universal quantifiers over
          variables that do not appear in the body.

## List of Heuristics that are not relevant to the current implementation of _PSL_.
- [ ] If one does induction on (a) sub-term(s) more complicated than (a) variable(s), 
      generalize free variables appearing in the sub-term(s).

[1] Tobias Nipkow, Lawrence C. Paulson, Markus Wenzel: Isabelle/HOL - A Proof Assistant for Higher-Order Logic. 
Lecture Notes in Computer Science 2283, Springer 2002, ISBN 3-540-43376-7
