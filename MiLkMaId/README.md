# MiLkMaId (Machine Learning Mathematical Induction)

This directory contains the experimental implementation of our recommendation system for mathematical induction in Isabelle/HOL.

## List of Heuristics

Note that these heuristics take the form of assertions. When we feed the results of these assertions to machine
learning algorithms, the results should be treated as _dummy variables_, which map `SOME true` to `1.0`, 
`SOME false` to `-1.0`, and `NONE` to `0.0`.

- [X] 1. Check if at least one argument of induction is an argument of an innermost constant that is a function.
- [X] 2. Check if the `induct` method uses `c.induct` in case the first sub-goal contains (a) constant(s) defined with 
         the `fun` keyword or `inductive` keyword as an innermost function.
- [X] 3. Check if
   - the `induct` method uses an `.induct` rule, say `bla.induct`,
     where `bla` is an innermost function that is applied to (a) variable(s),
   - the `induct` method has `n` arguments in the uncurried form where
     n is the number of arguments in the conclusion of `bla.induct` in the uncurried form,
   - for some `bla`, 
      - all arguments to it are used as arguments to the `induct` method and 
      - they appear in the same order.
- [ ] 4. If the first sub-goal involves a meta-implication and terms of types that are defined with the `datatype` keyword
         in the conclusion of the meta-implication, one should apply induction on the term
         that has a type defined with the `datatype` keyword.
- [X] 5. (Heuristics from Section 3.2 of the old Isabelle tutorial.[1]) _Do induction on argument number `i`
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
- [X] 7. Check if the sum of the number of `arbitrary` terms in the `induct` method and the number of constants appearing
         in the first sub-goal is strictly larger than the number of constants in the first sub-goal appearing
         after applying a mathematical induction involves fewer constants.
         I expect that this heuristics helps MiLkMaId detect mathematical inductions that destroy provability.
- [ ] 8. If multiple recursively defined constants appear at the same level in the syntax tree of 
         the uncurried version of the first sub-goal, do induction on the argument(s) of constants that are defined outside
         `HOL/Main.thy`.
- [X] 9. Check if
   - The `induct` rule has at least one argument in the `rule` field, and
   - for any `.induct` rule, say `c.induct`, in the `rule` field of the `induct` method,
      - there is no constants with an associated `.induct` rule that appear at a level that is deeper than the level of
        the lowest `c` in the uncurried syntax tree of the first sub-goal.
        (Check `Isaplanner/TIP_prop_01.thy` for example.)
- [ ] 10. Check if
   - the `induct` rule ses at least one argument for the `rule` field, and
   - all the `rule`s used as arguments to the `induct` method the innermost ones. More precisely: 
      - for any `c1.induct` rule,
         - if the deepest level of the occurrences of `c1` is `n`,
         - there is no constant `c2`, such that
            - `c2` has an associated `.induct` rule in the proof context, and
            - the level of `c2` is higher than `n`.
   - (`Isaplanner/TIP_prop_01.thy`)
- [ ] 11. If the underlying context has a simplification rule applicable to
          all sub-goals that appear after applying mathematical induction, the mathematical induction tends to be promising.
- [X] 12. If the same variable (or sub-term) appears as the induction variable and generalized variable,
          this mathematical induction is less promising.
- [X] 13. Checks if the number of arguments for the `rule` field is less than two.
- [X] 14. All arguments of induction are arguments of the same innermost constant that are free variables.
- [X] 15. Check if the `induct` method introduces a lambda abstraction in the first-sub goal that is not used in the body.
          This includes quantified variables that are not used in the body.
- [X] 16. The `induct` method uses at least one argument for the `rule` field.
- [X] 17. (Heuristics from Section 3.2 of the old Isabelle tutorial.[1]) _Do induction on argument number `i`
         if the function is defined by recursion in argument number `i`._
         More precisely, this assertion checks if
   - the `induct` method takes at least one argument to specify on which sub-term Isabelle should apply mathematical induction, and
   - for any argument to the `induct` method, say `x`, the following statement holds:
      - there is an occurrence of `x` in the proof obligation, such that
         - `x` appears as an argument or part of argument to a function, say `f`, and
         - for all such functions, the instance of `x` or the sub-term, to which the instance of `x` belong,
           appears as the `n`th argument, where
           pattern-matching is complete for the `n`th parameter in the definition of `f`.
- [X] 18. The `induct` method does not take any argument.
- [X] 19. Check if
   - the `induct` method uses an `.induct` rule, say `bla.induct`,
     where `bla` is an innermost function that is applied to (a) variable(s),
   - the `induct` method has `n` arguments in the uncurried form where
     n is the number of arguments in the conclusion of `bla.induct` in the uncurried form,
   - for some `bla`, 
      - all arguments to the `induct` method appears as an argument to the same instance of `bla`.
   - Assrtion019 is similar to assertion003, but more relaxed.
- [X] 20. Check if the proof context contains local assumption introduced by the `using` keyword.
- [ ] 21. Check if 
   - for any variable, say `ys`, generalized by the `arbitrary` keyword,
      - for any occurrence of `ys` in the proof goal,
         - if `ys` is the nth argument of a function `foo`,
            - then there is an induction variable, say `xs`, 
              that appears as the nth argument of an occurrence of `foo` in the proof obligation.
   - `by (induct xs arbitrary: ys)` in line 1833 of `src/HOL/Library/Multiset.thy`.
- [ ] 22. Check if
   - for any variable, say `Q` generalized by the `arbitrary` keyword,
      - if there exists a function, say `nextl`, that takes `Q` as part of its `n`th argument,
         - there exists an induction variable, say `xs`, such that
            - for some natural number `m` that is smaller than or equal to the number of arguments `nextl` can take,
               - there are multiple occurrences of `nextl` such that
                  - `xs` appears as part of the `m`th argument to `nextl`, and
                  - `Q` appears as part of the `n`th argument to `nextl`.
   - `by (induct xs arbitrary: Q)` in line 623 of `thys/Finite_Automata_HF/Finite_Automate_HF.thy`.

## List of Heuristics that are not relevant to the current implementation of _PSL_.
- [ ] If one does induction on (a) sub-term(s) more complicated than (a) variable(s),
      generalize free variables appearing in the sub-term(s).

[1] Tobias Nipkow, Lawrence C. Paulson, Markus Wenzel: Isabelle/HOL - A Proof Assistant for Higher-Order Logic.
Lecture Notes in Computer Science 2283, Springer 2002, ISBN 3-540-43376-7
