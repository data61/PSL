(*  Title:      PSL/LiFtEr/assertion2.md
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

# Generalization hueristics

## Generalization based on control-flow analysis of function definitions.
- If we apply induction on `xs`,
- `xs` is the nth argument of an occurrence of `foo`, 
- the `induct` method does not take any argument in the `rule` field, and
- the nth parameter in a clause of the definition of `foo` is used as part of the mth argument to a recursive call of `foo` appearing in the same clause,
- then all non-`xs` variables appearing as part of the mth argument of any `foo` should be generalized.

### Example 1
- `itrev xs ys = rev xs @ ys` in `Concrete_Semantics/Induction_Demo.thy`.
- `apply (induction xs arbitrary ys)`
- `itrev` takes `xs` as its first argument.
- `ys` occurs as the second argument of this `itrev`.
- The second clause of the definition of `itrev` is as following:
   - `itrev (x#xs) ys = itrev xs (x#ys)`
   - Note that `ys` is the second parameter of `itrev` on the left-hand side of the definition.
   - Ad `ys` is used as part of the second argument of `itrev` on the right-hand side of the definition.
- `ys` in the proof oglibation is the second argument of `itrev`.
- Therefore, `ys` should be generalized.

# Non-generalization heuristics

## Non-generalization based on control-flow analysis of function definitions.
- If we apply induction on `xs`,
- `xs` is the nth argument of an occurrence of `foo`, 
- the `induct` method does not take any argument in the `rule` field, and
- in any recursive call of `foo` on the right-hand side in its definition
   - the mth argument of `foo` is always as same as the mth parameter on the left-hand side,
- then no variables appearing as part of the mth argument of any `foo` should be generalized.
