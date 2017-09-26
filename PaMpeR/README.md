# PaMpeR (Proof Method Recommendation system)

PaMpeR is an enhancement tool to give proof engineers hints in their work.

- The first part of the system is a feature extraction algorithm which obtains training data from existing Proof.
Users can also create their own training data and modify features they want to use.
Currently the features are all in binary assertion form.

- The second part of the system uses a machine learning result from AFP (Archive of Formal Proof) 
and provides runtime proof method recommendation to user in a proof stage by the keyword Proof_advice.

# List of assertions

## Assertions about existence of objects (rules) in the proof state

- [x] 1. local assumption

- check the existence of rules in the Proof.state that are associated with a constant in the first subgoal.

   - [x] 5. associated "pinduct" rule.

   - [x] 6. associated "psimps" rule.

   - [x] 7. associated "pelims" rule.

   - [x] 8. associated "cases" rule.

   - [x] 9. associated "intro" rule.

   - [x] 10. associated recursive "simp" rule

## Assertions about the first subgoal

### Assertions about existence of an object

- [x] 2. "case_of" constant

- [x] 3. "Conjunction" as outmost constant

- [x] 4. "For all" constant

- [x] 12. constant defined by lift_definition

- [x] 13. constant defined by primcorec

- [x] 14. constant defined by interpretation (Not working accurately)

- [x] 15. check if the length of outmost constant is greater than 1. (a function Constant)

- [x] 11. constant with prefix "Num"

- [x] check if there is a constant with prefix "Real"

- [x] check if there is a constant with prefix "List"

- [ ] check if there is a record typed variable

- [ ] check for typeclass definition

- [ ] constant "===>"

### Assertions about the all constants appearing in the first subgoal.

- [x] check if all constants are defined in Main

## Assertions about the classification () of proof obligation

- [ ] is a "Equational" problem

- [ ] is an "Inductive" problem

- [ ] is a "Co-Inductive" problem

- [ ] is an "Unknown" problem

### Assertions about the outermost construct of the first subgoal

The first subgoal has ... as the outermost constant

- [ ] "==" (meta equality)

- [ ] "=" (HOL equality)

- [ ] "==>" (meta implication)

- [ ] "-->" (HOL implication)

- [ ] "!!" (meta universal quantifier)

- [ ] "!" (HOL universal quantifier)

- [ ] "?" (HOL existential quantifier)

### Assertions about the existence of constants not as the outermost constant

The first subgoal has ... but not as the outermost constant.

- [ ] "==" (meta equality)

- [ ] "=" (HOL equality)

- [ ] "==>" (meta implication)

- [ ] "-->" (HOL implication)

- [ ] "!!" (meta universal quantifier)

- [ ] "!" (HOL universal quantifier)

- [ ] "?" (HOL existential quantifier)

## Possible future assertions:

- [ ] Expanding into integer feature:

   - [ ] number of subgoals

   - [ ] length of proof obligation

