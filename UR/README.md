**Warning! UR is still work in progress! It is not ready for use!**

# UR for United Reasoning.

## Overview

UR integrates
- traced (inverse) deductive reasonoing using Isabelle tactics
- inductive reasoning to produce promising induction tactics using `sem_ind`
- two conjecturing frameworks
   - top-down abductive reasoning
   - bottom-up conjecturing

## Workflow

- 1. Apply a PSL strategy to look for a short proof.
- 2. One-level iterative bottom-up conjecturing till saturate.
   - "one-level" because we do not produce new bottom-up conjectures for constants that newly appear in our scope while investigating the definitions of constants.
- 3. First-level top-down abductive reasoning
- 4. Second-level top-down abductive reasoning

## TODOs

- [ ] build bottom-up conjecturing mechanism.
   - [X] associativity
   - [X] identity
   - [X] invertibility -> I guess this wouldn't be helpful.
   - [X] commutativity
   - [X] idempotent_element
   - [X] idempotence
   - [X] distributivity
   - [X] ant_distributivity
   - [X] homomorphism_2
   - [X] transitivity
   - [X] symmetry
   - [X] connexity
   - [X] reflexivity
- [ ] implement an iteration mechanism for bottom-up conjecturing.
- [ ] build more top-down conjecturing mechanism.
   - [ ] more variations
   - [ ] quickcheck and nitpick as a separate lemma.
   - [ ] abductive reasonoing as a reparate lemma. See [this example](https://github.com/data61/PSL/blob/708fadc98369865447086f3a60878138c94141e6/UR/United_Reasoning.thy#L304)
   - [ ] build a final proof using auxiliary lemmas. See [this example](https://github.com/data61/PSL/blob/708fadc98369865447086f3a60878138c94141e6/UR/United_Reasoning.thy#L310).
   - [ ] record which conjectures are alreadh tried out.
- [ ] integrate the top-down and bottom-up approaches into one framework. (For each small proof search, we can use PSL.)
- [X] enrich each proof context by registering proved conjectures.
- [ ] implement an abductive-reasoning framework outside the tactic language.
   - [X] use the `assumes` keyword. -> Look at [this example](https://github.com/data61/PSL/blob/2a7564209bb412999c44b85081a97f41d90ba976/UR/United_Reasoning.thy#L298).
   - We can use 
      - priority queue to implement the best-first search or the breadth-first search,
      - [stack](https://github.com/seL4/isabelle/blob/b4a0546e568ea7fb667fadabe126d944991b05cc/src/Pure/General/stack.ML#L7) in [Isar](https://github.com/seL4/isabelle/blob/b4a0546e568ea7fb667fadabe126d944991b05cc/src/Pure/Isar/proof.ML#L163) to implement each non-deterministic choice.
      - How can I share the context with proved auxiliary lemmas and lemmas that are refuted or tried-in-vain?
      - Record what has been proved in each node, and pass the context around as an argument.
      - Always keep the orders (/dependencies) of proved lemmas.
- [ ] support `deep` reasoning (nested bottom-up or top-down conjecturing).
- [ ] evaluation using TIP.
- [ ] extended definitions of properties for binary functions, such as commutativity.

## Design decisions made to implement the first working prototype
- Breadth-First Search for now. I want to swtich to a Best-First Search.
- No parallelism for now.
- No multi-level bottom-up conjecturing for now. -> Yes. We should implement it. This shouldn't be too hard.
- Support only the top-level theorems instead of aiming at tight integration with Isar.
- When to do nested top-down conjecturing? Just after applying top-down conjecturing? Or after applying proof by induction?
- Our abductive reasoning mechanism has to resides ouside PSL to allow for sharing of conjectures. 
   - How should I orchestrate the entire framework? 
   - It is still essentially a best-first search or beam search. 
   - Probably beam search is a better choice here for simpler implementation. 
   - We can still use PSL for applying `fastforce` and `sledgehammer` using `RepeatN`.
   - But we need to extract remaining sub-goals from `Proof.state`.
 
