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
- 3. One-level top-down abductive reasoning

## TODOs

- [ ] build bottom-up conjecturing mechanism.
   - [X] associativity
   - [ ] idnetity
   - [ ] invertibility
   - [X] commutativity
   - [ ] idempotent_element
   - [ ] idempotency
   - [X] distributivity
   - [X] ant_distributivity
   - [X] homomorphism_2
   - [ ] transitivity
   - [ ] symmetry
   - [ ] connexity
   - [ ] reflexivity
- [ ] build more top-down conjecturing mechanism.
- [ ] integrate the top-down and bottom-up approaches into one framework. (For each small proof search, we can use PSL.)
- [ ] enrich each proof context by registering proved conjectures.
- [ ] support `deep` reasoning (nested bottom-up or top-down conjecturing).
- [ ] evaluation using TIP.
- [ ] extended definitions of properties for binary functions, such as commutativity.

## Design decisions made to implement the first working prototype
- No parallelism for now.
- No multi-level bottom-up conjecturing for now.
- Support only the top-level theorems instead of aiming at tight integration with Isar.
- When to do nested top-down conjecturing? Just after applying top-down conjecturing? Or after applying proof by induction?
- Our abductive reasoning mechanism has to resides ouside PSL to allow for sharing of conjectures. 
   - How should I orchestrate the entire framework? 
   - It is still essentially a best-first search or beam search. 
   - Probably beam search is a better choice here for simpler implementation. 
   - We can still use PSL for applying `fastforce` and `sledgehammer` using `RepeatN`.
   - But we need to extract remaining sub-goals from `Proof.state`.
 
