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
- [ ] build more top-down conjecturing mechanism.
- [ ] integrate the top-down and bottom-up approaches into one framework. (For each small proof search, we can use PSL.)
- [ ] enrich each proof context by registering proved conjectures.
- [ ] support `deep` reasoning (nested bottom-up or top-down conjecturing).
- [ ] evaluation using TIP.

## Design decisions made to implement the first working prototype
- No parallelism for now.
- No multi-level bottom-up conjecturing for now.
- Support only the top-level theorems instead of aiming at tight integration with Isar.
