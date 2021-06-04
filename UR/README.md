# UR for United Reasoning.

## Overview

UR integrates
- traced (inverse) deductive reasonoing using Isabelle tactics
- inductive reasoning to produce promising induction tactics using `sem_ind`
- two conjecturing frameworks
   - top-down abductive reasoning
   - bottom-up conjecturing

## TODOs

- [ ] build bottom-up conjecturing mechanism.
- [ ] build more top-down conjecturing mechanism.
- [ ] integrate the top-down and bottom-up approaches into one framework. (For each small proof search, we can use PSL.)
- [ ] support `deep` reasoning (nested bottom-up or top-down conjecturing).
- [ ] evaluation using TIP.
