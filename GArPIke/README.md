# GArPIke

GArPIke is an attempt to improve the weights of `sem_ind` using genetic algorithm.

## TODOs

- [ ] Step 1: build a system that checks if an induction candidate is good ignoring variable generalisation. For this we can take some hints from a similar system that was used for sem_ind: the system for sem_ind ignores the order of variables.
- [ ] Step 2: modify the `induct` tactic and `induction` tactic, so that they produce a datapoint, which consists of triples of (1) location, (2) assertion results (booleans) and (3) a boolean value that represents if it coincides with the choice of human engineer *ignoring* variable generalisation.
- [ ] Step 3: randomly split the database into the training data and validation data.
- [ ] Step 4: use genetic algorithm on the weights of each induction assertion.
   - [ ] Step 4-1: build a Python script to read/write weights of assertions from/to CSV files.
   - [ ] Step 4-2: build a ML function to read CSV files.
   - [ ] Step 4-3: update weights in Isabelle/HOL based on the values in such CSV files.
- [ ] Step 5: modify the `induct` tactic and `induction` tactic again, so that they produce a datapoint, which consists of triples of (1) location,  (2) assertion results (booleans) and (3) a boolean value that represents if it coincides with the choice of human engineer *including* variable generalisation.
- [ ] Step 6: merge the dataset about induction terms (Step 2) with the dataset about variable generalisation (Step 5) using locations as hints.
- [ ] Step 7: split the merged dataset, so that this splitting becomes consistent with Step 3.
- [ ] Step 8: use genetic algorithm on the weights of each induction assertion.
- [ ] Step 9: compare the coincidence rates of the new version against the original one using the validation data.
