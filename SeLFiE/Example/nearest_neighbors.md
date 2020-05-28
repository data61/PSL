# Heuristics useful to predict how to apply induction in Nearest_Neighborst.thy in KD_Tree

- [ ] proof of `set_nns` in line 189  
   - `lemma set (nearest_nbors n ps p kdt) ⊆ set_kdt kdt ∪ set ps`
   - `apply (induction kdt arbitrary: ps)`
   - `induction kdt` is obvious.
   - But why `arbitrary: ps`?
   - because of the second clause of the definition of `nearest_nbors`, which is
      - `"nearest_nbors n ps p (Node k v l r) = (...`
      - `let candidates = nearest_nbors n ps p l in`
      - `nearest_nbors n candidates p r`.
   - `candidate` is defined using `nearest_nbors`, and 
   - `candidate` is the second argument to `nearest_nbors` in `nearest_nbors n candidates p r`.
   - Maybe it does not matter that `candidate` is defined using `nearest_nbors`, 
   - but it matters that `candidate` is defined using `l`, which is
      - part of the fourth parameter (i.e. `Node k v l r`) to `nearest_nbors`.
   - `@{term "let x = True in y"}` is implemented as 
   - `Const ("HOL.Let", "bool ⇒ (bool ⇒ 'a) ⇒ 'a") $ Const ("HOL.True", "bool") $ Abs ("x", "bool", Free ("y", "'a")): term`
