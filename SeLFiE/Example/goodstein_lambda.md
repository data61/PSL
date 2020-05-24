- [ ] `evalC_inj_on_hbase` in Line 440
   - ```
     "n ∈ hbase b ⟹ m ∈ hbase b ⟹ evalC b n = evalC b m ⟹ n = m"
      proof2 (induct n arbitrary: m rule: hbase.induct)
      ```
   - `induct n` because we prefer to apply induction on the left-hand side of the equation.
   - `arbitrary: m` because `n = m` and `induct n`. (and same relative location heuristic w.r.t. `n`. in `m ∈ hbase b` and `evalC b m`.)
   
- [ ] `have "addO n (expω m) = addO n' (expω m') ⟹ n = n'` in Line 194
   - `apply (induct m arbitrary: m'`
   - because of the same reason we used for `evalC_inj_on_hbase`.
     
- [ ] `have "goodsteinC_dom (c, n)" for c n`
   - `apply (induct n arbitrary: c rule: C_Ord_induct)`
   - because of
   ```
   function (domintros) goodsteinC where
      "goodsteinC c (C [])                = c"
    | "goodsteinC c (C (C [] # ns))       = goodsteinC (c+1) (C ns)"
    | "goodsteinC c (C (C (n # ns) # ms)) = goodsteinC c (C (funC (C (n # ns)) (c+2) @ ms))"
    ```
    
- [ ] `lemma hbase_funC`
   - ```
     "c ≠ 0 ⟹ C (n # ns) ∈ hbase_ext (Suc c) ⟹
      C (funC n (Suc c) @ ns) ∈ hbase_ext (Suc c)"
      proof (induct n arbitrary: ns rule: funC.induct)
      ```
   - `arbitrary: ns` because of `C (n # ns) ∈ hbase_ext (Suc c)`?

- [ ] `lemma goodstein⇩O:` in Line 709
   - `"goodsteinO c n = goodstein⇩O c ⟨n⟩⇩O"`
   - `apply (induct n arbitrary: c) by simp_all`
   - `arbitrary: c` because of
     ```
     primrec goodsteinO where
       "goodsteinO c Z = c"
     | "goodsteinO c (S n) = goodsteinO (c+1) n"
     | "goodsteinO c (L f) = goodsteinO c (f (c+2))"
     ```
