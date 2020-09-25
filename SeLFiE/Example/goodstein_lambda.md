- [ ] `evalC_inj_on_hbase` in Line 440 
   - -> implemented in [this SeLFiE heuristic](https://github.com/data61/PSL/blob/ae99a769ae676967431ce8ed05ee783f0f8e13a7/SeLFiE/SeLFiE_Assertion.ML#L981).
   - -> It seems that this function is now called ind_on_lhs_of_eq_then_arb_on_rhs_of_eq, but it is not working well...
   - For example, semantic_induct does not recommend rule induction using hbase.induct here.
   - Instead of the rule induction using hbase.induct, semantic_induct recommends functional induction using .evalC.induct.
   - ```
     "n ∈ hbase b ⟹ m ∈ hbase b ⟹ evalC b n = evalC b m ⟹ n = m"
      proof2 (induct n arbitrary: m rule: hbase.induct)
      ```
   - `induct n` because we prefer to apply induction on the left-hand side of the equation.
      - if only one of `n` and `m` is an `Ind` term and both `n` and `m` are arguments of the same `=`, then apply induction on the one which comes as the LHS of the `=`, which is, in this case, `n`.
   - `arbitrary: m` because `n = m` and `induct n`. (and same relative location heuristic w.r.t. `n`. in `m ∈ hbase b` and `evalC b m`.)
   
- [X] `have "addO n (expω m) = addO n' (expω m') ⟹ n = n'` in Line 194 -> implemented in [this SeLFiE heuristic](https://github.com/data61/PSL/blob/f8c208f96b6ee4bcfda0ad22865bbdc7e13f19bd/SeLFiE/SeLFiE_Assertion.ML#L1043).
   - `apply (induct m arbitrary: m'`
   - because of the same reason we used for `evalC_inj_on_hbase`.
   - No. Not really. `m` and `m'` appear as sub-terms of arguments to an `=`. -> We used `Is_Nth_Arg_Or_Below_Nth_Arg_Of` instead.
     
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

- [X] `lemma goodstein⇩O:` in Line 709 -> done as [this](https://github.com/data61/PSL/blob/8bccbc06716b23192db8f3ff1f912dfdcc163b0b/SeLFiE/Example/afp-2020-05-16/thys/Goodstein_Lambda/Goodstein_Lambda.thy#L741).
   - `"goodsteinO c n = goodstein⇩O c ⟨n⟩⇩O"`
   - `apply (induct n arbitrary: c) by simp_all`
   - `arbitrary: c` because of
     ```
     primrec goodsteinO where
       "goodsteinO c Z = c"
     | "goodsteinO c (S n) = goodsteinO (c+1) n"
     | "goodsteinO c (L f) = goodsteinO c (f (c+2))"
     ```
