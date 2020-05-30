- [X] `lemma mapi_rev_nth:` in Line 937 -> It is not a good example. We can deal with this proof without generalization.
   - ```
     assumes ‹xs !. v = Some x›
     shows ‹mapi f xs !. v = Some (f v x)›
     using assms
     proof (induct xs arbitrary: v)
     ```
   - `arbitrary: v` because
     ```
     primrec rev_nth :: ‹'a list ⇒ nat ⇒ 'a option› (infixl ‹!.› 100) where
       ‹[] !. v = None›
     | ‹(x # xs) !. v = (if length xs = v then Some x else xs !. v)›
     ```
     Note that the recursive call `xs !. v` appears after `length xs = v`.
     No. We did not have to generalize this.

- [ ] `lemma ST_sub':` in Line 1765
   - ```
     fixes f :: ‹'b ⇒ 'c›
     assumes ‹⋀(f :: 'b ⇒ 'c) i A. finite A ⟹ i ∉ A ⟹ ∃j. j ∉ f ` A›
     shows ‹n ⊢ branch ⟹ ⊢ sub_branch f branch›
     ```
   - `proof (induct branch arbitrary: f rule: ST.induct)`
   - Note that alternatively we can use `proof (induct n branch arbitrary: f rule: ST.induct)` without any observational change.
   - Because 
     ```
     abbreviation ST_ex :: ‹('a, 'b) branch ⇒ bool› (‹⊢ _› [50] 50) where
     ‹⊢ branch ≡ ∃n. n ⊢ branch›
     ```
   - So, `branch` and `sub_branch f branch` appear in the same relative location in terms of `⊢`(Hybrid_Logic.ST).
   - Furthermore, `f` is a variable with a function type.
   - Note that "Abbreviations participate in the usual type-inference process, but are expanded before the logic ever sees them. Pretty printing of terms in- volves higher-order rewriting with rules stemming from reverted abbre- viations." according to [the reference manual](https://isabelle.in.tum.de/dist/Isabelle2020/doc/isar-ref.pdf)
   - Why `induct branch` with `ST.induct` rather than `induct "sub_branch f branch"` with `ST.induct`?
   - ... because the former appears in the assumption of the meta-implication.

- [ ] `lemma ex_witness_list:` in Line 4268
   - ```
     assumes ‹p ∈. ps› ‹proper_dia p = Some q›
     shows ‹∃i. {❙@ i q, ❙◇ Nom i} ⊆ set (witness_list ps used)›
     using ‹p ∈. ps›
     proof (induct ps arbitrary: used)
     ```
   - `arbitrary: used` because 
      - `(witness_list ps used)`
      - `induct ps` , and
      - ```
        primrec witness_list :: ‹('a, 'b) fm list ⇒ 'b set ⇒ ('a, 'b) fm list› where
          ‹witness_list [] _ = []›
        | ‹witness_list (p # ps) used =
           (case proper_dia p of
              None ⇒ witness_list ps used
            | Some q ⇒
                let i = SOME i. i ∉ used
                in (❙@ i q) # (❙◇ Nom i) # witness_list ps ({i} ∪ used))›
        ```
        
- [ ] `lemma descendants_initial:` in Line 2655
   - ```
     assumes ‹descendants k i branch xs›
     shows ‹∃(v, v') ∈ xs. ∃ps.
       branch !. v = Some (ps, i) 
       ∧ ps !. v' = Some (❙◇ Nom k)›
     using assms by (induct k i branch xs rule: descendants.induct) simp_all
     ```
   - Note that `descendants k i branch xs` is a chained-fact.
   
- [ ] `lemma bridge_branch_nominals:` in Line 2543
   - ```
     ‹branch_nominals (mapi_branch (bridge k j xs) branch) ∪ {k, j} =
      branch_nominals branch ∪ {k, j}›
      proof (induct branch)
     ```
   - Note that `mapi_branch` is defined with `definition` by as a syntactic sugar for `mapi` which is defined recursively on the second argument.
   -
    ```
    primrec mapi :: ‹(nat ⇒ 'a ⇒ 'b) ⇒ 'a list ⇒ 'b list› where
      ‹mapi f [] = []›
    | ‹mapi f (x # xs) = f (length xs) x # mapi f xs›

    primrec mapi_block ::
      ‹(nat ⇒ ('a, 'b) fm ⇒ ('a, 'b) fm) ⇒ (('a, 'b) block ⇒ ('a, 'b) block)› where
      ‹mapi_block f (ps, i) = (mapi f ps, i)›

    definition mapi_branch ::
      ‹(nat ⇒ nat ⇒ ('a, 'b) fm ⇒ ('a, 'b) fm) ⇒ (('a, 'b) branch ⇒ ('a, 'b) branch)› where
      ‹mapi_branch f branch ≡ mapi (λv. mapi_block (f v)) branch›  
    ```
   - So, this is the case where deep-dive would be a help!

- [ ] `lemma list_down_induct [consumes 1, case_names Start Cons]:` in Line 2031
   - ```
     assumes 
       ‹∀y ∈ set ys. Q y›
       ‹P (ys @ xs)›
       ‹⋀y xs. Q y ⟹ P (y # xs) ⟹ P xs›
     shows ‹P xs›
       using assms by (induct ys) auto
     ```
   - because of `@`, which appears inside a chained fact.
