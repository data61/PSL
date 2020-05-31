- [ ] `lemma block_nominals:` in Line 279
   - ```
     lemma block_nominals:
     ‹p on block ⟹ i ∈ nominals p ⟹ i ∈ block_nominals block›
     by (induct block) auto
     ```
   - why `induct block`?
   - because of `p on block` where `on` is defined as
   - ```
     primrec on :: ‹('a, 'b) fm ⇒ ('a, 'b) block ⇒ bool› (‹_ on _› [51, 51] 50) where
     ‹p on (ps, i) = (p ∈. ps ∨ p = Nom i)›
     ```
   - and `∈.` is defined as
   - ```
     abbreviation member_list :: ‹'a ⇒ 'a list ⇒ bool› (‹_ ∈. _› [51, 51] 50) where
     ‹x ∈. xs ≡ x ∈ set xs›
     ```
   - That is, after one step of deep-dive, we see that a part of `block` in `p on block`is an argument of `set` inside the second argument of `∈`.

- [ ] `lemma soundness':` in Line 306
   - ```
     ‹n ⊢ branch ⟹ M, g ⊨⇩Θ branch ⟹ False›
     proof (induct branch arbitrary: g rule: ST.induct)
     ```
   - Why `arbitrary: g`?
   - because 
   - ```
     abbreviation branch_sat :: ‹('w, 'a) model ⇒ ('b ⇒ 'w) ⇒ ('a, 'b) branch ⇒ bool› (‹_, _ ⊨⇩Θ _› [50, 50] 50) where
     ‹M, g ⊨⇩Θ branch ≡ ∀(ps, i) ∈ set branch. M, g ⊨⇩B (ps, i)›
     ```
   - where `⊨⇩B` is defined as
   - ```
     primrec block_sat :: ‹('w, 'a) model ⇒ ('b ⇒ 'w) ⇒ ('a, 'b) block ⇒ bool› (‹_, _ ⊨⇩B _› [50, 50] 50) where
     ‹(M, g ⊨⇩B (ps, i)) = (∀p on (ps, i). M, g, g i ⊨ p)›
    ```
  - where `⊨` is defined as
  - ```
    primrec semantics :: ‹('w, 'a) model ⇒ ('b ⇒ 'w) ⇒ 'w ⇒ ('a, 'b) fm ⇒ bool› (‹_, _, _ ⊨ _› [50, 50, 50] 50) where
       ‹(M, _, w ⊨ Pro x   ) = V M w x›
     | ‹(_, g, w ⊨ Nom i   ) = (w = g i)›
     | ‹(M, g, w ⊨ ❙¬ p    ) = (¬ M, g, w ⊨ p)›
     | ‹(M, g, w ⊨ (p ❙∨ q)) = ((M, g, w ⊨ p) ∨ (M, g, w ⊨ q))›
     | ‹(M, g, w ⊨ ❙◇ p    ) = (∃v ∈ R M w. M, g, v ⊨ p)›       (*Third argument changes in the recursive call.*)
     | ‹(M, g, _ ⊨ ❙@ i p  ) = (M, g, g i ⊨ p)›                 (*Third argument changes in the recursive call.*)
     ```
   - That is to say, `g` in the proof goal is the second argument to `⊨⇩Θ` which is an abbreviation for `⊨⇩B`,
     so `g` is in practice both the second argument and a part of the third argument passed to `⊨`,
   - and if we deep-dive into the definition of `⊨` we can see that the third argument to `⊨` in the recursive calls in the 5th and 6th clauses are not the parameters from the left-hand side of the equations. That is why `g` in the proof goal has to be generalized.
   - This example shows that we sometimes have to deep-dive in the definition even for constants defined with `primrec` especially when the definition has only one clause.

- [ ] `lemma mapi_branch_mem:` in Line 910
   - ```
     assumes ‹(ps, i) ∈. branch›
     shows ‹∃v. (mapi (f v) ps, i) ∈. mapi_branch f branch›
     unfolding mapi_branch_def using assms by (induct branch) auto
     ```
   - because of unfolding, we have
   - ```
     using this:
       (ps, i) ∈. branch
     goal (1 subgoal):
       1. ∃v. (mapi (f v) ps, i) ∈. mapi (λv. mapi_block (f v)) branch
     ```
   - where `∈.` is defined as
   - ```
     abbreviation member_list :: ‹'a ⇒ 'a list ⇒ bool› (‹_ ∈. _› [51, 51] 50) where
       ‹x ∈. xs ≡ x ∈ set xs›
     ```
   - Therefore, `branch` in `(ps, i) ∈. branch` is passed as the argument to the `set` in `x ∈ set x`.
   - Note that we do not even need a dive-in, because `∈.` is defined with `abbreviation`.
   
- [ ] `lemma rev_nth_mapi_block:` in Line 921
   - ```
     assumes ‹ps !. v' = Some p›
     shows ‹f v' p on (mapi f ps, a)›
     using assms by (induct ps) (simp_all, metis option.sel)
     ```
   - Why `induct ps`?
   - Because `mapi` is defined recursively on the second argument.
   - Because `(mapi f ps, a)` is the second argument of `on` similarly to the case for `lemma block_nominals:`, but we take only `ps` rather than `mapi f ps` maybe because `mapi` is defined recursively,
   - and `ps` is also the first argument to `!.` where `!.` is defined recursively on the first argument?

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

- [ ] `lemma descendants_initial:` in Line 2655
   - ```
     assumes ‹descendants k i branch xs›
     shows ‹∃(v, v') ∈ xs. ∃ps.
       branch !. v = Some (ps, i) 
       ∧ ps !. v' = Some (❙◇ Nom k)›
     using assms by (induct k i branch xs rule: descendants.induct) simp_all
     ```
   - Note that `descendants k i branch xs` is a chained-fact.
   
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
