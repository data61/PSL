- [ ] `lemma mapi_rev_nth:` in Line 937
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
     
- `lemma ex_witness_list:` in Line 4268
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
