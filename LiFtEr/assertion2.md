(*  Title:      PSL/LiFtEr/assertion2.md
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

# Generalization hueristics

## Generalization based on control-flow analysis of function definitions.
- If we apply induction on `xs`,
- `xs` is the nth argument of an occurrence of `foo`, 
- (the `induct` method does not take any argument in the `rule` field), and
   - Probably the presence of arguments in the `rule` field is not relevant.
   - See, for example, `lemma mono2_step: "c1 ≤ c2 ⟹ S1 ⊆ S2 ⟹ step S1 c1 ≤ step S2 c2"` line 155 in `Abs_Int_ITP2012/Collecting.thy`.
- the nth parameter in a clause of the definition of `foo` is used as part of the mth argument to a recursive call of `foo` appearing in the same clause,
- then all non-`xs` variables appearing as part of the mth argument of any `foo` should be generalized.
- Maybe it is enough to check if the mth arguments of all recursive calls of `foo` are identical to the mth parameters in each clause of the definition.
- Note that if a proof obligation involve constants defined with the `definition` keyword, it is worth trying to look into the definition. And we might find a recursively defined constants there. In that case, we should take one step further in the ladder of definitions: invetigate how that recursive function is defined.
   - Example: line 204 in `Berlekamp_Zassenhaus/Arithmetic_Record_Based.thy`.
   - `goal (1 subgoal): 1. S (nth_default x xs n) (nth_default y ys n)`
   - `proof (induct arbitrary: n)`
   - But `nth_default` itself is not defined recursively, but its definition involves the `!` operator.
   - And because of the recursive definition of `!`, `n` in the proof goal should be generalized.

### Example (`itrev xs ys = rev xs @ ys` in `Concrete_Semantics/Induction_Demo.thy`)
- `apply (induction xs arbitrary ys)`
- `itrev` takes `xs` as its first argument.
- `ys` occurs as the second argument of this `itrev`.
- The second clause of the definition of `itrev` is as following:
   - `itrev (x#xs) ys = itrev xs (x#ys)`
   - Note that `ys` is the second parameter of `itrev` on the left-hand side of the definition.
   - Ad `ys` is used as part of the second argument of `itrev` on the right-hand side of the definition.
- `ys` in the proof oglibation is the second argument of `itrev`.
- Therefore, `ys` should be generalized.

### Other examples
- `exec_append[simp]: "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"` line 33 in `Concrete_Semantics/ASM.thy`.
- `(∀j. j ≠ i ⟶ netmap s' j = netmap s j) ∧ net_ip_action np (i:deliver(d)) i p s s'` line 488 in `AWN/Pnet.thy`.
- `is_binqueue_append: "is_binqueue l xs ⟹ is_binqueue (length xs + l) ys ⟹ is_binqueue l (xs @ ys)"` line 156 in `Binomial-Queues/Binomial_Queue.thy`.
- `lemma mono2_step: "c1 ≤ c2 ⟹ S1 ⊆ S2 ⟹ step S1 c1 ≤ step S2 c2"` line 155 in `Abs_Int_ITP2012/Collecting.thy`.
   - They probably focused on `c1 ≤ c2` when deciding induction terms. But they probably looked at `step S1 c1 ≤ step S2 c2` when deciding to generalize `S1` and `S2`.
- `shows "tensor_vec_from_lookup ds e = v"` line 125 in `Deep_Learning/Tensor.thy`.
   
## Generalization based on a bound variable in function definitions.

### Example
- `lemma length_tensor_vec_from_lookup: "length (tensor_vec_from_lookup ds e) = prod_list ds"` line 214 in `Deep_Learning/Tensor.thy`.
- It is induction on `ds`, which is the first argument of `tensor_vec_from_lookup` in the proof goal.
- `e` is the second argument of `tensor_vec_from_lookup` in the proof goal.
- In the second clause of `tensor_vec_from_lookup`, the recursive call of `tensor_vec_from_lookup` has a bound variable `i` inside its second argument.
- When `tensor_vec_from_lookup` is `map`ped over, `i` becomes a natural number smaller than `d`.
- And `d` is the first parameter on the left-hand side of the definition in this clause.
- Therefore, `e` in the proof goal should be generalized.

### Other examples
- `lemma lookup_tensor_vec:`
   - `assumes "is⊲ds" shows "lookup_base ds (tensor_vec_from_lookup ds e) is = e is"` line 217 in `Deep_Learning/Tensor.thy`.
   - Note that the recursion induction is applied to `is` and `ds` in `is⊲ds` as 
   -`proof (induction arbitrary:e rule:valid_index.induct).
   - Note that the recursion induction is applied to `is` and `ds` in `is⊲ds` as  `proof (induction arbitrary:e rule:valid_index.induct).
   - Note that the recursion induction is applied to `is` and `ds` in `is⊲ds` as `proof (induction arbitrary:e rule:valid_index.induct).
   - This proof script is equivalent to `proof (induction "is" ds arbitrary:e rule:valid_index.induct)`.
   - But the generalization heuristic is applied to `tensor_vec_from_lookup ds e`.
   
## The position of induction terms relative to a recursive function for a difference occurrence of the same recursive function.

### Examples
- `using this: x ≤ y y ≤ z goal (1 subgoal):  1. x ≤ z` line 53 in `Abs_Int_ITP2012/Collecting.thy`.
   - `apply(induct x y arbitrary: z rule: less_eq_acom.induct)`
   - Note that the current implementation of `Dynaimc (Induct)` probably cannot find `less_eq_acom.induct`.
-  `(eq, eq') ∈ R → R → bool_rel ⟹ (l1, l1') ∈ ⟨R⟩list_rel ⟹ (l2, l2') ∈ ⟨R⟩list_rel ⟹ (local.list_eq eq l1 l2, local.list_eq eq' l1' l2') ∈ bool_rel` line 515 `Automatic_Refinement/Autoref_Bidings_HOL.thy`.
   - `apply (induct eq' l1' l2' arbitrary: (*eq*) l1 l2 rule: list_eq.induct)`
   - `eq'`, `l1'`, and `l2'` are arguments of `local.list_eq`. 
   - `eq`, `l1`, and `l2` are arguments of a different occurrence of `local.list_eq`.
- `lemma cf_similarI: assumes "x ∈ CF" "y ∈ CF" and "opaque x = opaque y" and "CF_pure x ↔ CF_pure y" shows "x ≅ y"`
   - `using assms proof (induction (*x*) arbitrary: y)` where `x` is optional (did not appear in the original script).
   - Well... it turned out that this proof goes through without `arbitrary:y`.
- `lemma mono_step': "S ⊑ S' ⟹ c ⊑ c' ⟹ step' S c ⊑ step' S' c'"`
   - line 390 in `Abs_Int_ITP2012/Abs_Int0.thy`.
   - `apply(induction c c' arbitrary: S S' rule: le_acom.induct)`
   - This is induction on `c` and `c'` in `S ⊑ S'`.

## Multiple occurrences in the same positions relative to a recursive function that takes induction terms.

### Examples
- `using this:`
   - `R x X` 
   - `R y Y` 
   - `goal (1 subgoal): 1. R (gcd_eucl_i x y) (normalization_euclidean_semiring_class.gcd X Y)`
   - `proof (induct X Y arbitrary: x y rule: Euclidean_Algorithm.gcd.induct)`
   - line 135 in `Berlekamp_Yassenhaus/Arithmetic_Record_Based.thy`
   - This is induction on `X` and `Y` in `gcd X Y`.
   - `gcd X Y` is the second argument to `R` in the goal.
   - The first argument to this occurrence of `R` is `gcd_eucl_i x y`, which contains `x` and `y`.
   - These induction variables `X`  and `Y` appear in the chained facts as the second arguments to `R`.
   - And `x` and `y` are the first arguments to those occurrences of `R`.
   - Therefore, `x` and `y` should be generalized.
- `lemma mono_step': "S ⊑ S' ⟹ c ⊑ c' ⟹ step' S c ⊑ step' S' c'"`
   - `apply(induction c c' arbitrary: S S' rule: le_acom.induct)`
   - line 390 in `Abs_Int_ITP2012/Abs_Int0.thy`.
   - This is induction on `S` and `S'` in `S ⊑ S'`.
   - `c` and `c'` are also arguments of a difference occurrence of `⊑`.
   - Therefore, `c` and `c'` should be generalized.
   
## The variables on the other side of equation of induction terms.
- especially for equations appearing in assupmtions.

### Examples
- `lemma size_partition: "partition p t = (l',r') ⟹ size t = size l' + size r'"`
   - `by (induction p t arbitrary: l' r' rule: partition.induct)`
   - line 52 in `Splay_Tree/Splay_Heap.thy`
   - Induction on `p` and `t` in `partition p t`, which appears on the left-hand side of an equation.
   - `l'` and `r'` appear in `(l',r')` on the right-hand side of the same equation.
   - Neither `l'` or `r'` is "hidden" by any recursive function.
   - Therefore, `l'` and `r'` should be generalized.
- `lemma bot_acom[rule_format]: "strip c' = c ⟶ ⊥⇩c c ⊑ c'"`
   - `apply(induct c arbitrary: c')`
   - line 173 in `Abs_Int_ITP2012/Abs_Int0.thy`
   - Note that one can complete this proof starting with `apply(induct c' arbitrary: c)` instead of `apply(induct c arbitrary: c')`.
- `have "min xs ≠ Some a"`
   - line 485 in `Binomial-Queue/Binomial_Queue.thy`.
   - `proof (induct xs arbitrary: a)`
- line 40 in `AWN/Pnet.thy`
   - `assume "s ∈ init (pnet np p)"`
   - `thus "net_ips s = net_tree_ips p"`
   - `proof (induction p arbitrary: s)`

## Generalization of variables appearing in induction terms.

### Examples
- line 19 in `AWN/OPnet_Lifting.thy`.
   - `using this: (σ, SubnetS s t) ∈ oreachable (opnet onp (p⇩1 ∥ p⇩2)) S U `
   - `goal (1 subgoal): 1. P σ s t`
   - `using assms proof (induction p arbitrary: s a s')`
   
- line 133 in `AWN/Pnet.thy`
   - `using this:`
   - `SubnetS s t ∈ reachable (pnet np (p1 ∥ p2)) I`
   - `goal (1 subgoal): 1. P s t`
   - `proof (induction "SubnetS s t" arbitrary: s t)`

## Generalization involving the membership function.
- line 40 in `AWN/Pnet.thy`
   - `assume "s ∈ init (pnet np p)"`
   - `thus "net_ips s = net_tree_ips p"`
   - `proof (induction p arbitrary: s)`
   - Induction on `p`, and
   - `p` appears on the right-hand side of `∈`, and
   - `s` appears on the left-hand side of `∈`,
   - Probably `s` should be generalized.
   
- line 95 in `Abs_Int_ITP2012/Collection.thy`
   - `a ∈ A ⟹ lift Inter (strip a) A ≤ a`
   - `proof(induction a arbitrary: A)`
   - Induction on `a`, and
   - `a` appears in `a ∈ A` in the assumption.
   - Probably `A` should be generalized.
   
- line 106 in `Abs_Int_ITP2012/Collection.thy`
   - `using this:`
   - `b ∈ {c'. strip c' = i}`
   - `∀a∈A. b ≤ a`
   - `goal (1 subgoal): 1. b ≤ lift Inter i A`
   - `(induction b arbitrary: i A)`
   
- line 16 in `AWN/Pnet.thy`
   - `lemma pnet_maintains_dom:`
   - `assumes "(s, a, s') ∈ trans (pnet np p)"`
   - `shows "net_ips s = net_ips s'"`
   - `using assms proof (induction p arbitrary: s a s')`
   - `p` appears as part of the second argument of `∈` in the assumption.
   - `s`, `a`, and `s'` appear as part of the first argument of `∈` in the assumption.

## Generalize pointfree-style arguments.

### Examples
- TODO

# Non-generalization heuristics

## Non-generalization based on control-flow analysis of function definitions.
- If we apply induction on `xs`,
- `xs` is the nth argument of an occurrence of `foo`, 
- the `induct` method does not take any argument in the `rule` field, and
- in any recursive call of `foo` on the right-hand side in its definition
   - the mth argument of `foo` is always as same as the mth parameter on the left-hand side,
- then no variables appearing as part of the mth argument of any `foo` should be generalized.

### Example (`(∀j. j ≠ i ⟶ netmap s' j = netmap s j) ∧ net_ip_action np (i:deliver(d)) i p s s'` line 488 in `AWN/Pnet.thy`)
- `proof (induction p arbitrary: s s')`
- `p` is the fourth argument of an occurrence of `net_ip_action`.
- In the definition of `net_ip_action`, we have two recursive calls.
   - In both calls, the first three parameters `np`, `a`, and `i` are used as the first three arguments without any change.
- `np`, `i`, and `d` are part of the first three arguments to the only occurrence of `net_ip_action` in the proof goal.
- Therefore, `np`, `i`, and `d` should not be generalized.

### Other examples
- `exec_append[simp]: "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"` line 33 in `Concrete_Semantics/ASM.thy`.

# Induction term heuristics

## Induction on terms that have maximum number of recursive functions above them in the syntax tree.

### Examples
- `lemma is_binqueue_append:`
- `"is_binqueue l xs ⟹ is_binqueue (length xs + l) ys ⟹ is_binqueue l (xs @ ys)"`
- `by (induct xs arbitrary: l)`
- line 154 in `Bionmial_Queses/Binomial_Queue.thy`.
- The occurrence of `xs` in the conclusion has `@` and `is_binqueue`, and both of them are defined recursively.

## Terms of type constructors are more likely to be inducted on than terms of type variables of function types.
- Especially there is no argument in the `rule` field.

### Examples

- line 204 in `Berlekamp_Zassenhaus/Arithmetic_Record_Based.thy`
   - `goal (1 subgoal): 1. S (nth_default x xs n) (nth_default y ys n)`
   - `y(induct l' arbitrary: σ')`

- line 30 in `Binomial-Queues/Binomial_Queue.thy`
   - `goal (1 subgoal): 1. P xs`
   - `proof (induct xs)`
   - The type of `P` is a function type, whereas the type of `xs` is `'a option list`.
