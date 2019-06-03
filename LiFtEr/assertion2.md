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
- `lemma lookup_tensor_vec: assumes "is⊲ds" shows "lookup_base ds (tensor_vec_from_lookup ds e) is = e is"` line 217 in `Deep_Learning/Tensor.thy`.
   - Note that the recursion induction is applied to `is` and `ds` in `is⊲ds` as `proof (induction arbitrary:e rule:valid_index.induct)proof (induction arbitrary:e rule:valid_index.induct)`.
   - This proof script is equivalent to `proof (induction "is" ds arbitrary:e rule:valid_index.induct)`.
   - But the generalization heuristic is applied to `tensor_vec_from_lookup ds e`.
   
## The same relative position heuristics.

### Other examples
- `using this: x ≤ y y ≤ z goal (1 subgoal):  1. x ≤ z` line 53 in `Abs_Int_ITP2012/Collecting.thy`.
   - `apply(induct x y arbitrary: z rule: less_eq_acom.induct)`
   - Note that the current implementation of `Dynaimc (Induct)` probably cannot find `less_eq_acom.induct`.
-  `(eq, eq') ∈ R → R → bool_rel ⟹ (l1, l1') ∈ ⟨R⟩list_rel ⟹ (l2, l2') ∈ ⟨R⟩list_rel ⟹ (local.list_eq eq l1 l2, local.list_eq eq' l1' l2') ∈ bool_rel` line 515 `Automatic_Refinement/Autoref_Bidings_HOL.thy`.
   - `apply (induct eq' l1' l2' arbitrary: (*eq*) l1 l2 rule: list_eq.induct)`

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
