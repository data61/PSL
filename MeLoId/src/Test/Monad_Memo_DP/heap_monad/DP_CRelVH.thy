subsection \<open>Parametricity of the Heap Monad\<close>

theory DP_CRelVH
  imports State_Heap
begin

locale dp_heap =
  state_dp_consistency: dp_consistency lookup_st update_st P dp + heap_mem_defs Q lookup update
  for P Q :: "heap \<Rightarrow> bool" and dp :: "'k \<Rightarrow> 'v" and lookup :: "'k \<Rightarrow> 'v option Heap"
  and lookup_st update update_st +
  assumes
    rel_state_lookup: "rel_fun op = (rel_state op =) lookup_st lookup"
      and
    rel_state_update: "rel_fun op = (rel_fun op = (rel_state op =)) update_st update"
begin

context
  includes lifting_syntax heap_monad_syntax
begin

definition "crel_vs R v f \<equiv>
  \<forall>heap. P heap \<and> Q heap \<and> state_dp_consistency.cmem heap \<longrightarrow>
    (case execute f heap of
      None \<Rightarrow> False |
      Some (v', heap') \<Rightarrow> P heap' \<and> Q heap' \<and> R v v' \<and> state_dp_consistency.cmem heap'
    )
"

abbreviation rel_fun_lifted :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('c ==H\<Longrightarrow> 'd) \<Rightarrow> bool" (infixr "===>\<^sub>T" 55) where
  "rel_fun_lifted R R' \<equiv> R ===> crel_vs R'"


definition consistentDP :: "('k \<Rightarrow> 'v Heap) \<Rightarrow> bool" where
  "consistentDP \<equiv> (op = ===> crel_vs op =) dp"

lemma consistentDP_intro:
  assumes "\<And>param. Transfer.Rel (crel_vs op=) (dp param) (dp\<^sub>T param)"
  shows "consistentDP dp\<^sub>T"
  using assms unfolding consistentDP_def Rel_def by blast

lemma crel_vs_execute_None:
  False if "crel_vs R a b" "execute b heap = None" "P heap" "Q heap" "state_dp_consistency.cmem heap"
  using that unfolding crel_vs_def by auto

lemma crel_vs_execute_Some:
  assumes "crel_vs R a b" "P heap" "Q heap" "state_dp_consistency.cmem heap"
  obtains x heap' where "execute b heap = Some (x, heap')" "P heap'" "Q heap'"
  using assms unfolding crel_vs_def by (cases "execute b heap") auto

lemma crel_vs_executeD:
  assumes "crel_vs R a b" "P heap" "Q heap" "state_dp_consistency.cmem heap"
  obtains x heap' where
    "execute b heap = Some (x, heap')" "P heap'" "Q heap'" "state_dp_consistency.cmem heap'" "R a x"
  using assms unfolding crel_vs_def by (cases "execute b heap") auto

lemma crel_vs_success:
  assumes "crel_vs R a b" "P heap" "Q heap" "state_dp_consistency.cmem heap"
  shows "success b heap"
  using assms unfolding success_def by (auto elim: crel_vs_executeD)

lemma crel_vsI: "crel_vs R a b" if "(state_dp_consistency.crel_vs R OO rel_state (op =)) a b"
  using that by (auto 4 3 elim: state_dp_consistency.crel_vs_elim rel_state_elim simp: crel_vs_def)

lemma transfer'_return[transfer_rule]:
  "(R ===> crel_vs R) Wrap return"
proof -
  have "(R ===> (state_dp_consistency.crel_vs R OO rel_state (op =))) Wrap return"
    by (rule rel_fun_comp1 state_dp_consistency.return_transfer transfer_return)+ auto
  then show ?thesis
    by (blast intro: rel_fun_mono crel_vsI)
qed

lemma crel_vs_return:
  "Transfer.Rel (crel_vs R) (Wrap x) (return y)" if "Transfer.Rel R x y"
  using that unfolding Rel_def by (rule transfer'_return[unfolded rel_fun_def, rule_format])

lemma crel_vs_return_ext:
  "\<lbrakk>Transfer.Rel R x y\<rbrakk> \<Longrightarrow> Transfer.Rel (crel_vs R) x (Heap_Monad.return y)"
  by (fact crel_vs_return[unfolded Wrap_def])
term 0 (**)

lemma bind_transfer[transfer_rule]:
  "(crel_vs R0 ===> (R0 ===> crel_vs R1) ===> crel_vs R1) (\<lambda>v f. f v) (op \<bind>)"
  unfolding rel_fun_def bind_def
  by safe (subst crel_vs_def, auto 4 4 elim: crel_vs_execute_Some elim!: crel_vs_executeD)


lemma crel_vs_update:
  "crel_vs op = () (update param (dp param))"
  by (rule
      crel_vsI relcomppI state_dp_consistency.crel_vs_update
      rel_state_update[unfolded rel_fun_def, rule_format] HOL.refl
     )+

lemma crel_vs_lookup:
  "crel_vs
    (\<lambda> v v'. case v' of None \<Rightarrow> True | Some v' \<Rightarrow> v = v' \<and> v = dp param) (dp param) (lookup param)"
  by (rule
      crel_vsI relcomppI state_dp_consistency.crel_vs_lookup
      rel_state_lookup[unfolded rel_fun_def, rule_format] HOL.refl
     )+

lemma crel_vs_eq_eq_onp:
  "crel_vs (eq_onp (\<lambda> x. x = v)) v s" if "crel_vs op = v s"
  using that unfolding crel_vs_def by (auto split: option.split simp: eq_onp_def)

lemma crel_vs_bind_eq:
  "\<lbrakk>crel_vs op = v s; crel_vs R (f v) (sf v)\<rbrakk> \<Longrightarrow> crel_vs R (f v) (s \<bind> sf)"
  by (erule bind_transfer[unfolded rel_fun_def, rule_format, OF crel_vs_eq_eq_onp])
     (auto simp: eq_onp_def)

lemma crel_vs_checkmem:
  "Transfer.Rel (crel_vs R) (dp param) (checkmem param s)" if "is_equality R" "Transfer.Rel (crel_vs R) (dp param) s"
  unfolding checkmem_def Rel_def that(1)[unfolded is_equality_def]
  by (rule bind_transfer[unfolded rel_fun_def, rule_format, OF crel_vs_lookup])
     (auto 4 3 split: option.split_asm intro: crel_vs_bind_eq crel_vs_update crel_vs_return[unfolded Wrap_def Rel_def] that(2)[unfolded Rel_def that(1)[unfolded is_equality_def]])

lemma crel_vs_checkmem_tupled:
  assumes "v = dp param"
  shows "\<lbrakk>is_equality R; Transfer.Rel (crel_vs R) v s\<rbrakk>
        \<Longrightarrow> Transfer.Rel (crel_vs R) v (checkmem param s)"
  unfolding assms by (fact crel_vs_checkmem)

lemma transfer_fun_app_lifted[transfer_rule]:
  "(crel_vs (R0 ===> crel_vs R1) ===> crel_vs R0 ===> crel_vs R1)
    App Heap_Monad_Ext.fun_app_lifted"
  unfolding Heap_Monad_Ext.fun_app_lifted_def App_def by transfer_prover

lemma crel_vs_fun_app:
  "\<lbrakk>Transfer.Rel (crel_vs R0) x x\<^sub>T; Transfer.Rel (crel_vs (R0 ===>\<^sub>T R1)) f f\<^sub>T\<rbrakk> \<Longrightarrow> Transfer.Rel (crel_vs R1) (App f x) (f\<^sub>T . x\<^sub>T)"
  unfolding Rel_def using transfer_fun_app_lifted[THEN rel_funD, THEN rel_funD] .

end (* Lifting Syntax *)

end (* Dynamic Programming Problem *)

locale dp_consistency_heap = heap_correct +
  fixes dp :: "'a \<Rightarrow> 'b"
begin

interpretation state_mem_correct: mem_correct lookup' update' P
  by (rule mem_correct_heap)

interpretation state_dp_consistency: dp_consistency lookup' update' P dp ..

lemma dp_heap: "dp_heap P P lookup lookup' update update'"
  by (standard; rule transfer_lookup transfer_update)

sublocale dp_heap P P dp lookup lookup' update update'
  by (rule dp_heap)

notation rel_fun_lifted (infixr "===>\<^sub>T" 55)
end

locale heap_correct_empty = heap_correct +
  fixes empty
  assumes empty_correct: "map_of_heap empty \<subseteq>\<^sub>m Map.empty" and P_empty: "P empty"

locale dp_consistency_heap_empty =
  dp_consistency_heap + heap_correct_empty
begin

lemma cmem_empty:
  "state_dp_consistency.cmem empty"
  using empty_correct
  unfolding state_dp_consistency.cmem_def
  unfolding map_of_heap_def
  unfolding state_dp_consistency.map_of_def
  unfolding lookup'_def
  unfolding map_le_def
  by auto

corollary memoization_correct:
  "dp x = v" "state_dp_consistency.cmem m" if
  "consistentDP dp\<^sub>T" "Heap_Monad.execute (dp\<^sub>T x) empty = Some (v, m)"
  using that unfolding consistentDP_def
  by (auto dest!: rel_funD[where x = x] elim!: crel_vs_executeD intro: P_empty cmem_empty)

lemma memoized_success:
  "success (dp\<^sub>T x) empty" if "consistentDP dp\<^sub>T"
  using that cmem_empty P_empty
  by (auto dest!: rel_funD intro: crel_vs_success simp: consistentDP_def)

lemma memoized:
  "dp x = fst (the (Heap_Monad.execute (dp\<^sub>T x) empty))" if "consistentDP dp\<^sub>T"
  using surjective_pairing memoization_correct(1)[OF that]
    memoized_success[OF that, unfolded success_def]
  by (cases "execute (dp\<^sub>T x) empty"; auto)

lemma cmem_result:
  "state_dp_consistency.cmem (snd (the (Heap_Monad.execute (dp\<^sub>T x) empty)))" if "consistentDP dp\<^sub>T"
  using surjective_pairing memoization_correct(2)[OF that(1)]
    memoized_success[OF that, unfolded success_def]
  by (cases "execute (dp\<^sub>T x) empty"; auto)

end

end (* Theory *)