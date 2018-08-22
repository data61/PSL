subsection \<open>Parametricity of the State Monad\<close>

theory DP_CRelVS
  imports "./State_Monad_Ext" "../Pure_Monad"
begin

definition lift_p :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'a) state \<Rightarrow> bool" where
  "lift_p P f =
    (\<forall> heap. P heap \<longrightarrow> (case State_Monad.run_state f heap of (_, heap) \<Rightarrow> P heap))"

context
  fixes P f heap
  assumes lift: "lift_p P f" and P: "P heap"
begin

lemma run_state_cases:
  "case State_Monad.run_state f heap of (_, heap) \<Rightarrow> P heap"
  using lift P unfolding lift_p_def by auto

lemma lift_p_P:
  "P heap'" if "State_Monad.run_state f heap = (v, heap')"
  using that run_state_cases by auto

end

locale state_mem_defs =
  fixes lookup :: "'param \<Rightarrow> ('mem, 'result option) state"
    and update :: "'param \<Rightarrow> 'result \<Rightarrow> ('mem, unit) state"
begin

definition checkmem :: "'param \<Rightarrow> ('mem, 'result) state \<Rightarrow> ('mem, 'result) state" where
  "checkmem param calc \<equiv> do {
    x \<leftarrow> lookup param;
    case x of
      Some x \<Rightarrow> State_Monad.return x
    | None \<Rightarrow> do {
        x \<leftarrow> calc;
        update param x;
        State_Monad.return x
      }
  }"

abbreviation checkmem_eq ::
  "('param \<Rightarrow> ('mem, 'result) state) \<Rightarrow> 'param \<Rightarrow> ('mem, 'result) state \<Rightarrow> bool"
  ("_$ _ =CHECKMEM= _" [1000,51] 51) where
  "(dp\<^sub>T$ param =CHECKMEM= calc) \<equiv> (dp\<^sub>T param = checkmem param calc)"
term 0 (**)

definition map_of where
  "map_of heap k = fst (run_state (lookup k) heap)"

definition checkmem' :: "'param \<Rightarrow> (unit \<Rightarrow> ('mem, 'result) state) \<Rightarrow> ('mem, 'result) state" where
  "checkmem' param calc \<equiv> do {
    x \<leftarrow> lookup param;
    case x of
      Some x \<Rightarrow> State_Monad.return x
    | None \<Rightarrow> do {
        x \<leftarrow> calc ();
        update param x;
        State_Monad.return x
      }
  }"

lemma checkmem_checkmem':
  "checkmem' param (\<lambda>_. calc) = checkmem param calc"
  unfolding checkmem'_def checkmem_def ..

lemma checkmem_eq_alt:
  "checkmem_eq dp param calc = (dp param = checkmem' param (\<lambda> _. calc))"
  unfolding checkmem_checkmem' ..

end (* Mem Defs *)


locale mem_correct = state_mem_defs +
  fixes P
  assumes lookup_inv: "lift_p P (lookup k)" and update_inv: "lift_p P (update k v)"
  assumes
    lookup_correct: "P m \<Longrightarrow> map_of (snd (State_Monad.run_state (lookup k) m)) \<subseteq>\<^sub>m (map_of m)"
      and
    update_correct: "P m \<Longrightarrow> map_of (snd (State_Monad.run_state (update k v) m)) \<subseteq>\<^sub>m (map_of m)(k \<mapsto> v)"
  (* assumes correct: "lookup (update m k v) \<subseteq>\<^sub>m (lookup m)(k \<mapsto> v)" *)

locale dp_consistency =
  mem_correct lookup update P
  for lookup :: "'param \<Rightarrow> ('mem, 'result option) state" and update and P +
  fixes dp :: "'param \<Rightarrow> 'result"
begin

context
  includes lifting_syntax state_monad_syntax
begin

definition cmem :: "'mem \<Rightarrow> bool" where
  "cmem M \<equiv> \<forall>param\<in>dom (map_of M). map_of M param = Some (dp param)"

definition crel_vs :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('mem, 'b) state \<Rightarrow> bool" where
  "crel_vs R v s \<equiv> \<forall>M. cmem M \<and> P M \<longrightarrow> (case State_Monad.run_state s M of (v', M') \<Rightarrow> R v v' \<and> cmem M' \<and> P M')"
  
abbreviation rel_fun_lifted :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('c ==_\<Longrightarrow> 'd) \<Rightarrow> bool" (infixr "===>\<^sub>T" 55) where
  "rel_fun_lifted R R' \<equiv> R ===> crel_vs R'"
term 0 (**)

definition consistentDP :: "('param == 'mem \<Longrightarrow> 'result) \<Rightarrow> bool" where
  "consistentDP \<equiv> (op = ===> crel_vs op =) dp"
term 0 (**)
  
  (* cmem *)
private lemma cmem_intro:
  assumes "\<And>param v M'. State_Monad.run_state (lookup param) M = (Some v, M') \<Longrightarrow> v = dp param"
  shows "cmem M"
  unfolding cmem_def map_of_def
  apply safe
  subgoal for param y
    by (cases "State_Monad.run_state (lookup param) M") (auto intro: assms)
  done

lemma cmem_elim:
  assumes "cmem M" "State_Monad.run_state (lookup param) M = (Some v, M')"
  obtains "dp param = v"
  using assms unfolding cmem_def dom_def map_of_def by auto (metis fst_conv option.inject)
term 0 (**)
  
  (* crel_vs *)
lemma crel_vs_intro:
  assumes "\<And>M v' M'. \<lbrakk>cmem M; P M; State_Monad.run_state v\<^sub>T M = (v', M')\<rbrakk> \<Longrightarrow> R v v' \<and> cmem M' \<and> P M'"
  shows "crel_vs R v v\<^sub>T"
  using assms unfolding crel_vs_def by blast
term 0 (**)
  
lemma crel_vs_elim:
  assumes "crel_vs R v v\<^sub>T" "cmem M" "P M"
  obtains v' M' where "State_Monad.run_state v\<^sub>T M = (v', M')" "R v v'" "cmem M'" "P M'"
  using assms unfolding crel_vs_def by blast
term 0 (**)
  
  (* consistentDP *)
lemma consistentDP_intro:
  assumes "\<And>param. Transfer.Rel (crel_vs op=) (dp param) (dp\<^sub>T param)"
  shows "consistentDP dp\<^sub>T"
  using assms unfolding consistentDP_def Rel_def by blast
  
lemma crel_vs_return:
  "\<lbrakk>Transfer.Rel R x y\<rbrakk> \<Longrightarrow> Transfer.Rel (crel_vs R) (Wrap x) (State_Monad.return y)"
  unfolding State_Monad.return_def Wrap_def Rel_def by (fastforce intro: crel_vs_intro)
term 0 (**)
  
lemma crel_vs_return_ext:
  "\<lbrakk>Transfer.Rel R x y\<rbrakk> \<Longrightarrow> Transfer.Rel (crel_vs R) x (State_Monad.return y)"
  by (fact crel_vs_return[unfolded Wrap_def])
term 0 (**)

  (* Low level operators *)
private lemma cmem_upd:
  "cmem M'" if "cmem M" "P M" "State_Monad.run_state (update param (dp param)) M = (v, M')"
  using update_correct[of M param "dp param"] that unfolding cmem_def map_le_def by simp force

private lemma P_upd:
  "P M'" if "P M" "State_Monad.run_state (update param (dp param)) M = (v, M')"
  by (meson lift_p_P that update_inv)

private lemma crel_vs_get:
  "\<lbrakk>\<And>M. cmem M \<Longrightarrow> crel_vs R v (sf M)\<rbrakk> \<Longrightarrow> crel_vs R v (State_Monad.get \<bind> sf)"
  unfolding State_Monad.get_def State_Monad.bind_def by (fastforce intro: crel_vs_intro elim: crel_vs_elim split: prod.split)
term 0 (**)
  
private lemma crel_vs_set:
  "\<lbrakk>crel_vs R v sf; cmem M; P M\<rbrakk> \<Longrightarrow> crel_vs R v (State_Monad.set M \<then> sf)"
  unfolding State_Monad.set_def State_Monad.bind_def by (fastforce intro: crel_vs_intro elim: crel_vs_elim split: prod.split)
term 0 (**)
  
private lemma crel_vs_bind_eq:
  "\<lbrakk>crel_vs op = v s; crel_vs R (f v) (sf v)\<rbrakk> \<Longrightarrow> crel_vs R (f v) (s \<bind> sf)"
  unfolding State_Monad.bind_def rel_fun_def by (fastforce intro: crel_vs_intro elim: crel_vs_elim split: prod.split)
term 0 (**)

lemma bind_transfer[transfer_rule]:
  "(crel_vs R0 ===> (R0 ===>\<^sub>T R1) ===> crel_vs R1) (\<lambda>v f. f v) (op \<bind>)"
  unfolding State_Monad.bind_def rel_fun_def by (fastforce intro: crel_vs_intro elim: crel_vs_elim split: prod.split)

private lemma cmem_lookup:
  "cmem M'" if "cmem M" "P M" "State_Monad.run_state (lookup param) M = (v, M')"
  using lookup_correct[of M param] that unfolding cmem_def map_le_def by force

private lemma P_lookup:
  "P M'" if "P M" "State_Monad.run_state (lookup param) M = (v, M')"
  by (meson lift_p_P that lookup_inv)

lemma crel_vs_lookup:
  "crel_vs (\<lambda> v v'. case v' of None \<Rightarrow> True | Some v' \<Rightarrow> v = v' \<and> v = dp param) (dp param) (lookup param)"
  by (auto elim: cmem_elim intro: cmem_lookup crel_vs_intro P_lookup split: option.split)

lemma crel_vs_update:
  "crel_vs op = () (update param (dp param))"
  by (auto intro: cmem_upd crel_vs_intro P_upd)

private lemma crel_vs_checkmem:
  "\<lbrakk>is_equality R; Transfer.Rel (crel_vs R) (dp param) s\<rbrakk>
  \<Longrightarrow> Transfer.Rel (crel_vs R) (dp param) (checkmem param s)"
  unfolding checkmem_def Rel_def is_equality_def
  by (rule bind_transfer[unfolded rel_fun_def, rule_format, OF crel_vs_lookup])
     (auto 4 3 intro: crel_vs_lookup crel_vs_update crel_vs_return[unfolded Rel_def Wrap_def] crel_vs_bind_eq
               split: option.split_asm
     )

lemma crel_vs_checkmem_tupled:
  assumes "v = dp param"
  shows "\<lbrakk>is_equality R; Transfer.Rel (crel_vs R) v s\<rbrakk>
        \<Longrightarrow> Transfer.Rel (crel_vs R) v (checkmem param s)"
  unfolding assms by (fact crel_vs_checkmem)

  (** Transfer rules **)
  (* Basics *)
lemma return_transfer[transfer_rule]:
  "(R ===>\<^sub>T R) Wrap State_Monad.return"
  unfolding rel_fun_def by (metis crel_vs_return Rel_def)

lemma fun_app_lifted_transfer[transfer_rule]:
  "(crel_vs (R0 ===>\<^sub>T R1) ===> crel_vs R0 ===> crel_vs R1) App (op .)"
  unfolding App_def fun_app_lifted_def by transfer_prover
    
lemma crel_vs_fun_app:
  "\<lbrakk>Transfer.Rel (crel_vs R0) x x\<^sub>T; Transfer.Rel (crel_vs (R0 ===>\<^sub>T R1)) f f\<^sub>T\<rbrakk> \<Longrightarrow> Transfer.Rel (crel_vs R1) (App f x) (f\<^sub>T . x\<^sub>T)"
  unfolding Rel_def using fun_app_lifted_transfer[THEN rel_funD, THEN rel_funD] .

  (* HOL *)
lemma if\<^sub>T_transfer[transfer_rule]:
  "(crel_vs op = ===> crel_vs R ===> crel_vs R ===> crel_vs R) If State_Monad_Ext.if\<^sub>T"
  unfolding State_Monad_Ext.if\<^sub>T_def by transfer_prover
end (* Lifting Syntax *)

end (* Consistency *)
end (* Theory *)