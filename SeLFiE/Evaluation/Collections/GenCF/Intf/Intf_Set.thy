section \<open>\isaheader{Set Interface}\<close>
theory Intf_Set
imports Refine_Monadic.Refine_Monadic
begin
consts i_set :: "interface \<Rightarrow> interface"
lemmas [autoref_rel_intf] = REL_INTFI[of set_rel i_set]


definition [simp]: "op_set_delete x s \<equiv> s - {x}"
definition [simp]: "op_set_isEmpty s \<equiv> s = {}"
definition [simp]: "op_set_isSng s \<equiv> card s = 1"
definition [simp]: "op_set_size_abort m s \<equiv> min m (card s)"
definition [simp]: "op_set_disjoint a b \<equiv> a\<inter>b={}"
definition [simp]: "op_set_filter P s \<equiv> {x\<in>s. P x}"
definition [simp]: "op_set_sel P s \<equiv> SPEC (\<lambda>x. x\<in>s \<and> P x)"
definition [simp]: "op_set_pick s \<equiv> SPEC (\<lambda>x. x\<in>s)"
definition [simp]: "op_set_to_sorted_list ordR s 
  \<equiv> SPEC (\<lambda>l. set l = s \<and> distinct l \<and> sorted_wrt ordR l)"
definition [simp]: "op_set_to_list s \<equiv> SPEC (\<lambda>l. set l = s \<and> distinct l)"
definition [simp]: "op_set_cart x y \<equiv> x \<times> y"

(* TODO: Do op_set_pick_remove (like op_map_pick_remove) *)

context begin interpretation autoref_syn .
lemma [autoref_op_pat]:
  fixes s a b :: "'a set" and x::'a and P :: "'a \<Rightarrow> bool"
  shows
  "s - {x} \<equiv> op_set_delete$x$s"

  "s = {} \<equiv> op_set_isEmpty$s"
  "{}=s \<equiv> op_set_isEmpty$s"

  "card s = 1 \<equiv> op_set_isSng$s"
  "\<exists>x. s={x} \<equiv> op_set_isSng$s"
  "\<exists>x. {x}=s \<equiv> op_set_isSng$s"

  "min m (card s) \<equiv> op_set_size_abort$m$s"
  "min (card s) m \<equiv> op_set_size_abort$m$s"

  "a\<inter>b={} \<equiv> op_set_disjoint$a$b"

  "{x\<in>s. P x} \<equiv> op_set_filter$P$s"

  "SPEC (\<lambda>x. x\<in>s \<and> P x) \<equiv> op_set_sel$P$s"
  "SPEC (\<lambda>x. P x \<and> x\<in>s) \<equiv> op_set_sel$P$s"

  "SPEC (\<lambda>x. x\<in>s) \<equiv> op_set_pick$s"
  by (auto intro!: eq_reflection simp: card_Suc_eq)

lemma [autoref_op_pat]:
  "a \<times> b \<equiv> op_set_cart a b"
  by (auto intro!: eq_reflection simp: card_Suc_eq)

lemma [autoref_op_pat]:
  "SPEC (\<lambda>(u,v). (u,v)\<in>s) \<equiv> op_set_pick$s"
  "SPEC (\<lambda>(u,v). P u v \<and> (u,v)\<in>s) \<equiv> op_set_sel$(case_prod P)$s"
  "SPEC (\<lambda>(u,v). (u,v)\<in>s \<and> P u v) \<equiv> op_set_sel$(case_prod P)$s"
  by (auto intro!: eq_reflection)

  lemma [autoref_op_pat]:
    "SPEC (\<lambda>l. set l = s \<and> distinct l \<and> sorted_wrt ordR l) 
    \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. set l = s \<and> sorted_wrt ordR l \<and> distinct l) 
    \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. distinct l \<and> set l = s \<and> sorted_wrt ordR l) 
    \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. distinct l \<and> sorted_wrt ordR l \<and> set l = s) 
    \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. sorted_wrt ordR l \<and> distinct l \<and> set l = s) 
    \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. sorted_wrt ordR l \<and> set l = s \<and> distinct l) 
    \<equiv> OP (op_set_to_sorted_list ordR)$s"

    "SPEC (\<lambda>l. s = set l \<and> distinct l \<and> sorted_wrt ordR l) 
    \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. s = set l \<and> sorted_wrt ordR l \<and> distinct l) 
    \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. distinct l \<and> s = set l \<and> sorted_wrt ordR l) 
    \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. distinct l \<and> sorted_wrt ordR l \<and> s = set l) 
    \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. sorted_wrt ordR l \<and> distinct l \<and> s = set l) 
    \<equiv> OP (op_set_to_sorted_list ordR)$s"
    "SPEC (\<lambda>l. sorted_wrt ordR l \<and> s = set l \<and> distinct l) 
    \<equiv> OP (op_set_to_sorted_list ordR)$s"

    "SPEC (\<lambda>l. set l = s \<and> distinct l) \<equiv> op_set_to_list$s"
    "SPEC (\<lambda>l. distinct l \<and> set l = s) \<equiv> op_set_to_list$s"

    "SPEC (\<lambda>l. s = set l \<and> distinct l) \<equiv> op_set_to_list$s"
    "SPEC (\<lambda>l. distinct l \<and> s = set l) \<equiv> op_set_to_list$s"
    by (auto intro!: eq_reflection)

end

lemma [autoref_itype]:
  "{} ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "insert ::\<^sub>i I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "op_set_delete ::\<^sub>i I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "(\<in>) ::\<^sub>i I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_bool"
  "op_set_isEmpty ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_bool"
  "op_set_isSng ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_bool"
  "(\<union>) ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "(\<inter>) ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "((-) :: 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set) ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "((=) :: 'a set \<Rightarrow> 'a set \<Rightarrow> bool) ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_bool"
  "(\<subseteq>) ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_bool"
  "op_set_disjoint ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_bool"
  "Ball ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i (I \<rightarrow>\<^sub>i i_bool) \<rightarrow>\<^sub>i i_bool"
  "Bex ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i (I \<rightarrow>\<^sub>i i_bool) \<rightarrow>\<^sub>i i_bool"
  "op_set_filter ::\<^sub>i (I \<rightarrow>\<^sub>i i_bool) \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "card ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_nat"
  "op_set_size_abort ::\<^sub>i i_nat \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_nat"
  "set ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "op_set_sel ::\<^sub>i (I \<rightarrow>\<^sub>i i_bool) \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_nres"
  "op_set_pick ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_nres"
  "Sigma ::\<^sub>i \<langle>Ia\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i (Ia \<rightarrow>\<^sub>i \<langle>Ib\<rangle>\<^sub>ii_set) \<rightarrow>\<^sub>i \<langle>\<langle>Ia,Ib\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_set"
  "(`) ::\<^sub>i (Ia\<rightarrow>\<^sub>iIb) \<rightarrow>\<^sub>i \<langle>Ia\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>Ib\<rangle>\<^sub>ii_set"
  "op_set_cart ::\<^sub>i \<langle>Ix\<rangle>\<^sub>iIsx \<rightarrow>\<^sub>i \<langle>Iy\<rangle>\<^sub>iIsy \<rightarrow>\<^sub>i \<langle>\<langle>Ix, Iy\<rangle>\<^sub>ii_prod\<rangle>\<^sub>iIsp"
  "Union ::\<^sub>i \<langle>\<langle>I\<rangle>\<^sub>ii_set\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "atLeastLessThan ::\<^sub>i i_nat \<rightarrow>\<^sub>i i_nat \<rightarrow>\<^sub>i \<langle>i_nat\<rangle>\<^sub>ii_set"
  by simp_all

lemma hom_set1[autoref_hom]:
  "CONSTRAINT {} (\<langle>R\<rangle>Rs)"
  "CONSTRAINT insert (R\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT (\<in>) (R\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT (\<union>) (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT (\<inter>) (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT (-) (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT (=) (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT (\<subseteq>) (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT Ball (\<langle>R\<rangle>Rs\<rightarrow>(R\<rightarrow>Id)\<rightarrow>Id)"
  "CONSTRAINT Bex (\<langle>R\<rangle>Rs\<rightarrow>(R\<rightarrow>Id)\<rightarrow>Id)"
  "CONSTRAINT card (\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT set (\<langle>R\<rangle>Rl\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT (`) ((Ra\<rightarrow>Rb) \<rightarrow> \<langle>Ra\<rangle>Rs\<rightarrow>\<langle>Rb\<rangle>Rs)"
  "CONSTRAINT Union (\<langle>\<langle>R\<rangle>Ri\<rangle>Ro \<rightarrow> \<langle>R\<rangle>Ri)"
  by simp_all

lemma hom_set2[autoref_hom]:
  "CONSTRAINT op_set_delete (R\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT op_set_isEmpty (\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT op_set_isSng (\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT op_set_size_abort (Id\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT op_set_disjoint (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT op_set_filter ((R\<rightarrow>Id)\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT op_set_sel ((R \<rightarrow> Id)\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rn)"
  "CONSTRAINT op_set_pick (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rn)"
  by simp_all

lemma hom_set_Sigma[autoref_hom]:
  "CONSTRAINT Sigma (\<langle>Ra\<rangle>Rs \<rightarrow> (Ra \<rightarrow> \<langle>Rb\<rangle>Rs) \<rightarrow> \<langle>\<langle>Ra,Rb\<rangle>prod_rel\<rangle>Rs2)"
  by simp_all
  
definition "finite_set_rel R \<equiv> Range R \<subseteq> Collect (finite)"

lemma finite_set_rel_trigger: "finite_set_rel R \<Longrightarrow> finite_set_rel R" .

declaration \<open>Tagged_Solver.add_triggers 
  "Relators.relator_props_solver" @{thms finite_set_rel_trigger}\<close>

end
