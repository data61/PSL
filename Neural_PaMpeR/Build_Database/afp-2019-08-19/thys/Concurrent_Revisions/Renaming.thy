section Renaming

text \<open>Similar to the bound variables of lambda calculus, location and revision identifiers are meaningless
  names. This theory contains all of the definitions and results required for renaming data structures
  and proving renaming-equivalence.\<close>

theory Renaming
  imports Occurrences
begin

subsection Definitions

abbreviation rename_val :: "('r \<Rightarrow> 'r) \<Rightarrow> ('l \<Rightarrow> 'l) \<Rightarrow> ('r,'l,'v) val \<Rightarrow> ('r,'l,'v) val" ("\<R>\<^sub>V") where
  "\<R>\<^sub>V \<alpha> \<beta> v \<equiv> map_val \<alpha> \<beta> id v"

abbreviation rename_expr :: "('r \<Rightarrow> 'r) \<Rightarrow> ('l \<Rightarrow> 'l) \<Rightarrow> ('r,'l,'v) expr \<Rightarrow> ('r,'l,'v) expr" ("\<R>\<^sub>E") where
  "\<R>\<^sub>E \<alpha> \<beta> e \<equiv> map_expr \<alpha> \<beta> id e"

abbreviation rename_cntxt :: "('r \<Rightarrow> 'r) \<Rightarrow> ('l \<Rightarrow> 'l) \<Rightarrow> ('r,'l,'v) cntxt \<Rightarrow> ('r,'l,'v) cntxt" ("\<R>\<^sub>C") where
  "\<R>\<^sub>C \<alpha> \<beta> \<E> \<equiv> map_cntxt \<alpha> \<beta> id \<E>"

definition is_store_renaming :: "('r \<Rightarrow> 'r) \<Rightarrow> ('l \<Rightarrow> 'l) \<Rightarrow> ('r,'l,'v) store \<Rightarrow> ('r,'l,'v) store \<Rightarrow> bool" where 
  "is_store_renaming \<alpha> \<beta> \<sigma> \<sigma>' \<equiv> \<forall>l. case \<sigma> l of None \<Rightarrow> \<sigma>' (\<beta> l) = None | Some v \<Rightarrow> \<sigma>' (\<beta> l) = Some (\<R>\<^sub>V \<alpha> \<beta> v)"

notation Option.bind (infixl "\<bind>" 80)

fun \<R>\<^sub>S :: "('r \<Rightarrow> 'r) \<Rightarrow> ('l \<Rightarrow> 'l) \<Rightarrow> ('r,'l,'v) store \<Rightarrow> ('r,'l,'v) store" where
  "\<R>\<^sub>S \<alpha> \<beta> \<sigma> l = \<sigma> (inv \<beta> l) \<bind> (\<lambda>v. Some (\<R>\<^sub>V \<alpha> \<beta> v))"

lemma \<R>\<^sub>S_implements_renaming: "bij \<beta> \<Longrightarrow> is_store_renaming \<alpha> \<beta> \<sigma> (\<R>\<^sub>S \<alpha> \<beta> \<sigma>)"
proof -
  assume "bij \<beta>"
  hence "inj \<beta>" using bij_def by auto
  thus ?thesis by (auto simp add: is_store_renaming_def option.case_eq_if)
qed

fun \<R>\<^sub>L :: "('r \<Rightarrow> 'r) \<Rightarrow> ('l \<Rightarrow> 'l) \<Rightarrow> ('r,'l,'v) local_state \<Rightarrow> ('r,'l,'v) local_state" where
  "\<R>\<^sub>L \<alpha> \<beta> (\<sigma>,\<tau>,e) = (\<R>\<^sub>S \<alpha> \<beta> \<sigma>, \<R>\<^sub>S \<alpha> \<beta> \<tau>, \<R>\<^sub>E \<alpha> \<beta> e)"

definition is_global_renaming :: "('r \<Rightarrow> 'r) \<Rightarrow> ('l \<Rightarrow> 'l) \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> bool" where 
  "is_global_renaming \<alpha> \<beta> s s' \<equiv> \<forall>r. case s r of None \<Rightarrow> s' (\<alpha> r) = None | Some ls \<Rightarrow> s' (\<alpha> r) = Some (\<R>\<^sub>L \<alpha> \<beta> ls)"

fun \<R>\<^sub>G :: "('r \<Rightarrow> 'r) \<Rightarrow> ('l \<Rightarrow> 'l) \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> ('r,'l,'v) global_state" where
  "\<R>\<^sub>G \<alpha> \<beta> s r = s (inv \<alpha> r) \<bind> (\<lambda>ls. Some (\<R>\<^sub>L \<alpha> \<beta> ls))"

lemma \<R>\<^sub>G_implements_renaming: "bij \<alpha> \<Longrightarrow> is_global_renaming \<alpha> \<beta> s (\<R>\<^sub>G \<alpha> \<beta> s)"
proof -
  assume "bij \<alpha>"
  hence "inj \<alpha>" using bij_def by auto
  thus ?thesis by (auto simp add: is_global_renaming_def option.case_eq_if)
qed

subsection \<open>Introduction rules\<close>

lemma \<R>\<^sub>SI [intro]:
  assumes
    bij_\<beta>: "bij \<beta>" and
    none_case: "\<And>l. \<sigma> l = None \<Longrightarrow> \<sigma>' (\<beta> l) = None" and
    some_case: "\<And>l v. \<sigma> l = Some v \<Longrightarrow> \<sigma>' (\<beta> l) = Some (\<R>\<^sub>V \<alpha> \<beta> v)"
  shows
    "\<R>\<^sub>S \<alpha> \<beta> \<sigma> = \<sigma>'"
proof (rule ext, subst \<R>\<^sub>S.simps)
  fix l
  show "\<sigma> (inv \<beta> l) \<bind> (\<lambda>v. Some (\<R>\<^sub>V \<alpha> \<beta> v)) = \<sigma>' l" (is "?lhs = \<sigma>' l")
  proof (cases "\<sigma> (inv \<beta> l) = None")
    case True
    have lhs_none: "?lhs = None" by (simp add: True)
    have "\<sigma>' (\<beta> (inv \<beta> l)) = None" by (simp add: none_case True)
    hence rhs_none: "\<sigma>' l = None" by (simp add: bij_\<beta> bijection.intro bijection.inv_right)
    show ?thesis by (simp add: lhs_none rhs_none)
  next
    case False
    from this obtain v where is_some: "\<sigma> (inv \<beta> l) = Some v" by blast
    hence lhs_some: "?lhs = Some (\<R>\<^sub>V \<alpha> \<beta> v)" by auto
    have "\<sigma>' (\<beta> (inv \<beta> l)) = Some (\<R>\<^sub>V \<alpha> \<beta> v)" by (simp add: is_some some_case)
    hence rhs_some: "\<sigma>' l = Some (\<R>\<^sub>V \<alpha> \<beta> v)" by (simp add: bij_\<beta> bijection.intro bijection.inv_right)
    then show ?thesis by (simp add: lhs_some)
  qed
qed

lemma \<R>\<^sub>GI [intro]: 
  assumes
    bij_\<alpha>: "bij \<alpha>" and
    none_case: "\<And>r. s r = None \<Longrightarrow> s' (\<alpha> r) = None" and
    some_case: "\<And>r \<sigma> \<tau> e. s r = Some (\<sigma>,\<tau>,e) \<Longrightarrow> s' (\<alpha> r) = Some (\<R>\<^sub>L \<alpha> \<beta> (\<sigma>,\<tau>,e))"
  shows
    "\<R>\<^sub>G \<alpha> \<beta> s = s'"
proof (rule ext, subst \<R>\<^sub>G.simps)
  fix r
  show "s (inv \<alpha> r) \<bind> (\<lambda>ls. Some (\<R>\<^sub>L \<alpha> \<beta> ls)) = s' r" (is "?lhs = s' r")
  proof (cases "s (inv \<alpha> r) = None")
    case True
    have lhs_none: "?lhs = None" by (simp add: True)
    have "s' (\<alpha> (inv \<alpha> r)) = None" by (simp add: none_case True)
    hence rhs_none: "s' r = None" by (simp add: bij_\<alpha> bijection.intro bijection.inv_right)
    show ?thesis by (simp add: lhs_none rhs_none)
  next
    case False
    from this obtain ls where "s (inv \<alpha> r) = Some ls" by blast
    from this obtain \<sigma> \<tau> e where is_some: "s (inv \<alpha> r) = Some (\<sigma>, \<tau>, e)" by (cases ls) blast
    hence lhs_some: "?lhs = Some (\<R>\<^sub>L \<alpha> \<beta> (\<sigma>, \<tau>, e))" by auto
    have "s' (\<alpha> (inv \<alpha> r)) = Some (\<R>\<^sub>L \<alpha> \<beta> (\<sigma>, \<tau>, e))" by (simp add: is_some some_case)
    hence rhs_some: "s' r = Some (\<R>\<^sub>L \<alpha> \<beta> (\<sigma>, \<tau>, e))" by (simp add: bij_\<alpha> bijection.intro bijection.inv_right)
    then show ?thesis by (simp add: lhs_some)
  qed
qed

subsection \<open>Renaming-equivalence\<close>

subsubsection Identity

declare val.map_id [simp]
declare expr.map_id [simp]
declare cntxt.map_id [simp]
lemma \<R>\<^sub>S_id [simp]: "\<R>\<^sub>S id id \<sigma> = \<sigma>" by auto
lemma \<R>\<^sub>L_id [simp]: "\<R>\<^sub>L id id ls = ls" by (cases ls) simp
lemma \<R>\<^sub>G_id [simp]: "\<R>\<^sub>G id id s = s" by auto

subsubsection Composition

declare val.map_comp [simp]
declare expr.map_comp [simp]
declare cntxt.map_comp [simp]
lemma \<R>\<^sub>S_comp [simp]: "\<lbrakk> bij \<beta>; bij \<beta>' \<rbrakk> \<Longrightarrow> \<R>\<^sub>S \<alpha>' \<beta>' (\<R>\<^sub>S \<alpha> \<beta> s) = \<R>\<^sub>S (\<alpha>' \<circ> \<alpha>) (\<beta>' \<circ> \<beta>) s"
  by (auto simp add: o_inv_distrib)
lemma \<R>\<^sub>L_comp [simp]: "\<lbrakk> bij \<beta>; bij \<beta>' \<rbrakk> \<Longrightarrow> \<R>\<^sub>L \<alpha>' \<beta>' (\<R>\<^sub>L \<alpha> \<beta> ls) = \<R>\<^sub>L (\<alpha>' \<circ> \<alpha>) (\<beta>' \<circ> \<beta>) ls"
  by (cases ls) simp
lemma \<R>\<^sub>G_comp [simp]: "\<lbrakk> bij \<alpha>; bij \<alpha>'; bij \<beta>; bij \<beta>' \<rbrakk> \<Longrightarrow> \<R>\<^sub>G \<alpha>' \<beta>' (\<R>\<^sub>G \<alpha> \<beta> s) = \<R>\<^sub>G (\<alpha>' \<circ> \<alpha>) (\<beta>' \<circ> \<beta>) s"
  by (rule ext) (auto simp add: o_inv_distrib)

subsubsection Inverse

lemma \<R>\<^sub>V_inv [simp]: "\<lbrakk> bij \<alpha>; bij \<beta> \<rbrakk> \<Longrightarrow> (\<R>\<^sub>V (inv \<alpha>) (inv \<beta>) v' = v) = (\<R>\<^sub>V \<alpha> \<beta> v = v')"
  by (auto simp add: bijection.intro bijection.inv_comp_right bijection.inv_comp_left)
lemma \<R>\<^sub>E_inv [simp]: "\<lbrakk> bij \<alpha>; bij \<beta> \<rbrakk> \<Longrightarrow> (\<R>\<^sub>E (inv \<alpha>) (inv \<beta>) e' = e) = (\<R>\<^sub>E \<alpha> \<beta> e = e')"
  by (auto simp add: bijection.intro bijection.inv_comp_right bijection.inv_comp_left)
lemma \<R>\<^sub>C_inv [simp]: "\<lbrakk> bij \<alpha>; bij \<beta> \<rbrakk> \<Longrightarrow> (\<R>\<^sub>C (inv \<alpha>) (inv \<beta>) \<E>' = \<E>) = (\<R>\<^sub>C \<alpha> \<beta> \<E> = \<E>')"
  by (auto simp add: bijection.intro bijection.inv_comp_right bijection.inv_comp_left)
lemma \<R>\<^sub>S_inv [simp]: "\<lbrakk> bij \<alpha>; bij \<beta> \<rbrakk> \<Longrightarrow> (\<R>\<^sub>S (inv \<alpha>) (inv \<beta>) \<sigma>' = \<sigma>) = (\<R>\<^sub>S \<alpha> \<beta> \<sigma> = \<sigma>')"
  by (auto simp add: bij_imp_bij_inv bijection.intro bijection.inv_comp_right bijection.inv_comp_left)
lemma \<R>\<^sub>L_inv [simp]: "\<lbrakk> bij \<alpha>; bij \<beta> \<rbrakk> \<Longrightarrow> (\<R>\<^sub>L (inv \<alpha>) (inv \<beta>) ls' = ls) = (\<R>\<^sub>L \<alpha> \<beta> ls = ls')"
  by (auto simp add: bij_imp_bij_inv bijection.intro bijection.inv_comp_right bijection.inv_comp_left)
lemma \<R>\<^sub>G_inv [simp]: "\<lbrakk> bij \<alpha>; bij \<beta> \<rbrakk> \<Longrightarrow> (\<R>\<^sub>G (inv \<alpha>) (inv \<beta>) s' = s) = (\<R>\<^sub>G \<alpha> \<beta> s = s')"
  by (auto simp add: bij_imp_bij_inv bijection.intro bijection.inv_comp_right bijection.inv_comp_left)

subsubsection Equivalence

definition eq_states :: "('r,'l,'v) global_state \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> bool" ("_ \<approx> _" [100, 100]) where
  "s \<approx> s' \<equiv> \<exists>\<alpha> \<beta>. bij \<alpha> \<and> bij \<beta> \<and> \<R>\<^sub>G \<alpha> \<beta> s = s'"

lemma eq_statesI [intro]:
  "\<R>\<^sub>G \<alpha> \<beta> s = s' \<Longrightarrow> bij \<alpha> \<Longrightarrow> bij \<beta> \<Longrightarrow> s \<approx> s'"
  using eq_states_def by auto

lemma eq_statesE [elim]:
  "s \<approx> s' \<Longrightarrow> (\<And>\<alpha> \<beta>. \<R>\<^sub>G \<alpha> \<beta> s = s' \<Longrightarrow> bij \<alpha> \<Longrightarrow> bij \<beta> \<Longrightarrow> P) \<Longrightarrow> P"
  using eq_states_def by blast

lemma \<alpha>\<beta>_refl: "s \<approx> s" by (rule eq_statesI[of id id s]) auto
 
lemma \<alpha>\<beta>_trans: "s \<approx> s' \<Longrightarrow> s' \<approx> s'' \<Longrightarrow> s \<approx> s''"
proof -
  assume "s \<approx> s'"
  from this obtain \<alpha> \<beta> where s_s': "bij \<alpha>" "bij \<beta>" "\<R>\<^sub>G \<alpha> \<beta> s = s'" by blast
  assume "s' \<approx> s''"
  from this obtain \<alpha>' \<beta>' where s'_s'': "bij \<alpha>'" "bij \<beta>'" "\<R>\<^sub>G \<alpha>' \<beta>' s' = s''" by blast
  show "s \<approx> s''" by (rule eq_statesI[of "\<alpha>' \<circ> \<alpha>" "\<beta>' \<circ> \<beta>"]) (use s_s' s'_s'' in \<open>auto simp add: bij_comp\<close>)
qed

lemma \<alpha>\<beta>_sym: "s \<approx> s' \<Longrightarrow> s' \<approx> s"
proof -
  assume "s \<approx> s'"
  from this obtain \<alpha> \<beta> where s_s': "bij \<alpha>" "bij \<beta>" "\<R>\<^sub>G \<alpha> \<beta> s = s'" by blast
  show "s' \<approx> s" by (rule eq_statesI[of "inv \<alpha>" "inv \<beta>"]) (use s_s' in \<open>auto simp add: bij_imp_bij_inv\<close>)
qed

subsection \<open>Distributive laws\<close>

subsubsection Expression

lemma renaming_distr_completion [simp]:
  "\<R>\<^sub>E \<alpha> \<beta> (\<E>[e]) = ((\<R>\<^sub>C \<alpha> \<beta> \<E>)[\<R>\<^sub>E \<alpha> \<beta> e])"
  by (induct \<E>) simp+

subsubsection Store

lemma renaming_distr_combination [simp]: 
  "\<R>\<^sub>S \<alpha> \<beta> (\<sigma>;;\<tau>) = (\<R>\<^sub>S \<alpha> \<beta> \<sigma>;;\<R>\<^sub>S \<alpha> \<beta> \<tau>)"
  by (rule ext) auto

lemma renaming_distr_store [simp]:
  "bij \<beta> \<Longrightarrow> \<R>\<^sub>S \<alpha> \<beta> (\<sigma>(l \<mapsto> v)) = \<R>\<^sub>S \<alpha> \<beta> \<sigma>(\<beta> l \<mapsto> \<R>\<^sub>V \<alpha> \<beta> v)"
  by (auto simp add: bijection.intro bijection.inv_left_eq_iff)

(* distribution law for local follows from the definition *)

subsubsection Global 

lemma renaming_distr_global [simp]:
  "bij \<alpha> \<Longrightarrow> \<R>\<^sub>G \<alpha> \<beta> (s(r \<mapsto> ls)) = \<R>\<^sub>G \<alpha> \<beta> s(\<alpha> r \<mapsto> \<R>\<^sub>L \<alpha> \<beta> ls)"
  "bij \<alpha> \<Longrightarrow> \<R>\<^sub>G \<alpha> \<beta> (s(r := None)) = (\<R>\<^sub>G \<alpha> \<beta> s)(\<alpha> r := None)"
  by (auto simp add: bijection.intro bijection.inv_left_eq_iff)

subsection \<open>Miscellaneous laws\<close>

lemma rename_empty [simp]:
  "\<R>\<^sub>S \<alpha> \<beta> \<epsilon> = \<epsilon>"
  "\<R>\<^sub>G \<alpha> \<beta> \<epsilon> = \<epsilon>"
  by auto

subsection Swaps

lemma swap_bij: 
  "bij (id(x := x', x' := x))" (is "bij ?f")
proof (rule bijI)
  show "inj ?f" by (simp add: inj_on_def)
  show "surj ?f"
  proof
    show "UNIV \<subseteq> range (id(x := x', x' := x))"
    proof (rule subsetI)
      fix y
      assume "y \<in> (UNIV :: 'a set)"
      show "y \<in> range (id(x := x', x' := x))" by (cases "y = x"; cases "y = x'") auto
    qed
  qed simp
qed

lemma id_trivial_update [simp]: "id(x := x) = id" by auto (* for solving trivial peaks *)

lemma eliminate_renaming_val_expr [simp]:
  fixes
    v :: "('r,'l,'v) val" and
    e :: "('r,'l,'v) expr"
  shows
    "l \<notin> LID\<^sub>V v \<Longrightarrow> \<R>\<^sub>V \<alpha> (\<beta>(l := l')) v = \<R>\<^sub>V \<alpha> \<beta> v"
    "l \<notin> LID\<^sub>E e \<Longrightarrow> \<R>\<^sub>E \<alpha> (\<beta>(l := l')) e = \<R>\<^sub>E \<alpha> \<beta> e"
    "r \<notin> RID\<^sub>V v \<Longrightarrow> \<R>\<^sub>V (\<alpha>(r := r')) \<beta> v = \<R>\<^sub>V \<alpha> \<beta> v"
    "r \<notin> RID\<^sub>E e \<Longrightarrow> \<R>\<^sub>E (\<alpha>(r := r')) \<beta> e = \<R>\<^sub>E \<alpha> \<beta> e"
proof -
  have "(\<forall>\<alpha> \<beta> r r'. r \<notin> RID\<^sub>V v \<longrightarrow> \<R>\<^sub>V (\<alpha>(r := r')) \<beta> v = \<R>\<^sub>V \<alpha> \<beta> v) \<and>
    (\<forall>\<alpha> \<beta> r r'. r \<notin> RID\<^sub>E e \<longrightarrow> \<R>\<^sub>E (\<alpha>(r := r')) \<beta> e = \<R>\<^sub>E \<alpha> \<beta> e)"
    by (induct rule: val_expr.induct) simp+
  thus 
    "r \<notin> RID\<^sub>V v \<Longrightarrow> \<R>\<^sub>V (\<alpha>(r := r')) \<beta> v = \<R>\<^sub>V \<alpha> \<beta> v" 
    "r \<notin> RID\<^sub>E e \<Longrightarrow> \<R>\<^sub>E (\<alpha>(r := r')) \<beta> e = \<R>\<^sub>E \<alpha> \<beta> e"
    by simp+
  have "(\<forall>\<alpha> \<beta> l l'. l \<notin> LID\<^sub>V v \<longrightarrow> \<R>\<^sub>V \<alpha> (\<beta>(l := l')) v = \<R>\<^sub>V \<alpha> \<beta> v) \<and>
    (\<forall>\<alpha> \<beta> l l'. l \<notin> LID\<^sub>E e \<longrightarrow> \<R>\<^sub>E \<alpha> (\<beta>(l := l')) e = \<R>\<^sub>E \<alpha> \<beta> e)"
    by (induct rule: val_expr.induct) simp+
  thus 
    "l \<notin> LID\<^sub>V v \<Longrightarrow> \<R>\<^sub>V \<alpha> (\<beta>(l := l')) v = \<R>\<^sub>V \<alpha> \<beta> v" and
    "l \<notin> LID\<^sub>E e \<Longrightarrow> \<R>\<^sub>E \<alpha> (\<beta>(l := l')) e = \<R>\<^sub>E \<alpha> \<beta> e"
    by simp+
qed

lemma eliminate_renaming_cntxt [simp]:
  "r \<notin> RID\<^sub>C \<E> \<Longrightarrow> \<R>\<^sub>C (\<alpha>(r := r')) \<beta> \<E> = \<R>\<^sub>C \<alpha> \<beta> \<E>"
  "l \<notin> LID\<^sub>C \<E> \<Longrightarrow> \<R>\<^sub>C \<alpha> (\<beta>(l := l')) \<E> = \<R>\<^sub>C \<alpha> \<beta> \<E>"
  by (induct \<E> rule: cntxt.induct) auto

lemma eliminate_swap_val [simp, intro]:
  "r \<notin> RID\<^sub>V v \<Longrightarrow> r' \<notin> RID\<^sub>V v \<Longrightarrow> \<R>\<^sub>V (id(r := r', r' := r)) id v = v"
  "l \<notin> LID\<^sub>V v \<Longrightarrow> l' \<notin> LID\<^sub>V v \<Longrightarrow> \<R>\<^sub>V id (id(l := l', l' := l)) v = v"
  by simp+

lemma eliminate_swap_expr [simp, intro]:
  "r \<notin> RID\<^sub>E e \<Longrightarrow> r' \<notin> RID\<^sub>E e \<Longrightarrow> \<R>\<^sub>E (id(r := r', r' := r)) id e = e"
  "l \<notin> LID\<^sub>E e \<Longrightarrow> l' \<notin> LID\<^sub>E e \<Longrightarrow> \<R>\<^sub>E id (id(l := l', l' := l)) e = e"
  by simp+

lemma eliminate_swap_cntxt [simp, intro]:
  "r \<notin> RID\<^sub>C \<E> \<Longrightarrow> r' \<notin> RID\<^sub>C \<E> \<Longrightarrow> \<R>\<^sub>C (id(r := r', r' := r)) id \<E> = \<E>"
  "l \<notin> LID\<^sub>C \<E> \<Longrightarrow> l' \<notin> LID\<^sub>C \<E> \<Longrightarrow> \<R>\<^sub>C id (id(l := l', l' := l)) \<E> = \<E>"
  by simp+

lemma eliminate_swap_store_rid [simp, intro]:
  "r \<notin> RID\<^sub>S \<sigma> \<Longrightarrow> r' \<notin> RID\<^sub>S \<sigma> \<Longrightarrow> \<R>\<^sub>S (id(r := r', r' := r)) id \<sigma> = \<sigma>"
  by (rule \<R>\<^sub>SI) (auto simp add: swap_bij RID\<^sub>S_def domIff ranI)

lemma eliminate_swap_store_lid [simp, intro]:
  "l \<notin> LID\<^sub>S \<sigma> \<Longrightarrow> l' \<notin> LID\<^sub>S \<sigma> \<Longrightarrow> \<R>\<^sub>S id (id(l := l', l' := l)) \<sigma> = \<sigma>"
  by (rule \<R>\<^sub>SI) (auto simp add: swap_bij LID\<^sub>S_def domIff ranI)

lemma eliminate_swap_global_rid [simp, intro]:
  "r \<notin> RID\<^sub>G s \<Longrightarrow> r' \<notin> RID\<^sub>G s \<Longrightarrow> \<R>\<^sub>G (id(r := r', r' := r)) id s = s"
  by (rule \<R>\<^sub>GI[OF swap_bij], ((rule sym, auto)[1])+)

lemma eliminate_swap_global_lid [simp, intro]:
  "l \<notin> LID\<^sub>G s \<Longrightarrow> l' \<notin> LID\<^sub>G s \<Longrightarrow> \<R>\<^sub>G id (id(l := l', l' := l)) s = s"
  by (rule \<R>\<^sub>GI) (auto simp add: ID_distr_global_conditional)

end