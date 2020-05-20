(*  Title:       BDD
    Author:      Veronika Ortner and Norbert Schirmer, 2004
    Maintainer:  Norbert Schirmer,  norbert.schirmer at web de
    License:     LGPL
*)

(*  
BinDag.thy

Copyright (C) 2004-2008 Veronika Ortner and Norbert Schirmer 
Some rights reserved, TU Muenchen

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

section \<open>BDD Abstractions\<close>

theory BinDag
imports Simpl.Simpl_Heap
begin

datatype dag = Tip | Node dag ref dag

lemma [simp]: "Node lt a rt \<noteq> lt"
  by (induct lt) auto

lemma [simp]: "lt \<noteq> Node lt a rt"
  by (induct lt) auto

lemma [simp]: "Node lt a rt \<noteq> rt"
  by (induct rt) auto

lemma [simp]: "rt \<noteq> Node lt a rt"
  by (induct rt) auto


primrec set_of:: "dag \<Rightarrow> ref set" where
  set_of_Tip: "set_of Tip = {}"
  | set_of_Node: "set_of (Node lt a rt) = {a} \<union> set_of lt \<union> set_of rt"

primrec DAG:: "dag \<Rightarrow> bool" where
  "DAG Tip = True"
  | "DAG (Node l a r) = (a \<notin> set_of l \<and> a \<notin> set_of r \<and> DAG l \<and> DAG r)"

primrec subdag:: "dag \<Rightarrow> dag \<Rightarrow> bool" where
  "subdag Tip t = False"
  | "subdag (Node l a r) t = (t=l \<or> t=r \<or> subdag l t \<or> subdag r t)"

lemma subdag_size: "subdag t s \<Longrightarrow> size s < size t"
  by  (induct t) auto

lemma subdag_neq: "subdag t s \<Longrightarrow> t\<noteq>s"
by (induct t) (auto dest: subdag_size)

lemma subdag_trans [trans]: "subdag t s \<Longrightarrow> subdag s r \<Longrightarrow> subdag t r"
by (induct t) auto

lemma subdag_NodeD: 
  "subdag t (Node lt a rt) \<Longrightarrow> subdag t lt \<and> subdag t rt"  
  by (induct t) auto

lemma subdag_not_sym: "\<And>t. \<lbrakk>subdag s t; subdag t s\<rbrakk> \<Longrightarrow> P"
  by (induct s) (auto dest: subdag_NodeD)

instantiation dag :: order
begin

definition
  less_dag_def: "s < (t::dag) \<longleftrightarrow> subdag t s"

definition
  le_dag_def: "s \<le> (t::dag) \<longleftrightarrow> s=t \<or> s < t"

lemma le_dag_refl: "(x::dag) \<le> x"
  by (simp add: le_dag_def)

lemma le_dag_trans:
  fixes x::dag and  y and z 
  assumes x_y: "x \<le> y" and y_z: "y \<le> z" 
  shows "x \<le> z"
proof (cases "x=y")
  case True with y_z show ?thesis by simp
next
  case False
  note x_neq_y = this
  with x_y have x_less_y: "x < y" by (simp add: le_dag_def)
  show ?thesis
  proof (cases "y=z")
    case True
    with x_y show ?thesis by simp
  next
    case False
    with y_z have "y < z" by (simp add: le_dag_def)
    with x_less_y have "x < z" 
      by (auto simp add: less_dag_def intro: subdag_trans)
    thus ?thesis
      by (simp add: le_dag_def)
  qed
qed

lemma le_dag_antisym:
  fixes x::dag and  y   
  assumes x_y: "x \<le> y" and y_x: "y \<le> x" 
  shows "x = y"
proof (cases "x=y")
  case True thus ?thesis .
next
  case False
  with x_y y_x show ?thesis
    by (auto simp add: less_dag_def le_dag_def intro: subdag_not_sym)
qed

lemma dag_less_le: 
  fixes x::dag and y
  shows "(x < y) = (x \<le> y \<and> x \<noteq> y)"
  by (auto simp add: less_dag_def le_dag_def dest: subdag_neq)
 
instance
  by standard (auto simp add: dag_less_le le_dag_refl intro: le_dag_trans dest: le_dag_antisym)

end

lemma less_dag_Tip [simp]: "\<not> (x < Tip)"
  by (simp add: less_dag_def)

lemma less_dag_Node: "x < (Node l a r) = 
  (x \<le> l \<or> x \<le> r)"
  by (auto simp add: order_le_less less_dag_def)

lemma less_dag_Node': "x < (Node l a r) = 
  (x=l \<or> x=r \<or> x < l \<or> x < r)" 
  by (simp add: less_dag_def)

lemma less_Node_dag: "(Node l a r) < x \<Longrightarrow> l < x \<and> r < x"
  by (auto simp add: less_dag_def dest: subdag_NodeD)

lemma less_dag_set_of: "x < y \<Longrightarrow> set_of x \<subseteq> set_of y" 
  by (unfold less_dag_def, induct y, auto)

lemma le_dag_set_of: "x \<le> y \<Longrightarrow> set_of x \<subseteq> set_of y"
  apply (unfold le_dag_def)
  apply (erule disjE)
   apply simp
  apply (erule less_dag_set_of)
  done

lemma DAG_less: "DAG y \<Longrightarrow> x < y \<Longrightarrow> DAG x"
  by (induct y) (auto simp add: less_dag_Node')

lemma less_DAG_set_of: 
  assumes x_less_y: "x < y" 
  assumes DAG_y: "DAG y"
  shows "set_of x \<subset> set_of y" 
proof (cases y)
  case Tip with x_less_y show ?thesis by simp
next
  case (Node l a r)
  with DAG_y obtain a: "a \<notin> set_of l" "a \<notin> set_of r"
    by simp
  from Node obtain l_less_y: "l < y" and r_less_y: "r < y" 
    by (simp add: less_dag_Node)
  from Node a obtain 
    l_subset_y: "set_of l \<subset> set_of y" and
    r_subset_y: "set_of r \<subset> set_of y"
    by auto
  from Node x_less_y have "x=l \<or> x=r \<or> x < l \<or> x < r"
    by (simp add: less_dag_Node')
  thus ?thesis
  proof (elim disjE)
    assume "x=l"
    with l_subset_y show ?thesis by simp
  next
    assume "x=r"
    with r_subset_y show ?thesis by simp
  next
    assume "x < l"
    hence "set_of x \<subseteq> set_of l"
      by (rule less_dag_set_of)
    also note l_subset_y
    finally show ?thesis .
  next
    assume "x < r"
    hence "set_of x \<subseteq> set_of r"
      by (rule less_dag_set_of)
    also note r_subset_y
    finally show ?thesis .
  qed 
qed


lemma in_set_of_decomp: 
  "p \<in> set_of t = (\<exists>l r. t=(Node l p r) \<or> subdag t (Node l p r))"
  (is "?A = ?B")
proof
  assume "?A" thus "?B"
    by (induct t) auto
next
  assume "?B" thus "?A"  
    by (induct t) auto
qed

primrec Dag:: "ref \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> dag \<Rightarrow> bool"
where
"Dag p l r Tip = (p = Null)" |
"Dag p l r (Node lt a rt) = (p = a \<and> p \<noteq> Null \<and> 
                              Dag (l p) l r lt \<and> Dag (r p) l r  rt)"

lemma Dag_Null [simp]: "Dag Null l r  t = (t = Tip)"
  by (cases t) simp_all

lemma Dag_Ref [simp]: 
  "p\<noteq>Null \<Longrightarrow> Dag p l r  t = (\<exists>lt rt. t=Node lt p rt \<and> 
                                Dag (l p) l r lt \<and> Dag (r p) l r rt)"
  by (cases t) auto

lemma Null_notin_Dag [simp, intro]: "\<And>p l r. Dag p l r t \<Longrightarrow> Null \<notin> set_of t"
  by (induct t) auto

theorem notin_Dag_update_l [simp]:
    "\<And> p. q \<notin> set_of t \<Longrightarrow> Dag p (l(q := y)) r  t = Dag p l r t"  
  by (induct t) auto

theorem notin_Dag_update_r [simp]:
    "\<And> p. q \<notin> set_of t \<Longrightarrow> Dag p l (r(q := y)) t = Dag p l r t"  
  by (induct t) auto


lemma Dag_upd_same_l_lemma: "\<And>p. p\<noteq>Null \<Longrightarrow> \<not> Dag p (l(p:=p)) r t"
  apply (induct t)
   apply simp
  apply (simp (no_asm_simp) del: fun_upd_apply)
  apply (simp (no_asm_simp) only: fun_upd_apply refl if_True)
  apply blast
  done

lemma Dag_upd_same_l [simp]: "Dag p (l(p:=p)) r t = (p=Null \<and> t=Tip)"
  apply (cases "p=Null")
   apply simp
  apply (fast dest: Dag_upd_same_l_lemma)
  done

text \<open>@{thm[source] Dag_upd_same_l} prevents 
@{term "p\<noteq>Null \<Longrightarrow> Dag p (l(p:=p)) r t = X"} from looping, because of 
@{thm[source] Dag_Ref} and @{thm[source] fun_upd_apply}.
\<close>

lemma Dag_upd_same_r_lemma: "\<And>p. p\<noteq>Null \<Longrightarrow> \<not> Dag p l (r(p:=p)) t"
  apply (induct t)
   apply simp
  apply (simp (no_asm_simp) del: fun_upd_apply)
  apply (simp (no_asm_simp) only: fun_upd_apply refl if_True)
  apply blast
  done

lemma Dag_upd_same_r [simp]: "Dag p l (r(p:=p)) t = (p=Null \<and> t=Tip)"
  apply (cases "p=Null")
   apply simp
  apply (fast dest: Dag_upd_same_r_lemma)
  done

lemma  Dag_update_l_new [simp]: "\<lbrakk>set_of t \<subseteq> set alloc\<rbrakk>
     \<Longrightarrow> Dag p (l(new (set alloc) := x)) r t = Dag p l r t"
  by (rule notin_Dag_update_l) fastforce

lemma  Dag_update_r_new [simp]: "\<lbrakk>set_of t \<subseteq> set alloc\<rbrakk>
     \<Longrightarrow> Dag p l (r(new (set alloc) := x)) t = Dag p l r t"
  by (rule notin_Dag_update_r) fastforce

lemma Dag_update_lI [intro]:
    "\<lbrakk>Dag p l r t; q \<notin> set_of t\<rbrakk> \<Longrightarrow> Dag p (l(q := y)) r t"
  by simp

lemma Dag_update_rI [intro]:
    "\<lbrakk>Dag p l r t; q \<notin> set_of t\<rbrakk> \<Longrightarrow> Dag p l (r(q := y)) t"
  by simp

lemma Dag_unique: "\<And> p t2. Dag p l r t1 \<Longrightarrow> Dag p l r t2 \<Longrightarrow> t1=t2"
  by (induct t1) auto

lemma Dag_unique1: "Dag p l r t \<Longrightarrow> \<exists>!t. Dag p l r t"
  by (blast intro: Dag_unique)

lemma Dag_subdag: "\<And> p. Dag p l r t \<Longrightarrow> subdag t s \<Longrightarrow> \<exists> q. Dag q l r s"
  by (induct t) auto

lemma Dag_root_not_in_subdag_l [simp,intro]: 
  assumes "Dag (l p) l r t"
  shows "p \<notin> set_of t"
proof - 
  {
    fix lt rt
    assume t: "t = Node lt p rt"
    from assms have "Dag (l p) l r lt" 
      by (clarsimp simp only: t Dag.simps)
    with assms have "t=lt"
      by (rule Dag_unique)
    with t have False
      by simp
  }
  moreover
  {
    fix lt rt
    assume subdag: "subdag t (Node lt p rt)"
    with assms obtain q where "Dag q l r (Node lt p rt)"
      by (rule Dag_subdag [elim_format]) iprover
    hence "Dag (l p) l r lt"
      by auto
    with assms have "t=lt"
      by (rule Dag_unique)
    moreover 
    have "subdag t lt" 
    proof -
      note subdag
      also have "subdag (Node lt p rt) lt" by simp
      finally show ?thesis .
    qed
    ultimately have False
      by (simp add: subdag_neq)
  }
  ultimately show ?thesis
    by (auto simp add: in_set_of_decomp)
qed

lemma Dag_root_not_in_subdag_r [simp, intro]:
  assumes "Dag (r p) l r t"
  shows "p \<notin> set_of t"
proof - 
  {
    fix lt rt
    assume t: "t = Node lt p rt"
    from assms have "Dag (r p) l r rt" 
      by (clarsimp simp only: t Dag.simps)
    with assms have "t=rt"
      by (rule Dag_unique)
    with t have False
      by simp
  }
  moreover
  {
    fix lt rt
    assume subdag: "subdag t (Node lt p rt)"
    with assms obtain q where "Dag q l r (Node lt p rt)"
      by (rule Dag_subdag [elim_format]) iprover
    hence "Dag (r p) l r rt"
      by auto
    with assms have "t=rt"
      by (rule Dag_unique)
    moreover 
    have "subdag t rt" 
    proof -
      note subdag
      also have "subdag (Node lt p rt) rt" by simp
      finally show ?thesis .
    qed
    ultimately have False
      by (simp add: subdag_neq)
  }
  ultimately show ?thesis
    by (auto simp add: in_set_of_decomp)
qed


lemma Dag_is_DAG: "\<And>p l r. Dag p l r t \<Longrightarrow> DAG t"
  by (induct t) auto
 
lemma heaps_eq_Dag_eq:
  "\<And>p. \<forall>x \<in> set_of t. l x = l' x \<and> r x = r' x 
    \<Longrightarrow> Dag p l r t = Dag p l' r' t"
  by (induct t) auto

lemma heaps_eq_DagI1: 
  "\<lbrakk>Dag p l r t; \<forall>x\<in>set_of t. l x = l' x \<and> r x = r' x\<rbrakk>
    \<Longrightarrow> Dag p l' r' t"
  by (rule heaps_eq_Dag_eq [THEN iffD1])

lemma heaps_eq_DagI2: 
  "\<lbrakk>Dag p l' r' t; \<forall>x\<in>set_of t. l x = l' x \<and> r x = r' x\<rbrakk>
    \<Longrightarrow> Dag p l r t"
  by (rule heaps_eq_Dag_eq [THEN iffD2]) auto
 
lemma  Dag_unique_all_impl_simp [simp]: 
  "Dag p l r t \<Longrightarrow> (\<forall>t. Dag p l r t \<longrightarrow> P t) = P t"
  by (auto dest: Dag_unique)

lemma Dag_unique_ex_conj_simp [simp]: 
  "Dag p l r t \<Longrightarrow> (\<exists>t. Dag p l r t \<and> P t) = P t"
  by (auto dest: Dag_unique)

lemma Dags_eq_hp_eq: 
  "\<And>p p'. \<lbrakk>Dag p l r t; Dag p' l' r' t\<rbrakk> \<Longrightarrow>
    p'=p \<and> (\<forall>no \<in> set_of t. l' no = l no \<and> r' no = r no)"
  by (induct t) auto

definition isDag :: "ref \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> bool"
  where "isDag p l r = (\<exists>t. Dag p l r t)"

definition dag :: "ref \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> dag"
  where "dag p l r = (THE t. Dag p l r t)"

lemma Dag_conv_isDag_dag: "Dag p l r t = (isDag p l r \<and> t=dag p l r)"
  apply (simp add: isDag_def dag_def)
  apply (rule iffI)
   apply (rule conjI)
    apply blast
   apply (subst the1_equality)
     apply (erule Dag_unique1)
    apply assumption
   apply (rule refl)
  apply clarify
  apply (rule theI)
   apply assumption
  apply (erule (1) Dag_unique)
  done

lemma Dag_dag: "Dag p l r t \<Longrightarrow> dag p l r = t"
  by (simp add: Dag_conv_isDag_dag)

end
