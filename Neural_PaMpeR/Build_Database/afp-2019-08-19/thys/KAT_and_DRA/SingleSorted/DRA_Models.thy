(* Title:      Demonic refinement algebra
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Models for Demonic Refinement Algebra with Tests\<close>

theory DRA_Models
  imports DRAT
begin

text \<open>
  We formalise the predicate transformer model of demonic refinement algebra.
  Predicate transformers are formalised as strict and additive functions over a field of sets,
  or alternatively as costrict and multiplicative functions. 
  In the future, this should be merged with Preoteasa's more abstract formalisation~\cite{Preoteasa11}.
\<close>

no_notation 
  plus (infixl "+" 65) and 
  less_eq  ("'(\<le>')") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

notation comp (infixl "\<cdot>" 55)

type_synonym 'a bfun = "'a set \<Rightarrow> 'a set"

text \<open>
  Definitions of signature:
\<close>

definition top :: "'a bfun" where "top \<equiv> \<lambda>x. UNIV"
definition bot :: "'a bfun" where "bot \<equiv> \<lambda>x. {}"
definition adjoint :: "'a bfun \<Rightarrow> 'a bfun" where "adjoint f \<equiv> (\<lambda>p. - f (-p))"

definition fun_inter :: "'a bfun \<Rightarrow> 'a bfun \<Rightarrow> 'a bfun" (infix "\<sqinter>" 51) where
  "f \<sqinter> g \<equiv> \<lambda>p. f p \<inter> g p"

definition fun_union :: "'a bfun \<Rightarrow> 'a bfun \<Rightarrow> 'a bfun" (infix "+" 52) where
  "f + g \<equiv> \<lambda>p. f p \<union> g p"

definition fun_order :: "'a bfun \<Rightarrow> 'a bfun \<Rightarrow> bool" (infix "\<le>" 50) where
  "f \<le> g \<equiv> \<forall>p. f p \<subseteq> g p"

definition fun_strict_order :: "'a bfun \<Rightarrow> 'a bfun \<Rightarrow> bool" (infix "<." 50) where
  "f <. g \<equiv> f \<le> g \<and> f \<noteq> g"

definition N :: "'a bfun \<Rightarrow> 'a bfun" where
  "N f \<equiv> ((adjoint f o bot) \<sqinter> id)"

lemma top_max: "f \<le> top"
  by (auto simp: top_def fun_order_def)

lemma bot_min: "bot \<le> f"
  by (auto simp: bot_def fun_order_def)

lemma oder_def: "f \<sqinter> g = f \<Longrightarrow> f \<le> g"
  by (metis fun_inter_def fun_order_def le_iff_inf)

lemma order_def_var: "f \<le> g \<Longrightarrow> f \<sqinter> g = f"
  by (auto simp: fun_inter_def fun_order_def)

lemma adjoint_idem [simp]: "adjoint (adjoint f) = f"
  by (auto simp: adjoint_def)

lemma adjoint_prop1[simp]: "(f o top) \<sqinter> (adjoint f o bot) = bot"
  by (auto simp: fun_inter_def adjoint_def bot_def top_def)

lemma adjoint_prop2[simp]: "(f o top) + (adjoint f o bot) = top"
  by (auto simp: fun_union_def adjoint_def bot_def top_def)

lemma adjoint_mult: "adjoint (f o g) = adjoint f o adjoint g"
  by (auto simp: adjoint_def)

lemma adjoint_top[simp]: "adjoint top = bot"
  by (auto simp: adjoint_def bot_def top_def)

lemma N_comp1: "(N (N f)) + N f = id"
  by (auto simp: fun_union_def N_def fun_inter_def adjoint_def bot_def)

lemma N_comp2: "(N (N f)) o N f = bot"
  by (auto simp: N_def fun_inter_def adjoint_def bot_def)

lemma N_comp3: "N f o (N (N f)) = bot"
  by (auto simp: N_def fun_inter_def adjoint_def bot_def)

lemma N_de_morgan: "N (N f) o N (N g) = N (N f) \<sqinter> N (N g)"
  by (auto simp: fun_union_def N_def fun_inter_def adjoint_def bot_def)

lemma conj_pred_aux [simp]: "(\<lambda>p. x p \<union> y p) = y \<Longrightarrow> \<forall>p. x p \<subseteq> y p"
  by (metis Un_upper1)

text \<open>
  Next, we define a type for conjuctive or multiplicative predicate transformers.
\<close>

typedef 'a bool_op = "{f::'a bfun. (\<forall>g h. mono f \<and> f \<circ> g + f \<circ> h = f \<circ> (g + h) \<and> bot o f = bot)}"
  apply (rule_tac x="\<lambda>x. x" in exI)
  apply auto
  apply (metis monoI)
  by (auto simp: fun_order_def fun_union_def)

setup_lifting type_definition_bool_op

text \<open>
  Conjuctive predicate transformers form a dioid with tests without right annihilator.
\<close>

instantiation bool_op :: (type) dioid_one_zerol 
begin
  lift_definition less_eq_bool_op :: "'a bool_op \<Rightarrow> 'a bool_op \<Rightarrow> bool" is fun_order .

  lift_definition less_bool_op :: "'a bool_op \<Rightarrow> 'a bool_op \<Rightarrow> bool" is "(<.)" .

  lift_definition zero_bool_op :: "'a bool_op" is "bot"
    by (auto simp: bot_def fun_union_def fun_order_def mono_def)

  lift_definition one_bool_op :: "'a bool_op" is "id"
    by (auto simp: fun_union_def fun_order_def mono_def)

  lift_definition times_bool_op :: "'a bool_op \<Rightarrow> 'a bool_op \<Rightarrow> 'a bool_op" is "(o)" 
    by (auto simp: o_def fun_union_def fun_order_def bot_def mono_def) metis

  lift_definition plus_bool_op :: "'a bool_op \<Rightarrow> 'a bool_op \<Rightarrow> 'a bool_op" is "(+)"
    apply (auto simp: o_def fun_union_def fun_order_def bot_def mono_def)
    apply (metis subsetD)
    apply (metis subsetD)
    apply (rule ext)
    by (metis (no_types, lifting) semilattice_sup_class.sup.assoc semilattice_sup_class.sup.left_commute)

  instance
    by standard (transfer, auto simp: fun_order_def fun_strict_order_def fun_union_def bot_def)+

end

instantiation bool_op :: (type) test_semiring_zerol 
begin
  lift_definition n_op_bool_op :: "'a bool_op \<Rightarrow> 'a bool_op" is "N"
    by (auto simp: N_def fun_inter_def adjoint_def bot_def fun_union_def mono_def)

  instance
  apply standard
  apply (transfer, clarsimp simp add: N_def adjoint_def bot_def id_def comp_def fun_inter_def)
  apply (transfer, clarsimp simp add: N_def adjoint_def bot_def id_def comp_def fun_inter_def fun_union_def mono_def, blast)
  apply (transfer, clarsimp simp add: N_def adjoint_def bot_def comp_def mono_def fun_union_def fun_inter_def)
  by (transfer, clarsimp simp add: N_def adjoint_def bot_def comp_def mono_def fun_union_def fun_inter_def, blast)

end

definition fun_star :: "'a bfun \<Rightarrow> 'a bfun" where
  "fun_star f = lfp (\<lambda>r. f o r + id)"

definition fun_iteration :: "'a bfun \<Rightarrow> 'a bfun" where
  "fun_iteration f = gfp (\<lambda>g. f o g + id)"
  
text \<open>
  Verifying the iteration laws is left for future work. This could be obtained by integrating
  Preoteasa's approach~\cite{Preoteasa11}.
\<close>

end
