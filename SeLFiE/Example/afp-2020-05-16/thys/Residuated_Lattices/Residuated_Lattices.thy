(* Title:      Residuated Lattices
   Author:     Victor Gomes <vborgesferreiragomes1 at sheffield.ac.uk>
   Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

theory Residuated_Lattices
  imports Kleene_Algebra.Signatures
begin

notation
  times (infixl "\<cdot>" 70)
  
notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 65) and
  sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900)

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)
  
section \<open>Residuated Lattices\<close>

subsection \<open>Residuated Functions on a Partial Order\<close>

text \<open>
  We follow Galatos and \emph{al.} to define residuated funtions on
  partial orders. Material from articles by Maddux, and J{\'o}sson and Tsinakis are also considered.
  
  This development should in the future be expanded to functions or categories where the sources and targets have
  different type.

  Let $P$ be a partial order, or a poset.
  A map $f : P \to P$ is residuated if there exists a map
  $g: P \to P$ such that $f(x) \le y \Leftrightarrow x \le g(y)$
  for all $x, y \in P$.
  That is, they are adjoints of a Galois connection.
\<close>

context order begin

definition residuated_pair :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "residuated_pair f g \<equiv> \<forall>x y. f(x) \<le> y \<longleftrightarrow> x \<le> g(y)"

theorem residuated_pairI [intro]: 
  assumes "\<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y"
  and "\<forall>x y. x \<le> y \<longrightarrow> g x \<le> g y"
  and "\<forall>x. x \<le> (g o f) x"
  and "\<forall>x. (f o g) x \<le> x"
  shows "residuated_pair f g"
  by (metis assms comp_apply local.order_trans residuated_pair_def antisym)
  
definition residuated :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "residuated f \<equiv> \<exists>g. residuated_pair f g"
  
text \<open>
  If a map $f$ is residuated, then its residual $g$ is unique. 
\<close>

lemma residual_unique: "residuated f \<Longrightarrow> \<exists>!g. residuated_pair f g"
  unfolding residuated_def residuated_pair_def
  by (metis ext eq_refl order.antisym)
  
text \<open>
  Since the residual of a map $f$ is unique, it makes sense to 
  define a residual operator. 
\<close>
  
definition residual :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "residual f \<equiv> THE g. residuated_pair f g"

lemma residual_galois: "residuated f \<Longrightarrow> f(x) \<le> y \<longleftrightarrow> x \<le> residual f y"
  apply (clarsimp simp: residuated_def residuated_pair_def)
  apply (subgoal_tac "residual f = g")
  apply (simp_all add: residual_def)
  apply (rule the1_equality)
  apply (metis residuated_def residuated_pair_def residual_unique) 
  by (simp add: residuated_pair_def)

lemma residual_galoisI1: "residuated f \<Longrightarrow> f(x) \<le> y \<Longrightarrow> x \<le> residual f y"
  by (metis residual_galois)

lemma residual_galoisI2: "residuated f \<Longrightarrow> x \<le> residual f y \<Longrightarrow> f(x) \<le> y"
  by (metis residual_galois)
  
text \<open>
  A closure operator on a poset is a map that is expansive, isotone and
  idempotent.
  The composition of the residual of a function $f$ with $f$ is a closure operator.
\<close>

definition closure :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "closure f \<equiv> (\<forall>x. x \<le> f x) \<and> (\<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y) \<and> (\<forall>x. f(f x) = f x)"
  
lemma res_c1: "residuated f \<Longrightarrow> x \<le> residual f (f x)"
  by (metis local.order.refl residual_galois)

lemma res_c2: "residuated f \<Longrightarrow> x \<le> y \<Longrightarrow> residual f (f x) \<le> residual f (f y)"
  by (metis local.order.refl local.order_trans residual_galois)
  
lemma res_c3: "residuated f \<Longrightarrow> residual f (f (residual f (f x))) = residual f (f x)"
  by (metis local.eq_iff local.order_trans res_c1 residual_galois)

lemma res_closure: "residuated f \<Longrightarrow> closure (residual f o f)"
  by (auto simp: closure_def intro: res_c1 res_c2 res_c3)

text \<open>
  Dually, an interior operator on a poset is a map that is contractive, isotone and
  idempotent.
  The composition of $f$ with its residual is an interior operator.
\<close>

definition interior :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "interior f \<equiv> (\<forall>x. f x \<le> x) \<and> (\<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y) \<and> (\<forall>x. f(f x) = f x)"

lemma res_i1: "residuated f \<Longrightarrow> f (residual f x) \<le> x"
  by (metis local.order.refl residual_galois)
  
lemma res_i2: "residuated f \<Longrightarrow> x \<le> y \<Longrightarrow> f (residual f x) \<le> f (residual f y)"
  by (metis local.order.refl local.order_trans residual_galois)
  
lemma res_i3: "residuated f \<Longrightarrow> f (residual f (f (residual f x))) = f (residual f x)"
  by (metis local.antisym_conv res_c1 res_c3 res_i1 residual_galois)
  
lemma res_interior: "residuated f \<Longrightarrow> interior (f o residual f)"
  by (auto simp: interior_def intro: res_i1 res_i2 res_i3)

text \<open>Next we show a few basic lemmas about residuated maps.\<close>

lemma res_iso: "residuated f \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  by (metis local.order.trans res_c1 residual_galois)
  
lemma res_residual_iso: "residuated f \<Longrightarrow> x \<le> y \<Longrightarrow> residual f x \<le> residual f y"
  by (metis local.order.trans res_i1 residual_galois)

lemma res_comp1 [simp]: "residuated f \<Longrightarrow> f o residual f o f = f"
proof -
  assume resf: "residuated f"
  { 
    fix x
    have "(f o residual f o f) x = f x"
      by (metis resf comp_apply local.eq_iff res_c1 res_i1 res_iso)
  }
  thus ?thesis
    by (metis ext)
qed

lemma res_comp2 [simp]: "residuated f \<Longrightarrow> residual f o f o residual f = residual f"
proof -
  assume resf: "residuated f"
  { 
    fix x
    have "(residual f o f o residual f) x = residual f x"
      by (metis resf comp_apply local.eq_iff res_c1 res_i1 res_residual_iso)
  }
  thus ?thesis
    by (metis ext)
qed

end (* order *)

text \<open>
  A residuated function $f$ preserves all existing joins.
  Dually, its residual preserves all existing meets.
  We restrict our attention to semilattices, where binary joins or meets exist, and to
  complete lattices, where arbitrary joins and meets exist.
\<close>

lemma (in semilattice_sup) residuated_sup: "residuated f \<Longrightarrow> f (x \<squnion> y) = f x \<squnion> f y"
proof (rule antisym)
  assume assm: "residuated f"
  thus "f (x \<squnion> y) \<le> f x \<squnion> f y"
    by (metis local.residual_galoisI1 local.residual_galoisI2 local.sup.bounded_iff local.sup_ge1 local.sup_ge2)
  show "f x \<squnion> f y \<le> f (x \<squnion> y)"
    by (metis assm local.res_iso local.sup.bounded_iff local.sup_ge1 local.sup_ge2)
qed

lemma (in semilattice_inf) residuated_inf: "residuated f \<Longrightarrow> residual f (x \<sqinter> y) = residual f x \<sqinter> residual f y"
proof (rule antisym)
  assume assm: "residuated f"
  thus "residual f (x \<sqinter> y) \<le> residual f x \<sqinter> residual f y"
    by (metis local.inf.boundedI local.inf.cobounded1 local.inf.cobounded2 local.res_residual_iso)
  show "residual f x \<sqinter> residual f y \<le> residual f (x \<sqinter> y)"
    by (metis assm local.inf.bounded_iff local.inf.cobounded1 local.inf.cobounded2 local.residual_galoisI1 local.residual_galoisI2)
qed

context bounded_lattice begin

lemma residuated_strict: "residuated f \<Longrightarrow> f \<bottom> = \<bottom>"
  by (metis local.bot_least local.bot_unique local.res_i1 local.res_iso)
  
lemma res_top: "residuated f \<Longrightarrow> residual f \<top> = \<top>"
  by (metis local.residual_galoisI1 local.top_greatest local.top_unique)

end

context complete_lattice begin

text \<open>
  On a complete lattice, a function $f$ is residuated if and only if
  it preserves arbitrary (possibly infinite) joins.
  Dually, a function $g$ is a residual of a residuated funtion $f$
  if and only if $g$ preserver arbitrary meets. 
\<close>

lemma residual_eq1: "residuated f \<Longrightarrow> residual f y = \<Squnion> {x. f x \<le> y}"
proof (rule antisym)
  assume assm: "residuated f"
  thus "residual f y \<le> \<Squnion>{x. f x \<le> y}"
    by (auto simp: res_i1 intro!: Sup_upper)
  show "\<Squnion>{x. f x \<le> y} \<le> residual f y"
    by (auto simp: assm intro!: Sup_least residual_galoisI1)
qed

lemma residual_eq2: "residuated f \<Longrightarrow> f x = \<Sqinter> {y. x \<le> residual f y}"
proof (rule antisym)
  assume assm: "residuated f"
  thus "f x \<le> \<Sqinter>{y. x \<le> residual f y}"
    by (auto intro: Inf_greatest residual_galoisI2)
  show "\<Sqinter>{y. x \<le> residual f y} \<le> f x"
    using assm by (auto simp: res_c1 intro!: Inf_lower)
qed

lemma residuated_Sup: "residuated f \<Longrightarrow> f(\<Squnion> X) = \<Squnion>{f x | x. x \<in> X}"
proof (rule antisym)
  assume assm: "residuated f"
  obtain y where y_def: "y = \<Squnion>{f x |x. x \<in> X}" 
    by auto
  hence "\<forall>x \<in> X. f x \<le> y"
    by (auto simp: y_def intro: Sup_upper)
  hence "\<forall>x \<in> X. x \<le> residual f y"
    by (auto simp: assm intro!: residual_galoisI1)
  hence "\<Squnion>X \<le> residual f y"
    by (auto intro: Sup_least)
  thus "f(\<Squnion> X) \<le> \<Squnion>{f x |x. x \<in> X}"
    by (metis y_def assm residual_galoisI2)
qed (clarsimp intro!: Sup_least res_iso Sup_upper)

lemma residuated_Inf: "residuated f \<Longrightarrow> residual f(\<Sqinter> X) = \<Sqinter>{residual f x | x. x \<in> X}"
proof (rule antisym, clarsimp intro!: Inf_greatest res_residual_iso Inf_lower)
  assume assm: "residuated f"
  obtain y where y_def: "y = \<Sqinter>{residual f x |x. x \<in> X}" 
    by auto
  hence "\<forall>x \<in> X. y \<le> residual f x"
    by (auto simp: y_def intro: Inf_lower)
  hence "\<forall>x \<in> X. f y \<le> x"
    by (metis assm residual_galoisI2)
  hence "f y \<le> \<Sqinter> X"
    by (auto intro: Inf_greatest)
  thus "\<Sqinter>{residual f x |x. x \<in> X} \<le> residual f (\<Sqinter>X)"
    by (auto simp: assm y_def intro!: residual_galoisI1)
qed

lemma Sup_sup: "\<forall>X. f(\<Squnion> X) = \<Squnion>{f x | x. x \<in> X} \<Longrightarrow> f (x \<squnion> y) = f x \<squnion> f y"
  apply (erule_tac x="{x, y}" in allE)
  by (force intro: Sup_eqI)

lemma Sup_residuatedI: "\<forall>X. f(\<Squnion> X) = \<Squnion>{f x | x. x \<in> X} \<Longrightarrow> residuated f"
proof (unfold residuated_def residuated_pair_def, standard+)
  fix x y
  assume "f x \<le> y"
  thus "x \<le> \<Squnion>{x. f x \<le> y}"
    by (clarsimp intro!: Sup_upper)
next
  fix x y
  assume assm: "\<forall>X. f (\<Squnion>X) = \<Squnion>{f x |x. x \<in> X}"
  hence f_iso: "\<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y"
    using Sup_sup by (auto simp: le_iff_sup)
  assume "x \<le> \<Squnion>{x. f x \<le> y}"
  hence "f x \<le> f(\<Squnion>{x. f x \<le> y})"
    by (metis f_iso)
  also have "... = \<Squnion>{f x | x . f x \<le> y}"
    using assm by auto
  finally show "f x \<le> y"
    apply (rule order_trans)
    by (auto intro!: Sup_least)
qed

lemma Inf_inf: "\<forall>X. f(\<Sqinter> X) = \<Sqinter>{f x | x. x \<in> X} \<Longrightarrow> f (x \<sqinter> y) = f x \<sqinter> f y"
  apply (erule_tac x="{x, y}" in allE)
  by (force intro: Inf_eqI)

lemma Inf_residuatedI: "\<forall>X. \<Sqinter>{g x | x. x \<in> X} = g (\<Sqinter> X) \<Longrightarrow> \<exists>f. residuated_pair f g"
proof (unfold residuated_pair_def, standard+)
  fix x y
  assume "x \<le> g y"
  thus "\<Sqinter>{y. x \<le> g y} \<le> y"
    by (clarsimp intro!: Inf_lower)
next
  fix x y
  assume assm: "\<forall>X. \<Sqinter>{g x | x. x \<in> X} = g (\<Sqinter> X)"
  hence g_iso: "\<forall>x y. x \<le> y \<longrightarrow> g x \<le> g y"
    using Inf_inf by (auto simp: le_iff_inf)
  assume "\<Sqinter>{y. x \<le> g y} \<le> y"
  hence "g (\<Sqinter>{y. x \<le> g y}) \<le> g y"
    by (metis g_iso)
  hence "(\<Sqinter>{g y | y. x \<le> g y}) \<le> g y"
    using assm apply (erule_tac x="{y. x \<le> g y}" in allE)
    by (auto intro!: Inf_lower)
  thus "x \<le> g y"
    apply (rule local.dual_order.trans)
    by (auto intro: Inf_greatest)
qed

end (* complete lattices *)

subsection \<open>Residuated Structures\<close>

text \<open>
  In this section, we define residuated algebraic structures, starting from the simplest of all,
  a \emph{residuated partial ordered groupoid}, to 
  \emph{residuated l-monoids}, which are residuated 
  lattices where the multiplicative operator forms a monoid.
\<close>

class pogroupoid = order + times +
  assumes mult_isor: "x \<le> y \<Longrightarrow> x \<cdot> z \<le> y \<cdot> z"
  and mult_isol: "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"

text \<open>
  A residuated partial ordered groupoid is simply a partial order and a multiplicative groupoid with 
  two extra operators satisfying the residuation laws.
  It is straighforward to prove that multiplication is compatible with the order,
  that is, multiplication is isotone.
  
  Most of the lemmas below come in pairs; they are related by opposition duality.
  Formalising this duality is left for future work.
\<close>

class residual_r_op =
  fixes residual_r :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<rightarrow>" 60)

class residual_l_op =
  fixes residual_l :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<leftarrow>" 60)
  
class residuated_pogroupoid = order + times + residual_l_op + residual_r_op +
  assumes resl_galois: "x \<le> z \<leftarrow> y \<longleftrightarrow> x \<cdot> y \<le> z"
  and resr_galois: "x \<cdot> y \<le> z \<longleftrightarrow> y \<le> x \<rightarrow> z"
begin

lemma reslI [intro]: "x \<cdot> y \<le> z \<Longrightarrow> x \<le> z \<leftarrow> y"
  by (metis resl_galois)

lemma resrI [intro]: "x \<cdot> y \<le> z \<Longrightarrow> y \<le> x \<rightarrow> z"
  by (metis resr_galois)

lemma residuated_pair_multl [simp]: "residuated_pair (\<lambda>x. x \<cdot> y) (\<lambda>x. x \<leftarrow> y)"
  by (auto simp: residuated_pair_def resl_galois)
  
lemma residuated_pair_multr [simp]: "residuated_pair (\<lambda>y. x \<cdot> y) (\<lambda>y. x \<rightarrow> y)"
  by (auto simp: residuated_pair_def resr_galois)

text \<open>
  Multiplication is then obviously residuated.
\<close>
  
lemma residuated_multl [simp]: "residuated (\<lambda>x. x \<cdot> y)"
  by (metis residuated_def residuated_pair_multl)

lemma residuated_multr [simp]: "residuated (\<lambda>y. x \<cdot> y)"
  by (metis residuated_def residuated_pair_multr)
  
lemma resl_eq [simp]: "residual (\<lambda>x. x \<cdot> y) = (\<lambda>x. x \<leftarrow> y)"
  unfolding residual_def apply (rule the1_equality)
  by (auto simp: intro!: residual_unique)
  
lemma resr_eq [simp]: "residual (\<lambda>y. x \<cdot> y) = (\<lambda>y. x \<rightarrow> y)"
  unfolding residual_def apply (rule the1_equality)
  by (auto simp: intro!: residual_unique)
  
text \<open>
  Next we prove a few lemmas, all of which are instantiation of more general facts about residuated functions.
\<close>
  
lemma res_lc1: "x \<le> x \<cdot> y \<leftarrow> y"
  by auto
  
lemma res_lc2: "x \<le> y \<Longrightarrow> x \<cdot> z \<leftarrow> z \<le> y \<cdot> z \<leftarrow> z"
  by (metis local.res_c2 resl_eq residuated_multl)

lemma res_lc3 [simp]: "(x \<cdot> y \<leftarrow> y) \<cdot> y \<leftarrow> y = x \<cdot> y \<leftarrow> y"
  by (metis local.res_c3 resl_eq residuated_multl)
  
lemma res_rc1: "x \<le> y \<rightarrow> y \<cdot> x"
  by auto

lemma res_rc2: "x \<le> y \<Longrightarrow> z \<rightarrow> z \<cdot> x \<le> z \<rightarrow> z \<cdot> y"
  by (metis local.res_c2 resr_eq residuated_multr)

lemma res_rc3 [simp]: "y \<rightarrow> y \<cdot> (y \<rightarrow> y \<cdot> x) = y \<rightarrow> y \<cdot> x"
  by (metis local.res_c3 resr_eq residuated_multr)
  
lemma res_li1: "(x \<leftarrow> y) \<cdot> y \<le> x"
  by (metis local.res_i1 resl_eq residuated_multl)
  
lemma res_li2: "x \<le> y \<Longrightarrow> (x \<leftarrow> z) \<cdot> z \<le> (y \<leftarrow> z) \<cdot> z"
  by (metis local.res_i2 resl_eq residuated_multl)
  
lemma res_li3 [simp]: "((x \<leftarrow> y) \<cdot> y \<leftarrow> y) \<cdot> y = (x \<leftarrow> y) \<cdot> y"
  by (metis local.res_i3 resl_eq residuated_multl)
  
lemma res_ri1: "y \<cdot> (y \<rightarrow> x) \<le> x"
  by (metis local.res_i1 resr_eq residuated_multr)
  
lemma res_ri2: "x \<le> y \<Longrightarrow> z \<cdot> (z \<rightarrow> x) \<le> z \<cdot> (z \<rightarrow> y)"
  by (metis local.res_i2 resr_eq residuated_multr)
  
lemma res_ri3 [simp]: "y \<cdot> (y \<rightarrow> y \<cdot> (y \<rightarrow> x)) = y \<cdot> (y \<rightarrow> x)"
  by (metis local.res_i3 resr_eq residuated_multr)
  
subclass pogroupoid
proof
  fix x y z
  show "x \<le> y \<Longrightarrow> x \<cdot> z \<le> y \<cdot> z"
    by (metis local.res_iso residuated_multl)
  show "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"
    by (metis local.res_iso residuated_multr)
qed

lemma resl_iso: "x \<le> y \<Longrightarrow> x \<leftarrow> z \<le> y \<leftarrow> z"
  by (metis res_residual_iso resl_eq residuated_multl)
  
lemma resr_iso: "x \<le> y \<Longrightarrow> z \<rightarrow> x \<le> z \<rightarrow> y"
  by (metis res_residual_iso resr_eq residuated_multr)

lemma resl_comp1 [simp]: "(x \<cdot> y \<leftarrow> y) \<cdot> y = x \<cdot> y"
  by (metis local.antisym local.mult_isor res_lc1 res_li1)
  
lemma resl_comp2 [simp]: "(x \<leftarrow> y) \<cdot> y \<leftarrow> y = x \<leftarrow> y"
  by (metis local.eq_iff res_lc1 res_li1 resl_iso)
  
lemma resr_comp1 [simp]: "y \<cdot> (y \<rightarrow> y \<cdot> x) = y \<cdot> x"
  by (metis local.antisym local.mult_isol res_rc1 res_ri1)
  
lemma resr_comp2 [simp]: "y \<rightarrow> y \<cdot> (y \<rightarrow> x) = y \<rightarrow> x"
  by (metis local.eq_iff res_rc1 res_ri1 resr_iso)
  
lemma resl_antitoner: "x \<le> y \<longrightarrow> z \<leftarrow> y \<le> z \<leftarrow> x"
  by (metis local.dual_order.trans local.mult_isol res_li1 reslI)

lemma resr_antitonel: "x \<le> y \<longrightarrow> y \<rightarrow> z \<le> x \<rightarrow> z"
  by (metis local.dual_order.trans local.resl_galois res_ri1 resrI)

text \<open>The following lemmas are taken from Galatos and \emph{al.}\<close>

lemma jipsen1l: "x \<le> y \<leftarrow> (x \<rightarrow> y)"
  by (metis res_ri1 reslI)
  
lemma jipsen1r: "x \<le> (y \<leftarrow> x) \<rightarrow> y"
  by (metis res_li1 resrI)
  
lemma jipsen2l: "(y \<leftarrow> (x \<rightarrow> y)) \<rightarrow> y = x \<rightarrow> y"
  by (metis jipsen1l jipsen1r local.eq_iff local.resr_antitonel)
  
lemma jipsen2r: "y \<leftarrow> ((y \<leftarrow> x) \<rightarrow> y) = y \<leftarrow> x"
  by (metis jipsen1l jipsen1r local.eq_iff local.resl_antitoner)
  
end (* residuated_pogroupoid *)

text \<open>
  In a residuated partial ordered semigroup, the multiplicative operator is associative.
\<close>
  
class residuated_posemigroup = semigroup_mult + residuated_pogroupoid 
begin

lemma resl_trans: "(x \<leftarrow> y)  \<cdot>  (y \<leftarrow> z) \<le> x \<leftarrow> z"
  by (metis local.res_li1 local.resl_antitoner local.resl_galois mult_assoc)
  
lemma resr_trans: "(x \<rightarrow> y)  \<cdot>  (y \<rightarrow> z) \<le> x \<rightarrow> z"
  by (metis local.res_ri1 local.resr_antitonel local.resr_galois mult_assoc)
  
lemma resr1: "(x \<rightarrow> y) \<cdot> z \<le> (x \<rightarrow> y \<cdot> z)"
  by (metis local.mult_isor local.res_ri1 local.resrI mult_assoc)
  
lemma resr2: "x \<rightarrow> y \<le> z \<cdot> x \<rightarrow> z \<cdot> y"
  by (metis local.mult_isol local.res_ri1 local.resrI mult_assoc)
  
lemma resr3: "x \<cdot> y \<rightarrow> z = y \<rightarrow> (x \<rightarrow> z)"
  by (metis local.eq_iff local.resr_galois mult_assoc)
  
lemma resl1: "z \<cdot> (x \<leftarrow> y) \<le> (z \<cdot> x \<leftarrow> y)"
  by (metis local.mult_isol local.res_li1 local.reslI mult_assoc)

lemma resl2: "x \<leftarrow> y \<le> x \<cdot> z \<leftarrow> y \<cdot> z"
  by (metis local.mult_isor local.res_li1 local.reslI mult_assoc)

lemma resl3: "x \<leftarrow> y \<cdot> z = (x \<leftarrow> z) \<leftarrow> y"
  by (metis local.eq_iff local.resl_galois mult_assoc)
  
lemma residual_assoc: "x \<rightarrow> (y \<leftarrow> z) = (x \<rightarrow> y) \<leftarrow> z"
proof (rule antisym)
  show "x \<rightarrow> (y \<leftarrow> z) \<le> (x \<rightarrow> y) \<leftarrow> z"
    by (metis local.res_ri1 local.resl_galois local.resr_galois mult_assoc)
  show "(x \<rightarrow> y) \<leftarrow> z \<le> x \<rightarrow> (y \<leftarrow> z)"
    by (metis local.res_li1 local.resl_galois local.resr_galois mult_assoc)
qed

end (* residuated_posemigroup *)

text \<open>
  In a residuated partially ordered monoid, the multiplicative operator has a unit $1$; that is,
  its reduct forms a monoid.
\<close>

class residuated_pomonoid = monoid_mult + residuated_pogroupoid 
begin

subclass residuated_posemigroup ..

lemma resl_unit: "x \<leftarrow> 1 = x"
  by (metis local.mult_1_right local.resl_comp1)

lemma resr_unit: "1 \<rightarrow> x = x"
  by (metis local.mult_1_left local.resr_comp1)
  
lemma mult_one_resl: "x \<cdot> (1 \<leftarrow> y) \<le> x \<leftarrow> y"  
  by (metis local.mult_1_right local.resl1)

lemma mult_one_resr: "(x \<rightarrow> 1) \<cdot> y \<le> x \<rightarrow> y"
  by (metis local.mult_1_left local.resr1)

text \<open>More lemmas from Galatos and \emph{al.} follow.\<close>

lemma jipsen3l: "1 \<le> x \<leftarrow> x"
  by (metis local.jipsen1l resr_unit)

lemma jipsen3r: "1 \<le> x \<rightarrow> x"
  by (metis local.jipsen1r resl_unit)
  
lemma jipsen4l [simp]: "(x \<leftarrow> x) \<cdot> x = x"
  by (metis local.mult_1_left local.resl_comp1)
  
lemma jipsen4r [simp]: "x \<cdot> (x \<rightarrow> x) = x"
  by (metis local.mult_1_right local.resr_comp1)
  
lemma jipsen5l [simp]: "(x \<leftarrow> x) \<cdot> (x \<leftarrow> x) = x \<leftarrow> x"
  by (metis jipsen4l local.resl3)
  
lemma jipsen5r [simp]: "(x \<rightarrow> x) \<cdot> (x \<rightarrow> x) = x \<rightarrow> x"
  by (metis jipsen4r local.resr3)
  
lemma jipsen6l: "y \<leftarrow> x \<le> (y \<leftarrow> z) \<leftarrow> (x \<leftarrow> z)"
  by (metis local.resl_galois local.resl_trans)
  
lemma jipsen6r: "x \<rightarrow> y \<le> (z \<rightarrow> x) \<rightarrow> (z \<rightarrow> y)"
  by (metis local.resr_galois local.resr_trans)
  
lemma jipsen7l: "y \<leftarrow> x \<le> (z \<leftarrow> y) \<rightarrow> (z \<leftarrow> x)"
  by (metis local.resr_galois local.resl_trans)
  
lemma jipsen7r: "x \<rightarrow> y \<le> (x \<rightarrow> z) \<leftarrow> (y \<rightarrow> z)"
  by (metis local.resl_galois local.resr_trans)

end (* residuated_pomonoid *)

text \<open>
  Residuated partially ordered groupoids can be expanded residuated join semilattice ordered groupoids.
  They are used as a base for action algebras, which are expansions 
  of Kleene algebras by operations of residuation.
  Action algebras can be found in the AFP entry for Kleene algebras.
\<close>

class residuated_sup_lgroupoid = semilattice_sup + residuated_pogroupoid
begin

lemma distl: "x \<cdot> (y \<squnion> z) = x \<cdot> y \<squnion> x \<cdot> z"
  by (metis local.residuated_multr local.residuated_sup)
  
lemma distr: "(x \<squnion> y) \<cdot> z = x \<cdot> z \<squnion> y \<cdot> z"
  by (metis local.residuated_multl local.residuated_sup)
  
lemma resl_subdist_var: "x \<leftarrow> z \<le> (x \<squnion> y) \<leftarrow> z"
  by (metis local.resl_iso local.sup_ge1)
 
lemma resl_subdist: "(x \<leftarrow> z) \<squnion> (y \<leftarrow> z) \<le> (x \<squnion> y) \<leftarrow> z"
  by (metis local.le_sup_iff local.sup_commute resl_subdist_var)
  
lemma resr_subdist_var: "(x \<rightarrow> y) \<le> x \<rightarrow> (y \<squnion> z)"
  by (metis local.resr_iso local.sup_ge1)
  
lemma resr_subdist: "(x \<rightarrow> y) \<squnion> (x \<rightarrow> z) \<le> x \<rightarrow> (y \<squnion> z)"
  by (metis sup_commute sup_least resr_subdist_var)
  
lemma resl_superdist_var: "x \<leftarrow> (y \<squnion> z) \<le> x \<leftarrow> y"
  by (metis local.le_sup_iff local.res_li1 local.reslI local.resr_galois)
  
lemma resr_superdist_var: "(x \<squnion> y) \<rightarrow> z \<le> x \<rightarrow> z"
  by (metis local.le_sup_iff local.res_ri1 local.resl_galois local.resrI)

end (* residuated_sup_lgroupoid *)

text \<open>
  Similarly, semigroup and monoid variants can be defined.
\<close>

class residuated_sup_lsemigroup = semilattice_sup + residuated_posemigroup
subclass (in residuated_sup_lsemigroup) residuated_sup_lgroupoid ..

class residuated_sup_lmonoid = semilattice_sup + residuated_posemigroup
subclass (in residuated_sup_lmonoid) residuated_sup_lsemigroup ..

text \<open>
  By lattice duality, we define residuated meet semillatice ordered groupoid.
\<close>

class residuated_inf_lgroupoid = semilattice_inf + residuated_pogroupoid
begin

lemma resl_dist: "(x \<sqinter> y) \<leftarrow> z = (x \<leftarrow> z) \<sqinter> (y \<leftarrow> z)"
  by (metis local.resl_eq local.residuated_inf local.residuated_multl)

lemma resr_dist: "x \<rightarrow> (y \<sqinter> z) = (x \<rightarrow> y) \<sqinter> (x \<rightarrow> z)"
  by (metis local.resr_eq local.residuated_inf local.residuated_multr)

lemma resl_inf_superdist: "x \<leftarrow> y \<le> x \<leftarrow> (y \<sqinter> z)"
  by (metis local.inf_le1 local.resl_antitoner)

lemma resr_inf_superdist_var: "x \<rightarrow> y \<le> (x \<sqinter> z) \<rightarrow> y"
  by (metis local.inf_le1 local.resr_antitonel)
  
end (* residuated_inf_lgroupoid *)

class residuated_inf_lsemigroup = semilattice_inf + residuated_posemigroup
subclass (in residuated_inf_lsemigroup) residuated_inf_lgroupoid ..

class residuated_inf_lmonoid = semilattice_inf + residuated_posemigroup
subclass (in residuated_inf_lmonoid) residuated_inf_lsemigroup ..

text \<open>
  Finally, we obtain residuated lattice groupoids. 
\<close>

class residuated_lgroupoid = lattice + residuated_pogroupoid
begin

subclass residuated_sup_lgroupoid ..

lemma resl_distr: "z \<leftarrow> (x \<squnion> y) = (z \<leftarrow> x) \<sqinter> (z \<leftarrow> y)"
proof (rule antisym)
  show "z \<leftarrow> x \<squnion> y \<le> (z \<leftarrow> x) \<sqinter> (z \<leftarrow> y)"
    by (metis local.inf.bounded_iff local.resl_superdist_var local.sup_commute)
  show "(z \<leftarrow> x) \<sqinter> (z \<leftarrow> y) \<le> z \<leftarrow> x \<squnion> y"
    by (metis local.inf.cobounded1 local.inf.cobounded2 local.resl_galois local.resr_galois local.sup.bounded_iff)
qed

lemma resr_distl: "(x \<squnion> y) \<rightarrow> z = (x \<rightarrow> z) \<sqinter> (y \<rightarrow> z)"
proof (rule antisym)
  show "x \<squnion> y \<rightarrow> z \<le> (x \<rightarrow> z) \<sqinter> (y \<rightarrow> z)"
    by (metis local.inf.bounded_iff local.resr_antitonel local.resr_superdist_var local.sup_ge2)
  show "(x \<rightarrow> z) \<sqinter> (y \<rightarrow> z) \<le> x \<squnion> y \<rightarrow> z"
    by (metis local.inf.cobounded1 local.inf.cobounded2 local.resl_galois local.resr_galois local.sup_least)
qed 

end (* residuated_lgroupoid *)

class residuated_lsemigroup = lattice + residuated_sup_lsemigroup
subclass (in residuated_lsemigroup) residuated_lgroupoid ..

class residuated_lmonoid = lattice + residuated_sup_lmonoid
subclass (in residuated_lmonoid) residuated_lsemigroup ..

class residuated_blgroupoid = bounded_lattice + residuated_pogroupoid
begin

lemma multl_strict [simp]: "x \<cdot> \<bottom> = \<bottom>"
  by (metis local.residuated_multr local.residuated_strict)

lemma multr_strict [simp]: "\<bottom> \<cdot> x = \<bottom>"
  by (metis local.residuated_multl local.residuated_strict)

lemma resl_top [simp]: "\<top> \<leftarrow> x = \<top>"
  by (metis local.res_top local.residuated_multl local.resl_eq)

lemma resl_impl [simp]: "x \<leftarrow> \<bottom> = \<top>"
  by (metis local.resl_comp2 multl_strict resl_top)

lemma resr_top [simp]: "x \<rightarrow> \<top> = \<top>"
  by (metis local.resrI local.top_greatest local.top_unique)

lemma resr_impl [simp]: "\<bottom> \<rightarrow> x = \<top>"
  by (metis local.resr_comp2 multr_strict resr_top)

end (* residuated_blgroupoid *)

class residuated_blsemigroup = bounded_lattice + residuated_sup_lsemigroup
subclass (in residuated_blsemigroup) residuated_blgroupoid ..

class residuated_blmonoid = bounded_lattice + residuated_sup_lmonoid
subclass (in residuated_blmonoid) residuated_blsemigroup ..

class residuated_clgroupoid = complete_lattice + residuated_pogroupoid
begin

lemma resl_eq_def: "y \<leftarrow> x = \<Squnion> {z. z \<cdot> x \<le> y}"
  by (metis local.residual_eq1 local.residuated_multl local.resl_eq)

lemma resr_eq_def: "x \<rightarrow> y = \<Squnion> {z. x \<cdot> z \<le> y}"
  by (metis local.residual_eq1 local.residuated_multr local.resr_eq)

lemma multl_def: "x \<cdot> y = \<Sqinter> {z. x \<le> z \<leftarrow> y}"
proof -
  have "\<Sqinter>{ya. x \<le> residual (\<lambda>a. a \<cdot> y) ya} = \<Sqinter>{z. x \<le> z \<leftarrow> y}"
    by simp
  thus ?thesis
    by (metis residuated_multl residual_eq2)
qed

lemma multr_def: "x \<cdot> y = \<Sqinter> {z. y \<le> x \<rightarrow> z}"
proof -
  have "\<Sqinter>{ya. y \<le> residual ((\<cdot>) x) ya} = \<Sqinter>{z. y \<le> x \<rightarrow> z}"
    by simp
  thus ?thesis
    by (metis residuated_multr residual_eq2)
qed

end (* residuated_clgroupoid *)

class residuated_clsemigroup = complete_lattice + residuated_sup_lsemigroup
subclass (in residuated_clsemigroup) residuated_clgroupoid ..

class residuated_clmonoid = complete_lattice + residuated_sup_lmonoid
subclass (in residuated_clmonoid) residuated_clsemigroup ..

end
