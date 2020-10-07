section \<open>Monotonic Boolean Transformers\<close>

theory Mono_Bool_Tran
imports
  LatticeProperties.Complete_Lattice_Prop
  LatticeProperties.Conj_Disj
begin

text\<open>
The type of monotonic transformers is the type associated to the set of monotonic
functions from a partially ordered set (poset) to itself. The type of monotonic
transformers with the pointwise extended order is also a poset. 
The monotonic transformers with composition and identity 
form a monoid, and the monoid operation is compatible with the order.

Gradually we extend the algebraic structure of monotonic transformers to
lattices, and complete lattices. We also introduce a dual operator 
($(\mathsf{dual}\;f) p = - f (-p)$) on monotonic transformers over
a boolean algebra. However the monotonic transformers over a boolean
algebra are not closed to the pointwise extended negation operator.

Finally we introduce an iteration operator on monotonic transformers
over a complete lattice.
\<close>

notation
  bot  ("\<bottom>") and
  top  ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  Inf  ("\<Sqinter>_" [900] 900) and
  Sup  ("\<Squnion>_" [900] 900)

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

lemma Inf_comp_fun:
  "\<Sqinter>M \<circ> f = (\<Sqinter>m\<in>M. m \<circ> f)"
  by (simp add: fun_eq_iff image_comp)

lemma INF_comp_fun:
  "(\<Sqinter>a\<in>A. g a) \<circ> f = (\<Sqinter>a\<in>A. g a \<circ> f)"
  by (simp add: fun_eq_iff image_comp)

lemma Sup_comp_fun:
  "\<Squnion>M \<circ> f = (\<Squnion>m\<in>M. m \<circ> f)"
  by (simp add: fun_eq_iff image_comp)

lemma SUP_comp_fun:
  "(\<Squnion>a\<in>A. g a) \<circ> f = (\<Squnion>a\<in>A. g a \<circ> f)"
  by (simp add: fun_eq_iff image_comp)

lemma (in order) mono_const [simp]:
  "mono (\<lambda>_. c)"
  by (auto intro: monoI)

lemma (in order) mono_id [simp]:
  "mono id"
  by (auto intro: order_class.monoI)

lemma (in order) mono_comp [simp]:
  "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (f \<circ> g)"
  by (auto intro!: monoI elim!: monoE order_class.monoE)

lemma (in bot) mono_bot [simp]:
  "mono \<bottom>"
  by (auto intro: monoI)

lemma (in top) mono_top [simp]:
  "mono \<top>"
  by (auto intro: monoI)

lemma (in semilattice_inf) mono_inf [simp]:
  assumes "mono f" and "mono g"
  shows "mono (f \<sqinter> g)"
proof
  fix a b
  assume "a \<le> b"
  have "f a \<sqinter> g a \<le> f a" by simp
  also from \<open>mono f\<close> \<open>a \<le> b\<close> have "\<dots> \<le> f b" by (auto elim: monoE)
  finally have *: "f a \<sqinter> g a \<le> f b" .
  have "f a \<sqinter> g a \<le> g a" by simp
  also from \<open>mono g\<close> \<open>a \<le> b\<close> have "\<dots> \<le> g b" by (auto elim: monoE)
  finally have **: "f a \<sqinter> g a \<le> g b" .
  from * ** show "(f \<sqinter> g) a \<le> (f \<sqinter> g) b" by auto
qed

lemma (in semilattice_sup) mono_sup [simp]:
  assumes "mono f" and "mono g"
  shows "mono (f \<squnion> g)"
proof
  fix a b
  assume "a \<le> b"
  from \<open>mono f\<close> \<open>a \<le> b\<close> have "f a \<le> f b" by (auto elim: monoE)
  also have "f b \<le> f b \<squnion> g b" by simp
  finally have *: "f a \<le> f b \<squnion> g b" .
  from \<open>mono g\<close> \<open>a \<le> b\<close> have "g a \<le> g b" by (auto elim: monoE)
  also have "g b \<le> f b \<squnion> g b" by simp
  finally have **: "g a \<le> f b \<squnion> g b" .
  from * ** show "(f \<squnion> g) a \<le> (f \<squnion> g) b" by auto
qed

lemma (in complete_lattice) mono_Inf [simp]:
  assumes "A \<subseteq> {f :: 'a \<Rightarrow> 'b:: complete_lattice. mono f}"
  shows "mono (\<Sqinter>A)"
proof
  fix a b
  assume "a \<le> b"
  { fix f
    assume "f \<in> A"
    with assms have "mono f" by auto
    with \<open>a \<le> b\<close> have "f a \<le> f b" by (auto elim: monoE)
  }
  then have "(\<Sqinter>f\<in>A. f a) \<le> (\<Sqinter>f\<in>A. f b)"
    by (auto intro: complete_lattice_class.INF_greatest complete_lattice_class.INF_lower2)
  then show "(\<Sqinter>A) a \<le> (\<Sqinter>A) b" by simp
qed

lemma (in complete_lattice) mono_Sup [simp]:
  assumes "A \<subseteq> {f :: 'a \<Rightarrow> 'b:: complete_lattice. mono f}"
  shows "mono (\<Squnion>A)"
proof
  fix a b
  assume "a \<le> b"
  { fix f
    assume "f \<in> A"
    with assms have "mono f" by auto
    with \<open>a \<le> b\<close> have "f a \<le> f b" by (auto elim: monoE)
  }
  then have "(\<Squnion>f\<in>A. f a) \<le> (\<Squnion>f\<in>A. f b)"
    by (auto intro: complete_lattice_class.SUP_least complete_lattice_class.SUP_upper2)
  then show "(\<Squnion>A) a \<le> (\<Squnion>A) b" by simp
qed

typedef (overloaded) 'a MonoTran = "{f::'a::order \<Rightarrow> 'a . mono f}"
proof
  show "id \<in> ?MonoTran" by simp
qed

lemma [simp]:
  "mono (Rep_MonoTran f)"
  using Rep_MonoTran [of f] by simp

setup_lifting type_definition_MonoTran

instantiation MonoTran :: (order) order
begin

lift_definition less_eq_MonoTran :: "'a MonoTran \<Rightarrow> 'a MonoTran \<Rightarrow> bool"
  is less_eq .

lift_definition less_MonoTran :: "'a MonoTran \<Rightarrow> 'a MonoTran \<Rightarrow> bool"
  is less .

instance
  by intro_classes (transfer, auto intro: order_antisym)+

end

instantiation MonoTran :: (order) monoid_mult
begin

lift_definition one_MonoTran :: "'a MonoTran"
  is id
  by (fact mono_id)

lift_definition times_MonoTran :: "'a MonoTran \<Rightarrow> 'a MonoTran \<Rightarrow> 'a MonoTran"
  is comp
  by (fact mono_comp)

instance
  by intro_classes (transfer, auto)+

end

instantiation MonoTran :: (order_bot) order_bot
begin

lift_definition bot_MonoTran :: "'a MonoTran"
  is \<bottom>
  by (fact mono_bot)

instance
  by intro_classes (transfer, simp)

end

instantiation MonoTran :: (order_top) order_top
begin

lift_definition top_MonoTran :: "'a MonoTran"
  is \<top>
  by (fact mono_top)

instance
  by intro_classes (transfer, simp)

end

instantiation MonoTran :: (lattice) lattice
begin

lift_definition inf_MonoTran :: "'a MonoTran \<Rightarrow> 'a MonoTran \<Rightarrow> 'a MonoTran"
  is inf
  by (fact mono_inf)

lift_definition sup_MonoTran :: "'a MonoTran \<Rightarrow> 'a MonoTran \<Rightarrow> 'a MonoTran"
  is sup
  by (fact mono_sup)

instance
  by intro_classes (transfer, simp)+

end

instance MonoTran :: (distrib_lattice) distrib_lattice
  by intro_classes (transfer, rule sup_inf_distrib1)

instantiation MonoTran :: (complete_lattice) complete_lattice
begin

lift_definition Inf_MonoTran :: "'a MonoTran set \<Rightarrow> 'a MonoTran"
  is Inf
  by (rule mono_Inf) auto

lift_definition Sup_MonoTran :: "'a MonoTran set \<Rightarrow> 'a MonoTran"
  is Sup
  by (rule mono_Sup) auto

instance
  by intro_classes (transfer, simp add: Inf_lower Sup_upper Inf_greatest Sup_least)+

end

context includes lifting_syntax
begin

lemma [transfer_rule]:
  "(rel_set A ===> (A ===> pcr_MonoTran HOL.eq) ===> pcr_MonoTran HOL.eq) (\<lambda>A f. \<Sqinter>(f ` A)) (\<lambda>A f. \<Sqinter>(f ` A))"
  by transfer_prover

lemma [transfer_rule]:
  "(rel_set A ===> (A ===> pcr_MonoTran HOL.eq) ===> pcr_MonoTran HOL.eq) (\<lambda>A f. \<Squnion>(f ` A)) (\<lambda>A f. \<Squnion>(f ` A))"
  by transfer_prover

end

instance MonoTran :: (complete_distrib_lattice) complete_distrib_lattice
proof (intro_classes, transfer)
  fix A :: "('a \<Rightarrow> 'a) set set"
  assume " \<forall>A\<in>A. Ball A mono"
  from this have [simp]: "{f ` A |f. \<forall>Y\<in>A. f Y \<in> Y} = {x. (\<exists>f. (\<forall>x. (\<forall>x\<in>x. mono x) \<longrightarrow> mono (f x)) \<and> x = f ` A \<and> (\<forall>Y\<in>A. f Y \<in> Y)) \<and> (\<forall>x\<in>x. mono x)}"
    apply safe
      apply (rule_tac x = "\<lambda> x . if x \<in> A then f x else \<bottom>" in exI)
      apply (simp add: if_split image_def)
    by blast+

  show " \<Sqinter>(Sup ` A) \<le> \<Squnion>(Inf ` {x. (\<exists>f\<in>Collect (pred_fun (\<lambda>A. Ball A mono) mono). x = f ` A \<and> (\<forall>Y\<in>A. f Y \<in> Y)) \<and> Ball x mono})"
    by (simp add: Inf_Sup)
qed



definition
  "dual_fun (f::'a::boolean_algebra \<Rightarrow> 'a) = uminus \<circ> f \<circ> uminus"

lemma dual_fun_apply [simp]:
  "dual_fun f p = - f (- p)"
  by (simp add: dual_fun_def)

lemma mono_dual_fun [simp]:
  "mono f \<Longrightarrow> mono (dual_fun f)"
  apply (rule monoI)
  apply (erule monoE)
  apply auto
  done

lemma (in order) mono_inf_fun [simp]:
  fixes x :: "'b::semilattice_inf"
  shows "mono (inf x)"
  by (auto intro!: order_class.monoI semilattice_inf_class.inf_mono)

lemma (in order) mono_sup_fun [simp]:
  fixes x :: "'b::semilattice_sup"
  shows "mono (sup x)"
  by (auto intro!: order_class.monoI semilattice_sup_class.sup_mono)

lemma mono_comp_fun:
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  shows "mono f \<Longrightarrow> mono ((\<circ>) f)"
  by (rule monoI) (auto simp add: le_fun_def elim: monoE)

definition
  "Omega_fun f g = inf g \<circ> comp f"

lemma Omega_fun_apply [simp]:
  "Omega_fun f g h p = (g p \<sqinter> f (h p))"
  by (simp add: Omega_fun_def)

lemma mono_Omega_fun [simp]:
  "mono f \<Longrightarrow> mono (Omega_fun f g)"
  unfolding Omega_fun_def
  by (auto intro: mono_comp mono_comp_fun)

lemma mono_mono_Omega_fun [simp]:
  fixes f :: "'b::order \<Rightarrow> 'a::semilattice_inf" and g :: "'c::semilattice_inf \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> mono g \<Longrightarrow> mono_mono (Omega_fun f g)"
  apply (auto simp add: mono_mono_def Omega_fun_def)
  apply (rule mono_comp)
  apply (rule mono_inf_fun)
  apply (rule mono_comp_fun)
  apply assumption
  done

definition 
  "omega_fun f = lfp (Omega_fun f id)"

definition
  "star_fun f = gfp (Omega_fun f id)"

lemma mono_omega_fun [simp]:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes "mono f"
  shows "mono (omega_fun f)"
proof
  fix a b :: 'a
  assume "a \<le> b"
  from assms have "mono (lfp (Omega_fun f id))"
    by (auto intro: mono_mono_Omega_fun)
  with \<open>a \<le> b\<close> show "omega_fun f a \<le> omega_fun f b"
    by (auto simp add: omega_fun_def elim: monoE)
qed

lemma mono_star_fun [simp]:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes "mono f"
  shows "mono (star_fun f)"
proof
  fix a b :: 'a
  assume "a \<le> b"
  from assms have "mono (gfp (Omega_fun f id))"
    by (auto intro: mono_mono_Omega_fun)
  with \<open>a \<le> b\<close> show "star_fun f a \<le> star_fun f b"
    by (auto simp add: star_fun_def elim: monoE)
qed

lemma lfp_omega_lowerbound:
  "mono f \<Longrightarrow> Omega_fun f g A \<le> A \<Longrightarrow> omega_fun f \<circ> g \<le> A"
  apply (simp add: omega_fun_def)
  apply (rule_tac P = "\<lambda> x . x \<circ> g \<le> A" and f = "Omega_fun f id" in lfp_ordinal_induct)
  apply simp_all
  apply (simp add: le_fun_def o_def inf_fun_def id_def Omega_fun_def)
  apply auto
  apply (rule_tac y = "f (A x) \<sqinter> g x" in order_trans)
  apply simp_all
  apply (rule_tac y = "f (S (g x))" in order_trans)
  apply simp_all
  apply (simp add: mono_def) apply (auto simp add: ac_simps)
  apply (unfold Sup_comp_fun)
  apply (rule SUP_least)
  by auto

lemma gfp_omega_upperbound:
  "mono f \<Longrightarrow> A \<le> Omega_fun f g A \<Longrightarrow> A \<le> star_fun f \<circ> g"
  apply (simp add: star_fun_def)
  apply (rule_tac P = "\<lambda> x . A \<le> x \<circ> g" and f = "Omega_fun f id" in gfp_ordinal_induct)
  apply simp_all
  apply (simp add: le_fun_def o_def inf_fun_def id_def Omega_fun_def)
  apply auto
  apply (rule_tac y = "f (A x) \<sqinter> g x" in order_trans)
  apply simp_all
  apply (rule_tac y = "f (A x)" in order_trans)
  apply simp_all
  apply (simp add: mono_def)
  apply (unfold Inf_comp_fun)
  apply (rule INF_greatest)
  by auto

lemma lfp_omega_greatest:
  assumes "\<And>u. Omega_fun f g u \<le> u \<Longrightarrow> A \<le> u"
  shows "A \<le> omega_fun f \<circ> g"
  apply (unfold omega_fun_def)
  apply (simp add: lfp_def)
  apply (unfold Inf_comp_fun)
  apply (rule INF_greatest)
  apply simp
  apply (rule assms)
  apply (simp add: le_fun_def)
  done

lemma gfp_star_least:
  assumes "\<And>u. u \<le> Omega_fun f g u \<Longrightarrow> u \<le> A"
  shows "star_fun f \<circ> g \<le> A"
  apply (unfold star_fun_def)
  apply (simp add: gfp_def)
  apply (unfold Sup_comp_fun)
  apply (rule SUP_least)
  apply simp
  apply (rule assms)
  apply (simp add: le_fun_def)
  done

lemma lfp_omega:
  "mono f \<Longrightarrow> omega_fun f \<circ> g = lfp (Omega_fun f g)"
  apply (rule antisym)
  apply (rule lfp_omega_lowerbound)
  apply simp_all
  apply (simp add: lfp_def)
  apply (rule Inf_greatest)
  apply safe
  apply (rule_tac y = "Omega_fun f g x" in order_trans)
  apply simp_all
  apply (rule_tac f = " Omega_fun f g" in monoD)
  apply simp_all
  apply (rule Inf_lower)
  apply simp
  apply (rule lfp_omega_greatest)
  apply (simp add: lfp_def)
  apply (rule Inf_lower)
  by simp

lemma gfp_star:
  "mono f \<Longrightarrow> star_fun f \<circ> g = gfp (Omega_fun f g)"
  apply (rule antisym)
  apply (rule gfp_star_least)
  apply (simp add: gfp_def)
  apply (rule Sup_upper, simp)
  apply (rule gfp_omega_upperbound)
  apply simp_all
  apply (simp add: gfp_def)
  apply (rule Sup_least)
  apply safe
  apply (rule_tac y = "Omega_fun f g x" in order_trans)
  apply simp_all
  apply (rule_tac f = " Omega_fun f g" in monoD)
  apply simp_all
  apply (rule Sup_upper)
  by simp

definition
  "assert_fun p q = (p \<sqinter> q :: 'a::semilattice_inf)"

lemma mono_assert_fun [simp]:
  "mono (assert_fun p)"
  apply (simp add: assert_fun_def mono_def, safe)
  by (rule_tac y = x in order_trans, simp_all)

lemma assert_fun_le_id [simp]: "assert_fun p \<le> id"
  by (simp add: assert_fun_def id_def le_fun_def)

lemma assert_fun_disjunctive [simp]: "assert_fun (p::'a::distrib_lattice) \<in> Apply.disjunctive"
  by (simp add: assert_fun_def Apply.disjunctive_def inf_sup_distrib)

definition
  "assertion_fun = range assert_fun"
  
lemma assert_cont:
  "(x :: 'a::boolean_algebra \<Rightarrow> 'a)  \<le> id \<Longrightarrow> x \<in> Apply.disjunctive \<Longrightarrow> x = assert_fun (x \<top>)"
  apply (rule antisym)
  apply (simp_all add: le_fun_def assert_fun_def, safe)
  apply (rule_tac f = x in  monoD, simp_all)
  apply (subgoal_tac "x top = sup (x xa) (x (-xa))")
  apply simp
  apply (subst inf_sup_distrib)
  apply simp
  apply (rule_tac y = "inf (- xa) xa" in order_trans)
  supply [[simproc del: boolean_algebra_cancel_inf]]
  apply (simp del: compl_inf_bot)
  apply (rule_tac y = "x (- xa)" in order_trans)
  apply simp
  apply simp
  apply simp
  apply (cut_tac x = x and y = xa and z = "-xa" in Apply.disjunctiveD, simp)
  apply (subst (asm) sup_commute)
  apply (subst (asm) compl_sup_top)
  by simp

lemma assertion_fun_disj_less_one: "assertion_fun = Apply.disjunctive \<inter> {x::'a::boolean_algebra \<Rightarrow> 'a . x \<le> id}"
  apply safe
  apply (simp_all add: assertion_fun_def, auto simp add: image_def)
  apply (rule_tac x = "x \<top>" in exI)
  by (rule assert_cont, simp_all)

lemma assert_fun_dual: "((assert_fun p) o \<top>) \<sqinter> (dual_fun (assert_fun p)) = assert_fun p"
  by (simp add: fun_eq_iff inf_fun_def dual_fun_def o_def assert_fun_def top_fun_def inf_sup_distrib)

lemma assertion_fun_dual: "x \<in> assertion_fun \<Longrightarrow> (x o \<top>) \<sqinter> (dual_fun x) = x"
  by (simp add: assertion_fun_def, safe, simp add: assert_fun_dual)

lemma assertion_fun_MonoTran [simp]: "x \<in> assertion_fun \<Longrightarrow> mono x"
  by (unfold assertion_fun_def, auto)

lemma assertion_fun_le_one [simp]: "x \<in> assertion_fun \<Longrightarrow> x \<le> id"
  by (unfold assertion_fun_def, auto)

end

