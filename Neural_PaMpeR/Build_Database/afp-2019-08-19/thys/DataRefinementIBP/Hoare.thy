section \<open>Hoare Triples\<close>

theory Hoare
imports Statements
begin

text \<open>
A hoare triple for $p,q\in \mathit{State}\ \mathit{set}$, and 
$S : \mathit{State}\ \mathit{set} \to \mathit{State}\ \mathit{set}$ is valid,
denoted $\models p \{|S|\} q$, if every execution of $S$ starting from state $s\in p$
always terminates, and if it terminates in state $s'$, then $s'\in q$. When $S$ is
modeled as a predicate transformer, this definition is equivalent to requiring that
$p$ is a subset of the initial states from which the execution of $S$ is guaranteed
to terminate in $q$, that is $p \subseteq S\ q$.

The formal definition of a valid hoare triple only assumes that $p$ (and also $S\ q$) ranges
over a complete lattice.
\<close>

definition
  Hoare :: "'a::complete_distrib_lattice \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> bool" ("\<Turnstile> (_){| _ |}(_)" [0,0,900] 900) where
  "\<Turnstile> p {|S|} q = (p \<le> (S q))"

theorem hoare_sequential:
  "mono S \<Longrightarrow> (\<Turnstile> p {| S o T |} r) = ( (\<exists> q. \<Turnstile> p {| S |} q \<and> \<Turnstile> q {| T |} r))"
  by (metis (no_types) Hoare_def monoD o_def order_refl order_trans)

theorem hoare_choice:
  "\<Turnstile> p {| S \<sqinter> T |} q = (\<Turnstile> p {| S |} q \<and> \<Turnstile> p {| T |} q)"
  by (simp_all add: Hoare_def inf_fun_def)

theorem hoare_assume:
  "(\<Turnstile> P {| [.R.] |} Q) = (P \<sqinter> R \<le> Q)"
  apply (simp add: Hoare_def assume_def)
  apply safe
  apply (case_tac "(inf P R) \<le> (inf (sup (- R) Q) R)")
  apply (simp add: inf_sup_distrib2)
  apply (simp add: le_infI1)
  apply (case_tac "(sup (-R) (inf P R)) \<le> sup (- R) Q")
  apply (simp add: sup_inf_distrib1)
  by (simp add: le_supI2)

theorem hoare_mono:
  "mono S \<Longrightarrow> Q \<le> R \<Longrightarrow> \<Turnstile> P {| S |} Q \<Longrightarrow> \<Turnstile> P {| S |} R"
  apply (simp add: mono_def Hoare_def)
  apply (rule_tac y = "S Q" in order_trans)
  by auto

theorem hoare_pre:
  "R \<le> P \<Longrightarrow> \<Turnstile> P {| S |} Q \<Longrightarrow> \<Turnstile> R {| S |} Q"
  by (simp add: Hoare_def)

theorem hoare_Sup:
  "(\<forall> p \<in> P . \<Turnstile> p {| S |} q) = \<Turnstile> Sup P {| S |} q"
  apply (simp add: Hoare_def, safe, simp add: Sup_least)
  apply (rule_tac y = "\<Squnion>P" in order_trans, simp_all)
  by (simp add: Sup_upper)
  
lemma hoare_magic [simp]: "\<Turnstile> P {| \<top> |} Q" 
  by (simp add: Hoare_def top_fun_def)

lemma hoare_demonic: "\<Turnstile> P {| [:R:] |} Q = (\<forall> s . s \<in> P \<longrightarrow>  R s \<subseteq> Q)"
  apply (unfold Hoare_def demonic_def)
  by auto

lemma hoare_not_guard:
  "mono (S :: (_::order_bot) \<Rightarrow> _) \<Longrightarrow> \<Turnstile> p {| S |} q = \<Turnstile> (p \<squnion> (- grd S)) {| S |} q"
  apply (simp add: Hoare_def grd_def, safe)
  apply (drule monoD)
  by auto

subsection \<open>Hoare rule for recursive statements\<close>

text \<open>
A statement $S$ is refined by another statement $S'$ if $\models p \{| S' |\} q$ 
is true for all $p$ and $q$ such that  $\models p \{| S |\} q$ is true. This
is equivalent to $S \le S'$. 

Next theorem can be used to prove refinement of a recursive program. A recursive
program is modeled as the least fixpoint of a monotonic mapping from predicate
transformers to predicate transformers.
\<close>

theorem lfp_wf_induction:
  "mono f \<Longrightarrow> (\<forall> w . (p w) \<le> f (Sup_less p w)) \<Longrightarrow> Sup (range p) \<le> lfp f"
 apply (rule fp_wf_induction, simp_all)
 by (drule lfp_unfold, simp)

definition
  "post_fun (p::'a::order) q = (if p \<le> q then \<top> else \<bottom>)"

lemma post_mono [simp]: "mono (post_fun p :: (_::{order_bot,order_top}))"
   apply (simp add: post_fun_def  mono_def, safe)
   apply (subgoal_tac "p \<le> y", simp)
   by (rule_tac y = x in order_trans, simp_all)

lemma post_top [simp]: "post_fun p p = \<top>"
  by (simp add: post_fun_def)

lemma post_refin [simp]: "mono S \<Longrightarrow> ((S p)::'a::bounded_lattice) \<sqinter> (post_fun p) x \<le> S x"
  apply (simp add: le_fun_def post_fun_def, safe)
  by (rule_tac f = S in monoD, simp_all)

text \<open>
Next theorem shows the equivalence between the validity of Hoare
triples and refinement statements. This theorem together with the
theorem for refinement of recursive programs will be used to prove
a Hoare rule for recursive programs.
\<close>

theorem hoare_refinement_post:
  "mono f \<Longrightarrow>  (\<Turnstile> x {| f |} y) = ({.x.} o (post_fun y) \<le> f)"
  apply safe
  apply (simp_all add: Hoare_def)
  apply (simp_all add: le_fun_def)
  apply (simp add: assert_def, safe)
  apply (rule_tac y = "f y \<sqinter> post_fun y xa" in order_trans, simp_all)
  apply (rule_tac y = "x" in order_trans, simp_all)
  apply (simp add: assert_def)
  by (drule_tac x = "y" in spec, simp)


text \<open>
Next theorem gives a Hoare rule for recursive programs. If we can prove correct the unfolding 
of the recursive definition applid to a program $f$, $\models p\ w\ \{| F\  f |\}\  y$, assumming
that $f$ is correct when starting from $p\  v$, $v<w$, $\models SUP-L\  p\  w\  \{| f |\}\  y$, then
the recursive program is correct $\models SUP\ p\ \{| lfp\  F |\}\  y$
\<close>

lemma assert_Sup: "{.\<Squnion> (X::'a::complete_distrib_lattice set).} = \<Squnion> (assert ` X)"
  by (simp add: fun_eq_iff assert_def Sup_inf image_comp)

lemma assert_Sup_range: "{.\<Squnion> (range (p::'W \<Rightarrow> 'a::complete_distrib_lattice)).} = \<Squnion> (range (assert o p))"
  by (simp add: fun_eq_iff assert_def SUP_inf image_comp)

lemma Sup_range_comp: "(\<Squnion> range p) o S = \<Squnion> (range (\<lambda> w . ((p w) o S)))"
  by (simp add: fun_eq_iff image_comp)

lemma Sup_less_comp: "(Sup_less P) w o S = Sup_less (\<lambda> w . ((P w) o S)) w"
  apply (simp add: Sup_less_def fun_eq_iff, safe)
  apply (subgoal_tac "((\<lambda>f. f (S x)) ` {y. \<exists>v<w. \<forall>x. y x = P v x}) = ((\<lambda>f. f x) ` {y. \<exists>v<w. \<forall>x. y x = P v (S x)})")
  apply (auto cong del: SUP_cong_simp)
  done

lemma Sup_less_assert: "Sup_less (\<lambda>w. {. (p w)::'a::complete_distrib_lattice .}) w = {.Sup_less p w.}"
  apply (simp add: Sup_less_def assert_Sup image_def)
  apply (subgoal_tac "{y. \<exists>v<w. y = {. p v .}} = {y. \<exists>x. (\<exists>v<w. x = p v) \<and> y = {. x .}}")
  apply (auto simp add: image_def cong del: SUP_cong_simp)
  done


declare mono_comp[simp]

theorem hoare_fixpoint:
  "mono_mono F \<Longrightarrow>
   (!! w f . mono f \<and> \<Turnstile> Sup_less p w {| f |} y \<Longrightarrow> \<Turnstile> p w {| F f |} y) \<Longrightarrow> \<Turnstile> (Sup (range p)) {| lfp F |} y"
  apply (simp add: mono_mono_def hoare_refinement_post assert_Sup_range Sup_range_comp)
  apply (rule lfp_wf_induction)
  apply auto
  apply (simp add: Sup_less_comp [THEN sym])
  apply (simp add: Sup_less_assert)
  apply (drule_tac x = "{. Sup_less p w .} \<circ> post_fun y" in spec, safe)
  apply simp
  by (simp add: hoare_refinement_post)

theorem "(\<forall> t . \<Turnstile> ({s . t \<in> R s}) {|S|} q) \<Longrightarrow> \<Turnstile> ({:R:} p) {| S |} q"
  apply (simp add: Hoare_def angelic_def subset_eq)
  by auto

end
