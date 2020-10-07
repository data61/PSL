theory Refinement imports Main
begin
  section\<open>Monotonic Predicate Transformers\<close>
text\<open>
  In this section we introduce the basics of refinement calculus \cite{back-wright-98}.
  Part of this theory is a reformulation of some definitions from \cite{preoteasa:back:2010a},
  but here they are given for predicates, while \cite{preoteasa:back:2010a} uses
  sets.
\<close>

  notation
    bot ("\<bottom>") and
    top ("\<top>") and
    inf (infixl "\<sqinter>" 70)
    and sup (infixl "\<squnion>" 65)

  subsection\<open>Basic predicate transformers\<close>

  definition
    demonic :: "('a => 'b::lattice) => 'b => 'a \<Rightarrow> bool" ("[: _ :]" [0] 1000) where
    "[:Q:] p s = (Q s \<le> p)"

  definition
    assert::"'a::semilattice_inf => 'a => 'a" ("{. _ .}" [0] 1000) where
    "{.p.} q \<equiv>  p \<sqinter> q"

  definition
    "assume"::"('a::boolean_algebra) => 'a => 'a" ("[. _ .]" [0] 1000) where
    "[.p.] q \<equiv>  (-p \<squnion> q)"

  definition
    angelic :: "('a \<Rightarrow> 'b::{semilattice_inf,order_bot}) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool" ("{: _ :}" [0] 1000) where
    "{:Q:} p s = (Q s \<sqinter> p \<noteq> \<bottom>)"

  syntax
    "_assert" :: "patterns => logic => logic"    ("(1{._./ _.})")
  translations
    "_assert (_patterns x xs) P" == "CONST assert (CONST id (_abs (_pattern x xs) P))"
    "_assert x P" == "CONST assert (CONST id (_abs x P))"

  term "{.x,z . P x y.}"

  syntax "_update" :: "patterns => patterns => logic => logic" ("_ \<leadsto> _ . _" 0)
  translations
    "_update (_patterns x xs) (_patterns y ys) t" == "CONST id (_abs
         (_pattern x xs) (CONST id (_abs (_pattern y ys) t)))"
    "_update x y t" == "CONST id (_abs x (CONST id (_abs y t)))"

  term "[: x \<leadsto> z . (P::'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool) x y y' z :]"
  term "[: x, y \<leadsto> y', z . (P::'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool) x y y' z :]"
  term "{: x, y \<leadsto> y', z . (P::'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool) x y y' z :}"

  lemma demonic_demonic: "[:r:] o [:r':] = [:r OO r':]"
    by (simp add: fun_eq_iff le_fun_def demonic_def, auto)

  lemma assert_demonic_comp: "{.p.} o [:r:] o {.p'.} o [:r':] = 
      {.x . p x \<and> (\<forall> y . r x y \<longrightarrow> p' y).} o [:r OO r':]"
      by (auto simp add: fun_eq_iff le_fun_def assert_def demonic_def)

  lemma demonic_assert_comp: "[:r:] o {.p.} = {.x.(\<forall> y . r x y \<longrightarrow> p y).} o [:r:]"
      by (auto simp add: fun_eq_iff le_fun_def assert_def demonic_def)

  lemma assert_assert_comp: "{.p::'a::lattice.} o {.p'.} = {.p \<sqinter> p'.}"
      by (simp add: fun_eq_iff le_fun_def assert_def demonic_def inf_assoc)
  
  definition "inpt r x = (\<exists> y . r x y)"

  definition "trs r = {. inpt r.} o [:r:]"

  lemma "trs (\<lambda> x y . x = y) q x = q x"
    by (simp add: trs_def fun_eq_iff assert_def demonic_def inpt_def bot_fun_def le_fun_def)

  lemma assert_demonic_prop: "{.p.} o [:r:] = {.p.} o [:(\<lambda> x y . p x) \<sqinter> r:]"
    by (auto simp add: fun_eq_iff assert_def demonic_def)

  lemma relcompp_exists: "relcompp r r' x y = (\<exists> u . r x u \<and> r' u y)"
    by auto

  lemma trs_trs: "(trs r) o (trs r') = trs ((\<lambda> s t. (\<forall> s' . r s s' \<longrightarrow> (inpt r' s'))) \<sqinter> (r OO r'))" (is "?S = ?T")
    proof -
      have [simp]: "(\<lambda>x. inpt r x \<and> (\<forall>y. r x y \<longrightarrow> inpt r' y)) = inpt ((\<lambda>s t. \<forall>s'. r s s' \<longrightarrow> inpt r' s') \<sqinter> r OO r')"
        by (auto simp add: fun_eq_iff inpt_def relcompp_exists, blast)
      have [simp]: "(\<lambda>x y. inpt r x \<and> (\<forall>y. r x y \<longrightarrow> inpt r' y)) \<sqinter> r OO r' = (\<lambda>s t. \<forall>s'. r s s' \<longrightarrow> inpt r' s') \<sqinter> r OO r'"
        by (auto simp add: fun_eq_iff inpt_def)
      have "?S = {. inpt r .} \<circ> [: r :] \<circ> {. inpt r' .} \<circ> [: r' :]"
        by (simp add: trs_def comp_assoc[symmetric])
      also have "... = {. \<lambda>x. inpt r x \<and> (\<forall>y. r x y \<longrightarrow> inpt r' y) .} \<circ> [: r OO r' :]"
        by (simp add: assert_demonic_comp)
      also have "... =  {. \<lambda>x. inpt r x \<and> (\<forall>y. r x y \<longrightarrow> inpt r' y) .} o [:(\<lambda> x y . inpt r x \<and> (\<forall>y. r x y \<longrightarrow> inpt r' y))  \<sqinter> (r OO r'):]"
        by (subst assert_demonic_prop, simp)
      also have "... = ?T"
        by (simp add: trs_def)
      finally show ?thesis by simp
    qed

  lemma assert_demonic_refinement: "({.p.} o [:r:] \<le> {.p'.} o [:r':]) = (p \<le> p' \<and> (\<forall> x . p x \<longrightarrow> r' x \<le> r x))"
    by  (auto simp add: le_fun_def assert_def demonic_def)

  lemma trs_refinement: "(trs r \<le> trs r') = ((\<forall> x . inpt r x \<longrightarrow> inpt r' x) \<and> (\<forall> x . inpt r x \<longrightarrow> r' x \<le> r x))"
    by (simp add: trs_def assert_demonic_refinement, simp add: le_fun_def)

  lemma "trs (\<lambda> x y . x \<ge> 0) \<le> trs (\<lambda> x y . x = y)"
    by (simp add: trs_def le_fun_def assert_def demonic_def inpt_def)

  lemma "trs (\<lambda> x y . x \<ge> 0) q x = (if q = \<top> then x \<ge> 0 else False)"
     by (auto simp add: trs_def fun_eq_iff assert_def demonic_def inpt_def bot_fun_def)

  lemma "[:r:] \<sqinter> [:r':] = [:r \<squnion> r':]"
    by (simp add: fun_eq_iff demonic_def)

  lemma spec_demonic_choice: "({.p.} o [:r:]) \<sqinter> ({.p'.} o [:r':]) = ({.p \<sqinter> p'.} o [:r \<squnion> r':])"
    by (auto simp add: fun_eq_iff demonic_def assert_def)

  lemma trs_demonic_choice: "trs r \<sqinter> trs r' = trs ((\<lambda> x y . inpt r x \<and> inpt r' x) \<sqinter> (r \<squnion> r'))"
    proof -
      have [simp]: "inpt ((\<lambda>x y. inpt r x \<and> inpt r' x) \<sqinter> (r \<squnion> r')) = inpt r \<sqinter> inpt r'"
        by (auto simp add: fun_eq_iff inpt_def)
      have "trs r \<sqinter> trs r' = {. inpt r \<sqinter> inpt r' .} \<circ> [: r \<squnion> r' :]"
        by (simp add: trs_def spec_demonic_choice)
      also have "... = {. inpt r \<sqinter> inpt r' .} \<circ> [: (\<lambda> x y . inpt r x \<and> inpt r' x) \<sqinter> (r \<squnion> r') :]"
        by (subst assert_demonic_prop, simp)
      also have "... = trs ((\<lambda> x y . inpt r x \<and> inpt r' x) \<sqinter> (r \<squnion> r'))"
        by (simp add: trs_def)
      finally show ?thesis by simp
    qed

  lemma "p \<sqinter> p' = \<bottom> \<Longrightarrow> ({.p.} o [:r:]) \<squnion> ({.p'.} o [:r':]) = {.p \<squnion> p'.} o [:(\<lambda> x y . p x \<longrightarrow> r x y) \<sqinter> ((\<lambda> x y . p' x \<longrightarrow> r' x y)):]"
    by (simp add: fun_eq_iff assert_def demonic_def, auto)

  subsection\<open>Conjunctive predicate transformers\<close>

  definition "conjunctive (S::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) = (\<forall> Q . S (Inf Q) = Inf (S ` Q))"
  definition "sconjunctive (S::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) = (\<forall> Q . (\<exists> x . x \<in> Q) \<longrightarrow> S (Inf Q) = Inf (S ` Q))"

  lemma [simp]: "conjunctive S \<Longrightarrow> sconjunctive S"
    by (simp add: conjunctive_def sconjunctive_def)

  lemma [simp]: "conjunctive \<top>"
    by (simp add: conjunctive_def)

  lemma conjuncive_demonic [simp]: "conjunctive [:r:]"
    proof (auto simp add: conjunctive_def fun_eq_iff demonic_def)
      fix Q:: "'a set" fix y::'a fix x :: 'b
      assume A: "y \<in> Q"
      assume "r x \<le> Inf Q"
      also from A have "Inf Q \<le> y"
        by (rule Inf_lower)
      finally show "r x \<le> y" by simp
    next
      fix Q:: "'a set" fix x :: 'b
      assume A : "\<forall>y\<in>Q. r x \<le> y"
      show "r x \<le> Inf Q"
        by (rule Inf_greatest, simp add: A)
    qed

  lemma sconjunctive_assert [simp]: "sconjunctive {.p.}"
    proof (auto simp add: sconjunctive_def assert_def image_def cong: INF_cong_simp, rule antisym, auto)
      fix Q :: "'a set"
      have [simp]: "\<And> x . x \<in> Q \<Longrightarrow> Inf Q \<le> x"
        by (rule Inf_lower, simp)
      have A: "\<And> x . x \<in> Q \<Longrightarrow> p \<sqinter> Inf Q \<le> p \<sqinter> x"
        by (simp, rule_tac y = "Inf Q" in order_trans, simp_all)
      show "p \<sqinter> Inf Q \<le> (INF x\<in>Q. p \<sqinter> x)"
        by (rule Inf_greatest, safe, rule A, simp)
    next
      fix Q :: "'a set"
      fix x :: 'a
      assume A: "x \<in> Q"
      have "Inf {y. \<exists>x\<in>Q. y = p \<sqinter> x} \<le> p \<sqinter> x"
        by (rule Inf_lower, cut_tac A, auto)
      also have "... \<le> p"
        by simp
      finally show "(INF x\<in>Q. p \<sqinter> x) \<le> p"
        by (simp only: image_def)
   next
      fix Q :: "'a set"
      show "(INF x\<in>Q. p \<sqinter> x) \<le> Inf Q"
        proof (rule Inf_greatest)
          fix x::'a
          assume A: "x \<in> Q"
          have "Inf {y. \<exists>x\<in>Q. y = p \<sqinter> x} \<le> p \<sqinter> x"
            by (cut_tac A, rule Inf_lower, blast)
          also have "... \<le> x"
            by simp
         finally show "(INF x\<in>Q. p \<sqinter> x) \<le> x"
            by (simp only: image_def)
       qed
   qed

  lemma sconjunctive_simp: "x \<in> Q \<Longrightarrow> sconjunctive S \<Longrightarrow> S (Inf Q) = Inf (S ` Q)"
    by (auto simp add: sconjunctive_def)

  lemma sconjunctive_INF_simp: "x \<in> X \<Longrightarrow> sconjunctive S \<Longrightarrow> S (Inf (Q ` X)) = Inf (S ` (Q ` X))"
    by (cut_tac x = "Q x" and Q = "Q ` X" in sconjunctive_simp, auto)

  lemma demonic_comp [simp]: "sconjunctive S \<Longrightarrow> sconjunctive S' \<Longrightarrow> sconjunctive (S o S')"
    proof (subst sconjunctive_def, safe)
      fix X :: "'c set"
      fix a :: 'c
      assume [simp]: "sconjunctive S"
      assume [simp]: "sconjunctive S'"
      assume [simp]: "a \<in> X"
      have A: "S' (Inf X) = Inf (S' ` X)"
        by (rule_tac x = a in sconjunctive_simp, auto)
      also have B: "S (Inf (S' ` X)) = Inf (S ` (S' ` X))"
        by (rule_tac x = "S' a" in sconjunctive_simp, auto)
      finally show "(S o S') (Inf X) = Inf ((S \<circ> S') ` X)" by (simp add: image_comp)
    qed

  lemma [simp]:"conjunctive S \<Longrightarrow> S (Inf (Q ` X)) = (Inf ((S o Q) ` X))"
    by (metis INF_image conjunctive_def)

  lemma conjunctive_simp: "conjunctive S \<Longrightarrow>  S (Inf Q) = Inf (S ` Q)"
    by (metis conjunctive_def)

  lemma conjunctive_monotonic: "sconjunctive S \<Longrightarrow> mono S"
    proof (rule monoI)
      fix a b :: 'a
      assume [simp]: "a \<le> b"
      assume [simp]: "sconjunctive S"
      have [simp]: "a \<sqinter> b = a"
        by (rule antisym, auto)
      have A: "S a = S a \<sqinter> S b"
        by (cut_tac S = S and x = a and Q = "{a, b}" in sconjunctive_simp, auto)
      show "S a \<le> S b"
        by (subst A, simp)
    qed

  definition "grd S = - S \<bottom>"

  lemma "grd [:r:] = inpt r"
    by (simp add: fun_eq_iff grd_def demonic_def le_fun_def inpt_def)

  definition "fail S = -(S \<top>)"
  definition "term S = (S \<top>)"

  lemma "fail ({.p.} o [:r :: 'a \<Rightarrow> 'b \<Rightarrow> bool:]) = -p"
    by (simp add: fail_def fun_eq_iff assert_def demonic_def le_fun_def top_fun_def)

  definition "Fail = \<bottom>"

  lemma "mono (S::'a::boolean_algebra \<Rightarrow> 'b::boolean_algebra) \<Longrightarrow> (S = Fail) = (fail S = \<top>)"
    proof auto
      show "fail (Fail::'a \<Rightarrow> 'b) = \<top>"
        by (metis Fail_def bot_apply compl_bot_eq fail_def)
    next
      assume A: "mono S"
      assume B: "fail S = \<top>"
      show "S = Fail"
        proof (rule antisym)
          show "S \<le> Fail"
            by (metis (hide_lams, no_types) A B bot.extremum_unique compl_le_compl_iff fail_def le_fun_def monoD top_greatest)
          next
            show "Fail \<le> S"
              by (metis Fail_def bot.extremum)
        qed
   qed

  definition "Skip = id"

  lemma [simp]: "{.\<top>::'a::bounded_lattice.} = Skip"
    by (simp add: fun_eq_iff assert_def Skip_def)

  lemma [simp]:"Skip o S = S"
    by (simp add: fun_eq_iff assert_def Skip_def)

  lemma [simp]:"S o Skip = S"
    by (simp add: fun_eq_iff assert_def Skip_def)

  lemma [simp]: "mono S \<Longrightarrow> mono S' \<Longrightarrow> mono (S o S')"
    by (simp add: mono_def)

  lemma [simp]: "mono {.p::('a \<Rightarrow> bool).}"
    by (simp add: conjunctive_monotonic)

  lemma [simp]: "mono [:r::('a \<Rightarrow> 'b \<Rightarrow> bool):]"
    by (simp add: conjunctive_monotonic)

  lemma [simp]:"{. \<lambda> x . True .} = Skip"
    by (simp add: fun_eq_iff assert_def Skip_def)
    
  lemma [simp]: "\<bottom> o S = \<bottom>"
    by (simp add: fun_eq_iff)

  lemma [simp]: "{.\<bottom>::'a::boolean_algebra.}  = \<bottom>"
    by (simp add: fun_eq_iff assert_def)

  lemma [simp]: "\<top> o S = \<top>"
    by (simp add: fun_eq_iff)

  lemma left_comp: "T o U = T' o U' \<Longrightarrow> S o T o U = S o T' o U'"
    by (simp add: comp_assoc)

  lemma assert_demonic: "{.p.} o [:r:] = {.p.} o [:\<lambda> x y . p x \<and> r x y:]"
    by (auto simp add: fun_eq_iff assert_def demonic_def le_fun_def)

  lemma "trs r \<sqinter> trs r' = trs (\<lambda> x y . inpt r x \<and> inpt r' x \<and> (r x y \<or> r' x y))"  
    by (auto simp add: fun_eq_iff trs_def assert_def demonic_def inpt_def)

  subsection\<open>Fusion of predicate transformers\<close>
  
  text\<open>
  In this section we define the fusion operator from \cite{back:butler:1995}. The fusion
  of two programs $S$ and $T$ is intuitively equivalent with the parallel execution of the two
  programs. If $S$ and $T$ assign nondeterministically some value to some program variable
  $x$, then the fusion of $S$ and $T$ will assign a value to $x$ which can be assigned by
  both $S$ and $T$.
\<close>

  definition fusion :: "(('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)) \<Rightarrow> (('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)) \<Rightarrow> (('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool))" (infixl "\<parallel>" 70) where
    "(S \<parallel> S') q x = (\<exists> (p::'a\<Rightarrow>bool) p' . p \<sqinter> p' \<le> q \<and> S p x \<and> S' p' x)"

  lemma fusion_spec: "({.p.} \<circ> [:r:]) \<parallel> ({.p'.} \<circ> [:r':]) = ({.p \<sqinter> p'.} \<circ> [:r \<sqinter> r':])"
    by (auto simp add: fun_eq_iff fusion_def assert_def demonic_def le_fun_def)

  lemma fusion_assoc: "S \<parallel> (T \<parallel> U) = (S \<parallel> T) \<parallel> U"
    proof (rule antisym, auto simp add: fusion_def)
      fix p p' q s s' :: "'a \<Rightarrow> bool"
      fix a
      assume A: "p \<sqinter> p' \<le> q" and B: "s \<sqinter> s' \<le> p'"
      assume C: "S p a" and D: "T s a" and E: "U s' a"
      from A and B  have F: "(p \<sqinter> s) \<sqinter> s' \<le> q"
        by (simp add: le_fun_def)
      have "(\<exists>v v'. v \<sqinter> v' \<le> (p \<sqinter> s) \<and> S v a \<and> T v' a)"
        by (metis C D order_refl)
      show "\<exists>u u' . u \<sqinter> u' \<le> q \<and> (\<exists>v v'. v \<sqinter> v' \<le> u \<and> S v a \<and> T v' a) \<and> U u' a"
        by (metis F C D E order_refl)
    next
      fix p p' q s s' :: "'a \<Rightarrow> bool"
      fix a
      assume A: "p \<sqinter> p' \<le> q" and B: "s \<sqinter> s' \<le> p"
      assume C: "S s a" and D: "T s' a" and E: "U p' a"
      from A and B  have F: "s \<sqinter> (s' \<sqinter> p')  \<le> q"
        by (simp add: le_fun_def)
      have "(\<exists>v v'. v \<sqinter> v' \<le> s' \<sqinter> p' \<and> T v a \<and> U v' a)"
        by (metis D E eq_iff)
      show "\<exists>u u'. u \<sqinter> u' \<le> q \<and> S u a \<and> (\<exists>v v'. v \<sqinter> v' \<le> u' \<and> T v a \<and> U v' a)"
        by (metis F C D E order_refl)
    qed

  lemma "P \<le> Q \<Longrightarrow> P' \<le> Q' \<Longrightarrow> P \<parallel> P' \<le> Q \<parallel> Q'"
    by (simp add: le_fun_def fusion_def, metis)

  lemma "conjunctive S \<Longrightarrow> S \<parallel> \<top> = \<top>"
    by (auto simp add: fun_eq_iff fusion_def le_fun_def conjunctive_def)

  lemma fusion_spec_local: "a \<in> init \<Longrightarrow> ([:x \<leadsto> u, y . u \<in> init \<and> x = y:] \<circ> {.p.} \<circ> [:r:]) \<parallel> ({.p'.} \<circ> [:r':]) 
      = [:x \<leadsto> u, y . u \<in> init \<and> x = y:] \<circ> {.u,x . p (u, x) \<and> p' x.} \<circ> [:u, x \<leadsto> y . r (u, x) y \<and> r' x y:]" (is "?p \<Longrightarrow> ?S = ?T")
    proof -
      assume "?p"
      from this have [simp]: "(\<lambda>x. \<forall>a. a \<in> init \<longrightarrow> p (a, x) \<and> p' x) = (\<lambda>x. \<forall>a. a \<in> init \<longrightarrow> p (a, x)) \<sqinter> p'"
         by auto
      have [simp]: "(\<lambda>x (u, y). u \<in> init \<and> x = y) OO (\<lambda>(u, x) y. r (u, x) y \<and> r' x y) = (\<lambda>x (u, y). u \<in> init \<and> x = y) OO r \<sqinter> r'"
        by auto
      have "?S = 
        ({. \<lambda>x. \<forall>a. a \<in> init \<longrightarrow> p (a, x) .} \<circ> [: \<lambda>x (u, y). u \<in> init \<and> x = y :] \<circ> [: r :]) \<parallel> ({. p' .} \<circ> [: r' :])"
        by (simp add: demonic_assert_comp)
      also have "... =  {. (\<lambda>x. \<forall>a. a \<in> init \<longrightarrow> p (a, x)) \<sqinter> p' .} \<circ> [: (\<lambda>x (u, y). u \<in> init \<and> x = y) OO r \<sqinter> r' :]"
        by (simp add: comp_assoc demonic_demonic fusion_spec)
      also have "... = ?T"
        by (simp add: demonic_assert_comp comp_assoc demonic_demonic fusion_spec)
      finally show ?thesis by simp
    qed

  lemma fusion_spec_local_a: "a \<in> init \<Longrightarrow> ([:x \<leadsto> u, y . u \<in> init \<and> x = y:] \<circ> {.p.} \<circ> [:r:]) \<parallel> [:r':] 
      = ([:x \<leadsto> u, y . u \<in> init \<and> x = y:] \<circ> {.p.} \<circ> [:u, x \<leadsto> y . r (u, x) y \<and> r' x y:])"
    by (cut_tac p' = "\<top>" and init = init and p = p and r = r and r' = r' in fusion_spec_local, auto)

  lemma fusion_local_refinement:
    "a \<in> init \<Longrightarrow> (\<And> x u y . u \<in> init \<Longrightarrow> p' x \<Longrightarrow> r (u, x) y \<Longrightarrow> r' x y) \<Longrightarrow> 
      {.p'.} o (([:x \<leadsto> u, y . u \<in> init \<and> x = y:] \<circ> {.p.} \<circ> [:r:]) \<parallel> [:r':]) \<le> [:x \<leadsto> u, y . u \<in> init \<and> x = y:] \<circ> {.p.} \<circ> [:r:]"
    proof -
     assume A: "a \<in> init"
     assume [simp]: "(\<And> x u y . u \<in> init \<Longrightarrow> p' x \<Longrightarrow> r (u, x) y \<Longrightarrow> r' x y)"
     have " {. x. p' x \<and> (\<forall>a. a \<in> init \<longrightarrow> p (a, x)) .} \<circ> [: (\<lambda>x (u, y). u \<in> init \<and> x = y) OO (\<lambda>(u, x) y. r (u, x) y \<and> r' x y) :]
              \<le> {. \<lambda>x. \<forall>a. a \<in> init \<longrightarrow> p (a, x) .} \<circ> [: (\<lambda>x (u, y). u \<in> init \<and> x = y) OO r :]"
      by (auto simp add: assert_demonic_refinement)
    from this have " {. x. p' x \<and> (\<forall>a. a \<in> init \<longrightarrow> p (a, x)) .} \<circ> [: (\<lambda>x (u, y). u \<in> init \<and> x = y) OO (\<lambda>(u, x) y. r (u, x) y \<and> r' x y) :]
            \<le> {. \<lambda>x. \<forall>a. a \<in> init \<longrightarrow> p (a, x) .} \<circ> [: \<lambda>x (u, y). u \<in> init \<and> x = y :] \<circ> [: r :]"
      by (simp add: comp_assoc demonic_demonic)
    from this have "{. p' .} \<circ> [: \<lambda>x (u, y). u \<in> init \<and> x = y :] \<circ> {. p .} \<circ> [: \<lambda>(u, x) y. r (u, x) y \<and> r' x y :] 
            \<le> [: x \<leadsto> u, y. u \<in> init \<and> x = y :] \<circ> {. p .} \<circ> [: r :]"
      by (simp add: demonic_assert_comp assert_demonic_comp)
    from this have "{. p' .} \<circ> ([: x \<leadsto> (u, y) . u \<in> init \<and> x = y :] \<circ> {. p .} \<circ> [: (u, x) \<leadsto> y . r (u, x) y \<and> r' x y :]) 
          \<le> [: x \<leadsto> (u, y) . u \<in> init \<and> x = y :] \<circ> {. p .} \<circ> [: r :]"
      by (simp add: comp_assoc [THEN sym])
    from A and this show ?thesis 
      by  (unfold fusion_spec_local_a, simp)
  qed
end
