(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Idiomatic terms -- Properties and operations\<close>

theory Idiomatic_Terms
imports Combinators
begin

text \<open>This theory proves the correctness of the normalisation algorithm for
  arbitrary applicative functors. We generalise the normal form using a framework
  for bracket abstraction algorithms. Both approaches justify lifting certain
  classes of equations. We model this as implications of term equivalences,
  where unlifting of idiomatic terms is expressed syntactically.\<close>

subsubsection \<open>Basic definitions\<close>

datatype 'a itrm =
    Opaque 'a | Pure dB
  | IAp "'a itrm" "'a itrm" (infixl "\<diamondop>" 150)

primrec opaque :: "'a itrm \<Rightarrow> 'a list"
where
    "opaque (Opaque x) = [x]"
  | "opaque (Pure _) = []"
  | "opaque (f \<diamondop> x) = opaque f @ opaque x"

abbreviation "iorder x \<equiv> length (opaque x)"

inductive itrm_cong :: "('a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool) \<Rightarrow> 'a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool"
for R
where
    into_itrm_cong: "R x y \<Longrightarrow> itrm_cong R x y"
  | pure_cong[intro]: "x \<leftrightarrow> y \<Longrightarrow> itrm_cong R (Pure x) (Pure y)"
  | ap_cong: "itrm_cong R f f' \<Longrightarrow> itrm_cong R x x' \<Longrightarrow> itrm_cong R (f \<diamondop> x) (f' \<diamondop> x')"
  | itrm_refl[iff]: "itrm_cong R x x"
  | itrm_sym[sym]: "itrm_cong R x y \<Longrightarrow> itrm_cong R y x"
  | itrm_trans[trans]: "itrm_cong R x y \<Longrightarrow> itrm_cong R y z \<Longrightarrow> itrm_cong R x z"

lemma ap_congL[intro]: "itrm_cong R f f' \<Longrightarrow> itrm_cong R (f \<diamondop> x) (f' \<diamondop> x)"
by (blast intro: ap_cong)

lemma ap_congR[intro]: "itrm_cong R x x' \<Longrightarrow> itrm_cong R (f \<diamondop> x) (f \<diamondop> x')"
by (blast intro: ap_cong)

text \<open>Idiomatic terms are \emph{similar} iff they have the same structure, and all contained
  lambda terms are equivalent.\<close>

abbreviation similar :: "'a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool" (infixl "\<cong>" 50)
where "x \<cong> y \<equiv> itrm_cong (\<lambda>_ _. False) x y"

lemma pure_similarE:
  assumes "Pure x' \<cong> y"
  obtains y' where "y = Pure y'" and "x' \<leftrightarrow> y'"
proof -
  define x :: "'a itrm" where "x = Pure x'"
  from assms have "x \<cong> y" unfolding x_def .
  then have "(\<forall>x''. x = Pure x'' \<longrightarrow> (\<exists>y'. y = Pure y' \<and> x'' \<leftrightarrow> y')) \<and>
    (\<forall>x''. y = Pure x'' \<longrightarrow> (\<exists>y'. x = Pure y' \<and> x'' \<leftrightarrow> y'))"
  proof (induction)
    case pure_cong thus ?case by (auto intro: term_sym)
  next
    case itrm_trans thus ?case by (fastforce intro: term_trans)
  qed simp_all
  with that show thesis unfolding x_def by blast
qed

lemma opaque_similarE:
  assumes "Opaque x' \<cong> y"
  obtains y' where "y = Opaque y'" and "x' = y'"
proof -
  define x :: "'a itrm" where "x = Opaque x'"
  from assms have "x \<cong> y" unfolding x_def .
  then have "(\<forall>x''. x = Opaque x'' \<longrightarrow> (\<exists>y'. y = Opaque y' \<and> x'' = y')) \<and>
    (\<forall>x''. y = Opaque x'' \<longrightarrow> (\<exists>y'. x = Opaque y' \<and> x'' = y'))"
  by induction fast+
  with that show thesis unfolding x_def by blast
qed

lemma ap_similarE:
  assumes "x1 \<diamondop> x2 \<cong> y"
  obtains y1 y2 where "y = y1 \<diamondop> y2" and "x1 \<cong> y1" and "x2 \<cong> y2"
proof -
  from assms
  have "(\<forall>x1' x2'. x1 \<diamondop> x2 = x1' \<diamondop> x2' \<longrightarrow> (\<exists>y1 y2. y = y1 \<diamondop> y2 \<and> x1' \<cong> y1 \<and> x2' \<cong> y2)) \<and>
    (\<forall>x1' x2'. y = x1' \<diamondop> x2' \<longrightarrow> (\<exists>y1 y2. x1 \<diamondop> x2 = y1 \<diamondop> y2 \<and> x1' \<cong> y1 \<and> x2' \<cong> y2))"
  proof (induction)
    case ap_cong thus ?case by (blast intro: itrm_sym)
  next
    case trans: itrm_trans thus ?case by (fastforce intro: itrm_trans)
  qed simp_all
  with that show thesis by blast
qed

text \<open>The following relations define semantic equivalence of idiomatic terms.
  We consider equivalences that hold universally in all idioms, as well as arbitrary
  specialisations using additional laws.\<close>

inductive idiom_rule :: "'a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool"
where
    idiom_id: "idiom_rule (Pure \<I> \<diamondop> x) x"
  | idiom_comp: "idiom_rule (Pure \<B> \<diamondop> g \<diamondop> f \<diamondop> x) (g \<diamondop> (f \<diamondop> x))"
  | idiom_hom: "idiom_rule (Pure f \<diamondop> Pure x) (Pure (f \<degree> x))"
  | idiom_xchng: "idiom_rule (f \<diamondop> Pure x) (Pure (\<T> \<degree> x) \<diamondop> f)"

abbreviation itrm_equiv :: "'a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool" (infixl "\<simeq>" 50)
where "x \<simeq> y \<equiv> itrm_cong idiom_rule x y"

lemma idiom_rule_into_equiv: "idiom_rule x y \<Longrightarrow> x \<simeq> y" ..

lemmas itrm_id = idiom_id[THEN idiom_rule_into_equiv]
lemmas itrm_comp = idiom_comp[THEN idiom_rule_into_equiv]
lemmas itrm_hom = idiom_hom[THEN idiom_rule_into_equiv]
lemmas itrm_xchng = idiom_xchng[THEN idiom_rule_into_equiv]

lemma similar_into_equiv: "x \<cong> y \<Longrightarrow> x \<simeq> y"
by (induction pred: itrm_cong) (auto intro: ap_cong itrm_sym itrm_trans)

lemma opaque_equiv: "x \<simeq> y \<Longrightarrow> opaque x = opaque y"
proof (induction pred: itrm_cong)
  case (into_itrm_cong x y)
  thus ?case by induction auto
qed simp_all

lemma iorder_equiv: "x \<simeq> y \<Longrightarrow> iorder x = iorder y"
by (auto dest: opaque_equiv)

locale special_idiom =
  fixes extra_rule :: "'a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool"
begin

definition "idiom_ext_rule = sup idiom_rule extra_rule"

abbreviation itrm_ext_equiv :: "'a itrm \<Rightarrow> 'a itrm \<Rightarrow> bool" (infixl "\<simeq>\<^sup>+" 50)
where "x \<simeq>\<^sup>+ y \<equiv> itrm_cong idiom_ext_rule x y"

lemma equiv_into_ext_equiv: "x \<simeq> y \<Longrightarrow> x \<simeq>\<^sup>+ y"
unfolding idiom_ext_rule_def
by (induction pred: itrm_cong)
   (auto intro: into_itrm_cong ap_cong itrm_sym itrm_trans)

lemmas itrm_ext_id = itrm_id[THEN equiv_into_ext_equiv]
lemmas itrm_ext_comp = itrm_comp[THEN equiv_into_ext_equiv]
lemmas itrm_ext_hom = itrm_hom[THEN equiv_into_ext_equiv]
lemmas itrm_ext_xchng = itrm_xchng[THEN equiv_into_ext_equiv]

end


subsubsection \<open>Syntactic unlifting\<close>

paragraph \<open>With generalisation of variables\<close>

primrec unlift' :: "nat \<Rightarrow> 'a itrm \<Rightarrow> nat \<Rightarrow> dB"
where
    "unlift' n (Opaque _) i = Var i"
  | "unlift' n (Pure x) i = liftn n x 0"
  | "unlift' n (f \<diamondop> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i"

abbreviation "unlift x \<equiv> (Abs^^iorder x) (unlift' (iorder x) x 0)"

lemma funpow_Suc_inside: "(f ^^ Suc n) x = (f ^^ n) (f x)"
using funpow_Suc_right unfolding comp_def by metis

lemma absn_cong[intro]: "s \<leftrightarrow> t \<Longrightarrow> (Abs^^n) s \<leftrightarrow> (Abs^^n) t"
by (induction n) auto

lemma free_unlift: "free (unlift' n x i) j \<Longrightarrow> j \<ge> n \<or> (j \<ge> i \<and> j < i + iorder x)"
proof (induction x arbitrary: i)
  case (Opaque x)
  thus ?case by simp
next
  case (Pure x)
  thus ?case using free_liftn by simp
next
  case (IAp x y)
  thus ?case by fastforce
qed

lemma unlift_subst: "j \<le> i \<and> j \<le> n \<Longrightarrow> (unlift' (Suc n) t (Suc i))[s/j] = unlift' n t i"
proof (induction t arbitrary: i)
  case (Opaque x)
  thus ?case by simp
next
  case (Pure x)
  thus ?case using subst_liftn by simp
next
  case (IAp x y)
  hence "j \<le> i + iorder y" by simp
  with IAp show ?case by auto
qed

lemma unlift'_equiv: "x \<simeq> y \<Longrightarrow> unlift' n x i \<leftrightarrow> unlift' n y i"
proof (induction arbitrary: n i pred: itrm_cong)
  case (into_itrm_cong x y) thus ?case
  proof induction
    case (idiom_id x)
    show ?case using I_equiv[symmetric] by simp
  next
    case (idiom_comp g f x)
    let ?G = "unlift' n g (i + iorder f + iorder x)"
    let ?F = "unlift' n f (i + iorder x)"
    let ?X = "unlift' n x i"
    have "unlift' n (g \<diamondop> (f \<diamondop> x)) i = ?G \<degree> (?F \<degree> ?X)"
      by (simp add: add.assoc)
    moreover have "unlift' n (Pure \<B> \<diamondop> g \<diamondop> f \<diamondop> x) i = \<B> \<degree> ?G \<degree> ?F \<degree> ?X"
      by (simp add: add.commute add.left_commute)
    moreover have "?G \<degree> (?F \<degree> ?X) \<leftrightarrow> \<B> \<degree> ?G \<degree> ?F \<degree> ?X" using B_equiv[symmetric] .
    ultimately show ?case by simp
  next
    case (idiom_hom f x)
    show ?case by auto
  next
    case (idiom_xchng f x)
    let ?F = "unlift' n f i"
    let ?X = "liftn n x 0"
    have "unlift' n (f \<diamondop> Pure x) i = ?F \<degree> ?X" by simp
    moreover have "unlift' n (Pure (\<T> \<degree> x) \<diamondop> f) i = \<T> \<degree> ?X \<degree> ?F" by simp
    moreover have "?F \<degree> ?X \<leftrightarrow> \<T> \<degree> ?X \<degree> ?F" using T_equiv[symmetric] .
    ultimately show ?case by simp
  qed
next
  case pure_cong
  thus ?case by (auto intro: equiv_liftn)
next
  case (ap_cong f f' x x')
  from \<open>x \<simeq> x'\<close> have iorder_eq: "iorder x = iorder x'" by (rule iorder_equiv)
  have "unlift' n (f \<diamondop> x) i = unlift' n f (i + iorder x) \<degree> unlift' n x i" by simp
  moreover have "unlift' n (f' \<diamondop> x') i = unlift' n f' (i + iorder x) \<degree> unlift' n x' i"
    using iorder_eq by simp
  ultimately show ?case using ap_cong.IH by (auto intro: equiv_app)
next
  case itrm_refl
  thus ?case by simp
next
  case itrm_sym
  thus ?case using term_sym by simp
next
  case itrm_trans
  thus ?case using term_trans by blast
qed

lemma unlift_equiv: "x \<simeq> y \<Longrightarrow> unlift x \<leftrightarrow> unlift y"
proof -
  assume "x \<simeq> y"
  then have "unlift' (iorder y) x 0 \<leftrightarrow> unlift' (iorder y) y 0" by (rule unlift'_equiv)
  moreover from \<open>x \<simeq> y\<close> have "iorder x = iorder y" by (rule iorder_equiv)
  ultimately show ?thesis by auto
qed


paragraph \<open>Preserving variables\<close>

primrec unlift_vars :: "nat \<Rightarrow> nat itrm \<Rightarrow> dB"
where
    "unlift_vars n (Opaque i) = Var i"
  | "unlift_vars n (Pure x) = liftn n x 0"
  | "unlift_vars n (x \<diamondop> y) = unlift_vars n x \<degree> unlift_vars n y"

lemma all_pure_unlift_vars: "opaque x = [] \<Longrightarrow> x \<simeq> Pure (unlift_vars 0 x)"
proof (induction x)
  case (Opaque x) then show ?case by simp
next
  case (Pure x) then show ?case by simp
next
  case (IAp x y)
  then have no_opaque: "opaque x = []" "opaque y = []" by simp+
  then have unlift_ap: "unlift_vars 0 (x \<diamondop> y) = unlift_vars 0 x \<degree> unlift_vars 0 y"
    by simp
  from no_opaque IAp.IH have "x \<diamondop> y \<simeq> Pure (unlift_vars 0 x) \<diamondop> Pure (unlift_vars 0 y)"
    by (blast intro: ap_cong)
  also have "... \<simeq> Pure (unlift_vars 0 x \<degree> unlift_vars 0 y)" by (rule itrm_hom)
  also have "... = Pure (unlift_vars 0 (x \<diamondop> y))" by (simp only: unlift_ap)
  finally show ?case .
qed


subsubsection \<open>Canonical forms\<close>

inductive_set CF :: "'a itrm set"
where
    pure_cf[iff]: "Pure x \<in> CF"
  | ap_cf[intro]: "f \<in> CF \<Longrightarrow> f \<diamondop> Opaque x \<in> CF"

primrec CF_pure :: "'a itrm \<Rightarrow> dB"
where
    "CF_pure (Opaque _) = undefined"
  | "CF_pure (Pure x) = x"
  | "CF_pure (x \<diamondop> _) = CF_pure x"

lemma ap_cfD1[dest]: "f \<diamondop> x \<in> CF \<Longrightarrow> f \<in> CF"
by (rule CF.cases) auto

lemma ap_cfD2[dest]: "f \<diamondop> x \<in> CF \<Longrightarrow> \<exists>x'. x = Opaque x'"
by (rule CF.cases) auto

lemma opaque_not_cf[simp]: "Opaque x \<in> CF \<Longrightarrow> False"
by (rule CF.cases) auto

lemma cf_unlift:
  assumes "x \<in> CF"
    shows "CF_pure x \<leftrightarrow> unlift x"
using assms proof (induction set: CF)
  case (pure_cf x)
  show ?case by simp
next
  case (ap_cf f x)
  let ?n = "iorder f + 1"
  have "unlift (f \<diamondop> Opaque x) = (Abs^^?n) (unlift' ?n f 1 \<degree> Var 0)"
    by simp
  also have "... = (Abs^^iorder f) (Abs (unlift' ?n f 1 \<degree> Var 0))"
    using funpow_Suc_inside by simp
  also have "... \<leftrightarrow> unlift f" proof -
    have "\<not> free (unlift' ?n f 1) 0" using free_unlift by fastforce
    hence "Abs (unlift' ?n f 1 \<degree> Var 0) \<rightarrow>\<^sub>\<eta> (unlift' ?n f 1)[Var 0/0]" ..
    also have "... = unlift' (iorder f) f 0"
      using unlift_subst by (metis One_nat_def Suc_eq_plus1 le0)
    finally show ?thesis
      by (simp add: r_into_rtranclp absn_cong eta_into_equiv)
  qed
  finally show ?case
    using ap_cf.IH by (auto intro: term_sym term_trans)
qed

lemma cf_similarI:
  assumes "x \<in> CF" "y \<in> CF"
      and "opaque x = opaque y"
      and "CF_pure x \<leftrightarrow> CF_pure y"
    shows "x \<cong> y"
using assms proof (induction arbitrary: y)
  case (pure_cf x)
  hence "opaque y = []" by auto
  with \<open>y \<in> CF\<close> obtain y' where "y = Pure y'" by cases auto
  with pure_cf.prems show ?case by auto
next
  case (ap_cf f x)
  from \<open>opaque (f \<diamondop> Opaque x) = opaque y\<close>
  obtain y1 y2 where "opaque y = y1 @ y2"
    and "opaque f = y1" and "[x] = y2" by fastforce
  from \<open>[x] = y2\<close> obtain y' where "y2 = [y']" and "x = y'"
    by auto
  with \<open>y \<in> CF\<close> and \<open>opaque y = y1 @ y2\<close> obtain g
    where "opaque g = y1" and y_split: "y = g \<diamondop> Opaque y'" "g \<in> CF" by cases auto
  with ap_cf.prems \<open>opaque f = y1\<close>
  have "opaque f = opaque g" "CF_pure f \<leftrightarrow> CF_pure g" by auto
  with ap_cf.IH \<open>g \<in> CF\<close> have "f \<cong> g" by simp
  with ap_cf.prems y_split \<open>x = y'\<close> show ?case by (auto intro: ap_cong)
qed

lemma cf_similarD:
  assumes in_cf: "x \<in> CF" "y \<in> CF"
      and similar: "x \<cong> y"
    shows "CF_pure x \<leftrightarrow> CF_pure y \<and> opaque x = opaque y"
using assms
by (blast intro!: similar_into_equiv opaque_equiv cf_unlift unlift_equiv
      intro: term_trans term_sym)

text \<open>Equivalent idiomatic terms in canonical form are similar. This justifies speaking of a
  normal form.\<close>

lemma cf_unique:
  assumes in_cf: "x \<in> CF" "y \<in> CF"
      and equiv: "x \<simeq> y"
    shows "x \<cong> y"
using in_cf proof (rule cf_similarI)
  from equiv show "opaque x = opaque y" by (rule opaque_equiv)
next
  from equiv have "unlift x \<leftrightarrow> unlift y" by (rule unlift_equiv)
  thus "CF_pure x \<leftrightarrow> CF_pure y"
    using cf_unlift[OF in_cf(1)] cf_unlift[OF in_cf(2)]
    by (auto intro: term_sym term_trans)
qed


subsubsection \<open>Normalisation of idiomatic terms\<close>

primrec norm_pn :: "dB \<Rightarrow> 'a itrm \<Rightarrow> 'a itrm"
where
    "norm_pn f (Opaque x) = undefined"
  | "norm_pn f (Pure x) = Pure (f \<degree> x)"
  | "norm_pn f (n \<diamondop> x) = norm_pn (\<B> \<degree> f) n \<diamondop> x"

primrec norm_nn :: "'a itrm \<Rightarrow> 'a itrm \<Rightarrow> 'a itrm"
where
    "norm_nn n (Opaque x) = undefined"
  | "norm_nn n (Pure x) = norm_pn (\<T> \<degree> x) n"
  | "norm_nn n (n' \<diamondop> x) = norm_nn (norm_pn \<B> n) n' \<diamondop> x"

primrec norm :: "'a itrm \<Rightarrow> 'a itrm"
where
    "norm (Opaque x) = Pure \<I> \<diamondop> Opaque x"
  | "norm (Pure x) = Pure x"
  | "norm (f \<diamondop> x) = norm_nn (norm f) (norm x)"


lemma norm_pn_in_cf:
  assumes "x \<in> CF"
    shows "norm_pn f x \<in> CF"
using assms
by (induction x arbitrary: f) auto

lemma norm_nn_in_cf:
  assumes "n \<in> CF" "n' \<in> CF"
    shows "norm_nn n n' \<in> CF"
using assms(2,1)
by (induction n' arbitrary: n) (auto intro: norm_pn_in_cf)

lemma norm_in_cf: "norm x \<in> CF"
by (induction x) (auto intro: norm_nn_in_cf)


lemma norm_pn_equiv:
  assumes "x \<in> CF"
    shows "norm_pn f x \<simeq> Pure f \<diamondop> x"
using assms proof (induction x arbitrary: f)
  case (pure_cf x)
  have "Pure (f \<degree> x) \<simeq> Pure f \<diamondop> Pure x" using itrm_hom[symmetric] .
  then show ?case by simp
next
  case (ap_cf n x)
  from ap_cf.IH have "norm_pn (\<B> \<degree> f) n \<simeq> Pure (\<B> \<degree> f) \<diamondop> n" .
  then have "norm_pn (\<B> \<degree> f) n \<diamondop> Opaque x \<simeq> Pure (\<B> \<degree> f) \<diamondop> n \<diamondop> Opaque x" ..
  also have "... \<simeq> Pure \<B> \<diamondop> Pure f \<diamondop> n \<diamondop> Opaque x"
    using itrm_hom[symmetric] by blast
  also have "... \<simeq> Pure f \<diamondop> (n \<diamondop> Opaque x)" using itrm_comp .
  finally show ?case by simp
qed

lemma norm_nn_equiv:
  assumes "n \<in> CF" "n' \<in> CF"
    shows "norm_nn n n' \<simeq> n \<diamondop> n'"
using assms(2,1) proof (induction n' arbitrary: n)
  case (pure_cf x)
  then have "norm_pn (\<T> \<degree> x) n \<simeq> Pure (\<T> \<degree> x) \<diamondop> n" by (rule norm_pn_equiv)
  also have "... \<simeq> n \<diamondop> Pure x" using itrm_xchng[symmetric] .
  finally show ?case by simp
next
  case (ap_cf n' x)
  have "norm_nn (norm_pn \<B> n) n' \<diamondop> Opaque x \<simeq> Pure \<B> \<diamondop> n \<diamondop> n' \<diamondop> Opaque x" proof
    from \<open>n \<in> CF\<close> have "norm_pn \<B> n \<in> CF" by (rule norm_pn_in_cf)
    with ap_cf.IH have "norm_nn (norm_pn \<B> n) n' \<simeq> norm_pn \<B> n \<diamondop> n'" .
    also have "... \<simeq> Pure \<B> \<diamondop> n \<diamondop> n'" using norm_pn_equiv \<open>n \<in> CF\<close> by blast
    finally show "norm_nn (norm_pn \<B> n) n' \<simeq> Pure \<B> \<diamondop> n \<diamondop> n'" .
  qed
  also have "... \<simeq> n \<diamondop> (n' \<diamondop> Opaque x)" using itrm_comp .
  finally show ?case by simp
qed

lemma norm_equiv: "norm x \<simeq> x"
proof (induction)
  case (Opaque x)
  have "Pure \<I> \<diamondop> Opaque x \<simeq> Opaque x" using itrm_id .
  then show ?case by simp
next
  case (Pure x)
  show ?case by simp
next
  case (IAp f x)
  have "norm f \<in> CF" and "norm x \<in> CF" by (rule norm_in_cf)+
  then have "norm_nn (norm f) (norm x) \<simeq> norm f \<diamondop> norm x"
    by (rule norm_nn_equiv)
  also have "... \<simeq> f \<diamondop> x" using IAp.IH ..
  finally show ?case by simp
qed

lemma normal_form: obtains n where "n \<simeq> x" and "n \<in> CF"
using norm_equiv norm_in_cf ..


subsubsection \<open>Lifting with normal forms\<close>

lemma nf_unlift:
  assumes equiv: "n \<simeq> x" and cf: "n \<in> CF"
    shows "CF_pure n \<leftrightarrow> unlift x"
proof -
  from cf have "CF_pure n \<leftrightarrow> unlift n" by (rule cf_unlift)
  also from equiv have "unlift n \<leftrightarrow> unlift x" by (rule unlift_equiv)
  finally show ?thesis .
qed

theorem nf_lifting:
  assumes opaque: "opaque x = opaque y"
      and base_eq: "unlift x \<leftrightarrow> unlift y"
    shows "x \<simeq> y"
proof -
  obtain n where nf_x: "n \<simeq> x" "n \<in> CF" by (rule normal_form)
  obtain n' where nf_y: "n' \<simeq> y" "n' \<in> CF" by (rule normal_form)

  from nf_x have "CF_pure n \<leftrightarrow> unlift x" by (rule nf_unlift)
  also note base_eq
  also from nf_y have "unlift y \<leftrightarrow> CF_pure n'" by (rule nf_unlift[THEN term_sym])
  finally have pure_eq: "CF_pure n \<leftrightarrow> CF_pure n'" .

  from nf_x(1) have "opaque n = opaque x" by (rule opaque_equiv)
  also note opaque
  also from nf_y(1) have "opaque y = opaque n'" by (rule opaque_equiv[THEN sym])
  finally have opaque_eq: "opaque n = opaque n'" .

  from nf_x(1) have "x \<simeq> n" ..
  also have "n \<simeq> n'"
    using nf_x nf_y pure_eq opaque_eq
    by (blast intro: similar_into_equiv cf_similarI)
  also from nf_y(1) have "n' \<simeq> y" .
  finally show "x \<simeq> y" .
qed


subsubsection \<open>Bracket abstraction, twice\<close>

paragraph \<open>Preliminaries: Sequential application of variables\<close>

definition frees :: "dB \<Rightarrow> nat set"
where [simp]: "frees t = {i. free t i}"

definition var_dist :: "nat list \<Rightarrow> dB \<Rightarrow> dB"
where "var_dist = fold (\<lambda>i t. t \<degree> Var i)"

lemma var_dist_Nil[simp]: "var_dist [] t = t"
unfolding var_dist_def by simp

lemma var_dist_Cons[simp]: "var_dist (v # vs) t = var_dist vs (t \<degree> Var v)"
unfolding var_dist_def by simp

lemma var_dist_append1: "var_dist (vs @ [v]) t = var_dist vs t \<degree> Var v"
unfolding var_dist_def by simp

lemma var_dist_frees: "frees (var_dist vs t) = frees t \<union> set vs"
by (induction vs arbitrary: t) auto

lemma var_dist_subst_lt:
  "\<forall>v\<in>set vs. i < v \<Longrightarrow> (var_dist vs s)[t/i] = var_dist (map (\<lambda>v. v - 1) vs) (s[t/i])"
by (induction vs arbitrary: s) simp_all

lemma var_dist_subst_gt:
  "\<forall>v\<in>set vs. v < i \<Longrightarrow> (var_dist vs s)[t/i] = var_dist vs (s[t/i])"
by (induction vs arbitrary: s) simp_all

definition vsubst :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where "vsubst u v w = (if u < w then u else if u = w then v else u - 1)"

lemma vsubst_subst[simp]: "(Var u)[Var v/w] = Var (vsubst u v w)"
unfolding vsubst_def by simp

lemma vsubst_subst_lt[simp]: "u < w \<Longrightarrow> vsubst u v w = u"
unfolding vsubst_def by simp

lemma var_dist_subst_Var:
  "(var_dist vs s)[Var i/j] = var_dist (map (\<lambda>v. vsubst v i j) vs) (s[Var i/j])"
by (induction vs arbitrary: s) simp_all

lemma var_dist_cong: "s \<leftrightarrow> t \<Longrightarrow> var_dist vs s \<leftrightarrow> var_dist vs t"
by (induction vs arbitrary: s t) auto


paragraph \<open>Preliminaries: Eta reductions with permuted variables\<close>

lemma absn_subst: "((Abs^^n) s)[t/k] = (Abs^^n) (s[liftn n t 0/k+n])"
by (induction n arbitrary: t k) (simp_all add: liftn_lift_swap)

lemma absn_beta_equiv: "(Abs^^Suc n) s \<degree> t \<leftrightarrow> (Abs^^n) (s[liftn n t 0/n])"
proof -
  have "(Abs^^Suc n) s \<degree> t = Abs ((Abs^^n) s) \<degree> t" by simp
  also have "... \<leftrightarrow> ((Abs^^n) s)[t/0]" by (rule beta_into_equiv) (rule beta.beta)
  also have "... = (Abs^^n) (s[liftn n t 0/n])" by (simp add: absn_subst)
  finally show ?thesis .
qed

lemma absn_dist_eta: "(Abs^^n) (var_dist (rev [0..<n]) (liftn n t 0)) \<leftrightarrow> t"
proof (induction n)
  case 0 show ?case by simp
next
  case (Suc n)
  let ?dist_range = "\<lambda>a k. var_dist (rev [a..<k]) (liftn k t 0)"
  have append: "rev [0..<Suc n] = rev [1..<Suc n] @ [0]" by (simp add: upt_rec)
  have dist_last: "?dist_range 0 (Suc n) = ?dist_range 1 (Suc n) \<degree> Var 0"
    unfolding append var_dist_append1 ..

  have "\<not> free (?dist_range 1 (Suc n)) 0" proof -
    have "frees (?dist_range 1 (Suc n)) = frees (liftn (Suc n) t 0) \<union> {1..n}"
      unfolding var_dist_frees by fastforce
    then have "0 \<notin> frees (?dist_range 1 (Suc n))" by simp
    then show ?thesis by simp
  qed
  then have "Abs (?dist_range 0 (Suc n)) \<rightarrow>\<^sub>\<eta> (?dist_range 1 (Suc n))[Var 0/0]"
    unfolding dist_last by (rule eta)
  also have "... = var_dist (rev [0..<n]) ((liftn (Suc n) t 0)[Var 0/0])" proof -
    have "\<forall>v\<in>set (rev [1..<Suc n]). 0 < v" by auto
    moreover have "rev [0..<n] = map (\<lambda>v. v - 1) (rev [1..<Suc n])" by (induction n) simp_all
    ultimately show ?thesis by (simp only: var_dist_subst_lt)
  qed
  also have "... = ?dist_range 0 n" using subst_liftn[of 0 n 0 t "Var 0"] by simp
  finally have "Abs (?dist_range 0 (Suc n)) \<leftrightarrow> ?dist_range 0 n" ..
  then have "(Abs^^Suc n) (?dist_range 0 (Suc n)) \<leftrightarrow> (Abs^^n) (?dist_range 0 n)"
    unfolding funpow_Suc_inside by (rule absn_cong)
  also from Suc.IH have "... \<leftrightarrow> t" .
  finally show ?case .
qed

primrec strip_context :: "nat \<Rightarrow> dB \<Rightarrow> nat \<Rightarrow> dB"
where
    "strip_context n (Var i) k = (if i < k then Var i else Var (i - n))"
  | "strip_context n (Abs t) k = Abs (strip_context n t (Suc k))"
  | "strip_context n (s \<degree> t) k = strip_context n s k \<degree> strip_context n t k"

lemma strip_context_liftn: "strip_context n (liftn (m + n) t k) k = liftn m t k"
by (induction t arbitrary: k) simp_all

lemma liftn_strip_context:
  assumes "\<forall>i\<in>frees t. i < k \<or> k + n \<le> i"
    shows "liftn n (strip_context n t k) k = t"
using assms proof (induction t arbitrary: k)
  case (Abs t)
  have "\<forall>i\<in>frees t. i < Suc k \<or> Suc k + n \<le> i" proof
    fix i assume free: "i \<in> frees t"
    show "i < Suc k \<or> Suc k + n \<le> i" proof (cases "i > 0")
      assume "i > 0"
      with free Abs.prems have "i-1 < k \<or> k + n \<le> i-1" by simp
      then show ?thesis by arith
    qed simp
  qed
  with Abs.IH show ?case by simp
qed auto

lemma absn_dist_eta_free:
  assumes "\<forall>i\<in>frees t. n \<le> i"
  shows "(Abs^^n) (var_dist (rev [0..<n]) t) \<leftrightarrow> strip_context n t 0" (is "?lhs t \<leftrightarrow> ?rhs")
proof -
  have "?lhs (liftn n ?rhs 0) \<leftrightarrow> ?rhs" by (rule absn_dist_eta)
  moreover have "liftn n ?rhs 0 = t"
    using assms by (auto intro: liftn_strip_context)
  ultimately show ?thesis by simp
qed

definition perm_vars :: "nat \<Rightarrow> nat list \<Rightarrow> bool"
where "perm_vars n vs \<longleftrightarrow> distinct vs \<and> set vs = {0..<n}"

lemma perm_vars_distinct: "perm_vars n vs \<Longrightarrow> distinct vs"
unfolding perm_vars_def by simp

lemma perm_vars_length: "perm_vars n vs \<Longrightarrow> length vs = n"
unfolding perm_vars_def using distinct_card by force

lemma perm_vars_lt: "perm_vars n vs \<Longrightarrow> \<forall>i\<in>set vs. i < n"
unfolding perm_vars_def by simp

lemma perm_vars_nth_lt: "perm_vars n vs \<Longrightarrow> i < n \<Longrightarrow> vs ! i < n"
using perm_vars_length perm_vars_lt by simp

lemma perm_vars_inj_on_nth:
  assumes "perm_vars n vs"
    shows "inj_on (nth vs) {0..<n}"
proof (rule inj_onI)
  fix i j
  assume "i \<in> {0..<n}" and "j \<in> {0..<n}"
  with assms have "i < length vs" and "j < length vs"
    using perm_vars_length by simp+
  moreover from assms have "distinct vs" by (rule perm_vars_distinct)
  moreover assume "vs ! i = vs ! j"
  ultimately show "i = j" using nth_eq_iff_index_eq by blast
qed

abbreviation perm_vars_inv :: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat"
where "perm_vars_inv n vs i \<equiv> the_inv_into {0..<n} ((!) vs) i"

lemma perm_vars_inv_nth:
  assumes "perm_vars n vs"
      and "i < n"
    shows "perm_vars_inv n vs (vs ! i) = i"
using assms by (auto intro: the_inv_into_f_f perm_vars_inj_on_nth)

lemma dist_perm_eta:
  assumes perm_vars: "perm_vars n vs"
  obtains vs' where "\<And>t. \<forall>i\<in>frees t. n \<le> i \<Longrightarrow>
    (Abs^^n) (var_dist vs' ((Abs^^n) (var_dist vs (liftn n t 0)))) \<leftrightarrow> strip_context n t 0"
proof -
  define vsubsts where "vsubsts n vs' vs =
    map (\<lambda>v.
      if v < n - length vs' then v
      else if v < n then vs' ! (n - v - 1) + (n - length vs')
      else v - length vs') vs" for n vs' vs

  let ?app_vars = "\<lambda>t n vs' vs. var_dist vs' ((Abs^^n) (var_dist vs (liftn n t 0)))"
  {
    fix t :: dB and vs' :: "nat list"
    assume partial: "length vs' \<le> n"

    let ?m = "n - length vs'"
    have "?app_vars t n vs' vs \<leftrightarrow> (Abs^^?m) (var_dist (vsubsts n vs' vs) (liftn ?m t 0))"
    using partial proof (induction vs' arbitrary: vs n)
      case Nil
      then have "vsubsts n [] vs = vs" unfolding vsubsts_def by (auto intro: map_idI)
      then show ?case by simp
    next
      case (Cons v vs')
      define n' where "n' = n - 1"
      have Suc_n': "Suc n' = n" unfolding n'_def using Cons.prems by simp
      have vs'_length: "length vs' \<le> n'" unfolding n'_def using Cons.prems by simp
      let ?m' = "n' - length vs'"
      have m'_conv: "?m' = n - length (v # vs')" unfolding n'_def by simp

      have "?app_vars t n (v # vs') vs = ?app_vars t (Suc n') (v # vs') vs"
        unfolding Suc_n' ..
      also have "... \<leftrightarrow> var_dist vs' ((Abs^^Suc n') (var_dist vs (liftn (Suc n') t 0)) \<degree> Var v)"
        unfolding var_dist_Cons ..
      also have "... \<leftrightarrow> ?app_vars t n' vs' (vsubsts n [v] vs)" proof (rule var_dist_cong)
        have "map (\<lambda>vv. vsubst vv (v + n') n') vs = vsubsts n [v] vs"
          unfolding Suc_n'[symmetric] vsubsts_def vsubst_def
          by (auto cong: if_cong)
        then have "(var_dist vs (liftn (Suc n') t 0))[liftn n' (Var v) 0/n']
                  = var_dist (vsubsts n [v] vs) (liftn n' t 0)"
          using var_dist_subst_Var subst_liftn by simp
        then show "(Abs^^Suc n') (var_dist vs (liftn (Suc n') t 0)) \<degree> Var v
                  \<leftrightarrow> (Abs^^n') (var_dist (vsubsts n [v] vs) (liftn n' t 0))"
          by (fastforce intro: absn_beta_equiv[THEN term_trans])
      qed
      also have "... \<leftrightarrow> (Abs^^?m') (var_dist (vsubsts n' vs' (vsubsts n [v] vs)) (liftn ?m' t 0))"
        using vs'_length Cons.IH by blast
      also have "... = (Abs^^?m') (var_dist (vsubsts n (v # vs') vs) (liftn ?m' t 0))"
      proof -
        have "vsubsts n' vs' (vsubsts (Suc n') [v] vs) = vsubsts (Suc n') (v # vs') vs"
          unfolding vsubsts_def
          using vs'_length [[linarith_split_limit=10]]
          by auto
        then show ?thesis unfolding Suc_n' by simp
      qed
      finally show ?case unfolding m'_conv .
    qed
  }
  note partial_appd = this

  define vs' where "vs' = map (\<lambda>i. n - perm_vars_inv n vs (n - i - 1) - 1) [0..<n]"

  from perm_vars have vs_length: "length vs = n" by (rule perm_vars_length)
  have vs'_length: "length vs' = n" unfolding vs'_def by simp

  have "map (\<lambda>v. vs' ! (n - v - 1)) vs = rev [0..<n]" proof -
    have "length vs = length (rev [0..<n])"
      unfolding vs_length by simp
    then have "list_all2 (\<lambda>v v'. vs' ! (n - v - 1) = v') vs (rev [0..<n])" proof
      fix i assume "i < length vs"
      then have "i < n" unfolding vs_length .
      then have "vs ! i < n" using perm_vars perm_vars_nth_lt by simp
      with \<open>i < n\<close> have "vs' ! (n - vs ! i - 1) = n - perm_vars_inv n vs (vs ! i) - 1"
        unfolding vs'_def by simp
      also from \<open>i < n\<close> have "... = n - i - 1" using perm_vars perm_vars_inv_nth by simp
      also from \<open>i < n\<close> have "... = rev [0..<n] ! i" by (simp add: rev_nth)
      finally show "vs' ! (n - vs ! i - 1) = rev [0..<n] ! i" .
    qed
    then show ?thesis
      unfolding list.rel_eq[symmetric]
      using list.rel_map
      by auto
  qed
  then have vs'_vs: "vsubsts n vs' vs = rev [0..<n]"
    unfolding vsubsts_def vs'_length
    using perm_vars perm_vars_lt
    by (auto intro: map_ext[THEN trans])

  let ?appd_vars = "\<lambda>t n. var_dist (rev [0..<n]) t"
  {
    fix t
    assume not_free: "\<forall>i\<in>frees t. n \<le> i"
    have "?app_vars t n vs' vs \<leftrightarrow> ?appd_vars t n" for t
      using partial_appd[of vs'] vs'_length vs'_vs by simp
    then have "(Abs^^n) (?app_vars t n vs' vs) \<leftrightarrow> (Abs^^n) (?appd_vars t n)"
      by (rule absn_cong)
    also have "... \<leftrightarrow> strip_context n t 0"
      using not_free by (rule absn_dist_eta_free)
    finally have "(Abs^^n) (?app_vars t n vs' vs) \<leftrightarrow> strip_context n t 0" .
  }
  with that show ?thesis .
qed

lemma liftn_absn: "liftn n ((Abs^^m) t) k = (Abs^^m) (liftn n t (k + m))"
by (induction m arbitrary: k) auto

lemma liftn_var_dist_lt:
  "\<forall>i\<in>set vs. i < k \<Longrightarrow> liftn n (var_dist vs t) k = var_dist vs (liftn n t k)"
by (induction vs arbitrary: t) auto

lemma liftn_context_conv: "k \<le> k' \<Longrightarrow> \<forall>i\<in>frees t. i < k \<or> k' \<le> i \<Longrightarrow> liftn n t k = liftn n t k'"
proof (induction t arbitrary: k k')
  case (Abs t)
  have "\<forall>i\<in>frees t. i < Suc k \<or> Suc k' \<le> i" proof
    fix i assume "i \<in> frees t"
    show "i < Suc k \<or> Suc k' \<le> i" proof (cases "i = 0")
      assume "i = 0" then show ?thesis by simp
    next
      assume "i \<noteq> 0"
      from Abs.prems(2) have "\<forall>i. free t (Suc i) \<longrightarrow> i < k \<or> k' \<le> i" by auto
      then have "\<forall>i. 0 < i \<and> free t i \<longrightarrow> i - 1 < k \<or> k' \<le> i - 1" by simp
      then have "\<forall>i. 0 < i \<and> free t i \<longrightarrow> i < Suc k \<or> Suc k' \<le> i" by auto
      with \<open>i \<noteq> 0\<close> \<open>i \<in> frees t\<close> show ?thesis by simp
    qed
  qed
  with Abs.IH Abs.prems(1) show ?case by auto
qed auto

lemma liftn_liftn0: "\<forall>i\<in>frees t. k \<le> i \<Longrightarrow> liftn n t k = liftn n t 0"
using liftn_context_conv by auto

lemma dist_perm_eta_equiv:
  assumes perm_vars: "perm_vars n vs"
      and not_free: "\<forall>i\<in>frees s. n \<le> i" "\<forall>i\<in>frees t. n \<le> i"
      and perm_equiv: "(Abs^^n) (var_dist vs s) \<leftrightarrow> (Abs^^n) (var_dist vs t)"
    shows "strip_context n s 0 \<leftrightarrow> strip_context n t 0"
proof -
  from perm_vars have vs_lt_n: "\<forall>i\<in>set vs. i < n" using perm_vars_lt by simp
  obtain vs' where
    etas: "\<And>t. \<forall>i\<in>frees t. n \<le> i \<Longrightarrow>
          (Abs^^n) (var_dist vs' ((Abs^^n) (var_dist vs (liftn n t 0)))) \<leftrightarrow> strip_context n t 0"
    using perm_vars dist_perm_eta by blast

  have "strip_context n s 0 \<leftrightarrow> (Abs^^n) (var_dist vs' ((Abs^^n) (var_dist vs (liftn n s 0))))"
    using etas[THEN term_sym] not_free(1) .
  also have "... \<leftrightarrow> (Abs^^n) (var_dist vs' ((Abs^^n) (var_dist vs (liftn n t 0))))"
  proof (rule absn_cong, rule var_dist_cong)
    have "(Abs^^n) (var_dist vs (liftn n s 0)) = (Abs^^n) (var_dist vs (liftn n s n))"
      using not_free(1) liftn_liftn0[of s n] by simp
    also have "... = (Abs^^n) (liftn n (var_dist vs s) n)"
      using vs_lt_n liftn_var_dist_lt by simp
    also have "... = liftn n ((Abs^^n) (var_dist vs s)) 0"
      using liftn_absn by simp
    also have "... \<leftrightarrow> liftn n ((Abs^^n) (var_dist vs t)) 0"
      using perm_equiv by (rule equiv_liftn)
    also have "... = (Abs^^n) (liftn n (var_dist vs t) n)"
      using liftn_absn by simp
    also have "... = (Abs^^n) (var_dist vs (liftn n t n))"
      using vs_lt_n liftn_var_dist_lt by simp
    also have "... = (Abs^^n) (var_dist vs (liftn n t 0))"
      using not_free(2) liftn_liftn0[of t n] by simp
    finally show "(Abs^^n) (var_dist vs (liftn n s 0)) \<leftrightarrow> ..." .
  qed
  also have "... \<leftrightarrow> strip_context n t 0"
    using etas not_free(2) .
  finally show ?thesis .
qed


paragraph \<open>General notion of bracket abstraction for lambda terms\<close>

definition foldr_option :: "('a \<Rightarrow> 'b \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b option"
where "foldr_option f xs e = foldr (\<lambda>a b. Option.bind b (f a)) xs (Some e)"

lemma bind_eq_SomeE:
  assumes "Option.bind x f = Some y"
  obtains x' where "x = Some x'" and "f x' = Some y"
using assms by (auto iff: bind_eq_Some_conv)

lemma foldr_option_Nil[simp]: "foldr_option f [] e = Some e"
unfolding foldr_option_def by simp

lemma foldr_option_Cons_SomeE:
  assumes "foldr_option f (x#xs) e = Some y"
  obtains y' where "foldr_option f xs e = Some y'" and "f x y' = Some y"
using assms unfolding foldr_option_def by (auto elim: bind_eq_SomeE)

locale bracket_abstraction =
  fixes term_bracket :: "nat \<Rightarrow> dB \<Rightarrow> dB option"
  assumes bracket_app: "term_bracket i s = Some s' \<Longrightarrow> s' \<degree> Var i \<leftrightarrow> s"
  assumes bracket_frees: "term_bracket i s = Some s' \<Longrightarrow> frees s' = frees s - {i}"
begin

definition term_brackets :: "nat list \<Rightarrow> dB \<Rightarrow> dB option"
where "term_brackets = foldr_option term_bracket"

lemma term_brackets_Nil[simp]: "term_brackets [] t = Some t"
unfolding term_brackets_def by simp

lemma term_brackets_Cons_SomeE:
  assumes "term_brackets (v#vs) t = Some t'"
  obtains s' where "term_brackets vs t = Some s'" and "term_bracket v s' = Some t'"
using assms unfolding term_brackets_def by (elim foldr_option_Cons_SomeE)

lemma term_brackets_ConsI:
  assumes "term_brackets vs t = Some t'"
      and "term_bracket v t' = Some t''"
    shows "term_brackets (v#vs) t = Some t''"
using assms unfolding term_brackets_def foldr_option_def by simp

lemma term_brackets_dist:
  assumes "term_brackets vs t = Some t'"
    shows "var_dist vs t' \<leftrightarrow> t"
proof -
  from assms have "\<forall>t''. t' \<leftrightarrow> t'' \<longrightarrow> var_dist vs t'' \<leftrightarrow> t"
  proof (induction vs arbitrary: t')
    case Nil then show ?case by (simp add: term_sym)
  next
    case (Cons v vs)
    from Cons.prems obtain u where
        inner: "term_brackets vs t = Some u" and
        step: "term_bracket v u = Some t'"
      by (auto elim: term_brackets_Cons_SomeE)
    from step have red1: "t' \<degree> Var v \<leftrightarrow> u" by (rule bracket_app)
    show ?case proof rule+
      fix t'' assume "t' \<leftrightarrow> t''"
      with red1 have red: "t'' \<degree> Var v \<leftrightarrow> u"
        using term_sym term_trans by blast
      have "var_dist (v # vs) t'' = var_dist vs (t'' \<degree> Var v)" by simp
      also have "... \<leftrightarrow> t" using Cons.IH[OF inner] red[symmetric] by blast
      finally show "var_dist (v # vs) t'' \<leftrightarrow> t" .
    qed
  qed
  then show ?thesis by blast
qed

end (* locale bracket_abstraction *)


paragraph \<open>Bracket abstraction for idiomatic terms\<close>

text \<open>We consider idiomatic terms with explicitly assigned variables.\<close>

lemma strip_unlift_vars:
  assumes "opaque x = []"
  shows "strip_context n (unlift_vars n x) 0 = unlift_vars 0 x"
using assms by (induction x) (simp_all add: strip_context_liftn[where m=0, simplified])

lemma unlift_vars_frees: "\<forall>i\<in>frees (unlift_vars n x). i \<in> set (opaque x) \<or> n \<le> i"
by (induction x) (auto simp add: free_liftn)

locale itrm_abstraction = special_idiom extra_rule for extra_rule :: "nat itrm \<Rightarrow> _" +
  fixes itrm_bracket :: "nat \<Rightarrow> nat itrm \<Rightarrow> nat itrm option"
  assumes itrm_bracket_ap: "itrm_bracket i x = Some x' \<Longrightarrow> x' \<diamondop> Opaque i \<simeq>\<^sup>+ x"
  assumes itrm_bracket_opaque:
    "itrm_bracket i x = Some x' \<Longrightarrow> set (opaque x') = set (opaque x) - {i}"
begin

definition "itrm_brackets = foldr_option itrm_bracket"

lemma itrm_brackets_Nil[simp]: "itrm_brackets [] x = Some x"
unfolding itrm_brackets_def by simp

lemma itrm_brackets_Cons_SomeE:
  assumes "itrm_brackets (v#vs) x = Some x'"
  obtains y' where "itrm_brackets vs x = Some y'" and "itrm_bracket v y' = Some x'"
using assms unfolding itrm_brackets_def by (elim foldr_option_Cons_SomeE)

definition "opaque_dist = fold (\<lambda>i y. y \<diamondop> Opaque i)"

lemma opaque_dist_cong: "x \<simeq>\<^sup>+ y \<Longrightarrow> opaque_dist vs x \<simeq>\<^sup>+ opaque_dist vs y"
unfolding opaque_dist_def
by (induction vs arbitrary: x y) (simp_all add: ap_congL)

lemma itrm_brackets_dist:
  assumes defined: "itrm_brackets vs x = Some x'"
    shows "opaque_dist vs x' \<simeq>\<^sup>+ x"
proof -
  define x'' where "x'' = x'"
  have "x' \<simeq>\<^sup>+ x''" unfolding x''_def ..
  with defined show "opaque_dist vs x'' \<simeq>\<^sup>+ x"
    unfolding opaque_dist_def
    proof (induction vs arbitrary: x' x'')
      case Nil then show ?case unfolding itrm_brackets_def by (simp add: itrm_sym)
    next
      case (Cons v vs)
      from Cons.prems(1) obtain y'
        where defined': "itrm_brackets vs x = Some y'"
          and "itrm_bracket v y' = Some x'"
        by (rule itrm_brackets_Cons_SomeE)
      then have "x' \<diamondop> Opaque v \<simeq>\<^sup>+ y'" by (elim itrm_bracket_ap)
      then have "x'' \<diamondop> Opaque v \<simeq>\<^sup>+ y'"
        using Cons.prems(2) by (blast intro: itrm_sym itrm_trans)
      note this[symmetric]
      with defined' have "fold (\<lambda>i y. y \<diamondop> Opaque i) vs (x'' \<diamondop> Opaque v) \<simeq>\<^sup>+ x"
        using Cons.IH by blast
      then show ?case by simp
    qed
qed

lemma itrm_brackets_opaque:
  assumes "itrm_brackets vs x = Some x'"
    shows "set (opaque x') = set (opaque x) - set vs"
using assms proof (induction vs arbitrary: x')
  case Nil
  then show ?case unfolding itrm_brackets_def by simp
next
  case (Cons v vs)
  then show ?case
    by (auto elim: itrm_brackets_Cons_SomeE dest!: itrm_bracket_opaque)
qed

lemma itrm_brackets_all:
  assumes all_opaque: "set (opaque x) \<subseteq> set vs"
      and defined: "itrm_brackets vs x = Some x'"
    shows "opaque x' = []"
proof -
  from defined have "set (opaque x') = set (opaque x) - set vs"
    by (rule itrm_brackets_opaque)
  with all_opaque have "set (opaque x') = {}" by simp
  then show ?thesis by simp
qed

lemma itrm_brackets_all_unlift_vars:
  assumes all_opaque: "set (opaque x) \<subseteq> set vs"
      and defined: "itrm_brackets vs x = Some x'"
    shows "x' \<simeq>\<^sup>+ Pure (unlift_vars 0 x')"
proof (rule equiv_into_ext_equiv)
  from assms have "opaque x' = []" by (rule itrm_brackets_all)
  then show "x' \<simeq> Pure (unlift_vars 0 x')" by (rule all_pure_unlift_vars)
qed

end (* locale itrm_abstraction *)


subsubsection \<open>Lifting with bracket abstraction\<close>

locale lifted_bracket = bracket_abstraction + itrm_abstraction +
  assumes bracket_compat:
    "set (opaque x) \<subseteq> {0..<n} \<Longrightarrow> i < n \<Longrightarrow>
      term_bracket i (unlift_vars n x) = map_option (unlift_vars n) (itrm_bracket i x)"
begin

lemma brackets_unlift_vars_swap:
  assumes all_opaque: "set (opaque x) \<subseteq> {0..<n}"
      and vs_bound: "set vs \<subseteq> {0..<n}"
      and defined: "itrm_brackets vs x = Some x'"
    shows "term_brackets vs (unlift_vars n x) = Some (unlift_vars n x')"
using vs_bound defined proof (induction vs arbitrary: x')
  case Nil
  then show ?case by simp
next
  case (Cons v vs)
  then obtain y'
    where ivs: "itrm_brackets vs x = Some y'"
      and iv: "itrm_bracket v y' = Some x'"
    by (elim itrm_brackets_Cons_SomeE)
  with Cons have "term_brackets vs (unlift_vars n x) = Some (unlift_vars n y')"
    by auto
  moreover {
    have "Some (unlift_vars n x') = map_option (unlift_vars n) (itrm_bracket v y')"
      unfolding iv by simp
    moreover have "set (opaque y') \<subseteq> {0..<n}"
      using all_opaque ivs by (auto dest: itrm_brackets_opaque)
    moreover have "v < n" using Cons.prems by simp
    ultimately have "term_bracket v (unlift_vars n y') = Some (unlift_vars n x')"
      using bracket_compat by auto
  }
  ultimately show ?case by (rule term_brackets_ConsI)
qed

theorem bracket_lifting:
  assumes all_vars: "set (opaque x) \<union> set (opaque y) \<subseteq> {0..<n}"
      and perm_vars: "perm_vars n vs"
      and defined: "itrm_brackets vs x = Some x'" "itrm_brackets vs y = Some y'"
      and base_eq: "(Abs^^n) (unlift_vars n x) \<leftrightarrow> (Abs^^n) (unlift_vars n y)"
    shows "x \<simeq>\<^sup>+ y"
proof -
  from perm_vars have set_vs: "set vs = {0..<n}"
    unfolding perm_vars_def by simp

  have x_swap: "term_brackets vs (unlift_vars n x) = Some (unlift_vars n x')"
    using all_vars set_vs defined(1) by (auto intro: brackets_unlift_vars_swap)
  have y_swap: "term_brackets vs (unlift_vars n y) = Some (unlift_vars n y')"
    using all_vars set_vs defined(2) by (auto intro: brackets_unlift_vars_swap)

  from all_vars have "set (opaque x) \<subseteq> set vs" unfolding set_vs by simp
  then have complete_x: "opaque x' = []"
    using defined(1) itrm_brackets_all by blast
  then have ux_frees: "\<forall>i\<in>frees (unlift_vars n x'). n \<le> i"
    using unlift_vars_frees by fastforce

  from all_vars have "set (opaque y) \<subseteq> set vs" unfolding set_vs by simp
  then have complete_y: "opaque y' = []"
    using defined(2) itrm_brackets_all by blast
  then have uy_frees: "\<forall>i\<in>frees (unlift_vars n y'). n \<le> i"
    using unlift_vars_frees by fastforce

  have "x \<simeq>\<^sup>+ opaque_dist vs x'"
    using defined(1) by (rule itrm_brackets_dist[symmetric])
  also have "... \<simeq>\<^sup>+ opaque_dist vs (Pure (unlift_vars 0 x'))"
    using all_vars set_vs defined(1)
    by (auto intro: opaque_dist_cong itrm_brackets_all_unlift_vars)
  also have "... \<simeq>\<^sup>+ opaque_dist vs (Pure (unlift_vars 0 y'))"
  proof (rule opaque_dist_cong, rule pure_cong)
    have "(Abs^^n) (var_dist vs (unlift_vars n x')) \<leftrightarrow> (Abs^^n) (unlift_vars n x)"
      using x_swap term_brackets_dist by auto
    also have "... \<leftrightarrow> (Abs^^n) (unlift_vars n y)" using base_eq .
    also have "... \<leftrightarrow> (Abs^^n) (var_dist vs (unlift_vars n y'))"
      using y_swap term_brackets_dist[THEN term_sym] by auto
    finally have "strip_context n (unlift_vars n x') 0 \<leftrightarrow> strip_context n (unlift_vars n y') 0"
      using perm_vars ux_frees uy_frees
      by (intro dist_perm_eta_equiv)
    then show "unlift_vars 0 x' \<leftrightarrow> unlift_vars 0 y'"
      using strip_unlift_vars complete_x complete_y by simp
  qed
  also have "... \<simeq>\<^sup>+ opaque_dist vs y'" proof (rule opaque_dist_cong)
    show "Pure (unlift_vars 0 y') \<simeq>\<^sup>+ y'"
      using all_vars set_vs defined(2) itrm_brackets_all_unlift_vars[THEN itrm_sym]
      by blast
  qed
  also have "... \<simeq>\<^sup>+ y" using defined(2) by (rule itrm_brackets_dist)
  finally show ?thesis .
qed

end (* locale lifted_bracket *)

end
