(*
  File:   Landau_Real_Products.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  Mathematical background and reification for a decision procedure for Landau symbols of
  products of powers of real functions (currently the identity and the natural logarithm)

  TODO: more functions (exp?), more preprocessing (log)
*)
section {* Decision procedure for real functions *}

theory Landau_Real_Products
imports
  Main Group_Sort Landau_Symbols_Definition "HOL-Library.Function_Algebras"
begin

text {*
  If there are two functions @{term "f"} and @{term "g"} where any power of @{term "g"} is
  asymptotically smaller than @{term "f"}, propositions like @{term "(\<lambda>x. f x ^ p1 * g x ^ q1) \<in>
  O(\<lambda>x. f x ^ p2 * g x ^ q2)"} can be decided just by looking at the exponents:
  the proposition is true iff @{term "p1 < p2"} or @{term "p1 = p2 \<and> q1 \<le> q2"}.

  The functions @{term "\<lambda>x. x"}, @{term "\<lambda>x. ln x"}, @{term "\<lambda>x. ln (ln x)"}, $\ldots$
  form a chain in which every function dominates all succeeding functions in the above sense,
  allowing to decide propositions involving Landau symbols and functions that are products of
  powers of functions from this chain by reducing the proposition to a statement involving only
  logical connectives and comparisons on the exponents.

  We will now give the mathematical background for this and implement reification to bring
  functions from this class into a canonical form, allowing the decision procedure to be
  implemented in a simproc.
*}

subsection {* Decision procedure *}

definition "powr_closure f \<equiv> {\<lambda>x. f x powr p :: real |p. True}"

lemma powr_closureI [simp]: "(\<lambda>x. f x powr p) \<in> powr_closure f"
  unfolding powr_closure_def by force

lemma powr_closureE:
  assumes "g \<in> powr_closure f"
  obtains p where "g = (\<lambda>x. f x powr p)"
  using assms unfolding powr_closure_def by force


locale landau_function_family =
  fixes F :: "'a filter" and H :: "('a \<Rightarrow> real) set"
  assumes F_nontrivial: "F \<noteq> bot"
  assumes pos: "h \<in> H \<Longrightarrow> eventually (\<lambda>x. h x > 0) F"
  assumes linear: "h1 \<in> H \<Longrightarrow> h2 \<in> H \<Longrightarrow> h1 \<in> o[F](h2) \<or> h2 \<in> o[F](h1) \<or> h1 \<in> \<Theta>[F](h2)"
  assumes mult: "h1 \<in> H \<Longrightarrow> h2 \<in> H \<Longrightarrow> (\<lambda>x. h1 x * h2 x) \<in> H"
  assumes inverse: "h \<in> H \<Longrightarrow> (\<lambda>x. inverse (h x)) \<in> H"
begin

lemma div: "h1 \<in> H \<Longrightarrow> h2 \<in> H \<Longrightarrow> (\<lambda>x. h1 x / h2 x) \<in> H"
  by (subst divide_inverse) (intro mult inverse)

lemma nonzero: "h \<in> H \<Longrightarrow> eventually (\<lambda>x. h x \<noteq> 0) F"
  by (drule pos) (auto elim: eventually_mono)

lemma landau_cases:
  assumes "h1 \<in> H" "h2 \<in> H"
  obtains "h1 \<in> o[F](h2)" | "h2 \<in> o[F](h1)" | "h1 \<in> \<Theta>[F](h2)"
  using linear[OF assms] by blast

lemma small_big_antisym:
  assumes "h1 \<in> H" "h2 \<in> H" "h1 \<in> o[F](h2)" "h2 \<in> O[F](h1)" shows False
proof-
  from nonzero[OF assms(1)] nonzero[OF assms(2)] landau_o.small_big_asymmetric[OF assms(3,4)]
    have "eventually (\<lambda>_::'a. False) F" by eventually_elim simp
  thus False by (simp add: eventually_False F_nontrivial)
qed

lemma small_antisym:
  assumes "h1 \<in> H" "h2 \<in> H" "h1 \<in> o[F](h2)" "h2 \<in> o[F](h1)" shows False
  using assms by (blast intro: small_big_antisym landau_o.small_imp_big)

end

locale landau_function_family_pair =
  G: landau_function_family F G + H: landau_function_family F H for F G H +
  fixes g
  assumes gs_dominate: "g1 \<in> G \<Longrightarrow> g2 \<in> G \<Longrightarrow> h1 \<in> H \<Longrightarrow> h2 \<in> H \<Longrightarrow> g1 \<in> o[F](g2) \<Longrightarrow>
     (\<lambda>x. g1 x * h1 x) \<in> o[F](\<lambda>x. g2 x * h2 x)"
  assumes g: "g \<in> G"
  assumes g_dominates: "h \<in> H \<Longrightarrow> h \<in> o[F](g)"
begin

sublocale GH: landau_function_family F "G * H"
proof (unfold_locales; (elim set_times_elim; hypsubst)?)
  fix g h assume "g \<in> G" "h \<in> H"
  from G.pos[OF this(1)] H.pos[OF this(2)] show "eventually (\<lambda>x. (g*h) x > 0) F"
    by eventually_elim simp
next
  fix g h assume A: "g \<in> G" "h \<in> H"
  have "(\<lambda>x. inverse ((g * h) x)) = (\<lambda>x. inverse (g x)) * (\<lambda>x. inverse (h x))" by (rule ext) simp
  also from A have "... \<in> G * H" by (intro G.inverse H.inverse set_times_intro)
  finally show "(\<lambda>x. inverse ((g * h) x)) \<in> G * H" .
next
  fix g1 g2 h1 h2 assume A: "g1 \<in> G" "g2 \<in> G" "h1 \<in> H" "h2 \<in> H"
  from gs_dominate[OF this] gs_dominate[OF this(2,1,4,3)]
       G.linear[OF this(1,2)] H.linear[OF this(3,4)]
    show "g1 * h1 \<in> o[F](g2 * h2) \<or> g2 * h2 \<in> o[F](g1 * h1) \<or> g1 * h1 \<in> \<Theta>[F](g2 * h2)"
    by (elim disjE) (force simp: func_times bigomega_iff_bigo intro: landau_theta.mult
         landau_o.small.mult landau_o.small_big_mult landau_o.big_small_mult)+
  have B: "(\<lambda>x. (g1 * h1) x * (g2 * h2) x) = (g1 * g2) * (h1 * h2)"
    by (rule ext) (simp add: func_times mult_ac)
  from A show "(\<lambda>x. (g1 * h1) x * (g2 * h2) x) \<in> G * H"
    by (subst B, intro set_times_intro) (auto intro: G.mult H.mult simp: func_times)
qed (fact G.F_nontrivial)

lemma smallo_iff:
  assumes "g1 \<in> G" "g2 \<in> G" "h1 \<in> H" "h2 \<in> H"
  shows "(\<lambda>x. g1 x * h1 x) \<in> o[F](\<lambda>x. g2 x * h2 x) \<longleftrightarrow>
             g1 \<in> o[F](g2) \<or> (g1 \<in> \<Theta>[F](g2) \<and> h1 \<in> o[F](h2))" (is "?P \<longleftrightarrow> ?Q")
proof (rule G.landau_cases[OF assms(1,2)])
  assume "g1 \<in> o[F](g2)"
  thus ?thesis by (auto intro!: gs_dominate assms)
next
  assume A: "g1 \<in> \<Theta>[F](g2)"
  hence B: "g2 \<in> O[F](g1)" by (subst (asm) bigtheta_sym) (rule bigthetaD1)
  hence "g1 \<notin> o[F](g2)" using assms by (auto dest: G.small_big_antisym)
  moreover from A have "o[F](\<lambda>x. g2 x * h2 x) = o[F](\<lambda>x. g1 x * h2 x)"
    by (intro landau_o.small.cong_bigtheta landau_theta.mult_right, subst bigtheta_sym)
  ultimately show ?thesis using G.nonzero[OF assms(1)] A
    by (auto simp add: landau_o.small.mult_cancel_left)
next
  assume A: "g2 \<in> o[F](g1)"
  from gs_dominate[OF assms(2,1,4,3) this] have B: "g2 * h2 \<in> o[F](g1 * h1)" by (simp add: func_times)
  have "g1 \<notin> o[F](g2)" "g1 \<notin> \<Theta>[F](g2)" using assms A
    by (auto dest: G.small_antisym G.small_big_antisym simp: bigomega_iff_bigo)
  moreover have "\<not>?P"
    by (intro notI GH.small_antisym[OF _ _ B] set_times_intro) (simp_all add: func_times assms)
  ultimately show ?thesis by blast
qed

lemma bigo_iff:
  assumes "g1 \<in> G" "g2 \<in> G" "h1 \<in> H" "h2 \<in> H"
  shows "(\<lambda>x. g1 x * h1 x) \<in> O[F](\<lambda>x. g2 x * h2 x) \<longleftrightarrow>
             g1 \<in> o[F](g2) \<or> (g1 \<in> \<Theta>[F](g2) \<and> h1 \<in> O[F](h2))" (is "?P \<longleftrightarrow> ?Q")
proof (rule G.landau_cases[OF assms(1,2)])
  assume "g1 \<in> o[F](g2)"
  thus ?thesis by (auto intro!: gs_dominate assms landau_o.small_imp_big)
next
  assume A: "g2 \<in> o[F](g1)"
  hence "g1 \<notin> O[F](g2)" using assms by (auto dest: G.small_big_antisym)
  moreover from gs_dominate[OF assms(2,1,4,3) A] have "g2*h2 \<in> o[F](g1*h1)" by (simp add: func_times)
  hence "g1*h1 \<notin> O[F](g2*h2)" by (blast intro: GH.small_big_antisym assms)
  ultimately show ?thesis using A assms
    by (auto simp: func_times dest: landau_o.small_imp_big)
next
  assume A: "g1 \<in> \<Theta>[F](g2)"
  hence "g1 \<notin> o[F](g2)" unfolding bigtheta_def using assms
    by (auto dest: G.small_big_antisym simp: bigomega_iff_bigo)
  moreover have "O[F](\<lambda>x. g2 x * h2 x) = O[F](\<lambda>x. g1 x * h2 x)"
    by (subst landau_o.big.cong_bigtheta[OF landau_theta.mult_right[OF A]]) (rule refl)
  ultimately show ?thesis using A G.nonzero[OF assms(2)]
    by (auto simp: landau_o.big.mult_cancel_left eventually_nonzero_bigtheta)
qed

lemma bigtheta_iff:
  "g1 \<in> G \<Longrightarrow> g2 \<in> G \<Longrightarrow> h1 \<in> H \<Longrightarrow> h2 \<in> H \<Longrightarrow>
    (\<lambda>x. g1 x * h1 x) \<in> \<Theta>[F](\<lambda>x. g2 x * h2 x) \<longleftrightarrow> g1 \<in> \<Theta>[F](g2) \<and> h1 \<in> \<Theta>[F](h2)"
  by (auto simp: bigtheta_def bigo_iff bigomega_iff_bigo intro: landau_o.small_imp_big
           dest: G.small_antisym G.small_big_antisym)

end


lemma landau_function_family_powr_closure:
  assumes "F \<noteq> bot" "filterlim f at_top F"
  shows   "landau_function_family F (powr_closure f)"
proof (unfold_locales; (elim powr_closureE; hypsubst)?)
  from assms have "eventually (\<lambda>x. f x \<ge> 1) F" using filterlim_at_top by auto
  hence A: "eventually (\<lambda>x. f x \<noteq> 0) F" by eventually_elim simp
  {
    fix p q :: real
    show "(\<lambda>x. f x powr p) \<in> o[F](\<lambda>x. f x powr q) \<or>
          (\<lambda>x. f x powr q) \<in> o[F](\<lambda>x. f x powr p) \<or>
          (\<lambda>x. f x powr p) \<in> \<Theta>[F](\<lambda>x. f x powr q)"
    by (cases p q rule: linorder_cases)
       (force intro!: smalloI_tendsto tendsto_neg_powr simp: powr_diff [symmetric]  assms A)+
  }
  fix p
  show "eventually (\<lambda>x. f x powr p > 0) F" using A by simp
qed (auto simp: powr_add[symmetric] powr_minus[symmetric] \<open>F \<noteq> bot\<close> intro: powr_closureI)

lemma landau_function_family_pair_trans:
  assumes "landau_function_family_pair Ftr F G f"
  assumes "landau_function_family_pair Ftr G H g"
  shows   "landau_function_family_pair Ftr F (G*H) f"
proof-
  interpret FG: landau_function_family_pair Ftr F G f by fact
  interpret GH: landau_function_family_pair Ftr G H g by fact
  show ?thesis
  proof (unfold_locales; (elim set_times_elim)?; (clarify)?;
         (unfold func_times mult.assoc[symmetric])?)
    fix f1 f2 g1 g2 h1 h2
    assume A: "f1 \<in> F" "f2 \<in> F" "g1 \<in> G" "g2 \<in> G" "h1 \<in> H" "h2 \<in> H" "f1 \<in> o[Ftr](f2)"

    from A have "(\<lambda>x. f1 x * g1 x * h1 x) \<in> o[Ftr](\<lambda>x. f1 x * g1 x * g x)"
      by (intro landau_o.small.mult_left GH.g_dominates)
    also have "(\<lambda>x. f1 x * g1 x * g x) = (\<lambda>x. f1 x * (g1 x * g x))" by (simp only: mult.assoc)
    also from A have "... \<in> o[Ftr](\<lambda>x. f2 x * (g2 x / g x))"
      by (intro FG.gs_dominate FG.H.mult FG.H.div GH.g)
    also from A have "(\<lambda>x. inverse (h2 x)) \<in> o[Ftr](g)" by (intro GH.g_dominates GH.H.inverse)
    with GH.g A have "(\<lambda>x. f2 x * (g2 x / g x)) \<in> o[Ftr](\<lambda>x. f2 x * (g2 x * h2 x))"
      by (auto simp: FG.H.nonzero GH.H.nonzero divide_inverse
               intro!: landau_o.small.mult_left intro: landau_o.small.inverse_flip)
    also have "... = o[Ftr](\<lambda>x. f2 x * g2 x * h2 x)" by (simp only: mult.assoc)
    finally show "(\<lambda>x. f1 x * g1 x * h1 x) \<in> o[Ftr](\<lambda>x. f2 x * g2 x * h2 x)" .
  next
    fix g1 h1 assume A: "g1 \<in> G" "h1 \<in> H"
    hence "(\<lambda>x. g1 x * h1 x) \<in> o[Ftr](\<lambda>x. g1 x * g x)"
      by (intro landau_o.small.mult_left GH.g_dominates)
    also from A have "(\<lambda>x. g1 x * g x) \<in> o[Ftr](f)" by (intro FG.g_dominates FG.H.mult GH.g)
    finally show "(\<lambda>x. g1 x * h1 x) \<in> o[Ftr](f)" .
  qed (simp_all add: FG.g)
qed

lemma landau_function_family_pair_trans_powr:
  assumes "landau_function_family_pair F (powr_closure g) H (\<lambda>x. g x powr 1)"
  assumes "filterlim f at_top F"
  assumes "\<And>p. (\<lambda>x. g x powr p) \<in> o[F](f)"
  shows   "landau_function_family_pair F (powr_closure f) (powr_closure g * H) (\<lambda>x. f x powr 1)"
proof (rule landau_function_family_pair_trans[OF _ assms(1)])
  interpret GH: landau_function_family_pair F "powr_closure g" H "\<lambda>x. g x powr 1" by fact
  interpret F: landau_function_family F "powr_closure f"
    by (rule landau_function_family_powr_closure) fact+
  show "landau_function_family_pair F (powr_closure f) (powr_closure g) (\<lambda>x. f x powr 1)"
  proof (unfold_locales; (elim powr_closureE; hypsubst)?)
    show "(\<lambda>x. f x powr 1) \<in> powr_closure f" by (rule powr_closureI)
  next
    fix p ::real
    note assms(3)[of p]
    also from assms(2) have "eventually (\<lambda>x. f x \<ge> 1) F" by (force simp: filterlim_at_top)
    hence "f \<in> \<Theta>[F](\<lambda>x. f x powr 1)" by (auto intro!: bigthetaI_cong elim!: eventually_mono)
    finally show "(\<lambda>x. g x powr p) \<in> o[F](\<lambda>x. f x powr 1)" .
  next
    fix p p1 p2 p3 :: real
    assume A: "(\<lambda>x. f x powr p) \<in> o[F](\<lambda>x. f x powr p1)"
    have p: "p < p1"
    proof (cases p p1 rule: linorder_cases)
      assume "p > p1"
      moreover from assms(2) have "eventually (\<lambda>x. f x \<ge> 1) F"
        by (force simp: filterlim_at_top)
      hence "eventually (\<lambda>x. f x \<noteq> 0) F" by eventually_elim simp
      ultimately have "(\<lambda>x. f x powr p1) \<in> o[F](\<lambda>x. f x powr p)" using assms
        by (auto intro!: smalloI_tendsto tendsto_neg_powr simp: powr_diff [symmetric] )
      from F.small_antisym[OF _ _ this A] show ?thesis by (auto simp: powr_closureI)
    next
      assume "p = p1"
      hence "(\<lambda>x. f x powr p1) \<in> O[F](\<lambda>x. f x powr p)" by (intro bigthetaD1) simp
      with F.small_big_antisym[OF _ _ A this] show ?thesis by (auto simp: powr_closureI)
    qed

    from assms(2) have f_pos: "eventually (\<lambda>x. f x \<ge> 1) F" by (force simp: filterlim_at_top)
    from assms have "(\<lambda>x. g x powr ((p2 - p3)/(p1 - p))) \<in> o[F](f)" by simp
    from smallo_powr[OF this, of "p1 - p"] p
      have "(\<lambda>x. g x powr (p2 - p3)) \<in> o[F](\<lambda>x. \<bar>f x\<bar> powr (p1 - p))" by (simp add: powr_powr)
    hence "(\<lambda>x. \<bar>f x\<bar> powr p * g x powr p2) \<in> o[F](\<lambda>x. \<bar>f x\<bar> powr p1 * g x powr p3)" (is ?P)
      using GH.G.nonzero[OF GH.g] F.nonzero[OF powr_closureI]
      by (simp add: powr_diff landau_o.small.divide_eq1
                    landau_o.small.divide_eq2 mult.commute)
    also have "?P \<longleftrightarrow> (\<lambda>x. f x powr p * g x powr p2) \<in> o[F](\<lambda>x. f x powr p1 * g x powr p3)"
      using f_pos by (intro landau_o.small.cong_ex) (auto elim!: eventually_mono)
    finally show "(\<lambda>x. f x powr p * g x powr p2) \<in> o[F](\<lambda>x. f x powr p1 * g x powr p3)" .
  qed
qed


definition dominates :: "'a filter \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" where
  "dominates F f g = (\<forall>p. (\<lambda>x. g x powr p) \<in> o[F](f))"

lemma dominates_trans:
  assumes "eventually (\<lambda>x. g x > 0) F"
  assumes "dominates F f g" "dominates F g h"
  shows   "dominates F f h"
unfolding dominates_def
proof
  fix p :: real
  from assms(3) have "(\<lambda>x. h x powr p) \<in> o[F](g)" unfolding dominates_def by simp
  also from assms(1) have "g \<in> \<Theta>[F](\<lambda>x. g x powr 1)"
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  also from assms(2) have "(\<lambda>x. g x powr 1) \<in> o[F](f)" unfolding dominates_def by simp
  finally show "(\<lambda>x. h x powr p) \<in> o[F](f)" .
qed

fun landau_dominating_chain where
  "landau_dominating_chain F (f # g # gs) \<longleftrightarrow>
    dominates F f g \<and> landau_dominating_chain F (g # gs)"
| "landau_dominating_chain F [f] \<longleftrightarrow> (\<lambda>x. 1) \<in> o[F](f)"
| "landau_dominating_chain F [] \<longleftrightarrow> True"

primrec landau_dominating_chain' where
  "landau_dominating_chain' F [] \<longleftrightarrow> True"
| "landau_dominating_chain' F (f # gs) \<longleftrightarrow>
    landau_function_family_pair F (powr_closure f) (prod_list (map powr_closure gs)) (\<lambda>x. f x powr 1) \<and>
    landau_dominating_chain' F gs"



primrec nonneg_list where
  "nonneg_list [] \<longleftrightarrow> True"
| "nonneg_list (x#xs) \<longleftrightarrow> x > 0 \<or> (x = 0 \<and> nonneg_list xs)"

primrec pos_list where
  "pos_list [] \<longleftrightarrow> False"
| "pos_list (x#xs) \<longleftrightarrow> x > 0 \<or> (x = 0 \<and> pos_list xs)"


lemma dominating_chain_imp_dominating_chain':
  "Ftr \<noteq> bot \<Longrightarrow> (\<And>g. g \<in> set gs \<Longrightarrow> filterlim g at_top Ftr) \<Longrightarrow>
     landau_dominating_chain Ftr gs \<Longrightarrow> landau_dominating_chain' Ftr gs"
proof (induction gs rule: landau_dominating_chain.induct)
  case (1 F f g gs)
  from 1 show ?case
    by (auto intro!: landau_function_family_pair_trans_powr simp add: dominates_def)
next
  case (2 F f)
  then interpret F: landau_function_family F "powr_closure f"
    by (intro landau_function_family_powr_closure) simp_all
  from 2 have "eventually (\<lambda>x. f x \<ge> 1) F" by (force simp: filterlim_at_top)
  hence "o[F](\<lambda>x. f x powr 1) = o[F](\<lambda>x. f x)"
    by (intro landau_o.small.cong) (auto elim!: eventually_mono)
  with 2 have "landau_function_family_pair F (powr_closure f) {\<lambda>_. 1} (\<lambda>x. f x powr 1)"
    by unfold_locales (auto intro: powr_closureI)
  thus ?case by (simp add: one_fun_def)
next
  case 3
  then show ?case by simp
qed


locale landau_function_family_chain =
  fixes F :: "'b filter"
  fixes gs :: "'a list"
  fixes get_param :: "'a \<Rightarrow> real"
  fixes get_fun :: "'a \<Rightarrow> ('b \<Rightarrow> real)"
  assumes F_nontrivial: "F \<noteq> bot"
  assumes gs_pos: "g \<in> set (map get_fun gs) \<Longrightarrow> filterlim g at_top F"
  assumes dominating_chain: "landau_dominating_chain F (map get_fun gs)"
begin

lemma dominating_chain': "landau_dominating_chain' F (map get_fun gs)"
  by (intro dominating_chain_imp_dominating_chain' gs_pos dominating_chain F_nontrivial)

lemma gs_powr_0_eq_one:
  "eventually (\<lambda>x. (\<Prod>g\<leftarrow>gs. get_fun g x powr 0) = 1) F"
using gs_pos
proof (induction gs)
  case (Cons g gs)
  from Cons have "eventually (\<lambda>x. get_fun g x > 0) F" by (auto simp: filterlim_at_top_dense)
  moreover from Cons have "eventually (\<lambda>x. (\<Prod>g\<leftarrow>gs. get_fun g x powr 0) = 1) F" by simp
  ultimately show ?case by eventually_elim simp
qed simp_all

lemma listmap_gs_in_listmap:
  "(\<lambda>x. \<Prod>g\<leftarrow>fs. h g x powr p g) \<in> prod_list (map powr_closure (map h fs))"
proof-
  have "(\<lambda>x. \<Prod>g\<leftarrow>fs. h g x powr p g) = (\<Prod>g\<leftarrow>fs. (\<lambda>x. h g x powr p g))"
    by (rule ext, induction fs) simp_all
  also have "... \<in> prod_list (map powr_closure (map h fs))"
    apply (induction fs)
    apply (simp add: fun_eq_iff)
    apply (simp only: list.map prod_list.Cons, rule set_times_intro)
    apply simp_all
    done
  finally show ?thesis .
qed

lemma smallo_iff:
  "(\<lambda>_. 1) \<in> o[F](\<lambda>x. \<Prod>g\<leftarrow>gs. get_fun g x powr get_param g) \<longleftrightarrow> pos_list (map get_param gs)"
proof-
  have "((\<lambda>_. 1) \<in> o[F](\<lambda>x. \<Prod>g\<leftarrow>gs. get_fun g x powr get_param g)) \<longleftrightarrow>
          ((\<lambda>x. \<Prod>g\<leftarrow>gs. get_fun g x powr 0) \<in> o[F](\<lambda>x. \<Prod>g\<leftarrow>gs. get_fun g x powr get_param g))"
    by (rule sym, intro landau_o.small.in_cong gs_powr_0_eq_one)
  also from gs_pos dominating_chain' have "... \<longleftrightarrow> pos_list (map get_param gs)"
  proof (induction gs)
    case Nil
    have "(\<lambda>x::'b. 1::real) \<notin> o[F](\<lambda>x. 1)" using F_nontrivial
      by (auto dest!: landau_o.small_big_asymmetric)
    thus ?case by simp
  next
    case (Cons g gs)
    then interpret G: landau_function_family_pair F "powr_closure (get_fun g)"
       "prod_list (map powr_closure (map get_fun gs))" "\<lambda>x. get_fun g x powr 1" by simp
    from Cons show ?case using listmap_gs_in_listmap[of get_fun _ gs] F_nontrivial
      by (simp_all add: G.smallo_iff listmap_gs_in_listmap powr_smallo_iff powr_bigtheta_iff
                   del: powr_zero_eq_one)
  qed
  finally show ?thesis .
qed

lemma bigo_iff:
  "(\<lambda>_. 1) \<in> O[F](\<lambda>x. \<Prod>g\<leftarrow>gs. get_fun g x powr get_param g) \<longleftrightarrow> nonneg_list (map get_param gs)"
proof-
  have "((\<lambda>_. 1) \<in> O[F](\<lambda>x. \<Prod>g\<leftarrow>gs. get_fun g x powr get_param g)) \<longleftrightarrow>
          ((\<lambda>x. \<Prod>g\<leftarrow>gs. get_fun g x powr 0) \<in> O[F](\<lambda>x. \<Prod>g\<leftarrow>gs. get_fun g x powr get_param g))"
    by (rule sym, intro landau_o.big.in_cong gs_powr_0_eq_one)
  also from gs_pos dominating_chain' have "... \<longleftrightarrow> nonneg_list (map get_param gs)"
  proof (induction gs)
    case Nil
    then show ?case by (simp add: func_one)
  next
    case (Cons g gs)
    then interpret G: landau_function_family_pair F "powr_closure (get_fun g)"
       "prod_list (map powr_closure (map get_fun gs))" "\<lambda>x. get_fun g x powr 1" by simp
    from Cons show ?case using listmap_gs_in_listmap[of get_fun _ gs] F_nontrivial
      by (simp_all add: G.bigo_iff listmap_gs_in_listmap powr_smallo_iff powr_bigtheta_iff
                   del: powr_zero_eq_one)
  qed
  finally show ?thesis .
qed

lemma bigtheta_iff:
  "(\<lambda>_. 1) \<in> \<Theta>[F](\<lambda>x. \<Prod>g\<leftarrow>gs. get_fun g x powr get_param g) \<longleftrightarrow> list_all (op= 0) (map get_param gs)"
proof-
  have "((\<lambda>_. 1) \<in> \<Theta>[F](\<lambda>x. \<Prod>g\<leftarrow>gs. get_fun g x powr get_param g)) \<longleftrightarrow>
          ((\<lambda>x. \<Prod>g\<leftarrow>gs. get_fun g x powr 0) \<in> \<Theta>[F](\<lambda>x. \<Prod>g\<leftarrow>gs. get_fun g x powr get_param g))"
    by (rule sym, intro landau_theta.in_cong gs_powr_0_eq_one)
  also from gs_pos dominating_chain' have "... \<longleftrightarrow> list_all (op= 0) (map get_param gs)"
  proof (induction gs)
    case Nil
    then show ?case by (simp add: func_one)
  next
    case (Cons g gs)
    then interpret G: landau_function_family_pair F "powr_closure (get_fun g)"
       "prod_list (map powr_closure (map get_fun gs))" "\<lambda>x. get_fun g x powr 1" by simp
    from Cons show ?case using listmap_gs_in_listmap[of get_fun _ gs] F_nontrivial
      by (simp_all add: G.bigtheta_iff listmap_gs_in_listmap powr_smallo_iff powr_bigtheta_iff
                   del: powr_zero_eq_one)
  qed
  finally show ?thesis .
qed

end



lemma fun_chain_at_top_at_top:
  assumes "filterlim (f :: ('a::order) \<Rightarrow> 'a) at_top at_top"
  shows   "filterlim (f ^^ n) at_top at_top"
  by (induction n) (auto intro: filterlim_ident filterlim_compose[OF assms])

lemma const_smallo_ln_chain: "(\<lambda>_. 1) \<in> o((ln::real\<Rightarrow>real)^^n)"
proof (intro smalloI_tendsto)
  show "((\<lambda>x::real. 1 / (ln^^n) x) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_divide_0 tendsto_const filterlim_at_top_imp_at_infinity
             fun_chain_at_top_at_top ln_at_top)+
next
  from fun_chain_at_top_at_top[OF ln_at_top, of n]
    have "eventually (\<lambda>x::real. (ln^^n) x > 0) at_top" by (simp add: filterlim_at_top_dense)
  thus "eventually (\<lambda>x::real. (ln^^n) x \<noteq> 0) at_top" by eventually_elim simp_all
qed

lemma ln_fun_in_smallo_fun:
  assumes "filterlim f at_top at_top"
  shows   "(\<lambda>x. ln (f x) powr p :: real) \<in> o(f)"
proof (rule smalloI_tendsto)
  have "((\<lambda>x. ln x powr p / x powr 1) \<longlongrightarrow> 0) at_top" by (rule tendsto_ln_powr_over_powr') simp
  moreover have "eventually (\<lambda>x. ln x powr p / x powr 1 = ln x powr p / x) at_top"
    using eventually_gt_at_top[of "0::real"] by eventually_elim simp
  ultimately have "((\<lambda>x. ln x powr p / x) \<longlongrightarrow> 0) at_top" by (subst (asm) tendsto_cong)
  from this assms show "((\<lambda>x. ln (f x) powr p / f x) \<longlongrightarrow> 0) at_top"
    by (rule filterlim_compose)
  from assms have "eventually (\<lambda>x. f x \<ge> 1) at_top" by (simp add: filterlim_at_top)
  thus "eventually (\<lambda>x. f x \<noteq> 0) at_top" by eventually_elim simp
qed

lemma ln_chain_dominates: "m > n \<Longrightarrow> dominates at_top ((ln::real \<Rightarrow> real)^^n) (ln^^m)"
proof (erule less_Suc_induct)
  fix n show "dominates at_top ((ln::real\<Rightarrow>real)^^n) (ln^^(Suc n))" unfolding dominates_def
    by (force intro: ln_fun_in_smallo_fun fun_chain_at_top_at_top ln_at_top)
next
  fix k m n
  assume A: "dominates at_top ((ln::real \<Rightarrow> real)^^k) (ln^^m)"
            "dominates at_top ((ln::real \<Rightarrow> real)^^m) (ln^^n)"
  from fun_chain_at_top_at_top[OF ln_at_top, of m]
    have "eventually (\<lambda>x::real. (ln^^m) x > 0) at_top" by (simp add: filterlim_at_top_dense)
  from this A show "dominates at_top ((ln::real \<Rightarrow> real)^^k) ((ln::real \<Rightarrow> real)^^n)"
    by (rule dominates_trans)
qed






datatype primfun = LnChain nat

instantiation primfun :: linorder
begin

fun less_eq_primfun :: "primfun \<Rightarrow> primfun \<Rightarrow> bool" where
  "LnChain x \<le> LnChain y \<longleftrightarrow> x \<le> y"

fun less_primfun :: "primfun \<Rightarrow> primfun \<Rightarrow> bool" where
  "LnChain x < LnChain y \<longleftrightarrow> x < y"

instance
proof (standard, goal_cases)
  case (1 x y) show ?case by (induction x y rule: less_eq_primfun.induct) auto
next
  case (2 x) show ?case by (cases x) auto
next
  case (3 x y z) thus ?case
    by (induction x y rule: less_eq_primfun.induct, cases z) auto
next
  case (4 x y) thus ?case by (induction x y rule: less_eq_primfun.induct) auto
next
  case (5 x y) thus ?case by (induction x y rule: less_eq_primfun.induct) auto
qed

end


fun eval_primfun' :: "_ \<Rightarrow> _ \<Rightarrow> real" where
  "eval_primfun' (LnChain n) = (\<lambda>x. (ln^^n) x)"

fun eval_primfun :: "_ \<Rightarrow> _ \<Rightarrow> real" where
  "eval_primfun (f, e) = (\<lambda>x. eval_primfun' f x powr e)"

lemma eval_primfun_altdef: "eval_primfun f x = eval_primfun' (fst f) x powr snd f"
  by (cases f) simp

fun merge_primfun where
  "merge_primfun (x::primfun, a) (y, b) = (x, a + b)"

fun inverse_primfun where
  "inverse_primfun (x::primfun, a) = (x, -a)"

fun powr_primfun where
  "powr_primfun (x::primfun, a) e = (x, e*a)"

lemma primfun_cases:
  assumes "(\<And>n e. P (LnChain n, e))"
  shows   "P x"
proof (cases x, hypsubst)
  fix a b show "P (a, b)" by (cases a; hypsubst, rule assms)
qed



lemma eval_primfun'_at_top: "filterlim (eval_primfun' f) at_top at_top"
  by (cases f) (auto intro!: fun_chain_at_top_at_top ln_at_top)

lemma primfun_dominates:
  "f < g \<Longrightarrow> dominates at_top (eval_primfun' f) (eval_primfun' g)"
  by (elim less_primfun.elims; hypsubst) (simp_all add: ln_chain_dominates)

lemma eval_primfun_pos: "eventually (\<lambda>x::real. eval_primfun f x > 0) at_top"
proof (cases f, hypsubst)
  fix f e
  from eval_primfun'_at_top have "eventually (\<lambda>x. eval_primfun' f x > 0) at_top"
    by (auto simp: filterlim_at_top_dense)
  thus "eventually (\<lambda>x::real. eval_primfun (f,e) x > 0) at_top" by eventually_elim simp
qed

lemma eventually_nonneg_primfun: "eventually_nonneg at_top (eval_primfun f)"
  unfolding eventually_nonneg_def using eval_primfun_pos[of f] by eventually_elim simp

lemma eval_primfun_nonzero: "eventually (\<lambda>x. eval_primfun f x \<noteq> 0) at_top"
  using eval_primfun_pos[of f] by eventually_elim simp

lemma eval_merge_primfun:
  "fst f = fst g \<Longrightarrow>
     eval_primfun (merge_primfun f g) x = eval_primfun f x * eval_primfun g x"
  by (induction f g rule: merge_primfun.induct) (simp_all add: powr_add)

lemma eval_inverse_primfun:
  "eval_primfun (inverse_primfun f) x = inverse (eval_primfun f x)"
  by (induction f rule: inverse_primfun.induct) (simp_all add: powr_minus)

lemma eval_powr_primfun:
  "eval_primfun (powr_primfun f e) x = eval_primfun f x powr e"
  by (induction f e rule: powr_primfun.induct) (simp_all add: powr_powr mult.commute)


definition eval_primfuns where
  "eval_primfuns fs x = (\<Prod>f\<leftarrow>fs. eval_primfun f x)"

lemma eval_primfuns_pos: "eventually (\<lambda>x. eval_primfuns fs x > 0) at_top"
proof-
  have "eventually (\<lambda>x. \<forall>f\<in>set fs. eval_primfun f x > 0) at_top"
    by (intro eventually_ball_finite ballI eval_primfun_pos finite_set)
  thus ?thesis unfolding eval_primfuns_def by eventually_elim (rule prod_list_pos, auto)
qed

lemma eval_primfuns_nonzero: "eventually (\<lambda>x. eval_primfuns fs x \<noteq> 0) at_top"
  using eval_primfuns_pos[of fs] by eventually_elim simp



subsection {* Reification *}

definition LANDAU_PROD' where
  "LANDAU_PROD' L c f = L(\<lambda>x. c * f x)"

definition LANDAU_PROD where
  "LANDAU_PROD L c1 c2 fs \<longleftrightarrow> (\<lambda>_. c1) \<in> L(\<lambda>x. c2 * eval_primfuns fs x)"

definition BIGTHETA_CONST' where "BIGTHETA_CONST' c = \<Theta>(\<lambda>x. c)"
definition BIGTHETA_CONST where "BIGTHETA_CONST c A = set_mult \<Theta>(\<lambda>_. c) A"
definition BIGTHETA_FUN where "BIGTHETA_FUN f = \<Theta>(f)"

lemma BIGTHETA_CONST'_tag: "\<Theta>(\<lambda>x. c) = BIGTHETA_CONST' c" using BIGTHETA_CONST'_def ..
lemma BIGTHETA_CONST_tag: "\<Theta>(f) = BIGTHETA_CONST 1 \<Theta>(f)"
  by (simp add: BIGTHETA_CONST_def bigtheta_mult_eq_set_mult[symmetric])
lemma BIGTHETA_FUN_tag: "\<Theta>(f) = BIGTHETA_FUN f"
  by (simp add: BIGTHETA_FUN_def)

lemma set_mult_is_times: "set_mult A B = A * B"
  unfolding set_mult_def set_times_def func_times by blast

lemma set_powr_mult:
  assumes "eventually_nonneg F f" and "eventually_nonneg F g"
  shows   "\<Theta>[F](\<lambda>x. (f x * g x :: real) powr p) = set_mult (\<Theta>[F](\<lambda>x. f x powr p)) (\<Theta>[F](\<lambda>x. g x powr p))"
proof-
  from assms have "eventually (\<lambda>x. f x \<ge> 0) F" "eventually (\<lambda>x. g x \<ge> 0) F"
    by (simp_all add: eventually_nonneg_def)
  hence "eventually (\<lambda>x. (f x * g x :: real) powr p = f x powr p * g x powr p) F"
    by eventually_elim (simp add: powr_mult)
  hence "\<Theta>[F](\<lambda>x. (f x * g x :: real) powr p) = \<Theta>[F](\<lambda>x. f x powr p * g x powr p)"
    by (rule landau_theta.cong)
  also have "... = set_mult (\<Theta>[F](\<lambda>x. f x powr p)) (\<Theta>[F](\<lambda>x. g x powr p))"
    by (simp add: bigtheta_mult_eq_set_mult)
  finally show ?thesis .
qed

lemma eventually_nonneg_bigtheta_pow_realpow:
  "\<Theta>(\<lambda>x. eval_primfun f x ^ e) = \<Theta>(\<lambda>x. eval_primfun f x powr real e)"
  using eval_primfun_pos[of f]
  by (auto intro!: landau_theta.cong elim!: eventually_mono simp: powr_realpow)

lemma BIGTHETA_CONST_fold:
  "BIGTHETA_CONST (c::real) (BIGTHETA_CONST d A) = BIGTHETA_CONST (c*d) A"
  "bigtheta_pow at_top (BIGTHETA_CONST c \<Theta>(eval_primfun pf)) k =
     BIGTHETA_CONST (c ^ k) \<Theta>(\<lambda>x. eval_primfun pf x powr k)"
  "set_inverse (BIGTHETA_CONST c \<Theta>(f)) = BIGTHETA_CONST (inverse c) \<Theta>(\<lambda>x. inverse (f x))"
  "set_mult (BIGTHETA_CONST c \<Theta>(f)) (BIGTHETA_CONST d \<Theta>(g)) =
     BIGTHETA_CONST (c*d) \<Theta>(\<lambda>x. f x*g x)"
  "BIGTHETA_CONST' (c::real) = BIGTHETA_CONST c \<Theta>(\<lambda>_. 1)"
  "BIGTHETA_FUN (f::real\<Rightarrow>real) = BIGTHETA_CONST 1 \<Theta>(f)"
  apply (simp add: BIGTHETA_CONST_def set_mult_is_times bigtheta_mult_eq_set_mult mult_ac)
  apply (simp only: BIGTHETA_CONST_def bigtheta_mult_eq_set_mult[symmetric]
           bigtheta_pow_eq_set_pow[symmetric] power_mult_distrib mult_ac)
  apply (simp add: bigtheta_mult_eq_set_mult eventually_nonneg_bigtheta_pow_realpow)
  by (simp_all add: BIGTHETA_CONST_def BIGTHETA_CONST'_def BIGTHETA_FUN_def
        bigtheta_mult_eq_set_mult[symmetric] set_mult_is_times[symmetric]
        bigtheta_pow_eq_set_pow[symmetric] bigtheta_inverse_eq_set_inverse[symmetric]
        mult_ac power_mult_distrib)


lemma fold_fun_chain:
  "g x = (g ^^ 1) x" "(g ^^ m) ((g ^^ n) x) = (g ^^ (m+n)) x"
  by (simp_all add: funpow_add)

lemma reify_ln_chain_1:
  "\<Theta>(\<lambda>x. (ln ^^ n) x) = \<Theta>(eval_primfun (LnChain n, 1))"
proof (intro landau_theta.cong)
  have "filterlim ((ln :: real \<Rightarrow> real) ^^ n) at_top at_top"
    by (intro fun_chain_at_top_at_top ln_at_top)
  hence "eventually (\<lambda>x::real. (ln ^^ n) x > 0) at_top" using filterlim_at_top_dense by auto
  thus "eventually (\<lambda>x. (ln ^^ n) x = eval_primfun (LnChain n, 1) x) at_top"
    by eventually_elim simp
qed

lemma reify_monom_1:
  "\<Theta>(\<lambda>x::real. x) = \<Theta>(eval_primfun (LnChain 0, 1))"
proof (intro landau_theta.cong)
  from eventually_gt_at_top[of "0::real"]
    show "eventually (\<lambda>x. x = eval_primfun (LnChain 0, 1) x) at_top"
    by eventually_elim simp
qed

lemma reify_monom_pow:
  "\<Theta>(\<lambda>x::real. x ^ e) = \<Theta>(eval_primfun (LnChain 0, real e))"
proof-
  have "\<Theta>(eval_primfun (LnChain 0, real e)) = \<Theta>(\<lambda>x. x powr (real e))" by simp
  also have "... = \<Theta>(\<lambda>x. x^e)" by (intro landau_theta.cong powr_realpow_eventually filterlim_ident)
  finally show ?thesis ..
qed

lemma reify_monom_powr:
  "\<Theta>(\<lambda>x::real. x powr e) = \<Theta>(eval_primfun (LnChain 0, e))"
  by (rule landau_theta.cong) simp

lemmas reify_monom = reify_monom_1 reify_monom_pow reify_monom_powr


lemma reify_ln_chain_pow:
  "\<Theta>(\<lambda>x. (ln ^^ n) x ^ e) = \<Theta>(eval_primfun (LnChain n, real e))"
proof-
  have "\<Theta>(eval_primfun (LnChain n, real e)) = \<Theta>(\<lambda>x. (ln ^^ n) x powr (real e))" by simp
  also have "... = \<Theta>(\<lambda>x. (ln ^^ n) x^e)"
    by (intro landau_theta.cong powr_realpow_eventually fun_chain_at_top_at_top ln_at_top)
  finally show ?thesis ..
qed

lemma reify_ln_chain_powr:
  "\<Theta>(\<lambda>x. (ln ^^ n) x powr e) = \<Theta>(eval_primfun (LnChain n, e))"
  by (intro landau_theta.cong) simp

lemmas reify_ln_chain = reify_ln_chain_1 reify_ln_chain_pow reify_ln_chain_powr

lemma numeral_power_Suc: "numeral n ^ Suc a = numeral n * numeral n ^ a"
  by (rule power.simps)

lemmas landau_product_preprocess =
  one_add_one one_plus_numeral numeral_plus_one arith_simps numeral_power_Suc power_0
  fold_fun_chain[where g = ln] reify_ln_chain reify_monom


lemma LANDAU_PROD'_fold:
  "BIGTHETA_CONST e \<Theta>(\<lambda>_. d) = BIGTHETA_CONST (e*d) \<Theta>(eval_primfuns [])"
  "LANDAU_PROD' c (\<lambda>_. 1) = LANDAU_PROD' c (eval_primfuns [])"
  "eval_primfun f = eval_primfuns [f]"
  "eval_primfuns fs x * eval_primfuns gs x = eval_primfuns (fs @ gs) x"
  apply (simp only: BIGTHETA_CONST_def set_mult_is_times eval_primfuns_def[abs_def] bigtheta_mult_eq)
  apply (simp add: bigtheta_mult_eq[symmetric])
  by (simp_all add: eval_primfuns_def[abs_def] BIGTHETA_CONST_def)


lemma inverse_prod_list_field:
  "prod_list (map (\<lambda>x. inverse (f x)) xs) = inverse (prod_list (map f xs :: _ :: field list))"
  by (induction xs) simp_all

lemma landau_prod_meta_cong:
  assumes "landau_symbol L L' Lr"
  assumes "\<Theta>(f) \<equiv> BIGTHETA_CONST c1 (\<Theta>(eval_primfuns fs))"
  assumes "\<Theta>(g) \<equiv> BIGTHETA_CONST c2 (\<Theta>(eval_primfuns gs))"
  shows   "f \<in> L at_top (g) \<equiv> LANDAU_PROD (L at_top) c1 c2 (map inverse_primfun fs @ gs)"
proof-
  interpret landau_symbol L L' Lr by fact
  have "f \<in> L at_top (g) \<longleftrightarrow> (\<lambda>x. c1 * eval_primfuns fs x) \<in> L at_top (\<lambda>x. c2 * eval_primfuns gs x)"
    using assms(2,3)[symmetric] unfolding BIGTHETA_CONST_def
    by (intro cong_ex_bigtheta) (simp_all add: bigtheta_mult_eq_set_mult[symmetric])
  also have "... \<longleftrightarrow> (\<lambda>x. c1) \<in> L at_top (\<lambda>x. c2 * eval_primfuns gs x / eval_primfuns fs x)"
    by (simp_all add: eval_primfuns_nonzero divide_eq1)
  finally show "f \<in> L at_top (g) \<equiv> LANDAU_PROD (L at_top) c1 c2 (map inverse_primfun fs @ gs)"
    by (simp add: LANDAU_PROD_def eval_primfuns_def eval_inverse_primfun
                  divide_inverse o_def inverse_prod_list_field mult_ac)
qed

fun pos_primfun_list where
  "pos_primfun_list [] \<longleftrightarrow> False"
| "pos_primfun_list ((_,x)#xs) \<longleftrightarrow> x > 0 \<or> (x = 0 \<and> pos_primfun_list xs)"

fun nonneg_primfun_list where
  "nonneg_primfun_list [] \<longleftrightarrow> True"
| "nonneg_primfun_list ((_,x)#xs) \<longleftrightarrow> x > 0 \<or> (x = 0 \<and> nonneg_primfun_list xs)"

fun iszero_primfun_list where
  "iszero_primfun_list [] \<longleftrightarrow> True"
| "iszero_primfun_list ((_,x)#xs) \<longleftrightarrow> x = 0 \<and> iszero_primfun_list xs"


definition "group_primfuns \<equiv> groupsort.group_sort fst merge_primfun"

lemma list_ConsCons_induct:
  assumes "P []" "\<And>x. P [x]" "\<And>x y xs. P (y#xs) \<Longrightarrow> P (x#y#xs)"
  shows   "P xs"
proof (induction xs rule: length_induct)
  case (1 xs)
  show ?case
  proof (cases xs)
    case (Cons x xs')
    note A = this
    from assms 1 show ?thesis
    proof (cases xs')
      case (Cons y xs'')
      with 1 A have "P (y#xs'')" by simp
      with Cons A assms show ?thesis by simp
    qed (simp add: assms A)
  qed (simp add: assms)
qed


lemma landau_function_family_chain_primfuns:
  assumes "sorted (map fst fs)"
  assumes "distinct (map fst fs)"
  shows   "landau_function_family_chain at_top fs (eval_primfun' o fst)"
proof (standard, goal_cases)
  case 3
  from assms show ?case
  proof (induction fs rule: list_ConsCons_induct)
    case (2 g)
    from eval_primfun'_at_top[of "fst g"]
      have "eval_primfun' (fst g) \<in> \<omega>(\<lambda>_. 1)"
      by (intro smallomegaI_filterlim_at_infinity filterlim_at_top_imp_at_infinity) simp
    thus ?case by (simp add: smallomega_iff_smallo)
  next
    case (3 f g gs)
    thus ?case by (auto simp: primfun_dominates sorted_Cons)
  qed simp
qed (auto simp: eval_primfun'_at_top)

interpretation groupsort_primfun: groupsort fst merge_primfun eval_primfuns
proof (standard, goal_cases)
  case (1 x y)
  thus ?case by (induction x y rule: merge_primfun.induct) simp_all
next
  case (2 fs gs)
  show ?case
  proof
    fix x
    have "eval_primfuns fs x = fold op* (map (\<lambda>f. eval_primfun f x) fs) 1"
      unfolding eval_primfuns_def by (simp add: fold_plus_prod_list_rev)
    also have "fold op* (map (\<lambda>f. eval_primfun f x) fs) = fold op* (map (\<lambda>f. eval_primfun f x) gs)"
      using 2 by (intro fold_multiset_equiv ext) auto
    also have "... 1 = eval_primfuns gs x"
      unfolding eval_primfuns_def by (simp add: fold_plus_prod_list_rev)
    finally show "eval_primfuns fs x = eval_primfuns gs x" .
  qed
qed (auto simp: fun_eq_iff eval_merge_primfun eval_primfuns_def)

lemma nonneg_primfun_list_iff: "nonneg_primfun_list fs = nonneg_list (map snd fs)"
  by (induction fs rule: nonneg_primfun_list.induct) simp_all

lemma pos_primfun_list_iff: "pos_primfun_list fs = pos_list (map snd fs)"
  by (induction fs rule: pos_primfun_list.induct) simp_all

lemma iszero_primfun_list_iff: "iszero_primfun_list fs = list_all (op= 0) (map snd fs)"
  by (induction fs rule: iszero_primfun_list.induct) simp_all

lemma landau_primfuns_iff:
  "((\<lambda>_. 1) \<in> O(eval_primfuns fs)) = nonneg_primfun_list (group_primfuns fs)" (is "?A")
  "((\<lambda>_. 1) \<in> o(eval_primfuns fs)) = pos_primfun_list (group_primfuns fs)" (is "?B")
  "((\<lambda>_. 1) \<in> \<Theta>(eval_primfuns fs)) = iszero_primfun_list (group_primfuns fs)" (is "?C")
proof-
  interpret landau_function_family_chain at_top "group_primfuns fs" snd "eval_primfun' o fst"
    by (rule landau_function_family_chain_primfuns)
       (simp_all add: group_primfuns_def groupsort_primfun.sorted_group_sort
                      groupsort_primfun.distinct_group_sort)

  have "(\<lambda>_. 1) \<in> O(eval_primfuns fs) \<longleftrightarrow> (\<lambda>_. 1) \<in> O(eval_primfuns (group_primfuns fs))"
    by (simp_all add: groupsort_primfun.g_group_sort group_primfuns_def)
  also have "... \<longleftrightarrow> nonneg_list (map snd (group_primfuns fs))" using bigo_iff
    by (simp add: eval_primfuns_def[abs_def] eval_primfun_altdef)
  finally show ?A by (simp add: nonneg_primfun_list_iff)

  have "(\<lambda>_. 1) \<in> o(eval_primfuns fs) \<longleftrightarrow> (\<lambda>_. 1) \<in> o(eval_primfuns (group_primfuns fs))"
    by (simp_all add: groupsort_primfun.g_group_sort group_primfuns_def)
  also have "... \<longleftrightarrow> pos_list (map snd (group_primfuns fs))" using smallo_iff
    by (simp add: eval_primfuns_def[abs_def] eval_primfun_altdef)
  finally show ?B by (simp add: pos_primfun_list_iff)

  have "(\<lambda>_. 1) \<in> \<Theta>(eval_primfuns fs) \<longleftrightarrow> (\<lambda>_. 1) \<in> \<Theta>(eval_primfuns (group_primfuns fs))"
    by (simp_all add: groupsort_primfun.g_group_sort group_primfuns_def)
  also have "... \<longleftrightarrow> list_all (op= 0) (map snd (group_primfuns fs))" using bigtheta_iff
    by (simp add: eval_primfuns_def[abs_def] eval_primfun_altdef)
  finally show ?C by (simp add: iszero_primfun_list_iff)
qed


lemma LANDAU_PROD_bigo_iff:
  "LANDAU_PROD (bigo at_top) c1 c2 fs \<longleftrightarrow> c1 = 0 \<or> (c2 \<noteq> 0 \<and> nonneg_primfun_list (group_primfuns fs))"
  unfolding LANDAU_PROD_def
  by (cases "c1 = 0", simp, cases "c2 = 0", simp) (simp_all add: landau_primfuns_iff)

lemma LANDAU_PROD_smallo_iff:
  "LANDAU_PROD (smallo at_top) c1 c2 fs \<longleftrightarrow> c1 = 0 \<or> (c2 \<noteq> 0 \<and> pos_primfun_list (group_primfuns fs))"
  unfolding LANDAU_PROD_def
  by (cases "c1 = 0", simp, cases "c2 = 0", simp) (simp_all add: landau_primfuns_iff)

lemma LANDAU_PROD_bigtheta_iff:
  "LANDAU_PROD (bigtheta at_top) c1 c2 fs \<longleftrightarrow> (c1 = 0 \<and> c2 = 0) \<or> (c1 \<noteq> 0 \<and> c2 \<noteq> 0 \<and>
     iszero_primfun_list (group_primfuns fs))"
proof-
  have A: "\<And>P x. (x = 0 \<Longrightarrow> P) \<Longrightarrow> (x \<noteq> 0 \<Longrightarrow> P) \<Longrightarrow> P" by blast
  {
    assume "eventually (\<lambda>x. eval_primfuns fs x = 0) at_top"
    with eval_primfuns_nonzero[of fs] have "eventually (\<lambda>x::real. False) at_top"
      by eventually_elim simp
    hence False by simp
  } note B = this
  show ?thesis by (rule A[of c1, case_product A[of c2]])
                  (insert B, auto simp: LANDAU_PROD_def landau_primfuns_iff)
qed

lemmas LANDAU_PROD_iff = LANDAU_PROD_bigo_iff LANDAU_PROD_smallo_iff LANDAU_PROD_bigtheta_iff


lemmas landau_real_prod_simps [simp] =
  groupsort_primfun.group_part_def
  group_primfuns_def groupsort_primfun.group_sort.simps
  groupsort_primfun.group_part_aux.simps pos_primfun_list.simps
  nonneg_primfun_list.simps iszero_primfun_list.simps

end
