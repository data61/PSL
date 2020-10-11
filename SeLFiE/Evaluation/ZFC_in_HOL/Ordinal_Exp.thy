section \<open>Exponentiation of ordinals\<close>

theory Ordinal_Exp
  imports Kirby

begin

text \<open>Source: Schlöder, Julian.  Ordinal Arithmetic; available online at
    \url{http://www.math.uni-bonn.de/ag/logik/teaching/2012WS/Set%20theory/oa.pdf}\<close>

definition oexp :: "[V,V] \<Rightarrow> V" (infixr "\<up>" 80)
  where "oexp a b \<equiv> transrec (\<lambda>f x. if x=0 then 1
                                    else if Limit x then if a=0 then 0 else SUP \<xi> \<in> elts x. f \<xi>
                                    else f (\<Squnion>(elts x)) * a) b"

text \<open>@{term "0\<up>\<omega> = 1"} if we don't make a special case for Limit ordinals and zero\<close>


lemma oexp_0_right [simp]: "\<alpha>\<up>0 = 1"
  by (simp add: def_transrec [OF oexp_def])

lemma oexp_succ [simp]: "Ord \<beta> \<Longrightarrow> \<alpha>\<up>(succ \<beta>) = \<alpha>\<up>\<beta> * \<alpha>"
  by (simp add: def_transrec [OF oexp_def])

lemma oexp_Limit: "Limit \<beta> \<Longrightarrow> \<alpha>\<up>\<beta> = (if \<alpha>=0 then 0 else SUP \<xi> \<in> elts \<beta>. \<alpha>\<up>\<xi>)"
  by (auto simp: def_transrec [OF oexp_def, of _ \<beta>])

lemma oexp_1_right [simp]: "\<alpha>\<up>1 = \<alpha>"
  using one_V_def oexp_succ by fastforce

lemma oexp_1 [simp]: "Ord \<alpha> \<Longrightarrow> 1\<up>\<alpha> = 1"
  by (induction rule: Ord_induct3) (use Limit_def oexp_Limit in auto)

lemma oexp_0 [simp]: "Ord \<alpha> \<Longrightarrow> 0\<up>\<alpha> = (if \<alpha> = 0 then 1 else 0)"
  by (induction rule: Ord_induct3) (use Limit_def oexp_Limit in auto)

lemma oexp_eq_0_iff [simp]:
  assumes "Ord \<beta>" shows "\<alpha>\<up>\<beta> = 0 \<longleftrightarrow> \<alpha>=0 \<and> \<beta>\<noteq>0"
  using \<open>Ord \<beta>\<close>
proof (induction rule: Ord_induct3)
  case (Limit \<mu>)
  then show ?case
    using Limit_def oexp_Limit by auto
qed auto

lemma oexp_gt_0_iff [simp]:
  assumes "Ord \<beta>" shows "\<alpha>\<up>\<beta> > 0 \<longleftrightarrow> \<alpha>>0 \<or> \<beta>=0"
  by (simp add: assms less_V_def)

lemma ord_of_nat_oexp: "ord_of_nat (m^n) = ord_of_nat m\<up>ord_of_nat n"
proof (induction n)
  case (Suc n)
  then show ?case
    by (simp add: mult.commute [of m]) (simp add: ord_of_nat_mult)
qed auto

lemma omega_closed_oexp [intro]:
  assumes "\<alpha> \<in> elts \<omega>" "\<beta> \<in> elts \<omega>" shows "\<alpha>\<up>\<beta> \<in> elts \<omega>"
proof -
  obtain m n where "\<alpha> = ord_of_nat m" "\<beta> = ord_of_nat n"
    using assms elts_\<omega> by auto
  then have "\<alpha>\<up>\<beta> = ord_of_nat (m^n)"
    by (simp add: ord_of_nat_oexp)
  then show ?thesis
    by (simp add: \<omega>_def)
qed


lemma Ord_oexp [simp]:
  assumes "Ord \<alpha>" "Ord \<beta>" shows "Ord (\<alpha>\<up>\<beta>)"
  using \<open>Ord \<beta>\<close>
proof (induction rule: Ord_induct3)
  case (Limit \<alpha>)
  then show ?case
    by (auto simp: oexp_Limit image_iff intro: Ord_Sup)
qed (auto intro: Ord_mult assms)

text \<open>Lemma 3.19\<close>
lemma le_oexp:
  assumes "Ord \<alpha>" "Ord \<beta>" "\<beta> \<noteq> 0" shows "\<alpha> \<le> \<alpha>\<up>\<beta>"
  using \<open>Ord \<beta>\<close> \<open>\<beta> \<noteq> 0\<close>
proof (induction rule: Ord_induct3)
  case (succ \<beta>)
  then show ?case
    by simp (metis \<open>Ord \<alpha>\<close> le_0 le_mult mult.left_neutral oexp_0_right order_refl order_trans)
next
  case (Limit \<mu>)
  then show ?case
    by (metis Limit_def Limit_eq_Sup_self ZFC_in_HOL.Sup_upper eq_iff image_eqI image_ident oexp_1_right oexp_Limit replacement small_elts one_V_def)
qed auto


text \<open>Lemma 3.20\<close>
lemma le_oexp':
  assumes "Ord \<alpha>" "1 < \<alpha>" "Ord \<beta>" shows "\<beta> \<le> \<alpha>\<up>\<beta>"
proof (cases "\<beta> = 0")
  case True
  then show ?thesis
    by auto
next
  case False
  show ?thesis
    using \<open>Ord \<beta>\<close>
  proof (induction rule: Ord_induct3)
    case 0
    then show ?case
      by auto
  next
    case (succ \<gamma>)
    then have "\<alpha>\<up>\<gamma> * 1 < \<alpha>\<up>\<gamma> * \<alpha>"
      using \<open>Ord \<alpha>\<close> \<open>1 < \<alpha>\<close>
      by (metis le_mult less_V_def mult.right_neutral mult_cancellation not_less_0 oexp_eq_0_iff succ.hyps)
    then have " \<gamma> < \<alpha>\<up>succ \<gamma>"
      using succ.IH succ.hyps by auto
    then show ?case
      using False \<open>Ord \<alpha>\<close> \<open>1 < \<alpha>\<close> succ
      by (metis Ord_mem_iff_lt Ord_oexp Ord_succ elts_succ insert_subset less_eq_V_def less_imp_le)
  next
    case (Limit \<mu>)
    with False \<open>1 < \<alpha>\<close> show ?case
      by (force simp: Limit_def oexp_Limit intro: elts_succ)
  qed
qed


lemma oexp_Limit_le:
  assumes "\<beta> < \<gamma>" "Limit \<gamma>" "Ord \<beta>" "\<alpha> > 0" shows "\<alpha>\<up>\<beta> \<le> \<alpha>\<up>\<gamma>"
proof -
  have "Ord \<gamma>"
    using Limit_def assms(2) by blast
  with assms show ?thesis
    using Ord_mem_iff_lt ZFC_in_HOL.Sup_upper oexp_Limit by auto
qed

proposition oexp_less:
  assumes \<beta>: "\<beta> \<in> elts \<gamma>" and "Ord \<gamma>" and \<alpha>: "\<alpha> > 1" "Ord \<alpha>" shows "\<alpha>\<up>\<beta> < \<alpha>\<up>\<gamma>"
proof -
  obtain "\<beta> < \<gamma>" "Ord \<beta>"
    using Ord_in_Ord OrdmemD assms by auto
  have gt0: "\<alpha>\<up>\<beta> > 0"
    using \<open>Ord \<beta>\<close> \<alpha> dual_order.order_iff_strict by auto
  show ?thesis
    using \<open>Ord \<gamma>\<close> \<beta>
  proof (induction rule: Ord_induct3)
    case 0
    then show ?case
      by auto
  next
    case (succ \<delta>)
    then consider "\<beta> = \<delta>" | "\<beta> < \<delta>"
      using OrdmemD elts_succ by blast
    then show ?case
    proof cases
      case 1
      then have "(\<alpha>\<up>\<beta>) * 1 < (\<alpha>\<up>\<delta>) * \<alpha>"
        using Ord_1 Ord_oexp \<alpha> gt0 mult_cancel_less_iff succ.hyps by metis
      then show ?thesis
        by (simp add: succ.hyps)
    next
      case 2
      then have "(\<alpha>\<up>\<delta>) * 1 < (\<alpha>\<up>\<delta>) * \<alpha>"
        by (meson Ord_1 Ord_mem_iff_lt Ord_oexp \<open>Ord \<beta>\<close> \<alpha> gt0 less_trans mult_cancel_less_iff succ)
      with 2 show ?thesis
        using Ord_mem_iff_lt \<open>Ord \<beta>\<close> succ by auto
    qed
  next
    case (Limit \<gamma>)
    then obtain "Ord \<gamma>" "succ \<beta> < \<gamma>"
      using Limit_def Ord_in_Ord OrdmemD assms by auto
    have "\<alpha>\<up>\<beta> = (\<alpha>\<up>\<beta>) * 1"
      by simp
    also have "\<dots> < (\<alpha>\<up>\<beta>) * \<alpha>"
      using Ord_oexp \<open>Ord \<beta>\<close> assms gt0 mult_cancel_less_iff by blast
    also have "\<dots> = \<alpha>\<up>succ \<beta>"
      by (simp add: \<open>Ord \<beta>\<close>)
    also have "\<dots> \<le> (SUP \<xi> \<in> elts \<gamma>. \<alpha>\<up>\<xi>)"
    proof -
      have "succ \<beta> \<in> elts \<gamma>"
        using Limit.hyps Limit.prems Limit_def by auto
      then show ?thesis
        by (simp add: ZFC_in_HOL.Sup_upper)
    qed
    finally
    have "\<alpha>\<up>\<beta> < (SUP \<xi> \<in> elts \<gamma>. \<alpha>\<up>\<xi>)" .
    then show ?case
      using Limit.hyps oexp_Limit \<open>\<alpha> > 1\<close> by auto
  qed
qed

corollary oexp_less_iff:
  assumes "\<alpha> > 0" "Ord \<alpha>" "Ord \<beta>" "Ord \<gamma>" shows "\<alpha>\<up>\<beta> < \<alpha>\<up>\<gamma> \<longleftrightarrow> \<beta> \<in> elts \<gamma> \<and> \<alpha> > 1"
proof safe
  show "\<beta> \<in> elts \<gamma>" "1 < \<alpha>"
    if "\<alpha>\<up>\<beta> < \<alpha>\<up>\<gamma>"
  proof -
    show "\<alpha> > 1"
    proof (rule ccontr)
      assume "\<not> \<alpha> > 1"
      then consider "\<alpha>=0" | "\<alpha>=1"
        using \<open>Ord \<alpha>\<close> less_V_def mem_0_Ord by fastforce
      then show False
        by cases (use that \<open>\<alpha> > 0\<close> \<open>Ord \<beta>\<close> \<open>Ord \<gamma>\<close> in \<open>auto split: if_split_asm\<close>)
    qed
    show \<beta>: "\<beta> \<in> elts \<gamma>"
    proof (rule ccontr)
      assume "\<beta> \<notin> elts \<gamma>"
      then have "\<gamma> \<le> \<beta>"
        by (meson Ord_linear_le Ord_mem_iff_lt assms less_le_not_le)
      then consider "\<gamma> = \<beta>" | "\<gamma> < \<beta>"
        using less_V_def by blast
      then show False
      proof cases
        case 1
        then show ?thesis
          using that by blast
      next
        case 2
        with \<open>\<alpha> > 1\<close> have "\<alpha>\<up>\<gamma> < \<alpha>\<up>\<beta>"
          by (simp add: Ord_mem_iff_lt assms oexp_less)
        with that show ?thesis
          by auto
      qed
    qed
  qed
  show "\<alpha>\<up>\<beta> < \<alpha>\<up>\<gamma>" if "\<beta> \<in> elts \<gamma>" "1 < \<alpha>"
    using that by (simp add: assms oexp_less)
qed

lemma \<omega>_oexp_iff [simp]: "\<lbrakk>Ord \<alpha>; Ord \<beta>\<rbrakk> \<Longrightarrow> \<omega>\<up>\<alpha> = \<omega>\<up>\<beta> \<longleftrightarrow> \<alpha>=\<beta>"
  by (metis Ord_\<omega> Ord_linear \<omega>_gt1 less_irrefl oexp_less)

lemma Limit_oexp:
  assumes "Limit \<gamma>" "Ord \<alpha>" "\<alpha> > 1" shows "Limit (\<alpha>\<up>\<gamma>)"
  unfolding Limit_def
proof safe
  show O\<alpha>\<gamma>: "Ord (\<alpha>\<up>\<gamma>)"
    using Limit_def Ord_oexp \<open>Limit \<gamma>\<close> assms(2) by blast
  show 0: "0 \<in> elts (\<alpha>\<up>\<gamma>)"
    using Limit_def oexp_Limit \<open>Limit \<gamma>\<close> \<open>\<alpha> > 1\<close> by fastforce
  have "Ord \<gamma>"
    using Limit_def \<open>Limit \<gamma>\<close> by blast
  fix x
  assume x: "x \<in> elts (\<alpha>\<up>\<gamma>)"
  with \<open>Limit \<gamma>\<close> \<open>\<alpha> > 1\<close>
  obtain \<beta> where "\<beta> < \<gamma>" "Ord \<beta>" "Ord x" and x\<beta>: "x \<in> elts (\<alpha>\<up>\<beta>)"
    apply (simp add: oexp_Limit split: if_split_asm)
    using Ord_in_Ord OrdmemD \<open>Ord \<gamma>\<close> O\<alpha>\<gamma> x by blast
  then have O\<alpha>\<beta>: "Ord (\<alpha>\<up>\<beta>)"
    using Ord_oexp assms(2) by blast
  have "\<beta> \<in> elts \<gamma>"
    by (simp add: Ord_mem_iff_lt \<open>Ord \<beta>\<close> \<open>Ord \<gamma>\<close> \<open>\<beta> < \<gamma>\<close>)
  moreover have "\<alpha> \<noteq> 0"
    using \<open>\<alpha> > 1\<close> by blast
  ultimately have \<alpha>\<beta>\<gamma>: "\<alpha>\<up>\<beta> \<le> \<alpha>\<up>\<gamma>"
    by (simp add: Sup_upper oexp_Limit \<open>Limit \<gamma>\<close>)
  have "succ x \<le> \<alpha>\<up>\<beta>"
    by (simp add: OrdmemD O\<alpha>\<beta> \<open>Ord x\<close> succ_le_iff x\<beta>)
  then consider "succ x < \<alpha>\<up>\<beta>" | "succ x = \<alpha>\<up>\<beta>"
    using le_neq_trans by blast
  then show "succ x \<in> elts (\<alpha>\<up>\<gamma>)"
  proof cases
    case 1
    with \<alpha>\<beta>\<gamma> show ?thesis
      using O\<alpha>\<beta> Ord_mem_iff_lt \<open>Ord x\<close> by blast
  next
    case 2
    then have "succ \<beta> < \<gamma>"
      using Limit_def OrdmemD \<open>\<beta> \<in> elts \<gamma>\<close> assms(1) by auto
    have ge1: "1 \<le> \<alpha>\<up>\<beta>"
      by (metis "2" Ord_0 \<open>Ord x\<close> le_0 le_succ_iff one_V_def)
    have "succ x < succ (\<alpha>\<up>\<beta>)"
      using "2" O\<alpha>\<beta> succ_le_iff by auto
    also have "\<dots> \<le> (\<alpha>\<up>\<beta>) + (\<alpha>\<up>\<beta>)"
      using ge1 by (simp add: succ_eq_add1)
    also have "\<dots> = (\<alpha>\<up>\<beta>) * succ (succ 0)"
      by (simp add: mult_succ)
    also have "\<dots> \<le> (\<alpha>\<up>\<beta>) * \<alpha>"
      using O\<alpha>\<beta> Ord_succ assms(2) assms(3) one_V_def succ_le_iff by auto
    also have "\<dots> = \<alpha>\<up>succ \<beta>"
      by (simp add: \<open>Ord \<beta>\<close>)
    also have "\<dots> \<le> \<alpha>\<up>\<gamma>"
      by (meson Limit_def \<open>\<beta> \<in> elts \<gamma>\<close> assms dual_order.order_iff_strict oexp_less)
  finally show ?thesis
    by (simp add: "2" O\<alpha>\<beta> O\<alpha>\<gamma> Ord_mem_iff_lt)
  qed
qed



lemma oexp_mono:
  assumes \<alpha>: "Ord \<alpha>" "\<alpha> \<noteq> 0" and \<beta>: "Ord \<beta>" "\<gamma> \<sqsubseteq> \<beta>" shows "\<alpha>\<up>\<gamma> \<le> \<alpha>\<up>\<beta>"
  using \<beta>
proof (induction rule: Ord_induct3)
  case 0
  then show ?case
    by simp
next
  case (succ \<beta>)
  with \<alpha> le_mult show ?case
    by (auto simp: le_TC_succ)
next
  case (Limit \<mu>)
  then have "\<alpha>\<up>\<gamma> \<le> \<Squnion> ((\<up>) \<alpha> ` elts \<mu>)"
    using Limit.hyps Ord_less_TC_mem \<open>\<alpha> \<noteq> 0\<close> le_TC_def by (auto simp: oexp_Limit Limit_def)
  then show ?case
    using \<alpha> by (simp add: oexp_Limit Limit.hyps)
qed

lemma oexp_mono_le:
  assumes "\<gamma> \<le> \<beta>" "\<alpha> \<noteq> 0" "Ord \<alpha>" "Ord \<beta>" "Ord \<gamma>" shows "\<alpha>\<up>\<gamma> \<le> \<alpha>\<up>\<beta>"
  by (simp add: assms oexp_mono vle2 vle_iff_le_Ord)

lemma oexp_sup:
  assumes "\<alpha> \<noteq> 0" "Ord \<alpha>" "Ord \<beta>" "Ord \<gamma>" shows "\<alpha>\<up>(\<beta> \<squnion> \<gamma>) = \<alpha>\<up>\<beta> \<squnion> \<alpha>\<up>\<gamma>"
  by (metis Ord_linear_le assms oexp_mono_le sup.absorb2 sup.orderE)

lemma oexp_Sup:
  assumes \<alpha>: "\<alpha> \<noteq> 0" "Ord \<alpha>" and X: "X \<subseteq> ON" "small X" "X \<noteq> {}" shows "\<alpha>\<up>\<Squnion> X = \<Squnion> ((\<up>) \<alpha> ` X)"
proof (rule order_antisym)
  show "\<Squnion> ((\<up>) \<alpha> ` X) \<le> \<alpha>\<up>\<Squnion> X"
    by (metis ON_imp_Ord Ord_Sup ZFC_in_HOL.Sup_upper assms cSUP_least oexp_mono_le)
next
  have "Ord (Sup X)"
    using Ord_Sup X by auto
  then show "\<alpha>\<up>\<Squnion> X \<le> \<Squnion> ((\<up>) \<alpha> ` X)"
  proof (cases rule: Ord_cases)
    case 0
    then show ?thesis
      using X dual_order.antisym by fastforce
  next
    case (succ \<beta>)
    then show ?thesis
      using ZFC_in_HOL.Sup_upper X succ_in_Sup_Ord by auto
  next
    case limit
    show ?thesis
    proof (clarsimp simp: assms oexp_Limit limit)
      fix x y z
      assume x: "x \<in> elts (\<alpha> \<up> y)" and "z \<in> X" "y \<in> elts z"
      then have "\<alpha> \<up> y \<le> \<alpha> \<up> z"
        by (meson ON_imp_Ord Ord_in_Ord OrdmemD \<alpha> \<open>X \<subseteq> ON\<close> le_less oexp_mono_le)
      with x have "x \<in> elts (\<alpha> \<up> z)" by blast
      then show "\<exists>u\<in>X. x \<in> elts (\<alpha> \<up> u)"
        using \<open>z \<in> X\<close> by blast
    qed
  qed
qed


lemma omega_le_Limit:
  assumes "Limit \<mu>" shows "\<omega> \<le> \<mu>"
proof
  fix \<rho>
  assume "\<rho> \<in> elts \<omega>"
  then obtain n where "\<rho> = ord_of_nat n"
    using elts_\<omega> by auto
  have "ord_of_nat n \<in> elts \<mu>"
    by (induction n) (use Limit_def assms in auto)
  then show "\<rho> \<in> elts \<mu>"
    using \<open>\<rho> = ord_of_nat n\<close> by auto
qed

lemma finite_omega_power [simp]:
  assumes "1 < n" "n \<in> elts \<omega>" shows "n\<up>\<omega> = \<omega>"
proof (rule order_antisym)
  have "\<Squnion> ((\<up>) (ord_of_nat k) ` elts \<omega>) \<le> \<omega>" for k
  proof (induction k)
    case 0
    then show ?case
      by auto
  next
    case (Suc k)
    then show ?case
      by (metis Ord_\<omega> OrdmemD Sup_eq_0_iff ZFC_in_HOL.SUP_le_iff le_0 le_less omega_closed_oexp ord_of_nat_\<omega>)
  qed
  then show "n\<up>\<omega> \<le> \<omega>"
    using assms
    by (simp add: elts_\<omega> oexp_Limit) metis
  show "\<omega> \<le> n\<up>\<omega>"
    using Ord_in_Ord assms le_oexp' by blast
qed


proposition oexp_add:
  assumes "Ord \<alpha>" "Ord \<beta>" "Ord \<gamma>" shows "\<alpha>\<up>(\<beta> + \<gamma>) = \<alpha>\<up>\<beta> * \<alpha>\<up>\<gamma>"
proof (cases \<open>\<alpha> = 0\<close>)
  case True
  then show ?thesis
    using assms by simp
next
  case False
  show ?thesis
    using \<open>Ord \<gamma>\<close>
  proof (induction rule: Ord_induct3)
    case 0
    then show ?case
      by auto
  next
    case (succ \<xi>)
    then show ?case
      using \<open>Ord \<beta>\<close> by (auto simp: plus_V_succ_right mult.assoc)
  next
    case (Limit \<mu>)
    have "\<alpha>\<up>(\<beta> + (SUP \<xi>\<in>elts \<mu>. \<xi>)) = (SUP \<xi>\<in>elts (\<beta> + \<mu>). \<alpha>\<up>\<xi>)"
      by (simp add: Limit.hyps oexp_Limit assms False)
    also have "\<dots> = (SUP \<xi> \<in> {\<xi>. Ord \<xi> \<and> \<beta> + \<xi> < \<beta> + \<mu>}. \<alpha>\<up>(\<beta> + \<xi>))"
    proof (rule Sup_eq_Sup)
      show "(\<lambda>\<xi>. \<alpha>\<up>(\<beta> + \<xi>)) ` {\<xi>. Ord \<xi> \<and> \<beta> + \<xi> < \<beta> + \<mu>} \<subseteq> (\<up>) \<alpha> ` elts (\<beta> + \<mu>)"
        using Limit.hyps Limit_def Ord_mem_iff_lt imageI by blast
      fix x
      assume "x \<in> (\<up>) \<alpha> ` elts (\<beta> + \<mu>)"
      then obtain \<xi> where \<xi>: "\<xi> \<in> elts (\<beta> + \<mu>)" and x: "x = \<alpha>\<up>\<xi>"
        by auto
      have "\<exists>\<gamma>. Ord \<gamma> \<and> \<gamma> < \<mu> \<and> \<alpha>\<up>\<xi> \<le> \<alpha>\<up>(\<beta> + \<gamma>)"
      proof (rule mem_plus_V_E [OF \<xi>])
        assume "\<xi> \<in> elts \<beta>"
        then have "\<alpha>\<up>\<xi> \<le> \<alpha>\<up>\<beta>"
          by (meson arg_subset_TC assms False le_TC_def less_TC_def oexp_mono vsubsetD)
        with zero_less_Limit [OF \<open>Limit \<mu>\<close>]
        show "\<exists>\<gamma>. Ord \<gamma> \<and> \<gamma> < \<mu> \<and> \<alpha>\<up>\<xi> \<le> \<alpha>\<up>(\<beta> + \<gamma>)"
          by force
      next
        fix \<delta>
        assume "\<delta> \<in> elts \<mu>" and "\<xi> = \<beta> + \<delta>"
        have "Ord \<delta>"
          using Limit.hyps Limit_def Ord_in_Ord \<open>\<delta> \<in> elts \<mu>\<close> by blast
        moreover have "\<delta> < \<mu>"
          using Limit.hyps Limit_def OrdmemD \<open>\<delta> \<in> elts \<mu>\<close> by auto
        ultimately show "\<exists>\<gamma>. Ord \<gamma> \<and> \<gamma> < \<mu> \<and> \<alpha>\<up>\<xi> \<le> \<alpha>\<up>(\<beta> + \<gamma>)"
          using \<open>\<xi> = \<beta> + \<delta>\<close> by blast
      qed
      then show "\<exists>y\<in>(\<lambda>\<xi>. \<alpha>\<up>(\<beta> + \<xi>)) ` {\<xi>. Ord \<xi> \<and> \<beta> + \<xi> < \<beta> + \<mu>}. x \<le> y"
        using x by auto
    qed auto
    also have "\<dots> = (SUP \<xi>\<in>elts \<mu>. \<alpha>\<up>(\<beta> + \<xi>))"
      using \<open>Limit \<mu>\<close>
      by (simp add: Ord_Collect_lt Limit_def)
    also have "\<dots> = (SUP \<xi>\<in>elts \<mu>. \<alpha>\<up>\<beta> * \<alpha>\<up>\<xi>)"
      using Limit.IH by auto
    also have "\<dots> = \<alpha>\<up>\<beta> * \<alpha>\<up>(SUP \<xi>\<in>elts \<mu>. \<xi>)"
      using \<open>\<alpha> \<noteq> 0\<close> Limit.hyps
      by (simp add: image_image oexp_Limit mult_Sup_distrib)
    finally show ?case .
  qed
qed

proposition oexp_mult:
  assumes "Ord \<alpha>" "Ord \<beta>" "Ord \<gamma>" shows "\<alpha>\<up>(\<beta> * \<gamma>) = (\<alpha>\<up>\<beta>)\<up>\<gamma>"
proof (cases "\<alpha> = 0 \<or> \<beta> = 0")
  case True
  then show ?thesis
    by (auto simp: \<open>Ord \<beta>\<close> \<open>Ord \<gamma>\<close>)
next
  case False
  show ?thesis
    using \<open>Ord \<gamma>\<close>
  proof (induction rule: Ord_induct3)
    case 0
    then show ?case
      by auto
  next
    case succ
    then show ?case
      using assms by (auto simp: mult_succ oexp_add)
  next
    case (Limit \<mu>)
    have Lim: "Limit (\<Squnion> ((*) \<beta> ` elts \<mu>))"
      unfolding Limit_def
    proof (intro conjI allI impI)
      show "Ord (\<Squnion> ((*) \<beta> ` elts \<mu>))"
        using Limit.hyps Limit_def Ord_in_Ord \<open>Ord \<beta>\<close> by (auto intro: Ord_Sup)
      have "succ 0 \<in> elts \<mu>"
        using Limit.hyps Limit_def by blast
      then show "0 \<in> elts (\<Squnion> ((*) \<beta> ` elts \<mu>))"
        using False \<open>Ord \<beta>\<close> mem_0_Ord by force
      show "succ y \<in> elts (\<Squnion> ((*) \<beta> ` elts \<mu>))"
        if "y \<in> elts (\<Squnion> ((*) \<beta> ` elts \<mu>))" for y
        using that False Limit.hyps
        apply (clarsimp simp: Limit_def)
        by (metis Ord_in_Ord Ord_linear Ord_mem_iff_lt Ord_mult Ord_succ assms(2) less_V_def mult_cancellation mult_succ not_add_mem_right succ_le_iff succ_ne_self)
    qed
    have "\<alpha>\<up>(\<beta> * (SUP \<xi>\<in>elts \<mu>. \<xi>)) = \<alpha>\<up>\<Squnion> ((*) \<beta> ` elts \<mu>)"
      by (simp add: mult_Sup_distrib)
    also have "\<dots> = \<Squnion> (\<Union>x\<in>elts \<mu>. (\<up>) \<alpha> ` elts (\<beta> * x))"
      using False Lim oexp_Limit by fastforce
    also have "\<dots> = (SUP x\<in>elts \<mu>. \<alpha>\<up>(\<beta> * x))"
    proof (rule Sup_eq_Sup)
      show "(\<lambda>x. \<alpha>\<up>(\<beta> * x)) ` elts \<mu> \<subseteq> (\<Union>x\<in>elts \<mu>. (\<up>) \<alpha> ` elts (\<beta> * x))"
        using \<open>Ord \<alpha>\<close> \<open>Ord \<beta>\<close> False Limit
        apply clarsimp
        by (metis Limit_def elts_succ imageI insertI1 mem_0_Ord mult_add_mem_0)
      show "\<exists>y\<in>(\<lambda>x. \<alpha>\<up>(\<beta> * x)) ` elts \<mu>. x \<le> y"
        if "x \<in> (\<Union>x\<in>elts \<mu>. (\<up>) \<alpha> ` elts (\<beta> * x))" for x
        using that \<open>Ord \<alpha>\<close> \<open>Ord \<beta>\<close> False Limit
        by clarsimp (metis Limit_def Ord_in_Ord Ord_mult VWO_TC_le mem_imp_VWO oexp_mono)
    qed auto
    also have "\<dots> = \<Squnion> ((\<up>) (\<alpha>\<up>\<beta>) ` elts (SUP \<xi>\<in>elts \<mu>. \<xi>))"
      using Limit.IH Limit.hyps by auto
    also have "\<dots> = (\<alpha>\<up>\<beta>)\<up>(SUP \<xi>\<in>elts \<mu>. \<xi>)"
      using False Limit.hyps oexp_Limit \<open>Ord \<beta>\<close> by auto
    finally show ?case .
  qed
qed

lemma Limit_omega_oexp:
  assumes "Ord \<delta>" "\<delta> \<noteq> 0"
  shows "Limit (\<omega>\<up>\<delta>)"
  using assms
proof (cases \<delta> rule: Ord_cases)
  case 0
  then show ?thesis
    using assms(2) by blast
next
  case (succ l)
  have *: "succ \<beta> \<in> elts (\<omega>\<up>l * n + \<omega>\<up>l)"
    if n: "n \<in> elts \<omega>" and \<beta>: "\<beta> \<in> elts (\<omega>\<up>l * n)" for n \<beta>
  proof -
    obtain "Ord n" "Ord \<beta>"
      by (meson Ord_\<omega> Ord_in_Ord Ord_mult Ord_oexp \<beta> n succ(1))
    obtain oo: "Ord (\<omega>\<up>l)" "Ord (\<omega>\<up>l * n)"
      by (simp add: \<open>Ord n\<close> succ(1))
    moreover have f4: "\<beta> < \<omega>\<up>l * n"
      using oo Ord_mem_iff_lt \<open>Ord \<beta>\<close> \<open>\<beta> \<in> elts (\<omega>\<up>l * n)\<close> by blast
    moreover have f5: "Ord (succ \<beta>)"
      using \<open>Ord \<beta>\<close> by blast
    moreover have "\<omega>\<up>l \<noteq> 0"
      using oexp_eq_0_iff omega_nonzero succ(1) by blast
    ultimately show ?thesis
      by (metis add_less_cancel_left Ord_\<omega> Ord_add Ord_mem_iff_lt OrdmemD \<open>Ord \<beta>\<close> add.right_neutral dual_order.strict_trans2 oexp_gt_0_iff succ(1) succ_le_iff zero_in_omega)
  qed
  show ?thesis
    using succ
    apply (clarsimp simp: Limit_def mem_0_Ord)
    apply (simp add: mult_Limit)
    by (metis * mult_succ succ_in_omega)
next
  case limit
  then show ?thesis
    by (metis Limit_oexp Ord_\<omega> OrdmemD one_V_def succ_in_omega zero_in_omega)
qed

lemma \<omega>_power_succ_gtr: "Ord \<alpha> \<Longrightarrow> \<omega> \<up> \<alpha> * ord_of_nat n < \<omega> \<up> succ \<alpha>"
  by (simp add: OrdmemD)

lemma countable_oexp:
  assumes \<nu>: "\<alpha> \<in> elts \<omega>1" 
  shows "\<omega> \<up> \<alpha> \<in> elts \<omega>1"
proof -
  have "Ord \<alpha>"
    using Ord_\<omega>1 Ord_in_Ord assms by blast
  then show ?thesis
    using assms
  proof (induction rule: Ord_induct3)
    case 0
    then show ?case
      by (simp add: Ord_mem_iff_lt)
  next
    case (succ \<alpha>)
    then have "countable (elts (\<omega> \<up> \<alpha> * \<omega>))"
      by (simp add: succ_in_Limit_iff countable_mult less_\<omega>1_imp_countable)
    then show ?case
      using Ord_mem_iff_lt countable_iff_less_\<omega>1 succ.hyps by auto
  next
    case (Limit \<alpha>)
    with Ord_\<omega>1 have "countable (\<Union>\<beta>\<in>elts \<alpha>. elts (\<omega> \<up> \<beta>))" "Ord (\<omega> \<up> \<Squnion> (elts \<alpha>))"
      by (force simp: Limit_def intro: Ord_trans less_\<omega>1_imp_countable)+
    then have "\<omega> \<up> \<Squnion> (elts \<alpha>) < \<omega>1"
      using Limit.hyps countable_iff_less_\<omega>1 oexp_Limit by fastforce
    then show ?case
      using Limit.hyps Limit_def Ord_mem_iff_lt by auto
  qed
qed

end
