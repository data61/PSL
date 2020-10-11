section \<open>Cantor Normal Form\<close>

theory Cantor_NF
  imports Ordinal_Exp
begin

subsection \<open>Cantor normal form\<close>

text \<open>Lemma 5.1\<close>
lemma cnf_1:
  assumes \<alpha>: "\<alpha> \<in> elts \<beta>" "Ord \<beta>" and "m > 0"
  shows "\<omega>\<up>\<alpha> * ord_of_nat n < \<omega>\<up>\<beta> * ord_of_nat m"
proof -
  have \<dagger>: "\<omega>\<up>succ \<alpha> \<le> \<omega>\<up>\<beta>"
    using Ord_mem_iff_less_TC assms oexp_mono succ_le_TC_iff by auto
  have "\<omega>\<up>\<alpha> * ord_of_nat n < \<omega>\<up>\<alpha> * \<omega>"
    using Ord_in_Ord OrdmemD assms by auto
  also have "\<dots> = \<omega>\<up>succ \<alpha>"
    using Ord_in_Ord \<alpha> by auto
  also have "\<dots> \<le> \<omega>\<up>\<beta>"
    using "\<dagger>" by blast
  also have "\<dots> \<le> \<omega>\<up>\<beta> * ord_of_nat m"
    using \<open>m > 0\<close> le_mult by auto
  finally show ?thesis .
qed


fun Cantor_sum  where
  Cantor_sum_Nil: "Cantor_sum [] ms = 0"
| Cantor_sum_Nil2: "Cantor_sum (\<alpha>#\<alpha>s) [] = 0"
| Cantor_sum_Cons: "Cantor_sum (\<alpha>#\<alpha>s) (m#ms) = (\<omega>\<up>\<alpha>) * ord_of_nat m + Cantor_sum \<alpha>s ms"


abbreviation Cantor_dec :: "V list \<Rightarrow> bool" where
  "Cantor_dec \<equiv> sorted_wrt (>)"

lemma Ord_Cantor_sum:
  assumes "List.set \<alpha>s \<subseteq> ON"
  shows "Ord (Cantor_sum \<alpha>s ms)"
  using assms
proof (induction \<alpha>s arbitrary: ms)
  case (Cons a \<alpha>s ms)
  then show ?case
    by (cases ms) auto
qed auto

lemma Cantor_dec_Cons_iff [simp]: "Cantor_dec (\<alpha>#\<beta>#\<beta>s) \<longleftrightarrow> \<beta> < \<alpha> \<and> Cantor_dec (\<beta>#\<beta>s)"
  by auto


text \<open>Lemma 5.2. The second and third premises aren't really necessary, but their
      removal requires quite a lot of work.\<close>
lemma cnf_2:
  assumes "List.set (\<alpha>#\<alpha>s) \<subseteq> ON" "list.set ms \<subseteq> {0<..}" "length \<alpha>s = length ms"
    and "Cantor_dec (\<alpha>#\<alpha>s)"
  shows "\<omega>\<up>\<alpha> > Cantor_sum \<alpha>s ms"
  using assms
proof (induction ms arbitrary: \<alpha> \<alpha>s)
  case Nil
  then obtain \<alpha>0 where \<alpha>0: "(\<alpha>#\<alpha>s) = [\<alpha>0]"
    by (metis length_0_conv)
  then have "Ord \<alpha>0"
    using Nil.prems(1) by auto
  then show ?case
    using \<alpha>0 zero_less_Limit by auto
next
  case (Cons m1 ms)
  then obtain \<alpha>0 \<alpha>1 \<alpha>s' where \<alpha>01: "(\<alpha>#\<alpha>s) = \<alpha>0#\<alpha>1#\<alpha>s'"
    by (metis (no_types, lifting) Cons.prems(3) Suc_length_conv)
  then have "Ord \<alpha>0" "Ord \<alpha>1"
    using Cons.prems(1) \<alpha>01 by auto
  have *: "\<omega>\<up>\<alpha>0 * ord_of_nat 1 > \<omega>\<up>\<alpha>1 * ord_of_nat m1"
  proof (rule cnf_1)
    show "\<alpha>1 \<in> elts \<alpha>0"
      using Cons.prems \<alpha>01 by (simp add: Ord_mem_iff_lt \<open>Ord \<alpha>0\<close> \<open>Ord \<alpha>1\<close>)
  qed (use \<open>Ord \<alpha>0\<close> in auto)
  show ?case
  proof (cases ms)
    case Nil
    then show ?thesis
      using * one_V_def Cons.prems(3) \<alpha>01 by auto
  next
    case (Cons m2 ms')
    then obtain \<alpha>2 \<alpha>s'' where \<alpha>02: "(\<alpha>#\<alpha>s) = \<alpha>0#\<alpha>1#\<alpha>2#\<alpha>s''"
      by (metis Cons.prems(3) Suc_length_conv \<alpha>01 length_tl list.sel(3))
    then have "Ord \<alpha>2"
      using Cons.prems(1) by auto
    have "m1 > 0" "m2 > 0"
      using Cons.prems Cons by auto
    have "\<omega>\<up>\<alpha>1 * ord_of_nat m1 + \<omega>\<up>\<alpha>1 * ord_of_nat m1 = (\<omega>\<up>\<alpha>1 * ord_of_nat m1) * ord_of_nat 2"
      by (simp add: mult_succ eval_nat_numeral)
    also have "\<dots> < \<omega>\<up>\<alpha>0"
      using cnf_1 [of concl: "\<alpha>1" "m1 * 2" "\<alpha>0" 1] Cons.prems \<alpha>01 one_V_def
      by (simp add: mult.assoc ord_of_nat_mult Ord_mem_iff_lt)
    finally have II: "\<omega>\<up>\<alpha>1 * ord_of_nat m1 + \<omega>\<up>\<alpha>1 * ord_of_nat m1 < \<omega>\<up>\<alpha>0"
      by simp
    have "Cantor_sum (tl \<alpha>s) ms < \<omega>\<up>hd \<alpha>s"
    proof (rule Cons.IH)
      show "Cantor_dec (hd \<alpha>s # tl \<alpha>s)"
        using \<open>Cantor_dec (\<alpha>#\<alpha>s)\<close> \<alpha>01 by auto
    qed (use Cons.prems \<alpha>01 in auto)
    then have "Cantor_sum (\<alpha>2 # \<alpha>s'') ms < \<omega>\<up>\<alpha>1"
      using \<alpha>02 by auto
    also have "\<dots> \<le> \<omega>\<up>\<alpha>1 * ord_of_nat m1"
      by (simp add: \<open>0 < m1\<close> le_mult)
    finally show ?thesis
      using II \<alpha>02 dual_order.strict_trans by fastforce
  qed
qed

proposition Cantor_nf_exists:
  assumes "Ord \<alpha>"
  obtains \<alpha>s ms where "List.set \<alpha>s \<subseteq> ON" "list.set ms \<subseteq> {0<..}" "length \<alpha>s = length ms"
    and "Cantor_dec \<alpha>s"
    and "\<alpha> = Cantor_sum \<alpha>s ms"
  using assms
proof (induction \<alpha> arbitrary: thesis rule: Ord_induct)
  case (step \<alpha>)
  show ?case
  proof (cases "\<alpha> = 0")
    case True
    have "Cantor_sum [] [] = 0"
      by simp
    with True show ?thesis
      using length_pos_if_in_set step.prems subset_eq
      by (metis length_0_conv not_gr_zero sorted_wrt.simps(1))
  next
    case False
    define \<alpha>hat where "\<alpha>hat \<equiv> Sup {\<gamma> \<in> ON. \<omega>\<up>\<gamma> \<le> \<alpha>}"
    then have "Ord \<alpha>hat"
      using Ord_Sup assms by fastforce
    have "\<And>\<xi>. \<lbrakk>Ord \<xi>; \<omega>\<up>\<xi> \<le> \<alpha>\<rbrakk> \<Longrightarrow> \<xi> \<le> \<omega>\<up>\<alpha>"
      by (metis Ord_\<omega> OrdmemD le_oexp' order_trans step.hyps one_V_def succ_in_omega zero_in_omega)
    then have "{\<gamma> \<in> ON. \<omega>\<up>\<gamma> \<le> \<alpha>} \<subseteq> elts (succ (\<omega>\<up>\<alpha>))"
      using Ord_mem_iff_lt step.hyps by force
    then have sma: "small {\<gamma> \<in> ON. \<omega>\<up>\<gamma> \<le> \<alpha>}"
      by (meson down)
    have le: "\<omega>\<up>\<alpha>hat \<le> \<alpha>"
    proof (rule ccontr)
      assume "\<not> \<omega>\<up>\<alpha>hat \<le> \<alpha>"
      then have \<dagger>: "\<alpha> \<in> elts (\<omega>\<up>\<alpha>hat)"
        by (meson Ord_\<omega> Ord_linear2 Ord_mem_iff_lt Ord_oexp \<open>Ord \<alpha>hat\<close> step.hyps)
      obtain \<gamma> where "Ord \<gamma>" "\<omega>\<up>\<gamma> \<le> \<alpha>" "\<alpha> < \<gamma>"
        using \<open>Ord \<alpha>hat\<close>
      proof (cases \<alpha>hat rule: Ord_cases)
        case 0
        with \<dagger> show thesis
          by (auto simp: False)
      next
        case (succ \<beta>)
        have "succ \<beta> \<in> {\<gamma> \<in> ON. \<omega>\<up>\<gamma> \<le> \<alpha>}"
          by (rule succ_in_Sup_Ord) (use succ \<alpha>hat_def sma in auto)
        then have "\<omega>\<up>succ \<beta> \<le> \<alpha>"
          by blast
        with \<dagger> show thesis
          using \<open>\<not> \<omega>\<up>\<alpha>hat \<le> \<alpha>\<close> succ by blast
      next
        case limit
        with \<dagger> show thesis
          apply (clarsimp simp: oexp_Limit \<alpha>hat_def)
          by (meson Ord_\<omega> Ord_in_Ord Ord_linear_le mem_not_refl oexp_mono_le omega_nonzero vsubsetD)
      qed
      then show False
        by (metis Ord_\<omega> OrdmemD leD le_less_trans le_oexp' one_V_def succ_in_omega zero_in_omega)
    qed
    have False if "\<nexists>M. \<alpha> < \<omega>\<up>\<alpha>hat * ord_of_nat M"
    proof -
      have \<dagger>: "\<omega>\<up>\<alpha>hat * ord_of_nat M \<le> \<alpha>" for M
        by (meson that Ord_\<omega> Ord_linear2 Ord_mult Ord_oexp Ord_ord_of_nat \<open>Ord \<alpha>hat\<close> step.hyps)
      have "\<not> \<omega>\<up>succ \<alpha>hat \<le> \<alpha>"
        using Ord_mem_iff_lt \<alpha>hat_def \<open>Ord \<alpha>hat\<close> sma elts_succ by blast
      then have "\<alpha> < \<omega>\<up>succ \<alpha>hat"
        by (meson Ord_\<omega> Ord_linear2 Ord_oexp Ord_succ \<open>Ord \<alpha>hat\<close> step.hyps)
      also have "\<dots> = \<omega>\<up>\<alpha>hat * \<omega>"
        using \<open>Ord \<alpha>hat\<close> oexp_succ by blast
      also have "\<dots> = Sup (range (\<lambda>m. \<omega>\<up>\<alpha>hat * ord_of_nat m))"
        by (simp add: mult_Limit) (auto simp: \<omega>_def image_image)
      also have "\<dots> \<le> \<alpha>"
        using \<dagger> by blast
      finally show False
        by simp
    qed
    then obtain M where M: "\<omega>\<up>\<alpha>hat * ord_of_nat M > \<alpha>"
      by blast
    have bound: "i \<le> M" if "\<omega>\<up>\<alpha>hat * ord_of_nat i \<le> \<alpha>" for i
    proof -
      have "\<omega>\<up>\<alpha>hat * ord_of_nat i < \<omega>\<up>\<alpha>hat * ord_of_nat M"
        using M dual_order.strict_trans2 that by blast
      then show ?thesis
        using \<open>Ord \<alpha>hat\<close> less_V_def by auto
    qed
    define mhat where "mhat \<equiv> Greatest (\<lambda>m. \<omega>\<up>\<alpha>hat * ord_of_nat m \<le> \<alpha>)"
    have mhat_ge: "m \<le> mhat" if "\<omega>\<up>\<alpha>hat * ord_of_nat m \<le> \<alpha>" for m
      unfolding mhat_def
      by (metis (mono_tags, lifting) Greatest_le_nat bound that)
    have mhat: "\<omega>\<up>\<alpha>hat * ord_of_nat mhat \<le> \<alpha>"
      unfolding mhat_def
      by (rule GreatestI_nat [where k=0 and b=M]) (use bound in auto)
    then obtain \<xi> where "Ord \<xi>" "\<xi> \<le> \<alpha>" and \<xi>: "\<alpha> = \<omega>\<up>\<alpha>hat * ord_of_nat mhat + \<xi>"
      by (metis Ord_\<omega> Ord_mult Ord_oexp Ord_ord_of_nat \<open>Ord \<alpha>hat\<close> step.hyps le_Ord_diff)
    have False if "\<xi> = \<alpha>"
    proof -
      have "\<xi> \<ge> \<omega>\<up>\<alpha>hat"
        by (simp add: le that)
      then obtain \<zeta> where "Ord \<zeta>" "\<zeta> \<le> \<xi>" and \<zeta>: "\<xi> = \<omega>\<up>\<alpha>hat + \<zeta>"
        by (metis Ord_\<omega> Ord_oexp \<open>Ord \<alpha>hat\<close> \<open>Ord \<xi>\<close> le_Ord_diff)
      then have "\<alpha> = \<omega>\<up>\<alpha>hat * ord_of_nat mhat + \<omega>\<up>\<alpha>hat + \<zeta>"
        by (simp add: \<xi> add.assoc)
      then have "\<omega>\<up>\<alpha>hat * ord_of_nat (Suc mhat) \<le> \<alpha>"
        by (metis add_le_cancel_left add.right_neutral le_0 mult_succ ord_of_nat.simps(2))
      then show False
        using Suc_n_not_le_n mhat_ge by blast
    qed
    then have \<xi>in\<alpha>: "\<xi> \<in> elts \<alpha>"
      using Ord_mem_iff_lt \<open>Ord \<xi>\<close> \<open>\<xi> \<le> \<alpha>\<close> less_V_def step.hyps by auto
    show thesis
    proof (cases "\<xi> = 0")
      case True
      show thesis
      proof (rule step.prems)
        show "\<alpha> = Cantor_sum [\<alpha>hat] [mhat]"
          by (simp add: True \<xi>)
      qed (use \<xi> True \<open>\<alpha> \<noteq> 0\<close> \<open>Ord \<alpha>hat\<close> in auto)
    next
      case False
      obtain \<beta>s ns where sub: "List.set \<beta>s \<subseteq> ON" "list.set ns \<subseteq> {0<..}"
        and len_eq: "length \<beta>s = length ns"
        and dec: "Cantor_dec \<beta>s"
        and \<xi>eq: "\<xi> = Cantor_sum \<beta>s ns"
        using step.IH [OF \<xi>in\<alpha>] by blast
      then have "length \<beta>s > 0" "length ns > 0"
        using False Cantor_sum.simps(1) \<open>\<xi> = Cantor_sum \<beta>s ns\<close> by auto
      then obtain \<beta>0 n0 \<beta>s' ns' where \<beta>0: "\<beta>s = \<beta>0 # \<beta>s'" and "Ord \<beta>0"
        and n0: "ns = n0 # ns'" and "n0 > 0"
        using sub by (auto simp: neq_Nil_conv)
      moreover have False if "\<beta>0 > \<alpha>hat"
      proof -
        have "\<omega>\<up>\<beta>0 \<le> \<omega>\<up>\<beta>0 * ord_of_nat n0 + u" for u
          using \<open>n0 > 0\<close>
          by (metis add_le_cancel_left Ord_ord_of_nat add.right_neutral dual_order.trans gr_implies_not_zero le_0 le_mult ord_of_eq_0_iff)
        moreover have "\<omega>\<up>\<beta>0 > \<alpha>"
          using that \<open>Ord \<beta>0\<close>
          by (metis (no_types, lifting) Ord_\<omega> Ord_linear2 Ord_oexp Sup_upper \<alpha>hat_def leD mem_Collect_eq sma step.hyps)
        ultimately have "\<xi> \<ge> \<omega>\<up>\<beta>0"
          by (simp add: \<xi>eq \<beta>0 n0)
        then show ?thesis
          using \<open>\<alpha> < \<omega>\<up>\<beta>0\<close> \<open>\<xi> \<le> \<alpha>\<close> by auto
      qed
      ultimately have "\<beta>0 \<le> \<alpha>hat"
        using Ord_linear2 \<open>Ord \<alpha>hat\<close> by auto
      then consider "\<beta>0 < \<alpha>hat" | "\<beta>0 = \<alpha>hat"
        using dual_order.order_iff_strict by auto
      then show ?thesis
      proof cases
        case 1
        show ?thesis
        proof (rule step.prems)
          show "list.set (\<alpha>hat#\<beta>s) \<subseteq> ON"
            using sub by (auto simp: \<open>Ord \<alpha>hat\<close>)
          show "list.set (mhat#ns) \<subseteq> {0::nat<..}"
            using sub using \<open>\<xi> = \<alpha> \<Longrightarrow> False\<close> \<xi> by fastforce
          show "Cantor_dec (\<alpha>hat#\<beta>s)"
            using that \<open>\<beta>0 < \<alpha>hat\<close> \<open>Ord \<alpha>hat\<close> \<open>Ord \<beta>0\<close> Ord_mem_iff_lt \<beta>0 dec less_Suc_eq_0_disj
            by (force simp: \<beta>0 n0)
          show "length (\<alpha>hat#\<beta>s) = length (mhat#ns)"
            by (auto simp: len_eq)
          show "\<alpha> = Cantor_sum (\<alpha>hat#\<beta>s) (mhat#ns)"
            by (simp add: \<xi> \<xi>eq \<beta>0 n0)
        qed
      next
        case 2
        show ?thesis
        proof (rule step.prems)
          show "list.set \<beta>s \<subseteq> ON"
            by (simp add: sub(1))
          show "list.set ((n0+mhat)#ns') \<subseteq> {0::nat<..}"
            using n0 sub(2) by auto
          show "length (\<beta>s::V list) = length ((n0+mhat)#ns')"
            by (simp add: len_eq n0)
          show "Cantor_dec \<beta>s"
            using that \<beta>0 dec by auto
          show "\<alpha> = Cantor_sum \<beta>s ((n0+mhat)#ns')"
            using 2
            by (simp add: add_mult_distrib \<beta>0 \<xi> \<xi>eq add.assoc add.commute n0 ord_of_nat_add)
        qed
      qed
    qed
  qed
qed

lemma Cantor_sum_0E:
  assumes "Cantor_sum \<alpha>s ms = 0" "List.set \<alpha>s \<subseteq> ON" "list.set ms \<subseteq> {0<..}" "length \<alpha>s = length ms"
  shows "\<alpha>s = []"
  using assms
proof (induction \<alpha>s arbitrary: ms)
  case Nil
  then show ?case
    by auto
next
  case (Cons a list)
  then obtain m ms' where "ms = m#ms'" "m \<noteq> 0" "list.set ms' \<subseteq> {0<..}"
    by simp (metis Suc_length_conv greaterThan_iff insert_subset list.set(2))
  with Cons show ?case by auto
qed


lemma Cantor_nf_unique_aux:
  assumes "Ord \<alpha>"
    and \<alpha>sON: "List.set \<alpha>s \<subseteq> ON"
    and \<beta>sON: "List.set \<beta>s \<subseteq> ON"
    and ms: "list.set ms \<subseteq> {0<..}"
    and ns: "list.set ns \<subseteq> {0<..}"
    and mseq: "length \<alpha>s = length ms"
    and nseq: "length \<beta>s = length ns"
    and \<alpha>sdec: "Cantor_dec \<alpha>s"
    and \<beta>sdec: "Cantor_dec \<beta>s"
    and \<alpha>seq: "\<alpha> = Cantor_sum \<alpha>s ms"
    and \<beta>seq: "\<alpha> = Cantor_sum \<beta>s ns"
  shows "\<alpha>s = \<beta>s \<and> ms = ns"
  using assms
proof (induction \<alpha> arbitrary: \<alpha>s ms \<beta>s ns rule: Ord_induct)
  case (step \<alpha>)
  show ?case
  proof (cases "\<alpha> = 0")
    case True
    then show ?thesis
      using step.prems by (metis Cantor_sum_0E length_0_conv)
  next
    case False
    then obtain \<alpha>0 \<alpha>s' \<beta>0 \<beta>s' where \<alpha>s: "\<alpha>s = \<alpha>0 # \<alpha>s'" and \<beta>s: "\<beta>s = \<beta>0 # \<beta>s'"
      by (metis Cantor_sum.simps(1) min_list.cases step.prems(9,10))
    then have ON: "Ord \<alpha>0" "list.set \<alpha>s' \<subseteq> ON" "Ord \<beta>0" "list.set \<beta>s' \<subseteq> ON"
      using \<alpha>s \<beta>s step.prems(1,2) by auto
    then obtain m0 ms' n0 ns' where ms: "ms = m0 # ms'" and ns: "ns = n0 # ns'"
      by (metis \<alpha>s \<beta>s length_0_conv list.distinct(1) list.exhaust step.prems(5,6))
    then have nz: "m0 \<noteq> 0" "list.set ms' \<subseteq> {0<..}" "n0 \<noteq> 0" "list.set ns' \<subseteq> {0<..}"
      using ms ns step.prems(3,4) by auto
    have False if "\<beta>0 < \<alpha>0"
    proof -
      have Ordc: "Ord (Cantor_sum \<beta>s ns)" "Ord (\<omega>\<up>\<alpha>0)"
        using Ord_oexp \<open>Ord \<alpha>0\<close>  step.hyps step.prems(10) by blast+
      have *: "Cantor_sum \<beta>s ns < \<omega>\<up>\<alpha>0"
        using step.prems(2-6) \<open>Ord \<alpha>0\<close> \<open>Cantor_dec \<beta>s\<close> that \<beta>s cnf_2
        by (metis Cantor_dec_Cons_iff insert_subset list.set(2) mem_Collect_eq)
      then show False
        by (metis Cantor_sum_Cons Ord_mem_iff_lt Ord_ord_of_nat Ordc \<alpha>s \<open>m0 \<noteq> 0\<close> * le_mult ms not_add_mem_right ord_of_eq_0 step.prems(9,10) vsubsetD)
    qed
    moreover
    have False if "\<alpha>0 < \<beta>0"
    proof -
      have Ordc: "Ord (Cantor_sum \<alpha>s ms)" "Ord (\<omega>\<up>\<beta>0)"
        using Ord_oexp \<open>Ord \<beta>0\<close>  step.hyps step.prems(9) by blast+
      have *: "Cantor_sum \<alpha>s ms < \<omega>\<up>\<beta>0"
        using step.prems(1-5) \<open>Ord \<beta>0\<close> \<open>Cantor_dec \<alpha>s\<close> that \<alpha>s cnf_2
        by (metis Cantor_dec_Cons_iff \<beta>s insert_subset list.set(2))
      then show False
        by (metis Cantor_sum_Cons Ord_mem_iff_lt Ord_ord_of_nat Ordc \<beta>s \<open>n0 \<noteq> 0\<close> * le_mult not_add_mem_right ns ord_of_eq_0 step.prems(9,10) vsubsetD)
    qed
    ultimately have 1: "\<alpha>0 = \<beta>0"
      using Ord_linear_lt \<open>Ord \<alpha>0\<close> \<open>Ord \<beta>0\<close> by blast
    have False if "m0 < n0"
    proof -
      have "\<omega>\<up>\<alpha>0 > Cantor_sum \<alpha>s' ms'"
        using \<alpha>s \<open>list.set ms' \<subseteq> {0<..}\<close> cnf_2 ms step.prems(1,5,7) by auto
      then have "\<alpha> < \<omega>\<up>\<alpha>0 * ord_of_nat m0 + \<omega>\<up>\<alpha>0"
        by (simp add: \<alpha>s ms step.prems(9))
      also have "\<dots> = \<omega>\<up>\<alpha>0 * ord_of_nat (Suc m0)"
        by (simp add: mult_succ)
      also have "\<dots> \<le> \<omega>\<up>\<alpha>0 * ord_of_nat n0"
        by (meson Ord_\<omega> Ord_oexp Ord_ord_of_nat Suc_leI \<open>Ord \<alpha>0\<close> mult_cancel_le_iff ord_of_nat_mono_iff that)
      also have "\<dots> \<le> \<alpha>"
        by (metis Cantor_sum_Cons add_le_cancel_left \<beta>s \<open>\<alpha>0 = \<beta>0\<close> add.right_neutral le_0 ns step.prems(10))
      finally show False
        by blast
    qed
    moreover have False if "n0 < m0"
    proof -
      have "\<omega>\<up>\<beta>0 > Cantor_sum \<beta>s' ns'"
        using \<beta>s \<open>list.set ns' \<subseteq> {0<..}\<close> cnf_2 ns step.prems(2,6,8) by auto
      then have "\<alpha> < \<omega>\<up>\<beta>0 * ord_of_nat n0 + \<omega>\<up>\<beta>0"
        by (simp add: \<beta>s ns step.prems(10))
      also have "\<dots> = \<omega>\<up>\<beta>0 * ord_of_nat (Suc n0)"
        by (simp add: mult_succ)
      also have "\<dots> \<le> \<omega>\<up>\<beta>0 * ord_of_nat m0"
        by (meson Ord_\<omega> Ord_oexp Ord_ord_of_nat Suc_leI \<open>Ord \<beta>0\<close> mult_cancel_le_iff ord_of_nat_mono_iff that)
      also have "\<dots> \<le> \<alpha>"
        by (metis Cantor_sum_Cons add_le_cancel_left \<alpha>s \<open>\<alpha>0 = \<beta>0\<close> add.right_neutral le_0 ms step.prems(9))
      finally show False
        by blast
    qed
    ultimately have 2: "m0 = n0"
      using nat_neq_iff by blast
    have "\<alpha>s' = \<beta>s' \<and> ms' = ns'"
    proof (rule step.IH)
      have "Cantor_sum \<alpha>s' ms' < \<omega>\<up>\<alpha>0"
        using \<alpha>s cnf_2 ms nz(2) step.prems(1) step.prems(5) step.prems(7) by auto
      also have "\<dots> \<le> Cantor_sum \<alpha>s ms"
        apply (simp add: \<alpha>s \<beta>s ms ns)
        by (metis Cantor_sum_Cons add_less_cancel_left ON(1) Ord_\<omega> Ord_linear2 Ord_oexp Ord_ord_of_nat \<alpha>s add.right_neutral dual_order.strict_trans1 le_mult ms not_less_0 nz(1) ord_of_eq_0 step.hyps step.prems(9))
      finally show "Cantor_sum \<alpha>s' ms' \<in> elts \<alpha>"
        using ON(2) Ord_Cantor_sum Ord_mem_iff_lt step.hyps step.prems(9) by blast
      show "length \<alpha>s' = length ms'" "length \<beta>s' = length ns'"
        using \<alpha>s ms \<beta>s ns step.prems by auto
      show "Cantor_dec \<alpha>s'" "Cantor_dec \<beta>s'"
        using \<alpha>s \<beta>s step.prems(7,8) by auto
      have "Cantor_sum \<alpha>s ms = Cantor_sum \<beta>s ns"
        using step.prems(9,10) by auto
      then show "Cantor_sum \<alpha>s' ms' = Cantor_sum \<beta>s' ns'"
        using 1 2 by (simp add: \<alpha>s \<beta>s ms ns)
    qed (use ON nz in auto)
    then show ?thesis
      using 1 2 by (simp add: \<alpha>s \<beta>s ms ns)
  qed
qed


proposition Cantor_nf_unique:
  assumes "Cantor_sum \<alpha>s ms = Cantor_sum \<beta>s ns"
    and \<alpha>sON: "List.set \<alpha>s \<subseteq> ON"
    and \<beta>sON: "List.set \<beta>s \<subseteq> ON"
    and ms: "list.set ms \<subseteq> {0<..}"
    and ns: "list.set ns \<subseteq> {0<..}"
    and mseq: "length \<alpha>s = length ms"
    and nseq: "length \<beta>s = length ns"
    and \<alpha>sdec: "Cantor_dec \<alpha>s"
    and \<beta>sdec: "Cantor_dec \<beta>s"
  shows "\<alpha>s = \<beta>s \<and> ms = ns"
  using Cantor_nf_unique_aux Ord_Cantor_sum assms  by auto


lemma less_\<omega>_power:
  assumes "Ord \<alpha>1" "Ord \<beta>"
    and \<alpha>2: "\<alpha>2 \<in> elts \<alpha>1" and \<beta>: "\<beta> < \<omega>\<up>\<alpha>2"
    and "m1 > 0" "m2 > 0"
  shows "\<omega>\<up>\<alpha>2 * ord_of_nat m2 + \<beta> < \<omega>\<up>\<alpha>1 * ord_of_nat m1 + (\<omega>\<up>\<alpha>2 * ord_of_nat m2 + \<beta>)"
        (is "?lhs < ?rhs")
proof -
  obtain oo: "Ord (\<omega>\<up>\<alpha>1)" "Ord (\<omega>\<up>\<alpha>2)"
    using Ord_in_Ord Ord_oexp assms by blast
  moreover obtain "ord_of_nat m2 \<noteq> 0"
    using assms ord_of_eq_0 by blast
  ultimately have "\<beta> < \<omega>\<up>\<alpha>2 * ord_of_nat m2"
    by (meson Ord_ord_of_nat \<beta> dual_order.strict_trans1 le_mult)
  with oo assms have "?lhs \<noteq> ?rhs"
    by (metis Ord_mult Ord_ord_of_nat add_strict_mono add.assoc cnf_1 not_add_less_right oo)
  then show ?thesis
    by (simp add: add_le_left \<open>Ord \<beta>\<close> less_V_def oo)
qed

lemma Cantor_sum_ge:
  assumes "List.set (\<alpha>#\<alpha>s) \<subseteq> ON" "list.set ms \<subseteq> {0<..}" "length ms > 0"
  shows "\<omega> \<up> \<alpha> \<le> Cantor_sum (\<alpha>#\<alpha>s) ms"
proof -
  obtain m ns where ms: "ms = Cons m ns"
    using assms(3) strict_sorted.cases by auto
  then have "\<omega> \<up> \<alpha> \<le> \<omega> \<up> \<alpha> * ord_of_nat m"
    using assms(2) le_mult by auto
  then show ?thesis
    using dual_order.trans ms by auto
qed

subsection \<open>Simplified Cantor normal form\<close>

text \<open>No coefficients, and the exponents decreasing non-strictly\<close>

fun \<omega>_sum  where
  \<omega>_sum_Nil: "\<omega>_sum [] = 0"
| \<omega>_sum_Cons: "\<omega>_sum (\<alpha>#\<alpha>s) = (\<omega>\<up>\<alpha>) + \<omega>_sum \<alpha>s"

abbreviation \<omega>_dec :: "V list \<Rightarrow> bool" where
  "\<omega>_dec \<equiv> sorted_wrt (\<ge>)"

lemma Ord_\<omega>_sum [simp]: "List.set \<alpha>s \<subseteq> ON \<Longrightarrow> Ord (\<omega>_sum \<alpha>s)"
  by (induction \<alpha>s) auto

lemma \<omega>_dec_Cons_iff [simp]: "\<omega>_dec (\<alpha>#\<beta>#\<beta>s) \<longleftrightarrow> \<beta> \<le> \<alpha> \<and> \<omega>_dec (\<beta>#\<beta>s)"
  by auto

lemma \<omega>_sum_0E:
  assumes "\<omega>_sum \<alpha>s = 0" "List.set \<alpha>s \<subseteq> ON"
  shows "\<alpha>s = []"
  using assms
by (induction \<alpha>s) auto

fun \<omega>_of_Cantor where
  \<omega>_of_Cantor_Nil: "\<omega>_of_Cantor [] ms = []"
| \<omega>_of_Cantor_Nil2: "\<omega>_of_Cantor (\<alpha>#\<alpha>s) [] = []"
| \<omega>_of_Cantor_Cons: "\<omega>_of_Cantor (\<alpha>#\<alpha>s) (m#ms) = replicate m \<alpha> @ \<omega>_of_Cantor \<alpha>s ms"


lemma \<omega>_sum_append [simp]: "\<omega>_sum (xs @ ys) = \<omega>_sum xs + \<omega>_sum ys"
  by (induction xs) (auto simp: add.assoc)

lemma \<omega>_sum_replicate [simp]: "\<omega>_sum (replicate m a) = \<omega> \<up> a * ord_of_nat m"
  by (induction m) (auto simp: mult_succ simp flip: replicate_append_same)

lemma \<omega>_sum_of_Cantor [simp]: "\<omega>_sum (\<omega>_of_Cantor \<alpha>s ms) = Cantor_sum \<alpha>s ms"
proof (induction \<alpha>s arbitrary: ms)
  case (Cons a \<alpha>s ms)
  then show ?case
    by (cases ms) auto
qed auto

lemma \<omega>_of_Cantor_subset: "List.set (\<omega>_of_Cantor \<alpha>s ms) \<subseteq> List.set \<alpha>s"
proof (induction \<alpha>s arbitrary: ms)
  case (Cons a \<alpha>s ms)
  then show ?case
    by (cases ms) auto
qed auto


lemma \<omega>_dec_replicate: "\<omega>_dec (replicate m \<alpha> @ \<alpha>s) = (if m=0 then \<omega>_dec \<alpha>s else \<omega>_dec (\<alpha>#\<alpha>s))"
  by (induction m arbitrary: \<alpha>s) (simp_all flip: replicate_append_same)


lemma \<omega>_dec_of_Cantor_aux:
  assumes "Cantor_dec (\<alpha>#\<alpha>s)" "length \<alpha>s = length ms"
  shows "\<omega>_dec (\<omega>_of_Cantor (\<alpha>#\<alpha>s) (m#ms))"
  using assms
proof (induction \<alpha>s arbitrary: ms)
  case Nil
  then show ?case
    using sorted_wrt_iff_nth_less by fastforce
next
  case (Cons a \<alpha>s ms)
  then obtain n ns where ns: "ms = n#ns"
    by (metis length_Suc_conv)
  then have "a \<le> \<alpha>"
    using Cons.prems(1) order.strict_implies_order by auto
  moreover have "\<forall>x\<in>list.set (\<omega>_of_Cantor \<alpha>s ns). x \<le> a"
    using Cons ns \<open>a \<le> \<alpha>\<close>
    apply (simp add: \<omega>_dec_replicate)
    by (meson \<omega>_of_Cantor_subset order.strict_implies_order subsetD)
  ultimately show ?case
    using Cons ns by (force simp: \<omega>_dec_replicate)
qed

lemma \<omega>_dec_of_Cantor:
  assumes "Cantor_dec \<alpha>s" "length \<alpha>s = length ms"
  shows "\<omega>_dec (\<omega>_of_Cantor \<alpha>s ms)"
proof (cases \<alpha>s)
  case Nil
  then have "ms = []"
    using assms by auto
  with Nil show ?thesis
    by simp
next
  case (Cons a list)
  then show ?thesis
    by (metis \<omega>_dec_of_Cantor_aux assms length_Suc_conv)
qed

proposition \<omega>_nf_exists:
  assumes "Ord \<alpha>"
  obtains \<alpha>s where "List.set \<alpha>s \<subseteq> ON" and "\<omega>_dec \<alpha>s" and "\<alpha> = \<omega>_sum \<alpha>s"
proof -
  obtain \<alpha>s ms where "List.set \<alpha>s \<subseteq> ON" "list.set ms \<subseteq> {0<..}" and length: "length \<alpha>s = length ms"
    and "Cantor_dec \<alpha>s"
    and \<alpha>: "\<alpha> = Cantor_sum \<alpha>s ms"
    using Cantor_nf_exists assms by blast
  then show thesis
    by (metis \<omega>_dec_of_Cantor \<omega>_of_Cantor_subset \<omega>_sum_of_Cantor order_trans that)
qed

lemma \<omega>_sum_take_drop: "\<omega>_sum \<alpha>s = \<omega>_sum (take k \<alpha>s) + \<omega>_sum (drop k \<alpha>s)"
proof (induction k arbitrary: \<alpha>s)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  then show ?case
  proof (cases "\<alpha>s")
    case Nil
    then show ?thesis
      by simp
  next
    case (Cons a list)
    with Suc.prems show ?thesis
      by (simp add: add.assoc flip: Suc.IH)
  qed
qed

lemma in_elts_\<omega>_sum:
  assumes "\<delta> \<in> elts (\<omega>_sum \<alpha>s)"
  shows "\<exists>k<length \<alpha>s. \<exists>\<gamma>\<in>elts (\<omega> \<up> (\<alpha>s!k)). \<delta> = \<omega>_sum (take k \<alpha>s) + \<gamma>"
  using assms
proof (induction \<alpha>s arbitrary: \<delta>)
  case (Cons \<alpha> \<alpha>s)
  then have "\<delta> \<in> elts (\<omega> \<up> \<alpha> + \<omega>_sum \<alpha>s)"
    by simp
  then show ?case
  proof (rule mem_plus_V_E)
    fix \<eta>
    assume \<eta>: "\<eta> \<in> elts (\<omega>_sum \<alpha>s)" and \<delta>: "\<delta> = \<omega> \<up> \<alpha> + \<eta>"
    then obtain k \<gamma> where "k<length \<alpha>s" "\<gamma> \<in> elts (\<omega> \<up> (\<alpha>s!k))" "\<eta> = \<omega>_sum (take k \<alpha>s) + \<gamma>"
      using Cons.IH by blast
    then show ?case
      by (rule_tac x="Suc k" in exI) (simp add: \<delta> add.assoc)
  qed auto
qed auto

lemma \<omega>_le_\<omega>_sum: "\<lbrakk>k < length \<alpha>s; List.set \<alpha>s \<subseteq> ON\<rbrakk> \<Longrightarrow> \<omega> \<up> (\<alpha>s!k) \<le> \<omega>_sum \<alpha>s"
proof (induction \<alpha>s arbitrary: k)
  case (Cons a \<alpha>s)
  then obtain "Ord a" "list.set \<alpha>s \<subseteq> ON"
    by simp
  with Cons.IH have "\<And>k x. k < length \<alpha>s \<Longrightarrow> \<omega> \<up> \<alpha>s ! k \<le> \<omega> \<up> a + \<omega>_sum \<alpha>s"
    by (meson Ord_\<omega> Ord_\<omega>_sum Ord_oexp add_le_left order_trans)
  then show ?case
    using Cons by (simp add: nth_Cons split: nat.split)
qed auto

lemma \<omega>_sum_less_self:
  assumes "List.set (\<alpha>#\<alpha>s) \<subseteq> ON" and "\<omega>_dec (\<alpha>#\<alpha>s)"
  shows "\<omega>_sum \<alpha>s < \<omega>\<up>\<alpha> + \<omega>_sum \<alpha>s"
  using assms
proof (induction \<alpha>s arbitrary: \<alpha>)
  case Nil
  then show ?case
    using ZFC_in_HOL.neq0_conv by fastforce
next
  case (Cons \<alpha>1 \<alpha>s)
  then show ?case
    by (simp add: add_right_strict_mono oexp_mono_le)
qed

text \<open>Something like Lemma 5.2 for @{term \<omega>_sum}\<close>
lemma \<omega>_sum_less_\<omega>_power:
  assumes "\<omega>_dec (\<alpha>#\<alpha>s)" "List.set (\<alpha>#\<alpha>s) \<subseteq> ON"
  shows "\<omega>_sum \<alpha>s < \<omega>\<up>\<alpha> * \<omega>"
  using assms
proof (induction \<alpha>s)
  case Nil
  then show ?case
    by (simp add: \<omega>_gt0)
next
  case (Cons \<beta> \<alpha>s)
  then have "Ord \<alpha>"
    by auto
  have "\<omega>_sum \<alpha>s < \<omega>\<up>\<alpha> * \<omega>"
    using Cons by force
  then have "\<omega>\<up>\<beta> + \<omega>_sum \<alpha>s < \<omega>\<up>\<alpha> + \<omega>\<up>\<alpha> * \<omega>"
    using Cons.prems add_right_strict_mono oexp_mono_le by auto
  also have "\<dots> = \<omega>\<up>\<alpha> * \<omega>"
    by (metis Kirby.add_mult_distrib mult.right_neutral one_plus_\<omega>_equals_\<omega>)
  finally show ?case
    by simp
qed


lemma \<omega>_sum_nf_unique_aux:
  assumes "Ord \<alpha>"
    and \<alpha>sON: "List.set \<alpha>s \<subseteq> ON"
    and \<beta>sON: "List.set \<beta>s \<subseteq> ON"
    and \<alpha>sdec: "\<omega>_dec \<alpha>s"
    and \<beta>sdec: "\<omega>_dec \<beta>s"
    and \<alpha>seq: "\<alpha> = \<omega>_sum \<alpha>s"
    and \<beta>seq: "\<alpha> = \<omega>_sum \<beta>s"
  shows "\<alpha>s = \<beta>s"
  using assms
proof (induction \<alpha> arbitrary: \<alpha>s \<beta>s rule: Ord_induct)
  case (step \<alpha>)
  show ?case
  proof (cases "\<alpha> = 0")
    case True
    then show ?thesis
      using step.prems by (metis \<omega>_sum_0E)
  next
    case False
    then obtain \<alpha>0 \<alpha>s' \<beta>0 \<beta>s' where \<alpha>s: "\<alpha>s = \<alpha>0 # \<alpha>s'" and \<beta>s: "\<beta>s = \<beta>0 # \<beta>s'"
      by (metis \<omega>_sum.elims step.prems(5,6))
    then have ON: "Ord \<alpha>0" "list.set \<alpha>s' \<subseteq> ON" "Ord \<beta>0" "list.set \<beta>s' \<subseteq> ON"
      using \<alpha>s \<beta>s step.prems(1,2) by auto
    have False if "\<beta>0 < \<alpha>0"
    proof -
      have Ordc: "Ord (\<omega>_sum \<beta>s)" "Ord (\<omega>\<up>\<alpha>0)"
        using Ord_oexp \<open>Ord \<alpha>0\<close>  step.hyps step.prems(6) by blast+
      have "\<omega>_sum \<beta>s < \<omega>\<up>\<beta>0 * \<omega>"
        by (rule \<omega>_sum_less_\<omega>_power) (use \<beta>s step.prems ON in auto)
      also have "\<dots> \<le> \<omega>\<up>\<alpha>0"
        using ON by (metis Ord_\<omega> Ord_succ oexp_mono_le oexp_succ omega_nonzero succ_le_iff that)
      finally show False
        using \<alpha>s leD step.prems(5,6) by auto
    qed
    moreover
    have False if "\<alpha>0 < \<beta>0"
    proof -
      have Ordc: "Ord (\<omega>_sum \<alpha>s)" "Ord (\<omega>\<up>\<beta>0)"
        using Ord_oexp \<open>Ord \<beta>0\<close>  step.hyps step.prems(5) by blast+
      have "\<omega>_sum \<alpha>s < \<omega>\<up>\<alpha>0 * \<omega>"
        by (rule \<omega>_sum_less_\<omega>_power) (use \<alpha>s step.prems ON in auto)
      also have "\<dots> \<le> \<omega>\<up>\<beta>0"
        using ON by (metis Ord_\<omega> Ord_succ oexp_mono_le oexp_succ omega_nonzero succ_le_iff that)
      finally show False
        using \<beta>s leD step.prems(5,6)
        by (simp add: \<open>\<alpha> = \<omega>_sum \<alpha>s\<close> leD)
    qed
    ultimately have \<dagger>: "\<alpha>0 = \<beta>0"
      using Ord_linear_lt \<open>Ord \<alpha>0\<close> \<open>Ord \<beta>0\<close> by blast
    moreover have "\<alpha>s' = \<beta>s'"
    proof (rule step.IH)
      show "\<omega>_sum \<alpha>s' \<in> elts \<alpha>"
        using step.prems \<alpha>s
        by (simp add: Ord_mem_iff_lt \<omega>_sum_less_self)
      show "\<omega>_dec \<alpha>s'" "\<omega>_dec \<beta>s'"
        using \<alpha>s \<beta>s step.prems(3,4) by auto
      have "\<omega>_sum \<alpha>s = \<omega>_sum \<beta>s"
        using step.prems(5,6) by auto
      then show "\<omega>_sum \<alpha>s' = \<omega>_sum \<beta>s'"
        by (simp add: \<dagger> \<alpha>s \<beta>s)
    qed (use ON in auto)
    ultimately show ?thesis
      by (simp add: \<alpha>s \<beta>s)
  qed
qed


subsection \<open>Indecomposable ordinals\<close>

text \<open>Cf exercise 5 on page 43 of Kunen\<close>

definition indecomposable
  where "indecomposable \<alpha> \<equiv> Ord \<alpha> \<and> (\<forall>\<beta> \<in> elts \<alpha>. \<forall>\<gamma> \<in> elts \<alpha>. \<beta>+\<gamma> \<in> elts \<alpha>)"

lemma indecomposableD:
  "\<lbrakk>indecomposable \<alpha>; \<beta> < \<alpha>; \<gamma> < \<alpha>; Ord \<beta>; Ord \<gamma>\<rbrakk> \<Longrightarrow> \<beta>+\<gamma> < \<alpha>"
  by (meson Ord_mem_iff_lt OrdmemD indecomposable_def)

lemma indecomposable_imp_Ord:
  "indecomposable \<alpha> \<Longrightarrow> Ord \<alpha>"
  using indecomposable_def by blast

lemma indecomposable_1: "indecomposable 1"
  by (auto simp: indecomposable_def)

lemma indecomposable_0: "indecomposable 0"
  by (auto simp: indecomposable_def)

lemma indecomposable_succ [simp]: "indecomposable (succ \<alpha>) \<longleftrightarrow> \<alpha> = 0"
  using not_add_mem_right
  apply (auto simp: indecomposable_def)
  apply (metis add_right_cancel add.right_neutral)
  done

lemma indecomposable_alt:
  assumes ord: "Ord \<alpha>" "Ord \<beta>" and \<beta>: "\<beta> < \<alpha>" and minor: "\<And>\<beta> \<gamma>. \<lbrakk>\<beta> < \<alpha>; \<gamma> < \<alpha>; Ord \<gamma>\<rbrakk> \<Longrightarrow> \<beta>+\<gamma> < \<alpha>"
  shows "\<beta>+\<alpha> = \<alpha>"
proof -
  have "\<not> \<beta>+\<alpha> < \<alpha>"
    by (simp add: add_le_left ord leD)
  moreover have "\<not> \<alpha> < \<beta>+\<alpha>"
    by (metis assms le_Ord_diff less_V_def)
  ultimately show ?thesis
    by (simp add: add_le_left less_V_def ord)
qed

lemma indecomposable_imp_eq:
  assumes "indecomposable \<alpha>" "Ord \<beta>" "\<beta> < \<alpha>"
  shows "\<beta>+\<alpha> = \<alpha>"
  by (metis assms indecomposableD indecomposable_def le_Ord_diff less_V_def less_irrefl)

lemma indecomposable2:
  assumes y: "y < x" and z: "z < x" and minor: "\<And>y::V. y < x \<Longrightarrow> y+x = x"
  shows "y+z < x"
  by (metis add_less_cancel_left y z minor)

lemma indecomposable_imp_Limit:
  assumes indec: "indecomposable \<alpha>" and "\<alpha> > 1"
  shows "Limit \<alpha>"
  using indecomposable_imp_Ord [OF indec]
proof (cases rule: Ord_cases)
  case (succ \<beta>)
  then show ?thesis
    using assms one_V_def by auto
qed (use assms in auto)

lemma eq_imp_indecomposable:
  assumes "Ord \<alpha>" "\<And>\<beta>::V. \<beta> \<in> elts \<alpha> \<Longrightarrow> \<beta>+\<alpha> = \<alpha>"
  shows "indecomposable \<alpha>"
  by (metis add_mem_right_cancel assms indecomposable_def)

lemma indecomposable_\<omega>_power:
  assumes "Ord \<delta>"
  shows "indecomposable (\<omega>\<up>\<delta>)"
  unfolding indecomposable_def
proof (intro conjI ballI)
  show "Ord (\<omega>\<up>\<delta>)"
    by (simp add: \<open>Ord \<delta>\<close>)
next
  fix \<beta> \<gamma>
  assume asm: "\<beta> \<in> elts (\<omega>\<up>\<delta>)" "\<gamma> \<in> elts (\<omega>\<up>\<delta>)"
  then obtain ord: "Ord \<beta>" "Ord \<gamma>" and \<beta>: "\<beta> < \<omega>\<up>\<delta>" and \<gamma>: "\<gamma> < \<omega>\<up>\<delta>"
    by (meson Ord_\<omega> Ord_in_Ord Ord_oexp OrdmemD \<open>Ord \<delta>\<close>)
  show "\<beta> + \<gamma> \<in> elts (\<omega>\<up>\<delta>)"
    using \<open>Ord \<delta>\<close>
  proof (cases \<delta> rule: Ord_cases)
    case 0
    then show ?thesis
      using \<open>Ord \<delta>\<close> asm by auto
  next
    case (succ l)
    have "\<exists>x\<in>elts \<omega>. \<beta> + \<gamma> \<in> elts (\<omega>\<up>l * x)"
      if x: "x \<in> elts \<omega>" "\<beta> \<in> elts (\<omega>\<up>l * x)" and y: "y \<in> elts \<omega>" "\<gamma> \<in> elts (\<omega>\<up>l * y)"
      for x y
    proof -
      obtain "Ord x" "Ord y" "Ord (\<omega>\<up>l * x)" "Ord (\<omega>\<up>l * y)"
        using Ord_\<omega> Ord_mult Ord_oexp x y nat_into_Ord succ(1) by presburger
      then have "\<beta> + \<gamma> \<in> elts (\<omega>\<up>l * (x+y))"
        using add_mult_distrib Ord_add Ord_mem_iff_lt add_strict_mono ord x y by presburger
      then show ?thesis
        using x y by blast
    qed
    then show ?thesis
      using \<open>Ord \<delta>\<close> succ ord \<beta> \<gamma> by (auto simp: mult_Limit simp flip: Ord_mem_iff_lt)
  next
    case limit
    have "Ord (\<omega>\<up>\<delta>)"
      by (simp add: \<open>Ord \<delta>\<close>)
    then obtain x y where x: "x \<in> elts \<delta>" "Ord x" "\<beta> \<in> elts (\<omega>\<up>x)"
      and y: "y \<in> elts \<delta>" "Ord y" "\<gamma> \<in> elts (\<omega>\<up>y)"
      using \<open>Ord \<delta>\<close> limit ord \<beta> \<gamma> oexp_Limit
      by (auto simp flip: Ord_mem_iff_lt intro: Ord_in_Ord)
    then have "succ (x \<squnion> y) \<in> elts \<delta>"
      by (metis Limit_def Ord_linear_le limit sup.absorb2 sup.orderE)
    moreover have "\<beta> + \<gamma> \<in> elts (\<omega>\<up>succ (x \<squnion> y))"
    proof -
      have oxy: "Ord (x \<squnion> y)"
        using Ord_sup x y by blast
      then obtain "\<omega>\<up>x \<le> \<omega>\<up>(x \<squnion> y)" "\<omega>\<up>y \<le> \<omega>\<up>(x \<squnion> y)"
        by (metis Ord_\<omega> Ord_linear_le Ord_mem_iff_less_TC Ord_mem_iff_lt le_TC_def less_le_not_le oexp_mono omega_nonzero sup.absorb2 sup.orderE x(2) y(2))
      then have "\<beta> \<in> elts (\<omega>\<up>(x \<squnion> y))" "\<gamma> \<in> elts (\<omega>\<up>(x \<squnion> y))"
        using x y by blast+
      then have "\<beta> + \<gamma> \<in> elts (\<omega>\<up>(x \<squnion> y) * succ (succ 0))"
        by (metis Ord_\<omega> Ord_add Ord_mem_iff_lt Ord_oexp Ord_sup add_strict_mono mult.right_neutral mult_succ ord one_V_def x(2) y(2))
      then show ?thesis
        apply (simp add: oxy)
        using Ord_\<omega> Ord_mult Ord_oexp Ord_trans mem_0_Ord mult_add_mem_0 oexp_eq_0_iff omega_nonzero oxy succ_in_omega by presburger
    qed
    ultimately show ?thesis
      using ord \<open>Ord (\<omega>\<up>\<delta>)\<close> limit oexp_Limit by auto
  qed
qed

lemma \<omega>_power_imp_eq:
  assumes "\<beta> < \<omega>\<up>\<delta>" "Ord \<beta>" "Ord \<delta>" "\<delta> \<noteq> 0"
  shows "\<beta> + \<omega>\<up>\<delta> = \<omega>\<up>\<delta>"
  by (simp add: assms indecomposable_\<omega>_power indecomposable_imp_eq)

lemma type_imp_indecomposable:
  assumes \<alpha>: "Ord \<alpha>"
    and minor: "\<And>X. X \<subseteq> elts \<alpha> \<Longrightarrow> ordertype X VWF = \<alpha> \<or> ordertype (elts \<alpha> - X) VWF = \<alpha>"
  shows "indecomposable \<alpha>"
  unfolding indecomposable_def
proof (intro conjI ballI)
  fix \<beta> \<gamma>
  assume \<beta>: "\<beta> \<in> elts \<alpha>" and \<gamma>: "\<gamma> \<in> elts \<alpha>"
  then obtain \<beta>\<gamma>: "elts \<beta> \<subseteq> elts \<alpha>" "elts \<gamma> \<subseteq> elts \<alpha>" "Ord \<beta>" "Ord \<gamma>"
    using \<alpha> Ord_in_Ord Ord_trans by blast
 then have oeq: "ordertype (elts \<beta>) VWF = \<beta>"
    by auto
  show "\<beta> + \<gamma> \<in> elts \<alpha>"
  proof (rule ccontr)
    assume "\<beta> + \<gamma> \<notin> elts \<alpha>"
    then obtain \<delta> where \<delta>: "Ord \<delta>" "\<beta> + \<delta> = \<alpha>"
      by (metis Ord_ordertype \<beta>\<gamma>(1) le_Ord_diff less_eq_V_def minor oeq)
    then have "\<delta> \<in> elts \<alpha>"
      using Ord_linear \<beta>\<gamma> \<gamma> \<open>\<beta> + \<gamma> \<notin> elts \<alpha>\<close> by blast
    then have "ordertype (elts \<alpha> - elts \<beta>) VWF = \<delta>"
      using \<delta> ordertype_diff Limit_def \<alpha> \<open>Ord \<beta>\<close> by blast
    then show False
      by (metis \<beta> \<open>\<delta> \<in> elts \<alpha>\<close> \<open>elts \<beta> \<subseteq> elts \<alpha>\<close> oeq mem_not_refl minor)
  qed
qed (use assms in auto)


text \<open>This proof uses Cantor normal form, yet still is rather long\<close>
proposition indecomposable_is_\<omega>_power:
  assumes inc: "indecomposable \<mu>"
  obtains "\<mu> = 0" | \<delta> where "Ord \<delta>" "\<mu> = \<omega>\<up>\<delta>"
proof (cases "\<mu> = 0")
  case True
  then show thesis
    by (simp add: that)
next
  case False
  obtain "Ord \<mu>"
    using Limit_def assms indecomposable_def by blast
  then obtain \<alpha>s ms where Cantor: "List.set \<alpha>s \<subseteq> ON" "list.set ms \<subseteq> {0<..}"
                                "length \<alpha>s = length ms" "Cantor_dec \<alpha>s"
    and \<mu>: "\<mu> = Cantor_sum \<alpha>s ms"
    using Cantor_nf_exists by blast
  consider (0) "length \<alpha>s = 0" | (1) "length \<alpha>s = 1" | (2) "length \<alpha>s \<ge> 2"
    by linarith
  then show thesis
  proof cases
    case 0
    then show ?thesis
      using \<mu> assms False indecomposable_def by auto
  next
    case 1
    then obtain \<alpha> m where \<alpha>m: "\<alpha>s = [\<alpha>]" "ms = [m]"
      by (metis One_nat_def \<open>length \<alpha>s = length ms\<close> length_0_conv length_Suc_conv)
    then obtain "Ord \<alpha>" "m \<noteq> 0" "Ord (\<omega>\<up>\<alpha>)"
      using \<open>list.set \<alpha>s \<subseteq> ON\<close> \<open>list.set ms \<subseteq> {0<..}\<close> by auto
    have \<mu>: "\<mu> = \<omega>\<up>\<alpha> * ord_of_nat m"
      using \<alpha>m by (simp add: \<mu>)
    moreover have "m = 1"
    proof (rule ccontr)
      assume "m \<noteq> 1"
      then have 2: "m \<ge> 2"
        using \<open>m \<noteq> 0\<close> by linarith
      then have "m = Suc 0 + Suc 0 + (m-2)"
        by simp
      then have "ord_of_nat m = 1 + 1 + ord_of_nat (m-2)"
        by (metis add.left_neutral mult.left_neutral mult_succ ord_of_nat.simps ord_of_nat_add)
      then have \<mu>eq: "\<mu> = \<omega>\<up>\<alpha> + \<omega>\<up>\<alpha> + \<omega>\<up>\<alpha> * ord_of_nat (m-2)"
        using \<mu> by (simp add: add_mult_distrib)
      moreover have less: "\<omega>\<up>\<alpha> < \<mu>"
        by (metis Ord_\<omega> OrdmemD \<mu>eq \<open>Ord \<alpha>\<close> add_le_cancel_left0 add_less_cancel_left0 le_less_trans less_V_def oexp_gt_0_iff zero_in_omega)
      moreover have "\<omega>\<up>\<alpha> + \<omega>\<up>\<alpha> * ord_of_nat (m-2) < \<mu>"
        using "2" "\<mu>" \<open>Ord \<alpha>\<close> assms less indecomposableD less_V_def by auto
      ultimately show False
        using indecomposableD [OF inc, of "\<omega>\<up>\<alpha>" "\<omega>\<up>\<alpha> + \<omega>\<up>\<alpha> * ord_of_nat (m-2)"]
        by (simp add: \<open>Ord (\<omega>\<up>\<alpha>)\<close> add.assoc)
    qed
    moreover have "Ord \<alpha>"
      using \<open>List.set \<alpha>s \<subseteq> ON\<close> by (simp add: \<open>\<alpha>s = [\<alpha>]\<close>)
    ultimately show ?thesis
      by (metis One_nat_def mult.right_neutral ord_of_nat.simps one_V_def that(2))
  next
    case 2
    then obtain \<alpha>1 \<alpha>2 \<alpha>s' m1 m2 ms' where \<alpha>m: "\<alpha>s = \<alpha>1#\<alpha>2#\<alpha>s'" "ms = m1#m2#ms'"
      by (metis Cantor(3) One_nat_def Suc_1 impossible_Cons length_Cons list.size(3) not_numeral_le_zero remdups_adj.cases)
    then obtain "Ord \<alpha>1" "Ord \<alpha>2" "m1 \<noteq> 0" "m2 \<noteq> 0" "Ord (\<omega>\<up>\<alpha>1)" "Ord (\<omega>\<up>\<alpha>2)"
                "list.set \<alpha>s' \<subseteq> ON" "list.set ms' \<subseteq> {0<..}"
      using \<open>list.set \<alpha>s \<subseteq> ON\<close> \<open>list.set ms \<subseteq> {0<..}\<close> by auto
    have oCs: "Ord (Cantor_sum \<alpha>s' ms')"
      by (simp add: Ord_Cantor_sum \<open>list.set \<alpha>s' \<subseteq> ON\<close>)
    have \<alpha>21: "\<alpha>2 \<in> elts \<alpha>1"
      using Cantor_dec_Cons_iff \<alpha>m(1) \<open>Cantor_dec \<alpha>s\<close>
      by (simp add: Ord_mem_iff_lt \<open>Ord \<alpha>1\<close> \<open>Ord \<alpha>2\<close>)
    have "\<omega>\<up>\<alpha>2 \<noteq> 0"
      by (simp add: \<open>Ord \<alpha>2\<close>)
    then have *: "(\<omega>\<up>\<alpha>2 * ord_of_nat m2 + Cantor_sum \<alpha>s' ms') > 0"
      by (simp add: OrdmemD \<open>Ord (\<omega>\<up>\<alpha>2)\<close> \<open>m2 \<noteq> 0\<close> mem_0_Ord oCs)
    have \<mu>: "\<mu> = \<omega>\<up>\<alpha>1 * ord_of_nat m1 + (\<omega>\<up>\<alpha>2 * ord_of_nat m2 + Cantor_sum \<alpha>s' ms')"
      (is "\<mu> = ?\<alpha> + ?\<beta>")
      using \<alpha>m by (simp add: \<mu>)
    moreover
    have "\<omega>\<up>\<alpha>2 * ord_of_nat m2 + Cantor_sum \<alpha>s' ms' < \<omega>\<up>\<alpha>1 * ord_of_nat m1 + (\<omega>\<up>\<alpha>2 * ord_of_nat m2 + Cantor_sum \<alpha>s' ms')"
      if "\<alpha>2 \<in> elts \<alpha>1"
    proof (rule less_\<omega>_power)
      show "Cantor_sum \<alpha>s' ms' < \<omega>\<up>\<alpha>2"
        using \<alpha>m Cantor cnf_2 by auto
    qed (use oCs \<open>Ord \<alpha>1\<close> \<open>m1 \<noteq> 0\<close> \<open>m2 \<noteq> 0\<close> that in auto)
    then have "?\<beta> < \<mu>"
      using \<alpha>21 by (simp add: \<mu> \<alpha>m)
    moreover have less: "?\<alpha> < \<mu>"
      using oCs by (metis \<mu> "*" add_less_cancel_left add.right_neutral)
    ultimately have False
      using indecomposableD [OF inc, of "?\<alpha>" "?\<beta>"]
      by (simp add: \<open>Ord (\<omega>\<up>\<alpha>1)\<close> \<open>Ord (\<omega>\<up>\<alpha>2)\<close> oCs)
    then show ?thesis ..
  qed
qed

corollary indecomposable_iff_\<omega>_power:
   "indecomposable \<mu> \<longleftrightarrow> \<mu> = 0 \<or> (\<exists>\<delta>. \<mu> = \<omega>\<up>\<delta> \<and> Ord \<delta>)"
  by (meson indecomposable_0 indecomposable_\<omega>_power indecomposable_is_\<omega>_power)

theorem indecomposable_imp_type:
  fixes X :: "bool \<Rightarrow> V set"
  assumes \<gamma>: "indecomposable \<gamma>"
    and "\<And>b. ordertype (X b) VWF \<le> \<gamma>" "\<And>b. small (X b)" "\<And>b. X b \<subseteq> ON"
    and "elts \<gamma> \<subseteq> (UN b. X b)"
  shows "\<exists>b. ordertype (X b) VWF = \<gamma>"
  using \<gamma> [THEN indecomposable_imp_Ord] assms
proof (induction arbitrary: X)
  case (succ \<beta>)
  show ?case
  proof (cases "\<beta> = 0")
    case True
    then have "\<exists>b. 0 \<in> X b"
      using succ.prems(5) by blast
    then have "\<exists>b. ordertype (X b) VWF \<noteq> 0"
      using succ.prems(3) by auto
    then have "\<exists>b. ordertype (X b) VWF \<ge> succ 0"
      by (meson Ord_0 Ord_linear2 Ord_ordertype less_eq_V_0_iff succ_le_iff)
    then show ?thesis
      using True succ.prems(2) by blast
  next
    case False
    then show ?thesis
      using succ.prems by auto
  qed
next
  case (Limit \<gamma>)
  then obtain \<delta> where \<delta>: "\<gamma> = \<omega>\<up>\<delta>" and "\<delta> \<noteq> 0" "Ord \<delta>"
    by (metis Limit_eq_Sup_self image_ident indecomposable_is_\<omega>_power not_succ_Limit oexp_0_right one_V_def zero_not_Limit)
  show ?case
  proof (cases "Limit \<delta>")
    case True
    have ot: "\<exists>b. ordertype (X b \<inter> elts (\<omega>\<up>\<alpha>)) VWF = \<omega>\<up>\<alpha>"
      if "\<alpha> \<in> elts \<delta>" for \<alpha>
    proof (rule Limit.IH)
      have "Ord \<alpha>"
        using Ord_in_Ord \<open>Ord \<delta>\<close> that by blast
      then show "\<omega>\<up>\<alpha> \<in> elts \<gamma>"
        by (simp add: Ord_mem_iff_lt \<delta> \<omega>_gt1 \<open>Ord \<delta>\<close> oexp_less that)
      show "indecomposable (\<omega>\<up>\<alpha>)"
        using \<open>Ord \<alpha>\<close> indecomposable_1 indecomposable_\<omega>_power by fastforce
      show "small (X b \<inter> elts (\<omega>\<up>\<alpha>))" for b
        by (meson down inf_le2)
      show "ordertype (X b \<inter> elts (\<omega> \<up> \<alpha>)) VWF \<le> \<omega> \<up> \<alpha>" for b
        by (simp add: \<open>Ord \<alpha>\<close> ordertype_le_Ord)
      show "X b \<inter> elts (\<omega> \<up> \<alpha>) \<subseteq> ON" for b
        by (simp add: Limit.prems inf.coboundedI1)
      show "elts (\<omega> \<up> \<alpha>) \<subseteq> (\<Union>b. X b \<inter> elts (\<omega> \<up> \<alpha>))"
        using Limit.prems Limit.hyps \<open>\<omega> \<up> \<alpha> \<in> elts \<gamma>\<close>
        by clarsimp (metis Ord_trans UN_E indecomposable_imp_Ord subset_eq)
    qed
    define A where "A \<equiv> \<lambda>b. {\<alpha> \<in> elts \<delta>. ordertype (X b \<inter> elts (\<omega>\<up>\<alpha>)) VWF \<ge> \<omega>\<up>\<alpha>}"
    have Asmall: "small (A b)" for b
      by (simp add: A_def)
    have AON: "A b \<subseteq> ON" for b
      using A_def \<open>Ord \<delta>\<close> elts_subset_ON by blast
    have eq: "elts \<delta> = (\<Union> b. A b)"
      by (auto simp: A_def) (metis ot eq_refl)
    then obtain b where b: "Sup (A b) = \<delta>"
      using \<open>Limit \<delta>\<close>
      apply (auto simp: UN_bool_eq)
      by (metis AON ON_imp_Ord Ord_Sup Ord_linear_le Limit_eq_Sup_self Sup_Un_distrib Asmall sup.absorb2 sup.orderE)
    have "\<omega>\<up>\<alpha> \<le> ordertype (X b) VWF" if "\<alpha> \<in> A b" for \<alpha>
    proof -
      have "(\<omega>\<up>\<alpha>) = ordertype ((X b) \<inter> elts (\<omega>\<up>\<alpha>)) VWF"
        using \<open>Ord \<delta>\<close> that by (simp add: A_def Ord_in_Ord dual_order.antisym ordertype_le_Ord)
      also have "\<dots> \<le> ordertype (X b) VWF"
        by (simp add: Limit.prems ordertype_VWF_mono)
      finally show ?thesis .
    qed
    then have "ordertype (X b) VWF \<ge> Sup ((\<lambda>\<alpha>. \<omega>\<up>\<alpha>) ` A b)"
      by blast
    moreover have "Sup ((\<lambda>\<alpha>. \<omega>\<up>\<alpha>) ` A b) = \<omega> \<up> Sup (A b)"
      by (metis b Ord_\<omega> ZFC_in_HOL.Sup_empty AON \<open>\<delta> \<noteq> 0\<close> Asmall oexp_Sup omega_nonzero)
    ultimately show ?thesis
      using Limit.hyps Limit.prems \<delta> b by auto
  next
    case False
    then obtain \<beta> where \<beta>: "\<delta> = succ \<beta>" "Ord \<beta>"
      using Ord_cases \<open>\<delta> \<noteq> 0\<close> \<open>Ord \<delta>\<close> by auto
    then have Ord\<omega>\<beta>: "Ord (\<omega>\<up>\<beta>)"
      using Ord_oexp by blast
    have subX12: "elts (\<omega>\<up>\<beta> * \<omega>) \<subseteq> (\<Union>b. X b)"
      using Limit \<beta> \<delta> by auto
    define E where "E \<equiv> \<lambda>n. {\<omega>\<up>\<beta> * ord_of_nat n ..< \<omega>\<up>\<beta> * ord_of_nat (Suc n)} \<inter> ON"
    have EON: "E n \<subseteq> ON" for n
      using E_def by blast
    have E_imp_less: "x < y" if "i < j" "x \<in> E i" "y \<in> E j" for x y i j
    proof -
      have "succ (i) \<le> ord_of_nat j"
        using that(1) by force
      then have "\<not> y \<le> x"
        using that
        apply (auto simp: E_def)
        by (metis Ord\<omega>\<beta> Ord_ord_of_nat leD mult_cancel_le_iff ord_of_nat.simps(2) order_trans)
      with that show ?thesis
        by (meson EON ON_imp_Ord Ord_linear2)
    qed
    then have djE: "disjnt (E i) (E j)" if "i \<noteq> j" for i j
      using that nat_neq_iff unfolding disjnt_def by auto
    have less_imp_E: "i \<le> j" if "x < y" "x \<in> E i" "y \<in> E j" for x y i j
      using that E_imp_less [OF _ \<open>y \<in> E j\<close> \<open>x \<in> E i\<close>] leI less_asym by blast
    have inc: "indecomposable (\<omega>\<up>\<beta>)"
      using \<beta> indecomposable_1 indecomposable_\<omega>_power by fastforce
    have in_En: "\<omega>\<up>\<beta> * ord_of_nat n + x \<in> E n" if "x \<in> elts (\<omega>\<up>\<beta>)" for x n
      using that Ord\<omega>\<beta> Ord_in_Ord [OF Ord\<omega>\<beta>] by (auto simp: E_def Ord\<omega>\<beta> OrdmemD mult_succ)
    have *: "elts \<gamma> = \<Union>(range E)"
    proof
      have "\<exists>m. \<omega>\<up>\<beta> * m \<le> x \<and> x < \<omega>\<up>\<beta> * succ (ord_of_nat m)"
        if "x \<in> elts (\<omega>\<up>\<beta> * ord_of_nat n)" for x n
        using that
        apply (clarsimp simp add: mult [of _ "ord_of_nat n"] lift_def)
        by (metis add_less_cancel_left OrdmemD inc indecomposable_imp_Ord mult_succ plus sup_ge1)
      moreover have "Ord x" if "x \<in> elts (\<omega>\<up>\<beta> * ord_of_nat n)" for x n
        by (meson Ord\<omega>\<beta> Ord_in_Ord Ord_mult Ord_ord_of_nat that)
      ultimately show "elts \<gamma> \<subseteq> \<Union>(range E)"
        by (auto simp: \<delta> \<beta> E_def mult_Limit elts_\<omega>)
      have "x \<in> elts (\<omega>\<up>\<beta> * succ(ord_of_nat n))"
        if "Ord x" "x < \<omega>\<up>\<beta> * succ (n)" for x n
        by (metis that Ord_mem_iff_lt Ord_mult Ord_ord_of_nat inc indecomposable_imp_Ord ord_of_nat.simps(2))
      then show "\<Union>(range E) \<subseteq> elts \<gamma>"
        by (force simp: \<delta> \<beta> E_def Limit.prems mult_Limit)
    qed
    have smE: "small (E n)" for n
      by (metis "*" complete_lattice_class.Sup_upper down rangeI)
    have otE: "ordertype (E n) VWF = \<omega>\<up>\<beta>" for n
      by (simp add: E_def inc indecomposable_imp_Ord mult_succ ordertype_interval_eq)

    define cut where "cut \<equiv> \<lambda>n x. odiff x (\<omega>\<up>\<beta> * ord_of_nat n)"
    have cutON: "cut n ` X \<subseteq> ON" if "X \<subseteq> ON" for n X
      using that by (simp add: image_subset_iff cut_def ON_imp_Ord Ord\<omega>\<beta> Ord_odiff)
    have cut [simp]: "cut n (\<omega> \<up> \<beta> * ord_of_nat n + x) = x" for x n
      by (auto simp: cut_def)
    have cuteq: "x \<in> cut n ` (X \<inter> E n) \<longleftrightarrow> \<omega>\<up>\<beta> * ord_of_nat n + x \<in> X"
      if x: "x \<in> elts (\<omega>\<up>\<beta>)" for x X n
    proof
      show "\<omega>\<up>\<beta> * ord_of_nat n + x \<in> X" if "x \<in> cut n ` (X \<inter> E n)"
        using E_def Ord\<omega>\<beta> Ord_odiff_eq image_iff local.cut_def that by auto
      show "x \<in> cut n ` (X \<inter> E n)"
        if "\<omega>\<up>\<beta> * ord_of_nat n + x \<in> X"
        by (metis (full_types) IntI cut image_iff in_En that x)
    qed
    have ot_cuteq: "ordertype (cut n ` (X \<inter> E n)) VWF = ordertype (X \<inter> E n) VWF" for n X
    proof (rule ordertype_VWF_inc_eq)
      show "X \<inter> E n \<subseteq> ON"
        using E_def by blast
      then show "cut n ` (X \<inter> E n) \<subseteq> ON"
        by (simp add: cutON)
      show "small (X \<inter> E n)"
        by (meson Int_lower2 smE smaller_than_small)
      show "cut n x < cut n y"
        if "x \<in> X \<inter> E n" "y \<in> X \<inter> E n" "x < y" for x y
        using that \<open>X \<inter> E n \<subseteq> ON\<close> by(simp add: E_def Ord\<omega>\<beta> Ord_odiff_less_odiff local.cut_def)
    qed

    define N where "N \<equiv> \<lambda>b. {n. ordertype (X b \<inter> E n) VWF = \<omega>\<up>\<beta>}"
    have "\<exists>b. infinite (N b)"
    proof (rule ccontr)
      assume "\<nexists>b. infinite (N b)"
      then obtain n where "\<And>b. n \<notin> N b"
        apply (simp add: ex_bool_eq)
        by (metis (full_types) finite_nat_set_iff_bounded not_less_iff_gr_or_eq)
      moreover
      have "\<exists>b. ordertype (cut n ` (X b \<inter> E n)) VWF = \<omega>\<up>\<beta>"
      proof (rule Limit.IH)
        show "\<omega>\<up>\<beta> \<in> elts \<gamma>"
          by (metis Limit.hyps Limit_def Limit_omega Ord_mem_iff_less_TC \<beta> \<delta> mult_le2 not_succ_Limit oexp_succ omega_nonzero one_V_def)
        show "indecomposable (\<omega>\<up>\<beta>)"
          by (simp add: inc)
        show "ordertype (cut n ` (X b \<inter> E n)) VWF \<le> \<omega>\<up>\<beta>" for b
          by (metis "otE" inf_le2 ordertype_VWF_mono ot_cuteq smE)
        show "small (cut n ` (X b \<inter> E n))" for b
          using smE subset_iff_less_eq_V
          by (meson inf_le2 replacement)
        show "cut n ` (X b \<inter> E n) \<subseteq> ON" for b
          using E_def cutON by auto
        have "elts (\<omega>\<up>\<beta> * succ n) \<subseteq> \<Union>(range X)"
          by (metis Ord\<omega>\<beta> Ord_\<omega> Ord_ord_of_nat less_eq_V_def mult_cancel_le_iff ord_of_nat.simps(2) ord_of_nat_le_omega order_trans subX12)
        then show "elts (\<omega>\<up>\<beta>) \<subseteq> (\<Union>b. cut n ` (X b \<inter> E n))"
          by (auto simp: mult_succ mult_Limit UN_subset_iff cuteq UN_bool_eq)
      qed
      then have "\<exists>b. ordertype (X b \<inter> E n) VWF = \<omega>\<up>\<beta>"
        by (simp add: ot_cuteq)
      ultimately show False
        by (simp add: N_def)
    qed
    then obtain b where b: "infinite (N b)"
      by blast
      then obtain \<phi> :: "nat \<Rightarrow> nat" where \<phi>: "bij_betw \<phi> UNIV (N b)" and mono: "strict_mono \<phi>"
        by (meson bij_enumerate enumerate_mono strict_mono_def)
      then have "ordertype (X b \<inter> E (\<phi> n)) VWF = \<omega>\<up>\<beta>" for n
        using N_def bij_betw_imp_surj_on by blast
      moreover have "small (X b \<inter> E (\<phi> n))" for n
        by (meson inf_le2 smE subset_iff_less_eq_V)
      ultimately have "\<exists>f. bij_betw f (X b \<inter> E (\<phi> n)) (elts (\<omega>\<up>\<beta>)) \<and> (\<forall>x \<in> X b \<inter> E (\<phi> n). \<forall>y \<in> X b \<inter> E (\<phi> n). f x < f y \<longleftrightarrow> (x,y) \<in> VWF)"
        for n by (metis Ord_ordertype ordertype_VWF_eq_iff)
      then obtain F where bijF: "\<And>n. bij_betw (F n) (X b \<inter> E (\<phi> n)) (elts (\<omega>\<up>\<beta>))"
              and F: "\<And>n. \<forall>x \<in> X b \<inter> E (\<phi> n). \<forall>y \<in> X b \<inter> E (\<phi> n). F n x < F n y \<longleftrightarrow> (x,y) \<in> VWF"
        by metis
      then have F_bound: "\<And>n. \<forall>x \<in> X b \<inter> E (\<phi> n). F n x < \<omega>\<up>\<beta>"
        by (metis Ord_\<omega> Ord_oexp OrdmemD \<beta>(2) bij_betw_imp_surj_on image_eqI)
      have F_Ord: "\<And>n. \<forall>x \<in> X b \<inter> E (\<phi> n). Ord (F n x)"
        by (metis otE ON_imp_Ord Ord_ordertype bijF bij_betw_def elts_subset_ON imageI)

      have inc: "\<phi> n \<ge> n" for n
        by (simp add: mono strict_mono_imp_increasing)

      have dj\<phi>: "disjnt (E (\<phi> i)) (E (\<phi> j))" if "i \<noteq> j" for i j
        by (rule djE) (use \<phi> that in \<open>auto simp: bij_betw_def inj_def\<close>)
      define Y where "Y \<equiv> (\<Union>n. E (\<phi> n))"
      have "\<exists>n. y \<in> E (\<phi> n)" if "y \<in> Y" for y
        using Y_def that by blast
      then obtain \<iota> where \<iota>: "\<And>y. y \<in> Y \<Longrightarrow> y \<in> E (\<phi> (\<iota> y))"
        by metis
      have "Y \<subseteq> ON"
        by (auto simp: Y_def E_def)
      have \<iota>le: "\<iota> x \<le> \<iota> y" if "x < y" "x \<in> Y" "y \<in> Y" for x y
        using less_imp_E strict_mono_less_eq that \<iota> [OF \<open>x \<in> Y\<close>] \<iota> [OF \<open>y \<in> Y\<close>] mono
        unfolding Y_def by blast
      have eq\<iota>: "x \<in> E (\<phi> k) \<Longrightarrow> \<iota> x = k" for x k
        using \<iota> unfolding Y_def
        by (meson UN_I disjnt_iff dj\<phi> iso_tuple_UNIV_I)

      have upper: "\<omega>\<up>\<beta> * ord_of_nat (\<iota> x) \<le> x" if "x \<in> Y" for x
        using that
      proof (clarsimp simp add: Y_def eq\<iota>)
        fix u v
        assume u: "u \<in> elts (\<omega>\<up>\<beta> * ord_of_nat v)" and v: "x \<in> E (\<phi> v)"
        then have "u < \<omega>\<up>\<beta> * ord_of_nat v"
          by (simp add: OrdmemD \<beta>(2))
        also have "\<dots> \<le> \<omega>\<up>\<beta> * ord_of_nat (\<phi> v)"
          by (simp add: \<beta>(2) inc)
        also have "\<dots> \<le> x"
          using v by (simp add: E_def)
        finally show "u \<in> elts x"
          using \<open>Y \<subseteq> ON\<close>
          by (meson ON_imp_Ord Ord_\<omega> Ord_in_Ord Ord_mem_iff_lt Ord_mult Ord_oexp Ord_ord_of_nat \<beta>(2) that u)
      qed

      define G where "G \<equiv> \<lambda>x. \<omega>\<up>\<beta> * ord_of_nat (\<iota> x) + F (\<iota> x) x"
      have G_strict_mono: "G x < G y" if "x < y" "x \<in> X b \<inter> Y" "y \<in> X b \<inter> Y" for x y
      proof (cases "\<iota> x = \<iota> y")
        case True
        then show ?thesis
          using that unfolding G_def
          by (metis F Int_iff add_less_cancel_left Limit.prems(4) ON_imp_Ord VWF_iff_Ord_less \<iota>)
      next
        case False
        then have "\<iota> x < \<iota> y"
          by (meson IntE \<iota>le le_less that)
        then show ?thesis
          using that by (simp add: G_def F_Ord F_bound Ord\<omega>\<beta> \<iota> mult_nat_less_add_less)
      qed

      have "ordertype (X b \<inter> Y) VWF = (\<omega>\<up>\<beta>) * \<omega>"
      proof (rule ordertype_VWF_eq_iff [THEN iffD2])
        show "Ord (\<omega>\<up>\<beta> * \<omega>)"
          by (simp add: \<beta>)
        show "small (X b \<inter> Y)"
          by (meson Limit.prems(3) inf_le1 subset_iff_less_eq_V)
        have "bij_betw G (X b \<inter> Y) (elts (\<omega>\<up>\<beta> * \<omega>))"
        proof (rule bij_betw_imageI)
          show "inj_on G (X b \<inter> Y)"
          proof (rule linorder_inj_onI)
            fix x y
            assume xy: "x < y" "x \<in> (X b \<inter> Y)" "y \<in> (X b \<inter> Y)"
            show "G x \<noteq> G y"
              using G_strict_mono xy by force
          next
            show "x \<le> y \<or> y \<le> x"
              if "x \<in> (X b \<inter> Y)" "y \<in> (X b \<inter> Y)" for x y
              using that \<open>X b \<subseteq> ON\<close> by (clarsimp simp: Y_def) (metis ON_imp_Ord Ord_linear Ord_trans)
          qed
          show "G ` (X b \<inter> Y) = elts (\<omega>\<up>\<beta> * \<omega>)"
          proof
            show "G ` (X b \<inter> Y) \<subseteq> elts (\<omega>\<up>\<beta> * \<omega>)"
              using \<open>X b \<subseteq> ON\<close>
              apply (clarsimp simp: G_def mult_Limit Y_def eq\<iota>)
              by (metis IntI add_mem_right_cancel bijF bij_betw_imp_surj_on image_eqI mult_succ ord_of_nat_\<omega> succ_in_omega)
            show "elts (\<omega>\<up>\<beta> * \<omega>) \<subseteq> G ` (X b \<inter> Y)"
            proof
              fix x
              assume x: "x \<in> elts (\<omega>\<up>\<beta> * \<omega>)"
              then obtain k where n: "x \<in> elts (\<omega>\<up>\<beta> * ord_of_nat (Suc k))"
                          and minim: "\<And>m. m < Suc k \<Longrightarrow> x \<notin> elts (\<omega>\<up>\<beta> * ord_of_nat m)"
                using elts_mult_\<omega>E
                by (metis old.nat.exhaust)
              then obtain y where y: "y \<in> elts (\<omega>\<up>\<beta>)" and xeq: "x = \<omega>\<up>\<beta> * ord_of_nat k + y"
                using x by (auto simp: mult_succ elim: mem_plus_V_E)
              then have 1: "inv_into (X b \<inter> E (\<phi> k)) (F k) y \<in> (X b \<inter> E (\<phi> k))"
                by (metis bijF bij_betw_def inv_into_into)
              then have "(inv_into (X b \<inter> E (\<phi> k)) (F k) y) \<in> X b \<inter> Y"
                by (force simp: Y_def)
              moreover have "G (inv_into (X b \<inter> E (\<phi> k)) (F k) y) = x"
                by (metis "1" G_def Int_iff bijF bij_betw_inv_into_right eq\<iota> xeq y)
                ultimately show "x \<in> G ` (X b \<inter> Y)"
                  by blast
            qed
          qed
        qed
        moreover have "(x,y) \<in> VWF"
          if "x \<in> X b" "x \<in> Y" "y \<in> X b" "y \<in> Y" "G x < G y" for x y
        proof -
          have "x < y"
            using that by (metis G_strict_mono Int_iff Limit.prems(4) ON_imp_Ord Ord_linear_lt less_asym)
          then show ?thesis
            using ON_imp_Ord \<open>Y \<subseteq> ON\<close> that by auto
        qed
        moreover have "G x < G y"
          if "x \<in> X b" "x \<in> Y" "y \<in> X b" "y \<in> Y" "(x, y) \<in> VWF" for x y
        proof -
          have "x < y"
            using that ON_imp_Ord \<open>Y \<subseteq> ON\<close> by auto
          then show ?thesis
            by (simp add: G_strict_mono that)
        qed
        ultimately show "\<exists>f. bij_betw f (X b \<inter> Y) (elts (\<omega>\<up>\<beta> * \<omega>)) \<and> (\<forall>x\<in>(X b \<inter> Y). \<forall>y\<in>(X b \<inter> Y). f x < f y \<longleftrightarrow> ((x, y) \<in> VWF))"
          by blast
      qed
      moreover have "ordertype (\<Union>n. X b \<inter> E (\<phi> n)) VWF \<le> ordertype (X b) VWF"
        using Limit.prems(3) ordertype_VWF_mono by auto
      ultimately have "ordertype (X b) VWF = (\<omega>\<up>\<beta>) * \<omega>"
        using Limit.hyps Limit.prems(2) \<beta> \<delta>
        using Y_def by auto
      then show ?thesis
        using Limit.hyps \<beta> \<delta> by auto
    qed
qed auto

corollary indecomposable_imp_type2:
  assumes \<alpha>: "indecomposable \<gamma>" "X \<subseteq> elts \<gamma>"
  shows "ordertype X VWF = \<gamma> \<or> ordertype (elts \<gamma> - X) VWF = \<gamma>"
proof -
  have "Ord \<gamma>"
    using assms indecomposable_imp_Ord by blast
  have "\<exists>b. ordertype (if b then X else elts \<gamma> - X) VWF = \<gamma>"
  proof (rule indecomposable_imp_type)
    show "ordertype (if b then X else elts \<gamma> - X) VWF \<le> \<gamma>" for b
      by (simp add: \<open>Ord \<gamma>\<close> assms ordertype_le_Ord)
    show "(if b then X else elts \<gamma> - X) \<subseteq> ON" for b
      using \<open>Ord \<gamma>\<close> assms elts_subset_ON by auto
  qed (use assms down in auto)
  then show ?thesis
    by (metis (full_types))
qed

subsection \<open>From ordinals to order types\<close>

lemma indecomposable_ordertype_eq:
  assumes indec: "indecomposable \<alpha>" and \<alpha>: "ordertype A VWF = \<alpha>" and A: "B \<subseteq> A" "small A"
  shows "ordertype B VWF = \<alpha> \<or> ordertype (A-B) VWF = \<alpha>"
proof (rule ccontr)
  assume "\<not> (ordertype B VWF = \<alpha> \<or> ordertype (A - B) VWF = \<alpha>)"
  moreover have "ordertype (ordermap A VWF ` B) VWF = ordertype B VWF"
    using \<open>B \<subseteq> A\<close> by (auto intro: ordertype_image_ordermap [OF \<open>small A\<close>])
  moreover have "ordertype (elts \<alpha> - ordermap A VWF ` B) VWF = ordertype (A - B) VWF"
    by (metis ordertype_map_image \<alpha> A elts_of_set ordertype_def replacement)
  moreover have "ordermap A VWF ` B \<subseteq> elts \<alpha>"
    using \<alpha> A by blast
  ultimately show False
    using indecomposable_imp_type2 [OF \<open>indecomposable \<alpha>\<close>]  \<open>small A\<close> by metis
qed

lemma indecomposable_ordertype_ge:
  assumes indec: "indecomposable \<alpha>" and \<alpha>: "ordertype A VWF \<ge> \<alpha>" and small: "small A" "small B"
  shows "ordertype B VWF \<ge> \<alpha> \<or> ordertype (A-B) VWF \<ge> \<alpha>"
proof -
  obtain A' where "A' \<subseteq> A" "ordertype A' VWF = \<alpha>"
    by (meson \<alpha> \<open>small A\<close> indec indecomposable_def le_ordertype_obtains_subset)
  then have "ordertype (B \<inter> A') VWF = \<alpha> \<or> ordertype (A'-B) VWF = \<alpha>"
    by (metis Diff_Diff_Int Diff_subset Int_commute \<open>small A\<close> indecomposable_ordertype_eq indec smaller_than_small)
  moreover have "ordertype (B \<inter> A') VWF \<le> ordertype B VWF"
    by (meson Int_lower1 small ordertype_VWF_mono smaller_than_small)
  moreover have "ordertype (A'-B) VWF \<le> ordertype (A-B) VWF"
    by (meson Diff_mono Diff_subset \<open>A' \<subseteq> A\<close> \<open>small A\<close> order_refl ordertype_VWF_mono smaller_than_small)
  ultimately show ?thesis
    by blast
qed

text \<open>now for finite partitions\<close>
lemma indecomposable_ordertype_finite_eq:
  assumes "indecomposable \<alpha>"
    and \<A>: "finite \<A>" "pairwise disjnt \<A>" "\<Union>\<A> = A" "\<A> \<noteq> {}" "ordertype A VWF = \<alpha>" "small A"
  shows "\<exists>X \<in> \<A>. ordertype X VWF = \<alpha>"
  using \<A>
proof (induction arbitrary: A)
  case (insert X \<A>)
  show ?case
  proof (cases "\<A> = {}")
    case True
    then show ?thesis
      using insert.prems by blast
  next
    case False
    have smA: "small (\<Union>\<A>)"
      using insert.prems by auto
    show ?thesis
    proof (cases "\<exists>X \<in> \<A>. ordertype X VWF = \<alpha>")
      case True
      then show ?thesis
        using insert.prems by blast
    next
      case False
      have "X = A - \<Union>\<A>"
        using insert.hyps insert.prems by (auto simp: pairwise_insert disjnt_iff)
      then have "ordertype X VWF = \<alpha>"
        using indecomposable_ordertype_eq assms insert False
        by (metis Union_mono cSup_singleton pairwise_insert smA subset_insertI)
      then show ?thesis
        using insert.prems by blast
    qed
  qed
qed auto

lemma indecomposable_ordertype_finite_ge:
  assumes indec: "indecomposable \<alpha>"
    and \<A>: "finite \<A>" "A \<subseteq> \<Union>\<A>" "\<A> \<noteq> {}" "ordertype A VWF \<ge> \<alpha>" "small (\<Union>\<A>)"
  shows "\<exists>X \<in> \<A>. ordertype X VWF \<ge> \<alpha>"
  using \<A>
proof (induction arbitrary: A)
  case (insert X \<A>)
  show ?case
  proof (cases "\<A> = {}")
    case True
    then have "\<alpha> \<le> ordertype X VWF"
      using insert.prems
      by (simp add: order.trans ordertype_VWF_mono)
    then show ?thesis
      using insert.prems by blast
  next
    case False
    show ?thesis
    proof (cases "\<exists>X \<in> \<A>. ordertype X VWF \<ge> \<alpha>")
      case True
      then show ?thesis
        using insert.prems by blast
    next
      case False
      moreover have "small (X \<union> \<Union>\<A>)"
        using insert.prems by auto
      moreover have "ordertype (\<Union>(insert X \<A>)) VWF \<ge> \<alpha>"
        using insert.prems ordertype_VWF_mono by blast
      ultimately have "ordertype X VWF \<ge> \<alpha>"
        using indecomposable_ordertype_ge [OF indec]
        by (metis Diff_subset_conv Sup_insert cSup_singleton insert.IH small_sup_iff subset_refl)
      then show ?thesis
        using insert.prems by blast
    qed
  qed
qed auto

end
