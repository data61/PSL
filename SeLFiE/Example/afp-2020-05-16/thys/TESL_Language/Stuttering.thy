subsection\<open>Main Theorems\<close>

theory Stuttering
imports StutteringLemmas

begin

text \<open>
  Using the lemmas of the previous section about the invariance by stuttering
  of various properties of TESL specifications, we can now prove that the atomic 
  formulae that compose TESL specifications are invariant by stuttering.
\<close>

text \<open>Sporadic specifications are preserved in a dilated run.\<close>
lemma sporadic_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> \<lbrakk>c sporadic \<tau> on c'\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    shows \<open>r \<in> \<lbrakk>c sporadic \<tau> on c'\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof -
  from assms(1) is_subrun_def obtain f
    where \<open>dilating f sub r\<close> by blast
  hence \<open>\<forall>n c. time ((Rep_run sub) n c) = time ((Rep_run r) (f n) c)
           \<and> hamlet ((Rep_run sub) n c) = hamlet ((Rep_run r) (f n) c)\<close> by (simp add: dilating_def)
  moreover from assms(2) have
    \<open>sub \<in> {r. \<exists> n. hamlet ((Rep_run r) n c) \<and> time ((Rep_run r) n c') = \<tau>}\<close> by simp
  from this obtain k where \<open>time ((Rep_run sub) k c') = \<tau> \<and> hamlet ((Rep_run sub) k c)\<close> by auto
  ultimately have \<open>time ((Rep_run r) (f k) c') = \<tau> \<and> hamlet ((Rep_run r) (f k) c)\<close> by simp
  thus ?thesis by auto
qed

text \<open>Implications are preserved in a dilated run.\<close>
theorem implies_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> \<lbrakk>c\<^sub>1 implies c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    shows \<open>r \<in> \<lbrakk>c\<^sub>1 implies c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof -
  from assms(1) is_subrun_def obtain f where \<open>dilating f sub r\<close> by blast
  moreover from assms(2) have
    \<open>sub \<in> {r. \<forall>n. hamlet ((Rep_run r) n c\<^sub>1) \<longrightarrow> hamlet ((Rep_run r) n c\<^sub>2)}\<close> by simp
  hence \<open>\<forall>n. hamlet ((Rep_run sub) n c\<^sub>1) \<longrightarrow> hamlet ((Rep_run sub) n c\<^sub>2)\<close> by simp
  ultimately have \<open>\<forall>n. hamlet ((Rep_run r) n c\<^sub>1) \<longrightarrow> hamlet ((Rep_run r) n c\<^sub>2)\<close>
    using ticks_imp_ticks_subk ticks_sub by blast
  thus ?thesis by simp
qed

theorem implies_not_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> \<lbrakk>c\<^sub>1 implies not c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    shows \<open>r \<in> \<lbrakk>c\<^sub>1 implies not c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof -
  from assms(1) is_subrun_def obtain f where \<open>dilating f sub r\<close> by blast
  moreover from assms(2) have
    \<open>sub \<in> {r. \<forall>n. hamlet ((Rep_run r) n c\<^sub>1) \<longrightarrow> \<not> hamlet ((Rep_run r) n c\<^sub>2)}\<close> by simp
  hence \<open>\<forall>n. hamlet ((Rep_run sub) n c\<^sub>1) \<longrightarrow> \<not> hamlet ((Rep_run sub) n c\<^sub>2)\<close> by simp
  ultimately have \<open>\<forall>n. hamlet ((Rep_run r) n c\<^sub>1) \<longrightarrow> \<not> hamlet ((Rep_run r) n c\<^sub>2)\<close>
    using ticks_imp_ticks_subk ticks_sub by blast
  thus ?thesis by simp
qed

text \<open>Precedence relations are preserved in a dilated run.\<close>
theorem weakly_precedes_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> \<lbrakk>c\<^sub>1 weakly precedes c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    shows \<open>r \<in> \<lbrakk>c\<^sub>1 weakly precedes c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof -
  from assms(1) is_subrun_def obtain f where *:\<open>dilating f sub r\<close> by blast
  from assms(2) have
    \<open>sub \<in> {r. \<forall>n. (run_tick_count r c\<^sub>2 n) \<le> (run_tick_count r c\<^sub>1 n)}\<close> by simp
  hence \<open>\<forall>n. (run_tick_count sub c\<^sub>2 n) \<le> (run_tick_count sub c\<^sub>1 n)\<close> by simp
  from dil_tick_count[OF assms(1) this]
    have \<open>\<forall>n. (run_tick_count r c\<^sub>2 n) \<le> (run_tick_count r c\<^sub>1 n)\<close> by simp
  thus ?thesis by simp
qed

theorem strictly_precedes_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> \<lbrakk>c\<^sub>1 strictly precedes c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    shows \<open>r \<in> \<lbrakk>c\<^sub>1 strictly precedes c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof -
  from assms(1) is_subrun_def obtain f where *:\<open>dilating f sub r\<close> by blast
  from assms(2) have
    \<open>sub \<in> { \<rho>. \<forall>n::nat. (run_tick_count \<rho> c\<^sub>2 n) \<le> (run_tick_count_strictly \<rho> c\<^sub>1 n) }\<close>
  by simp
  with strictly_precedes_alt_def2[of \<open>c\<^sub>2\<close> \<open>c\<^sub>1\<close>]  have
    \<open>sub \<in> { \<rho>. (\<not>hamlet ((Rep_run \<rho>) 0 c\<^sub>2))
  \<and> (\<forall>n::nat. (run_tick_count \<rho> c\<^sub>2 (Suc n)) \<le> (run_tick_count \<rho> c\<^sub>1 n)) }\<close>
  by blast
  hence \<open>(\<not>hamlet ((Rep_run sub) 0 c\<^sub>2))
       \<and> (\<forall>n::nat. (run_tick_count sub c\<^sub>2 (Suc n)) \<le> (run_tick_count sub c\<^sub>1 n))\<close>
    by simp
  hence
    1:\<open>(\<not>hamlet ((Rep_run sub) 0 c\<^sub>2))
     \<and> (\<forall>n::nat. (tick_count sub c\<^sub>2 (Suc n)) \<le> (tick_count sub c\<^sub>1 n))\<close>
  by (simp add: tick_count_is_fun)
  have \<open>\<forall>n::nat. (tick_count r c\<^sub>2 (Suc n)) \<le> (tick_count r c\<^sub>1 n)\<close>
  proof -
    { fix n::nat
      have \<open>tick_count r c\<^sub>2 (Suc n) \<le> tick_count r c\<^sub>1 n\<close>
      proof (cases \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>)
        case True \<comment> \<open>n is in the image of f\<close>
          from this obtain n\<^sub>0 where fn:\<open>f n\<^sub>0 = n\<close> by blast
          show ?thesis
          proof (cases \<open>\<exists>sn\<^sub>0. f sn\<^sub>0 = Suc n\<close>)
            case True \<comment> \<open>Suc n is in the image of f\<close>
              from this obtain sn\<^sub>0 where fsn:\<open>f sn\<^sub>0 = Suc n\<close> by blast
              with fn strict_mono_suc * have \<open>sn\<^sub>0 = Suc n\<^sub>0\<close>
                using  dilating_def dilating_fun_def by blast
              with 1 have \<open>tick_count sub c\<^sub>2 sn\<^sub>0 \<le> tick_count sub c\<^sub>1 n\<^sub>0\<close> by simp
              thus ?thesis using fn fsn tick_count_sub[OF *] by simp
          next
            case False \<comment> \<open>Suc n is not in the image of f\<close>
              hence \<open>\<not>hamlet ((Rep_run r) (Suc n) c\<^sub>2)\<close>
                using * by (simp add: dilating_def dilating_fun_def)
              hence \<open>tick_count r c\<^sub>2 (Suc n) = tick_count r c\<^sub>2 n\<close>
                by (simp add: tick_count_suc)
              also have \<open>... = tick_count sub c\<^sub>2 n\<^sub>0\<close>
                using fn tick_count_sub[OF *] by simp
              finally have \<open>tick_count r c\<^sub>2 (Suc n) = tick_count sub c\<^sub>2 n\<^sub>0\<close> .
              moreover have \<open>tick_count sub c\<^sub>2 n\<^sub>0 \<le> tick_count sub c\<^sub>2 (Suc n\<^sub>0)\<close>
                by (simp add: tick_count_suc)
              ultimately have
                \<open>tick_count r c\<^sub>2 (Suc n) \<le> tick_count sub c\<^sub>2 (Suc n\<^sub>0)\<close> by simp
              moreover have
                \<open>tick_count sub c\<^sub>2 (Suc n\<^sub>0) \<le> tick_count sub c\<^sub>1 n\<^sub>0\<close> using 1 by simp
              ultimately have \<open>tick_count r c\<^sub>2 (Suc n) \<le> tick_count sub c\<^sub>1 n\<^sub>0\<close> by simp
              thus ?thesis using tick_count_sub[OF *] fn by simp
          qed
      next
        case False \<comment> \<open>n is not in the image of f\<close>
          from greatest_prev_image[OF * this] obtain n\<^sub>p  where
            np_prop:\<open>f n\<^sub>p < n \<and> (\<forall>k. f n\<^sub>p < k \<and> k \<le> n \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close> by blast
          from tick_count_latest[OF * this] have
            \<open>tick_count r c\<^sub>1 n = tick_count r c\<^sub>1 (f n\<^sub>p)\<close> . 
          hence a:\<open>tick_count r c\<^sub>1 n = tick_count sub c\<^sub>1 n\<^sub>p\<close>
            using tick_count_sub[OF *] by simp
          have b: \<open>tick_count sub c\<^sub>2 (Suc n\<^sub>p) \<le> tick_count sub c\<^sub>1 n\<^sub>p\<close> using 1 by simp
          show ?thesis
          proof (cases \<open>\<exists>sn\<^sub>0. f sn\<^sub>0 = Suc n\<close>)
            case True \<comment> \<open>Suc n is in the image of f\<close>
              from this obtain sn\<^sub>0 where fsn:\<open>f sn\<^sub>0 = Suc n\<close> by blast
              from next_non_stuttering[OF * np_prop this]  have sn_prop:\<open>sn\<^sub>0 = Suc n\<^sub>p\<close> .
              with b have \<open>tick_count sub c\<^sub>2 sn\<^sub>0 \<le> tick_count sub c\<^sub>1 n\<^sub>p\<close> by simp
              thus ?thesis using tick_count_sub[OF *] fsn a by auto
          next
            case False \<comment> \<open>Suc n is not in the image of f\<close>
              hence \<open>\<not>hamlet ((Rep_run r) (Suc n) c\<^sub>2)\<close>
                using * by (simp add: dilating_def dilating_fun_def)
              hence \<open>tick_count r c\<^sub>2 (Suc n) = tick_count r c\<^sub>2 n\<close>
                by (simp add: tick_count_suc)
              also have \<open>... = tick_count sub c\<^sub>2 n\<^sub>p\<close> using np_prop tick_count_sub[OF *]
                by (simp add: tick_count_latest[OF * np_prop])
              finally have \<open>tick_count r c\<^sub>2 (Suc n) = tick_count sub c\<^sub>2 n\<^sub>p\<close> .
              moreover have \<open>tick_count sub c\<^sub>2 n\<^sub>p \<le> tick_count sub c\<^sub>2 (Suc n\<^sub>p)\<close>
                by (simp add: tick_count_suc)
              ultimately have
                \<open>tick_count r c\<^sub>2 (Suc n) \<le> tick_count sub c\<^sub>2 (Suc n\<^sub>p)\<close> by simp
              moreover have
                \<open>tick_count sub c\<^sub>2 (Suc n\<^sub>p) \<le> tick_count sub c\<^sub>1 n\<^sub>p\<close> using 1 by simp
              ultimately have \<open>tick_count r c\<^sub>2 (Suc n) \<le> tick_count sub c\<^sub>1 n\<^sub>p\<close> by simp
              thus ?thesis using np_prop mono_tick_count  using a by linarith
          qed
      qed
    } thus ?thesis ..
  qed
  moreover from 1 have \<open>\<not>hamlet ((Rep_run r) 0 c\<^sub>2)\<close>
    using * empty_dilated_prefix ticks_sub by fastforce
  ultimately show ?thesis by (simp add: tick_count_is_fun strictly_precedes_alt_def2) 
qed

text \<open>
  Time delayed relations are preserved in a dilated run.
\<close>
theorem time_delayed_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> \<lbrakk> a time-delayed by \<delta>\<tau> on ms implies b \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    shows \<open>r \<in> \<lbrakk> a time-delayed by \<delta>\<tau> on ms implies b \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof -
  from assms(1) is_subrun_def obtain f where *:\<open>dilating f sub r\<close> by blast
  from assms(2) have \<open>\<forall>n. hamlet ((Rep_run sub) n a)
                          \<longrightarrow> (\<forall>m \<ge> n. first_time sub ms m (time ((Rep_run sub) n ms) + \<delta>\<tau>)
                                       \<longrightarrow> hamlet ((Rep_run sub) m b))\<close>
    using TESL_interpretation_atomic.simps(5)[of \<open>a\<close> \<open>\<delta>\<tau>\<close> \<open>ms\<close> \<open>b\<close>] by simp
  hence **:\<open>\<forall>n\<^sub>0. hamlet ((Rep_run r) (f n\<^sub>0) a)
                  \<longrightarrow> (\<forall>m\<^sub>0 \<ge> n\<^sub>0. first_time r ms (f m\<^sub>0) (time ((Rep_run r) (f n\<^sub>0) ms) + \<delta>\<tau>)
                                  \<longrightarrow> hamlet ((Rep_run r) (f m\<^sub>0) b))  \<close>
    using first_time_image[OF *] dilating_def * by fastforce
  hence \<open>\<forall>n. hamlet ((Rep_run r) n a)
                  \<longrightarrow> (\<forall>m \<ge> n. first_time r ms m (time ((Rep_run r) n ms) + \<delta>\<tau>)
                                \<longrightarrow> hamlet ((Rep_run r) m b))\<close>
  proof -
    { fix n assume assm:\<open>hamlet ((Rep_run r) n a)\<close>
      from ticks_image_sub[OF * assm] obtain n\<^sub>0 where nfn0:\<open>n = f n\<^sub>0\<close> by blast
      with ** assm have ft0:
        \<open>(\<forall>m\<^sub>0 \<ge> n\<^sub>0. first_time r ms (f m\<^sub>0) (time ((Rep_run r) (f n\<^sub>0) ms) + \<delta>\<tau>)
                    \<longrightarrow> hamlet ((Rep_run r) (f m\<^sub>0) b))\<close> by blast
      have \<open>(\<forall>m \<ge> n. first_time r ms m (time ((Rep_run r) n ms) + \<delta>\<tau>) 
                       \<longrightarrow> hamlet ((Rep_run r) m b)) \<close>
      proof -
      { fix m assume hyp:\<open>m \<ge> n\<close>
        have \<open>first_time r ms m (time (Rep_run r n ms) + \<delta>\<tau>) \<longrightarrow> hamlet (Rep_run r m b)\<close>
        proof (cases \<open>\<exists>m\<^sub>0. f m\<^sub>0 = m\<close>)
          case True
          from this obtain m\<^sub>0 where \<open>m = f m\<^sub>0\<close> by blast
          moreover have \<open>strict_mono f\<close> using * by (simp add: dilating_def dilating_fun_def)
          ultimately show ?thesis using ft0 hyp nfn0 by (simp add: strict_mono_less_eq)
        next
          case False thus ?thesis
          proof (cases \<open>m = 0\<close>)
            case True
              hence \<open>m = f 0\<close> using * by (simp add: dilating_def dilating_fun_def)
              then show ?thesis using False by blast
          next
            case False
            hence \<open>\<exists>pm. m = Suc pm\<close> by (simp add: not0_implies_Suc)
            from this obtain pm where mpm:\<open>m = Suc pm\<close> by blast
            hence \<open>\<nexists>pm\<^sub>0. f pm\<^sub>0 = Suc pm\<close> using \<open>\<nexists>m\<^sub>0. f m\<^sub>0 = m\<close> by simp 
            with *  have \<open>time (Rep_run r (Suc pm) ms) = time (Rep_run r pm ms)\<close>
              using dilating_def dilating_fun_def by blast
            hence \<open>time (Rep_run r pm ms) = time (Rep_run r m ms)\<close> using mpm by simp
            moreover from mpm have \<open>pm < m\<close> by simp
            ultimately have \<open>\<exists>m' < m. time (Rep_run r m' ms) = time (Rep_run r m ms)\<close> by blast
            hence \<open>\<not>(first_time r ms m (time (Rep_run r n ms) + \<delta>\<tau>))\<close>
              by (auto simp add: first_time_def)
            thus ?thesis by simp
          qed
        qed
      } thus ?thesis by simp
      qed
    } thus ?thesis by simp
  qed
  thus ?thesis by simp
qed

text \<open>Time relations are preserved through dilation of a run.\<close>
lemma tagrel_sub':
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> \<lbrakk> time-relation \<lfloor>c\<^sub>1,c\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    shows \<open>R (time ((Rep_run r) n c\<^sub>1), time ((Rep_run r) n c\<^sub>2))\<close>
proof -
  from assms(1) is_subrun_def obtain f where *:\<open>dilating f sub r\<close> by blast
  moreover from assms(2) TESL_interpretation_atomic.simps(2) have
    \<open>sub \<in> {r. \<forall>n. R (time ((Rep_run r) n c\<^sub>1), time ((Rep_run r) n c\<^sub>2))}\<close> by blast
  hence 1:\<open>\<forall>n. R (time ((Rep_run sub) n c\<^sub>1), time ((Rep_run sub) n c\<^sub>2))\<close> by simp
  show ?thesis
  proof (induction n)
    case 0
      from 1 have \<open>R (time ((Rep_run sub) 0 c\<^sub>1), time ((Rep_run sub) 0 c\<^sub>2))\<close> by simp
      moreover from * have \<open>f 0 = 0\<close> by (simp add: dilating_def dilating_fun_def)
      moreover from * have \<open>\<forall>c. time ((Rep_run sub) 0 c) = time ((Rep_run r) (f 0) c)\<close>
        by (simp add: dilating_def)
      ultimately show ?case by simp
  next
    case (Suc n)
    then show ?case
    proof (cases \<open>\<nexists>n\<^sub>0. f n\<^sub>0 = Suc n\<close>)
      case True
      with * have \<open>\<forall>c. time (Rep_run r (Suc n) c) = time (Rep_run r n c)\<close>
        by (simp add: dilating_def dilating_fun_def) 
      thus ?thesis using Suc.IH by simp
    next
      case False
      from this obtain n\<^sub>0 where n\<^sub>0prop:\<open>f n\<^sub>0 = Suc n\<close> by blast
      from 1 have \<open>R (time ((Rep_run sub) n\<^sub>0 c\<^sub>1), time ((Rep_run sub) n\<^sub>0 c\<^sub>2))\<close> by simp
      moreover from n\<^sub>0prop * have \<open>time ((Rep_run sub) n\<^sub>0 c\<^sub>1) = time ((Rep_run r) (Suc n) c\<^sub>1)\<close>
        by (simp add: dilating_def)
      moreover from n\<^sub>0prop * have \<open>time ((Rep_run sub) n\<^sub>0 c\<^sub>2) = time ((Rep_run r) (Suc n) c\<^sub>2)\<close>
        by (simp add: dilating_def)
      ultimately show ?thesis by simp
    qed
  qed
qed

corollary tagrel_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> \<lbrakk> time-relation \<lfloor>c\<^sub>1,c\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    shows \<open>r \<in> \<lbrakk> time-relation \<lfloor>c\<^sub>1,c\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
using tagrel_sub'[OF assms] unfolding TESL_interpretation_atomic.simps(3) by simp

text \<open>Time relations are also preserved by contraction\<close>
lemma tagrel_sub_inv:
  assumes \<open>sub \<lless> r\<close>
      and \<open>r \<in> \<lbrakk> time-relation \<lfloor>c\<^sub>1, c\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    shows \<open>sub \<in> \<lbrakk> time-relation \<lfloor>c\<^sub>1, c\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof -
  from assms(1) is_subrun_def obtain f where df:\<open>dilating f sub r\<close> by blast
  moreover from assms(2) TESL_interpretation_atomic.simps(2) have
    \<open>r \<in> {\<rho>. \<forall>n. R (time ((Rep_run \<rho>) n c\<^sub>1), time ((Rep_run \<rho>) n c\<^sub>2))}\<close> by blast
  hence \<open>\<forall>n. R (time ((Rep_run r) n c\<^sub>1), time ((Rep_run r) n c\<^sub>2))\<close> by simp
  hence \<open>\<forall>n. (\<exists>n\<^sub>0. f n\<^sub>0 = n) \<longrightarrow> R (time ((Rep_run r) n c\<^sub>1), time ((Rep_run r) n c\<^sub>2))\<close> by simp
  hence \<open>\<forall>n\<^sub>0. R (time ((Rep_run r) (f n\<^sub>0) c\<^sub>1), time ((Rep_run r) (f n\<^sub>0) c\<^sub>2))\<close> by blast
  moreover from dilating_def df have
    \<open>\<forall>n c. time ((Rep_run sub) n c) = time ((Rep_run r) (f n) c)\<close> by blast
  ultimately have \<open>\<forall>n\<^sub>0. R (time ((Rep_run sub) n\<^sub>0 c\<^sub>1), time ((Rep_run sub) n\<^sub>0 c\<^sub>2))\<close> by auto
  thus ?thesis by simp
qed

text \<open>
  Kill relations are preserved in a dilated run.
\<close>
theorem kill_sub:
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> \<lbrakk> c\<^sub>1 kills c\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    shows \<open>r \<in> \<lbrakk> c\<^sub>1 kills c\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof -
  from assms(1) is_subrun_def obtain f where *:\<open>dilating f sub r\<close> by blast
  from assms(2) TESL_interpretation_atomic.simps(8) have
    \<open>\<forall>n. hamlet (Rep_run sub n c\<^sub>1) \<longrightarrow> (\<forall>m\<ge>n. \<not> hamlet (Rep_run sub m c\<^sub>2))\<close> by simp
  hence 1:\<open>\<forall>n. hamlet (Rep_run r (f n) c\<^sub>1) \<longrightarrow> (\<forall>m\<ge>n. \<not> hamlet (Rep_run r (f m) c\<^sub>2))\<close>
    using ticks_sub[OF *] by simp
  hence \<open>\<forall>n. hamlet (Rep_run r (f n) c\<^sub>1) \<longrightarrow> (\<forall>m\<ge> (f n). \<not> hamlet (Rep_run r m c\<^sub>2))\<close>
  proof -
    { fix n assume \<open>hamlet (Rep_run r (f n) c\<^sub>1)\<close>
      with 1 have 2:\<open>\<forall> m \<ge> n. \<not> hamlet (Rep_run r (f m) c\<^sub>2)\<close> by simp
      have \<open>\<forall> m\<ge> (f n). \<not> hamlet (Rep_run r m c\<^sub>2)\<close>
      proof -
        { fix m assume h:\<open>m \<ge> f n\<close>
          have \<open>\<not> hamlet (Rep_run r m c\<^sub>2)\<close>
          proof (cases \<open>\<exists>m\<^sub>0. f m\<^sub>0 = m\<close>)
            case True
              from this obtain m\<^sub>0 where fm0:\<open>f m\<^sub>0 = m\<close> by blast
              hence \<open>m\<^sub>0 \<ge> n\<close>
                using * dilating_def dilating_fun_def h strict_mono_less_eq by fastforce
              with 2 show ?thesis using fm0 by blast
          next
            case False
              thus ?thesis  using ticks_image_sub'[OF *] by blast
          qed
        } thus ?thesis by simp
      qed
    } thus ?thesis by simp
  qed
  hence \<open>\<forall>n. hamlet (Rep_run r n c\<^sub>1) \<longrightarrow> (\<forall>m \<ge> n. \<not> hamlet (Rep_run r m c\<^sub>2))\<close>
    using ticks_imp_ticks_subk[OF *] by blast
  thus ?thesis using TESL_interpretation_atomic.simps(8) by blast
qed

lemmas atomic_sub_lemmas = sporadic_sub tagrel_sub implies_sub implies_not_sub
                           time_delayed_sub weakly_precedes_sub
                           strictly_precedes_sub kill_sub

text \<open>
  We can now prove that all atomic specification formulae are preserved
  by the dilation of runs.
\<close>
lemma atomic_sub: 
  assumes \<open>sub \<lless> r\<close>
      and \<open>sub \<in> \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    shows \<open>r \<in> \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
using assms(2) atomic_sub_lemmas[OF assms(1)] by (cases \<phi>, simp_all)

text \<open>
  Finally, any TESL specification is invariant by stuttering.
\<close>
theorem TESL_stuttering_invariant:
  assumes \<open>sub \<lless> r\<close>
    shows \<open>sub \<in> \<lbrakk>\<lbrakk> S \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<Longrightarrow> r \<in> \<lbrakk>\<lbrakk> S \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof (induction S)
  case Nil
    thus ?case by simp
next
  case (Cons a s)
    from Cons.prems have sa:\<open>sub \<in> \<lbrakk> a \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close> and sb:\<open>sub \<in> \<lbrakk>\<lbrakk> s \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
      using TESL_interpretation_image by simp+
    from Cons.IH[OF sb] have \<open>r \<in> \<lbrakk>\<lbrakk> s \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close> .
    moreover from atomic_sub[OF assms(1) sa] have \<open>r \<in> \<lbrakk> a \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close> .
    ultimately show ?case using  TESL_interpretation_image by simp
qed

end
