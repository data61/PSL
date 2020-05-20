subsection\<open>Stuttering Lemmas\<close>

theory StutteringLemmas

imports StutteringDefs

begin

text \<open>
  In this section, we prove several lemmas that will be used to show that TESL 
  specifications are invariant by stuttering.

  The following one will be useful in proving properties over a sequence of 
  stuttering instants.
\<close>
lemma bounded_suc_ind:
  assumes \<open>\<And>k. k < m \<Longrightarrow> P (Suc (z + k)) = P (z + k)\<close>
    shows \<open>k < m \<Longrightarrow> P (Suc (z + k)) = P z\<close>
proof (induction k)
  case 0
    with assms(1)[of 0] show ?case by simp
next
  case (Suc k')
    with assms[of \<open>Suc k'\<close>] show ?case by force
qed

subsection \<open>Lemmas used to prove the invariance by stuttering\<close>

text \<open>Since a dilating function is strictly monotonous, it is injective.\<close>

lemma dilating_fun_injects:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>inj_on f A\<close>
using assms dilating_fun_def strict_mono_imp_inj_on by blast

lemma dilating_injects:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>inj_on f A\<close>
using assms dilating_def dilating_fun_injects by blast

text \<open>
  If a clock ticks at an instant in a dilated run, that instant is the image
  by the dilating function of an instant of the original run.
\<close>
lemma ticks_image:
  assumes \<open>dilating_fun f r\<close>
  and     \<open>hamlet ((Rep_run r) n c)\<close>
  shows   \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>
using dilating_fun_def assms by blast

lemma ticks_image_sub:
  assumes \<open>dilating f sub r\<close>
  and     \<open>hamlet ((Rep_run r) n c)\<close>
  shows   \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>
using assms dilating_def ticks_image by blast

lemma ticks_image_sub':
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>c. hamlet ((Rep_run r) n c)\<close>
  shows   \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>
using ticks_image_sub[OF assms(1)] assms(2) by blast


text \<open> 
  The image of the ticks in an interval by a dilating function is the interval 
  bounded by the image of the bounds of the original interval.
  This is proven for all 4 kinds of intervals:  \<^verbatim>\<open>]m, n[\<close>, \<^verbatim>\<open>[m, n[\<close>, \<^verbatim>\<open>]m, n]\<close>
  and \<^verbatim>\<open>[m, n]\<close>.
\<close>

lemma dilating_fun_image_strict:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>{k. f m < k \<and> k < f n \<and> hamlet ((Rep_run r) k c)}
            = image f {k. m < k \<and> k < n \<and> hamlet ((Rep_run r) (f k) c)}\<close>
  (is \<open>?IMG = image f ?SET\<close>)
proof
  { fix k assume h:\<open>k \<in> ?IMG\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k \<and> hamlet ((Rep_run r) (f k\<^sub>0) c)\<close>
      using ticks_image[OF assms] by blast
    with h have \<open>k \<in> image f ?SET\<close>
      using assms dilating_fun_def strict_mono_less by blast
  } thus \<open>?IMG \<subseteq> image f ?SET\<close> ..
next
  { fix k assume h:\<open>k \<in> image f ?SET\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET\<close> by blast
    hence \<open>k \<in> ?IMG\<close> using assms by (simp add: dilating_fun_def strict_mono_less)
  } thus \<open>image f ?SET \<subseteq> ?IMG\<close> ..
qed

lemma dilating_fun_image_left:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>{k. f m \<le> k \<and> k < f n \<and> hamlet ((Rep_run r) k c)}
          = image f {k. m \<le> k \<and> k < n \<and> hamlet ((Rep_run r) (f k) c)}\<close>
  (is \<open>?IMG = image f ?SET\<close>)
proof
  { fix k assume h:\<open>k \<in> ?IMG\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k \<and> hamlet ((Rep_run r) (f k\<^sub>0) c)\<close>
      using ticks_image[OF assms] by blast
    with h have \<open>k \<in> image f ?SET\<close>
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus \<open>?IMG \<subseteq> image f ?SET\<close> ..
next
  { fix k assume h:\<open>k \<in> image f ?SET\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET\<close> by blast
    hence \<open>k \<in> ?IMG\<close>
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus \<open>image f ?SET \<subseteq> ?IMG\<close> ..
qed

lemma dilating_fun_image_right:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>{k. f m < k \<and> k \<le> f n \<and> hamlet ((Rep_run r) k c)}
          = image f {k. m < k \<and> k \<le> n \<and> hamlet ((Rep_run r) (f k) c)}\<close>
  (is \<open>?IMG = image f ?SET\<close>)
proof
  { fix k assume h:\<open>k \<in> ?IMG\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k \<and> hamlet ((Rep_run r) (f k\<^sub>0) c)\<close>
      using ticks_image[OF assms] by blast
    with h have \<open>k \<in> image f ?SET\<close>
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus \<open>?IMG \<subseteq> image f ?SET\<close> ..
next
  { fix k assume h:\<open>k \<in> image f ?SET\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET\<close> by blast
    hence \<open>k \<in> ?IMG\<close>
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus \<open>image f ?SET \<subseteq> ?IMG\<close> ..
qed

lemma dilating_fun_image:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>{k. f m \<le> k \<and> k \<le> f n \<and> hamlet ((Rep_run r) k c)}
          = image f {k. m \<le> k \<and> k \<le> n \<and> hamlet ((Rep_run r) (f k) c)}\<close>
  (is \<open>?IMG = image f ?SET\<close>)
proof
  { fix k assume h:\<open>k \<in> ?IMG\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k \<and> hamlet ((Rep_run r) (f k\<^sub>0) c)\<close>
      using ticks_image[OF assms] by blast
    with h have \<open>k \<in> image f ?SET\<close>
      using assms dilating_fun_def strict_mono_less_eq by blast
  } thus \<open>?IMG \<subseteq> image f ?SET\<close> ..
next
  { fix k assume h:\<open>k \<in> image f ?SET\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET\<close> by blast
    hence \<open>k \<in> ?IMG\<close> using assms by (simp add: dilating_fun_def strict_mono_less_eq)
  } thus \<open>image f ?SET \<subseteq> ?IMG\<close> ..
qed

text \<open>
  On any clock, the number of ticks in an interval is preserved
  by a dilating function.
\<close>
lemma ticks_as_often_strict:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>card {p. n < p \<and> p < m \<and> hamlet ((Rep_run r) (f p) c)}
          = card {p. f n < p \<and> p < f m \<and> hamlet ((Rep_run r) p c)}\<close>
    (is \<open>card ?SET = card ?IMG\<close>)
proof -
  from dilating_fun_injects[OF assms] have \<open>inj_on f ?SET\<close> .
  moreover have \<open>finite ?SET\<close> by simp
  from inj_on_iff_eq_card[OF this] calculation
    have \<open>card (image f ?SET) = card ?SET\<close> by blast
  moreover from dilating_fun_image_strict[OF assms] have \<open>?IMG = image f ?SET\<close> .
  ultimately show ?thesis by auto
qed

lemma ticks_as_often_left:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>card {p. n \<le> p \<and> p < m \<and> hamlet ((Rep_run r) (f p) c)}
          = card {p. f n \<le> p \<and> p < f m \<and> hamlet ((Rep_run r) p c)}\<close>
    (is \<open>card ?SET = card ?IMG\<close>)
proof -
  from dilating_fun_injects[OF assms] have \<open>inj_on f ?SET\<close> .
  moreover have \<open>finite ?SET\<close> by simp
  from inj_on_iff_eq_card[OF this] calculation
    have \<open>card (image f ?SET) = card ?SET\<close> by blast
  moreover from dilating_fun_image_left[OF assms] have \<open>?IMG = image f ?SET\<close> .
  ultimately show ?thesis by auto
qed

lemma ticks_as_often_right:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>card {p. n < p \<and> p \<le> m \<and> hamlet ((Rep_run r) (f p) c)}
          = card {p. f n < p \<and> p \<le> f m \<and> hamlet ((Rep_run r) p c)}\<close>
    (is \<open>card ?SET = card ?IMG\<close>)
proof -
  from dilating_fun_injects[OF assms] have \<open>inj_on f ?SET\<close> .
  moreover have \<open>finite ?SET\<close> by simp
  from inj_on_iff_eq_card[OF this] calculation
    have \<open>card (image f ?SET) = card ?SET\<close> by blast
  moreover from dilating_fun_image_right[OF assms] have \<open>?IMG = image f ?SET\<close> .
  ultimately show ?thesis by auto
qed

lemma ticks_as_often:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>card {p. n \<le> p \<and> p \<le> m \<and> hamlet ((Rep_run r) (f p) c)}
          = card {p. f n \<le> p \<and> p \<le> f m \<and> hamlet ((Rep_run r) p c)}\<close>
    (is \<open>card ?SET = card ?IMG\<close>)
proof -
  from dilating_fun_injects[OF assms] have \<open>inj_on f ?SET\<close> .
  moreover have \<open>finite ?SET\<close> by simp
  from inj_on_iff_eq_card[OF this] calculation
    have \<open>card (image f ?SET) = card ?SET\<close> by blast
  moreover from dilating_fun_image[OF assms] have \<open>?IMG = image f ?SET\<close> .
  ultimately show ?thesis by auto
qed

text \<open>The date of an event is preserved by dilation.\<close>

lemma ticks_tag_image:
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>c. hamlet ((Rep_run r) k c)\<close>
  and     \<open>time ((Rep_run r) k c) = \<tau>\<close>
  shows   \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k \<and> time ((Rep_run sub) k\<^sub>0 c) = \<tau>\<close>
proof -
  from ticks_image_sub'[OF assms(1,2)] have \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k\<close> .
  from this obtain k\<^sub>0 where \<open>f k\<^sub>0 = k\<close> by blast
  moreover with assms(1,3) have \<open>time ((Rep_run sub) k\<^sub>0 c) = \<tau>\<close>
    by (simp add: dilating_def) 
  ultimately show ?thesis by blast
qed

text \<open>TESL operators are invariant by dilation.\<close>

lemma ticks_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>hamlet ((Rep_run sub) n a) = hamlet ((Rep_run r) (f n) a)\<close>
using assms by (simp add: dilating_def)

lemma no_tick_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>(\<nexists>n\<^sub>0. f n\<^sub>0 = n) \<longrightarrow> \<not>hamlet ((Rep_run r) n a)\<close>
using assms dilating_def dilating_fun_def by blast

text \<open>Lifting a total function to a partial function on an option domain.\<close>

definition opt_lift::\<open>('a \<Rightarrow> 'a) \<Rightarrow> ('a option \<Rightarrow> 'a option)\<close>
where
  \<open>opt_lift f \<equiv> \<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (f y)\<close>

text \<open>
  The set of instants when a clock ticks in a dilated run is the image by the 
  dilation function of the set of instants when it ticks in the subrun.
\<close>
lemma tick_set_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{k. hamlet ((Rep_run r) k c)} = image f {k. hamlet ((Rep_run sub) k c)}\<close>
    (is \<open>?R = image f ?S\<close>)
proof
  { fix k assume h:\<open>k \<in> ?R\<close>
    with no_tick_sub[OF assms] have \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k\<close> by blast
    from this obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k\<close> by blast
    with ticks_sub[OF assms] h have \<open>hamlet ((Rep_run sub) k\<^sub>0 c)\<close> by blast
    with k0prop have \<open>k \<in> image f ?S\<close> by blast
  }
  thus \<open>?R \<subseteq> image f ?S\<close> by blast
next
  { fix k assume h:\<open>k \<in> image f ?S\<close>
    from this obtain k\<^sub>0 where \<open>f k\<^sub>0 = k \<and> hamlet ((Rep_run sub) k\<^sub>0 c)\<close> by blast
    with assms have \<open>k \<in> ?R\<close> using ticks_sub by blast 
  }
  thus \<open>image f ?S \<subseteq> ?R\<close> by blast
qed

text \<open>
  Strictly monotonous functions preserve the least element.
\<close>
lemma Least_strict_mono:
  assumes \<open>strict_mono f\<close>
  and     \<open>\<exists>x \<in> S. \<forall>y \<in> S. x \<le> y\<close>
  shows   \<open>(LEAST y. y \<in> f ` S) = f (LEAST x. x \<in> S)\<close>
using Least_mono[OF strict_mono_mono, OF assms] .

text \<open>
  A non empty set of @{typ nat}s has a least element.
\<close>
lemma Least_nat_ex:
  \<open>(n::nat) \<in> S \<Longrightarrow> \<exists>x \<in> S. (\<forall>y \<in> S. x \<le> y)\<close>
by (induction n rule: nat_less_induct, insert not_le_imp_less, blast)

text \<open>  
  The first instant when a clock ticks in a dilated run is the image by the dilation
  function of the first instant when it ticks in the subrun.
\<close>
lemma Least_sub:
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>k::nat. hamlet ((Rep_run sub) k c)\<close>
  shows   \<open>(LEAST k. k \<in> {t. hamlet ((Rep_run r) t c)})
              = f (LEAST k. k \<in> {t. hamlet ((Rep_run sub) t c)})\<close>
          (is \<open>(LEAST k. k \<in> ?R) = f (LEAST k. k \<in> ?S)\<close>)
proof -
  from assms(2) have \<open>\<exists>x. x \<in> ?S\<close> by simp
  hence least:\<open>\<exists>x \<in> ?S. \<forall>y \<in> ?S. x \<le> y\<close>
    using Least_nat_ex ..
  from assms(1) have \<open>strict_mono f\<close> by (simp add: dilating_def dilating_fun_def)
  from Least_strict_mono[OF this least] have
    \<open>(LEAST y. y \<in> f ` ?S)  = f (LEAST x. x \<in> ?S)\<close> .
  with tick_set_sub[OF assms(1), of \<open>c\<close>] show ?thesis by auto
qed

text \<open>
  If a clock ticks in a run, it ticks in the subrun.
\<close>
lemma ticks_imp_ticks_sub:
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>k. hamlet ((Rep_run r) k c)\<close>
  shows   \<open>\<exists>k\<^sub>0. hamlet ((Rep_run sub) k\<^sub>0 c)\<close>
proof -
  from assms(2) obtain k where \<open>hamlet ((Rep_run r) k c)\<close> by blast
  with ticks_image_sub[OF assms(1)] ticks_sub[OF assms(1)] show ?thesis by blast
qed

text \<open>
  Stronger version: it ticks in the subrun and we know when.
\<close>
lemma ticks_imp_ticks_subk:
  assumes \<open>dilating f sub r\<close>
  and     \<open>hamlet ((Rep_run r) k c)\<close>
  shows   \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k \<and> hamlet ((Rep_run sub) k\<^sub>0 c)\<close>
proof -
  from no_tick_sub[OF assms(1)] assms(2) have \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k\<close> by blast
  from this obtain k\<^sub>0 where \<open>f k\<^sub>0 = k\<close> by blast
  moreover with ticks_sub[OF assms(1)] assms(2)
    have \<open>hamlet ((Rep_run sub) k\<^sub>0 c)\<close> by blast
  ultimately show ?thesis by blast
qed

text \<open>
  A dilating function preserves the tick count on an interval for any clock.
\<close>
lemma dilated_ticks_strict:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f m < i \<and> i < f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. m < i \<and> i < n \<and> hamlet ((Rep_run sub) i c)}\<close>
    (is \<open>?RUN = image f ?SUB\<close>)
proof
  { fix i assume h:\<open>i \<in> ?SUB\<close>
    hence \<open>m < i \<and> i < n\<close> by simp
    hence \<open>f m < f i \<and> f i < (f n)\<close> using assms
      by (simp add: dilating_def dilating_fun_def strict_monoD strict_mono_less_eq)
    moreover from h have \<open>hamlet ((Rep_run sub) i c)\<close> by simp
    hence \<open>hamlet ((Rep_run r) (f i) c)\<close> using ticks_sub[OF assms] by blast
    ultimately have \<open>f i \<in> ?RUN\<close> by simp
  } thus \<open>image f ?SUB \<subseteq> ?RUN\<close> by blast
next
  { fix i assume h:\<open>i \<in> ?RUN\<close>
    hence \<open>hamlet ((Rep_run r) i c)\<close> by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:\<open>f i\<^sub>0 = i \<and> hamlet ((Rep_run sub) i\<^sub>0 c)\<close> by blast
    with h have \<open>f m < f i\<^sub>0 \<and> f i\<^sub>0 < f n\<close> by simp
    moreover have \<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
    ultimately have \<open>m < i\<^sub>0 \<and> i\<^sub>0 < n\<close>
      using strict_mono_less strict_mono_less_eq by blast
    with i0prop have \<open>\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB\<close> by blast
  } thus \<open>?RUN \<subseteq> image f ?SUB\<close> by blast
qed

lemma dilated_ticks_left:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f m \<le> i \<and> i < f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. m \<le> i \<and> i < n \<and> hamlet ((Rep_run sub) i c)}\<close>
    (is \<open>?RUN = image f ?SUB\<close>)
proof
  { fix i assume h:\<open>i \<in> ?SUB\<close>
    hence \<open>m \<le> i \<and> i < n\<close> by simp
    hence \<open>f m \<le> f i \<and> f i < (f n)\<close> using assms
      by (simp add: dilating_def dilating_fun_def strict_monoD strict_mono_less_eq)
    moreover from h have \<open>hamlet ((Rep_run sub) i c)\<close> by simp
    hence \<open>hamlet ((Rep_run r) (f i) c)\<close> using ticks_sub[OF assms] by blast
    ultimately have \<open>f i \<in> ?RUN\<close> by simp
  } thus \<open>image f ?SUB \<subseteq> ?RUN\<close> by blast
next
  { fix i assume h:\<open>i \<in> ?RUN\<close>
    hence \<open>hamlet ((Rep_run r) i c)\<close> by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:\<open>f i\<^sub>0 = i \<and> hamlet ((Rep_run sub) i\<^sub>0 c)\<close> by blast
    with h have \<open>f m \<le> f i\<^sub>0 \<and> f i\<^sub>0 < f n\<close> by simp
    moreover have \<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
    ultimately have \<open>m \<le> i\<^sub>0 \<and> i\<^sub>0 < n\<close>
      using strict_mono_less strict_mono_less_eq by blast
    with i0prop have \<open>\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB\<close> by blast
  } thus \<open>?RUN \<subseteq> image f ?SUB\<close> by blast
qed

lemma dilated_ticks_right:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f m < i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. m < i \<and> i \<le> n \<and> hamlet ((Rep_run sub) i c)}\<close>
    (is \<open>?RUN = image f ?SUB\<close>)
proof
  { fix i  assume h:\<open>i \<in> ?SUB\<close>
    hence \<open>m < i \<and> i \<le> n\<close> by simp
    hence \<open>f m < f i \<and> f i \<le> (f n)\<close> using assms
      by (simp add: dilating_def dilating_fun_def strict_monoD strict_mono_less_eq)
    moreover from h have \<open>hamlet ((Rep_run sub) i c)\<close> by simp
    hence \<open>hamlet ((Rep_run r) (f i) c)\<close> using ticks_sub[OF assms] by blast
    ultimately have \<open>f i \<in> ?RUN\<close> by simp
  } thus \<open>image f ?SUB \<subseteq> ?RUN\<close> by blast
next
  { fix i assume h:\<open>i \<in> ?RUN\<close>
    hence \<open>hamlet ((Rep_run r) i c)\<close> by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:\<open>f i\<^sub>0 = i \<and> hamlet ((Rep_run sub) i\<^sub>0 c)\<close> by blast
    with h have \<open>f m < f i\<^sub>0 \<and> f i\<^sub>0 \<le> f n\<close> by simp
    moreover have \<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
    ultimately have \<open>m < i\<^sub>0 \<and> i\<^sub>0 \<le> n\<close>
      using strict_mono_less strict_mono_less_eq by blast
    with i0prop have \<open>\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB\<close> by blast
  } thus \<open>?RUN \<subseteq> image f ?SUB\<close> by blast
qed

lemma dilated_ticks:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f m \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. m \<le> i \<and> i \<le> n \<and> hamlet ((Rep_run sub) i c)}\<close>
    (is \<open>?RUN = image f ?SUB\<close>)
proof
  { fix i assume h:\<open>i \<in> ?SUB\<close>
    hence \<open>m \<le> i \<and> i \<le> n\<close> by simp
    hence \<open>f m \<le> f i \<and> f i \<le> (f n)\<close>
      using assms by (simp add: dilating_def dilating_fun_def strict_mono_less_eq)
    moreover from h have \<open>hamlet ((Rep_run sub) i c)\<close> by simp
    hence \<open>hamlet ((Rep_run r) (f i) c)\<close> using ticks_sub[OF assms] by blast
    ultimately have \<open>f i \<in>?RUN\<close> by simp
  } thus \<open>image f ?SUB \<subseteq> ?RUN\<close> by blast
next
  { fix i assume h:\<open>i \<in> ?RUN\<close>
    hence \<open>hamlet ((Rep_run r) i c)\<close> by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:\<open>f i\<^sub>0 = i \<and> hamlet ((Rep_run sub) i\<^sub>0 c)\<close> by blast
    with h have \<open>f m \<le> f i\<^sub>0 \<and> f i\<^sub>0 \<le> f n\<close> by simp
    moreover have \<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
    ultimately have \<open>m \<le> i\<^sub>0 \<and> i\<^sub>0 \<le> n\<close> using strict_mono_less_eq by blast
    with i0prop have \<open>\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB\<close> by blast
  } thus \<open>?RUN \<subseteq> image f ?SUB\<close> by blast
qed


text \<open>
  No tick can occur in a dilated run before the image of 0 by the dilation function.
\<close>

lemma empty_dilated_prefix:
  assumes \<open>dilating f sub r\<close>
  and     \<open>n < f 0\<close>
shows   \<open>\<not> hamlet ((Rep_run r) n c)\<close>
proof -
  from assms have False by (simp add: dilating_def dilating_fun_def)
  thus ?thesis ..
qed

corollary empty_dilated_prefix':
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f 0 \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}
         = {i. i \<le> f n \<and> hamlet ((Rep_run r) i c)}\<close>
proof -
  from assms have \<open>strict_mono f\<close> by (simp add: dilating_def dilating_fun_def)
  hence \<open>f 0 \<le> f n\<close> unfolding strict_mono_def by (simp add: less_mono_imp_le_mono)
  hence \<open>\<forall>i. i \<le> f n = (i < f 0) \<or> (f 0 \<le> i \<and> i \<le> f n)\<close> by auto
  hence \<open>{i. i \<le> f n \<and> hamlet ((Rep_run r) i c)}
        = {i. i < f 0 \<and> hamlet ((Rep_run r) i c)}
        \<union> {i. f 0 \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}\<close>
    by auto
  also have \<open>... = {i. f 0 \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}\<close>
     using empty_dilated_prefix[OF assms] by blast
  finally show ?thesis by simp
qed

corollary dilated_prefix:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. i \<le> f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. i \<le> n \<and> hamlet ((Rep_run sub) i c)}\<close>
proof -
  have \<open>{i. 0 \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}
        = image f {i. 0 \<le> i \<and> i \<le> n \<and> hamlet ((Rep_run sub) i c)}\<close>
    using dilated_ticks[OF assms] empty_dilated_prefix'[OF assms] by blast
  thus ?thesis by simp
qed

corollary dilated_strict_prefix:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. i < f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. i < n \<and> hamlet ((Rep_run sub) i c)}\<close>
proof -
  from assms have dil:\<open>dilating_fun f r\<close> unfolding dilating_def by simp
  from dil have f0:\<open>f 0 = 0\<close>  using dilating_fun_def by blast
  from dilating_fun_image_left[OF dil, of \<open>0\<close> \<open>n\<close> \<open>c\<close>]
  have \<open>{i. f 0 \<le> i \<and> i < f n \<and> hamlet ((Rep_run r) i c)}
        = image f {i. 0 \<le> i \<and> i < n \<and> hamlet ((Rep_run r) (f i) c)}\<close> .
  hence \<open>{i. i < f n \<and> hamlet ((Rep_run r) i c)}
        = image f {i. i < n \<and> hamlet ((Rep_run r) (f i) c)}\<close>
    using f0 by simp
  also have \<open>... = image f {i. i < n \<and> hamlet ((Rep_run sub) i c)}\<close>
    using assms dilating_def by blast
  finally show ?thesis by simp
qed

text\<open>A singleton of @{typ nat} can be defined with a weaker property.\<close> 
lemma nat_sing_prop:
  \<open>{i::nat. i = k \<and> P(i)} = {i::nat. i = k \<and> P(k)}\<close>
by auto

text \<open>
  The set definition and the function definition of @{const tick_count}
  are equivalent.
\<close>
lemma tick_count_is_fun[code]:\<open>tick_count r c n = run_tick_count r c n\<close>
proof (induction n)
  case 0
    have \<open>tick_count r c 0 = card {i. i \<le> 0 \<and> hamlet ((Rep_run r) i c)}\<close>
      by (simp add: tick_count_def)
    also have \<open>... = card {i::nat. i = 0 \<and> hamlet ((Rep_run r) 0 c)}\<close>
      using le_zero_eq nat_sing_prop[of \<open>0\<close> \<open>\<lambda>i. hamlet ((Rep_run r) i c)\<close>] by simp
    also have \<open>... = (if hamlet ((Rep_run r) 0 c) then 1 else 0)\<close> by simp
    also have \<open>... = run_tick_count r c 0\<close> by simp
    finally show ?case .
next
  case (Suc k)
    show ?case
    proof (cases \<open>hamlet ((Rep_run r) (Suc k) c)\<close>)
      case True
        hence \<open>{i. i \<le> Suc k \<and> hamlet ((Rep_run r) i c)}
             = insert (Suc k) {i. i \<le> k \<and> hamlet ((Rep_run r) i c)}\<close> by auto
        hence \<open>tick_count r c (Suc k) = Suc (tick_count r c k)\<close>
          by (simp add: tick_count_def)
        with Suc.IH have \<open>tick_count r c (Suc k) = Suc (run_tick_count r c k)\<close> by simp
        thus ?thesis by (simp add: True)
    next
      case False
        hence \<open>{i. i \<le> Suc k \<and> hamlet ((Rep_run r) i c)}
             = {i. i \<le> k \<and> hamlet ((Rep_run r) i c)}\<close>
          using le_Suc_eq by auto
        hence \<open>tick_count r c (Suc k) = tick_count r c k\<close>
          by (simp add: tick_count_def)
        thus ?thesis using Suc.IH by (simp add: False)
    qed
qed

text \<open>
  To show that the set definition and the function definition 
  of @{const tick_count_strict} are equivalent, we first show that
  the \<^emph>\<open>strictness\<close> of @{const tick_count_strict} can be softened using @{const Suc}.
\<close> 
lemma tick_count_strict_suc:\<open>tick_count_strict r c (Suc n) = tick_count r c n\<close>
  unfolding tick_count_def tick_count_strict_def using less_Suc_eq_le by auto

lemma tick_count_strict_is_fun[code]:
  \<open>tick_count_strict r c n = run_tick_count_strictly r c n\<close>
proof (cases \<open>n = 0\<close>)
  case True
    hence \<open>tick_count_strict r c n = 0\<close> unfolding tick_count_strict_def by simp
    also have \<open>... = run_tick_count_strictly r c 0\<close>
      using run_tick_count_strictly.simps(1)[symmetric] .
    finally show ?thesis using True by simp
next
  case False
    from not0_implies_Suc[OF this] obtain m where *:\<open>n = Suc m\<close> by blast
    hence \<open>tick_count_strict r c n = tick_count r c m\<close>
      using tick_count_strict_suc by simp
    also have \<open>... = run_tick_count r c m\<close> using tick_count_is_fun[of \<open>r\<close> \<open>c\<close> \<open>m\<close>] .
    also have \<open>... = run_tick_count_strictly r c (Suc m)\<close>
      using run_tick_count_strictly.simps(2)[symmetric] .
    finally show ?thesis using * by simp
qed

text \<open>
  This leads to an alternate definition of the strict precedence relation.
\<close>
lemma strictly_precedes_alt_def1:
  \<open>{ \<rho>. \<forall>n::nat. (run_tick_count \<rho> K\<^sub>2 n) \<le> (run_tick_count_strictly \<rho> K\<^sub>1 n) }
 = { \<rho>. \<forall>n::nat. (run_tick_count_strictly \<rho> K\<^sub>2 (Suc n))
                  \<le> (run_tick_count_strictly \<rho> K\<^sub>1 n) }\<close>
by auto

text \<open>
  The strict precedence relation can even be defined using 
  only @{const \<open>run_tick_count\<close>}:
\<close>
lemma zero_gt_all:
  assumes \<open>P (0::nat)\<close>
      and \<open>\<And>n. n > 0 \<Longrightarrow> P n\<close>
    shows \<open>P n\<close>
  using assms neq0_conv by blast

lemma strictly_precedes_alt_def2:
  \<open>{ \<rho>. \<forall>n::nat. (run_tick_count \<rho> K\<^sub>2 n) \<le> (run_tick_count_strictly \<rho> K\<^sub>1 n) }
 = { \<rho>. (\<not>hamlet ((Rep_run \<rho>) 0 K\<^sub>2))
      \<and> (\<forall>n::nat. (run_tick_count \<rho> K\<^sub>2 (Suc n)) \<le> (run_tick_count \<rho> K\<^sub>1 n)) }\<close>
  (is \<open>?P = ?P'\<close>)
proof
  { fix r::\<open>'a run\<close>
    assume \<open>r \<in> ?P\<close>
    hence \<open>\<forall>n::nat. (run_tick_count r K\<^sub>2 n) \<le> (run_tick_count_strictly r K\<^sub>1 n)\<close>
      by simp
    hence 1:\<open>\<forall>n::nat. (tick_count r K\<^sub>2 n) \<le> (tick_count_strict r K\<^sub>1 n)\<close>
      using tick_count_is_fun[symmetric, of r] tick_count_strict_is_fun[symmetric, of r]
      by simp
    hence \<open>\<forall>n::nat. (tick_count_strict r K\<^sub>2 (Suc n)) \<le> (tick_count_strict r K\<^sub>1 n)\<close>
      using tick_count_strict_suc[symmetric, of \<open>r\<close> \<open>K\<^sub>2\<close>] by simp
    hence \<open>\<forall>n::nat. (tick_count_strict r K\<^sub>2 (Suc (Suc n))) \<le> (tick_count_strict r K\<^sub>1 (Suc n))\<close>
      by simp
    hence \<open>\<forall>n::nat. (tick_count r K\<^sub>2 (Suc n)) \<le> (tick_count r K\<^sub>1 n)\<close>
      using tick_count_strict_suc[symmetric, of \<open>r\<close>] by simp
    hence *:\<open>\<forall>n::nat. (run_tick_count r K\<^sub>2 (Suc n)) \<le> (run_tick_count r K\<^sub>1 n)\<close>
      by (simp add: tick_count_is_fun)
    from 1 have \<open>tick_count r K\<^sub>2 0 <= tick_count_strict r K\<^sub>1 0\<close> by simp
    moreover have \<open>tick_count_strict r K\<^sub>1 0 = 0\<close> unfolding tick_count_strict_def by simp
    ultimately have \<open>tick_count r K\<^sub>2 0 = 0\<close> by simp
    hence \<open>\<not>hamlet ((Rep_run r) 0 K\<^sub>2)\<close> unfolding tick_count_def by auto
    with * have \<open>r \<in> ?P'\<close> by simp
  } thus \<open>?P \<subseteq> ?P'\<close> ..
  { fix r::\<open>'a run\<close>
    assume h:\<open>r \<in> ?P'\<close>
    hence \<open>\<forall>n::nat. (run_tick_count r K\<^sub>2 (Suc n)) \<le> (run_tick_count r K\<^sub>1 n)\<close> by simp
    hence \<open>\<forall>n::nat. (tick_count r K\<^sub>2 (Suc n)) \<le> (tick_count r K\<^sub>1 n)\<close>
      by (simp add: tick_count_is_fun) 
    hence \<open>\<forall>n::nat. (tick_count r K\<^sub>2 (Suc n)) \<le> (tick_count_strict r K\<^sub>1 (Suc n))\<close>
      using tick_count_strict_suc[symmetric, of \<open>r\<close> \<open>K\<^sub>1\<close>] by simp
    hence *:\<open>\<forall>n. n > 0 \<longrightarrow> (tick_count r K\<^sub>2 n) \<le> (tick_count_strict r K\<^sub>1 n)\<close>
      using gr0_implies_Suc by blast
    have \<open>tick_count_strict r K\<^sub>1 0 = 0\<close> unfolding tick_count_strict_def by simp
    moreover from h have \<open>\<not>hamlet ((Rep_run r) 0 K\<^sub>2)\<close> by simp
    hence \<open>tick_count r K\<^sub>2 0 = 0\<close> unfolding tick_count_def by auto
    ultimately have \<open>tick_count r K\<^sub>2 0 \<le> tick_count_strict r K\<^sub>1 0\<close> by simp
    from zero_gt_all[of \<open>\<lambda>n. tick_count r K\<^sub>2 n \<le> tick_count_strict r K\<^sub>1 n\<close>, OF this ] *
      have \<open>\<forall>n. (tick_count r K\<^sub>2 n) \<le> (tick_count_strict r K\<^sub>1 n)\<close> by simp
    hence \<open>\<forall>n. (run_tick_count r K\<^sub>2 n) \<le> (run_tick_count_strictly r K\<^sub>1 n)\<close>
      by (simp add: tick_count_is_fun tick_count_strict_is_fun)
    hence \<open>r \<in> ?P\<close> ..
  } thus \<open>?P' \<subseteq> ?P\<close> ..
qed

text \<open>
  Some properties of @{const \<open>run_tick_count\<close>}, @{const \<open>tick_count\<close>} 
  and @{const \<open>Suc\<close>}:
\<close>
lemma run_tick_count_suc:
  \<open>run_tick_count r c (Suc n) = (if hamlet ((Rep_run r) (Suc n) c)
                                 then Suc (run_tick_count r c n)
                                 else run_tick_count r c n)\<close>
by simp

corollary tick_count_suc:
  \<open>tick_count r c (Suc n) = (if hamlet ((Rep_run r) (Suc n) c)
                             then Suc (tick_count r c n)
                             else tick_count r c n)\<close>
by (simp add: tick_count_is_fun)

text \<open>
  Some generic properties on the cardinal of sets of nat that we will need later.
\<close>
lemma card_suc:
  \<open>card {i. i \<le> (Suc n) \<and> P i} = card {i. i \<le> n \<and> P i} + card {i. i = (Suc n) \<and> P i}\<close>
proof -
  have \<open>{i. i \<le> n \<and> P i} \<inter> {i. i = (Suc n) \<and> P i} = {}\<close> by auto
  moreover have \<open>{i. i \<le> n \<and> P i} \<union> {i. i = (Suc n) \<and> P i}
               = {i. i \<le> (Suc n) \<and> P i}\<close> by auto
  moreover have \<open>finite {i. i \<le> n \<and> P i}\<close> by simp
  moreover have \<open>finite {i. i = (Suc n) \<and> P i}\<close> by simp
  ultimately show ?thesis
    using card_Un_disjoint[of \<open>{i. i \<le> n \<and> P i}\<close> \<open>{i. i = Suc n \<and> P i}\<close>] by simp
qed

lemma card_le_leq:
  assumes \<open>m < n\<close>
    shows \<open>card {i::nat. m < i \<and> i \<le> n \<and> P i}
         = card {i. m < i \<and> i < n \<and> P i} + card {i. i = n \<and> P i}\<close>
proof -
  have \<open>{i::nat. m < i \<and> i < n \<and> P i} \<inter> {i. i = n \<and> P i} = {}\<close> by auto
  moreover with assms have
    \<open>{i::nat. m < i \<and> i < n \<and> P i} \<union> {i. i = n \<and> P i} = {i. m < i \<and> i \<le> n \<and> P i}\<close>
  by auto
  moreover have \<open>finite {i. m < i \<and> i < n \<and> P i}\<close> by simp
  moreover have \<open>finite {i. i = n \<and> P i}\<close> by simp
  ultimately show ?thesis
    using card_Un_disjoint[of \<open>{i. m < i \<and> i < n \<and> P i}\<close> \<open>{i. i = n \<and> P i}\<close>] by simp
qed

lemma card_le_leq_0:
  \<open>card {i::nat. i \<le> n \<and> P i} = card {i. i < n \<and> P i} + card {i. i = n \<and> P i}\<close>
proof -
  have \<open>{i::nat. i < n \<and> P i} \<inter> {i. i = n \<and> P i} = {}\<close> by auto
  moreover have \<open>{i. i < n \<and> P i} \<union> {i. i = n \<and> P i} = {i. i \<le> n \<and> P i}\<close> by auto
  moreover have \<open>finite {i. i < n \<and> P i}\<close> by simp
  moreover have \<open>finite {i. i = n \<and> P i}\<close> by simp
  ultimately show ?thesis
    using card_Un_disjoint[of \<open>{i. i < n \<and> P i}\<close> \<open>{i. i = n \<and> P i}\<close>] by simp
qed

lemma card_mnm:
  assumes \<open>m < n\<close>
    shows \<open>card {i::nat. i < n \<and> P i}
         = card {i. i \<le> m \<and> P i} + card {i. m < i \<and> i < n \<and> P i}\<close>
proof -
  have 1:\<open>{i::nat. i \<le> m \<and> P i} \<inter> {i. m < i \<and> i < n \<and> P i} = {}\<close> by auto
  from assms have \<open>\<forall>i::nat. i < n = (i \<le> m) \<or> (m < i \<and> i < n)\<close>
    using less_trans by auto
  hence 2:
    \<open>{i::nat. i < n \<and> P i} = {i. i \<le> m \<and> P i} \<union> {i. m < i \<and> i < n \<and> P i}\<close> by blast
  have 3:\<open>finite {i. i \<le> m \<and> P i}\<close> by simp
  have 4:\<open>finite {i. m < i \<and> i < n \<and> P i}\<close> by simp
  from card_Un_disjoint[OF 3 4 1] 2 show ?thesis by simp
qed

lemma card_mnm':
  assumes \<open>m < n\<close>
    shows \<open>card {i::nat. i < n \<and> P i}
         = card {i. i < m \<and> P i} + card {i. m \<le> i \<and> i < n \<and> P i}\<close>
proof -
  have 1:\<open>{i::nat. i < m \<and> P i} \<inter> {i. m \<le> i \<and> i < n \<and> P i} = {}\<close> by auto
  from assms have \<open>\<forall>i::nat. i < n = (i < m) \<or> (m \<le> i \<and> i < n)\<close>
    using less_trans by auto
  hence 2:
    \<open>{i::nat. i < n \<and> P i} = {i. i < m \<and> P i} \<union> {i. m \<le> i \<and> i < n \<and> P i}\<close> by blast
  have 3:\<open>finite {i. i < m \<and> P i}\<close> by simp
  have 4:\<open>finite {i. m \<le> i \<and> i < n \<and> P i}\<close> by simp
  from card_Un_disjoint[OF 3 4 1] 2 show ?thesis by simp
qed

lemma nat_interval_union:
  assumes \<open>m \<le> n\<close>
    shows \<open>{i::nat. i \<le> n \<and> P i}
         = {i::nat. i \<le> m \<and> P i} \<union> {i::nat. m < i \<and> i \<le> n \<and> P i}\<close>
using assms le_cases nat_less_le by auto

lemma card_sing_prop:\<open>card {i. i = n \<and> P i} = (if P n then 1 else 0)\<close>
proof (cases \<open>P n\<close>)
  case True
    hence \<open>{i. i = n \<and> P i} = {n}\<close> by (simp add: Collect_conv_if)
    with \<open>P n\<close> show ?thesis by simp
next
  case False
    hence \<open>{i. i = n \<and> P i} = {}\<close> by (simp add: Collect_conv_if)
    with \<open>\<not>P n\<close> show ?thesis by simp
qed

lemma card_prop_mono:
  assumes \<open>m \<le> n\<close>
    shows \<open>card {i::nat. i \<le> m \<and> P i} \<le> card {i. i \<le> n \<and> P i}\<close>
proof -
  from assms have \<open>{i. i \<le> m \<and> P i} \<subseteq> {i. i \<le> n \<and> P i}\<close> by auto
  moreover have \<open>finite {i. i \<le> n \<and> P i}\<close> by simp
  ultimately show ?thesis by (simp add: card_mono)
qed


text \<open>
  In a dilated run, no tick occurs strictly between two successive instants that 
  are the images by @{term \<open>f\<close>} of instants of the original run.
\<close>
lemma no_tick_before_suc:
  assumes \<open>dilating f sub r\<close>
      and \<open>(f n) < k \<and> k < (f (Suc n))\<close>
    shows \<open>\<not>hamlet ((Rep_run r) k c)\<close>
proof -
  from assms(1) have smf:\<open>strict_mono f\<close> by (simp add: dilating_def dilating_fun_def)
  { fix k assume h:\<open>f n < k \<and> k < f (Suc n) \<and> hamlet ((Rep_run r) k c)\<close>
    hence \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k\<close> using assms(1) dilating_def dilating_fun_def by blast
    from this obtain k\<^sub>0 where \<open>f k\<^sub>0 = k\<close> by blast
    with h have \<open>f n < f k\<^sub>0 \<and> f k\<^sub>0 < f (Suc n)\<close> by simp
    hence False using smf not_less_eq strict_mono_less by blast
  } thus ?thesis using assms(2) by blast
qed

text \<open>
  From this, we show that the number of ticks on any clock at @{term \<open>f (Suc n)\<close>}
  depends only on the number of ticks on this clock at @{term \<open>f n\<close>} and whether
  this clock ticks at @{term \<open>f (Suc n)\<close>}.
  All the instants in between are stuttering instants.
\<close>
lemma tick_count_fsuc:
  assumes \<open>dilating f sub r\<close>
    shows \<open>tick_count r c (f (Suc n))
         = tick_count r c (f n) + card {k. k = f (Suc n) \<and> hamlet ((Rep_run r) k c)}\<close>
proof -
  have smf:\<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
  moreover have \<open>finite {k. k \<le> f n \<and> hamlet ((Rep_run r) k c)}\<close> by simp
  moreover have *:\<open>finite {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}\<close> by simp
  ultimately have \<open>{k. k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)} =
                        {k. k \<le> f n \<and> hamlet ((Rep_run r) k c)}
                      \<union> {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}\<close>
    by (simp add: nat_interval_union strict_mono_less_eq)
  moreover have \<open>{k. k \<le> f n \<and> hamlet ((Rep_run r) k c)}
                  \<inter> {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)} = {}\<close>
     by auto
  ultimately have \<open>card {k. k \<le> f (Suc n) \<and> hamlet (Rep_run r k c)} =
                      card {k. k \<le> f n \<and> hamlet (Rep_run r k c)}
                    + card {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet (Rep_run r k c)}\<close>
    by (simp add: * card_Un_disjoint)
  moreover from no_tick_before_suc[OF assms] have
    \<open>{k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)} =
            {k. k = f (Suc n) \<and> hamlet ((Rep_run r) k c)}\<close>
    using smf strict_mono_less by fastforce
  ultimately show ?thesis by (simp add: tick_count_def)
qed

corollary tick_count_f_suc:
  assumes \<open>dilating f sub r\<close>
    shows \<open>tick_count r c (f (Suc n))
         = tick_count r c (f n) + (if hamlet ((Rep_run r) (f (Suc n)) c) then 1 else 0)\<close>
using tick_count_fsuc[OF assms]
      card_sing_prop[of \<open>f (Suc n)\<close> \<open>\<lambda>k. hamlet ((Rep_run r) k c)\<close>] by simp

corollary tick_count_f_suc_suc:
  assumes \<open>dilating f sub r\<close>
    shows \<open>tick_count r c (f (Suc n)) = (if hamlet ((Rep_run r) (f (Suc n)) c)
                                         then Suc (tick_count r c (f n))
                                         else tick_count r c (f n))\<close>
using tick_count_f_suc[OF assms] by simp

lemma tick_count_f_suc_sub:
  assumes \<open>dilating f sub r\<close>
    shows \<open>tick_count r c (f (Suc n)) = (if hamlet ((Rep_run sub) (Suc n) c)
                                         then Suc (tick_count r c (f n))
                                         else tick_count r c (f n))\<close>
using tick_count_f_suc_suc[OF assms] assms by (simp add: dilating_def)

text \<open>
  The number of ticks does not progress during stuttering instants.
\<close>
lemma tick_count_latest:
  assumes \<open>dilating f sub r\<close>
      and \<open>f n\<^sub>p < n \<and> (\<forall>k. f n\<^sub>p < k \<and> k \<le> n \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close>
    shows \<open>tick_count r c n = tick_count r c (f n\<^sub>p)\<close>
proof -
  have union:\<open>{i. i \<le> n \<and> hamlet ((Rep_run r) i c)} =
          {i. i \<le> f n\<^sub>p \<and> hamlet ((Rep_run r) i c)}
        \<union> {i. f n\<^sub>p < i \<and> i \<le> n \<and> hamlet ((Rep_run r) i c)}\<close> using assms(2) by auto
  have partition: \<open>{i. i \<le> f n\<^sub>p \<and> hamlet ((Rep_run r) i c)}
        \<inter> {i. f n\<^sub>p < i \<and> i \<le> n \<and> hamlet ((Rep_run r) i c)} = {}\<close>
    by (simp add: disjoint_iff_not_equal)
  from assms have \<open>{i. f n\<^sub>p < i \<and> i \<le> n \<and> hamlet ((Rep_run r) i c)} = {}\<close>
    using no_tick_sub by fastforce
  with union and partition show ?thesis by (simp add: tick_count_def)
qed

text \<open>
  We finally show that the number of ticks on any clock is preserved by dilation.
\<close>
lemma tick_count_sub:
  assumes \<open>dilating f sub r\<close>
    shows \<open>tick_count sub c n = tick_count r c (f n)\<close>
proof -
  have \<open>tick_count sub c n = card {i. i \<le> n \<and> hamlet ((Rep_run sub) i c)}\<close>
    using tick_count_def[of \<open>sub\<close> \<open>c\<close> \<open>n\<close>] .
  also have \<open>... = card (image f {i. i \<le> n \<and> hamlet ((Rep_run sub) i c)})\<close>
    using assms dilating_def dilating_injects[OF assms] by (simp add: card_image)
  also have \<open>... = card {i. i \<le> f n \<and> hamlet ((Rep_run r) i c)}\<close>
    using dilated_prefix[OF assms, symmetric, of \<open>n\<close> \<open>c\<close>] by simp
  also have \<open>... = tick_count r c (f n)\<close>
    using tick_count_def[of \<open>r\<close> \<open>c\<close> \<open>f n\<close>] by simp
  finally show ?thesis .
qed

corollary run_tick_count_sub:
  assumes \<open>dilating f sub r\<close>
    shows \<open>run_tick_count sub c n = run_tick_count r c (f n)\<close>
proof -
  have \<open>run_tick_count sub c n = tick_count sub c n\<close>
    using tick_count_is_fun[of \<open>sub\<close> c n, symmetric] .
  also from tick_count_sub[OF assms] have \<open>... = tick_count r c (f n)\<close> .
  also have \<open>... = #\<^sub>\<le> r c (f n)\<close> using tick_count_is_fun[of r c \<open>f n\<close>] .
  finally show ?thesis .
qed

text \<open>
  The number of ticks occurring strictly before the first instant is null.
\<close>
lemma tick_count_strict_0:
  assumes \<open>dilating f sub r\<close>
    shows \<open>tick_count_strict r c (f 0) = 0\<close>
proof -
  from assms have \<open>f 0 = 0\<close> by (simp add: dilating_def dilating_fun_def)
  thus ?thesis unfolding tick_count_strict_def by simp
qed

text \<open>
  The number of ticks strictly before an instant does not progress
  during stuttering instants.
\<close>
lemma tick_count_strict_stable:
  assumes \<open>dilating f sub r\<close>
  assumes \<open>(f n) < k \<and> k < (f (Suc n))\<close>
  shows \<open>tick_count_strict r c k = tick_count_strict r c (f (Suc n))\<close>
proof -
  from assms(1) have smf:\<open>strict_mono f\<close> by (simp add: dilating_def dilating_fun_def)
  from assms(2) have \<open>f n < k\<close> by simp
  hence \<open>\<forall>i. k \<le> i \<longrightarrow> f n < i\<close> by simp
  with no_tick_before_suc[OF assms(1)] have
    *:\<open>\<forall>i. k \<le> i \<and> i < f (Suc n) \<longrightarrow> \<not>hamlet ((Rep_run r) i c)\<close> by blast
  from tick_count_strict_def have
    \<open>tick_count_strict r c (f (Suc n)) = card {i. i < f (Suc n) \<and> hamlet ((Rep_run r) i c)}\<close> .
  also have
    \<open>... = card {i. i < k \<and> hamlet ((Rep_run r) i c)}
         + card {i. k \<le> i \<and> i < f (Suc n) \<and> hamlet ((Rep_run r) i c)}\<close> 
    using card_mnm' assms(2) by simp
  also have \<open>... = card {i. i < k \<and> hamlet ((Rep_run r) i c)}\<close> using * by simp
  finally show ?thesis by (simp add: tick_count_strict_def)
qed

text \<open>
  Finally, the number of ticks strictly before an instant is preserved by dilation.
\<close>
lemma tick_count_strict_sub:
  assumes \<open>dilating f sub r\<close>
    shows \<open>tick_count_strict sub c n = tick_count_strict r c (f n)\<close>
proof -
  have \<open>tick_count_strict sub c n = card {i. i < n \<and> hamlet ((Rep_run sub) i c)}\<close>
    using tick_count_strict_def[of \<open>sub\<close> \<open>c\<close> \<open>n\<close>] .
  also have \<open>... = card (image f {i. i < n \<and> hamlet ((Rep_run sub) i c)})\<close>
    using assms dilating_def dilating_injects[OF assms] by (simp add: card_image)
  also have \<open>... = card {i. i < f n \<and> hamlet ((Rep_run r) i c)}\<close>
    using dilated_strict_prefix[OF assms, symmetric, of \<open>n\<close> \<open>c\<close>] by simp
  also have \<open>... = tick_count_strict r c (f n)\<close>
    using tick_count_strict_def[of \<open>r\<close> \<open>c\<close> \<open>f n\<close>] by simp
  finally show ?thesis .
qed

text \<open>
  The tick count on any clock can only increase.
\<close>

lemma mono_tick_count:
  \<open>mono (\<lambda> k. tick_count r c k)\<close>
proof
  { fix x y::nat
    assume \<open>x \<le> y\<close>
    from card_prop_mono[OF this] have \<open>tick_count r c x \<le> tick_count r c y\<close>
      unfolding tick_count_def by simp
  } thus \<open>\<And>x y. x \<le> y \<Longrightarrow> tick_count r c x \<le> tick_count r c y\<close> .
qed

text \<open>
  In a dilated run, for any stuttering instant, there is an instant which is the 
  image of an instant in the original run, and which is the latest one before
  the stuttering instant.
\<close>
lemma greatest_prev_image:
  assumes \<open>dilating f sub r\<close>
    shows \<open>(\<nexists>n\<^sub>0. f n\<^sub>0 = n) \<Longrightarrow> (\<exists>n\<^sub>p. f n\<^sub>p < n \<and> (\<forall>k. f n\<^sub>p < k \<and> k \<le> n \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k)))\<close>
proof (induction n)
  case 0
    with assms have \<open>f 0 = 0\<close> by (simp add: dilating_def dilating_fun_def)
    thus ?case using "0.prems" by blast
next
  case (Suc n)
  show ?case
  proof (cases \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>)
    case True
      from this obtain n\<^sub>0 where \<open>f n\<^sub>0 = n\<close> by blast
      hence \<open>f n\<^sub>0 < (Suc n) \<and> (\<forall>k. f n\<^sub>0 < k \<and> k \<le> (Suc n) \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close>
        using Suc.prems Suc_leI le_antisym by blast
      thus ?thesis by blast
  next
    case False
    from Suc.IH[OF this] obtain n\<^sub>p
      where \<open>f n\<^sub>p < n \<and> (\<forall>k. f n\<^sub>p < k \<and> k \<le> n \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close> by blast
    hence \<open>f n\<^sub>p < Suc n \<and> (\<forall>k. f n\<^sub>p < k \<and> k \<le> n \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close> by simp
    with Suc(2) have \<open>f n\<^sub>p < (Suc n) \<and> (\<forall>k. f n\<^sub>p < k \<and> k \<le> (Suc n) \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close>
      using le_Suc_eq by auto
    thus ?thesis by blast
  qed
qed

text \<open>
  If a strictly monotonous function on @{typ \<open>nat\<close>} increases only by one,
  its argument was increased only by one.
\<close>
lemma strict_mono_suc:
  assumes \<open>strict_mono f\<close>
      and \<open>f sn = Suc (f n)\<close>
    shows \<open>sn = Suc n\<close>
proof -
  from assms(2) have \<open>f sn > f n\<close> by simp
  with strict_mono_less[OF assms(1)] have \<open>sn > n\<close> by simp
  moreover have \<open>sn \<le> Suc n\<close>
  proof -
    { assume \<open>sn > Suc n\<close>
      from this obtain i where \<open>n < i \<and> i < sn\<close> by blast
      hence \<open>f n < f i \<and> f i < f sn\<close> using assms(1) by (simp add: strict_mono_def)
      with assms(2) have False by simp
    } thus ?thesis using not_less by blast
  qed
  ultimately show ?thesis by (simp add: Suc_leI)
qed

text \<open>
  Two successive non stuttering instants of a dilated run are the images
  of two successive instants of the original run.
\<close>
lemma next_non_stuttering:
  assumes \<open>dilating f sub r\<close>
      and \<open>f n\<^sub>p < n \<and> (\<forall>k. f n\<^sub>p < k \<and> k \<le> n \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close>
      and \<open>f sn\<^sub>0 = Suc n\<close>
    shows \<open>sn\<^sub>0 = Suc n\<^sub>p\<close>
proof -
  from assms(1) have smf:\<open>strict_mono f\<close> by (simp add: dilating_def dilating_fun_def)
  from assms(2) have *:\<open>\<forall>k. f n\<^sub>p < k \<and> k < Suc n \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k)\<close> by simp
  from assms(2) have \<open>f n\<^sub>p < n\<close> by simp
  with smf assms(3) have **:\<open>sn\<^sub>0 > n\<^sub>p\<close> using strict_mono_less by fastforce
  have \<open>Suc n \<le> f (Suc n\<^sub>p)\<close>
  proof -
    { assume h:\<open>Suc n > f (Suc n\<^sub>p)\<close>
      hence \<open>Suc n\<^sub>p < sn\<^sub>0\<close> using ** Suc_lessI assms(3) by fastforce
      hence \<open>\<exists>k. k > n\<^sub>p \<and> f k < Suc n\<close> using h by blast
      with * have False using smf strict_mono_less by blast
    } thus ?thesis using not_less by blast
  qed
  hence \<open>sn\<^sub>0 \<le> Suc n\<^sub>p\<close> using assms(3) smf using strict_mono_less_eq by fastforce
  with ** show ?thesis by simp
qed

text \<open>
  The order relation between tick counts on clocks is preserved by dilation.
\<close>
lemma dil_tick_count:
  assumes \<open>sub \<lless> r\<close>
      and \<open>\<forall>n. run_tick_count sub a n \<le> run_tick_count sub b n\<close>
    shows \<open>run_tick_count r a n \<le> run_tick_count r b n\<close>
proof -
  from assms(1) is_subrun_def obtain f where *:\<open>dilating f sub r\<close> by blast
  show ?thesis
  proof (induction n)
    case 0 
      from assms(2) have \<open>run_tick_count sub a 0 \<le> run_tick_count sub b 0\<close> ..
      with run_tick_count_sub[OF *, of _ 0] have
        \<open>run_tick_count r a (f 0) \<le> run_tick_count r b (f 0)\<close> by simp
      moreover from * have \<open>f 0 = 0\<close> by (simp add:dilating_def dilating_fun_def)
      ultimately show ?case by simp
  next
    case (Suc n') thus ?case 
    proof (cases \<open>\<exists>n\<^sub>0. f n\<^sub>0 = Suc n'\<close>)
      case True
        from this obtain n\<^sub>0 where fn0:\<open>f n\<^sub>0 = Suc n'\<close> by blast
        show ?thesis
        proof (cases \<open>hamlet ((Rep_run sub) n\<^sub>0 a)\<close>)
          case True
            have \<open>run_tick_count r a (f n\<^sub>0) \<le> run_tick_count r b (f n\<^sub>0)\<close>
              using assms(2) run_tick_count_sub[OF *] by simp
            thus ?thesis by (simp add: fn0)
        next
          case False
            hence \<open>\<not> hamlet ((Rep_run r) (Suc n') a)\<close>
              using * fn0 ticks_sub by fastforce
            thus ?thesis by (simp add: Suc.IH le_SucI)
        qed
    next
      case False
        thus ?thesis  using * Suc.IH no_tick_sub by fastforce
    qed
  qed
qed

text \<open>
  Time does not progress during stuttering instants.
\<close>
lemma stutter_no_time:
  assumes \<open>dilating f sub r\<close>
      and \<open>\<And>k. f n < k \<and> k \<le> m \<Longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k)\<close>
      and \<open>m > f n\<close>
    shows \<open>time ((Rep_run r) m c) = time ((Rep_run r) (f n) c)\<close>
proof -
  from assms have \<open>\<forall>k. k < m - (f n) \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = Suc ((f n) + k))\<close> by simp
  hence \<open>\<forall>k. k < m - (f n)
            \<longrightarrow> time ((Rep_run r) (Suc ((f n) + k)) c) = time ((Rep_run r) ((f n) + k) c)\<close>
    using assms(1) by (simp add: dilating_def dilating_fun_def)
  hence *:\<open>\<forall>k. k < m - (f n) \<longrightarrow> time ((Rep_run r) (Suc ((f n) + k)) c) = time ((Rep_run r) (f n) c)\<close>
    using bounded_suc_ind[of \<open>m - (f n)\<close> \<open>\<lambda>k. time (Rep_run r k c)\<close> \<open>f n\<close>] by blast
  from assms(3) obtain m\<^sub>0 where m0:\<open>Suc m\<^sub>0 = m - (f n)\<close> using Suc_diff_Suc by blast
  with * have \<open>time ((Rep_run r) (Suc ((f n) + m\<^sub>0)) c) = time ((Rep_run r) (f n) c)\<close> by auto
  moreover from m0 have \<open>Suc ((f n) + m\<^sub>0) = m\<close> by simp
  ultimately show ?thesis by simp
qed

lemma time_stuttering:
  assumes \<open>dilating f sub r\<close>
      and \<open>time ((Rep_run sub) n c) = \<tau>\<close>
      and \<open>\<And>k. f n < k \<and> k \<le> m \<Longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k)\<close>
      and \<open>m > f n\<close>
    shows \<open>time ((Rep_run r) m c) = \<tau>\<close>
proof -
  from assms(3) have \<open>time ((Rep_run r) m c) = time ((Rep_run r) (f n) c)\<close>
    using  stutter_no_time[OF assms(1,3,4)] by blast
  also from assms(1,2) have \<open>time ((Rep_run r) (f n) c) = \<tau>\<close> by (simp add: dilating_def)
  finally show ?thesis .
qed

text \<open>
  The first instant at which a given date is reached on a clock is preserved
  by dilation.
\<close>
lemma first_time_image:
  assumes \<open>dilating f sub r\<close>
    shows \<open>first_time sub c n t = first_time r c (f n) t\<close>
proof
  assume \<open>first_time sub c n t\<close>
  with before_first_time[OF this]
    have *:\<open>time ((Rep_run sub) n c) = t \<and> (\<forall>m < n. time((Rep_run sub) m c) < t)\<close>
      by (simp add: first_time_def)
  moreover have \<open>\<forall>n c. time (Rep_run sub n c) = time (Rep_run r (f n) c)\<close>
      using assms(1) by (simp add: dilating_def)
  ultimately have **:
    \<open>time ((Rep_run r) (f n) c) = t \<and> (\<forall>m < n. time((Rep_run r) (f m) c) < t)\<close>
    by simp
  have \<open>\<forall>m < f n. time ((Rep_run r) m c) < t\<close>
  proof -
  { fix m assume hyp:\<open>m < f n\<close>
    have \<open>time ((Rep_run r) m c) < t\<close>
    proof (cases \<open>\<exists>m\<^sub>0. f m\<^sub>0 = m\<close>)
      case True
        from this obtain m\<^sub>0 where mm0:\<open>m = f m\<^sub>0\<close> by blast
        with hyp have m0n:\<open>m\<^sub>0 < n\<close> using assms(1)
          by (simp add: dilating_def dilating_fun_def strict_mono_less)
        hence \<open>time ((Rep_run sub) m\<^sub>0 c) < t\<close> using * by blast
        thus ?thesis by (simp add: mm0 m0n **)
    next
      case False
        hence \<open>\<exists>m\<^sub>p. f m\<^sub>p < m \<and> (\<forall>k. f m\<^sub>p < k \<and> k \<le> m \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close>
          using greatest_prev_image[OF assms] by simp
        from this obtain m\<^sub>p where
          mp:\<open>f m\<^sub>p < m \<and> (\<forall>k. f m\<^sub>p < k \<and> k \<le> m \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close> by blast
        hence \<open>time ((Rep_run r) m c) = time ((Rep_run sub) m\<^sub>p c)\<close>
          using time_stuttering[OF assms] by blast
        also from hyp mp have \<open>f m\<^sub>p < f n\<close> by linarith
        hence \<open>m\<^sub>p < n\<close> using assms
          by (simp add:dilating_def dilating_fun_def strict_mono_less)
        hence \<open>time ((Rep_run sub) m\<^sub>p c) < t\<close> using * by simp
        finally show ?thesis by simp
      qed
    } thus ?thesis by simp
  qed
  with ** show \<open>first_time r c (f n) t\<close> by (simp add: alt_first_time_def)
next
  assume \<open>first_time r c (f n) t\<close>
  hence *:\<open>time ((Rep_run r) (f n) c) = t \<and> (\<forall>k < f n. time ((Rep_run r) k c) < t)\<close>
    by (simp add: first_time_def before_first_time)
  hence \<open>time ((Rep_run sub) n c) = t\<close> using assms dilating_def by blast
  moreover from * have \<open>(\<forall>k < n. time ((Rep_run sub) k c) < t)\<close>
    using assms dilating_def dilating_fun_def strict_monoD by fastforce
  ultimately show \<open>first_time sub c n t\<close> by (simp add: alt_first_time_def)
qed

text \<open>
  The first instant of a dilated run is necessarily the image of the first instant
  of the original run.
\<close>
lemma first_dilated_instant:
  assumes \<open>strict_mono f\<close>
      and \<open>f (0::nat) = (0::nat)\<close>
    shows \<open>Max {i. f i \<le> 0} = 0\<close>
proof -
  from assms(2) have \<open>\<forall>n > 0. f n > 0\<close> using strict_monoD[OF assms(1)] by force
  hence \<open>\<forall>n \<noteq> 0. \<not>(f n \<le> 0)\<close> by simp
  with assms(2) have \<open>{i. f i \<le> 0} = {0}\<close> by blast
  thus ?thesis by simp
qed

text \<open>
  For any instant @{term \<open>n\<close>} of a dilated run, let @{term \<open>n\<^sub>0\<close>} be the last 
  instant before @{term \<open>n\<close>} that is the image of an original instant. All instants
  strictly after @{term \<open>n\<^sub>0\<close>} and before @{term \<open>n\<close>} are stuttering instants.
\<close>
lemma not_image_stut:
  assumes \<open>dilating f sub r\<close>
      and \<open>n\<^sub>0 = Max {i. f i \<le> n}\<close>
      and \<open>f n\<^sub>0 < k \<and> k \<le> n\<close>
    shows \<open>\<nexists>k\<^sub>0. f k\<^sub>0 = k\<close>
proof -
  from assms(1) have smf:\<open>strict_mono f\<close>
                and fxge:\<open>\<forall>x. f x \<ge> x\<close>
    by (auto simp add: dilating_def dilating_fun_def)
  have finite_prefix:\<open>finite {i. f i \<le> n}\<close> by (simp add: finite_less_ub fxge)
  from assms(1) have \<open>f 0 \<le> n\<close> by (simp add: dilating_def dilating_fun_def)
  hence \<open>{i. f i \<le> n} \<noteq> {}\<close> by blast
  from assms(3) fxge have \<open>f n\<^sub>0 < n\<close> by linarith
  from assms(2) have \<open>\<forall>x > n\<^sub>0. f x > n\<close> using Max.coboundedI[OF finite_prefix]
    using not_le by auto
  with assms(3) strict_mono_less[OF smf] show ?thesis by auto
qed

text \<open>
  For any dilating function @{term \<open>f\<close>}, @{term \<open>dil_inverse f\<close>} is a 
  contracting function.
\<close>
lemma contracting_inverse:
  assumes \<open>dilating f sub r\<close>
    shows \<open>contracting (dil_inverse f) r sub f\<close>
proof -
  from assms have smf:\<open>strict_mono f\<close>
    and no_img_tick:\<open>\<forall>k. (\<nexists>k\<^sub>0. f k\<^sub>0 = k) \<longrightarrow> (\<forall>c. \<not>(hamlet ((Rep_run r) k c)))\<close>
    and no_img_time:\<open>\<And>n. (\<nexists>n\<^sub>0. f n\<^sub>0 = (Suc n))
                          \<longrightarrow> (\<forall>c. time ((Rep_run r) (Suc n) c) = time ((Rep_run r) n c))\<close>
    and fxge:\<open>\<forall>x. f x \<ge> x\<close> and f0n:\<open>\<And>n. f 0 \<le> n\<close> and f0:\<open>f 0 = 0\<close>
    by (auto simp add: dilating_def dilating_fun_def)
  have finite_prefix:\<open>\<And>n. finite {i. f i \<le> n}\<close> by (auto simp add: finite_less_ub fxge)
  have prefix_not_empty:\<open>\<And>n. {i. f i \<le> n} \<noteq> {}\<close> using f0n by blast                

  have 1:\<open>mono (dil_inverse f)\<close>
  proof -
  { fix x::\<open>nat\<close> and y::\<open>nat\<close> assume hyp:\<open>x \<le> y\<close>
    hence inc:\<open>{i. f i \<le> x} \<subseteq> {i. f i \<le> y}\<close>
      by (simp add: hyp Collect_mono le_trans)
    from Max_mono[OF inc prefix_not_empty finite_prefix]
      have \<open>(dil_inverse f) x \<le> (dil_inverse f) y\<close> unfolding dil_inverse_def .
  } thus ?thesis unfolding mono_def by simp
  qed

  from first_dilated_instant[OF smf f0] have 2:\<open>(dil_inverse f) 0 = 0\<close>
    unfolding dil_inverse_def .

  from fxge have \<open>\<forall>n i. f i \<le> n \<longrightarrow> i \<le> n\<close> using le_trans by blast
  hence 3:\<open>\<forall>n. (dil_inverse f) n \<le> n\<close> using Max_in[OF finite_prefix prefix_not_empty] 
    unfolding dil_inverse_def by blast

  from 1 2 3 have *:\<open>contracting_fun (dil_inverse f)\<close> by (simp add: contracting_fun_def)
  
  have \<open>\<forall>n. finite {i. f i \<le> n}\<close> by (simp add: finite_prefix)
  moreover have \<open>\<forall>n. {i. f i \<le> n} \<noteq> {}\<close> using prefix_not_empty by blast
  ultimately have 4:\<open>\<forall>n. f ((dil_inverse f) n) \<le> n\<close> 
    unfolding dil_inverse_def
    using assms(1) dilating_def dilating_fun_def Max_in by blast

  have 5:\<open>\<forall>n c k. f ((dil_inverse f) n) < k \<and> k \<le> n
                              \<longrightarrow> \<not> hamlet ((Rep_run r) k c)\<close>
    using not_image_stut[OF assms] no_img_tick unfolding dil_inverse_def by blast

  have 6:\<open>(\<forall>n c k. f ((dil_inverse f) n) \<le> k \<and> k \<le> n
                      \<longrightarrow> time ((Rep_run r) k c) = time ((Rep_run sub) ((dil_inverse f) n) c))\<close>
  proof -
    { fix n c k assume h:\<open>f ((dil_inverse f) n) \<le> k \<and> k \<le> n\<close>
      let ?\<tau> = \<open>time (Rep_run sub ((dil_inverse f) n) c)\<close>
      have tau:\<open>time (Rep_run sub ((dil_inverse f) n) c) = ?\<tau>\<close> ..
      have gn:\<open>(dil_inverse f) n = Max {i. f i \<le> n}\<close> unfolding dil_inverse_def ..
      from time_stuttering[OF assms tau, of k] not_image_stut[OF assms gn]
      have \<open>time ((Rep_run r) k c) = time ((Rep_run sub) ((dil_inverse f) n) c)\<close>
      proof (cases \<open>f ((dil_inverse f) n) = k\<close>)
        case True
          moreover have \<open>\<forall>n c. time (Rep_run sub n c) = time (Rep_run r (f n) c)\<close>
            using assms by (simp add: dilating_def)
          ultimately show ?thesis by simp
      next
        case False
          with h have \<open>f (Max {i. f i \<le> n}) < k \<and> k \<le> n\<close> by (simp add: dil_inverse_def)
          with time_stuttering[OF assms tau, of k] not_image_stut[OF assms gn]
            show ?thesis unfolding dil_inverse_def by auto
      qed
    } thus ?thesis by simp
  qed

  from * 4 5 6 show ?thesis unfolding contracting_def by simp
qed

text \<open>
  The only possible contracting function toward a dense run (a run with no empty 
  instants) is the inverse of the dilating function as defined by 
  @{term \<open>dil_inverse\<close>}.
\<close>
lemma dense_run_dil_inverse_only:
  assumes \<open>dilating f sub r\<close>
      and \<open>contracting g r sub f\<close>
      and \<open>dense_run sub\<close>
    shows \<open>g = (dil_inverse f)\<close>
proof
  from assms(1) have *:\<open>\<And>n. finite {i. f i \<le> n}\<close>
    using finite_less_ub by (simp add:  dilating_def dilating_fun_def)
  from assms(1) have \<open>f 0 = 0\<close> by (simp add:  dilating_def dilating_fun_def)
  hence \<open>\<And>n. 0 \<in> {i. f i \<le> n}\<close> by simp
  hence **:\<open>\<And>n. {i. f i \<le> n} \<noteq> {}\<close> by blast
  { fix n assume h:\<open>g n < (dil_inverse f) n\<close>
    hence \<open>\<exists>k > g n. f k \<le> n\<close> unfolding dil_inverse_def using Max_in[OF * **] by blast
    from this obtain k where kprop:\<open>g n < k \<and> f k \<le> n\<close> by blast
    with assms(3) dense_run_def obtain c where \<open>hamlet ((Rep_run sub) k c)\<close> by blast
    hence \<open>hamlet ((Rep_run r) (f k) c)\<close> using ticks_sub[OF assms(1)] by blast
    moreover from kprop have \<open>f (g n) < f k \<and> f k \<le> n\<close> using assms(1)
      by (simp add: dilating_def dilating_fun_def strict_monoD)
    ultimately have False using assms(2) unfolding contracting_def by blast
  } hence 1:\<open>\<And>n. \<not>(g n < (dil_inverse f) n)\<close> by blast
  { fix n assume h:\<open>g n > (dil_inverse f) n\<close>
    have \<open>\<exists>k \<le> g n. f k > n\<close> 
    proof -
      { assume \<open>\<forall>k \<le> g n. f k \<le> n\<close>
        with h have False unfolding dil_inverse_def
        using Max_gr_iff[OF * **] by blast
      }
      thus ?thesis using not_less by blast
    qed
    from this obtain k where \<open>k \<le> g n \<and> f k > n\<close> by blast
    hence \<open>f (g n) \<ge> f k \<and> f k > n\<close> using assms(1)
      by (simp add: dilating_def dilating_fun_def strict_mono_less_eq)
    hence \<open>f (g n) > n\<close> by simp
    with assms(2) have False unfolding contracting_def by (simp add: leD)
  } hence 2:\<open>\<And>n. \<not>(g n > (dil_inverse f) n)\<close> by blast
  from 1 2 show \<open>\<And>n. g n = (dil_inverse f) n\<close> by (simp add: not_less_iff_gr_or_eq)
qed

end
