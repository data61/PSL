(*  Title:      Filtration.thy
    Author:     Mnacho Echenim, Univ. Grenoble Alpes
*)

section \<open>Filtrations\<close>

text \<open>This theory introduces basic notions about filtrations, which permit to define adaptable processes
and predictable processes in the case where the filtration is indexed by natural numbers.\<close>

theory Filtration imports "HOL-Probability.Probability"
begin
subsection \<open>Basic definitions\<close>
class linorder_bot = linorder + bot
instantiation nat::linorder_bot
begin
instance proof qed
end


definition filtration :: "'a measure \<Rightarrow> ('i::linorder_bot \<Rightarrow> 'a measure) \<Rightarrow> bool" where
  "filtration M F \<longleftrightarrow>
    (\<forall>t. subalgebra M (F t))  \<and>
    (\<forall> s t. s \<le> t \<longrightarrow> subalgebra (F t) (F s))"

lemma filtrationI:
  assumes "\<forall>t. subalgebra M (F t)"
  and "\<forall>s t. s \<le> t \<longrightarrow> subalgebra (F t) (F s)"
shows "filtration M F" unfolding filtration_def using assms by simp

lemma filtrationE1:
  assumes "filtration M F"
  shows "subalgebra M (F t)" using assms unfolding filtration_def by simp

lemma filtrationE2:
  assumes "filtration M F"
  shows "s\<le> t \<Longrightarrow> subalgebra (F t) (F s)" using assms unfolding filtration_def by simp

locale filtrated_prob_space = prob_space +
  fixes F
  assumes filtration: "filtration M F"

lemma (in filtrated_prob_space) filtration_space:
  assumes "s \<le> t"
  shows "space (F s) = space (F t)" by (metis filtration filtration_def subalgebra_def)

lemma (in filtrated_prob_space) filtration_measurable:
  assumes "f\<in> measurable (F t) N"
shows "f\<in> measurable M N" unfolding measurable_def
proof
  show "f \<in> space M \<rightarrow> space N \<and> (\<forall>y\<in>sets N. f -` y \<inter> space M \<in> sets M)"
  proof (intro conjI ballI)
    have "space (F t) = space M" using assms filtration unfolding filtration_def subalgebra_def by auto
    thus "f\<in> space M \<rightarrow> space N" using assms unfolding measurable_def by simp
    fix y
    assume "y\<in> sets N"
    hence "f -`y\<inter> space M \<in> sets (F t)" using assms unfolding measurable_def
      using \<open>space (F t) = space M\<close> by auto
    thus "f -`y\<inter> space M \<in> sets M"  using assms filtration unfolding filtration_def subalgebra_def by auto
  qed
qed


lemma (in filtrated_prob_space) increasing_measurable_info:
  assumes "f\<in> measurable (F s) N"
  and "s \<le> t"
  shows "f\<in> measurable (F t) N"
proof (rule measurableI)
  have inc: "sets (F s) \<subseteq> sets (F t)"
    using assms(2) filtration by (simp add: filtration_def subalgebra_def)
  have sp: "space (F s) = space (F t)" by (metis filtration filtration_def subalgebra_def)
  thus "\<And>x. x \<in> space (F t) \<Longrightarrow> f x \<in> space N" using assms by (simp add: measurable_space)
  show "\<And>A. A \<in> sets N \<Longrightarrow> f -` A \<inter> space (F t) \<in> sets (F t)"
  proof -
    fix A
    assume "A\<in> sets N"
    hence "f -` A \<inter> space (F s) \<in> sets (F s)" using assms using measurable_sets by blast
    hence "f -` A \<inter> space (F s) \<in> sets (F t)" using subsetD[of "F s" "F t"] inc by blast
    thus "f -` A \<inter> space (F t) \<in> sets (F t)" using sp by simp
  qed
qed



definition disc_filtr :: "'a measure \<Rightarrow> (nat \<Rightarrow> 'a measure) \<Rightarrow> bool" where
  "disc_filtr M F \<longleftrightarrow>
    (\<forall>n. subalgebra M (F n))  \<and>
    (\<forall> n m. n \<le> m \<longrightarrow> subalgebra (F m) (F n))"


locale disc_filtr_prob_space = prob_space +
  fixes F
  assumes discrete_filtration: "disc_filtr M F"

lemma (in disc_filtr_prob_space) subalgebra_filtration:
  assumes "subalgebra N M"
  and "filtration M F"
shows "filtration N F"
proof (rule filtrationI)
  show "\<forall>s t. s \<le> t \<longrightarrow> subalgebra (F t) (F s)" using assms unfolding filtration_def by simp
  show "\<forall>t. subalgebra N (F t)"
  proof
    fix t
    have "subalgebra M (F t)" using assms unfolding filtration_def by auto
    thus "subalgebra N (F t)" using assms by (metis subalgebra_def subsetCE subsetI)
  qed
qed



sublocale disc_filtr_prob_space \<subseteq>  filtrated_prob_space
proof unfold_locales
  show "filtration M F"
    using  discrete_filtration by (simp add: filtration_def disc_filtr_def)
qed



subsection \<open>Stochastic processes\<close>

text  \<open>Stochastic processes are collections of measurable functions. Those of a particular interest when
there is a filtration are the adapted stochastic processes.\<close>

definition stoch_procs where
  "stoch_procs M N = {X. \<forall>t. (X t) \<in> measurable M N}"

subsubsection \<open>Adapted stochastic processes\<close>

definition adapt_stoch_proc where
  "(adapt_stoch_proc F X N) \<longleftrightarrow> (\<forall>t. (X t) \<in> measurable (F t) N)"


abbreviation "borel_adapt_stoch_proc F X \<equiv> adapt_stoch_proc F X borel"

lemma (in filtrated_prob_space) adapted_is_dsp:
  assumes "adapt_stoch_proc F X N"
  shows "X \<in> stoch_procs M N"
  unfolding  stoch_procs_def
  by (intro CollectI, (meson adapt_stoch_proc_def assms filtration filtration_def measurable_from_subalg))


lemma (in filtrated_prob_space) adapt_stoch_proc_borel_measurable:
  assumes "adapt_stoch_proc F X N"
  shows "\<forall>n. (X n) \<in> measurable M N"
proof
  fix n
  have "X n \<in> measurable (F n) N" using assms unfolding  adapt_stoch_proc_def by simp
  moreover have "subalgebra M (F n)" using filtration unfolding filtration_def by simp
  ultimately show "X n \<in> measurable M N" by (simp add:measurable_from_subalg)
qed

lemma (in filtrated_prob_space) borel_adapt_stoch_proc_borel_measurable:
  assumes "borel_adapt_stoch_proc F X"
  shows "\<forall>n. (X n) \<in> borel_measurable M"
proof
  fix n
  have "X n \<in> borel_measurable (F n)" using assms unfolding  adapt_stoch_proc_def by simp
  moreover have "subalgebra M (F n)" using filtration unfolding filtration_def by simp
  ultimately show "X n \<in> borel_measurable M" by (simp add:measurable_from_subalg)
qed


lemma (in filtrated_prob_space) constant_process_borel_adapted:
  shows "borel_adapt_stoch_proc F (\<lambda> n w. c)"
unfolding  adapt_stoch_proc_def
proof
  fix t
  show "(\<lambda>w. c) \<in> borel_measurable (F t)" using borel_measurable_const by blast
qed


lemma (in filtrated_prob_space) borel_adapt_stoch_proc_add:
  fixes X::"'b \<Rightarrow> 'a \<Rightarrow> ('c::{second_countable_topology, topological_monoid_add})"
  assumes "borel_adapt_stoch_proc F X"
  and "borel_adapt_stoch_proc F Y"
shows "borel_adapt_stoch_proc F (\<lambda>t w. X t w + Y t w)" unfolding adapt_stoch_proc_def
proof
  fix t
  have "X t \<in> borel_measurable (F t)" using assms unfolding adapt_stoch_proc_def by simp
  moreover have "Y t \<in> borel_measurable (F t)" using assms unfolding adapt_stoch_proc_def by simp
  ultimately show "(\<lambda>w. X t w + Y t w) \<in> borel_measurable (F t)" by simp
qed


lemma (in filtrated_prob_space) borel_adapt_stoch_proc_sum:
  fixes A::"'d \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> ('c::{second_countable_topology, topological_comm_monoid_add})"
  assumes "\<And>i. i\<in> S \<Longrightarrow> borel_adapt_stoch_proc F (A i)"
shows "borel_adapt_stoch_proc F (\<lambda> t w. (\<Sum> i\<in> S. A i t w))" unfolding adapt_stoch_proc_def
proof
  fix t
  have "\<And>i. i\<in> S\<Longrightarrow> A i t \<in> borel_measurable (F t)" using assms unfolding adapt_stoch_proc_def by simp
  thus "(\<lambda> w. (\<Sum> i\<in> S. A i t w)) \<in> borel_measurable (F t)" by (simp add:borel_measurable_sum)
qed

lemma (in filtrated_prob_space) borel_adapt_stoch_proc_times:
  fixes X::"'b \<Rightarrow> 'a \<Rightarrow> ('c::{second_countable_topology, real_normed_algebra})"
  assumes "borel_adapt_stoch_proc F X"
  and "borel_adapt_stoch_proc F Y"
shows "borel_adapt_stoch_proc F (\<lambda>t w. X t w * Y t w)" unfolding adapt_stoch_proc_def
proof
  fix t
  have "X t \<in> borel_measurable (F t)" using assms unfolding adapt_stoch_proc_def by simp
  moreover have "Y t \<in> borel_measurable (F t)" using assms unfolding adapt_stoch_proc_def by simp
  ultimately show "(\<lambda>w. X t w * Y t w) \<in> borel_measurable (F t)" by simp
qed

lemma (in filtrated_prob_space) borel_adapt_stoch_proc_prod:
  fixes A::"'d \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> ('c::{second_countable_topology, real_normed_field})"
  assumes "\<And>i. i\<in> S \<Longrightarrow> borel_adapt_stoch_proc F (A i)"
shows "borel_adapt_stoch_proc F (\<lambda> t w. (\<Prod> i\<in> S. A i t w))" unfolding adapt_stoch_proc_def
proof
  fix t
  have "\<And>i. i\<in> S\<Longrightarrow> A i t \<in> borel_measurable (F t)" using assms unfolding adapt_stoch_proc_def by simp
  thus "(\<lambda> w. (\<Prod> i\<in> S. A i t w)) \<in> borel_measurable (F t)" by simp
qed


subsubsection \<open>Predictable stochastic processes\<close>

definition predict_stoch_proc where
  "(predict_stoch_proc F X N) \<longleftrightarrow> (X 0 \<in> measurable (F 0) N \<and> (\<forall>n. (X (Suc n)) \<in> measurable (F n) N))"


abbreviation  "borel_predict_stoch_proc F X \<equiv> predict_stoch_proc F X borel"

lemma (in disc_filtr_prob_space) predict_imp_adapt:
  assumes "predict_stoch_proc F X N"
  shows "adapt_stoch_proc F X N" unfolding adapt_stoch_proc_def
proof
  fix n
  show "X n \<in> measurable (F n) N"
  proof (cases "n = 0")
    case True
    thus ?thesis using assms unfolding predict_stoch_proc_def by auto
  next
    case False
    thus ?thesis using assms unfolding predict_stoch_proc_def
      by (metis Suc_n_not_le_n increasing_measurable_info nat_le_linear not0_implies_Suc)
  qed
qed


lemma (in disc_filtr_prob_space) predictable_is_dsp:
  assumes "predict_stoch_proc F X N"
  shows "X \<in> stoch_procs M N"
unfolding  stoch_procs_def
proof
  show "\<forall>n. random_variable N (X n)"
  proof
    fix n
    show "random_variable N (X n)"
    proof (cases "n=0")
      case True
      thus ?thesis using assms unfolding predict_stoch_proc_def
        using filtration filtration_def measurable_from_subalg by blast
    next
      case False
      thus ?thesis using assms unfolding predict_stoch_proc_def
        by (metis filtration filtration_def measurable_from_subalg not0_implies_Suc)
    qed
  qed
qed



lemma (in disc_filtr_prob_space) borel_predict_stoch_proc_borel_measurable:
  assumes "borel_predict_stoch_proc F X"
  shows "\<forall>n. (X n) \<in> borel_measurable M" using assms predictable_is_dsp unfolding stoch_procs_def by auto



lemma (in disc_filtr_prob_space) constant_process_borel_predictable:
  shows "borel_predict_stoch_proc F (\<lambda> n w. c)"
unfolding  predict_stoch_proc_def
proof
  show "(\<lambda>w. c) \<in> borel_measurable (F 0)" using borel_measurable_const by blast
next
  show "\<forall>n. (\<lambda>w. c) \<in> borel_measurable (F n)" using borel_measurable_const by blast
qed

lemma (in disc_filtr_prob_space) borel_predict_stoch_proc_add:
  fixes X::"nat \<Rightarrow> 'a \<Rightarrow> ('c::{second_countable_topology, topological_monoid_add})"
  assumes "borel_predict_stoch_proc F X"
  and "borel_predict_stoch_proc F Y"
shows "borel_predict_stoch_proc F (\<lambda>t w. X t w + Y t w)" unfolding predict_stoch_proc_def
proof
  show "(\<lambda>w. X 0 w + Y 0 w) \<in> borel_measurable (F 0)"
    using assms(1) assms(2) borel_measurable_add predict_stoch_proc_def by blast
next
  show "\<forall>n. (\<lambda>w. X (Suc n) w + Y (Suc n) w) \<in> borel_measurable (F n)"
  proof
    fix n
    have "X (Suc n) \<in> borel_measurable (F n)" using assms unfolding predict_stoch_proc_def by simp
    moreover have "Y (Suc n) \<in> borel_measurable (F n)" using assms unfolding predict_stoch_proc_def by simp
    ultimately show "(\<lambda>w. X (Suc n) w + Y (Suc n) w) \<in> borel_measurable (F n)" by simp
  qed
qed



lemma (in disc_filtr_prob_space) borel_predict_stoch_proc_sum:
  fixes A::"'d \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('c::{second_countable_topology, topological_comm_monoid_add})"
  assumes "\<And>i. i\<in> S \<Longrightarrow> borel_predict_stoch_proc F (A i)"
shows "borel_predict_stoch_proc F (\<lambda> t w. (\<Sum> i\<in> S. A i t w))" unfolding predict_stoch_proc_def
proof
  show "(\<lambda>w. \<Sum>i\<in>S. A i 0 w) \<in> borel_measurable (F 0)"
  proof
    have "\<And>i. i\<in> S\<Longrightarrow> A i 0 \<in> borel_measurable (F 0)" using assms unfolding predict_stoch_proc_def by simp
    thus "(\<lambda> w. (\<Sum> i\<in> S. A i 0 w)) \<in> borel_measurable (F 0)" by (simp add:borel_measurable_sum)
  qed simp
next
  show "\<forall>n. (\<lambda>w. \<Sum>i\<in>S. A i (Suc n) w) \<in> borel_measurable (F n)"
  proof
    fix n
    have "\<And>i. i\<in> S\<Longrightarrow> A i (Suc n) \<in> borel_measurable (F n)" using assms unfolding predict_stoch_proc_def by simp
    thus "(\<lambda> w. (\<Sum> i\<in> S. A i (Suc n) w)) \<in> borel_measurable (F n)" by (simp add:borel_measurable_sum)
  qed
qed


lemma (in disc_filtr_prob_space) borel_predict_stoch_proc_times:
  fixes X::"nat \<Rightarrow> 'a \<Rightarrow> ('c::{second_countable_topology, real_normed_algebra})"
  assumes "borel_predict_stoch_proc F X"
  and "borel_predict_stoch_proc F Y"
shows "borel_predict_stoch_proc F (\<lambda>t w. X t w * Y t w)" unfolding predict_stoch_proc_def
proof
  show "(\<lambda>w. X 0 w * Y 0 w) \<in> borel_measurable (F 0)"
  proof -
    have "X 0 \<in> borel_measurable (F 0)" using assms unfolding predict_stoch_proc_def by simp
    moreover have "Y 0 \<in> borel_measurable (F 0)" using assms unfolding predict_stoch_proc_def by simp
    ultimately show "(\<lambda>w. X 0 w * Y 0 w) \<in> borel_measurable (F 0)" by simp
  qed
next
  show "\<forall>n. (\<lambda>w. X (Suc n) w * Y (Suc n) w) \<in> borel_measurable (F n)"
  proof
    fix n
    have "X (Suc n) \<in> borel_measurable (F n)" using assms unfolding predict_stoch_proc_def by simp
    moreover have "Y (Suc n) \<in> borel_measurable (F n)" using assms unfolding predict_stoch_proc_def by simp
    ultimately show "(\<lambda>w. X (Suc n) w * Y (Suc n) w) \<in> borel_measurable (F n)" by simp
  qed
qed

lemma (in disc_filtr_prob_space) borel_predict_stoch_proc_prod:
  fixes A::"'d \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('c::{second_countable_topology, real_normed_field})"
  assumes "\<And>i. i\<in> S \<Longrightarrow> borel_predict_stoch_proc F (A i)"
shows "borel_predict_stoch_proc F (\<lambda> t w. (\<Prod> i\<in> S. A i t w))" unfolding predict_stoch_proc_def
proof
  show "(\<lambda>w. \<Prod>i\<in>S. A i 0 w) \<in> borel_measurable (F 0)"
  proof -
    have "\<And>i. i\<in> S\<Longrightarrow> A i 0 \<in> borel_measurable (F 0)" using assms unfolding predict_stoch_proc_def by simp
    thus "(\<lambda> w. (\<Prod> i\<in> S. A i 0 w)) \<in> borel_measurable (F 0)" by simp
  qed
next
  show "\<forall>n. (\<lambda>w. \<Prod>i\<in>S. A i (Suc n) w) \<in> borel_measurable (F n)"
  proof
    fix n
    have "\<And>i. i\<in> S\<Longrightarrow> A i (Suc n) \<in> borel_measurable (F n)" using assms unfolding predict_stoch_proc_def by simp
    thus "(\<lambda> w. (\<Prod> i\<in> S. A i (Suc n) w)) \<in> borel_measurable (F n)" by simp
  qed
qed


definition (in prob_space) constant_image where
  "constant_image f = (if \<exists> c::'b::{t2_space}. \<forall>x\<in> space M. f x = c then
    SOME c. \<forall>x \<in> space M. f x = c else undefined)"

lemma (in prob_space) constant_imageI:
  assumes "\<exists>c::'b::{t2_space}. \<forall>x\<in> space M. f x = c"
  shows "\<forall>x\<in> space M. f x = (constant_image f)"
proof
  fix x
  assume "x\<in> space M"
  let ?c = "SOME c. \<forall>x\<in> space M. f x = c"
  have "f x = ?c" using \<open>x\<in> space M\<close> someI_ex[of "\<lambda>c. \<forall>x\<in> space M. f x = c"] assms by blast
  thus "f x = (constant_image f)" by (simp add: assms prob_space.constant_image_def prob_space_axioms)
qed

lemma (in prob_space) constant_image_pos:
  assumes "\<forall>x\<in> space M. (0::real) < f x"
  and "\<exists>c::real. \<forall>x\<in> space M. f x = c"
shows "0 < (constant_image f)"
proof -
  {
    fix x
    assume "x\<in> space M"
    hence "0 < f x" using assms by simp
    also have "... = constant_image f" using assms constant_imageI \<open>x\<in> space M\<close> by auto
    finally have ?thesis .
  }
  thus ?thesis using subprob_not_empty by auto
qed

definition open_except where
"open_except x y = (if x = y then {} else SOME A. open A \<and> x\<in> A \<and> y\<notin> A)"


lemma open_exceptI:
  assumes "(x::'b::{t1_space}) \<noteq> y"
  shows "open (open_except x y)" and "x\<in> open_except x y" and  "y\<notin> open_except x y"
proof-
  have ex:"\<exists>U. open U \<and> x \<in> U \<and> y \<notin> U" using \<open>x\<noteq> y\<close> by (simp add:t1_space)
  let ?V = "SOME A. open A \<and> x\<in> A \<and> y\<notin> A"
  have vprop: "open ?V \<and> x \<in> ?V \<and> y \<notin> ?V" using someI_ex[of "\<lambda>U. open U \<and> x \<in> U \<and> y \<notin> U"] ex by blast
  show "open (open_except x y)" by (simp add: open_except_def vprop)
  show "x\<in> open_except x y" by (metis (full_types) open_except_def vprop)
  show "y\<notin> open_except x y" by (metis (full_types) open_except_def vprop)
qed

lemma open_except_set:
  assumes "finite A"
  and "(x::'b::{t1_space}) \<notin> A"
shows "\<exists>U. open U \<and> x\<in> U \<and> U\<inter> A = {}"
proof(intro exI conjI)
  have "\<forall>y\<in> A. x\<noteq> y" using assms by auto
  let ?U = "\<Inter> y \<in> A. open_except x y"
  show "open ?U"
  proof (intro open_INT ballI, (simp add: assms))
    fix y
    assume "y\<in> A"
    show "open (open_except x y)" using \<open>\<forall>y\<in> A. x\<noteq> y\<close> by (simp add: \<open>y \<in> A\<close> open_exceptI)
  qed
  show "x \<in> (\<Inter>y\<in>A. open_except x y)"
  proof
    fix y
    assume "y\<in> A"
    show "x\<in>open_except x y" using \<open>\<forall>y\<in> A. x\<noteq> y\<close> by (simp add: \<open>y \<in> A\<close> open_exceptI)
  qed
  have "\<forall>y\<in>A. y\<notin> ?U" using \<open>\<forall>y\<in> A. x\<noteq> y\<close> open_exceptI(3) by auto
  thus "(\<Inter>y\<in>A. open_except x y) \<inter> A = {}" by auto
qed

definition open_exclude_set where
"open_exclude_set x A = (if (\<exists>U. open U \<and> U\<inter> A = {x}) then SOME U. open U \<and> U \<inter> A = {x} else {})"

lemma open_exclude_setI:
  assumes "\<exists>U. open U \<and> U\<inter> A = {x}"
shows "open (open_exclude_set x A)" and "(open_exclude_set x A) \<inter> A = {x}"
proof -
  let ?V = "SOME U. open U \<and> U \<inter> A = {x}"
  have vprop: "open ?V \<and> ?V \<inter> A = {x}" using someI_ex[of "\<lambda>U. open U \<and> U \<inter> A = {x}"] assms by blast
  show "open (open_exclude_set x A)" by (simp add: open_exclude_set_def vprop)
  show "open_exclude_set x A \<inter> A = {x}" by (metis (mono_tags, lifting) open_exclude_set_def vprop)
qed

lemma open_exclude_finite:
  assumes "finite A"
  and "(x::'b::{t1_space})\<in> A"
shows open_set: "open (open_exclude_set x A)" and inter_x:"(open_exclude_set x A) \<inter> A = {x}"
proof -
  have "\<exists>U. open U \<and> U\<inter> A = {x}"
  proof -
    have "\<exists>U. open U \<and> x\<in> U \<and> U\<inter> (A-{x}) = {}"
    proof (rule open_except_set)
      show "finite (A -{x})" using assms by auto
      show "x\<notin> A -{x}" by simp
    qed
    thus ?thesis using assms by auto
  qed
  thus "open (open_exclude_set x A)" and "(open_exclude_set x A) \<inter> A = {x}" by (auto simp add: open_exclude_setI)
qed

subsection \<open>Initially trivial filtrations\<close>
text \<open>Intuitively, these are filtrations that can be used to denote the fact that there is no information at the start.\<close>

definition init_triv_filt::"'a measure \<Rightarrow> ('i::linorder_bot \<Rightarrow> 'a measure) \<Rightarrow> bool" where
  "init_triv_filt M F \<longleftrightarrow> filtration M F \<and> sets (F bot) = {{}, space M}"

lemma triv_measurable_cst:
  fixes f::"'a\<Rightarrow>'b::{t2_space}"
  assumes "space N = space M"
  and "space M \<noteq> {}"
  and "sets N = {{}, space M}"
  and "f\<in> measurable N borel"
shows "\<exists> c::'b. \<forall>x\<in> space N. f x = c"
proof -
  have "f `(space N) \<noteq> {}" using assms by (simp add: assms)
  hence "\<exists> c. c\<in> f`(space N)" by auto
  from this obtain c where "c\<in> f`(space N)" by auto
  have "\<forall>x \<in> space N. f x = c"
  proof
    fix x
    assume "x\<in> space N"
    show "f x = c"
    proof (rule ccontr)
      assume "f x \<noteq> c"
      hence "(\<exists>U V. open U \<and> open V \<and> (f x) \<in> U \<and> c \<in> V \<and> U \<inter> V = {})" by (simp add: separation_t2)
      from this obtain U and V where "open U" and "open V" and "(f x) \<in> U" and "c \<in> V" and "U \<inter> V = {}" by blast
      have "(f -`V) \<inter> space N = space N"
      proof -
        have "V\<in> sets borel" using \<open>open V\<close> unfolding borel_def by simp
        hence "(f -`V) \<inter> space N \<in> sets N" using assms unfolding measurable_def by simp
        show "(f -`V) \<inter> space N = space N"
        proof (rule ccontr)
          assume "(f -`V) \<inter> space N \<noteq> space N"
          hence "(f -`V) \<inter> space N = {}" using assms \<open>(f -`V) \<inter> space N \<in> sets N\<close> by simp
          thus False using \<open>c\<in>V\<close> using \<open>c \<in> f ` space N\<close> by blast
        qed
      qed
      have "((f-`U)\<inter> space N) \<inter> ((f-`V) \<inter> space N) = {}" using \<open>U\<inter>V = {}\<close> by auto
      moreover have "(f -`U) \<inter> space N \<in> sets N" using assms \<open>open U\<close> unfolding measurable_def by simp
      ultimately have "(f -`U) \<inter> space N = {}" using assms \<open>(f -`V) \<inter> space N = space N\<close> by simp
      thus False using \<open>f x \<in> U\<close> \<open>x \<in> space N\<close> by blast
    qed
  qed
  thus "\<exists> c. \<forall>x\<in> space N. f x = c" by auto
qed

locale trivial_init_filtrated_prob_space = prob_space +
  fixes F
  assumes info_filtration: "init_triv_filt M F"

sublocale trivial_init_filtrated_prob_space \<subseteq> filtrated_prob_space
  using info_filtration unfolding init_triv_filt_def by (unfold_locales, simp)


locale triv_init_disc_filtr_prob_space = prob_space +
  fixes F
  assumes info_disc_filtr: "disc_filtr M F \<and> sets (F bot) = {{}, space M}"

sublocale triv_init_disc_filtr_prob_space \<subseteq> trivial_init_filtrated_prob_space
proof unfold_locales
  show "init_triv_filt M F" using info_disc_filtr bot_nat_def unfolding init_triv_filt_def disc_filtr_def
    by (simp add: filtrationI)

qed


sublocale triv_init_disc_filtr_prob_space \<subseteq> disc_filtr_prob_space
proof unfold_locales
  show "disc_filtr M F" using info_disc_filtr by simp
qed

lemma (in triv_init_disc_filtr_prob_space) adapted_init:
  assumes "borel_adapt_stoch_proc F x"
  shows "\<exists>c. \<forall>w \<in> space M. ((x 0 w)::real) = c"
proof -
  have "space M = space (F 0)" using filtration
    by (simp add: filtration_def subalgebra_def)
  moreover have "\<exists>c. \<forall>w \<in> space (F 0). x 0 w = c"
  proof (rule triv_measurable_cst)
    show "space (F 0) = space M" using \<open>space M = space (F 0)\<close> ..
    show "sets (F 0) = {{}, space M}" using info_disc_filtr
      by (simp add: init_triv_filt_def bot_nat_def)
    show "x 0 \<in> borel_measurable (F 0)" using assms by (simp add: adapt_stoch_proc_def)
    show "space M \<noteq> {}" by (simp add:not_empty)
  qed
  ultimately show ?thesis by simp
qed

subsection \<open>Filtration-equivalent measure spaces\<close>
text \<open>This is a relaxation of the notion of equivalent probability spaces, where equivalence is tested modulo a
filtration. Equivalent measure spaces agree on events that have a zero probability of occurring; here, filtration-equivalent
measure spaces agree on such events when they belong to the filtration under consideration.\<close>

definition filt_equiv where
"filt_equiv F M N \<longleftrightarrow> sets M = sets N \<and> filtration M F  \<and> (\<forall> t A. A \<in> sets (F t) \<longrightarrow> (emeasure M A = 0) \<longleftrightarrow> (emeasure N A = 0))"


lemma filt_equiv_space:
  assumes "filt_equiv F M N"
  shows "space M = space N" using assms unfolding filt_equiv_def
 filtration_def subalgebra_def by (meson sets_eq_imp_space_eq)

lemma filt_equiv_sets:
  assumes "filt_equiv F M N"
  shows "sets M = sets N" using assms unfolding filt_equiv_def by simp



lemma filt_equiv_filtration:
  assumes "filt_equiv F M N"
  shows "filtration N F" using assms unfolding filt_equiv_def filtration_def subalgebra_def
  by (metis sets_eq_imp_space_eq)




lemma (in filtrated_prob_space) AE_borel_eq:
fixes f::"'a\<Rightarrow>real"
assumes "f\<in> borel_measurable (F t)"
and "g\<in> borel_measurable (F t)"
and "AE w in M. f w = g w"
shows "{w\<in> space M. f w \<noteq> g w} \<in> sets (F t) \<and> emeasure M {w\<in> space M. f w \<noteq> g w} = 0"
proof
  show "{w \<in> space M. f w \<noteq> g w} \<in> sets (F t)"
  proof -
    define minus where "minus = (\<lambda>w. (f w) - (g w))"
    have "minus \<in> borel_measurable (F t)" unfolding minus_def using assms by simp
    hence "{w\<in> space (F t). 0 < minus w} \<in> sets (F t)" using borel_measurable_iff_greater by auto
    moreover have "{w\<in> space (F t). minus w < 0} \<in> sets (F t)" using borel_measurable_iff_less
      \<open>minus \<in> borel_measurable (F t)\<close> by auto
    ultimately have "{w\<in> space (F t). 0 < minus w} \<union> {w\<in> space (F t). minus w < 0} \<in> sets (F t)" by simp
    moreover have "{w\<in> space (F t). f w \<noteq> g w} = {w\<in> space (F t). 0 < minus w} \<union> {w\<in> space (F t). minus w < 0}"
    proof
      show "{w \<in> space (F t). f w \<noteq> g w} \<subseteq> {w \<in> space (F t). 0 < minus w} \<union> {w \<in> space (F t). minus w < 0}"
      proof
        fix w
        assume "w \<in> {w \<in> space (F t). f w \<noteq> g w}"
        hence "w\<in> space (F t)" and "f w \<noteq> g w" by auto
        thus "w\<in> {w \<in> space (F t). 0 < minus w} \<union> {w \<in> space (F t). minus w < 0}" unfolding minus_def
          by (cases "f w < g w") auto
      qed
      have "{w \<in> space (F t). 0 < minus w} \<subseteq> {w \<in> space (F t). f w \<noteq> g w}" unfolding minus_def by auto
      moreover have "{w \<in> space (F t). minus w < 0} \<subseteq> {w \<in> space (F t). f w \<noteq> g w}" unfolding minus_def by auto
      ultimately show "{w \<in> space (F t). 0 < minus w} \<union> {w \<in> space (F t). minus w < 0} \<subseteq> {w \<in> space (F t). f w \<noteq> g w}"
        by simp
    qed
    moreover have "space (F t) = space M" using filtration unfolding filtration_def subalgebra_def by simp
    ultimately show ?thesis by simp
  qed
  show "emeasure M {w\<in> space M. f w \<noteq> g w} = 0" by (metis (no_types) AE_iff_measurable assms(3) emeasure_notin_sets)
qed


lemma (in prob_space) filt_equiv_borel_AE_eq:
  fixes f::"'a\<Rightarrow> real"
  assumes "filt_equiv F M N"
and "f\<in> borel_measurable (F t)"
and "g\<in> borel_measurable (F t)"
and "AE w in M. f w = g w"
shows "AE w in N. f w = g w"
proof -
  have set0: "{w\<in> space M. f w \<noteq> g w} \<in> sets (F t) \<and> emeasure M {w\<in> space M. f w \<noteq> g w} = 0"
  proof (rule filtrated_prob_space.AE_borel_eq, (auto simp add: assms))
    show "filtrated_prob_space M F" using assms unfolding filt_equiv_def
      by (simp add: filtrated_prob_space_axioms.intro filtrated_prob_space_def prob_space_axioms)
  qed
  hence "emeasure N {w\<in> space M. f w \<noteq> g w} = 0" using assms unfolding filt_equiv_def by auto
  moreover have "{w\<in> space M. f w \<noteq> g w} \<in> sets N" using set0 assms unfolding filt_equiv_def
    filtration_def subalgebra_def by auto
  ultimately show ?thesis
  proof -
  have "space M = space N"
    by (metis assms(1) filt_equiv_space)
    then have "\<forall>p. almost_everywhere N p \<or> {a \<in> space N. \<not> p a} \<noteq> {a \<in> space N. f a \<noteq> g a}"
      using AE_iff_measurable \<open>emeasure N {w \<in> space M. f w \<noteq> g w} = 0\<close> \<open>{w \<in> space M. f w \<noteq> g w} \<in> sets N\<close>
      by auto
    then show ?thesis
      by metis
  qed
qed

lemma filt_equiv_prob_space_subalgebra:
  assumes "prob_space N"
  and "filt_equiv F M N"
  and "sigma_finite_subalgebra M G"
shows "sigma_finite_subalgebra N G" unfolding sigma_finite_subalgebra_def
proof
  show "subalgebra N G"
    by (metis assms(2) assms(3) filt_equiv_space filt_equiv_def sigma_finite_subalgebra_def subalgebra_def)
  show "sigma_finite_measure (restr_to_subalg N G)" unfolding restr_to_subalg_def
    by (metis \<open>subalgebra N G\<close> assms(1) finite_measure_def finite_measure_restr_to_subalg prob_space_def restr_to_subalg_def)
qed


lemma filt_equiv_measurable:
  assumes "filt_equiv F M N"
  and "f\<in> measurable M P"
shows "f\<in> measurable N P" using assms unfolding filt_equiv_def measurable_def
proof -
  assume a1: "sets M = sets N \<and> Filtration.filtration M F \<and> (\<forall>t A. A \<in> sets (F t) \<longrightarrow> (emeasure M A = 0) = (emeasure N A = 0))"
  assume a2: "f \<in> {f \<in> space M \<rightarrow> space P. \<forall>y\<in>sets P. f -` y \<inter> space M \<in> sets M}"
  have "space N = space M"
    using a1 by (metis (lifting) sets_eq_imp_space_eq)
  then show "f \<in> {f \<in> space N \<rightarrow> space P. \<forall>C\<in>sets P. f -` C \<inter> space N \<in> sets N}"
    using a2 a1 by force
qed


lemma filt_equiv_imp_subalgebra:
  assumes "filt_equiv F M N"
shows "subalgebra N M" unfolding subalgebra_def
  using assms filt_equiv_space filt_equiv_def by blast




end