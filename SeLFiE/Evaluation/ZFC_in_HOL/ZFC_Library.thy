theory ZFC_Library
  imports "HOL-Library.Countable_Set" "HOL-Library.Equipollence" "HOL-Cardinals.Cardinals"

begin

text\<open>Equipollence and Lists.\<close>

lemma countable_iff_lepoll: "countable A \<longleftrightarrow> A \<lesssim> (UNIV :: nat set)"
  by (auto simp: countable_def lepoll_def)

lemma infinite_times_eqpoll_self:
  assumes "infinite A" shows "A \<times> A \<approx> A"
  by (simp add: Times_same_infinite_bij_betw assms eqpoll_def)

lemma infinite_finite_times_lepoll_self:
  assumes "infinite A" "finite B" shows "A \<times> B \<lesssim> A"
proof -
  have "B \<lesssim> A"
    by (simp add: assms finite_lepoll_infinite)
  then have "A \<times> B \<lesssim> A \<times> A"
    by (simp add: subset_imp_lepoll times_lepoll_mono)
  also have "\<dots> \<approx> A"
    by (simp add: \<open>infinite A\<close> infinite_times_eqpoll_self)
  finally show ?thesis .
qed

lemma lists_n_lepoll_self:
  assumes "infinite A" shows "{l \<in> lists A. length l = n} \<lesssim> A"
proof (induction n)
  case 0
  have "{l \<in> lists A. length l = 0} = {[]}"
    by auto
  then show ?case
    by (metis Set.set_insert assms ex_in_conv finite.emptyI singleton_lepoll)
next
  case (Suc n)
  have "{l \<in> lists A. length l = Suc n} = (\<Union>x\<in>A. \<Union>l \<in> {l \<in> lists A. length l = n}. {x#l})"
    by (auto simp: length_Suc_conv)
  also have "\<dots> \<lesssim> A \<times> {l \<in> lists A. length l = n}"
    unfolding lepoll_iff
    by (rule_tac x="\<lambda>(x,l). Cons x l" in exI) auto
  also have "\<dots> \<lesssim> A"
  proof (cases "finite {l \<in> lists A. length l = n}")
    case True
    then show ?thesis
      using assms infinite_finite_times_lepoll_self by blast
  next
    case False
    have "A \<times> {l \<in> lists A. length l = n} \<lesssim> A \<times> A"
      by (simp add: Suc.IH subset_imp_lepoll times_lepoll_mono)
    also have "\<dots> \<approx> A"
      by (simp add: assms infinite_times_eqpoll_self)
    finally show ?thesis .
  qed
  finally show ?case .
qed

lemma infinite_eqpoll_lists:
    assumes "infinite A" shows "lists A \<approx> A"
proof -
  have "lists A \<lesssim> Sigma UNIV (\<lambda>n. {l \<in> lists A. length l = n})"
    unfolding lepoll_iff
    by (rule_tac x=snd in exI) (auto simp: in_listsI snd_image_Sigma)
  also have "\<dots> \<lesssim> (UNIV::nat set) \<times> A"
    by (rule Sigma_lepoll_mono) (auto simp: lists_n_lepoll_self assms)
  also have "\<dots> \<lesssim> A \<times> A"
    by (metis assms infinite_le_lepoll order_refl subset_imp_lepoll times_lepoll_mono)
  also have "\<dots> \<approx> A"
    by (simp add: assms infinite_times_eqpoll_self)
  finally show ?thesis
    by (simp add: lepoll_antisym lepoll_lists)
qed

end
