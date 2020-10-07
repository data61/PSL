theory Nominal_Bounded_Set
imports
  Nominal2.Nominal2
  "HOL-Cardinals.Bounded_Set"
begin

section \<open>Bounded Sets Equipped With a Permutation Action\<close>

text \<open>Additional lemmas about bounded sets.\<close>

interpretation bset_lifting: bset_lifting .

lemma Abs_bset_inverse' [simp]:
  assumes "|A| <o natLeq +c |UNIV :: 'k set|"
  shows "set_bset (Abs_bset A :: 'a set['k]) = A"
by (metis Abs_bset_inverse assms mem_Collect_eq)

text \<open>Bounded sets are equipped with a permutation action, provided their elements are.\<close>

instantiation bset :: (pt,type) pt
begin

  lift_definition permute_bset :: "perm \<Rightarrow> 'a set['b] \<Rightarrow> 'a set['b]" is
    permute
  proof -
    fix p and A :: "'a set"
    have "|p \<bullet> A| \<le>o |A|" by (simp add: permute_set_eq_image)
    also assume "|A| <o natLeq +c |UNIV :: 'b set|"
    finally show "|p \<bullet> A| <o natLeq +c |UNIV :: 'b set|" .
  qed

  instance
  by standard (transfer, simp)+

end

lemma Abs_bset_eqvt [simp]:
  assumes "|A| <o natLeq +c |UNIV :: 'k set|"
  shows "p \<bullet> (Abs_bset A :: 'a::pt set['k]) = Abs_bset (p \<bullet> A)"
by (simp add: permute_bset_def map_bset_def image_def permute_set_def) (metis (no_types, lifting) Abs_bset_inverse' assms)

lemma supp_Abs_bset [simp]:
  assumes "|A| <o natLeq +c |UNIV :: 'k set|"
  shows "supp (Abs_bset A :: 'a::pt set['k]) = supp A"
proof -
  from assms have "\<And>p. p \<bullet> (Abs_bset A :: 'a::pt set['k]) \<noteq> Abs_bset A \<longleftrightarrow> p \<bullet> A \<noteq> A"
    by simp (metis map_bset.rep_eq permute_set_eq_image set_bset_inverse set_bset_to_set_bset)
  then show ?thesis
    unfolding supp_def by simp
qed

lemma map_bset_permute: "p \<bullet> B = map_bset (permute p) B"
by transfer (auto simp add: image_def permute_set_def)

lemma set_bset_eqvt [eqvt]:
  "p \<bullet> set_bset B = set_bset (p \<bullet> B)"
by transfer simp

lemma map_bset_eqvt [eqvt]:
  "p \<bullet> map_bset f B = map_bset (p \<bullet> f) (p \<bullet> B)"
by transfer simp

lemma bempty_eqvt [eqvt]: "p \<bullet> bempty = bempty"
by transfer simp

lemma binsert_eqvt [eqvt]: "p \<bullet> (binsert x B) = binsert (p \<bullet> x) (p \<bullet> B)"
by transfer simp

lemma bsingleton_eqvt [eqvt]: "p \<bullet> bsingleton x = bsingleton (p \<bullet> x)"
by (simp add: map_bset_permute)

end
