(* Title: List_Bits.thy
  Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Exclusive or on lists\<close>

theory List_Bits imports Misc_CryptHOL begin

definition xor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a :: {uminus,inf,sup}" (infixr "\<oplus>" 67)
where "x \<oplus> y = inf (sup x y) (- (inf x y))"

lemma xor_bool_def [iff]: fixes x y :: bool shows "x \<oplus> y \<longleftrightarrow> x \<noteq> y"
by(auto simp add: xor_def)

lemma xor_commute:
  fixes x y :: "'a :: {semilattice_sup,semilattice_inf,uminus}"
  shows "x \<oplus> y = y \<oplus> x"
by(simp add: xor_def sup.commute inf.commute)

lemma xor_assoc:
  fixes x y :: "'a :: boolean_algebra"
  shows "(x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
by(simp add: xor_def inf_sup_aci inf_sup_distrib1 inf_sup_distrib2)

lemma xor_left_commute:
  fixes x y :: "'a :: boolean_algebra"
  shows "x \<oplus> (y \<oplus> z) = y \<oplus> (x \<oplus> z)"
by (metis xor_assoc xor_commute)

lemma [simp]:
  fixes x :: "'a :: boolean_algebra"
  shows xor_bot: "x \<oplus> bot = x"
  and bot_xor: "bot \<oplus> x = x"
  and xor_top: "x \<oplus> top = - x"
  and top_xor: "top \<oplus> x = - x"
by(simp_all add: xor_def)

lemma xor_inverse [simp]:
  fixes x :: "'a :: boolean_algebra"
  shows "x \<oplus> x = bot"
by(simp add: xor_def)

lemma xor_left_inverse [simp]:
  fixes x :: "'a :: boolean_algebra"
  shows "x \<oplus> x \<oplus> y = y"
by(metis xor_left_commute xor_inverse xor_bot)

lemmas xor_ac = xor_assoc xor_commute xor_left_commute


definition xor_list :: "'a :: {uminus,inf,sup} list \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixr "[\<oplus>]" 67)
where "xor_list xs ys = map (case_prod (\<oplus>)) (zip xs ys)"

lemma xor_list_unfold:
  "xs [\<oplus>] ys = (case xs of [] \<Rightarrow> [] | x # xs' \<Rightarrow> (case ys of [] \<Rightarrow> [] | y # ys' \<Rightarrow> x \<oplus> y # xs' [\<oplus>] ys'))"
by(simp add: xor_list_def split: list.split)

lemma xor_list_commute: fixes xs ys :: "'a :: {semilattice_sup,semilattice_inf,uminus} list"
  shows "xs [\<oplus>] ys = ys [\<oplus>] xs"
unfolding xor_list_def by(subst zip_commute)(auto simp add: split_def xor_commute)

lemma xor_list_assoc [simp]: 
  fixes xs ys :: "'a :: boolean_algebra list"
  shows "(xs [\<oplus>] ys) [\<oplus>] zs = xs [\<oplus>] (ys [\<oplus>] zs)"
unfolding xor_list_def zip_map1 zip_map2
apply(subst (2) zip_commute)
apply(subst zip_left_commute)
apply(subst (2) zip_commute)
apply(auto simp add: zip_map2 split_def xor_assoc)
done

lemma xor_list_left_commute:
  fixes xs ys zs :: "'a :: boolean_algebra list"
  shows "xs [\<oplus>] (ys [\<oplus>] zs) = ys [\<oplus>] (xs [\<oplus>] zs)"
by(metis xor_list_assoc xor_list_commute)

lemmas xor_list_ac = xor_list_assoc xor_list_commute xor_list_left_commute

lemma xor_list_inverse [simp]: 
  fixes xs :: "'a :: boolean_algebra list"
  shows "xs [\<oplus>] xs = replicate (length xs) bot"
by(simp add: xor_list_def zip_same_conv_map o_def map_replicate_const)

lemma xor_replicate_bot_right [simp]:
  fixes xs :: "'a :: boolean_algebra list"
  shows "\<lbrakk> length xs \<le> n; x = bot \<rbrakk> \<Longrightarrow> xs [\<oplus>] replicate n x = xs"
by(simp add: xor_list_def zip_replicate2 o_def)

lemma xor_replicate_bot_left [simp]:
  fixes xs :: "'a :: boolean_algebra list"
  shows "\<lbrakk> length xs \<le> n; x = bot \<rbrakk> \<Longrightarrow> replicate n x [\<oplus>] xs = xs"
by(simp add: xor_list_commute)

lemma xor_list_left_inverse [simp]:
  fixes xs :: "'a :: boolean_algebra list"
  shows "length ys \<le> length xs \<Longrightarrow> xs [\<oplus>] (xs [\<oplus>] ys) = ys"
by(subst xor_list_assoc[symmetric])(simp)

lemma length_xor_list [simp]: "length (xor_list xs ys) = min (length xs) (length ys)"
by(simp add: xor_list_def)

lemma inj_on_xor_list_nlists [simp]:
  fixes xs :: "'a :: boolean_algebra list"
  shows "n \<le> length xs \<Longrightarrow> inj_on (xor_list xs) (nlists UNIV n)"
apply(clarsimp simp add: inj_on_def in_nlists_UNIV)
using xor_list_left_inverse by fastforce

lemma one_time_pad:
  fixes xs :: "_ :: boolean_algebra list"
  shows "length xs \<ge> n \<Longrightarrow> map_spmf (xor_list xs) (spmf_of_set (nlists UNIV n)) = spmf_of_set (nlists UNIV n)"
by(auto 4 3 simp add: in_nlists_UNIV intro: xor_list_left_inverse[symmetric] rev_image_eqI intro!: arg_cong[where f=spmf_of_set])

end
