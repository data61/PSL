section "List Inversion"

theory Inversion
imports "List-Index.List_Index"
begin

abbreviation "dist_perm xs ys \<equiv> distinct xs \<and> distinct ys \<and> set xs = set ys"

definition before_in :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
  ("(_ </ _/ in _)" [55,55,55] 55) where
"x < y in xs = (index xs x < index xs y \<and> y \<in> set xs)"

definition Inv :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a * 'a) set" where
"Inv xs ys = {(x,y). x < y in xs \<and> y < x in ys}"

lemma before_in_setD1: "x < y in xs \<Longrightarrow> x : set xs"
by (metis index_conv_size_if_notin index_less before_in_def less_asym order_refl)

lemma before_in_setD2: "x < y in xs \<Longrightarrow> y : set xs"
by (simp add: before_in_def)


lemma not_before_in:
  "x : set xs \<Longrightarrow> y : set xs \<Longrightarrow> \<not> x < y in xs \<longleftrightarrow> y < x in xs \<or> x=y"
by (metis index_eq_index_conv before_in_def less_asym linorder_neqE_nat)

lemma before_in_irefl: "x < x in xs = False"
by (meson before_in_setD2 not_before_in)

lemma no_before_inI[simp]: "x < y in xs \<Longrightarrow> (\<not> y < x in xs) = True"
by (metis before_in_setD1 not_before_in)

lemma finite_Invs[simp]:  "finite(Inv xs ys)"
apply(rule finite_subset[where B = "set xs \<times> set ys"])
apply(auto simp add: Inv_def before_in_def)
apply(metis index_conv_size_if_notin index_less_size_conv less_asym)+
done

lemma Inv_id[simp]: "Inv xs xs = {}"
by(auto simp add: Inv_def before_in_def)

lemma card_Inv_sym: "card(Inv xs ys) = card(Inv ys xs)"
proof -
  have "Inv xs ys = (\<lambda>(x,y). (y,x)) ` Inv ys xs" by(auto simp: Inv_def)
  thus ?thesis by (metis card_image swap_inj_on)
qed

lemma Inv_tri_ineq:
  "dist_perm xs ys \<Longrightarrow> dist_perm ys zs \<Longrightarrow>
  Inv xs zs \<subseteq> Inv xs ys Un Inv ys zs"
by(auto simp: Inv_def) (metis before_in_setD1 not_before_in)

lemma card_Inv_tri_ineq:
  "dist_perm xs ys \<Longrightarrow> dist_perm ys zs \<Longrightarrow>
  card (Inv xs zs) \<le> card(Inv xs ys) + card (Inv ys zs)"
using card_mono[OF _ Inv_tri_ineq[of xs ys zs]]
by auto (metis card_Un_Int finite_Invs trans_le_add1)

end
