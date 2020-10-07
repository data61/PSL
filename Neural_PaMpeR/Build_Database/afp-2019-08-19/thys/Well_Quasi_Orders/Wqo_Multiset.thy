(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>Multiset Extension Preserves Well-Quasi-Orders\<close>

theory Wqo_Multiset
imports
  Multiset_Extension
  Well_Quasi_Orders
begin

lemma list_emb_imp_reflclp_mulex_on:
  assumes "xs \<in> lists A" and "ys \<in> lists A"
    and "list_emb P xs ys"
  shows "(mulex_on P A)\<^sup>=\<^sup>= (mset xs) (mset ys)"
using assms(3, 1, 2)
proof (induct)
  case (list_emb_Nil ys)
  then show ?case
    by (cases ys) (auto intro!: empty_mulex_on simp: multisets_def)
next
  case (list_emb_Cons xs ys y)
  then show ?case by (auto intro!: mulex_on_self_add_singleton_right simp: multisets_def)
next
  case (list_emb_Cons2 x y xs ys)
  then show ?case
    by (force intro: union_mulex_on_mono mulex_on_add_mset
             mulex_on_add_mset' mulex_on_add_mset_mono
             simp: multisets_def)
qed

text \<open>The (reflexive closure of the) multiset extension of an almost-full relation
is almost-full.\<close>
lemma almost_full_on_multisets:
  assumes "almost_full_on P A"
  shows "almost_full_on (mulex_on P A)\<^sup>=\<^sup>= (multisets A)"
proof -
  let ?P = "(mulex_on P A)\<^sup>=\<^sup>="
  from almost_full_on_hom [OF _ almost_full_on_lists, of A P ?P mset,
    OF list_emb_imp_reflclp_mulex_on, simplified]
    show ?thesis using assms by blast
qed

lemma wqo_on_multisets:
  assumes "wqo_on P A"
  shows "wqo_on (mulex_on P A)\<^sup>=\<^sup>= (multisets A)"
proof
  from transp_on_mulex_on [of P A "multisets A"]
    show "transp_on (mulex_on P A)\<^sup>=\<^sup>= (multisets A)"
    unfolding transp_on_def by blast
next
  from almost_full_on_multisets [OF assms [THEN wqo_on_imp_almost_full_on]]
    show "almost_full_on (mulex_on P A)\<^sup>=\<^sup>= (multisets A)" .
qed

end

