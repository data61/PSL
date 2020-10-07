section \<open>List Prefixes\<close>

theory List_Prefixes
imports "HOL-Library.Prefix_Order"
begin

  lemmas [intro] = prefixI strict_prefixI[folded less_eq_list_def]
  lemmas [elim] = prefixE strict_prefixE[folded less_eq_list_def]

  lemmas [intro?] = take_is_prefix[folded less_eq_list_def]

  hide_const (open) Sublist.prefix Sublist.suffix

  lemma prefix_finI_item[intro!]:
    assumes "a = b" "u \<le> v"
    shows "a # u \<le> b # v"
    using assms by force
  lemma prefix_finE_item[elim!]:
    assumes "a # u \<le> b # v"
    obtains "a = b" "u \<le> v"
    using assms by force

  lemma prefix_fin_append[intro]: "u \<le> u @ v" by auto
  lemma pprefix_fin_length[dest]:
    assumes "u < v"
    shows "length u < length v"
  proof -
    obtain a w where 1: "v = u @ a # w" using assms by rule
    show ?thesis unfolding 1 by simp
  qed

end