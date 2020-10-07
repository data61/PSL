theory Word_Extensions
imports
  "HOL-Library.Omega_Words_Fun"
  List_Extensions
begin

  hide_const (open) Sublist.prefix Sublist.suffix

  (*abbreviation "prefix k w \<equiv> map w [0 ..< k]"*)
  abbreviation "scan f w a \<equiv> \<lambda> i. fold f (prefix i w) a"

  (*lemma set_subsequence[intro, simp]: "set (w[i\<rightarrow>j]) \<subseteq> range w" 
    unfolding subsequence_def by auto*)
  lemma range_suffix[intro, simp]: "range (suffix i w) \<subseteq> range w"
    unfolding Omega_Words_Fun.suffix_def by blast

  lemma suffix_comp: "suffix i v = v \<circ> plus i" unfolding suffix_def by force

  (* \<rightarrow> see subsequence_shift
  lemma map_suffix[simp]: "map (suffix i v) [j ..< j + n] = map v [i + j ..< i + j + n]"
  proof -
    have "map (suffix i v) [j ..< j + n] = map (v \<circ> op + i) [j ..< j + n]"
      unfolding suffix_comp by simp
    also have "\<dots> = (map v \<circ> map (op + i)) [j ..< j + n]" by simp
    also have "\<dots> =  map v (map (op + i) [j ..< j + n])" unfolding comp_apply by simp
    also have "\<dots> =  map v [i + j ..< i + j + n]" by (simp add: algebra_simps)
    finally show ?thesis by this
  qed*)

  (*
  \<rightarrow> see suffix_subseq_join

  lemma suffix_prefix_suffix[simp]: "map v [i ..< i + n] \<frown> suffix (i + n) v = suffix i v"
  proof -
    have "suffix i v = map (suffix i v) [0 ..< n] \<frown> suffix n (suffix i v)"
      using prefix_suffix
      by blast
    also have "\<dots> = map (suffix i v) [0 ..< 0 + n] \<frown> suffix (i + n) v" by simp
    also have "\<dots> = map v [i ..< i + n] \<frown> suffix (i + n) v" unfolding map_suffix by simp
    finally show ?thesis by simp
  qed*)


end