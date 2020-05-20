(*  Author: Tobias Nipkow  *)

section \<open>Comparing Enumeration and Archive\<close>

theory ArchCompAux
imports TameEnum Trie.Tries Maps Arch Worklist
begin

function qsort :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"qsort le []       = []" |
"qsort le (x#xs) = qsort le [y\<leftarrow>xs . \<not> le x y] @ [x] @
                   qsort le [y\<leftarrow>xs . le x y]"
by pat_completeness auto
termination by (relation "measure (size \<circ> snd)")
  (auto simp add: length_filter_le [THEN le_less_trans])

definition nof_vertices :: "'a fgraph \<Rightarrow> nat" where
"nof_vertices = length \<circ> remdups \<circ> concat"

definition fgraph :: "graph \<Rightarrow> nat fgraph" where
"fgraph g = map vertices (faces g)"

definition hash :: "nat fgraph \<Rightarrow> nat list" where
  "hash fs = (let n = nof_vertices fs in
     [n, size fs] @
     qsort (\<lambda>x y. y < x) (map (\<lambda>i. foldl (+) 0 (map size [f\<leftarrow>fs. i \<in> set f]))
                             [0..<n]))"
(*
definition diff2 :: "nat fgraph list \<Rightarrow> nat fgraph list
   \<Rightarrow> nat fgraph list * nat fgraph list" where
"diff2 fgs ags =
 (let tfgs = trie_of_list hash fgs;
      tags = trie_of_list hash ags in
  (filter (\<lambda>fg. \<not>list_ex (iso_test fg) (lookup_trie tags (hash fg))) fgs,
   filter (\<lambda>ag. \<not>list_ex (iso_test ag) (lookup_trie tfgs (hash ag))) ags))"
*)
definition samet :: "(nat,nat fgraph) tries option \<Rightarrow> nat fgraph list \<Rightarrow> bool"
where
  "samet fgto ags = (case fgto of None \<Rightarrow> False | Some tfgs \<Rightarrow>
   let tags = tries_of_list hash ags in
   (all_tries (\<lambda>fg. list_ex (iso_test fg) (lookup_tries tags (hash fg))) tfgs \<and>
    all_tries (\<lambda>ag. list_ex (iso_test ag) (lookup_tries tfgs (hash ag))) tags))"

definition pre_iso_test :: "vertex fgraph \<Rightarrow> bool" where
  "pre_iso_test Fs \<longleftrightarrow>
   [] \<notin> set Fs \<and> (\<forall>F\<in>set Fs. distinct F) \<and> distinct (map rotate_min Fs)"


interpretation map:
  maps "Trie None []" update_trie lookup_tries invar_trie
proof (standard, goal_cases)
  case 1 show ?case by(rule ext) simp
next
  case 2 show ?case by(rule ext) (simp add: lookup_update)
next
  case 3 show ?case by(simp)
next
  case 4 thus ?case by (simp add: invar_trie_update)
qed

lemma set_of_conv: "set_tries = maps.set_of lookup_tries"
by(rule ext) (auto simp add: set_tries_def map.set_of_def)

end
