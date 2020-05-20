section \<open>Finite partial functions\<close>

theory More_Finite_Map imports
  "HOL-Library.Finite_Map"
begin

unbundle lifting_syntax
unbundle fmap.lifting

type_notation fmap (infix "\<rightharpoonup>\<^sub>f" 9)


subsection \<open>Difference\<close>

definition
  map_diff :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k fset \<Rightarrow> ('k \<rightharpoonup> 'v)"
where
  "map_diff f ks = restrict_map f (- fset ks)"

lift_definition
  fmap_diff :: "('k \<rightharpoonup>\<^sub>f 'v) \<Rightarrow> 'k fset \<Rightarrow> ('k \<rightharpoonup>\<^sub>f 'v)" (infix "\<ominus>" 110)
is "map_diff"
by (auto simp add: map_diff_def)

subsection \<open>Comprehension\<close>

definition
  make_map :: "'k fset \<Rightarrow> 'v \<Rightarrow> ('k \<rightharpoonup> 'v)"
where
  "make_map ks v \<equiv> \<lambda>k. if k \<in> fset ks then Some v else None"

lemma make_map_transfer[transfer_rule]: "(rel_fset (=) ===> A ===> rel_map A) make_map make_map"
unfolding make_map_def
by transfer_prover

lemma dom_make_map:
  "dom (make_map ks v) = fset ks"
by (metis domIff make_map_def not_Some_eq set_eqI)

lift_definition
  make_fmap :: "'k fset \<Rightarrow> 'v \<Rightarrow> ('k \<rightharpoonup>\<^sub>f 'v)" ("[ _ |=> _ ]")
is "make_map" parametric make_map_transfer
by (unfold make_map_def dom_def, auto)

lemma make_fmap_empty[simp]: "[ {||} |=> f ] = fmempty"
by transfer (simp add: make_map_def)



subsection \<open>Domain\<close>


lemma fmap_add_commute:
  assumes "fmdom A |\<inter>| fmdom B = {||}"
  shows "A ++\<^sub>f B = B ++\<^sub>f A"
using assms including fset.lifting
apply (transfer)
apply (rule ext)
apply (auto simp: dom_def map_add_def split: option.splits)
done

lemma make_fmap_union:
  "[ xs |=> v ] ++\<^sub>f [ ys |=> v] = [ xs |\<union>| ys |=> v ]"
by (transfer, auto simp add: make_map_def map_add_def)

lemma fdom_make_fmap: "fmdom [ ks |=> v ] = ks"
(* FIXME proper transfer proof *)
apply (subst fmdom_def)
apply transfer
apply (auto simp: dom_def make_map_def fset_inverse)
done

subsection \<open>Lookup\<close>

lift_definition
  lookup :: "('k \<rightharpoonup>\<^sub>f 'v) \<Rightarrow> 'k \<Rightarrow> 'v"
is "(\<circ>) the" .

lemma lookup_make_fmap:
  assumes "k \<in> fset ks"
  shows "lookup [ ks |=> v ] k = v"
using assms by (transfer, simp add: make_map_def)

lemma lookup_make_fmap1:
  "lookup [ {|k|} |=> v ] k = v"
by (metis finsert.rep_eq insert_iff lookup_make_fmap)

lemma lookup_union1:
  assumes "k |\<in>| fmdom ys"
  shows "lookup (xs ++\<^sub>f ys) k = lookup ys k"
using assms including fset.lifting
by transfer auto

lemma lookup_union2:
  assumes "k |\<notin>| fmdom ys"
  shows "lookup (xs ++\<^sub>f ys) k = lookup xs k"
using assms including fset.lifting
by transfer (auto simp: map_add_def split: option.splits)

lemma lookup_union3:
  assumes "k |\<notin>| fmdom xs"
  shows "lookup (xs ++\<^sub>f ys) k = lookup ys k"
using assms including fset.lifting
by transfer (auto simp: map_add_def split: option.splits)

end
