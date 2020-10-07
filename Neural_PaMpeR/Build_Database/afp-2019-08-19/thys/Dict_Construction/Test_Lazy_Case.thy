subsection \<open>Interaction with \<open>Lazy_Case\<close>\<close>

theory Test_Lazy_Case
imports
  Dict_Construction
  Lazy_Case.Lazy_Case
  Show.Show_Instances
begin

datatype 'a tree = Node | Fork 'a "'a tree list"

lemma map_tree[code]:
  "map_tree f t = (case t of Node \<Rightarrow> Node | Fork x ts \<Rightarrow> Fork (f x) (map (map_tree f) ts))"
by (induction t) auto

experiment begin

(* FIXME proper qualified path *)
text \<open>
  Dictionary construction of @{const map_tree} requires the [@{attribute fundef_cong}] rule of
  @{const Test_Lazy_Case.tree.case_lazy}.
\<close>

declassify valid: map_tree
thm valid

lemma "Test__Lazy__Case_tree_map__tree = map_tree" by (fact valid)

end


definition i :: "(unit \<times> (bool list \<times> string \<times> nat option) list) option \<Rightarrow> string" where
"i = show"

experiment begin

text \<open>This currently requires @{theory Lazy_Case.Lazy_Case} because of @{const divmod_nat}.\<close>

(* FIXME get rid of Lazy_Case dependency *)
declassify valid: i
thm valid

lemma "Test__Lazy__Case_i = i" by (fact valid)

end

end