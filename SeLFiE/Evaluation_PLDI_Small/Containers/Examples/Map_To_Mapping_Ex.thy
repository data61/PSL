(*  Title:      Containers/Map_To_Mapping_Ex.thy
    Author:     Andreas Lochbihler, ETH Zurich *)

theory Map_To_Mapping_Ex imports "../Map_To_Mapping" begin

subsection \<open>Test cases for replacing @{typ "'a \<rightharpoonup> 'b"} with @{typ "('a, 'b) mapping"}\<close>

lift_definition mapping_filter :: "('a, 'b) mapping \<Rightarrow> 'a list \<Rightarrow> 'b list" is "List.map_filter" .

lemmas mapping_filter_code [code] = map_filter_simps[containers_identify]

definition test :: "(nat \<Rightarrow> int option) \<Rightarrow> nat list \<Rightarrow> int list"
where
  "test f xs = 
  (if f = Map.empty then [] else List.map_filter (f(2 := None)(1 \<mapsto> -1)) xs)"

lift_definition test' :: "(nat, int) mapping \<Rightarrow> nat list \<Rightarrow> int list" is test .

lemmas [code] = test_def[containers_identify]

export_code test' checking SML


fun iter :: "('a \<Rightarrow> 'a option) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a option"
where
  "iter m 0 x = Some x"
| "iter m (Suc n) x = Option.bind (m x) (iter m n)"

lift_definition iter' :: "('a, 'a) mapping \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a option" is iter .

lemmas [code] = iter.simps[containers_identify]

export_code iter' in SML


definition dom_test :: "bool"
where "dom_test \<longleftrightarrow> (dom [(1 :: int) \<mapsto> ([()] :: unit list)] = {1})"

lemmas [code] = dom_test_def[containers_identify]

ML \<open>val true = @{code dom_test}\<close>

end

