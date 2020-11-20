(*  Title:      Containers/Mapping_Impl.thy
    Author:     Andreas Lochbihler, KIT
                René Thiemann, UIBK *)

theory Mapping_Impl imports 
  RBT_Mapping2
  AssocList
  "HOL-Library.Mapping"
  Set_Impl
  Containers_Generator
begin

section \<open>Different implementations of maps\<close>

code_identifier
  code_module Mapping \<rightharpoonup> (SML) Mapping_Impl
| code_module Mapping_Impl \<rightharpoonup> (SML) Mapping_Impl

subsection \<open>Map implementations\<close>

definition Assoc_List_Mapping :: "('a, 'b) alist \<Rightarrow> ('a, 'b) mapping"
where [simp]: "Assoc_List_Mapping al = Mapping.Mapping (DAList.lookup al)"

definition RBT_Mapping :: "('a :: ccompare, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping"
where [simp]: "RBT_Mapping t = Mapping.Mapping (RBT_Mapping2.lookup t)"

code_datatype Assoc_List_Mapping RBT_Mapping Mapping

subsection \<open>Map operations\<close>

declare [[code drop: Mapping.lookup]]

lemma lookup_Mapping_code [code]:
  "Mapping.lookup (Assoc_List_Mapping al) = DAList.lookup al"
  "Mapping.lookup (RBT_Mapping t) = RBT_Mapping2.lookup t"
by(simp_all)(transfer, rule)+

declare [[code drop: Mapping.is_empty]]

lemma is_empty_transfer [transfer_rule]:
  includes lifting_syntax
  shows "(pcr_mapping (=) (=) ===> (=)) (\<lambda>m. m = Map.empty) Mapping.is_empty"
unfolding mapping.pcr_cr_eq
apply(rule rel_funI)
apply(case_tac y)
apply(simp add: Mapping.is_empty_def cr_mapping_def Mapping_inverse Mapping.keys.rep_eq)
done

lemma is_empty_Mapping [code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.is_empty (Assoc_List_Mapping al) \<longleftrightarrow> al = DAList.empty"
  "Mapping.is_empty (RBT_Mapping t) \<longleftrightarrow>
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''is_empty RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.is_empty (RBT_Mapping t))
                     | Some _ \<Rightarrow> RBT_Mapping2.is_empty t)"
apply(simp_all split: option.split)
 apply(transfer, case_tac al, simp_all)
apply(transfer, simp)
done

declare [[code drop: Mapping.update]]

lemma update_Mapping [code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.update k v (Mapping m) = Mapping (m(k \<mapsto> v))"
  "Mapping.update k v (Assoc_List_Mapping al) = Assoc_List_Mapping (DAList.update k v al)"
  "Mapping.update k v (RBT_Mapping t) =
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''update RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.update k v (RBT_Mapping t))
                     | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.insert k v t))" (is ?RBT)
by(simp_all split: option.split)(transfer, simp)+

declare [[code drop: Mapping.delete]]

lemma delete_Mapping [code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.delete k (Mapping m) = Mapping (m(k := None))"
  "Mapping.delete k (Assoc_List_Mapping al) = Assoc_List_Mapping (AssocList.delete k al)"
  "Mapping.delete k (RBT_Mapping t) = 
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''delete RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.delete k (RBT_Mapping t))
                     | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.delete k t))"
by(simp_all split: option.split)(transfer, simp)+

declare [[code drop: Mapping.keys]]

theorem rbt_comp_lookup_map_const: "rbt_comp_lookup c (RBT_Impl.map (\<lambda>_. f) t) = map_option f \<circ> rbt_comp_lookup c t"
by(induct t)(auto simp: fun_eq_iff split: order.split)

lemma keys_Mapping [code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.keys (Mapping m) = Collect (\<lambda>k. m k \<noteq> None)" (is "?Mapping")
  "Mapping.keys (Assoc_List_Mapping al) = AssocList.keys al" (is "?Assoc_List")
  "Mapping.keys (RBT_Mapping t) = RBT_set (RBT_Mapping2.map (\<lambda>_ _. ()) t)" (is "?RBT")
proof -
  show ?Mapping by transfer auto
  show ?Assoc_List by simp(transfer, auto intro: rev_image_eqI)
  show ?RBT
    by(simp add: RBT_set_def, transfer, auto simp add: rbt_comp_lookup_map_const o_def)
qed

declare [[code drop: Mapping.size]]

lemma Mapping_size_transfer [transfer_rule]:
  includes lifting_syntax
  shows "(pcr_mapping (=) (=) ===> (=)) (card \<circ> dom) Mapping.size"
apply(rule rel_funI)
apply(case_tac y)
apply(simp add: Mapping.size_def Mapping.keys.rep_eq Mapping_inverse mapping.pcr_cr_eq cr_mapping_def)
done

lemma size_Mapping [code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.size (Assoc_List_Mapping al) = size al"
  "Mapping.size (RBT_Mapping t) =
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''size RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.size (RBT_Mapping t))
                     | Some _ \<Rightarrow> length (RBT_Mapping2.entries t))"
apply(simp_all split: option.split)
apply(transfer, simp add: dom_map_of_conv_image_fst set_map[symmetric] distinct_card del: set_map)
apply transfer
apply(clarsimp simp add: size_eq_card_dom_lookup)
apply(simp add: linorder.rbt_lookup_keys[OF ID_ccompare] ord.is_rbt_rbt_sorted RBT_Impl.keys_def distinct_card linorder.distinct_entries[OF ID_ccompare] del: set_map)
done


declare [[code drop: Mapping.tabulate]]
declare tabulate_fold [code]

datatype mapping_impl = Mapping_IMPL
declare
  mapping_impl.eq.simps [code del]
  mapping_impl.rec [code del]
  mapping_impl.case [code del]

lemma [code]:
  fixes x :: mapping_impl
  shows "size x = 0"
  and "size_mapping_impl x = 0"
by(case_tac [!] x) simp_all

definition mapping_Choose :: mapping_impl where [simp]: "mapping_Choose = Mapping_IMPL"
definition mapping_Assoc_List :: mapping_impl where [simp]: "mapping_Assoc_List = Mapping_IMPL"
definition mapping_RBT :: mapping_impl where [simp]: "mapping_RBT = Mapping_IMPL"
definition mapping_Mapping :: mapping_impl where [simp]: "mapping_Mapping = Mapping_IMPL"

code_datatype mapping_Choose mapping_Assoc_List mapping_RBT mapping_Mapping

definition mapping_empty_choose :: "('a, 'b) mapping" 
where [simp]: "mapping_empty_choose = Mapping.empty"

lemma mapping_empty_choose_code [code]:
  "(mapping_empty_choose :: ('a :: ccompare, 'b) mapping) =
   (case ID CCOMPARE('a) of Some _  \<Rightarrow> RBT_Mapping RBT_Mapping2.empty
    | None \<Rightarrow> Assoc_List_Mapping DAList.empty)"
by(auto split: option.split simp add: DAList.lookup_empty[abs_def] Mapping.empty_def)

definition mapping_impl_choose2 :: "mapping_impl \<Rightarrow> mapping_impl \<Rightarrow> mapping_impl"
where [simp]: "mapping_impl_choose2 = (\<lambda>_ _. Mapping_IMPL)"

lemma mapping_impl_choose2_code [code]:
  "mapping_impl_choose2 x y = mapping_Choose"
  "mapping_impl_choose2 mapping_Mapping mapping_Mapping = mapping_Mapping"
  "mapping_impl_choose2 mapping_Assoc_List mapping_Assoc_List = mapping_Assoc_List"
  "mapping_impl_choose2 mapping_RBT mapping_RBT = mapping_RBT"
by(simp_all)

definition mapping_empty :: "mapping_impl \<Rightarrow> ('a, 'b) mapping"
where [simp]: "mapping_empty = (\<lambda>_. Mapping.empty)"

lemma mapping_empty_code [code]:
  "mapping_empty mapping_Choose = mapping_empty_choose"
  "mapping_empty mapping_Mapping = Mapping (\<lambda>_. None)"
  "mapping_empty mapping_Assoc_List = Assoc_List_Mapping DAList.empty"
  "mapping_empty mapping_RBT = RBT_Mapping RBT_Mapping2.empty"
by(simp_all add: Mapping.empty_def DAList.lookup_empty[abs_def])

subsection \<open>Type classes\<close>

class mapping_impl = 
  fixes mapping_impl :: "('a, mapping_impl) phantom"

syntax (input)
  "_MAPPING_IMPL" :: "type => logic"  ("(1MAPPING'_IMPL/(1'(_')))")

parse_translation \<open>
let
  fun mapping_impl_tr [ty] =
     (Syntax.const @{syntax_const "_constrain"} $ Syntax.const @{const_syntax "mapping_impl"} $
       (Syntax.const @{type_syntax phantom} $ ty $ Syntax.const @{type_syntax mapping_impl}))
    | mapping_impl_tr ts = raise TERM ("mapping_impl_tr", ts);
in [(@{syntax_const "_MAPPING_IMPL"}, K mapping_impl_tr)] end
\<close>

declare [[code drop: Mapping.empty]]

lemma Mapping_empty_code [code, code_unfold]: 
  "(Mapping.empty :: ('a :: mapping_impl, 'b) mapping) =
   mapping_empty (of_phantom MAPPING_IMPL('a))"
by simp

subsection \<open>Generator for the @{class mapping_impl}-class\<close>

text \<open>
This generator registers itself at the derive-manager for the classes @{class mapping_impl}.
Here, one can choose
the desired implementation via the parameter. 

\begin{itemize}
\item \texttt{instantiation type :: (type,\ldots,type) (rbt,assoclist,mapping,choose, or arbitrary constant name) mapping-impl}
\end{itemize}
\<close>


text \<open>
This generator can be used for arbitrary types, not just datatypes. 
\<close>

ML_file \<open>mapping_impl_generator.ML\<close> 

derive (assoclist) mapping_impl unit bool
derive (rbt) mapping_impl nat
derive (mapping_RBT) mapping_impl int (* shows usage of constant names *)
derive (assoclist) mapping_impl Enum.finite_1 Enum.finite_2 Enum.finite_3
derive (rbt) mapping_impl integer natural
derive (rbt) mapping_impl char

instantiation sum :: (mapping_impl, mapping_impl) mapping_impl begin
definition "MAPPING_IMPL('a + 'b) = Phantom('a + 'b) 
  (mapping_impl_choose2 (of_phantom MAPPING_IMPL('a)) (of_phantom MAPPING_IMPL('b)))"
instance ..
end

instantiation prod :: (mapping_impl, mapping_impl) mapping_impl begin
definition "MAPPING_IMPL('a * 'b) = Phantom('a * 'b) 
  (mapping_impl_choose2 (of_phantom MAPPING_IMPL('a)) (of_phantom MAPPING_IMPL('b)))"
instance ..
end

derive (choose) mapping_impl list
derive (rbt) mapping_impl String.literal

instantiation option :: (mapping_impl) mapping_impl begin
definition "MAPPING_IMPL('a option) = Phantom('a option) (of_phantom MAPPING_IMPL('a))"
instance ..
end

derive (choose) mapping_impl set

instantiation phantom :: (type, mapping_impl) mapping_impl begin
definition "MAPPING_IMPL(('a, 'b) phantom) = Phantom (('a, 'b) phantom) 
  (of_phantom MAPPING_IMPL('b))"
instance ..
end

end
