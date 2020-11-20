section \<open>Set Interface\<close>
theory IICF_Set
imports "../../Sepref"
begin

subsection \<open>Operations\<close>
definition [simp]: "op_set_is_empty s \<equiv> s={}"
lemma op_set_is_empty_param[param]: "(op_set_is_empty,op_set_is_empty)\<in>\<langle>A\<rangle>set_rel \<rightarrow> bool_rel" by auto

context 
  notes [simp] = IS_LEFT_UNIQUE_def (* Argh, the set parametricity lemmas use single_valued (K\<inverse>) here. *)
begin

sepref_decl_op set_empty: "{}" :: "\<langle>A\<rangle>set_rel" .
sepref_decl_op (no_def) set_is_empty: op_set_is_empty :: "\<langle>A\<rangle>set_rel \<rightarrow> bool_rel" .
sepref_decl_op set_member: "(\<in>)" :: "A \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> bool_rel" where "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_insert: Set.insert :: "A \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" where "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_delete: "\<lambda>x s. s - {x}" :: "A \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" 
  where "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_union: "(\<union>)" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" .
sepref_decl_op set_inter: "(\<inter>)" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" where "IS_LEFT_UNIQUE A"  "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_diff: "(-) ::_ set \<Rightarrow> _" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel" where "IS_LEFT_UNIQUE A"  "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_subseteq: "(\<subseteq>)" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> bool_rel" where "IS_LEFT_UNIQUE A"  "IS_RIGHT_UNIQUE A" .
sepref_decl_op set_subset: "(\<subset>)" :: "\<langle>A\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> bool_rel" where "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A" .

(* TODO: We may want different operations here: pick with predicate returning option,
  pick with remove, ... *)    
sepref_decl_op set_pick: "RES" :: "[\<lambda>s. s\<noteq>{}]\<^sub>f \<langle>K\<rangle>set_rel \<rightarrow> K" by auto

end

(* TODO: Set-pick. Move from where it is already defined! *)

subsection \<open>Patterns\<close>
lemma pat_set[def_pat_rules]:
  "{} \<equiv> op_set_empty"
  "(\<in>) \<equiv> op_set_member"    
  "Set.insert \<equiv> op_set_insert"
  "(\<union>) \<equiv> op_set_union"
  "(\<inter>) \<equiv> op_set_inter"
  "(-) \<equiv> op_set_diff"
  "(\<subseteq>) \<equiv> op_set_subseteq"
  "(\<subset>) \<equiv> op_set_subset"
  by (auto intro!: eq_reflection)
  
lemma pat_set2[pat_rules]: 
  "(=) $s${} \<equiv> op_set_is_empty$s"
  "(=) ${}$s \<equiv> op_set_is_empty$s"

  "(-) $s$(Set.insert$x${}) \<equiv> op_set_delete$x$s"
  "SPEC$(\<lambda>\<^sub>2x. (\<in>) $x$s) \<equiv> op_set_pick s"
  "RES$s \<equiv> op_set_pick s"
  by (auto intro!: eq_reflection)


locale set_custom_empty = 
  fixes empty and op_custom_empty :: "'a set"
  assumes op_custom_empty_def: "op_custom_empty = op_set_empty"
begin
  sepref_register op_custom_empty :: "'ax set"

  lemma fold_custom_empty:
    "{} = op_custom_empty"
    "op_set_empty = op_custom_empty"
    "mop_set_empty = RETURN op_custom_empty"
    unfolding op_custom_empty_def by simp_all
end

end

