section \<open>\isaheader{Map Interface}\<close>
theory Intf_Map
imports Refine_Monadic.Refine_Monadic
begin

consts i_map :: "interface \<Rightarrow> interface \<Rightarrow> interface"

definition [simp]: "op_map_empty \<equiv> Map.empty"
definition op_map_lookup :: "'k \<Rightarrow> ('k\<rightharpoonup>'v) \<rightharpoonup> 'v"
  where [simp]: "op_map_lookup k m \<equiv> m k"
definition [simp]: "op_map_update k v m \<equiv> m(k\<mapsto>v)"
definition [simp]: "op_map_delete k m \<equiv> m |` (-{k})"
definition [simp]: "op_map_restrict P m \<equiv> m |` {k\<in>dom m. P (k, the (m k))}"
definition [simp]: "op_map_isEmpty x \<equiv> x=Map.empty"
definition [simp]: "op_map_isSng x \<equiv> \<exists>k v. x=[k\<mapsto>v]"
definition [simp]: "op_map_ball m P \<equiv> Ball (map_to_set m) P"
definition [simp]: "op_map_bex m P \<equiv> Bex (map_to_set m) P"
definition [simp]: "op_map_size m \<equiv> card (dom m)"
definition [simp]: "op_map_size_abort n m \<equiv> min n (card (dom m))"
definition [simp]: "op_map_sel m P \<equiv> SPEC (\<lambda>(k,v). m k = Some v \<and> P k v)"
definition [simp]: "op_map_pick m \<equiv> SPEC (\<lambda>(k,v). m k = Some v)"

definition [simp]: "op_map_pick_remove m \<equiv> 
  SPEC (\<lambda>((k,v),m'). m k = Some v \<and> m' = m |` (-{k}))"


context begin interpretation autoref_syn .

lemma [autoref_op_pat]:
  "Map.empty \<equiv> op_map_empty"
  "(m::'k\<rightharpoonup>'v) k \<equiv> op_map_lookup$k$m"
  "m(k\<mapsto>v) \<equiv> op_map_update$k$v$m"
  "m |` (-{k}) \<equiv> op_map_delete$k$m"
  "m |` {k\<in>dom m. P (k, the (m k))} \<equiv> op_map_restrict$P$m"

  "m=Map.empty \<equiv> op_map_isEmpty$m"
  "Map.empty=m \<equiv> op_map_isEmpty$m"
  "dom m = {} \<equiv> op_map_isEmpty$m"
  "{} = dom m \<equiv> op_map_isEmpty$m"

  "\<exists>k v. m=[k\<mapsto>v] \<equiv> op_map_isSng$m"
  "\<exists>k v. [k\<mapsto>v]=m \<equiv> op_map_isSng$m"
  "\<exists>k. dom m={k} \<equiv> op_map_isSng$m"
  "\<exists>k. {k} = dom m \<equiv> op_map_isSng$m"
  "1 = card (dom m) \<equiv> op_map_isSng$m"

  "\<And>P. Ball (map_to_set m) P \<equiv> op_map_ball$m$P"
  "\<And>P. Bex (map_to_set m) P \<equiv> op_map_bex$m$P"

  "card (dom m) \<equiv> op_map_size$m"

  "min n (card (dom m)) \<equiv> op_map_size_abort$n$m"
  "min (card (dom m)) n \<equiv> op_map_size_abort$n$m"

  "\<And>P. SPEC (\<lambda>(k,v). m k=Some v \<and> P k v) \<equiv> op_map_sel$m$P"
  "\<And>P. SPEC (\<lambda>(k,v). P k v \<and> m k=Some v) \<equiv> op_map_sel$m$P"

  "\<And>P. SPEC (\<lambda>(k,v). m k = Some v) \<equiv> op_map_pick$m"
  "\<And>P. SPEC (\<lambda>(k,v). (k,v) \<in> map_to_set m) \<equiv> op_map_pick$m"
  by (auto 
    intro!: eq_reflection ext
    simp: restrict_map_def dom_eq_singleton_conv card_Suc_eq map_to_set_def
    dest!: sym[of "Suc 0" "card (dom m)"] sym[of _ "dom m"]
  )

  lemma [autoref_op_pat]: 
    "SPEC (\<lambda>((k,v),m'). m k = Some v \<and> m' = m |` (-{k})) 
      \<equiv> op_map_pick_remove$m"
    by simp

  lemma op_map_pick_remove_alt: "
    do {((k,v),m) \<leftarrow> op_map_pick_remove m; f k v m}
      = (
    do {
      (k,v)\<leftarrow>SPEC (\<lambda>(k,v). m k = Some v); 
       let m=m |` (-{k});
       f k v m
    })"
    unfolding op_map_pick_remove_def
    apply (auto simp: pw_eq_iff refine_pw_simps)
    done

  lemma [autoref_op_pat]: 
    "do {
      (k,v)\<leftarrow>SPEC (\<lambda>(k,v). m k = Some v); 
       let m=m |` (-{k});
       f k v m
    } \<equiv> do {((k,v),m) \<leftarrow> op_map_pick_remove m; f k v m}"
    unfolding op_map_pick_remove_alt .


end

lemma [autoref_itype]:
  "op_map_empty ::\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map"
  "op_map_lookup ::\<^sub>i Ik \<rightarrow>\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i \<langle>Iv\<rangle>\<^sub>ii_option"
  "op_map_update ::\<^sub>i Ik \<rightarrow>\<^sub>i Iv \<rightarrow>\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map"
  "op_map_delete ::\<^sub>i Ik \<rightarrow>\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map"
  "op_map_restrict 
    ::\<^sub>i (\<langle>Ik,Iv\<rangle>\<^sub>ii_prod \<rightarrow>\<^sub>i i_bool) \<rightarrow>\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map"
  "op_map_isEmpty ::\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i i_bool"
  "op_map_isSng ::\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i i_bool"
  "op_map_ball ::\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i (\<langle>Ik,Iv\<rangle>\<^sub>ii_prod \<rightarrow>\<^sub>i i_bool) \<rightarrow>\<^sub>i i_bool"
  "op_map_bex ::\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i (\<langle>Ik,Iv\<rangle>\<^sub>ii_prod \<rightarrow>\<^sub>i i_bool) \<rightarrow>\<^sub>i i_bool"
  "op_map_size ::\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i i_nat"
  "op_map_size_abort ::\<^sub>i i_nat \<rightarrow>\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i i_nat"
  "(++) ::\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map"
  "map_of ::\<^sub>i \<langle>\<langle>Ik,Iv\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map"

  "op_map_sel ::\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i (Ik \<rightarrow>\<^sub>i Iv \<rightarrow>\<^sub>i i_bool) 
    \<rightarrow>\<^sub>i \<langle>\<langle>Ik,Iv\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres"
  "op_map_pick ::\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i \<langle>\<langle>Ik,Iv\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres"
  "op_map_pick_remove 
    ::\<^sub>i \<langle>Ik,Iv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i \<langle>\<langle>\<langle>Ik,Iv\<rangle>\<^sub>ii_prod,\<langle>Ik,Iv\<rangle>\<^sub>ii_map\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres"
  by simp_all

lemma hom_map1[autoref_hom]:
  "CONSTRAINT Map.empty (\<langle>Rk,Rv\<rangle>Rm)"
  "CONSTRAINT map_of (\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel \<rightarrow> \<langle>Rk,Rv\<rangle>Rm)"
  "CONSTRAINT (++) (\<langle>Rk,Rv\<rangle>Rm \<rightarrow> \<langle>Rk,Rv\<rangle>Rm \<rightarrow> \<langle>Rk,Rv\<rangle>Rm)"
  by simp_all

term op_map_restrict
lemma hom_map2[autoref_hom]:
  "CONSTRAINT op_map_lookup (Rk\<rightarrow>\<langle>Rk,Rv\<rangle>Rm\<rightarrow>\<langle>Rv\<rangle>option_rel)"
  "CONSTRAINT op_map_update (Rk\<rightarrow>Rv\<rightarrow>\<langle>Rk,Rv\<rangle>Rm\<rightarrow>\<langle>Rk,Rv\<rangle>Rm)"
  "CONSTRAINT op_map_delete (Rk\<rightarrow>\<langle>Rk,Rv\<rangle>Rm\<rightarrow>\<langle>Rk,Rv\<rangle>Rm)"
  "CONSTRAINT op_map_restrict ((\<langle>Rk,Rv\<rangle>prod_rel \<rightarrow> Id) \<rightarrow> \<langle>Rk,Rv\<rangle>Rm \<rightarrow> \<langle>Rk,Rv\<rangle>Rm)"
  "CONSTRAINT op_map_isEmpty (\<langle>Rk,Rv\<rangle>Rm\<rightarrow>Id)"
  "CONSTRAINT op_map_isSng (\<langle>Rk,Rv\<rangle>Rm\<rightarrow>Id)"
  "CONSTRAINT op_map_ball (\<langle>Rk,Rv\<rangle>Rm\<rightarrow>(\<langle>Rk,Rv\<rangle>prod_rel\<rightarrow>Id)\<rightarrow>Id)"
  "CONSTRAINT op_map_bex (\<langle>Rk,Rv\<rangle>Rm\<rightarrow>(\<langle>Rk,Rv\<rangle>prod_rel\<rightarrow>Id)\<rightarrow>Id)"
  "CONSTRAINT op_map_size (\<langle>Rk,Rv\<rangle>Rm\<rightarrow>Id)"
  "CONSTRAINT op_map_size_abort (Id\<rightarrow>\<langle>Rk,Rv\<rangle>Rm\<rightarrow>Id)"

  "CONSTRAINT op_map_sel (\<langle>Rk,Rv\<rangle>Rm\<rightarrow>(Rk \<rightarrow> Rv \<rightarrow> bool_rel)\<rightarrow>\<langle>Rk\<times>\<^sub>rRv\<rangle>nres_rel)"
  "CONSTRAINT op_map_pick (\<langle>Rk,Rv\<rangle>Rm \<rightarrow> \<langle>Rk\<times>\<^sub>rRv\<rangle>nres_rel)"
  "CONSTRAINT op_map_pick_remove (\<langle>Rk,Rv\<rangle>Rm \<rightarrow> \<langle>(Rk\<times>\<^sub>rRv)\<times>\<^sub>r\<langle>Rk,Rv\<rangle>Rm\<rangle>nres_rel)"
  by simp_all


definition "finite_map_rel R \<equiv> Range R \<subseteq> Collect (finite \<circ> dom)"
lemma finite_map_rel_trigger: "finite_map_rel R \<Longrightarrow> finite_map_rel R" .


declaration \<open>Tagged_Solver.add_triggers 
  "Relators.relator_props_solver" @{thms finite_map_rel_trigger}\<close>

end
