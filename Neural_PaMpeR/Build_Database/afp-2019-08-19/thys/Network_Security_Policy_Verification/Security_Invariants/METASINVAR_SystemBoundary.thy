theory METASINVAR_SystemBoundary
imports SINVAR_BLPtrusted_impl
        SINVAR_SubnetsInGW_impl
        "../TopoS_Composition_Theory_impl"
begin


subsubsection \<open>Meta SecurityInvariant: System Boundaries\<close>


datatype system_components = SystemComponent
                           | SystemBoundaryInput
                           | SystemBoundaryOutput
                           | SystemBoundaryInputOutput


fun system_components_to_subnets :: "system_components \<Rightarrow> subnets" where
  "system_components_to_subnets SystemComponent = Member" |
  "system_components_to_subnets SystemBoundaryInput = InboundGateway" |
  "system_components_to_subnets SystemBoundaryOutput = Member" |
  "system_components_to_subnets SystemBoundaryInputOutput = InboundGateway"

fun system_components_to_blp :: "system_components \<Rightarrow> SINVAR_BLPtrusted.node_config" where
  "system_components_to_blp SystemComponent = \<lparr> security_level = 1, trusted = False \<rparr>" |
  "system_components_to_blp SystemBoundaryInput = \<lparr> security_level = 1, trusted = False \<rparr>" |
  "system_components_to_blp SystemBoundaryOutput = \<lparr> security_level = 0, trusted = True \<rparr>" |
  "system_components_to_blp SystemBoundaryInputOutput = \<lparr> security_level = 0, trusted = True \<rparr>"

definition new_meta_system_boundary :: "('v::vertex \<times> system_components) list \<Rightarrow> string \<Rightarrow> ('v SecurityInvariant) list" where 
  "new_meta_system_boundary C description = [
      new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = map_of (map (\<lambda>(v,c). (v, system_components_to_subnets c)) C)
          \<rparr> (description @ '' (ACS)'')
      ,
      new_configured_list_SecurityInvariant SINVAR_LIB_BLPtrusted \<lparr> 
          node_properties = map_of (map (\<lambda>(v,c). (v, system_components_to_blp c)) C)
          \<rparr> (description @ '' (IFS)'')
      ]"


lemma system_components_to_subnets:
      "SINVAR_SubnetsInGW.allowed_subnet_flow
        SINVAR_SubnetsInGW.default_node_properties
        (system_components_to_subnets c) \<longleftrightarrow>
       c = SystemBoundaryInput \<or> c = SystemBoundaryInputOutput"
by(cases c)(simp_all add: SINVAR_SubnetsInGW.default_node_properties_def)

lemma system_components_to_blp:
      "(\<not> trusted SINVAR_BLPtrusted.default_node_properties \<longrightarrow>
       security_level (system_components_to_blp c) \<le> security_level SINVAR_BLPtrusted.default_node_properties)
       \<longleftrightarrow>
       c = SystemBoundaryOutput \<or> c = SystemBoundaryInputOutput"
by(cases c)(simp_all add: SINVAR_BLPtrusted.default_node_properties_def)


lemma "all_security_requirements_fulfilled (new_meta_system_boundary C description) G \<longleftrightarrow>
       (\<forall>(v\<^sub>1, v\<^sub>2) \<in> set (edgesL G). case ((map_of C) v\<^sub>1, (map_of C) v\<^sub>2)
          of 
          \<comment> \<open>No restrictions outside of the component\<close>
             (None, None) \<Rightarrow> True

          \<comment> \<open>no restrictions inside the component\<close>
          |  (Some c1, Some c2) \<Rightarrow> True

          \<comment> \<open>System Boundaries Input\<close>
          |  (None, Some SystemBoundaryInputOutput) \<Rightarrow> True
          |  (None, Some SystemBoundaryInput) \<Rightarrow> True

          \<comment> \<open>System Boundaries Output\<close>
          |  (Some SystemBoundaryOutput, None) \<Rightarrow> True
          |  (Some SystemBoundaryInputOutput, None) \<Rightarrow> True

          \<comment> \<open>everything else is prohibited\<close>
          |  _ \<Rightarrow> False
       )"
apply(simp)
apply(simp add: new_meta_system_boundary_def)
apply(simp add: all_security_requirements_fulfilled_def)
apply(simp add: Let_def)
apply(simp add: SINVAR_LIB_SubnetsInGW_def SINVAR_LIB_BLPtrusted_def)
apply(simp add: SINVAR_SubnetsInGW_impl.NetModel_node_props_def SINVAR_BLPtrusted_impl.NetModel_node_props_def)
apply(rule iffI)
 apply(clarsimp)
 subgoal for a b
 apply(erule_tac x="(a,b)" in ballE)+
  apply(simp_all)
 apply(case_tac "map_of C a")
  apply(case_tac "map_of C b")
   apply(simp_all)
  apply(simp add: map_of_map)
  apply(simp split: system_components.split)
  apply(simp add: system_components_to_subnets)
  apply blast
 apply(case_tac "map_of C b")
  apply(simp add: map_of_map)
  apply(simp split: system_components.split)
  apply(simp add: system_components_to_blp)
  apply blast
 apply(simp add: map_of_map)
 apply(simp split: system_components.split; fail)
 done
apply(intro conjI)
 apply(simp add: map_of_map)
 apply(clarsimp)
 subgoal for a b
 apply(erule_tac x="(a,b)" in ballE)+
  apply(simp_all)
 apply(simp split: option.split_asm system_components.split_asm)
    by(simp_all add: SINVAR_SubnetsInGW.default_node_properties_def)
apply(clarsimp)
subgoal for a b
apply(erule_tac x="(a,b)" in ballE)+
 apply(simp_all)
apply(simp add: map_of_map)
apply(simp split: option.split_asm system_components.split_asm)
  apply(simp add: SINVAR_BLPtrusted.default_node_properties_def; fail)
 apply(rename_tac x, case_tac x, simp_all)+
done
done


value[code] "let nodes = [1,2,3,4,8,9,10];
           sinvars = new_meta_system_boundary
              [(1::int, SystemBoundaryInput),
               (2, SystemComponent),
               (3, SystemBoundaryOutput),
               (4, SystemBoundaryInputOutput)
               ] ''foobar''
       in generate_valid_topology sinvars \<lparr>nodesL = nodes, edgesL = List.product nodes nodes \<rparr>"


end
