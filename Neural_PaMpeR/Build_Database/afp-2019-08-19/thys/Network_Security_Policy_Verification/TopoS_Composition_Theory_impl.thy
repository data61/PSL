theory TopoS_Composition_Theory_impl
imports TopoS_Interface_impl TopoS_Composition_Theory
begin

section\<open>Composition Theory -- List Implementation\<close>

text\<open>Several invariants may apply to one policy.\<close>


(*the packed network model record from the list implementation*)
term "X::('v::vertex, 'a) TopoS_packed"


subsection\<open>Generating instantiated (configured) network security invariants\<close>

  \<comment> \<open>a configured network security invariant in list implementaion\<close>
  (*very minimal version, no eval, ...*)
  record ('v) SecurityInvariant =
    implc_type :: string
    implc_description :: string
    implc_sinvar ::"('v) list_graph \<Rightarrow> bool"
    implc_offending_flows ::"('v) list_graph \<Rightarrow> ('v \<times> 'v) list list"
    implc_isIFS :: "bool"

  text\<open>Test if this definition is compliant with the formal definition on sets.\<close>
  definition SecurityInvariant_complies_formal_def :: 
    "('v) SecurityInvariant \<Rightarrow> 'v TopoS_Composition_Theory.SecurityInvariant_configured \<Rightarrow> bool" where
    "SecurityInvariant_complies_formal_def impl spec \<equiv> 
      (\<forall> G. wf_list_graph G \<longrightarrow> implc_sinvar impl G = c_sinvar spec (list_graph_to_graph G)) \<and>
      (\<forall> G. wf_list_graph G \<longrightarrow> set`set (implc_offending_flows impl G) = c_offending_flows spec (list_graph_to_graph G)) \<and>
      (implc_isIFS impl = c_isIFS spec)"
    

  fun new_configured_list_SecurityInvariant :: 
    "('v::vertex, 'a) TopoS_packed \<Rightarrow> ('v::vertex, 'a) TopoS_Params \<Rightarrow> string \<Rightarrow>
        ('v SecurityInvariant)" where 
      "new_configured_list_SecurityInvariant m C description = 
        (let nP = nm_node_props m C in
         \<lparr> 
            implc_type = nm_name m,
            implc_description = description,
            implc_sinvar = (\<lambda>G. (nm_sinvar m) G nP),
            implc_offending_flows = (\<lambda>G. (nm_offending_flows m) G nP),
            implc_isIFS = nm_receiver_violation m
          \<rparr>)"

  text\<open>the @{term TopoS_Composition_Theory.new_configured_SecurityInvariant} must give a
         result if we have the SecurityInvariant modelLibrary\<close>
  lemma TopoS_modelLibrary_yields_new_configured_SecurityInvariant:
    assumes NetModelLib: "TopoS_modelLibrary m sinvar_spec"
    and     nPdef:       "nP = nm_node_props m C"
    and formalSpec:      "Spec = \<lparr> 
                              c_sinvar = (\<lambda>G. sinvar_spec G nP),
                              c_offending_flows = (\<lambda>G. SecurityInvariant_withOffendingFlows.set_offending_flows sinvar_spec G nP),
                              c_isIFS = nm_receiver_violation m
                            \<rparr>"
    shows "new_configured_SecurityInvariant (sinvar_spec, nm_default m, nm_receiver_violation m, nP) = Some Spec"
    proof -
      from NetModelLib have NetModel: "SecurityInvariant sinvar_spec (nm_default m) (nm_receiver_violation m)"
        by(simp add: TopoS_modelLibrary_def TopoS_List_Impl_def)

      have Spec: "\<lparr>c_sinvar = \<lambda>G. sinvar_spec G nP,
             c_offending_flows = \<lambda>G. SecurityInvariant_withOffendingFlows.set_offending_flows sinvar_spec G nP,
             c_isIFS = nm_receiver_violation m\<rparr> = Spec"
      by(simp add: formalSpec)
      show ?thesis
        unfolding new_configured_SecurityInvariant.simps
        by(simp add: NetModel Spec)
    qed
    thm TopoS_modelLibrary_yields_new_configured_SecurityInvariant[simplified] (*todo fold in Spec*)


  (* The new_* functions comply, i.e. we can instance network security models that are executable. *)
  lemma new_configured_list_SecurityInvariant_complies:
    assumes NetModelLib: "TopoS_modelLibrary m sinvar_spec"
    and     nPdef:       "nP = nm_node_props m C"
    and formalSpec:      "Spec = new_configured_SecurityInvariant (sinvar_spec, nm_default m, nm_receiver_violation m, nP)"
    and implSpec:        "Impl = new_configured_list_SecurityInvariant m C description"
    shows "SecurityInvariant_complies_formal_def Impl (the Spec)"
    proof -
      from TopoS_modelLibrary_yields_new_configured_SecurityInvariant[OF NetModelLib nPdef]
      have SpecUnfolded: "new_configured_SecurityInvariant (sinvar_spec, nm_default m, nm_receiver_violation m, nP) =
        Some \<lparr>c_sinvar = \<lambda>G. sinvar_spec G nP,
             c_offending_flows = \<lambda>G. SecurityInvariant_withOffendingFlows.set_offending_flows sinvar_spec G nP,
             c_isIFS = nm_receiver_violation m\<rparr>" by simp
      
      from NetModelLib show ?thesis
        apply(simp add: SpecUnfolded formalSpec implSpec Let_def)
        apply(simp add: SecurityInvariant_complies_formal_def_def)
        apply(simp add: TopoS_modelLibrary_def TopoS_List_Impl_def)
        apply(simp add: nPdef)
        done
    qed


  corollary new_configured_list_SecurityInvariant_complies':
    "\<lbrakk> TopoS_modelLibrary m sinvar_spec \<rbrakk> \<Longrightarrow> 
    SecurityInvariant_complies_formal_def (new_configured_list_SecurityInvariant m C description)
      (the (new_configured_SecurityInvariant (sinvar_spec, nm_default m, nm_receiver_violation m, nm_node_props m C)))"
    by(blast dest: new_configured_list_SecurityInvariant_complies)

  \<comment> \<open>From\<close>
  thm new_configured_SecurityInvariant_sound
  \<comment> \<open>we get that @{const new_configured_list_SecurityInvariant} has all the necessary properties (modulo @{const SecurityInvariant_complies_formal_def})\<close>

subsection\<open>About security invariants\<close>

   text\<open>specification and implementation comply.\<close>
   type_synonym 'v security_models_spec_impl="('v SecurityInvariant \<times> 'v TopoS_Composition_Theory.SecurityInvariant_configured) list"
   
   definition get_spec :: "'v security_models_spec_impl \<Rightarrow> ('v TopoS_Composition_Theory.SecurityInvariant_configured) list" where
    "get_spec M \<equiv> [snd m. m \<leftarrow> M]"
   definition get_impl :: "'v security_models_spec_impl \<Rightarrow> ('v SecurityInvariant) list" where
    "get_impl M \<equiv> [fst m. m \<leftarrow> M]"

subsection\<open>Calculating offending flows\<close>
  fun implc_get_offending_flows :: "('v) SecurityInvariant list \<Rightarrow> 'v list_graph \<Rightarrow> (('v \<times> 'v) list list)" where
    "implc_get_offending_flows [] G = []"  |
    "implc_get_offending_flows (m#Ms) G = (implc_offending_flows m G)@(implc_get_offending_flows Ms G)"  
  

  lemma implc_get_offending_flows_fold: 
    "implc_get_offending_flows M G = fold (\<lambda>m accu. accu@(implc_offending_flows m G)) M []"
    proof- 
    { fix accu
      have "accu@(implc_get_offending_flows M G) = fold (\<lambda>m accu. accu@(implc_offending_flows m G)) M accu"
      apply(induction M arbitrary: accu)
       apply(simp_all)
      by(metis append_eq_appendI) }
    from this[where accu2="[]"] show ?thesis by simp
  qed

  lemma implc_get_offending_flows_Un: "set`set (implc_get_offending_flows M G) = (\<Union>m\<in>set M. set`set (implc_offending_flows m G))"
    apply(induction M)
     apply(simp_all)
    by (metis image_Un)


  lemma implc_get_offending_flows_map_concat: "(implc_get_offending_flows M G) = concat [implc_offending_flows m G. m \<leftarrow> M]"
    apply(induction M)
     by(simp_all)

  
  theorem implc_get_offending_flows_complies:
    assumes a1: "\<forall> (m_impl, m_spec) \<in> set M. SecurityInvariant_complies_formal_def m_impl m_spec"
    and     a2: "wf_list_graph G"
    shows   "set`set (implc_get_offending_flows (get_impl M) G) = (get_offending_flows (get_spec M) (list_graph_to_graph G))"
    proof -
      from a1 have "\<forall> (m_impl, m_spec) \<in> set M. set ` set (implc_offending_flows m_impl G) = c_offending_flows m_spec (list_graph_to_graph G)"
        apply(simp add: SecurityInvariant_complies_formal_def_def)
        using a2 by blast
      hence "\<forall> m \<in> set M. set ` set (implc_offending_flows (fst m) G) = c_offending_flows (snd m) (list_graph_to_graph G)" by fastforce
      thus ?thesis
        by(simp add: get_impl_def get_spec_def implc_get_offending_flows_Un get_offending_flows_def)
   qed



subsection\<open>Accessors\<close>
  definition get_IFS :: "'v SecurityInvariant list \<Rightarrow> 'v SecurityInvariant list" where
    "get_IFS M \<equiv> [m \<leftarrow> M. implc_isIFS m]"
  definition get_ACS :: "'v SecurityInvariant list \<Rightarrow> 'v SecurityInvariant list" where
    "get_ACS M \<equiv> [m \<leftarrow> M. \<not> implc_isIFS m]"

  lemma get_IFS_get_ACS_complies:
  assumes a: "\<forall> (m_impl, m_spec) \<in> set M. SecurityInvariant_complies_formal_def m_impl m_spec"
    shows "\<forall> (m_impl, m_spec) \<in> set (zip (get_IFS (get_impl M)) (TopoS_Composition_Theory.get_IFS (get_spec M))).
      SecurityInvariant_complies_formal_def m_impl m_spec"
    and "\<forall> (m_impl, m_spec) \<in> set (zip (get_ACS (get_impl M)) (TopoS_Composition_Theory.get_ACS (get_spec M))).
      SecurityInvariant_complies_formal_def m_impl m_spec"
    proof -
      from a have "\<forall> (m_impl, m_spec) \<in> set M. implc_isIFS m_impl = c_isIFS m_spec"
        apply(simp add: SecurityInvariant_complies_formal_def_def) by fastforce
      hence set_zip_IFS: "set (zip (filter implc_isIFS (get_impl M)) (filter c_isIFS (get_spec M))) \<subseteq> set M"
        apply(simp add: get_impl_def get_spec_def)
        apply(induction M)
         apply(simp_all)
        by force
      from set_zip_IFS a show "\<forall> (m_impl, m_spec) \<in> set (zip (get_IFS (get_impl M)) (TopoS_Composition_Theory.get_IFS (get_spec M))).
          SecurityInvariant_complies_formal_def m_impl m_spec"
        apply(simp add: get_IFS_def get_ACS_def
          TopoS_Composition_Theory.get_IFS_def TopoS_Composition_Theory.get_ACS_def) by blast
      next
      from a have "\<forall> (m_impl, m_spec) \<in> set M. implc_isIFS m_impl = c_isIFS m_spec"
        apply(simp add: SecurityInvariant_complies_formal_def_def) by fastforce
      hence set_zip_ACS: "set (zip [m\<leftarrow>get_impl M . \<not> implc_isIFS m] [m\<leftarrow>get_spec M . \<not> c_isIFS m]) \<subseteq> set M"
        apply(simp add: get_impl_def get_spec_def)
        apply(induction M)
         apply(simp_all)
        by force
      from this a show "\<forall> (m_impl, m_spec) \<in> set (zip (get_ACS (get_impl M)) (TopoS_Composition_Theory.get_ACS (get_spec M))).
        SecurityInvariant_complies_formal_def m_impl m_spec"
        apply(simp add: get_IFS_def get_ACS_def
          TopoS_Composition_Theory.get_IFS_def TopoS_Composition_Theory.get_ACS_def) by fast
     qed



   lemma get_IFS_get_ACS_select_simps:
    assumes a1: "\<forall> (m_impl, m_spec) \<in> set M. SecurityInvariant_complies_formal_def m_impl m_spec"
    shows "\<forall> (m_impl, m_spec) \<in> set (zip (get_IFS (get_impl M)) (TopoS_Composition_Theory.get_IFS (get_spec M))). SecurityInvariant_complies_formal_def m_impl m_spec" (is "\<forall> (m_impl, m_spec) \<in> set ?zippedIFS. SecurityInvariant_complies_formal_def m_impl m_spec")
    and   "(get_impl (zip (TopoS_Composition_Theory_impl.get_IFS (get_impl M)) (TopoS_Composition_Theory.get_IFS (get_spec M)))) = TopoS_Composition_Theory_impl.get_IFS (get_impl M)"
    and   "(get_spec (zip (TopoS_Composition_Theory_impl.get_IFS (get_impl M)) (TopoS_Composition_Theory.get_IFS (get_spec M)))) = TopoS_Composition_Theory.get_IFS (get_spec M)"
    and   "\<forall> (m_impl, m_spec) \<in> set (zip (get_ACS (get_impl M)) (TopoS_Composition_Theory.get_ACS (get_spec M))). SecurityInvariant_complies_formal_def m_impl m_spec" (is "\<forall> (m_impl, m_spec) \<in> set ?zippedACS. SecurityInvariant_complies_formal_def m_impl m_spec")
    and   "(get_impl (zip (TopoS_Composition_Theory_impl.get_ACS (get_impl M)) (TopoS_Composition_Theory.get_ACS (get_spec M)))) = TopoS_Composition_Theory_impl.get_ACS (get_impl M)"
    and   "(get_spec (zip (TopoS_Composition_Theory_impl.get_ACS (get_impl M)) (TopoS_Composition_Theory.get_ACS (get_spec M)))) = TopoS_Composition_Theory.get_ACS (get_spec M)"
    proof -
        from get_IFS_get_ACS_complies(1)[OF a1]
        show "\<forall> (m_impl, m_spec) \<in> set (?zippedIFS). SecurityInvariant_complies_formal_def m_impl m_spec" by simp
      next
        from a1 show "(get_impl ?zippedIFS) = TopoS_Composition_Theory_impl.get_IFS (get_impl M)"
          apply(simp add: TopoS_Composition_Theory_impl.get_IFS_def get_spec_def get_impl_def TopoS_Composition_Theory.get_IFS_def)
          apply(induction M)
           apply(simp)
          apply(simp)
          apply(rule conjI)
           apply(clarify)
           using SecurityInvariant_complies_formal_def_def apply (auto)[1]
          apply(clarify)
          using SecurityInvariant_complies_formal_def_def apply (auto)[1]
          done
      next
        from a1 show "(get_spec ?zippedIFS) = TopoS_Composition_Theory.get_IFS (get_spec M)"
          apply(simp add: TopoS_Composition_Theory_impl.get_IFS_def get_spec_def get_impl_def TopoS_Composition_Theory.get_IFS_def)
          apply(induction M)
           apply(simp)
          apply(simp)
          apply(rule conjI)
           apply(clarify)
           using SecurityInvariant_complies_formal_def_def apply (auto)[1]
          apply(clarify)
          using SecurityInvariant_complies_formal_def_def apply (auto)[1]
          done
      next
        from get_IFS_get_ACS_complies(2)[OF a1]
        show "\<forall> (m_impl, m_spec) \<in> set (?zippedACS). SecurityInvariant_complies_formal_def m_impl m_spec" by simp
      next
        from a1 show "(get_impl ?zippedACS) = TopoS_Composition_Theory_impl.get_ACS (get_impl M)"
          apply(simp add: TopoS_Composition_Theory_impl.get_ACS_def get_spec_def get_impl_def TopoS_Composition_Theory.get_ACS_def)
          apply(induction M)
           apply(simp)
          apply(simp)
          apply(rule conjI)
           apply(clarify)
           using SecurityInvariant_complies_formal_def_def apply (auto)[1]
          apply(clarify)
          using SecurityInvariant_complies_formal_def_def apply (auto)[1]
          done
      next
        from a1 show "(get_spec ?zippedACS) = TopoS_Composition_Theory.get_ACS (get_spec M)"
          apply(simp add: TopoS_Composition_Theory_impl.get_ACS_def get_spec_def get_impl_def TopoS_Composition_Theory.get_ACS_def)
          apply(induction M)
           apply(simp)
          apply(simp)
          apply(rule conjI)
           apply(clarify)
           using SecurityInvariant_complies_formal_def_def apply (auto)[1]
          apply(clarify)
          using SecurityInvariant_complies_formal_def_def apply (auto)[1]
          done
      qed 
 
   thm get_IFS_get_ACS_select_simps

subsection\<open>All security requirements fulfilled\<close>
   definition all_security_requirements_fulfilled :: "'v SecurityInvariant list \<Rightarrow> 'v list_graph \<Rightarrow> bool" where
      "all_security_requirements_fulfilled M G \<equiv> \<forall>m \<in> set M. (implc_sinvar m) G"

  lemma all_security_requirements_fulfilled_complies:
    "\<lbrakk> \<forall> (m_impl, m_spec) \<in> set M. SecurityInvariant_complies_formal_def m_impl m_spec; 
       wf_list_graph (G::('v::vertex) list_graph) \<rbrakk> \<Longrightarrow>
    all_security_requirements_fulfilled (get_impl M) G \<longleftrightarrow> TopoS_Composition_Theory.all_security_requirements_fulfilled (get_spec M) (list_graph_to_graph G)"
    apply(simp add: all_security_requirements_fulfilled_def TopoS_Composition_Theory.all_security_requirements_fulfilled_def)
    apply(simp add: get_impl_def get_spec_def)
    using SecurityInvariant_complies_formal_def_def by fastforce

subsection\<open>generate valid topology\<close>
  value "concat [[1::int,2,3], [4,6,5]]"

  fun generate_valid_topology :: "'v SecurityInvariant list \<Rightarrow> 'v list_graph \<Rightarrow> ('v list_graph)" where
    "generate_valid_topology M G = delete_edges G (concat (implc_get_offending_flows M G))"


  lemma generate_valid_topology_complies:
    "\<lbrakk> \<forall> (m_impl, m_spec) \<in> set M. SecurityInvariant_complies_formal_def m_impl m_spec;
       wf_list_graph (G::('v list_graph)) \<rbrakk> \<Longrightarrow> 
       list_graph_to_graph (generate_valid_topology (get_impl M) G) = 
       TopoS_Composition_Theory.generate_valid_topology (get_spec M) (list_graph_to_graph G)"
    apply (subst generate_valid_topology_def_alt)
    apply (drule(1) implc_get_offending_flows_complies)
    apply (simp add: delete_edges_correct [symmetric])
    done



subsection\<open>generate valid topology\<close>
  text\<open>tuned for invariants where we don't want to calculate all offending flows\<close>

  text\<open>Theoretic foundations: The algorithm @{const generate_valid_topology_SOME} picks
        ONE offending flow non-deterministically.
        This is sound: @{thm generate_valid_topology_SOME_sound}.
        However, this non-deterministic choice is hard to implement. 
        To pick one offending flow deterministically, we have implemented @{const minimalize_offending_overapprox}.
        It gives back one offending flow:
          @{thm SecurityInvariant_preliminaries.minimalize_offending_overapprox_gives_back_an_offending_flow}
        The good thing about this function is, that it does not need to construct the complete
        @{const SecurityInvariant_withOffendingFlows.set_offending_flows}. Therefore, 
        it can be used for security invariants which may have an exponential number of offending flows. 
        The corresponding algorithm that uses this function is @{const TopoS_Composition_Theory.generate_valid_topology_some}.
        It is also sound: @{thm generate_valid_topology_some_sound}.\<close>

  fun generate_valid_topology_some :: "'v SecurityInvariant list \<Rightarrow> 'v list_graph \<Rightarrow> ('v list_graph)" where
    "generate_valid_topology_some [] G = G" |
    "generate_valid_topology_some (m#Ms) G = (if implc_sinvar m G
      then generate_valid_topology_some Ms G
      else delete_edges (generate_valid_topology_some Ms G) (minimalize_offending_overapprox (implc_sinvar m) (edgesL G) [] G)
      )"

  thm TopoS_Composition_Theory.generate_valid_topology_some_sound

  lemma generate_valid_topology_some_complies:
    "\<lbrakk> \<forall> (m_impl, m_spec) \<in> set M. SecurityInvariant_complies_formal_def m_impl m_spec;
       wf_list_graph (G::('v::vertex list_graph)) \<rbrakk> \<Longrightarrow> 
       list_graph_to_graph (generate_valid_topology_some (get_impl M) G) = 
       TopoS_Composition_Theory.generate_valid_topology_some (get_spec M) (edgesL G) (list_graph_to_graph G)"
    proof(induction M)
    case Nil thus ?case by(simp add: get_spec_def get_impl_def)
    next
    case (Cons m M)
      obtain m_impl m_spec where m: "m = (m_impl, m_spec)" by(cases m) blast
      from m have m_impl: "get_impl ((m_impl, m_spec) # M) = m_impl # (get_impl M)" by (simp add: get_impl_def) 
      from m have m_spec: "get_spec ((m_impl, m_spec) # M) = m_spec # (get_spec M)" by (simp add: get_spec_def) 
      
      from Cons.prems(1) m have complies_formal_def: "SecurityInvariant_complies_formal_def m_impl m_spec" by simp
      with Cons.prems(2) have impl_spec: "implc_sinvar m_impl G \<longleftrightarrow> c_sinvar m_spec (list_graph_to_graph G)"
        by (simp add: SecurityInvariant_complies_formal_def_def)

      from complies_formal_def
      have "\<And>G nP. wf_list_graph G \<Longrightarrow>
        (\<lambda>G nP. (c_sinvar m_spec) G) (list_graph_to_graph G) nP = (\<lambda>G nP. (implc_sinvar m_impl) G) G nP"
        by (simp add: SecurityInvariant_complies_formal_def_def)

      from minimalize_offending_overapprox_spec_impl[OF Cons.prems(2),
          of "(\<lambda>G nP. (c_sinvar m_spec) G)" "(\<lambda>G nP. (implc_sinvar m_impl) G)", OF this]
        (*TODO: because of funny type, horribly complex instantiation*)
      have "TopoS_Interface_impl.minimalize_offending_overapprox (implc_sinvar m_impl) fs keeps G =
            TopoS_withOffendingFlows.minimalize_offending_overapprox (c_sinvar m_spec) fs keeps (list_graph_to_graph G)"
        for fs keeps by simp
      from this[of "(edgesL G)"  "[]"] have minimalize_offending_overapprox_spec:
         "TopoS_Interface_impl.minimalize_offending_overapprox (implc_sinvar m_impl) (edgesL G) [] G =
          TopoS_withOffendingFlows.minimalize_offending_overapprox (c_sinvar m_spec) (edgesL G) [] (list_graph_to_graph G)" .
      
      from Cons show ?case
        apply(simp)
        apply(simp add: m m_impl m_spec)
        apply(intro conjI impI)
          apply (simp add: impl_spec; fail)
         apply (simp add: impl_spec; fail)
        apply(simp add: delete_edges_correct[symmetric])
        apply(simp add: list_graph_to_graph_def FiniteGraph.delete_edges_simp2)
        apply(simp add: minimalize_offending_overapprox_spec)
        by (simp add: list_graph_to_graph_def)
    qed

(*
subsection{*generate valid topology*}
  text{*tuned for invariants where we don't want to calculate all offending flows*}

  fun generate_valid_topology_SOME :: "'v SecurityInvariant list \<Rightarrow> 'v list_graph \<Rightarrow> ('v list_graph)" where
    "generate_valid_topology_SOME [] G = G" |
    "generate_valid_topology_SOME (m#Ms) G = (if implc_sinvar m G
      then generate_valid_topology_SOME Ms G
      else delete_edges (generate_valid_topology_SOME Ms G) (minimalize_offending_overapprox (implc_sinvar m) (edgesL G) [] G)
      )"

  thm TopoS_Composition_Theory.generate_valid_topology_SOME_sound

  (*TODO: show conformance to generate_valid_topology_some_sound*)
  (*TODO: won't work because of the SOME!
    I will probably have to show something like
       all_security_requirements_fulfilled (get_impl M) (generate_valid_topology_SOME (get_impl M) G)
    How can I do this without copy&pasting the proof of the spec?*)
  lemma generate_valid_topology_SOME_complies:
    "\<lbrakk> \<forall> (m_impl, m_spec) \<in> set M. SecurityInvariant_complies_formal_def m_impl m_spec;
       wf_list_graph (G::('v list_graph)) \<rbrakk> \<Longrightarrow> 
       list_graph_to_graph (generate_valid_topology_SOME (get_impl M) G) = 
       TopoS_Composition_Theory.generate_valid_topology_SOME (get_spec M) (list_graph_to_graph G)"
    proof(induction M)
    case Nil thus ?case by(simp add: get_spec_def get_impl_def)
    next
    case (Cons m M)
      obtain m_impl m_spec where m: "m = (m_impl, m_spec)" by(cases m) blast
      from m have m_impl: "get_impl ((m_impl, m_spec) # M) = m_impl # (get_impl M)" by (simp add: get_impl_def) 
      from m have m_spec: "get_spec ((m_impl, m_spec) # M) = m_spec # (get_spec M)" by (simp add: get_spec_def) 
      
      from Cons.prems(1) m have complies_formal_def:  "SecurityInvariant_complies_formal_def m_impl m_spec" by simp
      with Cons.prems(2) have impl_spec: "implc_sinvar m_impl G \<longleftrightarrow>  c_sinvar m_spec (list_graph_to_graph G)"
        by (simp add: SecurityInvariant_complies_formal_def_def)
      
      (*from minimalize_offending_overapprox_gives_some_offending_flow
      have "set (minimalize_offending_overapprox (implc_sinvar m_impl) (edgesL G) [] G)
        \<in> SecurityInvariant_withOffendingFlows.set_offending_flows (c_sinvar_m_spec_bound_to_nP) (list_graph_to_graph G) nP" sorry
      *)

      have my_todo: "set (minimalize_offending_overapprox (implc_sinvar m_impl) (edgesL G) [] G)
        \<in> c_offending_flows m_spec (list_graph_to_graph G)" sorry
      
      from my_todo[simplified list_graph_to_graph_def] have how_do_i_solve_this:
      "set (minimalize_offending_overapprox (implc_sinvar m_impl) (edgesL G) [] G) =
       (SOME F. F \<in> c_offending_flows m_spec \<lparr>nodes = set (nodesL G), edges = set (edgesL G)\<rparr>)" sorry
      
      from Cons show ?case
        apply(simp)
        apply(simp add: m m_impl m_spec)
        apply(intro conjI impI)
          apply (simp add: impl_spec; fail)
         apply (simp add: impl_spec; fail)
        apply(simp add: delete_edges_correct[symmetric])
        apply(simp add: list_graph_to_graph_def FiniteGraph.delete_edges_simp2)
        using how_do_i_solve_this by simp
    qed
*)

    
end
