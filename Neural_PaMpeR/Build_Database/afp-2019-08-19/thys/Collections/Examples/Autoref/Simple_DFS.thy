section \<open>\isaheader{Simple DFS Algorithm}\<close>
theory Simple_DFS
imports 
  Collections.Refine_Dflt 
begin



section \<open>Graphs Implemented by Successor Function\<close>
subsection \<open>Refinement relation\<close>
definition "E_of_succ succ \<equiv> {(u,v). v\<in>succ u}"
definition [to_relAPP]: "succg_rel R \<equiv> (R \<rightarrow> \<langle>R\<rangle>list_set_rel) O br E_of_succ (\<lambda>_. True)"


consts i_graph :: "interface \<Rightarrow> interface"
  \<comment> \<open>Define the conceptual type of graphs.\<close>

lemmas [autoref_rel_intf] = REL_INTFI[of "succg_rel" i_graph]
  \<comment> \<open>Declare \<open>succg_rel\<close> to be a relator for graphs.\<close>


lemma in_id_succg_rel_iff: "(s,E)\<in>\<langle>Id\<rangle>succg_rel \<longleftrightarrow> (\<forall>v. distinct (s v) \<and> set (s v) = E``{v})"  
  \<comment> \<open>Simplification in case of identity refinements for nodes\<close>
  unfolding succg_rel_def br_def E_of_succ_def list_set_rel_def
  by (auto; force dest: fun_relD)
  
  
subsection \<open>Successor Operation\<close>
definition [simp]: "op_succ E u \<equiv> E``{u}"
  \<comment> \<open>Define the abstract successor operation.\<close>

context begin interpretation autoref_syn .
  lemma [autoref_op_pat]: "E``{v} \<equiv> op_succ$E$v" by simp
  \<comment> \<open>Declare a rewrite rule to operation identification.\<close>
end

lemma refine_succg_succs[autoref_rules]: 
  "(\<lambda>succs v. succs v,op_succ)\<in>\<langle>R\<rangle>succg_rel\<rightarrow>R\<rightarrow>\<langle>R\<rangle>list_set_rel"
  \<comment> \<open>Declare implementation of successor function to Autoref.\<close>
  apply (intro fun_relI)
  apply (auto simp add: succg_rel_def br_def E_of_succ_def dest: fun_relD)
  done

section \<open>DFS Algorithm\<close>
text \<open>
  We define a simple DFS-algorithm, prove a simple correctness
  property, and do data refinement to an efficient implementation.
\<close>

subsection \<open>Definition\<close>

text \<open>Recursive DFS-Algorithm. 
  \<open>E\<close> is the edge relation of the graph, \<open>tgt\<close> the node to 
  search for, and \<open>src\<close> the start node.
  Already explored nodes are 
  stored in \<open>V\<close>.\<close>

context 
  fixes E :: "('v\<times>'v) set" and src :: 'v and tgt :: 'v
begin
  definition dfs :: "bool nres" where
    "dfs \<equiv> do {
      (_,r) \<leftarrow> RECT (\<lambda>dfs (V,v). 
        if v=tgt then RETURN (V,True)
        else do {
          let V = insert v V;
          FOREACHc (E``{v}) (\<lambda>(V,brk). \<not>brk) (\<lambda>v' (V,brk). 
            if v'\<notin>V then dfs (V,v') else RETURN (V,False)
          ) (V,False)
        }) ({},src);
      RETURN r
    }"

  definition "reachable \<equiv> {v. (src,v)\<in>E\<^sup>*}"

subsection \<open>Correctness Proof\<close>  
  lemma dfs_correct:
    assumes FIN: "finite (E\<^sup>*``{src})"
    shows "dfs \<le> SPEC (\<lambda>r. r \<longleftrightarrow> (src,tgt)\<in>E\<^sup>*)"
  proof -
    from FIN have [simp, intro!]: "finite reachable"
      unfolding reachable_def by (auto simp: Image_def)

    text \<open>We first define the (inductive) pre and postconditions for 
      the recursion, and the loop invariant\<close>  
          
    define rpre where "rpre \<equiv> \<lambda>S (V,v). 
        v\<in>reachable - V 
      \<and> V\<subseteq>reachable
      \<and> S\<subseteq>V
      \<and> tgt\<notin>V
      \<and> E``(V-S) \<subseteq> V"

    define rpost where "rpost \<equiv> \<lambda>S (V,v) (V',r). 
          (r\<longrightarrow>tgt\<in>reachable) 
        \<and> (\<not>r \<longrightarrow> 
            tgt\<notin>V'
          \<and> V\<subseteq>V' 
          \<and> v\<in>V'
          \<and> V'\<subseteq>reachable
          \<and> E``(V'-S) \<subseteq> V'
          )
      "

    define fe_inv where "fe_inv \<equiv> \<lambda>S V v it (V',r).
        (r\<longrightarrow>tgt\<in>reachable)
      \<and> (\<not>r \<longrightarrow> 
          tgt \<notin> V'
        \<and> insert v V\<subseteq>V'
        \<and> E``{v} - it \<subseteq> V'
        \<and> V'\<subseteq>reachable
        \<and> S\<subseteq>insert v V
        \<and> E``(V'-S) \<subseteq> V' \<union> it 
        \<and> E``(V'-insert v S) \<subseteq> V'
        )"

    text \<open>Then we prove the verification conditions that our VCG will generate as separate facts.
      Of course, the workflow is to first let run the VCG, and then extract these facts from 
      its output. This way, we can make explicit the ideas of the proof, and present them separately 
      from the mainly technical VC generation.
     \<close>
        
    have vc_pre_initial: "rpre {} ({}, src)"
      by (auto simp: rpre_def reachable_def)

    {
      (* Case: Found node *)
      fix S V
      assume "rpre S (V,tgt)"
      hence "rpost S (V,tgt) (insert tgt V, True)"
        unfolding rpre_def rpost_def
        by auto
    } note vc_node_found = this

    { (* The set of nodes that the foreach loop iterates over is finite *)
      fix S V v
      assume "rpre S (V, v)"
      hence "finite (E``{v})"
        unfolding rpre_def reachable_def
        using FIN  
        apply auto
        by (meson finite_Image_subset finite_reachable_advance r_le_rtrancl)
    } note vc_foreach_finite = this
  
    {
      (* fe_inv initial *)
      fix S V v
      assume A: "v \<notin> V" "v \<noteq> tgt"
        and PRE: "rpre S (V, v)"
      hence "fe_inv S V v (E``{v}) (insert v V, False)"
        unfolding fe_inv_def rpre_def by (auto simp: )
    } note vc_enter_foreach = this

    {
      (* fe_inv ensures rpre *)
      fix S V v v' it V'
      assume A: "v'\<notin>V'" "v' \<in> it" "it \<subseteq> E``{v}"
        and FEI: "fe_inv S V v it (V', False)"
        and PRE: "rpre S (V, v)"

      from A have "(v,v')\<in>E" by auto
      moreover from PRE have "v \<in> reachable" by (auto simp: rpre_def)
      hence "E``{v} \<subseteq> reachable" by (auto simp: reachable_def)
      ultimately have [simp]: "v'\<in>reachable" by blast

      from A FEI PRE have "rpre (insert v S) (V', v')"
        unfolding rpre_def fe_inv_def by auto
    } note vc_rec_pre = this

    {
      (* rpost implies fe_inv *)
      fix S V V' v v' it Vr''
      assume "fe_inv S V v it (V', False)"
        and "rpost (insert v S) (V', v') Vr''"
      hence "fe_inv S V v (it - {v'}) Vr''"
        unfolding rpre_def rpost_def fe_inv_def by clarsimp (auto; blast)
    } note vc_iterate_foreach = this

    { (* Recursive call in variant relation *)
      fix S V V' v it
      assume "rpre S (V, v)"  
      and "fe_inv S V v it (V', False)"
      hence "(V',V)\<in>finite_psupset local.reachable"
        unfolding fe_inv_def rpre_def
        by (auto simp: finite_psupset_def)
      
    } note vc_rec_var = this
      
    {
      (* fe_inv preserved if ignoring visitied node*)
      fix S V V' v v' it Vr''
      assume "fe_inv S V v it (V', False)"
        and "v'\<in>V'"
      hence "fe_inv S V v (it - {v'}) (V', False)"
        unfolding fe_inv_def by auto
    } note vc_foreach_ignore = this


    {
      (* fe_inv (completed) implies rpost *)
      fix S V v V'
      assume FEI: "fe_inv S V v {} (V', False)"
      have "rpost S (V, v) (V', False)"
        unfolding rpost_def
        using FEI by (auto simp: fe_inv_def) []
    } note vc_foreach_completed_imp_post = this

    {
      (* fe_inv (interrupted) implies rpost *)
      fix S V v V' it
      assume FEI: "fe_inv S V v it (V', True)"
      hence "rpost S (V, v) (V', True)"
        by (auto simp add: rpost_def fe_inv_def) []
    } note vc_foreach_interrupted_imp_post = this

    { (* The postcondition of the recursion implies our desired specification *)
      fix V r
      assume "rpost {} ({}, src) (V, r)"
      hence "r = ((src, tgt) \<in> E\<^sup>*)"
        by (auto 
          simp: rpost_def reachable_def 
          dest: Image_closed_trancl 
          intro: rev_ImageI)
    } note vc_rpost_imp_spec = this

    text \<open>The verification condition generation is technical. We invoke the VCG,
      and discharge the generated VCs. The trivial ones are discharged on the spot, the
      more complicated ones have been extracted to separate facts, that we use in the proof 
      text below.
    \<close>
    show ?thesis
      unfolding dfs_def
      apply (refine_vcg RECT_rule_arb[
        where 
              pre=rpre and arb="{}"
          and M="\<lambda>a x. SPEC (rpost a x)"
          and V="inv_image (finite_psupset reachable) fst", 
        THEN order_trans
        ])
      subgoal by blast  (* Well-Foundedness  *)
      subgoal by (rule vc_pre_initial)
      subgoal by (auto simp add: rpre_def rpost_def) (* Found tgt node *)
      
      subgoal for f S _ V v (* Entering inner FOREACH loop *)
        apply (refine_rcg refine_vcg 
          FOREACHc_rule'[where I="fe_inv S V v" (*for S V*)]
          )
        apply clarsimp_all

        subgoal by (simp add: vc_foreach_finite) (* Finiteness of iteration set *)

        subgoal by (rule vc_enter_foreach) (simp add: rpre_def) (* Loop invar holds initially*)
        subgoal (* Loop invar preserved by inner recursion *)
          apply (rule order_trans, rprems)   (* Applying recursion induction hypothesis *)
          apply (erule (4) vc_rec_pre; fail) (* Precondition of inner recursion holds*)
          apply (simp add: vc_rec_var; fail) (* Parameters are smaller wrt termination ordering *)
          apply (auto simp: vc_iterate_foreach; fail) (* Postcondition of inner rec implies loop invar again  *)
          done
          
        subgoal by (rule vc_foreach_ignore; auto)  (* Node already visited: invariant is preserved *)
        subgoal by (auto simp: vc_foreach_completed_imp_post) (* Foreach loop terminated normally: Implies postcondition *)
        subgoal by (auto simp: vc_foreach_interrupted_imp_post) (* Foreach loop interrupted (tgt found): Implies postcondition *)
        done
      subgoal by (auto simp add: vc_rpost_imp_spec) (* Postcondition implies our specification *)
      done
    qed
    
end


subsection \<open>Data Refinement and Determinization\<close>

text \<open>
  Next, we use automatic data refinement and transfer to generate an
  executable algorithm. We fix the node-type to natural numbers,
  and the successor-function to return a list-set. 
  The implementation of the visited set is left open, and Autoref's heuristics
  will choose one (default for nat set: red-black-trees).
\<close>

text \<open>In our first example, we use \<open>autoref_monadic\<close>, which combines the 
  Autoref tool and the determinization of the Monadic Refinement Framework.\<close>
  
schematic_goal dfs_impl_refine_aux:
  fixes succi and E :: "('a::linorder \<times> 'a) set" and tgt src :: 'a
  assumes [autoref_rules]: "(succi,E)\<in>\<langle>Id\<rangle>succg_rel"
  notes [autoref_rules] = IdI[of src] IdI[of tgt]
  shows "RETURN (?f::?'c) \<le> \<Down>?R (dfs E src tgt)"
  unfolding dfs_def by autoref_monadic 

text \<open>We define a new constant from the synthesis result\<close>
concrete_definition dfs_impl for succi src tgt uses dfs_impl_refine_aux
text \<open>Set up code equations for the recursion combinators\<close>
prepare_code_thms dfs_impl_def
text \<open>And export the algorithm to all supported target languages\<close>
export_code dfs_impl in Haskell
export_code dfs_impl checking SML OCaml? Haskell? Scala


text \<open>Chaining the refinement theorems, we get correctness arguments that 
  are almost independent of the refinement framework:\<close>

lemma succ_ran_fin:
  assumes R: "(succi,E) \<in> \<langle>Rv\<rangle>succg_rel"
  assumes "v\<in>Range Rv"
  shows "finite (E``{v})"
  using assms
  unfolding succg_rel_def br_def E_of_succ_def
  apply clarsimp
  apply (drule (1) fun_relD)
  using list_set_rel_range[of Rv]
  by auto

lemma run_ran_aux:
  assumes R: "(succi,E) \<in> \<langle>Rv\<rangle>succg_rel"
  assumes REACH: "(src,v)\<in>E\<^sup>*"
  assumes R0: "(v0i,src) \<in> Rv"
  shows "v \<in> Range Rv"
  using REACH R0
proof (induction arbitrary: v0i rule: converse_rtrancl_induct)
  case base thus ?case by auto
next
  case (step src v')  
  from \<open>(src, v') \<in> E\<close> have "v' \<in> Range Rv" using R list_set_rel_range[of Rv]
    apply (clarsimp simp: succg_rel_def br_def E_of_succ_def)
    apply (drule fun_relD[OF _ \<open>(v0i, src) \<in> Rv\<close>])
    by auto
  with step.IH show ?thesis by blast
qed

lemma run_ran_fin: 
  assumes R: "(succi,E) \<in> \<langle>Rv\<rangle>succg_rel"
  assumes R0: "(v0i,src) \<in> Rv"
  shows "\<forall>v. (src,v)\<in>E\<^sup>* \<longrightarrow> finite (E``{v})"
  using succ_ran_fin run_ran_aux assms by metis

text \<open>Correctness theorem presented in the paper:\<close>
theorem dfs_code_correct: 
  assumes SUCCI: "(succi,E)\<in>\<langle>Id\<rangle>succg_rel"
  assumes FIN: "finite (E\<^sup>*``{src})"  
  shows "dfs_impl succi src tgt \<longleftrightarrow> (src,tgt)\<in>E\<^sup>*"
proof -
  note dfs_impl.refine[OF SUCCI, of src tgt]
  also note dfs_correct[OF FIN]
  finally show ?thesis by (auto simp: split: dres.split)
qed

subsubsection \<open>Using only Autoref\<close>

text \<open>Here we show the result of Autoref, without the determinization phase of
  the Monadic Refinement Framework: \<close>
schematic_goal 
  fixes succi and E :: "('a::linorder \<times> 'a) set" and tgt src :: 'a
  assumes [autoref_rules]: "(succi,E)\<in>\<langle>Id\<rangle>succg_rel"
  notes [autoref_rules] = IdI[of src] IdI[of tgt]
  shows "(?f::?'c, dfs E src tgt) \<in> ?R"
  unfolding dfs_def[abs_def] 
  apply (autoref (trace))
  done

subsubsection \<open>Choosing Different Implementations\<close>
text \<open>Ad-hoc override of implementation selection heuristics: Using hashset for the visited set\<close>  
schematic_goal dfs_impl_refine_aux2:
  fixes succi and E :: "(('a::hashable) \<times> 'a) set" and tgt src :: 'a
  assumes [autoref_rules]: "(succi,E)\<in>\<langle>Id\<rangle>succg_rel"
  notes [autoref_rules] = IdI[of src] IdI[of tgt]
  notes [autoref_tyrel] = ty_REL[where 'a="'a set" and R="\<langle>Id\<rangle>dflt_ahs_rel"] 
  shows "(?f::?'c, dfs E src tgt) \<in> ?R"
  unfolding dfs_def[abs_def] 
  apply autoref_monadic
  done
  

text \<open>We can also leave the type of the nodes and its implementation
  unspecified. However, we need a comparison operator on nodes\<close>
  
(* With linorder typeclass on abstract type *)  
schematic_goal dfs_impl_refine_aux3:
  fixes succi and E :: "('a::linorder \<times> 'a) set" 
    and Rv :: "('ai\<times>'a) set"
  assumes [autoref_rules_raw]: "(cmpk, dflt_cmp (\<le>) (<))\<in>(Rv\<rightarrow>Rv\<rightarrow>Id)"
  notes [autoref_tyrel] = ty_REL[where 'a="'a set" and R="\<langle>Rv\<rangle>dflt_rs_rel"]
  assumes P_REF[autoref_rules]: 
    "(succi,E)\<in>\<langle>Rv\<rangle>succg_rel"
    "(vdi,tgt::'a)\<in>Rv"
    "(v0i,src)\<in>Rv"
  shows "(RETURN (?f::?'c), dfs E src tgt)\<in>?R"
  unfolding dfs_def[abs_def]
  by autoref_monadic

(* With arbitrary cmpk' operator on abstract type, not forcing a linorder typeclass instance.
  Useful if there are multiple possible instantiations of a typeclass (eg for product ordering), 
  and one does not want to commit to one.
*)  
schematic_goal dfs_impl_refine_aux3':
  fixes succi and E :: "('a \<times> 'a) set" 
    and Rv :: "('ai\<times>'a) set"
  assumes [autoref_ga_rules]: "eq_linorder cmpk'"
  assumes [autoref_rules_raw]: "(cmpk, cmpk')\<in>(Rv\<rightarrow>Rv\<rightarrow>comp_res_rel)"
  notes [autoref_tyrel] = ty_REL[where 'a="'a set" and R="\<langle>Rv\<rangle>map2set_rel (rbt_map_rel (comp2lt cmpk'))"]
  assumes P_REF[autoref_rules]: 
    "(succi,E)\<in>\<langle>Rv\<rangle>succg_rel"
    "(vdi,tgt::'a)\<in>Rv"
    "(v0i,src)\<in>Rv"
  shows "(RETURN (?f::?'c), dfs E src tgt)\<in>?R"
  unfolding dfs_def[abs_def]
  by autoref_monadic
  
  
text \<open>We also generate code for the alternative implementations\<close>
concrete_definition dfs_impl2 for succi src tgt uses dfs_impl_refine_aux2
concrete_definition dfs_impl3 for cmpk succi v0i vdi uses dfs_impl_refine_aux3
concrete_definition dfs_impl3' for cmpk succi v0i vdi uses dfs_impl_refine_aux3'

prepare_code_thms dfs_impl2_def
prepare_code_thms dfs_impl3_def
prepare_code_thms dfs_impl3'_def

export_code dfs_impl dfs_impl2 dfs_impl3 dfs_impl3' checking SML OCaml? Haskell? Scala

text \<open>And we prove the alternative implementations correct \<close>

theorem dfs_code2_correct: 
  assumes SUCCI: "(succi,E)\<in>\<langle>Id\<rangle>succg_rel"
  assumes FIN: "finite (E\<^sup>*``{src})"  
  shows "dfs_impl2 succi src tgt \<longleftrightarrow> (src,tgt)\<in>E\<^sup>*"
proof -
  note dfs_impl2.refine[OF SUCCI, of src tgt, THEN nres_relD]
  also note dfs_correct[OF FIN]
  finally show ?thesis by (auto simp: split: dres.split)
qed
  
theorem dfs_code3_correct: 
  fixes succi and succ :: "'a::linorder \<Rightarrow> 'a set" 
    and Rv :: "('ai\<times>'a) set"
  assumes V0: "(v0i,src)\<in>Rv"
  assumes VD: "(vdi,tgt)\<in>Rv"
  assumes SUCCI: "(succi,E)\<in>\<langle>Rv\<rangle>succg_rel"
  assumes CMP: "(cmpk, dflt_cmp (\<le>) (<))\<in>(Rv\<rightarrow>Rv\<rightarrow>Id)"
  assumes FIN: "finite (E\<^sup>*``{src})"  
  shows "dfs_impl3 cmpk succi v0i vdi \<longleftrightarrow> (src,tgt)\<in>E\<^sup>*"
proof -
  note dfs_impl3.refine[OF CMP SUCCI VD V0, THEN nres_relD]
  also note dfs_correct[OF FIN]
  finally show ?thesis by (auto simp: split: dres.split)
qed

theorem dfs_code3'_correct: 
  fixes succi and succ :: "'a::linorder \<Rightarrow> 'a set" 
    and Rv :: "('ai\<times>'a) set"
  assumes V0: "(v0i,src)\<in>Rv"
  assumes VD: "(vdi,tgt)\<in>Rv"
  assumes SUCCI: "(succi,E)\<in>\<langle>Rv\<rangle>succg_rel"
  assumes CGA: "eq_linorder cmpk'"
  assumes CMP: "(cmpk, cmpk') \<in> Rv\<rightarrow>Rv\<rightarrow>comp_res_rel"
  assumes FIN: "finite (E\<^sup>*``{src})"  
  shows "dfs_impl3' cmpk succi v0i vdi \<longleftrightarrow> (src,tgt)\<in>E\<^sup>*"
proof -
  note dfs_impl3'.refine[OF CGA CMP SUCCI VD V0, THEN nres_relD]
  also note dfs_correct[OF FIN]
  finally show ?thesis by (auto simp: split: dres.split)
qed


(* Reachability *)  

definition [simp]: "op_reachable E u v \<equiv> (u,v)\<in>E\<^sup>*"
context begin interpretation autoref_syn .
  lemma [autoref_op_pat]: "(u,v)\<in>E\<^sup>* \<equiv> op_reachable$E$u$v" by simp


  (* We use a quite general setup here, working with any linearly ordered
    abstract node type, refined by any relation. *)
  theorem dfs_code3_correct_rl[autoref_rules]: 
    fixes succi and succ :: "'a::linorder \<Rightarrow> 'a set" 
      and Rv :: "('ai\<times>'a) set"
    assumes V0: "(v0i,src)\<in>Rv"
    assumes VD: "(vdi,tgt)\<in>Rv"
    assumes SUCCI: "(succi,E)\<in>\<langle>Rv\<rangle>succg_rel"
    assumes CGA: "SIDE_GEN_ALGO (eq_linorder cmpk')"
    assumes CMP: "GEN_OP cmpk cmpk' (Rv\<rightarrow>Rv\<rightarrow>comp_res_rel)"
    assumes FIN: "SIDE_PRECOND (finite (E\<^sup>*``{src}))"  
    shows "(dfs_impl3' cmpk succi v0i vdi, 
          (OP op_reachable ::: \<langle>Rv\<rangle>succg_rel \<rightarrow> Rv \<rightarrow> Rv \<rightarrow> bool_rel)$E$src$tgt)
          \<in> bool_rel"
    using dfs_code3'_correct[OF V0 VD SUCCI, of cmpk' cmpk] CGA CMP FIN
    unfolding autoref_tag_defs by simp
    
end


end
