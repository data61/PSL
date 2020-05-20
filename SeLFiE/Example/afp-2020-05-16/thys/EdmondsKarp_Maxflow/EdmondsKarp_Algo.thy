theory EdmondsKarp_Algo
imports EdmondsKarp_Termination_Abstract FordFulkerson_Algo
begin
text \<open>
  In this theory, we formalize an abstract version of
  Edmonds-Karp algorithm, which we obtain by refining the 
  Ford-Fulkerson algorithm to always use shortest augmenting paths.

  Then, we show that the algorithm always terminates within $O(VE)$ iterations.
\<close>

subsection \<open>Algorithm\<close>

context Network 
begin

text \<open>First, we specify the refined procedure for finding augmenting paths\<close>
definition "find_shortest_augmenting_spec f \<equiv> assert (NFlow c s t f) \<then> 
  (select p. Graph.isShortestPath (residualGraph c f) s p t)"

text \<open>We show that our refined procedure is actually a refinement\<close>  
thm SELECT_refine  
lemma find_shortest_augmenting_refine[refine]: 
  "(f',f)\<in>Id \<Longrightarrow> find_shortest_augmenting_spec f' \<le> \<Down>(\<langle>Id\<rangle>option_rel) (find_augmenting_spec f)"  
  unfolding find_shortest_augmenting_spec_def find_augmenting_spec_def
  apply (refine_vcg)
  apply (auto 
    simp: NFlow.shortest_is_augmenting RELATESI
    dest: NFlow.augmenting_path_imp_shortest)
  done

text \<open>Next, we specify the Edmonds-Karp algorithm. 
  Our first specification still uses partial correctness, 
  termination will be proved afterwards. \<close>  
definition "edka_partial \<equiv> do {
  let f = (\<lambda>_. 0);

  (f,_) \<leftarrow> while\<^bsup>fofu_invar\<^esup>
    (\<lambda>(f,brk). \<not>brk) 
    (\<lambda>(f,_). do {
      p \<leftarrow> find_shortest_augmenting_spec f;
      case p of 
        None \<Rightarrow> return (f,True)
      | Some p \<Rightarrow> do {
          assert (p\<noteq>[]);
          assert (NPreflow.isAugmentingPath c s t f p);
          assert (Graph.isShortestPath (residualGraph c f) s p t);
          let f = NFlow.augment_with_path c f p;
          assert (NFlow c s t f);
          return (f, False)
        }  
    })
    (f,False);
  assert (NFlow c s t f);
  return f 
}"

lemma edka_partial_refine[refine]: "edka_partial \<le> \<Down>Id fofu"
  unfolding edka_partial_def fofu_def
  apply (refine_rcg bind_refine')
  apply (refine_dref_type)
  apply (vc_solve simp: find_shortest_augmenting_spec_def)
  done


end \<comment> \<open>Network\<close>

subsubsection \<open>Total Correctness\<close>
context Network begin
text \<open>We specify the total correct version of Edmonds-Karp algorithm.\<close>
definition "edka \<equiv> do {
  let f = (\<lambda>_. 0);

  (f,_) \<leftarrow> while\<^sub>T\<^bsup>fofu_invar\<^esup>
    (\<lambda>(f,brk). \<not>brk) 
    (\<lambda>(f,_). do {
      p \<leftarrow> find_shortest_augmenting_spec f;
      case p of 
        None \<Rightarrow> return (f,True)
      | Some p \<Rightarrow> do {
          assert (p\<noteq>[]);
          assert (NPreflow.isAugmentingPath c s t f p);
          assert (Graph.isShortestPath (residualGraph c f) s p t);
          let f = NFlow.augment_with_path c f p;
          assert (NFlow c s t f);
          return (f, False)
        }  
    })
    (f,False);
  assert (NFlow c s t f);
  return f 
}"

text \<open>Based on the measure function, it is easy to obtain a well-founded 
  relation that proves termination of the loop in the Edmonds-Karp algorithm:\<close>
definition "edka_wf_rel \<equiv> inv_image 
  (less_than_bool <*lex*> measure (\<lambda>cf. ek_analysis_defs.ekMeasure cf s t))
  (\<lambda>(f,brk). (\<not>brk,residualGraph c f))"

lemma edka_wf_rel_wf[simp, intro!]: "wf edka_wf_rel"
  unfolding edka_wf_rel_def by auto

text \<open>The following theorem states that the total correct 
  version of Edmonds-Karp algorithm refines the partial correct one.\<close>  
theorem edka_refine[refine]: "edka \<le> \<Down>Id edka_partial"
  unfolding edka_def edka_partial_def
  apply (refine_rcg bind_refine' 
    WHILEIT_refine_WHILEI[where V=edka_wf_rel])
  apply (refine_dref_type)
  apply (simp; fail)
  subgoal
    txt \<open>Unfortunately, the verification condition for introducing 
      the variant requires a bit of manual massaging to be solved:\<close>
    apply (simp)
    apply (erule bind_sim_select_rule)
    apply (auto split: option.split 
      simp: NFlow.augment_with_path_def
      simp: assert_bind_spec_conv Let_def
      simp: find_shortest_augmenting_spec_def
      simp: edka_wf_rel_def NFlow.shortest_path_decr_ek_measure
    ; fail) []
  done

  txt \<open>The other VCs are straightforward\<close>
  apply (vc_solve)
  done

subsubsection \<open>Complexity Analysis\<close>

text \<open>For the complexity analysis, we additionally show that the measure
  function is bounded by $O(VE)$. Note that our absolute bound is not as 
  precise as possible, but clearly $O(VE)$.\<close>
  (* TODO: #edgesSp even bound by |E|, as either e or swap e lays on shortest path! *)
lemma ekMeasure_upper_bound: 
  "ek_analysis_defs.ekMeasure (residualGraph c (\<lambda>_. 0)) s t 
   < 2 * card V * card E + card V"
proof -  
  interpret NFlow c s t "(\<lambda>_. 0)"
    by unfold_locales (auto simp: s_node t_node cap_non_negative)

  interpret ek: ek_analysis cf  
    by unfold_locales auto

  have cardV_positive: "card V > 0" and cardE_positive: "card E > 0"
    using card_0_eq[OF finite_V] V_not_empty apply blast
    using card_0_eq[OF finite_E] E_not_empty apply blast
    done

  show ?thesis proof (cases "cf.connected s t")  
    case False hence "ek.ekMeasure = 0" by (auto simp: ek.ekMeasure_def)
    with cardV_positive cardE_positive show ?thesis
      by auto
  next
    case True 

    have "cf.min_dist s t > 0"
      apply (rule ccontr)
      apply (auto simp: Graph.min_dist_z_iff True s_not_t[symmetric])
      done

    have "cf = c"  
      unfolding residualGraph_def E_def
      by auto
    hence "ek.uE = E\<union>E\<inverse>" unfolding ek.uE_def by simp

    from True have "ek.ekMeasure 
      = (card cf.V - cf.min_dist s t) * (card ek.uE + 1) + (card (ek.spEdges))"
      unfolding ek.ekMeasure_def by simp
    also from 
      mlex_bound[of "card cf.V - cf.min_dist s t" "card V", 
                 OF _ ek.card_spEdges_less]
    have "\<dots> < card V * (card ek.uE+1)" 
      using \<open>cf.min_dist s t > 0\<close> \<open>card V > 0\<close>
      by (auto simp: resV_netV)
    also have "card ek.uE \<le> 2*card E" unfolding \<open>ek.uE = E\<union>E\<inverse>\<close> 
      apply (rule order_trans)
      apply (rule card_Un_le)
      by auto
    finally show ?thesis by (auto simp: algebra_simps)
  qed  
qed  

text \<open>Finally, we present a version of the Edmonds-Karp algorithm 
  which is instrumented with a loop counter, and asserts that
  there are less than $2|V||E|+|V| = O(|V||E|)$ iterations.

  Note that we only count the non-breaking loop iterations.
  \<close>

text \<open>The refinement is achieved by a refinement relation, coupling the 
  instrumented loop state with the uninstrumented one\<close>
definition "edkac_rel \<equiv> {((f,brk,itc), (f,brk)) | f brk itc.
    itc + ek_analysis_defs.ekMeasure (residualGraph c f) s t 
  < 2 * card V * card E + card V
}"

definition "edka_complexity \<equiv> do {
  let f = (\<lambda>_. 0);

  (f,_,itc) \<leftarrow> while\<^sub>T 
    (\<lambda>(f,brk,_). \<not>brk) 
    (\<lambda>(f,_,itc). do {
      p \<leftarrow> find_shortest_augmenting_spec f;
      case p of 
        None \<Rightarrow> return (f,True,itc)
      | Some p \<Rightarrow> do {
          let f = NFlow.augment_with_path c f p;
          return (f, False,itc + 1)
        }  
    })
    (f,False,0);
  assert (itc < 2 * card V * card E + card V);
  return f 
}"
  
lemma edka_complexity_refine: "edka_complexity \<le> \<Down>Id edka"
proof -
  have [refine_dref_RELATES]: 
    "RELATES edkac_rel"
    by (auto simp: RELATES_def)

  show ?thesis  
    unfolding edka_complexity_def edka_def
    apply (refine_rcg)
    apply (refine_dref_type)
    apply (vc_solve simp: edkac_rel_def "NFlow.augment_with_path_def")
    subgoal using ekMeasure_upper_bound by auto []
    subgoal by (drule (1) NFlow.shortest_path_decr_ek_measure; auto)
    done
qed    

text \<open>We show that this algorithm never fails, and computes a maximum flow.\<close>
theorem "edka_complexity \<le> (spec f. isMaxFlow f)"
proof -  
  note edka_complexity_refine
  also note edka_refine
  also note edka_partial_refine
  also note fofu_partial_correct
  finally show ?thesis .
qed  


end \<comment> \<open>Network\<close>
end \<comment> \<open>Theory\<close>
