theory TopoS_withOffendingFlows
imports TopoS_Interface
begin


section \<open>@{term SecurityInvariant} Instantiation Helpers\<close>

text\<open>
  The security invariant locales are set up hierarchically to ease instantiation proofs.
  The first locale, @{term SecurityInvariant_withOffendingFlows} has no assumptions, thus instantiations is for free. 
  The first step focuses on monotonicity,
\<close>



context SecurityInvariant_withOffendingFlows
begin
  text\<open>We define the monotonicity of \<open>sinvar\<close>:
  
  @{term "(\<And> nP N E' E. wf_graph \<lparr> nodes = N, edges = E \<rparr>  \<Longrightarrow> E' \<subseteq> E \<Longrightarrow> sinvar \<lparr> nodes = N, edges = E \<rparr> nP \<Longrightarrow> sinvar \<lparr> nodes = N, edges = E' \<rparr> nP )"}
  
  Having a valid invariant, removing edges retains the validity. I.e.\ prohibiting more, is more or equally secure.
\<close>

  definition sinvar_mono :: "bool" where
    "sinvar_mono \<longleftrightarrow> (\<forall> nP N E' E. 
      wf_graph \<lparr> nodes = N, edges = E \<rparr> \<and> 
      E' \<subseteq> E \<and> 
      sinvar \<lparr> nodes = N, edges = E \<rparr> nP \<longrightarrow> sinvar \<lparr> nodes = N, edges = E' \<rparr> nP )"

  text\<open>
    If one can show @{const sinvar_mono}, then the instantiation of the @{term SecurityInvariant_preliminaries} locale is tremendously simplified. 
\<close>

  lemma sinvar_mono_I_proofrule_simple: 
  "\<lbrakk> (\<forall> G nP. sinvar G nP = (\<forall> (e1, e2) \<in> edges G. P e1 e2 nP) ) \<rbrakk> \<Longrightarrow> sinvar_mono"
  apply(simp add: sinvar_mono_def)
  apply(clarify)
  apply(fast)
  done

  lemma sinvar_mono_I_proofrule:
  "\<lbrakk> (\<forall> nP (G:: 'v graph). sinvar G nP = (\<forall> (e1, e2) \<in> edges G. P e1 e2 nP G) ); 
    (\<forall> nP e1 e2 N E' E. 
      wf_graph \<lparr> nodes = N, edges = E \<rparr> \<and> 
      (e1,e2) \<in> E \<and> 
      E' \<subseteq> E \<and> 
      P e1 e2 nP \<lparr>nodes = N, edges = E\<rparr> \<longrightarrow> P e1 e2 nP \<lparr>nodes = N, edges = E'\<rparr>) \<rbrakk> \<Longrightarrow> sinvar_mono"
  unfolding sinvar_mono_def
  proof(clarify)
    fix nP N E' E
    assume AllForm: "(\<forall> nP (G:: 'v graph). sinvar G nP = (\<forall> (e1, e2) \<in> edges G. P e1 e2 nP G) )"
    and Pmono: "\<forall>nP e1 e2 N E' E. wf_graph \<lparr> nodes = N, edges = E \<rparr> \<and> (e1,e2) \<in> E \<and> E' \<subseteq> E \<and> P e1 e2 nP \<lparr>nodes = N, edges = E\<rparr> \<longrightarrow> P e1 e2 nP \<lparr>nodes = N, edges = E'\<rparr>"
    and wfG: "wf_graph \<lparr>nodes = N, edges = E\<rparr>"
    and E'subset: "E' \<subseteq> E"
    and evalE: "sinvar \<lparr>nodes = N, edges = E\<rparr> nP"
    
    from Pmono have Pmono1: 
      "\<And>nP N E' E. wf_graph \<lparr> nodes = N, edges = E \<rparr> \<Longrightarrow> E' \<subseteq> E \<Longrightarrow> (\<forall>(e1,e2) \<in> E. P e1 e2 nP \<lparr>nodes = N, edges = E\<rparr> \<longrightarrow> P e1 e2 nP \<lparr>nodes = N, edges = E'\<rparr>)" 
    by blast

    from AllForm have "sinvar \<lparr>nodes = N, edges = E\<rparr> nP = (\<forall> (e1, e2) \<in> E. P e1 e2 nP \<lparr>nodes = N, edges = E\<rparr>)" by force
    from this evalE have "(\<forall> (e1, e2) \<in> E. P e1 e2 nP \<lparr>nodes = N, edges = E\<rparr>)" by simp
    from Pmono1[OF wfG E'subset, of "nP"] this have "\<forall>(e1, e2) \<in> E. P e1 e2 nP \<lparr>nodes = N, edges = E'\<rparr>" by fast
    from this E'subset have "\<forall>(e1, e2) \<in> E'. P e1 e2 nP \<lparr>nodes = N, edges = E'\<rparr>" by fast
    from this have "\<forall>(e1, e2) \<in> (edges \<lparr>nodes = N, edges = E'\<rparr>). P e1 e2 nP \<lparr>nodes = N, edges = E'\<rparr>" by simp
    from this AllForm show "sinvar \<lparr>nodes = N, edges = E'\<rparr> nP" by presburger
  qed
 

   text\<open>Invariant violations do not disappear if we add more flows.\<close>
   lemma sinvar_mono_imp_negative_mono:
   "sinvar_mono \<Longrightarrow> wf_graph \<lparr> nodes = N, edges = E \<rparr> \<Longrightarrow>  E' \<subseteq> E \<Longrightarrow>
   \<not> sinvar \<lparr> nodes = N, edges = E' \<rparr> nP \<Longrightarrow> \<not> sinvar \<lparr> nodes = N, edges = E \<rparr> nP"
   unfolding sinvar_mono_def by(blast)

  corollary sinvar_mono_imp_negative_delete_edge_mono:
   "sinvar_mono \<Longrightarrow> wf_graph G \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> \<not> sinvar (delete_edges G Y) nP \<Longrightarrow> \<not> sinvar (delete_edges G X) nP "
  proof -
   assume sinvar_mono
   and "wf_graph G" and "X \<subseteq> Y" and "\<not> sinvar (delete_edges G Y) nP"
   from delete_edges_wf[OF \<open>wf_graph G\<close>] have valid_G_delete: "wf_graph \<lparr>nodes = nodes G, edges = edges G - X\<rparr>" by(simp add: delete_edges_simp2)
   from \<open>X \<subseteq> Y\<close> have "edges G - Y \<subseteq> edges G - X" by blast
   with \<open>sinvar_mono\<close> sinvar_mono_def valid_G_delete have
    "sinvar \<lparr>nodes = nodes G, edges = edges G - X\<rparr> nP \<Longrightarrow> sinvar \<lparr>nodes = nodes G, edges = edges G - Y\<rparr> nP" by blast
   hence "sinvar (delete_edges G X) nP \<Longrightarrow> sinvar (delete_edges G Y) nP" by(simp add: delete_edges_simp2)
   with \<open>\<not> sinvar (delete_edges G Y) nP\<close> show ?thesis by blast
  qed


  (*lemma mono_offending_flows_min_set:
  assumes mono_isoffending: "(\<forall> ff f' G nP. is_offending_flows ff G nP \<longrightarrow> is_offending_flows (f' \<union> ff) G nP)"
  and offending: "is_offending_flows_min_set As G nP"
  shows "sinvar (delete_edges G (As \<union> Bs)) nP"
  proof -
    from offending have "is_offending_flows As G nP" using is_offending_flows_min_set_def by simp
    from mono_isoffending this have "is_offending_flows (Bs \<union> As) G nP" by simp
    hence "is_offending_flows (As \<union> Bs) G nP" by (metis Un_commute)
    from this is_offending_flows_def show ?thesis by simp
  qed*)


  (*use this to show locale preliminaries from mono*)
  lemma sinvar_mono_imp_is_offending_flows_mono:
  assumes mono: "sinvar_mono"
  and wfG: "wf_graph G"
  shows "is_offending_flows FF G nP  \<Longrightarrow> is_offending_flows (FF \<union> F) G nP"
  proof -
    from wfG have wfG': "wf_graph \<lparr>nodes = nodes G, edges = {(e1, e2). (e1, e2) \<in> edges G \<and> (e1, e2) \<notin> FF}\<rparr>" 
      by (metis delete_edges_def delete_edges_wf)
    from mono have sinvarE: "(\<And> nP N E' E. wf_graph \<lparr> nodes = N, edges = E \<rparr> \<Longrightarrow> E' \<subseteq> E \<Longrightarrow> sinvar \<lparr> nodes = N, edges = E \<rparr> nP \<Longrightarrow> sinvar \<lparr> nodes = N, edges = E' \<rparr> nP )"
      unfolding sinvar_mono_def
      by metis
    have "\<And> G FF F. {(e1, e2). (e1, e2) \<in> edges G \<and> (e1, e2) \<notin> FF \<and> (e1, e2) \<notin> F} \<subseteq> {(e1, e2). (e1, e2) \<in> edges G \<and> (e1, e2) \<notin> FF} "
      by(rule Collect_mono) (simp)
    from sinvarE[OF wfG' this]
    show "is_offending_flows FF G nP \<Longrightarrow> is_offending_flows (FF \<union> F) G nP"
      by(simp add: is_offending_flows_def delete_edges_def)
  qed

  (*use this to show locale sinvar_mono*)
  lemma sinvar_mono_imp_sinvar_mono: 
  "sinvar_mono \<Longrightarrow> wf_graph \<lparr> nodes = N, edges = E \<rparr> \<Longrightarrow> E' \<subseteq> E \<Longrightarrow> sinvar \<lparr> nodes = N, edges = E \<rparr> nP \<Longrightarrow> 
        sinvar \<lparr> nodes = N, edges = E' \<rparr> nP"
  apply(simp add: sinvar_mono_def)
  by blast

end



subsection \<open>Offending Flows Not Empty Helper Lemmata\<close>
context SecurityInvariant_withOffendingFlows
begin
  text \<open>Give an over-approximation of offending flows (e.g. all edges) and get back a
          minimal set\<close>
  (*offending_overapproximation keepingInOffendingApproximation G nP*)
  fun minimalize_offending_overapprox :: "('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 
  'v graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<times> 'v) list" where
  "minimalize_offending_overapprox [] keep _ _ = keep" |
  "minimalize_offending_overapprox (f#fs) keep G nP = (if sinvar (delete_edges_list G (fs@keep)) nP then
      minimalize_offending_overapprox fs keep G nP 
    else
      minimalize_offending_overapprox fs (f#keep) G nP
    )"



  text\<open>The graph we check in @{const minimalize_offending_overapprox},
  @{term "G minus (fs \<union> keep)"} is the graph from the \<open>offending_flows_min_set\<close> condition.
  We add @{term f} and remove it.\<close>
 

  (*lemma minimalize_offending_overapprox_not_in: 
  "f \<notin> set fs \<Longrightarrow> f \<notin> set keep \<Longrightarrow> f \<notin> set (minimalize_offending_overapprox fs keep G nP)"
   apply(induction fs arbitrary: keep)
    by(simp_all)*)




  (*lemma offending_min_set_ab_in_fs: "wf_graph (G::'v graph) \<Longrightarrow> (a,b) \<in> edges G \<Longrightarrow>
       is_offending_flows_min_set ({(a, b)} \<union> fs) G nP \<Longrightarrow>
       sinvar (delete_edges G fs) nP \<Longrightarrow>
       (a,b) \<in> fs"
  apply(rule ccontr)
  apply(simp add: is_offending_flows_min_set_def)
  apply(clarify)
  apply(simp add: add_delete_edges)
  done*)


  lemma minimalize_offending_overapprox_subset:
  "set (minimalize_offending_overapprox ff keeps G nP) \<subseteq> set ff \<union> set keeps"
   proof(induction ff arbitrary: keeps)
   case Nil
    thus ?case by simp
   next
   case (Cons a ff)
    from Cons have case1: "(sinvar (delete_edges_list G (ff @ keeps)) nP \<Longrightarrow>
     set (minimalize_offending_overapprox ff keeps G nP) \<subseteq> insert a (set ff \<union> set keeps))" 
      by blast
     from Cons have case2: "(\<not> sinvar (delete_edges_list G (ff @ keeps)) nP \<Longrightarrow>
     set (minimalize_offending_overapprox ff (a # keeps) G nP) \<subseteq> insert a (set ff \<union> set keeps))"
      by fastforce
    from case1 case2 show ?case by simp
   qed



  lemma not_model_mono_imp_addedge_mono: 
  assumes mono: "sinvar_mono"
   and vG: "wf_graph G" and ain: "(a1,a2) \<in> edges G" and xy: "X \<subseteq> Y" and ns: "\<not> sinvar (add_edge a1 a2 (delete_edges G (Y))) nP"  
  shows "\<not> sinvar (add_edge a1 a2 (delete_edges G X)) nP"
   proof -
      have wf_graph_add_delete_edge_simp: 
        "\<And>Y. add_edge a1 a2 (delete_edges G Y) = (delete_edges G (Y - {(a1,a2)}))"
        apply(simp add: delete_edges_simp2 add_edge_def)
        apply(rule conjI)
         using ain apply (metis insert_absorb vG wf_graph.E_wfD(1) wf_graph.E_wfD(2))
         apply(auto simp add: ain)
        done
      from this ns have 1: "\<not> sinvar (delete_edges G (Y - {(a1, a2)})) nP" by simp
      have 2: "X - {(a1, a2)} \<subseteq> Y - {(a1, a2)}" by (metis Diff_mono subset_refl xy)
      from sinvar_mono_imp_negative_delete_edge_mono[OF mono] vG have
        "\<And>X Y. X \<subseteq> Y \<Longrightarrow> \<not> sinvar (delete_edges G Y) nP \<Longrightarrow> \<not> sinvar (delete_edges G X) nP" by blast
      from this[OF 2 1] have "\<not> sinvar (delete_edges G (X - {(a1, a2)})) nP" by simp
      from this wf_graph_add_delete_edge_simp[symmetric] show ?thesis by simp
   qed


  theorem is_offending_flows_min_set_minimalize_offending_overapprox:
      assumes mono: "sinvar_mono"
      and vG: "wf_graph G" and iO: "is_offending_flows (set ff) G nP" and sF: "set ff \<subseteq> edges G" and dF: "distinct ff"
      shows "is_offending_flows_min_set (set (minimalize_offending_overapprox ff [] G nP)) G nP"
              (is "is_offending_flows_min_set ?minset G nP")
  proof -
    from iO have "sinvar (delete_edges G (set ff)) nP" by (metis is_offending_flows_def)

    \<comment> \<open>@{term "sinvar"} holds if we delete @{term "ff"}.
        With the following generalized statement, we show that it also holds if we delete @{term "minimalize_offending_overapprox ff []"}\<close>
    { 
      fix keeps
      \<comment> \<open>Generalized for arbitrary @{term keeps}\<close>
        have "sinvar (delete_edges G (set ff \<union> set keeps)) nP \<Longrightarrow> 
          sinvar (delete_edges G (set (minimalize_offending_overapprox ff keeps G nP))) nP"
         apply(induction ff arbitrary: keeps)
          apply(simp)
         apply(simp)
         apply(rule impI)
         apply(simp add:delete_edges_list_union)
         done
    } 
    \<comment> \<open>@{term "keeps = []"}\<close>
    note minimalize_offending_overapprox_maintains_evalmodel=this[of "[]"]


    from \<open>sinvar (delete_edges G (set ff)) nP\<close> minimalize_offending_overapprox_maintains_evalmodel have
      "sinvar (delete_edges G ?minset) nP" by simp
    hence 1: "is_offending_flows ?minset G nP" by (metis iO is_offending_flows_def)

    txt\<open>We need to show minimality of @{term "minimalize_offending_overapprox ff []"}.
      Minimality means @{term "\<forall>(e1, e2)\<in>?minset. \<not> sinvar (add_edge e1 e2 (delete_edges G ?minset)) nP"}.
      We show the following generalized fact.
\<close>
    {
      fix ff keeps
      have "\<forall> x \<in> set ff. x \<notin> set keeps \<Longrightarrow>
        \<forall> x \<in> set ff. x \<in> edges G \<Longrightarrow>
        distinct ff \<Longrightarrow>
        \<forall>(e1, e2)\<in> set keeps.
           \<not> sinvar (add_edge e1 e2 (delete_edges G (set (minimalize_offending_overapprox ff keeps G nP)))) nP \<Longrightarrow>
        \<forall>(e1, e2)\<in>set (minimalize_offending_overapprox ff keeps G nP).
           \<not> sinvar (add_edge e1 e2 (delete_edges G (set (minimalize_offending_overapprox ff keeps G nP)))) nP"
       proof(induction ff arbitrary: keeps)
       case Nil
        from Nil show ?case by(simp)
       next
       case (Cons a ff)
        assume not_in_keeps: "\<forall>x\<in>set (a # ff). x \<notin> set keeps"
          hence a_not_in_keeps: "a \<notin> set keeps" by simp
        assume in_edges: "\<forall>x\<in>set (a # ff). x \<in> edges G"
          hence ff_in_edges: "\<forall>x\<in>set ff. x \<in> edges G" and a_in_edges: "a \<in> edges G" by simp_all
        assume distinct: "distinct (a # ff)"
          hence ff_distinct: "distinct ff" and a_not_in_ff: "a \<notin> set ff "by simp_all
        assume minimal: "\<forall>(e1, e2)\<in>set keeps. 
          \<not> sinvar (add_edge e1 e2 (delete_edges G (set (minimalize_offending_overapprox (a # ff) keeps G nP)))) nP"
        
        
        have delete_edges_list_union_insert: "\<And> f fs keep. delete_edges_list G (f#fs@keep) = delete_edges G ({f} \<union> set fs \<union> set keep)"
        by(simp add: graph_ops delete_edges_list_set)

        let ?goal="?case" \<comment> \<open>we show this by case distinction\<close>
        show ?case
        proof(cases "sinvar (delete_edges_list G (ff@keeps)) nP")
        case True 
          from True have "sinvar (delete_edges_list G (ff@keeps)) nP" .
          from this Cons show ?goal using delete_edges_list_union by simp
        next
        case False
          (*MONO=Cons.prems(1)"*)
           { \<comment> \<open>a lemma we only need once here\<close>
              fix a ff keeps
              assume mono: "sinvar_mono" and ankeeps: "a \<notin> set keeps"
              and anff: "a \<notin> set ff" and aE: "a \<in> edges G"
              and nsinvar: "\<not> sinvar (delete_edges_list G (ff @ keeps)) nP"
              have "\<not> sinvar (add_edge (fst a) (snd a) (delete_edges G (set (minimalize_offending_overapprox (a # ff) keeps G nP)))) nP"
              proof -
                { fix F Fs keep
                  from vG have "F \<in> edges G \<Longrightarrow> F \<notin> set Fs \<Longrightarrow> F \<notin> set keep \<Longrightarrow>
                    (add_edge (fst F) (snd F) (delete_edges_list G (F#Fs@keep))) = (delete_edges_list G (Fs@keep))"
                  apply(simp add:delete_edges_list_union delete_edges_list_union_insert)
                  apply(simp add: graph_ops)
                  apply(rule conjI)
                   apply(simp add: wf_graph_def)
                   apply blast
                  apply(simp add: wf_graph_def)
                  by fastforce
                } note delete_edges_list_add_add_iff=this
                from aE have "(fst a, snd a) \<in> edges G" by simp
                from delete_edges_list_add_add_iff[of a ff keeps] have
                  "delete_edges_list G (ff @ keeps) = add_edge (fst a) (snd a) (delete_edges_list G (a # ff @ keeps))"
                  by (metis aE anff ankeeps)
                from this nsinvar have "\<not> sinvar (add_edge (fst a) (snd a) (delete_edges_list G (a # ff @ keeps))) nP" by simp
                from this delete_edges_list_union_insert have 1:
                  "\<not> sinvar (add_edge (fst a) (snd a) (delete_edges G (insert a (set ff \<union> set keeps)))) nP" by (metis insert_is_Un sup_assoc)
            
                from minimalize_offending_overapprox_subset[of "ff" "a#keeps" G nP] have
                  "set (minimalize_offending_overapprox ff (a # keeps) G nP) \<subseteq> insert a (set ff \<union> set keeps)" by simp
            
                from not_model_mono_imp_addedge_mono[OF mono vG \<open>(fst a, snd a) \<in> edges G\<close> this 1] show ?thesis
                  by (metis minimalize_offending_overapprox.simps(2) nsinvar)
              qed
           } note not_model_mono_imp_addedge_mono_minimalize_offending_overapprox=this
    
          from not_model_mono_imp_addedge_mono_minimalize_offending_overapprox[OF mono a_not_in_keeps a_not_in_ff a_in_edges False] have a_minimal: "
          \<not> sinvar (add_edge (fst a) (snd a) (delete_edges G (set (minimalize_offending_overapprox (a # ff) keeps G nP)))) nP"
          by simp
          from minimal a_minimal
          have a_keeps_minimal: "\<forall>(e1, e2)\<in>set (a # keeps). 
          \<not> sinvar (add_edge e1 e2 (delete_edges G (set (minimalize_offending_overapprox ff (a # keeps) G nP)))) nP" 
            using False by fastforce
          from Cons.prems have a_not_in_keeps: "\<forall>x\<in>set ff. x \<notin> set (a#keeps)" by auto
          from Cons.IH[OF a_not_in_keeps ff_in_edges ff_distinct a_keeps_minimal] have IH:
            "\<forall>(e1, e2)\<in>set (minimalize_offending_overapprox ff (a # keeps) G nP).
           \<not> sinvar (add_edge e1 e2 (delete_edges G (set (minimalize_offending_overapprox ff (a # keeps) G nP)))) nP" .
          
          from False have "\<not> sinvar (delete_edges G (set ff \<union> set keeps)) nP " using delete_edges_list_union by metis
          from this have "set (minimalize_offending_overapprox (a # ff) keeps G nP) = 
            set (minimalize_offending_overapprox ff (a#keeps) G nP)"
            by(simp add: delete_edges_list_union)
          from this IH have ?goal by presburger
          thus ?goal .
        qed
      qed
    } note mono_imp_minimalize_offending_overapprox_minimal=this[of ff "[]"]

    from mono_imp_minimalize_offending_overapprox_minimal[OF _ _ dF] sF have 2:
      "\<forall>(e1, e2)\<in>?minset. \<not> sinvar (add_edge e1 e2 (delete_edges G ?minset)) nP"
    by auto
    from 1 2 show ?thesis
      by(simp add: is_offending_flows_def is_offending_flows_min_set_def)
  qed

  corollary mono_imp_set_offending_flows_not_empty:
  assumes mono_sinvar: "sinvar_mono"
  and vG: "wf_graph G" and iO: "is_offending_flows (set ff) G nP" and sS: "set ff \<subseteq> edges G" and dF: "distinct ff"
  shows
    "set_offending_flows G nP \<noteq> {}"
  proof -
    from iO SecurityInvariant_withOffendingFlows.is_offending_flows_def have nS: "\<not> sinvar G nP" by metis
    from sinvar_mono_imp_negative_delete_edge_mono[OF mono_sinvar] have negative_delete_edge_mono: 
      "\<forall> G nP X Y. wf_graph G \<and> X \<subseteq> Y \<and> \<not> sinvar (delete_edges G (Y)) nP \<longrightarrow> \<not> sinvar (delete_edges G X) nP" by blast
      
    from is_offending_flows_min_set_minimalize_offending_overapprox[OF mono_sinvar vG iO sS dF] 
     have "is_offending_flows_min_set (set (minimalize_offending_overapprox ff [] G nP)) G nP" by simp
    from this set_offending_flows_def sS have
      "(set (minimalize_offending_overapprox ff [] G nP)) \<in> set_offending_flows G nP"
      using minimalize_offending_overapprox_subset[where keeps="[]"] by fastforce
    thus ?thesis by blast 
   qed


   text\<open>
   To show that @{const set_offending_flows} is not empty, the previous corollary @{thm mono_imp_set_offending_flows_not_empty} is very useful.
   Just select @{term "set ff = edges G"}.
\<close>



   text\<open>
   If there exists a security violations,
   there a means to fix it if and only if the network in which nobody communicates with anyone fulfills the security requirement
\<close>
   theorem valid_empty_edges_iff_exists_offending_flows: 
    assumes mono: "sinvar_mono" and wfG: "wf_graph G" and noteval: "\<not> sinvar G nP"
    shows "sinvar \<lparr> nodes = nodes G, edges = {} \<rparr> nP \<longleftrightarrow> set_offending_flows G nP \<noteq> {}"
   proof 
      assume a: "sinvar \<lparr> nodes = nodes G, edges = {} \<rparr> nP"
  
      from finite_distinct_list[OF wf_graph.finiteE] wfG
      obtain list_edges where list_edges_props: "set list_edges = edges G \<and> distinct list_edges" by blast
      hence listedges_subseteq_edges: "set list_edges \<subseteq> edges G" by blast
  
      have empty_edge_graph_simp: "(delete_edges G (edges G)) = \<lparr> nodes = nodes G, edges = {} \<rparr>" by(auto simp add: graph_ops)
      from a is_offending_flows_def noteval list_edges_props empty_edge_graph_simp 
        have overapprox: "is_offending_flows (set list_edges) G nP" by auto
  
      from mono_imp_set_offending_flows_not_empty[OF mono wfG overapprox listedges_subseteq_edges] list_edges_props 
      show "set_offending_flows G nP \<noteq> {}" by simp
    next
      assume a: "set_offending_flows G nP \<noteq> {}"
  
      from a obtain f where f_props: "f \<subseteq> edges G \<and> is_offending_flows_min_set f G nP" using set_offending_flows_def by fastforce
  
      from f_props have "sinvar (delete_edges G f) nP" using is_offending_flows_min_set_def is_offending_flows_def by simp
        hence evalGf: "sinvar \<lparr>nodes = nodes G, edges = {(e1, e2). (e1, e2) \<in> edges G \<and> (e1, e2) \<notin> f}\<rparr> nP" by(simp add: delete_edges_def)
      from delete_edges_wf[OF wfG, unfolded delete_edges_def] 
        have wfGf: "wf_graph \<lparr>nodes = nodes G, edges = {(e1, e2). (e1, e2) \<in> edges G \<and> (e1, e2) \<notin> f}\<rparr>" by simp
      have emptyseqGf: "{} \<subseteq>  {(e1, e2). (e1, e2) \<in> edges G \<and> (e1, e2) \<notin> f}" by simp
  
      from mono[unfolded sinvar_mono_def] evalGf wfGf emptyseqGf have "sinvar \<lparr>nodes = nodes G, edges = {}\<rparr> nP" by blast
      thus "sinvar \<lparr>nodes = nodes G, edges = {}\<rparr> nP" .
  qed



  text\<open>
  @{const minimalize_offending_overapprox} not only computes a set where @{const is_offending_flows_min_set} holds, but it also returns a subset of the input.
\<close>
  lemma minimalize_offending_overapprox_keeps_keeps: "(set keeps) \<subseteq> set (minimalize_offending_overapprox ff keeps G nP)"
    proof(induction ff keeps G nP rule: minimalize_offending_overapprox.induct)
    qed(simp_all)

  lemma minimalize_offending_overapprox_subseteq_input: "set (minimalize_offending_overapprox ff keeps G nP) \<subseteq> (set ff) \<union> (set keeps)"
    proof(induction ff keeps G nP rule: minimalize_offending_overapprox.induct)
    case 1 thus ?case by simp
    next
    case 2 thus ?case by(simp add: delete_edges_list_set delete_edges_simp2) blast
    qed

end




context SecurityInvariant_preliminaries
  begin
    text\<open>@{const sinvar_mono} naturally holds in @{const SecurityInvariant_preliminaries}\<close>
    lemma sinvar_monoI: "sinvar_mono"
      unfolding sinvar_mono_def using mono_sinvar by blast

    text\<open>Note: due to monotonicity, the minimality also holds for arbitrary subsets\<close>
    lemma assumes "wf_graph G" and "is_offending_flows_min_set F G nP" and "F \<subseteq> edges G" and "E \<subseteq> F" and "E \<noteq> {}"
          shows "\<not> sinvar \<lparr> nodes = nodes G, edges = ((edges G) - F) \<union> E \<rparr> nP"
    proof -
      from sinvar_mono_imp_negative_delete_edge_mono[OF sinvar_monoI \<open>wf_graph G\<close>] have negative_delete_edge_mono: 
      "\<And>X Y. X \<subseteq> Y \<Longrightarrow> \<not> sinvar \<lparr> nodes = nodes G, edges = (edges G) - Y \<rparr> nP \<Longrightarrow> \<not> sinvar \<lparr> nodes = nodes G, edges = edges G - X \<rparr> nP"
        using delete_edges_simp2 by metis
      from assms(2) have "(\<forall>(e1, e2)\<in>F. \<not> sinvar (add_edge e1 e2 (delete_edges G F)) nP)"
      unfolding is_offending_flows_min_set_def by simp
      with \<open>wf_graph G\<close> have min: "(\<forall>(e1, e2)\<in>F. \<not> sinvar \<lparr> nodes = nodes G, edges = ((edges G) - F) \<union> {(e1,e2)} \<rparr> nP)"
        apply(simp add: delete_edges_simp2 add_edge_def)
        apply(rule, rename_tac x, case_tac x, rename_tac e1 e2, simp)
        apply(erule_tac x="(e1, e2)" in ballE)
         apply(simp_all)
        apply(subgoal_tac "insert e1 (insert e2 (nodes G)) = nodes G")
         apply(simp)
        by (metis assms(3) insert_absorb rev_subsetD wf_graph.E_wfD(1) wf_graph.E_wfD(2))
      from \<open>E \<noteq> {}\<close> obtain e where "e \<in> E" by blast
      with min \<open>E \<subseteq> F\<close> have mine: "\<not> sinvar \<lparr> nodes = nodes G, edges = ((edges G) - F) \<union> {e} \<rparr> nP" by fast
      have e1: "edges G - (F - {e}) = insert e (edges G - F)" using DiffD2 \<open>e \<in> E\<close> assms(3) assms(4) by auto 
      have e2: "edges G - (F - E) = ((edges G) - F) \<union> E" using assms(3) assms(4) by auto 
      from negative_delete_edge_mono[where Y="F - {e}" and X="F - E"] \<open>e \<in> E\<close> have
      "\<not> sinvar \<lparr>nodes = nodes G, edges = edges G - (F - {e})\<rparr> nP \<Longrightarrow> \<not> sinvar \<lparr>nodes = nodes G, edges = edges G - (F - E)\<rparr> nP" by blast
      with mine e1 e2 show ?thesis by simp
    qed

    
    text\<open>The algorithm @{const minimalize_offending_overapprox} is correct\<close>
    lemma minimalize_offending_overapprox_sound: 
      "\<lbrakk> wf_graph G; is_offending_flows (set ff) G nP; set ff \<subseteq> edges G; distinct ff \<rbrakk>
        \<Longrightarrow> is_offending_flows_min_set (set (minimalize_offending_overapprox ff [] G nP)) G nP "
    using is_offending_flows_min_set_minimalize_offending_overapprox sinvar_monoI by blast

    text\<open>
      If @{term "\<not> sinvar G nP"}
      Given a list ff, (ff is distinct and a subset of G's edges)
      such that \<open>sinvar (V, E - ff) nP\<close>
      @{const minimalize_offending_overapprox} minimizes ff such that we get an offending flows
      Note: choosing ff = edges G is a good choice!
\<close>
    theorem minimalize_offending_overapprox_gives_back_an_offending_flow:
      "\<lbrakk> wf_graph G; is_offending_flows (set ff) G nP; set ff \<subseteq> edges G; distinct ff \<rbrakk>
        \<Longrightarrow>
         (set (minimalize_offending_overapprox ff [] G nP)) \<in> set_offending_flows G nP"
    apply(frule(3) minimalize_offending_overapprox_sound)
    apply(simp add: set_offending_flows_def)
    using minimalize_offending_overapprox_subseteq_input[where keeps="[]", simplified] by blast


    (*TODO better minimality condition for keeps*)
    (*lemma  minimalize_offending_overapprox_sound_fixKeep:
      "\<lbrakk> wf_graph G; is_offending_flows (set (ff @ keeps)) G nP; \<forall> x \<in> set ff. x \<notin> set keeps; \<forall> x \<in> set ff. x \<in> edges G; distinct ff; 
        \<forall>(e1, e2)\<in> set keeps. \<not> sinvar (add_edge e1 e2 (delete_edges G (set (minimalize_offending_overapprox ff keeps G nP)))) nP \<rbrakk>
        \<Longrightarrow>
         is_offending_flows_min_set (set (minimalize_offending_overapprox ff keeps G nP)) G nP \<and> set keeps \<subseteq> (set (minimalize_offending_overapprox ff keeps G nP))"
       apply(rule conjI)
        apply(simp only: is_offending_flows_min_set_def)
        apply(rule conjI)
         apply(simp add: is_offending_flows_def is_offending_flows_min_set_def)
         apply(simp add:minimalize_offending_overapprox_maintains_evalmodel)
        apply(rule mono_imp_minimalize_offending_overapprox_minimal)
             apply (metis sinvar_monoI sinvar_mono_imp_negative_delete_edge_mono)
            apply(simp)
           apply(simp)
          apply(simp)
         apply(simp)
        apply(simp)
          
       apply(thin_tac "?x")+
       apply(induction ff keeps G nP rule: minimalize_offending_overapprox.induct)
        apply(simp_all)
      done*)

    
end


text\<open>A version which acts on configured security invariants.
      I.e. there is no type @{typ 'a} for the host attributes in it.\<close>
fun minimalize_offending_overapprox :: "('v graph \<Rightarrow> bool) \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> 
'v graph \<Rightarrow>('v \<times> 'v) list" where
"minimalize_offending_overapprox _ [] keep _ = keep" |
"minimalize_offending_overapprox m (f#fs) keep G = (if m (delete_edges_list G (fs@keep)) then
    minimalize_offending_overapprox m fs keep G
  else
    minimalize_offending_overapprox m fs (f#keep) G
  )"

lemma minimalize_offending_overapprox_boundnP:
shows "minimalize_offending_overapprox (\<lambda>G. m G nP) fs keeps G =
         SecurityInvariant_withOffendingFlows.minimalize_offending_overapprox m fs keeps G nP"
  apply(induction fs arbitrary: keeps)
   apply(simp add: SecurityInvariant_withOffendingFlows.minimalize_offending_overapprox.simps; fail)
  apply(simp add: SecurityInvariant_withOffendingFlows.minimalize_offending_overapprox.simps)
  done

context SecurityInvariant_withOffendingFlows
begin

    text\<open>If there is a violation and there are no offending flows, there does not exist a possibility to fix the violation by 
          tightening the policy. @{thm valid_empty_edges_iff_exists_offending_flows} already hints this.\<close>
    lemma mono_imp_emptyoffending_eq_nevervalid:
       "\<lbrakk> sinvar_mono; wf_graph G; \<not> sinvar G nP; set_offending_flows G nP = {}\<rbrakk> \<Longrightarrow> 
        \<not> (\<exists> F \<subseteq> edges G. sinvar (delete_edges G F) nP)"
    proof -
      assume mono: "sinvar_mono"
      and wfG: "wf_graph G"
      and a1:  "\<not> sinvar G nP"
      and a2: "set_offending_flows G nP = {}"

      from wfG have wfG': "wf_graph \<lparr>nodes = nodes G, edges = edges G\<rparr>" by(simp add:wf_graph_def)

      from a2 set_offending_flows_def have "\<forall>f \<subseteq> edges G. \<not> is_offending_flows_min_set f G nP" by simp
      from this is_offending_flows_min_set_def is_offending_flows_def a1 have notdeleteconj:
        "\<forall>f \<subseteq> edges G. 
          \<not> sinvar (delete_edges G f) nP \<or> 
          \<not> ((\<forall>(e1, e2)\<in>f. \<not> sinvar (add_edge e1 e2 (delete_edges G f)) nP))" 
      by simp
      have "\<forall>f\<subseteq>edges G. \<not> sinvar (delete_edges G f) nP"
      proof (rule allI, rule impI)
        fix f
        assume "f \<subseteq> edges G"
        from this notdeleteconj have 
         "\<not> sinvar (delete_edges G f) nP \<or> 
          \<not> ((\<forall>(e1, e2)\<in>f. \<not> sinvar (add_edge e1 e2 (delete_edges G f)) nP))" by simp
        from this show "\<not> sinvar (delete_edges G f) nP"
          proof
            assume "\<not> sinvar (delete_edges G f) nP" thus "\<not> sinvar (delete_edges G f) nP" .
          next
            assume "\<not> (\<forall>(e1, e2)\<in>f. \<not> sinvar (add_edge e1 e2 (delete_edges G f)) nP)"
            hence "\<exists>(e1,e2)\<in>f. sinvar (add_edge e1 e2 (delete_edges G f)) nP" by(auto)
            from this obtain e1 e2 where e1e2cond: "(e1,e2)\<in>f \<and> sinvar (add_edge e1 e2 (delete_edges G f)) nP" by blast
            
            from \<open>f \<subseteq> edges G\<close> wfG have "finite f" apply(simp add: wf_graph_def) by (metis rev_finite_subset)
            from this obtain listf where listf: "set listf = f \<and> distinct listf" by (metis finite_distinct_list)

            from e1e2cond \<open>f \<subseteq> edges G\<close> have Geq:
            "(add_edge e1 e2 (delete_edges G f)) = \<lparr> nodes = nodes G, edges = edges G - f \<union> {(e1,e2)}\<rparr>"
              apply(simp add: graph_ops wfG')
              apply(clarify)
               using wfG[unfolded wf_graph_def] by force


            from this[symmetric] add_edge_wf[OF delete_edges_wf[OF wfG]] have 
              "wf_graph \<lparr>nodes = nodes G, edges = edges G - f \<union> {(e1, e2)}\<rparr>" by simp
            from mono this  have mono'':
              "\<And> E'. E' \<subseteq> edges G - f \<union> {(e1, e2)} \<Longrightarrow>
                sinvar \<lparr>nodes = nodes G, edges = edges G - f \<union> {(e1, e2)}\<rparr> nP \<Longrightarrow> 
                sinvar \<lparr>nodes = nodes G, edges = E'\<rparr> nP" unfolding sinvar_mono_def by blast
            
            from e1e2cond Geq have "sinvar \<lparr> nodes = nodes G, edges = edges G - f \<union> {(e1,e2)}\<rparr> nP" by simp
            from this mono'' have "sinvar \<lparr> nodes = nodes G, edges = edges G - f\<rparr> nP" by auto
            hence overapprox: "sinvar (delete_edges G f) nP" by (simp add: delete_edges_simp2) 
            (*Interesting, the opposite of what we want to show holds ...*)

            from a1 overapprox have "is_offending_flows f G nP" by(simp add: is_offending_flows_def)
            from this listf have c1: "is_offending_flows (set listf) G nP" by(simp add: is_offending_flows_def)
            from listf \<open>f \<subseteq> edges G\<close> have c2: "set listf \<subseteq> edges G" by simp

            from mono_imp_set_offending_flows_not_empty[OF mono wfG c1 c2 conjunct2[OF listf]] have 
              "set_offending_flows G nP \<noteq> {}" .
            from this a2 have "False" by simp
            (*I knew this can't be!*)

            thus "\<not> sinvar (delete_edges G f) nP" by simp
          qed
      qed
      thus ?thesis by simp
    qed
end
 

(*
text{* Old version of security invariant gave @{term "F \<in> set_offending_flows G nP"} and @{term "sinvar (delete_edges G F) nP"}
  as assumption for @{text "default_secure"}. We can conclude this from mono. *}
context SecurityInvariant_withOffendingFlows
begin
  lemma mono_exists_offending_flows:
  "\<lbrakk> sinvar_mono; wf_graph G; is_offending_flows (set ff) G nP; set ff \<subseteq> edges G; distinct ff \<rbrakk> 
    \<Longrightarrow> \<exists>F. F \<in> set_offending_flows G nP \<and> sinvar (delete_edges G F) nP"
    apply(frule mono_imp_set_offending_flows_not_empty[of G nP ff])
         apply(simp_all add:is_offending_flows_def)
    apply(simp add: set_offending_flows_def)
    apply(erule exE)
    apply(rename_tac exF)
    apply(clarify)
    apply(rule_tac x="exF" in exI)
    apply(rule conjI)
     apply(simp)
    apply(rule conjI)
     apply(simp)
    apply(simp add:is_offending_flows_min_set_def is_offending_flows_def)
  done
end
*)


subsection \<open>Monotonicity of offending flows\<close>
  context SecurityInvariant_preliminaries
  begin
  
    (*todo: simplify proof*)
    text\<open>If there is some @{term "F'"} in the offending flows of a small graph and you have a bigger graph, 
          you can extend @{term "F'"} by some @{term "Fadd"} and minimality in @{term F} is preserved\<close>
    lemma minimality_offending_flows_mono_edges_graph_extend:
    "\<lbrakk> wf_graph \<lparr> nodes = V, edges = E \<rparr>; E' \<subseteq> E; Fadd \<inter> E' = {}; F' \<in> set_offending_flows \<lparr>nodes = V, edges = E'\<rparr> nP \<rbrakk> \<Longrightarrow> 
            (\<forall>(e1, e2)\<in>F'. \<not> sinvar (add_edge e1 e2 (delete_edges \<lparr>nodes = V, edges = E \<rparr> (F' \<union> Fadd))) nP)"
    proof -
      assume a1: "wf_graph \<lparr> nodes = V, edges = E \<rparr>"
      and    a2: "E' \<subseteq> E"
      and    a3: "Fadd \<inter> E' = {}"
      and    a4: "F' \<in> set_offending_flows \<lparr>nodes = V, edges = E'\<rparr> nP"

      from a4 have "F' \<subseteq> E'" by(simp add: set_offending_flows_def)

      obtain Eadd where Eadd_prop: "E' \<union> Eadd = E" and "E' \<inter> Eadd = {}" using a2 by blast

      have Fadd_notinE': "\<And>Fadd. Fadd \<inter> E' = {} \<Longrightarrow>  E' - (F' \<union> Fadd) =  E' - F'" by blast
      from \<open>F' \<subseteq> E'\<close> a1[simplified wf_graph_def] a2 have FinV1: "fst ` F' \<subseteq> V" and FinV2: "snd ` F' \<subseteq> V"
      proof -
        from a1 have "fst ` E \<subseteq> V" by(simp add: wf_graph_def)
        with \<open>F' \<subseteq> E'\<close> a2 show "fst ` F' \<subseteq> V" by fast
        from a1 have "snd ` E \<subseteq> V" by(simp add: wf_graph_def)
        with \<open>F' \<subseteq> E'\<close> a2 show "snd ` F' \<subseteq> V" by fast
      qed
      hence insert_e1_e2_V: "\<forall> (e1, e2) \<in> F'. insert e1 (insert e2 V) = V" by auto
      hence add_edge_F: "\<forall> (e1, e2) \<in> F'. add_edge e1 e2 \<lparr>nodes = V, edges = E' - F' \<rparr> =  \<lparr>nodes = V, edges = (E' - F') \<union> {(e1, e2)}\<rparr>"
        by(simp add: add_edge_def)
         
      have Fadd_notinE': "\<And>Fadd. Fadd \<inter> E' = {} \<Longrightarrow>  E' - (F' \<union> Fadd) =  E' - F'" by blast
       from \<open>F' \<subseteq> E'\<close> this have Fadd_notinF: "\<And>Fadd. Fadd \<inter> E' = {} \<Longrightarrow>  F' \<inter> Fadd = {}" by blast
 
      have Fadd_subseteq_Eadd: "\<And>Fadd. (Fadd \<inter> E' = {} \<and> Fadd \<subseteq> E) = (Fadd \<subseteq> Eadd)"
        proof(rule iffI, goal_cases)
        case 1 thus ?case using Eadd_prop a2 by blast
        next
        case 2 thus ?case using Eadd_prop a2 \<open>E' \<inter> Eadd = {}\<close> by blast
        qed
 
      from a4 have "(\<forall>(e1, e2)\<in>F'. \<not> sinvar (add_edge e1 e2 \<lparr>nodes = V, edges = E' - F'\<rparr>) nP)"
        by(simp add: set_offending_flows_def is_offending_flows_min_set_def delete_edges_simp2)
      with add_edge_F have noteval_F: "\<forall>(e1, e2)\<in>F'. \<not> sinvar \<lparr>nodes = V, edges = (E' - F') \<union> {(e1, e2)}\<rparr> nP"
        by fastforce 

      (*proof rule that preserves the tuple*)
      have tupleBallI: "\<And>A P. (\<And>e1 e2. (e1, e2)\<in>A \<Longrightarrow> P (e1, e2)) \<Longrightarrow> ALL (e1, e2):A. P (e1, e2)" by force
      have "\<forall>(e1, e2)\<in>F'. \<not> sinvar \<lparr>nodes = V, edges = (E - (F' \<union> Fadd)) \<union> {(e1, e2)}\<rparr> nP"
      proof(rule tupleBallI)
        fix e1 e2
        assume f2: "(e1, e2) \<in> F'"
           with a3 have gFadd1: "\<not> sinvar \<lparr>nodes = V, edges = (E' - (F' \<union> Fadd)) \<union> {(e1, e2)}\<rparr> nP"
           using Fadd_notinE' noteval_F by fastforce
     
           from a1 FinV1 FinV2 a3 f2 have gFadd2: 
             "wf_graph \<lparr>nodes = V, edges = (E - (F' \<union> Fadd)) \<union> {(e1, e2)}\<rparr>"
             by(auto simp add: wf_graph_def)
           from a2 a3 f2 have gFadd3: 
                "(E' - (F' \<union> Fadd)) \<union> {(e1, e2)} \<subseteq> (E - (F' \<union> Fadd)) \<union> {(e1, e2)}" by blast
             
           from mono_sinvar[OF gFadd2 gFadd3] gFadd1
           show "\<not> sinvar \<lparr>nodes = V, edges = (E - (F' \<union> Fadd)) \<union> {(e1, e2)}\<rparr> nP" by blast 
       qed
       thus ?thesis
        apply(simp add: delete_edges_simp2 Fadd_notinE' add_edge_def)
        apply(clarify)
        using insert_e1_e2_V by fastforce
    qed

    text\<open>The minimality condition of the offending flows also holds if we increase the graph.\<close>
    corollary minimality_offending_flows_mono_edges_graph: 
      "\<lbrakk> wf_graph \<lparr> nodes = V, edges = E \<rparr>; 
         E' \<subseteq> E;
         F \<in> set_offending_flows \<lparr>nodes = V, edges = E'\<rparr> nP \<rbrakk> \<Longrightarrow>
      \<forall>(e1, e2)\<in>F. \<not> sinvar (add_edge e1 e2 (delete_edges \<lparr>nodes = V, edges = E \<rparr> F)) nP"
      using minimality_offending_flows_mono_edges_graph_extend[where Fadd="{}", simplified] by presburger


    text\<open>all sets in the set of offending flows are monotonic, hence, for a larger graph, they can be extended to match the smaller graph. I.e. everything is monotonic.\<close>
    theorem mono_extend_set_offending_flows: "\<lbrakk> wf_graph \<lparr> nodes = V, edges = E \<rparr>; E' \<subseteq> E; F' \<in> set_offending_flows \<lparr> nodes = V, edges = E' \<rparr> nP \<rbrakk> \<Longrightarrow>
        \<exists> F \<in> set_offending_flows \<lparr> nodes = V, edges = E \<rparr> nP. F' \<subseteq> F"
      proof -
        fix F'V E E'
        assume a1: "wf_graph \<lparr> nodes = V, edges = E \<rparr>"
        and    a2: "E' \<subseteq> E"
        and    a4: "F' \<in> set_offending_flows \<lparr>nodes = V, edges = E'\<rparr> nP"

        \<comment> \<open>Idea: @{text "F = F' \<union> minimize (E - E')"}\<close>
  
        have "\<And>f. wf_graph (delete_edges \<lparr>nodes = V, edges = E\<rparr> f)"
        using delete_edges_wf[OF a1] by fast
        hence wf1: "\<And>f. wf_graph \<lparr>nodes = V, edges = E -f\<rparr>"
        by(simp add: delete_edges_simp2)
  
        obtain Eadd where Eadd_prop: "E' \<union> Eadd = E" and "E' \<inter> Eadd = {}" using a2 by blast
  
        from a4 have "F' \<subseteq> E'" by(simp add: set_offending_flows_def)
  
        from wf1 have wf2: "wf_graph \<lparr>nodes = V, edges = E' - F' \<union> Eadd\<rparr>"
          apply(subgoal_tac "E' - F' \<union> Eadd = E - F'")
           apply fastforce
          using Eadd_prop \<open>E' \<inter> Eadd = {}\<close> \<open>F' \<subseteq> E'\<close> by fast
  
        from a4 have offending_F: "\<not> sinvar \<lparr>nodes = V, edges = E'\<rparr> nP"
          by(simp add: set_offending_flows_def is_offending_flows_min_set_def is_offending_flows_def)
        from this mono_sinvar[OF a1 a2] have 
          goal_noteval: "\<not> sinvar \<lparr>nodes = V, edges = E\<rparr> nP" by blast
  
         from a4 have eval_E_minus_FEadd_simp: "sinvar \<lparr>nodes = V, edges = E' - F'\<rparr> nP"
           by(simp add: set_offending_flows_def is_offending_flows_min_set_def is_offending_flows_def delete_edges_simp2)
        (* moreover have "E - (F' \<union> Eadd) = E' - F'"  using `E' \<inter> Eadd = {}` Eadd_prop by blast
         ultimately have eval_E_minus_FEadd: "sinvar (delete_edges \<lparr>nodes = V, edges = E\<rparr> (F' \<union> Eadd)) nP"
           by(simp add: delete_edges_simp2)*)
  
        show "\<exists> F \<in> set_offending_flows \<lparr> nodes = V, edges = E \<rparr> nP. F' \<subseteq> F"
        proof(cases "\<not> sinvar \<lparr>nodes = V, edges = E' - F' \<union> Eadd\<rparr> nP")
          assume assumption_new_violation: "\<not> sinvar \<lparr>nodes = V, edges = E' - F' \<union> Eadd\<rparr> nP"
          from a1 have "finite Eadd"
            apply(simp add: wf_graph_def)
            using Eadd_prop wf_graph.finiteE by blast
          from this obtain Eadd_list where Eadd_list_prop: "set Eadd_list = Eadd" and "distinct Eadd_list" by (metis finite_distinct_list)
          from a1 have "finite E'"
            apply(simp add: wf_graph_def)
            using Eadd_prop by blast
          from this obtain E'_list where E'_list_prop: "set E'_list = E'" and "distinct E'_list" by (metis finite_distinct_list)
          from \<open>finite E'\<close> \<open>F' \<subseteq> E'\<close> obtain F'_list where "set F'_list = F'" and "distinct F'_list" by (metis finite_distinct_list rev_finite_subset)
    
          have "E' - F' \<union> Eadd - Eadd = E' - F'" using Eadd_prop \<open>E' \<inter> Eadd = {}\<close> \<open>F' \<subseteq> E'\<close> by blast
          with assumption_new_violation eval_E_minus_FEadd_simp have
            "is_offending_flows (set (Eadd_list)) \<lparr>nodes = V, edges = (E' - F') \<union> Eadd\<rparr> nP"
            by (simp add: Eadd_list_prop delete_edges_simp2 is_offending_flows_def)
          from minimalize_offending_overapprox_sound[OF wf2 this _ \<open>distinct Eadd_list\<close>] have
            "is_offending_flows_min_set
              (set (minimalize_offending_overapprox Eadd_list []
                 \<lparr>nodes = V, edges = E' - F' \<union> Eadd\<rparr> nP)) \<lparr>nodes = V, edges = E' - F' \<union> Eadd\<rparr> nP"
            by(simp add: Eadd_list_prop)
          with minimalize_offending_overapprox_subseteq_input[of "Eadd_list" "[]" "\<lparr>nodes = V, edges = E' - F' \<union> Eadd\<rparr>" "nP", simplified Eadd_list_prop]
          obtain Fadd where Fadd_prop: "is_offending_flows_min_set Fadd \<lparr>nodes = V, edges = E' - F' \<union> Eadd\<rparr> nP" and "Fadd \<subseteq> Eadd" by auto
        
          have graph_edges_simp_helper: "E' - F' \<union> Eadd - Fadd =  E - (F' \<union> Fadd)"
            using \<open>E' \<inter> Eadd = {}\<close> Eadd_prop \<open>F' \<subseteq> E'\<close> by blast
        
          from Fadd_prop graph_edges_simp_helper have
            goal_eval_Fadd: "sinvar (delete_edges \<lparr>nodes = V, edges = E\<rparr> (F' \<union> Fadd)) nP" and
            pre_goal_minimal_Fadd: "(\<forall>(e1, e2)\<in>Fadd. \<not> sinvar (add_edge e1 e2 (delete_edges \<lparr>nodes = V, edges = E \<rparr> (F' \<union> Fadd))) nP)"
            by(simp add: is_offending_flows_min_set_def is_offending_flows_def delete_edges_simp2)+
    
          from \<open>E' \<inter> Eadd = {}\<close> \<open>Fadd \<subseteq> Eadd\<close> have "Fadd \<inter> E' = {}" by blast
          from minimality_offending_flows_mono_edges_graph_extend[OF a1 \<open>E' \<subseteq> E\<close> \<open>Fadd \<inter> E' = {}\<close> a4]
          have mono_delete_edges_minimal: "(\<forall>(e1, e2)\<in>F'. \<not> sinvar (add_edge e1 e2 (delete_edges \<lparr>nodes = V, edges = E \<rparr> (F' \<union> Fadd))) nP)" .
    
          from mono_delete_edges_minimal pre_goal_minimal_Fadd have goal_minimal: 
            "\<forall>(e1, e2)\<in>F' \<union> Fadd. \<not> sinvar (add_edge e1 e2 (delete_edges \<lparr>nodes = V, edges = E\<rparr> (F' \<union> Fadd))) nP" by fastforce
    
           from Eadd_prop \<open>Fadd \<subseteq> Eadd\<close> \<open>F' \<subseteq> E'\<close> have goal_subset: "F' \<subseteq> E \<and> Fadd \<subseteq> E" by blast
    
          show "\<exists> F \<in> set_offending_flows \<lparr> nodes = V, edges = E \<rparr> nP. F' \<subseteq> F"
              apply(simp add: set_offending_flows_def is_offending_flows_min_set_def is_offending_flows_def)
              apply(rule_tac x="F' \<union> Fadd" in exI)
              apply(simp add: goal_noteval goal_eval_Fadd goal_minimal goal_subset)
             done
      next
          assume "\<not> \<not> sinvar \<lparr>nodes = V, edges = E' - F' \<union> Eadd\<rparr> nP"
          hence assumption_no_new_violation: "sinvar \<lparr>nodes = V, edges = E' - F' \<union> Eadd\<rparr> nP" by simp
          from this  \<open>F' \<subseteq> E'\<close> \<open>E' \<inter> Eadd = {}\<close>  have "sinvar \<lparr>nodes = V, edges = E - F'\<rparr> nP"
            proof(subst Eadd_prop[symmetric])
              assume a1: "F' \<subseteq> E'"
              assume a2: "E' \<inter> Eadd = {}"
              assume a3: "sinvar \<lparr>nodes = V, edges = E' - F' \<union> Eadd\<rparr> nP"
              have "\<And>x\<^sub>1. x\<^sub>1 \<inter> E' - Eadd = x\<^sub>1 \<inter> E'"
                using a2 Un_Diff_Int by auto
              hence "F' - Eadd = F'"
                using a1 by auto
              hence "{} \<union> (Eadd - F') = Eadd"
                using Int_Diff Un_Diff_Int sup_commute by auto
              thus "sinvar \<lparr>nodes = V, edges = E' \<union> Eadd - F'\<rparr> nP"
                using a3 by (metis Un_Diff sup_bot.left_neutral)
            qed
          from this have goal_eval: "sinvar (delete_edges \<lparr>nodes = V, edges = E\<rparr> F') nP" 
          by(simp add: delete_edges_simp2)
  
          from Eadd_prop \<open>F' \<subseteq> E'\<close> have goal_subset: "F' \<subseteq> E" by(blast)
  
          from minimality_offending_flows_mono_edges_graph[OF a1 a2 a4] 
          have goal_minimal: "(\<forall>(e1, e2)\<in>F'. \<not> sinvar (add_edge e1 e2 (delete_edges \<lparr>nodes = V, edges = E \<rparr> F')) nP)" .
  
          show "\<exists> F \<in> set_offending_flows \<lparr> nodes = V, edges = E \<rparr> nP. F' \<subseteq> F"
              apply(simp add: set_offending_flows_def is_offending_flows_min_set_def is_offending_flows_def)
              apply(rule_tac x="F'" in exI)
              apply(simp add: goal_noteval goal_subset goal_minimal goal_eval)
            done
         qed
    qed


    text\<open>The offending flows are monotonic.\<close>
    corollary offending_flows_union_mono: "\<lbrakk> wf_graph \<lparr> nodes = V, edges = E \<rparr>; E' \<subseteq> E \<rbrakk> \<Longrightarrow> 
      \<Union> (set_offending_flows \<lparr> nodes = V, edges = E' \<rparr> nP) \<subseteq> \<Union> (set_offending_flows \<lparr> nodes = V, edges = E \<rparr> nP)"
      apply(clarify)
      apply(drule(2) mono_extend_set_offending_flows)
      by blast



   (* I guess set_offending_flows = {{e}} does not hold. Consider the Dependability invariant:
      having a wf graph.
      Add an edge s.t. a dependability violation occurs.
      The offending flows now contains the new edge ans all edges on the path from the node with the violation to the end of the new edge. *)
   lemma set_offending_flows_insert_contains_new:
   "\<lbrakk> wf_graph \<lparr> nodes = V, edges = insert e E \<rparr>; set_offending_flows \<lparr>nodes = V, edges = E\<rparr> nP = {}; set_offending_flows \<lparr>nodes = V, edges = insert e E\<rparr> nP \<noteq> {} \<rbrakk> \<Longrightarrow> 
      {e} \<in> set_offending_flows \<lparr>nodes = V, edges = insert e E\<rparr> nP"
     proof -
       assume wfG: "wf_graph \<lparr> nodes = V, edges = insert e E \<rparr>"
       and    a1: "set_offending_flows \<lparr>nodes = V, edges = E\<rparr> nP = {}"
       and    a2: "set_offending_flows \<lparr>nodes = V, edges = insert e E\<rparr> nP \<noteq> {}"

       from a1 a2 have "e \<notin> E" by (metis insert_absorb)
       
       from a1 have a1': "\<forall>F \<subseteq> E. \<not> is_offending_flows_min_set F \<lparr>nodes = V, edges = E\<rparr> nP"
         by(simp add: set_offending_flows_def)
       from a2 have a2': "\<exists>F \<subseteq> insert e E. is_offending_flows_min_set F \<lparr>nodes = V, edges = insert e E\<rparr> nP"
        by(simp add: set_offending_flows_def)

       from wfG have wfG': "wf_graph \<lparr> nodes = V, edges = E \<rparr>" by(simp add:wf_graph_def)

       from a1 defined_offending[OF wfG'] have evalG: "sinvar \<lparr>nodes = V, edges = E \<rparr> nP" by blast
       from sinvar_monoI[unfolded sinvar_mono_def] wfG' this
       have goal_eval: "sinvar \<lparr>nodes = V, edges = E - {e}\<rparr> nP" by (metis Diff_subset)

       from sinvar_no_offending a2 have goal_not_eval: "\<not> sinvar \<lparr>nodes = V, edges = insert e E\<rparr> nP" by blast

       obtain a b where e: "e = (a,b)" by (cases e) blast
       with wfG have insert_e_V: "insert a (insert b V) = V" by(auto simp add: wf_graph_def)

       from a1' a2' have min_set_e: "is_offending_flows_min_set {e} \<lparr>nodes = V, edges = insert e E\<rparr> nP"
        apply(simp add: is_offending_flows_min_set_def is_offending_flows_def add_edge_def delete_edges_simp2 goal_not_eval goal_eval)
        using goal_not_eval by(simp add: e insert_e_V)

       thus "{e} \<in> set_offending_flows \<lparr>nodes = V, edges = insert e E\<rparr> nP"
        by(simp add: set_offending_flows_def)
    qed
     
end

    value "Pow {1::int, 2, 3} \<union> {{8}, {9}}"
    value "\<Union> x\<in>Pow {1::int, 2, 3}. \<Union> y \<in> {{8::int}, {9}}. {x \<union> y}"
    
    (*similar to \<times>_def*)
    \<comment> \<open>combines powerset of A with B\<close>
    definition pow_combine :: "'x set \<Rightarrow> 'x set set \<Rightarrow> 'x set set" where 
      "pow_combine A B \<equiv> (\<Union> X \<in> Pow A. \<Union> Y \<in> B. {X \<union> Y}) \<union> Pow A"

    value "pow_combine {1::int,2} {{5::int, 6}, {8}}"
    value "pow_combine {1::int,2} {}"

    lemma pow_combine_mono: 
    fixes S :: "'a set set"
    and   X :: "'a set"
    and   Y :: "'a set"
    assumes a1: "\<forall> F \<in> S. F \<subseteq> X"
    shows "\<forall> F \<in> pow_combine Y S. F \<subseteq> Y \<union> X"
    apply(simp add: pow_combine_def)
    apply(rule)
    apply(simp)
    by (metis Pow_iff assms sup.coboundedI1 sup.orderE sup.orderI sup_assoc)


    lemma "S \<subseteq> pow_combine X S" by(auto simp add: pow_combine_def)
    lemma "Pow X \<subseteq> pow_combine X S" by(auto simp add: pow_combine_def)

    lemma rule_pow_combine_fixfst: "B \<subseteq> C \<Longrightarrow> pow_combine A B \<subseteq> pow_combine A C"
      by(auto simp add: pow_combine_def)


    value "pow_combine {1::int,2} {{5::int, 6}, {1}} \<subseteq> pow_combine {1::int,2} {{5::int, 6}, {8}}"

    lemma rule_pow_combine_fixfst_Union: "\<Union> B \<subseteq> \<Union> C \<Longrightarrow> \<Union> (pow_combine A B) \<subseteq> \<Union> (pow_combine A C)"
      apply(rule)
      apply(fastforce simp: pow_combine_def)
    done

    (*does the following hold?
      (set_offending_flows \<lparr>nodes = V, edges = E \<union> X\<rparr> nP) \<subseteq> pow_combine X (set_offending_flows \<lparr>nodes = V, edges = E\<rparr> nP)

      I guess not:  ^D  I'm convinced this does not hold!
      Graph:   A -> B -> C
      E = A -> B
      E \<union> X = A -> B -> C
      
      model is A and C are interfering

      set_offending_flows(E \<union> X) = {{(A,B)}, {B,C}}
       set_offending_flows(E) = {}
      pow_combine X set_offending_flows(E) = {{}, {C}}

      the {(A,B)} is the problem here such that subset does not hold.

      It holds if
        \<forall> F \<in> (set_offending_flows \<lparr>nodes = V, edges = E \<union> X\<rparr> nP). F \<subseteq> X
      however, then (set_offending_flows \<lparr>nodes = V, edges = E\<rparr> nP) = {} which renders the whole statement useless
     *)

  context SecurityInvariant_preliminaries
  begin

    lemma offending_partition_subset_empty: 
    assumes a1:"\<forall> F \<in> (set_offending_flows \<lparr>nodes = V, edges = E \<union> X\<rparr> nP). F \<subseteq> X"
    and wfGEX: "wf_graph \<lparr>nodes = V, edges = E \<union> X\<rparr>"
    and disj: "E \<inter> X = {}"
    shows "(set_offending_flows \<lparr>nodes = V, edges = E\<rparr> nP) = {}"
    proof(rule ccontr)
      assume c: "set_offending_flows \<lparr>nodes = V, edges = E\<rparr> nP \<noteq> {}"
      from this obtain F' where F'_prop: "F' \<in> set_offending_flows \<lparr>nodes = V, edges = E\<rparr> nP" by blast
      from F'_prop have "F' \<subseteq> E" using set_offending_flows_def by simp
      from mono_extend_set_offending_flows[OF wfGEX _ F'_prop] have 
        "\<exists>F\<in>set_offending_flows \<lparr>nodes = V, edges = E \<union> X\<rparr> nP. F' \<subseteq> F" by blast
      from this a1 have "F' \<subseteq> X" by fast
      from F'_prop have "{} \<noteq> F'" by (metis empty_offending_contra)
      from \<open>F' \<subseteq> X\<close> \<open>F' \<subseteq> E\<close> disj \<open>{} \<noteq> F'\<close>
      show "False" by blast
    qed

    corollary partitioned_offending_subseteq_pow_combine:
    assumes wfGEX: "wf_graph \<lparr>nodes = V, edges = E \<union> X\<rparr>"
    and disj: "E \<inter> X = {}"
    and partitioned_offending: "\<forall> F \<in> (set_offending_flows \<lparr>nodes = V, edges = E \<union> X\<rparr> nP). F \<subseteq> X" (*offending does not contain E*)
    shows "(set_offending_flows \<lparr>nodes = V, edges = E \<union> X\<rparr> nP) \<subseteq> pow_combine X (set_offending_flows \<lparr>nodes = V, edges = E\<rparr> nP)"
    apply(subst offending_partition_subset_empty[OF partitioned_offending wfGEX disj])
    apply(simp add: pow_combine_def)
    apply(rule)
    apply(simp)
    using partitioned_offending by simp
  end


  context SecurityInvariant_preliminaries
  begin

    text\<open>Knowing that the \<open>\<Union> offending is \<subseteq> X\<close>, removing something from the graphs's edges, 
           it also disappears from the offending flows.\<close>
    lemma Un_set_offending_flows_bound_minus:
    assumes wfG: "wf_graph \<lparr> nodes = V, edges = E \<rparr>"
    and     Foffending: "\<Union>(set_offending_flows \<lparr>nodes = V, edges = E\<rparr> nP) \<subseteq> X"
    shows   "\<Union>(set_offending_flows \<lparr>nodes = V, edges = E - {f}\<rparr> nP) \<subseteq> X - {f}"
    proof -
      from wfG have wfG': "wf_graph \<lparr> nodes = V, edges = E - {f} \<rparr>"
        by(auto simp add: wf_graph_def finite_subset)
      
      from offending_flows_union_mono[OF wfG, where E'="E - {f}"] have 
        "\<Union>(set_offending_flows \<lparr>nodes = V, edges = E - {f}\<rparr> nP) - {f} \<subseteq> \<Union>(set_offending_flows \<lparr>nodes = V, edges = E\<rparr> nP) - {f}" by blast
      also have 
        "\<Union>(set_offending_flows \<lparr>nodes = V, edges = E - {f}\<rparr> nP) \<subseteq> \<Union>(set_offending_flows \<lparr>nodes = V, edges = E - {f}\<rparr> nP) - {f}"
        apply(simp add: set_offending_flows_simp[OF wfG']) by blast
      ultimately have Un_set_offending_flows_minus:
        "\<Union>(set_offending_flows \<lparr>nodes = V, edges = E - {f}\<rparr> nP) \<subseteq> \<Union>(set_offending_flows \<lparr>nodes = V, edges = E \<rparr> nP) - {f}"
        by blast

      from Foffending Un_set_offending_flows_minus 
      show ?thesis by blast
    qed


  text\<open>
    If the offending flows are bound by some @{term X},
    the we can remove all finite @{term "E'"}from the graph's edges
    and the offending flows from the smaller graph are bound by @{term "X - E'"}.
\<close>
    lemma Un_set_offending_flows_bound_minus_subseteq:
    assumes wfG: "wf_graph \<lparr> nodes = V, edges = E \<rparr>"
    and     Foffending: "\<Union> (set_offending_flows \<lparr>nodes = V, edges = E\<rparr> nP) \<subseteq> X"
    shows   "\<Union> (set_offending_flows \<lparr>nodes = V, edges = E - E'\<rparr> nP) \<subseteq> X - E'"
    proof -
      from wfG have wfG': "wf_graph \<lparr> nodes = V, edges = E - E' \<rparr>"
        by(auto simp add: wf_graph_def finite_subset)
      
      from offending_flows_union_mono[OF wfG, where E'="E - E'"] have 
        "\<Union>(set_offending_flows \<lparr>nodes = V, edges = E - E'\<rparr> nP) - E' \<subseteq> \<Union>(set_offending_flows \<lparr>nodes = V, edges = E\<rparr> nP) - E'" by blast
      also have 
        "\<Union>(set_offending_flows \<lparr>nodes = V, edges = E - E'\<rparr> nP) \<subseteq> \<Union>(set_offending_flows \<lparr>nodes = V, edges = E - E'\<rparr> nP) - E'"
        apply(simp add: set_offending_flows_simp[OF wfG']) by blast
      ultimately have Un_set_offending_flows_minus:
        "\<Union> (set_offending_flows \<lparr>nodes = V, edges = E - E'\<rparr> nP) \<subseteq> \<Union> (set_offending_flows \<lparr>nodes = V, edges = E \<rparr> nP) - E'"
        by blast

      from Foffending Un_set_offending_flows_minus 
      show ?thesis by blast
    qed

  corollary Un_set_offending_flows_bound_minus_subseteq': 
    "\<lbrakk> wf_graph \<lparr> nodes = V, edges = E \<rparr>;
    \<Union> (set_offending_flows \<lparr> nodes = V, edges = E \<rparr> nP) \<subseteq> X \<rbrakk> \<Longrightarrow>
    \<Union> (set_offending_flows \<lparr> nodes = V, edges = E - E' \<rparr> nP) \<subseteq> X - E'"
    apply(drule(1) Un_set_offending_flows_bound_minus_subseteq) by blast


  end

end
