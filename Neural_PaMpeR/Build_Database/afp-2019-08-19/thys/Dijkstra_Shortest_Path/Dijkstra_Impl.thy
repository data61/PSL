section \<open>Implementation of Dijkstra's-Algorithm using the ICF\<close>
theory Dijkstra_Impl
imports 
  Dijkstra 
  GraphSpec 
  HashGraphImpl 
  "HOL-Library.Code_Target_Numeral"
begin 
text\<open>
  In this second refinement step, we use interfaces from the 
  Isabelle Collection Framework (ICF) to implement the priority queue and
  the result map. Moreover, we use a graph interface (that is not contained 
  in the ICF, but in this development) to represent the graph.

  The data types of the first refinement step were designed to fit the
  abstract data types of the used ICF-interfaces, which makes this refinement
  quite straightforward.

  Finally, we instantiate the ICF-interfaces by concrete implementations, 
  obtaining an executable algorithm, for that we generate code using 
  Isabelle/HOL's code generator.
\<close>

locale dijkstraC =
  g: StdGraph g_ops + 
  mr: StdMap mr_ops +
  qw: StdUprio qw_ops
  for g_ops :: "('V,'W::weight,'G,'moreg) graph_ops_scheme"
  and mr_ops :: "('V, (('V,'W) path \<times> 'W), 'mr,'more_mr) map_ops_scheme"
  and qw_ops :: "('V ,'W infty,'qw,'more_qw) uprio_ops_scheme" 
begin
  definition "\<alpha>sc == map_prod qw.\<alpha> mr.\<alpha>"
  definition "dinvarC_add == \<lambda>(wl,res). qw.invar wl \<and> mr.invar res"

  definition cdinit :: "'G \<Rightarrow> 'V \<Rightarrow> ('qw\<times>'mr) nres" where
    "cdinit g v0 \<equiv> do {
      wl \<leftarrow> FOREACH (nodes (g.\<alpha> g)) 
        (\<lambda>v wl. RETURN (qw.insert wl v Weight.Infty)) (qw.empty ());
      RETURN (qw.insert wl v0 (Num 0),mr.sng v0 ([],0))
    }"

  definition cpop_min :: "('qw\<times>'mr) \<Rightarrow> ('V\<times>'W infty\<times>('qw\<times>'mr)) nres" where
    "cpop_min \<sigma> \<equiv> do {
      let (wl,res) = \<sigma>; 
      let (v,w,wl')=qw.pop wl;
      RETURN (v,w,(wl',res))
    }"

  definition cupdate :: "'G \<Rightarrow> 'V \<Rightarrow> 'W infty \<Rightarrow> ('qw\<times>'mr) \<Rightarrow> ('qw\<times>'mr) nres"
    where
    "cupdate g v wv \<sigma> = do {
      ASSERT (dinvarC_add \<sigma>);
      let (wl,res)=\<sigma>;
      let pv=mpath' (mr.lookup v res);
      FOREACH (succ (g.\<alpha> g) v) (\<lambda>(w',v') (wl,res).
        if (wv + Num w' < mpath_weight' (mr.lookup v' res)) then do {
          RETURN (qw.insert wl v' (wv+Num w'), 
                  mr.update v' ((v,w',v')#the pv,val wv + w') res)
        } else RETURN (wl,res)
      ) (wl,res)
    }"

  definition cdijkstra where
    "cdijkstra g v0 \<equiv> do {
      \<sigma>0 \<leftarrow> cdinit g v0; 
      (_,res) \<leftarrow> WHILE\<^sub>T (\<lambda>(wl,_). \<not> qw.isEmpty wl) 
            (\<lambda>\<sigma>. do { (v,wv,\<sigma>') \<leftarrow> cpop_min \<sigma>; cupdate g v wv \<sigma>' } )
            \<sigma>0;
      RETURN res
    }"

end

locale dijkstraC_fixg = dijkstraC g_ops mr_ops qw_ops +
  Dijkstra ga v0
  for g_ops :: "('V,'W::weight,'G,'moreg) graph_ops_scheme"
  and mr_ops :: "('V, (('V,'W) path \<times> 'W), 'mr,'more_mr) map_ops_scheme"
  and qw_ops :: "('V ,'W infty,'qw,'more_qw) uprio_ops_scheme" 
  and ga :: "('V,'W) graph" 
  and v0 :: 'V +
  fixes g :: 'G
  assumes g_rel: "(g,ga)\<in>br g.\<alpha> g.invar"
begin
  schematic_goal cdinit_refines: 
    notes [refine] = inj_on_id
    shows "cdinit g v0 \<le>\<Down>?R mdinit"
    using g_rel
    unfolding cdinit_def mdinit_def
    apply (refine_rcg)
    apply (refine_dref_type)
    apply (simp_all add: \<alpha>sc_def dinvarC_add_def refine_rel_defs
      qw.correct mr.correct refine_hsimp)
    done

  schematic_goal cpop_min_refines:
    "(\<sigma>,\<sigma>') \<in> build_rel \<alpha>sc dinvarC_add
      \<Longrightarrow> cpop_min \<sigma> \<le> \<Down>?R (mpop_min \<sigma>')"
    unfolding cpop_min_def mpop_min_def
    apply (refine_rcg)
    apply (refine_dref_type)
    apply (simp add: \<alpha>sc_def dinvarC_add_def refine_hsimp refine_rel_defs)
    apply (simp add: \<alpha>sc_def dinvarC_add_def refine_hsimp refine_rel_defs)
    done

  schematic_goal cupdate_refines:
    notes [refine] = inj_on_id
    shows "(\<sigma>,\<sigma>')\<in>build_rel \<alpha>sc dinvarC_add \<Longrightarrow> v=v' \<Longrightarrow> wv=wv' \<Longrightarrow> 
    cupdate g v wv \<sigma> \<le> \<Down>?R (mupdate v' wv' \<sigma>')"
    unfolding cupdate_def mupdate_def
    using g_rel
    apply (refine_rcg)
    apply (refine_dref_type)
    apply (simp_all add: \<alpha>sc_def dinvarC_add_def refine_rel_defs 
      qw.correct mr.correct refine_hsimp)
    done

  lemma cdijkstra_refines: 
    "cdijkstra g v0 \<le> \<Down>(build_rel mr.\<alpha> mr.invar) mdijkstra"
  proof -
    note [refine] = cdinit_refines cpop_min_refines cupdate_refines
    show ?thesis
      unfolding cdijkstra_def mdijkstra_def
      using g_rel
      apply (refine_rcg)

      apply (auto
        split: prod.split prod.split_asm 
        simp add: qw.correct mr.correct dinvarC_add_def \<alpha>sc_def refine_hsimp
          refine_rel_defs)
      done
  qed
end

context dijkstraC
begin

  thm g.nodes_it_is_iterator

  schematic_goal idijkstra_refines_aux: 
    assumes "g.invar g"
    shows "RETURN ?f \<le> cdijkstra g v0"
    using assms
    unfolding cdijkstra_def cdinit_def cpop_min_def cupdate_def 
    apply (refine_transfer)
    done

  concrete_definition idijkstra for g ?v0.0 uses idijkstra_refines_aux 

  lemma idijkstra_refines: 
    assumes "g.invar g"
    shows "RETURN (idijkstra g v0) \<le> cdijkstra g v0"
    using assms
    by (rule idijkstra.refine) 

end

text \<open>
  The following theorem states correctness of the algorithm independent
  from the refinement framework.

  Intuitively, the first goal states that the abstraction of the returned 
  result is correct, the second goal states that the result
  datastructure satisfies its invariant, and the third goal states 
  that the cached weights in the returned result are correct.

  Note that this is the main theorem for a user of Dijkstra's algorithm in some 
  bigger context. It may also be specialized for concrete instances of the
  implementation, as exemplarily done below.
\<close>
theorem (in dijkstraC_fixg) idijkstra_correct:
  shows
  "weighted_graph.is_shortest_path_map ga v0 (\<alpha>r (mr.\<alpha> (idijkstra g v0)))" 
    (is ?G1)
  and "mr.invar (idijkstra g v0)" (is ?G2) 
  and "Dijkstra.res_invarm (mr.\<alpha> (idijkstra g v0))" (is ?G3)
proof -
  from g_rel have I: "g.invar g" by (simp add: refine_rel_defs)

  note idijkstra_refines[OF I]
  also note cdijkstra_refines
  also note mdijkstra_refines
  finally have Z: "RETURN (idijkstra g v0) \<le> 
    \<Down>(build_rel (\<alpha>r \<circ> mr.\<alpha>) (\<lambda>m. mr.invar m \<and> res_invarm (mr.\<alpha> m))) 
      dijkstra'"
    apply (subst (asm) conc_fun_chain)
    apply (simp only: br_chain)
    done
  also note dijkstra'_refines[simplified]
  also note dijkstra_correct 
  finally show ?G1 ?G2 ?G3 
    by (auto elim: RETURN_ref_SPECD simp: refine_rel_defs)
qed


theorem (in dijkstraC) idijkstra_correct:
  assumes INV: "g.invar g"
  assumes V0: "v0 \<in> nodes (g.\<alpha> g)"
  assumes nonneg_weights: "\<And>v w v'. (v,w,v')\<in>edges (g.\<alpha> g) \<Longrightarrow> 0\<le>w"
  shows 
  "weighted_graph.is_shortest_path_map (g.\<alpha> g) v0 
      (Dijkstra.\<alpha>r (mr.\<alpha> (idijkstra g v0)))" (is ?G1)
  and "Dijkstra.res_invarm (mr.\<alpha> (idijkstra g v0))" (is ?G2)
proof -
  interpret gv: valid_graph "g.\<alpha> g" using g.valid INV .

  interpret dcg: dijkstraC_fixg g_ops mr_ops qw_ops "g.\<alpha> g" v0 g
    apply (rule dijkstraC_fixg.intro)
    apply unfold_locales 
    apply (simp_all add: hlg.finite INV V0 hlg_ops_def 
      nonneg_weights refine_rel_defs)
    done

  from dcg.idijkstra_correct show ?G1 ?G2 by simp_all
qed


text \<open>
  Example instantiation with HashSet.based graph, 
  red-black-tree based result map, and finger-tree based priority queue.
\<close>
setup Locale_Code.open_block
interpretation hrf: dijkstraC hlg_ops rm_ops aluprioi_ops
  by unfold_locales
setup Locale_Code.close_block



definition "hrf_dijkstra \<equiv> hrf.idijkstra"
lemmas hrf_dijkstra_correct = hrf.idijkstra_correct[folded hrf_dijkstra_def]

export_code hrf_dijkstra checking SML
export_code hrf_dijkstra in OCaml
export_code hrf_dijkstra in Haskell
export_code hrf_dijkstra checking Scala

definition hrfn_dijkstra :: "(nat,nat) hlg \<Rightarrow> _" 
  where "hrfn_dijkstra \<equiv> hrf_dijkstra"

export_code hrfn_dijkstra in SML

lemmas hrfn_dijkstra_correct = 
  hrf_dijkstra_correct[where ?'a = nat and ?'b = nat, folded hrfn_dijkstra_def]

term hrfn_dijkstra
term hlg.from_list

definition "test_hrfn_dijkstra 
  \<equiv> rm.to_list 
    (hrfn_dijkstra (hlg.from_list ([0..<4],[(0,3,1),(0,4,2),(2,1,3),(1,4,3)])) 0)"

ML_val \<open>
  @{code test_hrfn_dijkstra}

\<close>

end
