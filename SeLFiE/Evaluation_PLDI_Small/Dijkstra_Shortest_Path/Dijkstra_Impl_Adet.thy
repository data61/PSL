section \<open>Implementation of Dijkstra's-Algorithm using Automatic Determinization\<close>
theory Dijkstra_Impl_Adet
imports 
  Dijkstra 
  GraphSpec 
  HashGraphImpl 
  Collections.Refine_Dflt_ICF
  "HOL-Library.Code_Target_Numeral"
begin 


subsection \<open>Setup\<close>

subsubsection \<open>Infinity\<close>
definition infty_rel_internal_def: 
  "infty_rel R \<equiv> {(Num a, Num a')| a a'. (a,a')\<in>R} \<union> {(Infty,Infty)}"
lemma infty_rel_def[refine_rel_defs]: 
  "\<langle>R\<rangle>infty_rel = {(Num a, Num a')| a a'. (a,a')\<in>R} \<union> {(Infty,Infty)}"
  unfolding infty_rel_internal_def relAPP_def by simp

lemma infty_relI: 
  "(Infty,Infty)\<in>\<langle>R\<rangle>infty_rel"
  "(a,a')\<in>R \<Longrightarrow> (Num a, Num a')\<in>\<langle>R\<rangle>infty_rel"
  unfolding infty_rel_def by auto

lemma infty_relE:
  assumes "(x,x')\<in>\<langle>R\<rangle>infty_rel"
  obtains "x=Infty" and "x'=Infty"
  | a a' where "x=Num a" and "x'=Num a'" and "(a,a')\<in>R"
  using assms
  unfolding infty_rel_def
  by auto
  
lemma infty_rel_simps[simp]:
  "(Infty,x')\<in>\<langle>R\<rangle>infty_rel \<longleftrightarrow> x'=Infty"
  "(x,Infty)\<in>\<langle>R\<rangle>infty_rel \<longleftrightarrow> x=Infty"
  "(Num a, Num a')\<in>\<langle>R\<rangle>infty_rel \<longleftrightarrow> (a,a')\<in>R"
  unfolding infty_rel_def by auto

lemma infty_rel_sv[relator_props]: 
  "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>infty_rel)"
  unfolding infty_rel_def
  by (auto intro: single_valuedI dest: single_valuedD)

lemma infty_rel_id[simp, relator_props]: "\<langle>Id\<rangle>infty_rel = Id"
  apply rule
  apply (auto elim: infty_relE) []
  apply safe
  apply (case_tac b) by auto

consts i_infty :: "interface \<Rightarrow> interface"
lemmas [autoref_rel_intf] = REL_INTFI[of infty_rel i_infty]

lemma autoref_infty[param,autoref_rules]:
  "(Infty,Infty)\<in>\<langle>R\<rangle>infty_rel"
  "(Num,Num)\<in>R\<rightarrow>\<langle>R\<rangle>infty_rel"
  "(case_infty,case_infty)\<in>Rr\<rightarrow>(R\<rightarrow>Rr)\<rightarrow>\<langle>R\<rangle>infty_rel\<rightarrow>Rr"
  "(rec_infty,rec_infty)\<in>Rr\<rightarrow>(R\<rightarrow>Rr)\<rightarrow>\<langle>R\<rangle>infty_rel\<rightarrow>Rr"
  unfolding infty_rel_def
  by (auto dest: fun_relD)
  
definition [simp]: "is_Infty x \<equiv> case x of Infty \<Rightarrow> True | _ \<Rightarrow> False"

context begin interpretation autoref_syn .
lemma pat_is_Infty[autoref_op_pat]: 
  "x=Infty \<equiv> (OP is_Infty :::\<^sub>i \<langle>I\<rangle>\<^sub>ii_infty \<rightarrow>\<^sub>i i_bool)$x"
  "Infty=x \<equiv> (OP is_Infty :::\<^sub>i \<langle>I\<rangle>\<^sub>ii_infty \<rightarrow>\<^sub>i i_bool)$x"
  by (auto intro!: eq_reflection split: infty.splits)
end

lemma autoref_is_Infty[autoref_rules]: 
  "(is_Infty, is_Infty)\<in>\<langle>R\<rangle>infty_rel \<rightarrow> bool_rel"
  by (auto split: infty.splits)

definition "infty_eq eq v1 v2 \<equiv> 
  case (v1,v2) of
    (Infty,Infty) \<Rightarrow> True
  | (Num a1, Num a2) \<Rightarrow> eq a1 a2
  | _ \<Rightarrow> False"

lemma infty_eq_autoref[autoref_rules (overloaded)]:
  "\<lbrakk> GEN_OP eq (=) (R\<rightarrow>R\<rightarrow>bool_rel) \<rbrakk> 
  \<Longrightarrow> (infty_eq eq,(=))\<in>\<langle>R\<rangle>infty_rel\<rightarrow>\<langle>R\<rangle>infty_rel\<rightarrow>bool_rel"
  unfolding infty_eq_def[abs_def]
  by (auto split: infty.splits dest: fun_relD elim!: infty_relE)

lemma infty_eq_expand[autoref_struct_expand]: "(=) = infty_eq (=)"
  by (auto intro!: ext simp: infty_eq_def split: infty.splits)

context begin interpretation autoref_syn .
lemma infty_val_autoref[autoref_rules]: 
  "\<lbrakk>SIDE_PRECOND (x\<noteq>Infty); (xi,x)\<in>\<langle>R\<rangle>infty_rel\<rbrakk> 
  \<Longrightarrow> (val xi,(OP val ::: \<langle>R\<rangle>infty_rel \<rightarrow> R) $ x)\<in>R"
  apply (cases x) 
  apply (auto elim: infty_relE)
  done
end

definition infty_plus where
  "infty_plus pl a b \<equiv> case (a,b) of (Num a, Num b) \<Rightarrow> Num (pl a b) | _ \<Rightarrow> Infty "

lemma infty_plus_param[param]:
  "(infty_plus,infty_plus) \<in> (R\<rightarrow>R\<rightarrow>R) \<rightarrow> \<langle>R\<rangle>infty_rel \<rightarrow> \<langle>R\<rangle>infty_rel \<rightarrow> \<langle>R\<rangle>infty_rel"
  unfolding infty_plus_def[abs_def]
  by parametricity

lemma infty_plus_eq_plus: "infty_plus (+) = (+)"
  unfolding infty_plus_def[abs_def] 
  by (auto intro!: ext split: infty.split)
  

lemma infty_plus_autoref[autoref_rules]:
  "GEN_OP pl (+) (R\<rightarrow>R\<rightarrow>R) 
  \<Longrightarrow> (infty_plus pl,(+)) \<in> \<langle>R\<rangle>infty_rel \<rightarrow> \<langle>R\<rangle>infty_rel \<rightarrow> \<langle>R\<rangle>infty_rel"
  apply (fold infty_plus_eq_plus)
  apply simp
  apply parametricity
  done

subsubsection \<open>Graph\<close>
consts i_graph :: "interface \<Rightarrow> interface \<Rightarrow> interface"

definition graph_more_rel_internal_def:
  "graph_more_rel Rm Rv Rw \<equiv> { (g,g'). 
    (graph.nodes g, graph.nodes g')\<in>\<langle>Rv\<rangle>set_rel     
  \<and> (graph.edges g, graph.edges g')\<in>\<langle>\<langle>Rv,\<langle>Rw,Rv\<rangle>prod_rel\<rangle>prod_rel\<rangle>set_rel
  \<and> (graph.more g, graph.more g')\<in>Rm}"

lemma graph_more_rel_def[refine_rel_defs]: 
  "\<langle>Rm,Rv,Rw\<rangle>graph_more_rel \<equiv> { (g,g'). 
    (graph.nodes g, graph.nodes g')\<in>\<langle>Rv\<rangle>set_rel     
  \<and> (graph.edges g, graph.edges g')\<in>\<langle>\<langle>Rv,\<langle>Rw,Rv\<rangle>prod_rel\<rangle>prod_rel\<rangle>set_rel
  \<and> (graph.more g, graph.more g')\<in>Rm}"
  unfolding relAPP_def graph_more_rel_internal_def by simp
  
abbreviation "graph_rel \<equiv> \<langle>unit_rel\<rangle>graph_more_rel"
lemmas graph_rel_def = graph_more_rel_def[where Rm=unit_rel, simplified]

lemma graph_rel_id[simp]: "\<langle>Id,Id\<rangle>graph_rel = Id"
  unfolding graph_rel_def by auto

lemma graph_more_rel_sv[relator_props]: 
  "\<lbrakk>single_valued Rm; single_valued Rv; single_valued Rw\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rv,Rw\<rangle>graph_more_rel)"
  unfolding graph_more_rel_def
  apply (rule single_valuedI, clarsimp)
  apply (rule graph.equality)
  apply (erule (1) single_valuedD[rotated], tagged_solver)+
  done

lemma [autoref_itype]: 
  "graph.nodes ::\<^sub>i \<langle>Iv,Iw\<rangle>\<^sub>ii_graph \<rightarrow>\<^sub>i \<langle>Iv\<rangle>\<^sub>ii_set" 
  by simp_all

thm is_map_to_sorted_list_def

definition "nodes_to_list g \<equiv> it_to_sorted_list (\<lambda>_ _. True) (graph.nodes g)"
lemma nodes_to_list_itype[autoref_itype]: "nodes_to_list ::\<^sub>i \<langle>Iv,Iw\<rangle>\<^sub>ii_graph \<rightarrow>\<^sub>i \<langle>\<langle>Iv\<rangle>\<^sub>ii_list\<rangle>\<^sub>ii_nres" by simp
lemma nodes_to_list_pat[autoref_op_pat]: "it_to_sorted_list (\<lambda>_ _. True) (graph.nodes g) \<equiv> nodes_to_list g"
  unfolding nodes_to_list_def by simp

definition "succ_to_list g v \<equiv> it_to_sorted_list (\<lambda>_ _. True) (Graph.succ g v)"
lemma succ_to_list_itype[autoref_itype]: 
  "succ_to_list ::\<^sub>i \<langle>Iv,Iw\<rangle>\<^sub>ii_graph \<rightarrow>\<^sub>i Iv \<rightarrow>\<^sub>i \<langle>\<langle>\<langle>Iw,Iv\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_list\<rangle>\<^sub>ii_nres" by simp
lemma succ_to_list_pat[autoref_op_pat]: "it_to_sorted_list (\<lambda>_ _. True) (Graph.succ g v) \<equiv> succ_to_list g v"
  unfolding succ_to_list_def by simp

context graph begin
  definition rel_def_internal: "rel Rv Rw \<equiv> br \<alpha> invar O \<langle>Rv,Rw\<rangle>graph_rel"
  lemma rel_def: "\<langle>Rv,Rw\<rangle>rel \<equiv> br \<alpha> invar O \<langle>Rv,Rw\<rangle>graph_rel"
    unfolding relAPP_def rel_def_internal by simp

  lemma rel_id[simp]: "\<langle>Id,Id\<rangle>rel = br \<alpha> invar" by (simp add: rel_def)

  lemma rel_sv[relator_props]: 
    "\<lbrakk>single_valued Rv; single_valued Rw\<rbrakk> \<Longrightarrow> single_valued (\<langle>Rv,Rw\<rangle>rel)"
    unfolding rel_def
    by tagged_solver

  lemmas [autoref_rel_intf] = REL_INTFI[of rel i_graph]
end

lemma (in graph_nodes_it) autoref_nodes_it[autoref_rules]: 
  assumes ID: "PREFER_id Rv"
  shows "(\<lambda>s. RETURN (it_to_list nodes_it s),nodes_to_list) \<in> \<langle>Rv,Rw\<rangle>rel \<rightarrow> \<langle>\<langle>Rv\<rangle>list_rel\<rangle>nres_rel"
  unfolding nodes_to_list_def[abs_def]
proof (intro fun_relI nres_relI)
  fix s s'
  from ID have [simp]: "Rv = Id" by simp

  assume "(s,s')\<in>\<langle>Rv,Rw\<rangle>rel"
  hence INV: "invar s" and [simp]: "nodes s' = nodes (\<alpha> s)" unfolding rel_def 
    by (auto simp add: br_def graph_rel_def)

  obtain l where 
    [simp]: "distinct l" "nodes (\<alpha> s) = set l" "it_to_list nodes_it s = l" 
    unfolding it_to_list_def
    by (metis nodes_it_correct[OF INV, unfolded set_iterator_def set_iterator_genord_def] 
      foldli_snoc_id self_append_conv2)
  
  show "RETURN (it_to_list nodes_it s)
          \<le> \<Down> (\<langle>Rv\<rangle>list_rel) (it_to_sorted_list (\<lambda>_ _. True) (nodes s'))"
    by (simp add: it_to_sorted_list_def)
qed


lemma (in graph_succ_it) autoref_succ_it[autoref_rules]: 
  assumes ID: "PREFER_id Rv" "PREFER_id Rw"
  shows "(\<lambda>s v. RETURN (it_to_list (\<lambda>s. succ_it s v) s),succ_to_list) 
    \<in> \<langle>Rv,Rw\<rangle>rel \<rightarrow> Rv \<rightarrow> \<langle>\<langle>\<langle>Rw,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>nres_rel"
  unfolding succ_to_list_def[abs_def]
proof (intro fun_relI nres_relI)
  fix s s' v v'
  from ID have [simp]: "Rv = Id" "Rw=Id" by simp_all

  assume "(v,v')\<in>Rv" hence [simp]: "v'=v" by simp

  assume "(s,s')\<in>\<langle>Rv,Rw\<rangle>rel"
  hence INV: "invar s" and [simp]: "Graph.succ s' = Graph.succ (\<alpha> s)" unfolding rel_def 
    by (auto simp add: br_def graph_rel_def succ_def)

  obtain l where 
    [simp]: "distinct l" "succ (\<alpha> s) v = set l" "it_to_list (\<lambda>s. succ_it s v) s = l" 
    unfolding it_to_list_def
    by (metis succ_it_correct[OF INV, unfolded set_iterator_def set_iterator_genord_def] 
      foldli_snoc_id self_append_conv2)
  
  show "RETURN (it_to_list (\<lambda>s. succ_it s v) s)
          \<le> \<Down> (\<langle>\<langle>Rw,Rv\<rangle>prod_rel\<rangle>list_rel) (it_to_sorted_list (\<lambda>_ _. True) (succ s' v'))"
    by (simp add: it_to_sorted_list_def)
qed

subsection \<open>Refinement\<close>

locale dijkstraC =
  g: StdGraph g_ops + 
  mr: StdMap mr_ops +
  qw: StdUprio qw_ops 
  for g_ops :: "('V,'W::weight,'G,'moreg) graph_ops_scheme"
  and mr_ops :: "('V, (('V,'W) path \<times> 'W), 'mr,'more_mr) map_ops_scheme"
  and qw_ops :: "('V ,'W infty,'qw,'more_qw) uprio_ops_scheme" 
begin
end

locale dijkstraC_fixg = dijkstraC g_ops mr_ops qw_ops +
  Dijkstra ga v0 
  for g_ops :: "('V,'W::weight,'G,'moreg) graph_ops_scheme"
  and mr_ops :: "('V, (('V,'W) path \<times> 'W), 'mr,'more_mr) map_ops_scheme"
  and qw_ops :: "('V ,'W infty,'qw,'more_qw) uprio_ops_scheme" 
  and ga::"('V,'W) graph" and "v0"::'V and g :: 'G+
  assumes ga_trans: "(g,ga)\<in>br g.\<alpha> g.invar"
begin
  abbreviation "v_rel \<equiv> Id :: ('V\<times>'V) set"
  abbreviation "w_rel \<equiv> Id :: ('W\<times>'W) set"

  definition i_node :: interface where "i_node \<equiv> undefined"
  definition i_weight :: interface where "i_weight \<equiv> undefined"

  lemmas [autoref_rel_intf] = REL_INTFI[of v_rel i_node]
  lemmas [autoref_rel_intf] = REL_INTFI[of w_rel i_weight]
  
  lemma weight_plus_autoref[autoref_rules]: 
    "(0,0) \<in> w_rel"
    "((+),(+)) \<in> w_rel \<rightarrow> w_rel \<rightarrow> w_rel" 
    "((+),(+)) \<in> \<langle>w_rel\<rangle>infty_rel \<rightarrow> \<langle>w_rel\<rangle>infty_rel \<rightarrow> \<langle>w_rel\<rangle>infty_rel" 
    "((<),(<)) \<in> \<langle>w_rel\<rangle>infty_rel \<rightarrow> \<langle>w_rel\<rangle>infty_rel \<rightarrow> bool_rel" 
    by simp_all

  lemma [autoref_rules]: "(g,ga)\<in>\<langle>v_rel,w_rel\<rangle>g.rel" using ga_trans
    by (simp add: g.rel_def)
   
  lemma [autoref_rules]: "(v0,v0)\<in>v_rel" by simp

  term mpath_weight'
  lemma [autoref_rules]: 
    "(mpath_weight',mpath_weight') 
      \<in> \<langle>\<langle>v_rel\<times>\<^sub>rw_rel\<times>\<^sub>rv_rel\<rangle>list_rel\<times>\<^sub>rw_rel\<rangle>option_rel \<rightarrow> \<langle>w_rel\<rangle>infty_rel"
    "(mpath', mpath') 
      \<in> \<langle>\<langle>v_rel\<times>\<^sub>rw_rel\<times>\<^sub>rv_rel\<rangle>list_rel\<times>\<^sub>rw_rel\<rangle>option_rel 
        \<rightarrow> \<langle>\<langle>v_rel\<times>\<^sub>rw_rel\<times>\<^sub>rv_rel\<rangle>list_rel\<rangle>option_rel"
    by auto

  term mdinit

  lemmas [autoref_tyrel] = 
    ty_REL[where R=v_rel]
    ty_REL[where R=w_rel]
    ty_REL[where R="\<langle>w_rel\<rangle>infty_rel"]
    ty_REL[where R="\<langle>v_rel,\<langle>w_rel\<rangle>infty_rel\<rangle>qw.rel"]
    ty_REL[where R="\<langle>v_rel,\<langle>v_rel\<times>\<^sub>rw_rel\<times>\<^sub>rv_rel\<rangle>list_rel\<times>\<^sub>rw_rel\<rangle>mr.rel"]
    ty_REL[where R="\<langle>v_rel\<times>\<^sub>rw_rel\<times>\<^sub>rv_rel\<rangle>list_rel"]
    
  lemmas [autoref_op_pat] = uprio_pats[where 'e = 'V and 'a = "'W infty"]


  schematic_goal cdijkstra_refines_aux:
    shows "(?c::?'c, 
      mdijkstra
    ) \<in> ?R"
    apply (simp only: mdijkstra_def mdinit_def mpop_min_def[abs_def] mupdate_def)

    using [[goals_limit = 1]]

    apply (fold op_map_empty_def[where 'a="'V" and 'b = "('V\<times>'W\<times>'V) list \<times> 'W"])
    apply (fold op_uprio_empty_def[where 'a="'V" and 'b = "'W infty"])

    (*using [[autoref_trace_intf_unif]]*)
    using [[autoref_trace_failed_id]]
  
    apply (autoref_monadic (plain,trace))
    done

end

context dijkstraC 
begin

  concrete_definition cdijkstra for g ?v0.0  
    uses dijkstraC_fixg.cdijkstra_refines_aux
    [of g_ops mr_ops qw_ops]

    term cdijkstra
end

context dijkstraC_fixg
begin

  term cdijkstra
  term mdijkstra

  lemma cdijkstra_refines: 
    "RETURN (cdijkstra g v0) \<le> \<Down>(build_rel mr.\<alpha> mr.invar) mdijkstra"
    apply (rule cdijkstra.refine[THEN nres_relD, simplified])
    apply unfold_locales
    done

  theorem cdijkstra_correct:
    shows
    "weighted_graph.is_shortest_path_map ga v0 (\<alpha>r (mr.\<alpha> (cdijkstra g v0)))"
    (is ?G1)
    and "mr.invar (cdijkstra g v0)" (is ?G2) 
    and "res_invarm (mr.\<alpha> (cdijkstra g v0))" (is ?G3)
  proof -
    note cdijkstra_refines
    also note mdijkstra_refines
    finally have Z: "RETURN (cdijkstra g v0) \<le> 
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

end

theorem (in dijkstraC) cdijkstra_correct:
  assumes INV: "g.invar g"
  assumes V0: "v0 \<in> nodes (g.\<alpha> g)"
  assumes nonneg_weights: "\<And>v w v'. (v,w,v')\<in>edges (g.\<alpha> g) \<Longrightarrow> 0\<le>w"
  shows 
  "weighted_graph.is_shortest_path_map (g.\<alpha> g) v0 
      (Dijkstra.\<alpha>r (mr.\<alpha> (cdijkstra g v0)))" (is ?G1)
  and "Dijkstra.res_invarm (mr.\<alpha> (cdijkstra g v0))" (is ?G2)
proof -
  interpret hlgv: valid_graph "g.\<alpha> g" using g.valid INV .

  interpret dc: dijkstraC_fixg g_ops mr_ops qw_ops "g.\<alpha> g" v0
    apply unfold_locales 
    apply (simp_all 
      add: hlg.finite INV V0 hlg_ops_def nonneg_weights refine_rel_defs)
    done

  from dc.cdijkstra_correct show ?G1 ?G2 by auto
qed

text \<open>
  Example instantiation with HashSet.based graph, 
  red-black-tree based result map, and finger-tree based priority queue.
\<close>
setup Locale_Code.open_block
interpretation hrf: dijkstraC hlg_ops rm_ops aluprioi_ops
  by unfold_locales
setup Locale_Code.close_block

definition "hrf_dijkstra \<equiv> hrf.cdijkstra"
lemmas hrf_dijkstra_correct = hrf.cdijkstra_correct[folded hrf_dijkstra_def]

export_code hrf_dijkstra checking SML
export_code hrf_dijkstra in OCaml
export_code hrf_dijkstra in Haskell
export_code hrf_dijkstra checking Scala

definition hrfn_dijkstra :: "(nat,nat) hlg \<Rightarrow> _" 
  where "hrfn_dijkstra \<equiv> hrf_dijkstra"

export_code hrfn_dijkstra checking SML

lemmas hrfn_dijkstra_correct = 
  hrf_dijkstra_correct[where ?'a = nat and ?'b = nat, folded hrfn_dijkstra_def]

end
