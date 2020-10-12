section \<open>Generic Algorithms for Graphs\<close>
theory GraphGA
imports 
  GraphSpec 
begin

  definition gga_from_list :: 
    "('V,'W,'G) graph_empty \<Rightarrow> ('V,'W,'G) graph_add_node 
      \<Rightarrow> ('V,'W,'G) graph_add_edge 
    \<Rightarrow> ('V,'W,'G) graph_from_list"
    where 
    "gga_from_list e a u l \<equiv> 
      let (nl,el) = l;
        g1 = foldl (\<lambda>g v. a v g) (e ()) nl
      in foldl (\<lambda>g (v,e,v'). u v e v' g) g1 el"
  
  lemma gga_from_list_correct:
    fixes \<alpha> :: "'G \<Rightarrow> ('V,'W) graph"
    assumes "graph_empty \<alpha> invar e"
    assumes "graph_add_node \<alpha> invar a"
    assumes "graph_add_edge \<alpha> invar u"
    shows "graph_from_list \<alpha> invar (gga_from_list e a u)"
  proof -
    interpret 
      graph_empty \<alpha> invar e + 
      graph_add_node \<alpha> invar a + 
      graph_add_edge \<alpha> invar u
      by fact+

    {
      fix nl el
      define g1 where "g1 = foldl (\<lambda>g v. a v g) (e ()) nl"
      define g2 where "g2 = foldl (\<lambda>g (v,e,v'). u v e v' g) g1 el"
      have "invar g1 \<and> \<alpha> g1 = \<lparr> nodes = set nl, edges = {} \<rparr>"
        unfolding g1_def
        by (induct nl rule: rev_induct)
           (auto simp: empty_correct add_node_correct empty_def add_node_def)
      hence "invar g2 
        \<and> \<alpha> g2 = \<lparr> nodes = set nl \<union> fst`set el \<union> snd`snd`set el,
                    edges = set el \<rparr>"
        unfolding g2_def
        by (induct el rule: rev_induct) (auto simp: add_edge_correct add_edge_def)
      hence "invar g2 \<and> adjl_\<alpha> (nl,el) = \<alpha> g2"
        unfolding adjl_\<alpha>_def by auto
    }
    thus ?thesis
      unfolding gga_from_list_def [abs_def]
      apply unfold_locales
      apply auto
      done
  qed
      
  term map_iterator_product


  locale gga_edges_it_defs =
    graph_nodes_it_defs nodes_list_it +
    graph_succ_it_defs succ_list_it
    for nodes_list_it :: "('V,'W,'V list,'G) graph_nodes_it"
    and succ_list_it :: "('V,'W,('W\<times>'V) list,'G) graph_succ_it"
  begin
    definition gga_edges_list_it ::
      "('V,'W,('V\<times>'W\<times>'V) list,'G) graph_edges_it"
      where "gga_edges_list_it G \<equiv> set_iterator_product 
        (nodes_it G) (succ_it G)"
    local_setup \<open>Locale_Code.lc_decl_del @{term gga_edges_list_it}\<close>
  end
  setup \<open>
    (Record_Intf.add_unf_thms_global @{thms 
      gga_edges_it_defs.gga_edges_list_it_def[abs_def]
    })
\<close> 

  locale gga_edges_it = gga_edges_it_defs nodes_list_it succ_list_it 
    + graph \<alpha> invar
    + graph_nodes_it \<alpha> invar nodes_list_it
    + graph_succ_it \<alpha> invar succ_list_it
    for \<alpha> :: "'G \<Rightarrow> ('V,'W) graph" 
    and invar 
    and nodes_list_it :: "('V,'W,'V list,'G) graph_nodes_it"
    and succ_list_it :: "('V,'W,('W\<times>'V) list,'G) graph_succ_it"  
  begin
    lemma gga_edges_list_it_impl:
      shows "graph_edges_it \<alpha> invar gga_edges_list_it"
    proof
      fix g
      assume INV: "invar g"

      from set_iterator_product_correct[OF 
        nodes_it_correct[OF INV] succ_it_correct[OF INV]]
      have "set_iterator (set_iterator_product (nodes_it g) (\<lambda>v. succ_it g v))
        (SIGMA v:nodes (\<alpha> g). succ (\<alpha> g) v)
        " .
      also have "(SIGMA v:nodes (\<alpha> g). succ (\<alpha> g) v) = edges (\<alpha> g)" 
        unfolding succ_def 
        by (auto dest: valid_graph.E_validD[OF valid[OF INV]])

      finally show "set_iterator (gga_edges_list_it g) (edges (\<alpha> g))"
        unfolding gga_edges_list_it_def .
    qed
  end

  locale gga_to_list_defs_loc = 
    graph_nodes_it_defs nodes_list_it
    + graph_edges_it_defs edges_list_it
    for nodes_list_it :: "('V,'W,'V list,'G) graph_nodes_it"
    and edges_list_it :: "('V,'W,('V\<times>'W\<times>'V) list,'G) graph_edges_it"  
  begin
    definition gga_to_list :: 
      "('V,'W,'G) graph_to_list"
      where 
      "gga_to_list g \<equiv> 
        (nodes_it g (\<lambda>_. True) (#) [], edges_it g (\<lambda>_. True) (#) [])
      "
  end

  locale gga_to_list_loc = gga_to_list_defs_loc nodes_list_it edges_list_it +
    graph \<alpha> invar 
    + graph_nodes_it \<alpha> invar nodes_list_it
    + graph_edges_it \<alpha> invar edges_list_it
    for \<alpha> :: "'G \<Rightarrow> ('V,'W) graph" and invar
    and nodes_list_it :: "('V,'W,'V list,'G) graph_nodes_it"
    and edges_list_it :: "('V,'W,('V\<times>'W\<times>'V) list,'G) graph_edges_it"  
  begin

    lemma gga_to_list_correct:
      shows "graph_to_list \<alpha> invar gga_to_list"
    proof 
      fix g
      assume [simp, intro!]: "invar g"
      then interpret valid_graph "\<alpha> g" by (rule valid)

      have "set (nodes_it g (\<lambda>_. True) (#) []) = V"
        apply (rule_tac I="\<lambda>it \<sigma>. set \<sigma> = V - it" 
          in set_iterator_rule_P[OF nodes_it_correct])
        by auto
      moreover have "set (edges_it g (\<lambda>_. True) (#) []) = E"
        apply (rule_tac I="\<lambda>it \<sigma>. set \<sigma> = E - it" 
          in set_iterator_rule_P[OF edges_it_correct])
        by auto
      ultimately show "adjl_\<alpha> (gga_to_list g) = \<alpha> g"
        unfolding adjl_\<alpha>_def gga_to_list_def
        apply simp
        apply (rule graph.equality)
        apply (auto intro: E_validD)
        done
    qed

  end

end
