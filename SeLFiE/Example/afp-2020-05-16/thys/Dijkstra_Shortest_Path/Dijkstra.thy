section \<open>Dijkstra's Algorithm\<close>
theory Dijkstra
  imports 
  Graph 
  Dijkstra_Misc 
  Collections.Refine_Dflt_ICF
  Weight
begin
text \<open>
  This theory defines Dijkstra's algorithm. First, a correct result of 
  Dijkstra's algorithm w.r.t. a graph and a start vertex is specified. 
  Then, the refinement 
  framework is used to specify Dijkstra's Algorithm, prove it correct, and
  finally refine it to datatypes that are closer to an implementation than
  the original specification.
\<close>

subsection "Graph's for Dijkstra's Algorithm"
  text \<open>A graph annotated with weights.\<close>
  locale weighted_graph = valid_graph G
    for G :: "('V,'W::weight) graph"

subsection "Specification of Correct Result"
  context weighted_graph
  begin
    text \<open>
      A result of Dijkstra's algorithm is correct, if it is a map from nodes 
      \<open>v\<close> to the shortest path from the start node \<open>v0\<close> to 
      \<open>v\<close>. Iff there is no such path, the node is not in the map.
\<close>
    definition is_shortest_path_map :: "'V \<Rightarrow> ('V \<rightharpoonup> ('V,'W) path) \<Rightarrow> bool" 
      where
      "is_shortest_path_map v0 res \<equiv> \<forall>v\<in>V. (case res v of
        None \<Rightarrow> \<not>(\<exists>p. is_path v0 p v) |
        Some p \<Rightarrow> is_path v0 p v 
                  \<and> (\<forall>p'. is_path v0 p' v \<longrightarrow> path_weight p \<le> path_weight p')
      )"
  end

  text \<open>
    The following function returns the weight of an optional path,
    where \<open>None\<close> is interpreted as infinity.
\<close>
  fun path_weight' where
    "path_weight' None = top" |
    "path_weight' (Some p) = Num (path_weight p)"

subsection "Dijkstra's Algorithm"
  text \<open>
    The state in the main loop of the algorithm consists of a workset 
    \<open>wl\<close> of vertexes that still need to be explored, and a map 
    \<open>res\<close> that contains the current shortest path for each vertex.
\<close>
  type_synonym ('V,'W) state = "('V set) \<times> ('V \<rightharpoonup> ('V,'W) path)"

  text \<open>
    The preconditions of Dijkstra's algorithm, i.e., that it operates on a 
    valid and finite graph, and that the start node is a node of the graph,
    are summarized in a locale.
\<close>
  locale Dijkstra = weighted_graph G 
    for G :: "('V,'W::weight) graph"+
    fixes v0 :: 'V
    assumes finite[simp,intro!]: "finite V" "finite E"
    assumes v0_in_V[simp, intro!]: "v0\<in>V"
    assumes nonneg_weights[simp, intro]: "(v,w,v')\<in>edges G \<Longrightarrow> 0\<le>w"
  begin

  text \<open>Paths have non-negative weights.\<close>
  lemma path_nonneg_weight: "is_path v p v' \<Longrightarrow> 0 \<le> path_weight p"
    by (induct rule: is_path.induct) auto

  text \<open>Invariant of the main loop: 
    \begin{itemize}
      \item The workset only contains nodes of the graph.
      \item If the result set contains a path for a node, it is actually a path,
        and uses only intermediate vertices outside the workset.
      \item For all vertices outside the workset, the result map contains the 
        shortest path.
      \item For all vertices in the workset, the result map contains the
        shortest path among all paths that only use intermediate vertices outside
        the workset.
    \end{itemize}
\<close>
  definition "dinvar \<sigma> \<equiv> let (wl,res)=\<sigma> in
    wl \<subseteq> V \<and>
    (\<forall>v\<in>V. \<forall>p. res v = Some p \<longrightarrow> is_path v0 p v \<and> int_vertices p \<subseteq> V-wl) \<and>
    (\<forall>v\<in>V-wl. \<forall>p. is_path v0 p v 
       \<longrightarrow> path_weight' (res v) \<le> path_weight' (Some p)) \<and>
    (\<forall>v\<in>wl. \<forall>p. is_path v0 p v \<and> int_vertices p \<subseteq> V-wl
       \<longrightarrow> path_weight' (res v) \<le> path_weight' (Some p)
    )
    "

  text \<open>Sanity check: The invariant is strong enough to imply correctness 
    of result.\<close>
  lemma invar_imp_correct: "dinvar ({},res) \<Longrightarrow> is_shortest_path_map v0 res"
    unfolding dinvar_def is_shortest_path_map_def
    by (auto simp: infty_unbox split: option.split)

  text \<open>
    The initial workset contains all vertices. The initial result maps
    \<open>v0\<close> to the empty path, and all other vertices to \<open>None\<close>.
\<close>
  definition dinit :: "('V,'W) state nres" where
    "dinit \<equiv> SPEC ( \<lambda>(wl,res) . 
        wl=V \<and> res v0 = Some [] \<and> (\<forall>v\<in>V-{v0}. res v = None))"

  text \<open>
    The initial state satisfies the invariant.
\<close>
  lemma dinit_invar: "dinit \<le> SPEC dinvar"
    unfolding dinit_def
    apply (intro refine_vcg)
    apply (force simp: dinvar_def split: option.split)
    done

  text \<open>
    In each iteration, the main loop of the algorithm pops a minimal node from
    the workset, and then updates the result map accordingly.
\<close>

  text \<open>
    Pop a minimal node from the workset. The node is minimal in the sense that
    the length of the current path for that node is minimal.
\<close>
  definition pop_min :: "('V,'W) state \<Rightarrow> ('V \<times> ('V,'W) state) nres" where
    "pop_min \<sigma> \<equiv> do {
      let (wl,res)=\<sigma>;
      ASSERT (wl\<noteq>{}); 
      v \<leftarrow> RES (least_map (path_weight' \<circ> res) wl);
      RETURN (v,(wl-{v},res))
    }"


  text \<open>
    Updating the result according to a node \<open>v\<close> is done by checking, 
    for each successor node, whether the path over \<open>v\<close> is shorter than 
    the path currently stored into the result map.
\<close>
  inductive update_spec :: "'V \<Rightarrow> ('V,'W) state \<Rightarrow> ('V,'W) state \<Rightarrow> bool"
    where
    "\<lbrakk> \<forall>v'\<in>V. 
      res' v' \<in> least_map path_weight' (
        { res v' } \<union> { Some (p@[(v,w,v')]) | p w. res v = Some p \<and> (v,w,v')\<in>E }
      )
     \<rbrakk> \<Longrightarrow> update_spec v (wl,res) (wl,res')"

  text \<open>
    In order to ease the refinement proof, we will assert the following 
    precondition for updating.
\<close>
  definition update_pre :: "'V \<Rightarrow> ('V,'W) state \<Rightarrow> bool" where
    "update_pre v \<sigma> \<equiv> let (wl,res)=\<sigma> in v\<in>V 
      \<and> (\<forall>v'\<in>V-wl. v'\<noteq>v \<longrightarrow> (\<forall>p. is_path v0 p v' 
          \<longrightarrow> path_weight' (res v') \<le> path_weight' (Some p)))
      \<and> (\<forall>v'\<in>V. \<forall>p. res v' = Some p \<longrightarrow> is_path v0 p v')"

  definition update :: "'V \<Rightarrow> ('V,'W) state \<Rightarrow> ('V,'W) state nres" where 
    "update v \<sigma> \<equiv> do {ASSERT (update_pre v \<sigma>); SPEC (update_spec v \<sigma>)}"

  text \<open>Finally, we define Dijkstra's algorithm:\<close>
  definition dijkstra where
    "dijkstra \<equiv> do {
       \<sigma>0\<leftarrow>dinit; 
       (_,res) \<leftarrow> WHILE\<^sub>T\<^bsup>dinvar\<^esup> (\<lambda>(wl,_). wl\<noteq>{}) 
            (\<lambda>\<sigma>. 
              do { (v,\<sigma>') \<leftarrow> pop_min \<sigma>; update v \<sigma>' }
            )
            \<sigma>0;
       RETURN res }
    "

  text \<open>The following theorem states (total) correctness of Dijkstra's 
    algorithm.\<close>

  theorem dijkstra_correct: "dijkstra \<le> SPEC (is_shortest_path_map v0)"
    unfolding dijkstra_def
    unfolding dinit_def
    unfolding pop_min_def update_def [abs_def]
    thm refine_vcg

    apply (refine_rcg
      WHILEIT_rule[where R="inv_image {(x,y). x<y} (card \<circ> fst)"]
      refine_vcg 
    )

    (* TODO/FIXME: Should we built in such massaging of the goal into 
        refine_rcg ?*)
    apply (simp_all split: prod.split_asm)
    apply (tactic \<open>
      ALLGOALS ((REPEAT_DETERM o Hypsubst.bound_hyp_subst_tac @{context})
      THEN' asm_full_simp_tac @{context}
      )\<close>)

  proof -
    fix wl res v
    assume INV: "dinvar (wl,res)"
    and LM: "v\<in>least_map (path_weight' \<circ> res) wl"
    hence "v\<in>V" unfolding dinvar_def by (auto dest: least_map_elemD)
    moreover
    from INV have " \<forall>v'\<in>V - (wl-{v}). v' \<noteq> v \<longrightarrow> 
      (\<forall>p. is_path v0 p v' \<longrightarrow> path_weight' (res v') \<le> Num (path_weight p))"
      by (auto simp: dinvar_def)
    moreover from INV have "\<forall>v'\<in>V. \<forall>p. res v'=Some p \<longrightarrow> is_path v0 p v'"
      by (auto simp: dinvar_def)
    ultimately show "update_pre v (wl-{v},res)" by (auto simp: update_pre_def)
  next
    fix res
    assume "dinvar ({}, res)"
    thus "is_shortest_path_map v0 res"
      by (rule invar_imp_correct)
  next
    show "wf (inv_image {(x, y). x < y} (card \<circ> fst))" 
      by (blast intro: wf_less)
  next
    fix wl res v \<sigma>''
    assume 
      LM: "v\<in>least_map (path_weight' \<circ> res) wl" and 
      UD: "update_spec v (wl-{v},res) \<sigma>''" and
      INV: "dinvar (wl,res)" 

    from LM have "v\<in>wl" by (auto dest: least_map_elemD)
    moreover from UD have "fst \<sigma>'' = wl-{v}" by (auto elim: update_spec.cases)
    moreover from INV have "finite wl" 
      unfolding dinvar_def by (auto dest: finite_subset)
    ultimately show "card (fst \<sigma>'') < card wl" 
      apply simp
      by (metis card_gt_0_iff diff_Suc_less empty_iff)
  next
    fix a and res :: "'V \<rightharpoonup> ('V,'W) path"
    assume "a = V \<and> res v0 = Some [] \<and> (\<forall>v\<in>V-{v0}. res v = None)"
    thus "dinvar (V,res)"
      by (force simp: dinvar_def split: option.split)
  next
    fix wl res
    assume INV: "dinvar (wl,res)"
    hence  
      WL_SUBSET: "wl \<subseteq> V" and
      PATH_VALID: "\<forall>v\<in>V. \<forall>p. res v = Some p 
        \<longrightarrow> is_path v0 p v \<and> int_vertices p \<subseteq> V - wl" and
      NWL_MIN: "\<forall>v\<in>V - wl. \<forall>p. is_path v0 p v 
        \<longrightarrow> path_weight' (res v) \<le> Num (path_weight p)" and
      WL_MIN: "\<forall>v\<in>wl. \<forall>p. is_path v0 p v \<and> int_vertices p \<subseteq> V - wl 
        \<longrightarrow> path_weight' (res v) \<le> Num (path_weight p)"
      unfolding dinvar_def by auto

    fix v \<sigma>''
    assume V_LEAST: "v\<in>least_map (path_weight' o res) wl" 
      and "update_spec v (wl-{v},res) \<sigma>''"
    then obtain res' where
      [simp]: "\<sigma>''=(wl-{v},res')"
      and CONSIDERED_NEW_PATHS: "\<forall>v'\<in>V. res' v' \<in> least_map path_weight' 
        (insert (res v') 
              ({ Some (p@[(v,w,v')]) | p w. res v = Some p \<and> (v,w,v')\<in>E }))"
      by (auto elim!: update_spec.cases)
      
    from V_LEAST have V_MEM: "v\<in>wl" by (blast intro: least_map_elemD)

    show "dinvar \<sigma>''"
      apply (unfold dinvar_def, simp)
      apply (intro conjI)
    proof -
      from WL_SUBSET show "wl-{v} \<subseteq> V" by auto

      show "\<forall>va\<in>V. \<forall>p. res' va = Some p 
        \<longrightarrow> is_path v0 p va \<and> int_vertices p \<subseteq> V - (wl - {v})"
      proof (intro ballI conjI impI allI)
        fix v' p
        assume V'_MEM: "v'\<in>V" and [simp]: "res' v' = Some p"
        txt \<open>The new paths that we have added are valid and only use 
          intermediate vertices outside the workset. 
          
          This proof works as follows: A path @{term "res' v'"} is either
          the old path, or has been assembled as a path over node @{term v}.
          In the former case the proposition follows straightforwardly from the
          invariant for the old state. In the latter case we get, by the invariant
          for the old state, that the path over node @{term v} is valid. 
          Then, we observe that appending an edge to a valid path yields a valid 
          path again. Also, adding @{term v} as intermediate node is legal, as we 
          just removed @{term v} from the workset.
\<close>
        with CONSIDERED_NEW_PATHS have "res' v' \<in> (insert (res v') 
          ({ Some (p@[(v,w,v')]) | p w. res v = Some p \<and> (v,w,v')\<in>E }))"
          by (rule_tac least_map_elemD) blast
        moreover {
          assume [symmetric,simp]: "res' v' = res v'"
          from V'_MEM PATH_VALID have 
            "is_path v0 p v'" 
            "int_vertices p \<subseteq> V - (wl-{v})"
            by force+
        } moreover {
          fix pv w
          assume "res' v' = Some (pv@[(v,w,v')])" 
            and [simp]: "res v = Some pv" 
            and EDGE: "(v,w,v')\<in>E"
          hence [simp]: "p = pv@[(v,w,v')]" by simp
          
          from bspec[OF PATH_VALID rev_subsetD[OF V_MEM WL_SUBSET]] have 
            PATHV: "is_path v0 pv v" and IVV: "int_vertices pv \<subseteq> V - wl" by auto
          hence 
            "is_path v0 p v'" 
            "int_vertices p \<subseteq> V - (wl-{v})"
            by (auto simp: EDGE V'_MEM)
        } 
        ultimately show 
          "is_path v0 p v'" 
          "int_vertices p \<subseteq> V - (wl-{v})"
          by blast+
      qed

      txt \<open>
        We show that already the {\em original} result stores the minimal 
        path for all vertices not in the {\em new} workset. 
        For vertices also not in the original workset, this follows 
        straightforwardly from the invariant.
        
        For the vertex \<open>v\<close>, that has been removed from the
        workset, we split a path \<open>p'\<close> to \<open>v\<close> at the point
        \<open>u\<close> where it first enters the original workset.  

        As we chose \<open>v\<close> to be the vertex in the workset with the
        minimal weight, its weight is less than the current weight of
        \<open>u\<close>.  As the vertices of the prefix of \<open>p'\<close> up to
        \<open>u\<close> are not in the workset, the current weight of
        \<open>u\<close> is less than the weight of the prefix of \<open>p'\<close>, and thus less than the weight of \<open>p'\<close>. 
        Together, the current weight of \<open>v\<close> is less than the weight of
        \<open>p'\<close>.\<close>
      have RES_MIN: "\<forall>v\<in>V - (wl - {v}). \<forall>p. is_path v0 p v 
        \<longrightarrow> path_weight' (res v) \<le> Num (path_weight p)"
      proof (intro ballI allI impI)
        fix v' p'
        assume NOT_IN_WL: "v' \<in> V - (wl - {v})" 
          and PATH: "is_path v0 p' v'"
        hence [simp, intro!]: "v'\<in>V" by auto

        show "path_weight' (res v') \<le> Num (path_weight p')"
        proof (cases "v' = v")
          assume NE[simp]: "v'\<noteq>v"
          from bspec[OF NWL_MIN, of v'] NOT_IN_WL PATH show
            "path_weight' (res v') \<le> Num (path_weight p')" by auto
        next
          assume EQ[simp]: "v'=v"
          
          from path_split_set'[OF PATH, of wl] V_MEM obtain p1 p2 u where
            [simp]: "p'=p1@p2" 
              and P1: "is_path v0 p1 u" 
              and P2: "is_path u p2 v'" 
              and P1V: "int_vertices p1 \<subseteq> -wl" 
              and [simp]: "u\<in>wl"
            by auto
          
          from least_map_leD[OF V_LEAST]
          have "path_weight' (res v') \<le> path_weight' (res u)"by auto
          also from bspec[OF WL_MIN, of u] P1 P1V int_vertices_subset[OF P1]
          have "path_weight' (res u) \<le> Num (path_weight p1)" by auto
          also have "\<dots> \<le> Num (path_weight p')" 
            using path_nonneg_weight[OF P2]
            apply (auto simp: infty_unbox )
            by (metis add_0_right add_left_mono)
          finally show ?thesis .
        qed
      qed
        
      txt \<open>With the previous statement, we easily show the
        third part of the invariant, as the new paths are not longer than the
        old ones.
\<close>
      show "\<forall>v\<in>V - (wl - {v}). \<forall>p. is_path v0 p v 
        \<longrightarrow> path_weight' (res' v) \<le> Num (path_weight p)"
      proof (intro allI ballI impI)
        fix v' p
        assume NOT_IN_WL: "v' \<in> V - (wl - {v})" 
          and PATH: "is_path v0 p v'"
        hence [simp, intro!]: "v'\<in>V" by auto
        from bspec[OF CONSIDERED_NEW_PATHS, of v']
        have "path_weight' (res' v') \<le> path_weight' (res v')"
          by (auto dest: least_map_leD)
        also from bspec[OF RES_MIN NOT_IN_WL] PATH 
        have "path_weight' (res v') \<le> Num (path_weight p)" by blast
        finally show "path_weight' (res' v') \<le> Num (path_weight p)" .
      qed

      txt \<open>
        Finally, we have to show that for nodes on the worklist,
        the stored paths are not longer than any path using only nodes not
        on the worklist. Compared to the situation before the step, those
        path may also use the node \<open>v\<close>.
\<close>
      show "\<forall>va\<in>wl - {v}. \<forall>p. 
        is_path v0 p va \<and> int_vertices p \<subseteq> V - (wl - {v}) 
        \<longrightarrow> path_weight' (res' va) \<le> Num (path_weight p)"
      proof (intro allI impI ballI, elim conjE)
        fix v' p
        assume IWS: "v'\<in>wl - {v}" 
          and PATH: "is_path v0 p v'" 
          and VERTICES: "int_vertices p \<subseteq> V - (wl - {v})"
        from IWS WL_SUBSET have [simp, intro!]: "v'\<in>V" by auto
        
        {
          txt \<open>
            If the path is empty, the proposition follows easily from the
            invariant for the original states, as no intermediate nodes are 
            used at all.
\<close>
          assume [simp]: "p=[]"
          from bspec[OF CONSIDERED_NEW_PATHS, of v'] have
            "path_weight' (res' v') \<le> path_weight' (res v')"
            using IWS WL_SUBSET by (auto dest: least_map_leD)
          also have "int_vertices p \<subseteq> V-wl" by auto
          with WL_MIN IWS PATH 
          have "path_weight' (res v') \<le> Num (path_weight p)"
            by (auto simp del: path_weight_empty)
          finally have "path_weight' (res' v') \<le> Num (path_weight p)" .
        } moreover {
          fix p1 u w
          assume [simp]: "p = p1@[(u,w,v')]"
          txt \<open>If the path is not empty, we pick the last but one vertex, and
            call it @{term u}.\<close>
          from PATH have PATH1: "is_path v0 p1 u" and EDGE: "(u,w,v')\<in>E" by auto
          from VERTICES have NIV: "u\<in>V - (wl-{v})" by simp
          hence U_MEM[simp]: "u\<in>V" by auto

          txt \<open>From @{thm [source] RES_MIN}, we know that @{term "res u"} holds
            the shortest path to @{term u}. Thus \<open>p\<close> is longer than the 
            path that is constructed by replacing the prefix of @{term p} by 
            {term "res u"}\<close>
          from NIV RES_MIN PATH1 
          have G: "Num (path_weight p1) \<ge> path_weight' (res u)" by simp
          then obtain pu where [simp]: "res u = Some pu" 
            by (cases "res u") (auto simp: infty_unbox)
          from G have "Num (path_weight p) \<ge> path_weight' (res u) + Num w"
            by (auto simp: infty_unbox add_right_mono)
          also 
          have "path_weight' (res u) + Num w \<ge> path_weight' (res' v')"
            txt \<open>
              The remaining argument depends on wether @{term u} 
              equals @{term v}. 
              In the case @{term "u\<noteq>v"}, all vertices of @{term "res u"} are
              outside the original workset. Thus, appending the edge 
              @{term "(u,w,v')"} to @{term "res u"} yields a path to @{term v}
              over intermediate nodes only outside the workset. By the invariant
              for the original state, @{term "res v'"} is shorter than this path.
              As a step does not replace paths by longer ones, also 
              @{term "res' v'"} is shorter.

              In the case @{term "u=v"}, the step has
              considered the path to \<open>v'\<close> over \<open>v\<close>, and thus the
              result path is not longer.
\<close>
          proof (cases "u=v")
            assume "u\<noteq>v"
            with NIV have NIV': "u\<in>V-wl" by auto
            from bspec[OF PATH_VALID U_MEM] NIV'
            have "is_path v0 pu u" and VU: "int_vertices (pu@[(u,w,v')]) \<subseteq> V-wl" 
              by auto
            with EDGE have PV': "is_path v0 (pu@[(u,w,v')]) v'" by auto
            with bspec[OF WL_MIN, of v'] IWS VU have 
              "path_weight' (res v') \<le> Num (path_weight (pu@[(u,w,v')]))"
              by blast
            hence "path_weight' (res u) + Num w \<ge> path_weight' (res v')"
              by (auto simp: infty_unbox)
            also from CONSIDERED_NEW_PATHS have 
              "path_weight' (res v') \<ge> path_weight' (res' v')"
              by (auto dest: least_map_leD)
            finally (order_trans[rotated]) show ?thesis .
          next
            assume [symmetric,simp]: "u=v"
            from CONSIDERED_NEW_PATHS EDGE have 
              "path_weight' (res' v') \<le> path_weight' (Some (pu@[(v,w,v')]))"
              by (rule_tac least_map_leD) auto
            thus ?thesis by (auto simp: infty_unbox)
          qed
          finally (order_trans[rotated]) have 
            "path_weight' (res' v') \<le> Num (path_weight p)" .
        } ultimately show "path_weight' (res' v') \<le> Num (path_weight p)"
          using PATH apply (cases p rule: rev_cases) by auto
      qed
    qed
  qed

  subsection \<open>Structural Refinement of Update\<close>
  text \<open>
    Now that we have proved correct the initial version of the algorithm, we start
    refinement towards an efficient implementation.
\<close>

  text \<open>
    First, the update function is refined to iterate over each successor of the
    selected node, and update the result on demand.
\<close>
  definition uinvar 
    :: "'V \<Rightarrow> 'V set \<Rightarrow> _ \<Rightarrow> ('W\<times>'V) set \<Rightarrow> ('V,'W) state \<Rightarrow> bool" where
    "uinvar v wl res it \<sigma> \<equiv> let (wl',res')=\<sigma> in wl'=wl 
    \<and> (\<forall>v'\<in>V. 
      res' v' \<in> least_map path_weight' (
        { res v' } \<union> { Some (p@[(v,w,v')]) | p w. res v = Some p 
          \<and> (w,v') \<in> succ G v - it }
      ))
    \<and> (\<forall>v'\<in>V. \<forall>p. res' v' = Some p \<longrightarrow> is_path v0 p v')
    \<and> res' v = res v
    "

  definition update' :: "'V \<Rightarrow> ('V,'W) state \<Rightarrow> ('V,'W) state nres" where 
    "update' v \<sigma> \<equiv> do {
      ASSERT (update_pre v \<sigma>);
      let (wl,res) = \<sigma>;
      let wv = path_weight' (res v);
      let pv = res v;
      FOREACH\<^bsup>uinvar v wl res\<^esup> (succ G v) (\<lambda>(w',v') (wl,res). 
        if (wv + Num w' < path_weight' (res v')) then do {
            ASSERT (v'\<in>wl \<and> pv\<noteq>None); 
            RETURN (wl,res(v' \<mapsto> the pv@[(v,w',v')]))
        } else RETURN (wl,res)
      ) (wl,res)}"

  lemma update'_refines:
    assumes "v'=v" and "\<sigma>'=\<sigma>"
    shows "update' v' \<sigma>' \<le> \<Down>Id (update v \<sigma>)"
    apply (simp only: assms)
    unfolding update'_def update_def
    apply (refine_rcg refine_vcg)

    (*apply (intro refine_vcg conjI)*)
    apply (simp_all only: singleton_iff)
  proof -
    fix wl res
    assume "update_pre v (wl,res)"
    thus "uinvar v wl res (succ G v) (wl,res)"
      by (simp add: uinvar_def update_pre_def)
  next

    fix wl res it wl' res' v' w'
    assume PRE: "update_pre v (wl,res)"
    assume INV: "uinvar v wl res it (wl',res')"
    assume MEM: "(w',v')\<in>it" 
    assume IT_SS: "it\<subseteq> succ G v"
    assume LESS: "path_weight' (res v) + Num w' < path_weight' (res' v')"

    from PRE have [simp, intro!]: "v\<in>V" by (simp add: update_pre_def)

    from MEM IT_SS have [simp,intro!]: "v'\<in>V" using succ_subset
      by auto

    from LESS obtain pv where [simp]: "res v = Some pv"
      by (cases "res v") auto

    thus "res v \<noteq> None" by simp

    have [simp]: "wl'=wl" and [simp]: "res' v = res v" 
      using INV unfolding uinvar_def by auto

    from MEM IT_SS have EDGE[simp]: "(v,w',v')\<in>E" 
      unfolding succ_def by auto
    with INV have [simp]: "is_path v0 pv v"
      unfolding uinvar_def by auto

    have "0\<le>w'" by (rule nonneg_weights[OF EDGE])
    hence [simp]: "v'\<noteq>v" using LESS
      by auto
    hence [simp]: "v\<noteq>v'" by blast

    show [simp]: "v'\<in>wl'" proof (rule ccontr)
      assume [simp]: "v'\<notin>wl'"
      hence [simp]: "v'\<in>V-wl" and [simp]: "v'\<notin>wl" by auto
      note LESS
      also
      from INV have "path_weight' (res' v') \<le> path_weight' (res v')"
        unfolding uinvar_def by (auto dest: least_map_leD)      
      also
      from PRE have PW: "\<And>p. is_path v0 p v' \<Longrightarrow> 
        path_weight' (res v') \<le> path_weight' (Some p)"
        unfolding update_pre_def 
        by auto
      have P: "is_path v0 (pv@[(v,w',v')]) v'" by simp
      from PW[OF P] have 
        "path_weight' (res v') \<le> Num (path_weight (pv@[(v,w',v')]))"
        by auto
      finally show False by (simp add: infty_unbox)
    qed

    show "uinvar v wl res (it-{(w',v')}) (wl',res'(v'\<mapsto>the (res v)@[(v,w',v')]))"
    proof -
      have "(res'(v'\<mapsto>the (res v)@[(v,w',v')])) v = res' v" by simp
      moreover {
        fix v'' assume VMEM: "v''\<in>V"
        have "(res'(v'\<mapsto>the (res v)@[(v,w',v')])) v'' \<in> least_map path_weight' (
          { res v'' } \<union> { Some (p@[(v,w,v'')]) | p w. res v = Some p 
          \<and> (w,v'') \<in> succ G v - (it - {(w',v')}) }
          ) \<and> (\<forall>p. (res'(v'\<mapsto>the (res v)@[(v,w',v')])) v'' = Some p 
                \<longrightarrow> is_path v0 p v'')"
        proof (cases "v''=v'")
          case [simp]: False
          have "{ Some (p@[(v,w,v'')]) | p w. res v = Some p 
          \<and> (w,v'') \<in> succ G v - (it - {(w',v')}) } = 
            { Some (p@[(v,w,v'')]) | p w. res v = Some p 
          \<and> (w,v'') \<in> succ G v - it }"
            by auto
          with INV VMEM show ?thesis unfolding uinvar_def 
            by simp
        next
          case [simp]: True
          have EQ: "{ res v'' } \<union> { Some (p@[(v,w,v'')]) | p w. res v = Some p 
          \<and> (w,v'') \<in> succ G v - (it - {(w',v')}) } =
          insert (Some (pv@[(v,w',v')])) (
            { res v'' } \<union> { Some (p@[(v,w,v'')]) | p w. res v = Some p 
          \<and> (w,v'') \<in> succ G v - it })"
            using MEM IT_SS
            by auto
          show ?thesis
            apply (subst EQ)
            apply simp
            apply (rule least_map_insert_min)
            apply (rule ballI)
          proof -
            fix r'
            assume A: 
              "r' \<in> insert (res v') 
               {Some (pv @ [(v, w, v')]) |w. (w, v') \<in> succ G v \<and> (w, v') \<notin> it}"

            from LESS have 
              "path_weight' (Some (pv @ [(v, w', v')])) < path_weight' (res' v')"
              by (auto simp: infty_unbox)
            also from INV[unfolded uinvar_def] have 
              "res' v' \<in> least_map path_weight' (
                insert (res v') 
                {Some (pv @ [(v, w, v')]) |w. (w, v') \<in> succ G v \<and> (w, v') \<notin> it}
              )"
              by auto
            with A have "path_weight' (res' v') \<le> path_weight' r'"
              by (auto dest: least_map_leD)
            finally show 
              "path_weight' (Some (pv @ [(v, w', v')])) \<le> path_weight' r'"
              by simp
          qed
        qed
      }
      ultimately show ?thesis
        unfolding uinvar_def Let_def 
        by auto
    qed
  next
    fix wl res it w' v' wl' res'
    assume INV: "uinvar v wl res it (wl',res')"
    and NLESS: "\<not> path_weight' (res v) + Num w' < path_weight' (res' v')"
    and IN_IT: "(w',v')\<in>it"
    and IT_SS: "it \<subseteq> succ G v"

    from IN_IT IT_SS have [simp, intro!]: "(w',v')\<in>succ G v" by auto
    hence [simp,intro!]: "v'\<in>V" using succ_subset
      by auto

    show "uinvar v wl res (it - {(w',v')}) (wl',res')"
    proof (cases "res v")
      case [simp]: None
      from INV show ?thesis
        unfolding uinvar_def by auto
    next
      case [simp]: (Some p)
      {
        fix v''
        assume [simp, intro!]: "v''\<in>V"
        have "res' v'' \<in> least_map path_weight' (
          { res v'' } \<union> { Some (p@[(v,w,v'')]) | p w. res v = Some p 
          \<and> (w,v'') \<in> succ G v - (it - {(w',v')}) }
          )" (is "_ \<in> least_map path_weight' ?S")
        proof (cases "v''=v'")
          case False with INV show ?thesis
            unfolding uinvar_def by auto
        next
          case [simp]: True
          
          have EQ: "?S = insert (Some (p@[(v,w',v')])) (
            { res v' } \<union> { Some (p@[(v,w,v'')]) | p w. res v = Some p 
                            \<and> (w,v'') \<in> succ G v - it }
            )"
            by auto
          from NLESS have 
            "path_weight' (res' v') \<le> path_weight' (Some (p@[(v,w',v')]))"
            by (auto simp: infty_unbox)
          thus ?thesis
            apply (subst EQ)
            apply (rule least_map_insert_nmin)
            using INV unfolding uinvar_def apply auto []
            apply simp
            done
        qed
      } with INV
      show ?thesis
        unfolding uinvar_def by auto
    qed
  next
    fix wl res \<sigma>'

    assume "uinvar v wl res {} \<sigma>'" 
    thus "update_spec v (wl,res) \<sigma>'"
      unfolding uinvar_def
      apply (cases \<sigma>')
      apply (auto intro: update_spec.intros simp: succ_def)
      done
  next
    show "finite (succ G v)" by simp
  qed

  text \<open>We integrate the new update function into the main algorithm:\<close>
  definition dijkstra' where
    "dijkstra' \<equiv> do {
      \<sigma>0 \<leftarrow> dinit; 
      (_,res) \<leftarrow> WHILE\<^sub>T\<^bsup>dinvar\<^esup> (\<lambda>(wl,_). wl\<noteq>{}) 
            (\<lambda>\<sigma>. do {(v,\<sigma>') \<leftarrow> pop_min \<sigma>; update' v \<sigma>'})
            \<sigma>0;
      RETURN res
    }"


  lemma dijkstra'_refines: "dijkstra' \<le> \<Down>Id dijkstra"
  proof -
    note [refine] = update'_refines
    have [refine]: "\<And>\<sigma> \<sigma>'. \<sigma>=\<sigma>' \<Longrightarrow> pop_min \<sigma> \<le> \<Down>Id (pop_min \<sigma>')" by simp
    show ?thesis
      unfolding dijkstra_def dijkstra'_def
      apply (refine_rcg)
      apply simp_all
      done
  qed
end

subsection \<open>Refinement to Cached Weights\<close>
text \<open>
  Next, we refine the data types of the workset and the result map.
  The workset becomes a map from nodes to their current weights.
  The result map stores, in addition to the shortest path, also the
  weight of the shortest path. Moreover, we store the shortest paths
  in reversed order, which makes appending new edges more effcient.

  These refinements allow to implement the workset as a priority queue,
  and save recomputation of the path weights in the inner loop of the
  algorithm.
\<close>

type_synonym ('V,'W) mwl = "('V \<rightharpoonup> 'W infty)"
type_synonym ('V,'W) mres = "('V \<rightharpoonup> (('V,'W) path \<times> 'W))"
type_synonym ('V,'W) mstate = "('V,'W) mwl \<times> ('V,'W) mres"

text \<open>
  Map a path with cached weight to one without cached weight.
\<close>
fun mpath' :: "(('V,'W) path \<times> 'W) option \<rightharpoonup> ('V,'W) path" where
  "mpath' None = None" |
  "mpath' (Some (p,w)) = Some p"

fun mpath_weight' :: "(('V,'W) path \<times> 'W) option \<Rightarrow> ('W::weight) infty" where
  "mpath_weight' None = top" |
  "mpath_weight' (Some (p,w)) = Num w"

context Dijkstra
begin
  definition \<alpha>w::"('V,'W) mwl \<Rightarrow> 'V set" where "\<alpha>w \<equiv> dom"
  definition \<alpha>r::"('V,'W) mres \<Rightarrow> 'V \<rightharpoonup> ('V,'W) path" where 
    "\<alpha>r \<equiv> \<lambda>res v. case res v of None \<Rightarrow> None | Some (p,w) \<Rightarrow> Some (rev p)"
  definition \<alpha>s:: "('V,'W) mstate \<Rightarrow> ('V,'W) state" where
    "\<alpha>s \<equiv> map_prod \<alpha>w \<alpha>r"

  text \<open>Additional invariants for the new state. They guarantee that
    the cached weights are consistent.\<close>
  definition res_invarm :: "('V \<rightharpoonup> (('V,'W) path\<times>'W)) \<Rightarrow> bool" where
    "res_invarm res \<equiv> (\<forall>v. case res v of 
        None \<Rightarrow> True | 
        Some (p,w) \<Rightarrow> w = path_weight (rev p))"
  definition dinvarm :: "('V,'W) mstate \<Rightarrow> bool" where
    "dinvarm \<sigma> \<equiv> let (wl,res) = \<sigma> in
      (\<forall>v\<in>dom wl. the (wl v) = mpath_weight' (res v)) \<and> res_invarm res
    "
  lemma mpath_weight'_correct: "\<lbrakk>dinvarm (wl,res)\<rbrakk> \<Longrightarrow>
    mpath_weight' (res v) = path_weight' (\<alpha>r res v)
    "
    unfolding dinvarm_def res_invarm_def \<alpha>r_def
    by (auto split: option.split option.split_asm)

  lemma mpath'_correct: "\<lbrakk>dinvarm (wl,res)\<rbrakk> \<Longrightarrow>
    mpath' (res v) = map_option rev (\<alpha>r res v)"
    unfolding dinvarm_def \<alpha>r_def
    by (auto split: option.split option.split_asm)

  lemma wl_weight_correct:
    assumes INV: "dinvarm (wl,res)" 
    assumes WLV: "wl v = Some w" 
    shows "path_weight' (\<alpha>r res v) = w"
  proof -
    from INV WLV have "w = mpath_weight' (res v)"
      unfolding dinvarm_def by force
    also from mpath_weight'_correct[OF INV] have 
      "\<dots> = path_weight' (\<alpha>r res v)" .
    finally show ?thesis by simp
  qed

  text \<open>The initial state is constructed using an iterator:\<close>
  definition mdinit :: "('V,'W) mstate nres" where
    "mdinit \<equiv> do {
      wl \<leftarrow> FOREACH V (\<lambda>v wl. RETURN (wl(v\<mapsto>Infty))) Map.empty;
      RETURN (wl(v0\<mapsto>Num 0),[v0 \<mapsto> ([],0)])
    }"

  lemma mdinit_refines: "mdinit \<le> \<Down>(build_rel \<alpha>s dinvarm) dinit"
    unfolding mdinit_def dinit_def
    apply (rule build_rel_SPEC)
    apply (intro FOREACH_rule[where I="\<lambda>it wl. (\<forall>v\<in>V-it. wl v = Some Infty) \<and> 
      dom wl = V-it"]
           refine_vcg)
    apply (auto 
      simp: \<alpha>s_def \<alpha>w_def \<alpha>r_def dinvarm_def res_invarm_def infty_unbox
      split: if_split_asm
    )
    done

  text \<open>The new pop function:\<close>
  definition 
    mpop_min :: "('V,'W) mstate \<Rightarrow> ('V \<times> 'W infty \<times> ('V,'W) mstate) nres" 
    where
    "mpop_min \<sigma> \<equiv> do {
      let (wl,res) = \<sigma>; 
      (v,w,wl')\<leftarrow>prio_pop_min wl;
      RETURN (v,w,(wl',res))
    }"
    
  lemma mpop_min_refines:
    "\<lbrakk> (\<sigma>,\<sigma>') \<in> build_rel \<alpha>s dinvarm \<rbrakk> \<Longrightarrow> 
      mpop_min \<sigma> \<le> 
       \<Down>(build_rel 
          (\<lambda>(v,w,\<sigma>). (v,\<alpha>s \<sigma>)) 
          (\<lambda>(v,w,\<sigma>). dinvarm \<sigma> \<and> w = mpath_weight' (snd \<sigma> v)))
      (pop_min \<sigma>')"
    \<comment> \<open>The two algorithms are structurally different, so we use the
      nofail/inres method to prove refinement.\<close>
    unfolding mpop_min_def pop_min_def prio_pop_min_def

    apply (rule pw_ref_I)
    apply rule
    apply (auto simp add: refine_pw_simps \<alpha>s_def \<alpha>w_def refine_rel_defs
      split: prod.split prod.split_asm)

    apply (auto simp: dinvarm_def) []

    apply (auto simp: mpath_weight'_correct wl_weight_correct) []

    apply (auto 
      simp: wl_weight_correct 
      intro!: least_map.intros
    ) []
    apply (metis restrict_map_eq(2))

    done

  text \<open>The new update function:\<close>
  definition "uinvarm v wl res it \<sigma> \<equiv> 
    uinvar v wl res it (\<alpha>s \<sigma>) \<and> dinvarm \<sigma>"

  definition mupdate :: "'V \<Rightarrow> 'W infty \<Rightarrow> ('V,'W) mstate \<Rightarrow> ('V,'W) mstate nres"
   where 
    "mupdate v wv \<sigma> \<equiv> do {
      ASSERT (update_pre v (\<alpha>s \<sigma>) \<and> wv=mpath_weight' (snd \<sigma> v));
      let (wl,res) = \<sigma>;
      let pv = mpath' (res v);
      FOREACH\<^bsup>uinvarm v (\<alpha>w wl) (\<alpha>r res)\<^esup> (succ G v) (\<lambda>(w',v') (wl,res). 
        if (wv + Num w' < mpath_weight' (res v')) then do {
          ASSERT (v'\<in>dom wl \<and> pv \<noteq> None);
          ASSERT (wv \<noteq> Infty);
          RETURN (wl(v'\<mapsto>wv + Num w'),
                    res(v' \<mapsto> ((v,w',v')#the pv,val wv + w') ))
        } else RETURN (wl,res)
        ) (wl,res)
    }"

  lemma mupdate_refines: 
    assumes SREF: "(\<sigma>,\<sigma>')\<in>build_rel \<alpha>s dinvarm"
    assumes WV: "wv = mpath_weight' (snd \<sigma> v)"
    assumes VV': "v'=v"
    shows "mupdate v wv \<sigma> \<le> \<Down>(build_rel \<alpha>s dinvarm) (update' v' \<sigma>')"
  proof (simp only: VV')
    {
      txt \<open>Show that IF-condition is a refinement:\<close>
      fix wl res wl' res' it w' v'
      assume "uinvarm v (\<alpha>w wl) (\<alpha>r res) it (wl',res')" 
        and "dinvarm (wl,res)"
      hence "mpath_weight' (res v) + Num w' < mpath_weight' (res' v') \<longleftrightarrow>
        path_weight' (\<alpha>r res v) + Num w' < path_weight' (\<alpha>r res' v')"
        unfolding uinvarm_def
        by (auto simp add: mpath_weight'_correct)
    } note COND_refine=this

    {
      txt \<open>THEN-case:\<close>
      fix wl res wl' res' it w' v'
      assume UINV: "uinvarm v (\<alpha>w wl) (\<alpha>r res) it (wl',res')"
        and DINV: "dinvarm (wl,res)"
        and "mpath_weight' (res v) + Num w' < mpath_weight' (res' v')"
        and "path_weight' (\<alpha>r res v) + Num w' < path_weight' (\<alpha>r res' v')"
        and V'MEM: "v'\<in>\<alpha>w wl'"
        and NN: "\<alpha>r res v \<noteq> None"
    
      from NN obtain pv wv where
        ARV: "\<alpha>r res v = Some (rev pv)" and
        RV: "res v = Some (pv,wv)" 
        unfolding \<alpha>r_def by (auto split: option.split_asm)

      with DINV have [simp]: "wv = path_weight (rev pv)"
        unfolding dinvarm_def res_invarm_def by (auto split: option.split_asm)
      
      note [simp] = ARV RV

      from V'MEM NN have "v'\<in>dom wl'" (is "?G1") 
        and "mpath' (res v) \<noteq> None" (is "?G2") 
        unfolding \<alpha>w_def \<alpha>r_def by (auto split: option.split_asm)
    
      hence "\<And>x. \<alpha>w wl' = \<alpha>w (wl'(v'\<mapsto>x))" by (auto simp: \<alpha>w_def)
      moreover have "mpath' (res v) = map_option rev (\<alpha>r res v)" using DINV 
        by (simp add: mpath'_correct)
      ultimately have
        "\<alpha>w wl' = \<alpha>w (wl'(v' \<mapsto> mpath_weight' (res v) + Num w')) 
        \<and> (\<alpha>r res')(v' \<mapsto> the (\<alpha>r res v)@[(v, w', v')]) 
           = \<alpha>r (res'(v' \<mapsto> ((v, w', v')#the (mpath' (res v)), 
                 val (mpath_weight' (res v)) + w')))" (is ?G3)
        by (auto simp add: \<alpha>r_def intro!: ext)
      have
        "(dinvarm (wl'(v'\<mapsto>mpath_weight' (res v) + Num w'),
                           res'(v' \<mapsto> ((v,w',v') # the (mpath' (res v)),
                                       val (mpath_weight' (res v)) + w'
                                      ))))" (is ?G4)
        using UINV unfolding uinvarm_def dinvarm_def res_invarm_def
        by (auto simp: infty_unbox split: option.split option.split_asm)
      note \<open>?G1\<close> \<open>?G2\<close> \<open>?G3\<close> \<open>?G4\<close>
    } note THEN_refine=this


    note [refine2] = inj_on_id

    note [simp] = refine_rel_defs

    show "mupdate v wv \<sigma> \<le> \<Down>(build_rel \<alpha>s dinvarm) (update' v \<sigma>')" 
      using SREF WV
      unfolding mupdate_def update'_def
      apply -

      apply (refine_rcg)

      apply simp_all [3]
      apply (simp add: \<alpha>s_def uinvarm_def)
      apply (simp_all add: \<alpha>s_def COND_refine THEN_refine(1-2)) [3]
      apply (rule ccontr,simp)
      using THEN_refine(3,4)
      apply (auto simp: \<alpha>s_def) []
      txt \<open>The ELSE-case is trivial:\<close>
      apply simp
      done
  qed

  text \<open>Finally, we assemble the refined algorithm:\<close>
  definition mdijkstra where
    "mdijkstra \<equiv> do {
      \<sigma>0 \<leftarrow> mdinit; 
      (_,res) \<leftarrow> WHILE\<^sub>T\<^bsup>dinvarm\<^esup> (\<lambda>(wl,_). dom wl\<noteq>{}) 
            (\<lambda>\<sigma>. do { (v,wv,\<sigma>') \<leftarrow> mpop_min \<sigma>; mupdate v wv \<sigma>' } )
            \<sigma>0;
      RETURN res
    }"

  lemma mdijkstra_refines: "mdijkstra \<le> \<Down>(build_rel \<alpha>r res_invarm) dijkstra'"
  proof -
    note [refine] = mdinit_refines mpop_min_refines mupdate_refines
    show ?thesis
      unfolding mdijkstra_def dijkstra'_def
      apply (refine_rcg)
      apply (simp_all split: prod.split
        add: \<alpha>s_def \<alpha>w_def dinvarm_def refine_rel_defs)
      done
  qed

end

end
