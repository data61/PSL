section "Kruskal on Symmetric Directed Graph"

theory Graph_Definition_Impl
imports
 Kruskal_Impl Graph_Definition_Aux
begin
 
subsection "Interpreting \<open>Kruskl_Impl\<close>"

locale fromlist = fixes
  L :: "(nat \<times> int \<times> nat) list" 
begin

 
  abbreviation "E\<equiv>set L"
  abbreviation "V\<equiv>fst ` E \<union> (snd \<circ> snd) ` E"
  abbreviation "ind (E'::(nat \<times> int \<times> nat) set) \<equiv> \<lparr>nodes=V, edges=E'\<rparr>"
  abbreviation "subforest E' \<equiv> forest (ind E') \<and> subgraph (ind E')  (ind E)"


  lemma max_node_is_Max_V: " E =  set la \<Longrightarrow> max_node la = Max (insert 0 V)"
  proof -
    assume E: "E =  set la"
    have *: "fst ` set la \<union> (snd \<circ> snd) ` set la
             = (\<Union>x\<in>set la. case x of (x1, x1a, x2a) \<Rightarrow> {x1, x2a})"
      by auto force 
    show ?thesis 
    unfolding E  
    by (auto simp add:    max_node_def prod.case_distrib * ) 
  qed

  lemma ind_valid_graph: "\<And>E'. E' \<subseteq> E \<Longrightarrow> valid_graph (ind E')"
    unfolding valid_graph_def by force
  
  lemma vE: "valid_graph (ind E)" apply(rule ind_valid_graph) by simp
  
  lemma ind_valid_graph': "\<And>E'. subgraph (ind E') (ind E) \<Longrightarrow> valid_graph (ind E')"
    apply(rule ind_valid_graph) by(auto simp: subgraph_def) 
    
  lemma add_edge_ind: "(a,w,b)\<in>E \<Longrightarrow> add_edge a w b (ind F) = ind (insert (a,w,b) F)"
    unfolding add_edge_def by force
  
                                                     
  lemma nodes_connected_ind_sym: "F\<subseteq>E \<Longrightarrow> sym {(x, y) |x y. nodes_connected (ind F) x y}"
    apply(frule ind_valid_graph) 
      unfolding sym_def using valid_graph.nodes_connected_sym by fast  
  lemma nodes_connected_ind_trans: "F\<subseteq>E \<Longrightarrow> trans {(x, y) |x y. nodes_connected (ind F) x y}"
    apply(frule ind_valid_graph) 
     unfolding trans_def using valid_graph.is_path_undir_append by fast
  
  lemma part_equiv_nodes_connected_ind:
    "F\<subseteq>E \<Longrightarrow> part_equiv {(x, y) |x y. nodes_connected (ind F) x y}"
     apply(rule) using nodes_connected_ind_trans nodes_connected_ind_sym by auto
  
  
  sublocale s: Kruskal_Impl E V
    "\<lambda>e. {fst e, snd (snd e)}" "\<lambda>u v (a,w,b). u=a \<and> v=b \<or> u=b \<and> v=a"
    "subforest"
    "\<lambda>E'. { (a,b) |a b. nodes_connected (ind E') a b}"
    "\<lambda>(u,w,v). w" id  "PR_CONST (\<lambda>(u,w,v). RETURN (u,v))"
    "PR_CONST (RETURN L)" "return L" "set L" "(\<lambda>(u,w,v). return (u,v))"
  proof (unfold_locales, goal_cases) 
    show "finite E" by simp
  next
    fix E'
    assume "forest (ind E') \<and> subgraph (ind E')  \<lparr>nodes=V, edges=E\<rparr>"
    then show "E' \<subseteq> E" unfolding subgraph_def by auto
  next
    show "subforest {}" by (auto simp: subgraph_def forest_def valid_graph_def forest_axioms_def)
  next
    case (4 X Y)
    then have *: "subgraph (ind Y) (ind X)" "subgraph (ind Y) (ind E)"
      unfolding subgraph_def by auto
    with 4 show ?case using forest.subgraph_forest by auto
  next
    case (5 u v)
    have k: "valid_graph (ind {})" apply(rule ind_valid_graph) by simp 
    show ?case   
      apply auto 
      subgoal for p  apply(cases p) by auto
      subgoal for p  apply(cases p) by auto
      subgoal apply(rule exI[where x="[]"]) by auto
      subgoal apply(rule exI[where x="[]"]) by force  
      done
  next
    case (6 E1 E2 u v)
    have *: "valid_graph (ind E)" apply(rule ind_valid_graph) by simp
    from 6 show ?case using valid_graph.augment_edge[of "ind E" "ind E1" "ind E2" u v, OF *]
      unfolding subgraph_def by simp 
  next
    case (7 F e u v)
    then have f: "forest (ind F)" and s: "subgraph (ind F) (ind E)" by auto
    from 7 have uv: "u\<in>V" "v\<in>V" by force+
    obtain a w b where e: "e=(a,w,b)" apply(cases e) by auto
    from e 7(3) have abuv: "u=a \<and> v=b \<or> u=b \<and> v=a" by auto
    show ?case
    proof 
      assume "forest (ind (insert e F)) \<and> subgraph (ind (insert e F)) (ind E) "
      then have "(\<forall>(a, w, b)\<in> insert e F. 
                \<not>nodes_connected (delete_edge a w b (ind (insert e F))) a b)"
        unfolding forest_def forest_axioms_def by auto
      with e have i: "\<not> nodes_connected (delete_edge a w b (ind (insert e F))) a b" by auto
      have ii: "(delete_edge a w b (ind (insert e F))) = ind F"
        using 7(2) e by (auto simp: delete_edge_def)
      from i have "\<not> nodes_connected (ind F) a b" using ii by auto
      then show "(u, v) \<notin> {(a, b) |a b. nodes_connected (ind F) a b}"
        using 7(3)   valid_graph.nodes_connected_sym[OF ind_valid_graph'[OF s]] e by auto
    next
      from s 7(2) have sg: "subgraph (ind (insert e F)) (ind E)" 
        unfolding subgraph_def by auto
      assume "(u, v) \<notin> {(a, b) |a b. nodes_connected (ind F) a b}"
      with abuv have "(a, b) \<notin> {(a, b) |a b. nodes_connected (ind F) a b}"
        using  valid_graph.nodes_connected_sym[OF ind_valid_graph'[OF s]]
        by auto
      then have nn: "~nodes_connected (ind F) a b" by auto
      have "forest (add_edge a w b (ind F))" apply(rule forest.forest_add_edge[OF f _ _ nn])
        using uv abuv by auto
      then have f': "forest (ind (insert e F))" using 7(2) add_edge_ind by (auto simp add: e)   
      from f' sg show "forest (ind (insert e F)) \<and> subgraph (ind (insert e F)) (ind E) "
        by auto
    qed
  next
    case (8 F)  
    then have s: "subgraph (ind F) (ind E)" unfolding subgraph_def by auto
    from valid_graph.connected_VV[OF vE s] 
      show i: "{(x, y) |x y. nodes_connected (ind F) x y} \<subseteq> V\<times>V" by simp
       
    from valid_graph.connected_equiv[OF vE s]
      show "equiv V {(x, y) |x y. nodes_connected (ind F) x y}" by simp
  next
    case (10 x y F e)
    from 10 have xy: "x\<in>V" "y\<in>V" by force+
    obtain a w b where e: "e=(a,w,b)" apply(cases e) by auto
    
    from 10(4) have ad_eq: "add_edge a w b (ind F) = ind (insert e F)"
      using e unfolding add_edge_def by (auto simp add: rev_image_eqI)  
    have *: "\<And>x y. nodes_connected (add_edge a w b (ind F)) x y
             = ((x, y) \<in> per_union {(x, y) |x y. nodes_connected (ind F) x y} a b)"
      apply(rule valid_graph.nodes_connected_insert_per_union[of "ind E"])
      subgoal apply(rule ind_valid_graph) by simp
      subgoal using 10(3) by(auto simp: subgraph_def)
      subgoal apply(rule part_equiv_nodes_connected_ind) by fact
      using xy e 10(5) by auto
    show ?case
      using 10(5) e * ad_eq by auto
  next
    case 11
    then show ?case by auto
  next
    case 12
    then show ?case by auto
  next
    case 13
    then show ?case by auto
  next
    case (14 a F e)
    then obtain w where "e=(a,w,a)" by auto
    with 14 have "a\<in>V" and p: "(a,w,a): edges (ind (insert e F))" by auto 
    then have *: "nodes_connected (delete_edge a w a (ind (insert e F))) a a"
      apply (intro exI[where x="[]"]) by simp
    have "\<exists>(a, w, b)\<in>edges (ind (insert e F)).
          nodes_connected (delete_edge a w b (ind (insert e F))) a b"
      apply (rule bexI[where x="(a,w,a)"])
      using * p by auto
    then
      have "\<not> forest (ind (insert e F))"
        unfolding forest_def forest_axioms_def by blast
    then show ?case by auto
  next
    case (15 e)
    then show ?case by auto
  next
    case 16
    thus ?case by force
  next
    case 17
    thus ?case by auto
  next
    case (18 a b)
    then show ?case apply auto
        subgoal for w apply(rule exI[where x="[(a, w, b)]"]) by force
        subgoal for w apply(rule exI[where x="[(a, w, b)]"]) apply simp by blast
        done
  next
    case 19 
    thus ?case by (auto split: prod.split )
  next
    case 20
    thus ?case by auto 
  next
    case 21
    thus ?case apply sepref_to_hoare apply sep_auto by(auto simp: pure_fold list_assn_emp)   
  next
    case (22 l)
    then show ?case using max_node_is_Max_V by auto
  next
    case 23
    then show ?case apply sepref_to_hoare by sep_auto
  qed
  
  subsection \<open>Showing the equivalence of minimum spanning forest definitions\<close>
  
  text \<open>As the definition of the minimum spanning forest from the minWeightBasis algorithm differs
    from the one of our graph formalization, we new show their equivalence.\<close>

  lemma spanning_forest_eq: "s.SpanningForest E' = spanning_forest (ind E') (ind E)"
  proof rule
    assume t: "s.SpanningForest E'"
    have f: "(forest (ind E'))" and sub: "subgraph (ind E') (ind E)" and
        n: "(\<forall>x\<in>E - E'.  \<not> (forest (ind ( insert x E')) \<and> subgraph (ind ( insert x E')) (ind E)))"
      using t[unfolded  s.SpanningForest_def ]  by auto
  
    have vE: "valid_graph (ind E)" apply(rule ind_valid_graph) by simp
   
    have "\<And>x. x\<in>E-E' \<Longrightarrow> subgraph (ind ( insert x E')) (ind E)"
      using sub unfolding subgraph_def by auto
    with n have "(\<forall>x\<in>E - E'.  \<not> (forest (ind ( insert x E'))))" by blast
    then have n': "(\<forall>(a,w,b)\<in>edges (ind E) - edges (ind E').  \<not> (forest (add_edge a w b (ind E'))))"
      using valid_graph.E_validD[OF vE]  by(auto simp: add_edge_def insert_absorb)  
  
    have mc: "maximally_connected (ind E') (ind E)"
      apply(rule valid_graph.forest_maximally_connected_incl_max1) by fact+
    
    show " spanning_forest (ind E') (ind E)"
      unfolding spanning_forest_def using f sub mc by blast
  next
    assume t: "spanning_forest (ind E') (ind E)"
    have  f: "(forest (ind E'))" and sub: "subgraph (ind E') (ind E)" and
        n: "maximally_connected (ind E') (ind E)" using t[unfolded spanning_forest_def] by auto
  
    have i: "\<And>x. x\<in>E-E' \<Longrightarrow> subgraph (ind ( insert x E')) (ind E)"
      using sub unfolding subgraph_def by auto 
    have vE: "valid_graph (ind E)" apply(rule ind_valid_graph) by simp
   
    have "\<forall>(a, w, b)\<in>edges (ind E) - edges (ind E'). \<not> forest (add_edge a w b (ind E'))"
      apply(rule valid_graph.forest_maximally_connected_incl_max2) by fact+
    then have t: "\<And>a w b. (a, w, b)\<in>edges (ind E) - edges (ind E')
                   \<Longrightarrow> \<not> forest (add_edge a w b (ind E'))" 
      by blast
      
    have ii: "(\<forall>x\<in>E - E'.  \<not> (forest (ind ( insert x E'))))"
      apply (auto simp: add_edge_def)
      subgoal for a w b using t[of a w b] valid_graph.E_validD[OF vE] 
        by(auto simp: add_edge_def insert_absorb) 
      done
  
    from i ii have 
      iii: "(\<forall>x\<in>E - E'. \<not>(forest (ind ( insert x E')) \<and> subgraph (ind ( insert x E')) (ind E)))"
      by blast 
  
    show "s.SpanningForest E'"
      unfolding s.SpanningForest_def using iii f sub  by blast 
  qed
  
  lemma edge_weight_alt: "edge_weight G = sum (\<lambda>(u,w,v). w) (edges G)"
  proof -
    have f: "fst o snd  = (\<lambda>(u,w,v). w) " by auto
    show ?thesis unfolding edge_weight_def f by (auto cong: ) 
  qed
  
  lemma MSF_eq: "s.MSF E' = minimum_spanning_forest (ind E') (ind E)"
    unfolding s.MSF_def minimum_spanning_forest_def optimal_forest_def
    unfolding spanning_forest_eq edge_weight_alt
  proof safe
    fix F'
    assume "spanning_forest (ind E') (ind E)"
      and B: "(\<forall>B'. spanning_forest (ind B') (ind E)
             \<longrightarrow> (\<Sum>(u, w, v)\<in>E'. w) \<le> (\<Sum>(u, w, v)\<in>B'. w))"
      and sf: "spanning_forest F' (ind E)"
    from sf have "subgraph F' (ind E)" by(auto simp: spanning_forest_def)
    then have "F' = ind (edges F')" unfolding subgraph_def by auto
    with B sf show "(\<Sum>(u, w, v)\<in>edges (ind E'). w) \<le> (\<Sum>(u, w, v)\<in>edges F'. w)" by auto 
  qed auto
    
  lemma kruskal_correct:
    "<emp> kruskal (return L) (\<lambda>(u,w,v). return (u,v)) ()
      <\<lambda>F. \<up> (distinct F \<and> set F \<subseteq> E \<and> minimum_spanning_forest (ind (set F)) (ind E))>\<^sub>t"
    using s.kruskal_correct_forest unfolding MSF_eq by auto
  
  definition (in -) "kruskal_algo L = kruskal (return L) (\<lambda>(u,w,v). return (u,v)) ()"

end


subsection \<open>Outside the locale\<close>


definition "GD_from_list_\<alpha>_weight L e = (case e of (u,w,v) \<Rightarrow> w)"
abbreviation "GD_from_list_\<alpha>_graph G L \<equiv> \<lparr>nodes=fst ` (set G) \<union> (snd \<circ> snd) ` (set G), edges=set L\<rparr>"
  
lemma corr: "
  <emp> kruskal_algo L
     <\<lambda>F. \<up> (set F \<subseteq> set L \<and>               
       minimum_spanning_forest (GD_from_list_\<alpha>_graph L F) (GD_from_list_\<alpha>_graph L L))>\<^sub>t"
  by(sep_auto heap: fromlist.kruskal_correct simp:  kruskal_algo_def  ) 
 

lemma kruskal_correct: "<emp> kruskal_algo L
     <\<lambda>F. \<up> (set F \<subseteq> set L \<and>
       spanning_forest (GD_from_list_\<alpha>_graph L F) (GD_from_list_\<alpha>_graph L L)
      \<and> (\<forall>F'. spanning_forest (GD_from_list_\<alpha>_graph L F') (GD_from_list_\<alpha>_graph L L) 
               \<longrightarrow>  sum (\<lambda>(u,w,v). w) (set F) \<le> sum (\<lambda>(u,w,v). w) (set F')))>\<^sub>t"
proof - 
  interpret fromlist L by unfold_locales
  have *: "\<And>F'. edge_weight (ind F') = sum (\<lambda>(u,w,v). w) F'"
    unfolding edge_weight_def apply auto by (metis fn_snd_conv fst_def)
  show ?thesis using *
    by (sep_auto heap: corr simp: minimum_spanning_forest_def optimal_forest_def)
qed


subsection \<open>Code export\<close>

export_code kruskal_algo checking SML_imp 

ML_val \<open>
  val export_nat = @{code integer_of_nat}
  val import_nat = @{code nat_of_integer}
  val export_int = @{code integer_of_int}
  val import_int = @{code int_of_integer}
  val import_list = map (fn (a,b,c) => (import_nat a, (import_int b, import_nat c)))
  val export_list = map (fn (a,(b,c)) => (export_nat a, export_int b, export_nat c))
  val export_Some_list = (fn SOME l => SOME (export_list l) | NONE => NONE)

  fun kruskal l = @{code kruskal} (fn () => import_list l) (fn (a,(_,c)) => fn () => (a,c)) () ()
                     |> export_list 
  fun kruskal_algo l = @{code kruskal_algo} (import_list l) ()  |> export_list

  val result = kruskal [(1,~9,2),(2,~3,3),(3,~4,1)]
  val result4 = kruskal [(1,~100,4), (3,64,5), (1,13,2), (3,20,2), (2,5,5), (4,80,3), (4,40,5)]

  val result' = kruskal_algo [(1,~9,2),(2,~3,3),(3,~4,1)]
  val result1' = kruskal_algo [(1,~9,2),(2,~3,3),(3,~4,1),(1,5,3)]
  val result2' = kruskal_algo [(1,~9,2),(2,~3,3),(3,~4,1),(1,~4,3)]
  val result3' = kruskal_algo [(1,~9,2),(2,~3,3),(3,~4,1),(1,~4,1)]
  val result4' = kruskal_algo [(1,~100,4), (3,64,5), (1,13,2), (3,20,2), 
                               (2,5,5), (4,80,3), (4,40,5)]
\<close>


end