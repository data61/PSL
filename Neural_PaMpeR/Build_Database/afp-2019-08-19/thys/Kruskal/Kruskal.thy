section \<open>Kruskal interface\<close>

theory Kruskal
imports Kruskal_Misc MinWeightBasis  
begin

text \<open>In order to instantiate Kruskal's algorithm for different graph formalizations we provide
  an interface consisting of the relevant concepts needed for the algorithm, but hiding the concrete
  structure of the graph formalization.
  We thus enable using both undirected graphs and symmetric directed graphs.

  Based on the interface, we show that the set of edges together with the predicate of being 
  cycle free (i.e. a forest) forms the cycle matroid.
  Together with a weight function on the edges we obtain a \<open>weighted_matroid\<close> and thus
  an instance of the minimum weight basis algorithm, which is an abstract version of Kruskal.\<close>
 
  
locale Kruskal_interface = 
  fixes E :: "'edge set"
    and V :: "'a set"
    and vertices :: "'edge \<Rightarrow> 'a set"
    and joins :: "'a \<Rightarrow> 'a \<Rightarrow> 'edge \<Rightarrow> bool"
    and forest :: "'edge set \<Rightarrow> bool"
    and connected :: "'edge set \<Rightarrow> ('a*'a) set"
    and weight :: "'edge \<Rightarrow> 'b::{linorder, ordered_comm_monoid_add}"
 assumes 
      finiteE[simp]: "finite E"  
   and forest_subE: "forest E' \<Longrightarrow> E' \<subseteq> E" 
   and forest_empty: "forest {}"
   and forest_mono: "forest X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> forest Y"  
   and connected_same: "(u,v) \<in> connected {} \<longleftrightarrow> u=v \<and> v\<in>V" 
   and findaugmenting_aux: "E1 \<subseteq> E \<Longrightarrow> E2 \<subseteq> E \<Longrightarrow> (u,v) \<in> connected E1 \<Longrightarrow> (u,v)\<notin> connected E2
           \<Longrightarrow> \<exists>a b e. (a,b) \<notin> connected E2 \<and> e \<notin> E2 \<and> e \<in> E1 \<and> joins a b e" 
   and augment_forest: "forest F \<Longrightarrow> e \<in> E-F \<Longrightarrow> joins u v e
           \<Longrightarrow> forest (insert e F) \<longleftrightarrow> (u,v) \<notin> connected F"  
   and equiv: "F \<subseteq> E \<Longrightarrow> equiv V (connected F)"
   and connected_in: "F \<subseteq> E \<Longrightarrow> connected F \<subseteq> V \<times> V"      
   and insert_reachable: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> F \<subseteq> E \<Longrightarrow> e\<in>E \<Longrightarrow> joins x y e
           \<Longrightarrow> connected (insert e F) = per_union (connected F) x y"   
   and exhaust: "\<And>x. x\<in>E \<Longrightarrow> \<exists>a b. joins a b x"
   and vertices_constr: "\<And>a b e. joins a b e \<Longrightarrow> {a,b} \<subseteq> vertices e"
   and joins_sym: "\<And>a b e. joins a b e = joins b a e"
   and selfloop_no_forest: "\<And>e. e\<in>E \<Longrightarrow> joins a a e \<Longrightarrow> ~forest (insert e F)"
   and finite_vertices: "\<And>e. e\<in>E \<Longrightarrow> finite (vertices e)"
  
  and edgesinvertices: "\<Union>( vertices ` E) \<subseteq> V"
  and finiteV[simp]: "finite V"
  and joins_connected: "joins a b e \<Longrightarrow> T\<subseteq>E \<Longrightarrow> e\<in>T \<Longrightarrow> (a,b) \<in> connected T"

begin

subsection \<open>Derived facts\<close> 

lemma joins_in_V: "joins a b e \<Longrightarrow> e\<in>E \<Longrightarrow> a\<in>V \<and> b\<in>V"
  apply(frule vertices_constr) using edgesinvertices by blast

  lemma finiteE_finiteV: "finite E \<Longrightarrow> finite V"
    using finite_vertices by auto
 
lemma E_inV: "\<And>e. e\<in>E \<Longrightarrow> vertices e \<subseteq> V"
  using edgesinvertices by auto  

definition "CC E' x = (connected E')``{x}"      

lemma sameCC_reachable: "E' \<subseteq> E \<Longrightarrow> u\<in>V \<Longrightarrow> v\<in>V \<Longrightarrow> CC E' u = CC E' v \<longleftrightarrow> (u,v) \<in> connected E'"
  unfolding CC_def using  equiv_class_eq_iff[OF equiv ] by auto

definition "CCs E' = quotient V (connected E')"  

lemma "quotient V Id = {{v}|v. v\<in>V}" unfolding quotient_def by auto  

lemma CCs_empty: "CCs {} = {{v}|v. v\<in>V}"   
  unfolding CCs_def unfolding quotient_def using connected_same by auto

lemma CCs_empty_card: "card (CCs {}) = card V"   
proof -
  have i: "{{v}|v. v\<in>V} = (\<lambda>v. {v})`V"  
    by blast 
  have "card (CCs {}) = card {{v}|v. v\<in>V}" 
    using CCs_empty  by auto
  also have "\<dots> = card ((\<lambda>v. {v})`V)" by(simp only: i) 
  also have "\<dots> = card V"
    apply(rule card_image)
    unfolding inj_on_def by auto
  finally show ?thesis .
qed

lemma CCs_imageCC: "CCs F = (CC F) ` V"
  unfolding CCs_def CC_def quotient_def  
  by blast


lemma union_eqclass_decreases_components: 
  assumes "CC F x \<noteq> CC F y" "e \<notin> F" "x\<in>V" "y\<in>V" "F \<subseteq> E" "e\<in>E" "joins x y e" 
  shows "Suc (card (CCs (insert e F))) = card (CCs F)"
proof -  
  from assms(1) have xny: "x\<noteq>y" by blast   
  show ?thesis unfolding CCs_def
    apply(simp only: insert_reachable[OF   assms(3-7)])
    apply(rule unify2EquivClasses_alt)          
         apply(fact assms(1)[unfolded CC_def])                           
        apply fact+
      apply (rule connected_in)  
      apply fact    
     apply(rule equiv) 
     apply fact  
    by (fact finiteV)      
qed

lemma forest_CCs: assumes "forest E'" shows "card (CCs E') + card E' = card V"
proof -
  from assms have "finite E'" using forest_subE
    using finiteE finite_subset by blast
  from this assms show ?thesis
  proof(induct E') 
    case (insert x F)
    then have xE: "x\<in>E" using forest_subE by auto
    from this obtain a b where xab: "joins a b x"  using exhaust by blast
    { assume "a=b"
      with xab xE selfloop_no_forest insert(4) have "False" by auto
    }
    then have xab': "a\<noteq>b" by auto
    from insert(4) forest_mono have fF: "forest F" by auto
    with insert(3) have eq: "card (CCs F) + card F = card V" by auto 

    from insert(4) forest_subE have k: "F \<subseteq> E" by auto     
    from xab xab' have abV: "a\<in>V" "b\<in>V" using vertices_constr E_inV xE by fastforce+

    have "(a,b) \<notin> connected F" 
      apply(subst augment_forest[symmetric])
         apply (rule fF)
      using xE xab xab insert by auto
    with k abV sameCC_reachable have "CC F a \<noteq> CC F b" by auto 
    have "Suc (card (CCs (insert x F))) = card (CCs F)" 
      apply(rule union_eqclass_decreases_components)  
      by fact+ 
    then show ?case using xab insert(1,2) eq   by auto 
  qed (simp add: CCs_empty_card)
qed

lemma pigeonhole_CCs: 
  assumes finiteV: "finite V" and cardlt: "card (CCs E1) < card (CCs E2)"
  shows "(\<exists>u v. u\<in>V \<and> v\<in>V \<and> CC E1 u = CC E1 v \<and> CC E2 u \<noteq> CC E2 v)"  
proof (rule ccontr, clarsimp)
  assume "\<forall>u. u \<in> V \<longrightarrow> (\<forall>v. CC E1 u = CC E1 v \<longrightarrow> v \<in> V \<longrightarrow> CC E2 u = CC E2 v)"
  then have "\<And>u v. u\<in>V \<Longrightarrow> v\<in>V \<Longrightarrow> CC E1 u = CC E1 v \<Longrightarrow> CC E2 u = CC E2 v" by blast

  with coarser[OF finiteV] have "card ((CC E1) ` V) \<ge> card ((CC E2) ` V)" by blast

  with CCs_imageCC cardlt show "False" by auto
qed

subsection \<open>The edge set and forest form the cycle matroid\<close> 
 

theorem assumes f1: "forest E1"
  and f2: "forest E2"  
  and c: "card E1 > card E2"
shows augment: "\<exists>e\<in>E1-E2. forest (insert e E2)"
proof -
  \<comment> \<open>as E1 and E2 are both forests, and E1 has more edges than E2, E2 has more connected
        components than E1\<close> 
  from forest_CCs[OF f1] forest_CCs[OF f2] c have "card (CCs E1) < card (CCs E2)" by linarith

  \<comment> \<open>by an pigeonhole argument, we can obtain two vertices u and v
     that are in the same components of E1, but in different components of E2\<close>
  then obtain u v where sameCCinE1: "CC E1 u = CC E1 v" and
    diffCCinE2: "CC E2 u \<noteq> CC E2 v" and k: "u \<in> V" "v \<in> V"
    using pigeonhole_CCs[OF finiteV] by blast   

  from diffCCinE2 have unv: "u \<noteq> v" by auto

  \<comment> \<open>this means that there is a path from u to v in E1 ...\<close>   
  from f1 forest_subE have e1: "E1 \<subseteq> E" by auto    
  with   sameCC_reachable k sameCCinE1 have pathinE1: "(u, v) \<in> connected E1" 
    by auto 
      \<comment> \<open>... but none in E2\<close>  
  from f2 forest_subE have e2: "E2 \<subseteq> E" by auto    
  with   sameCC_reachable k diffCCinE2
  have nopathinE2: "(u, v) \<notin> connected E2" 
    by auto

  \<comment> \<open>hence, we can find vertices a and b that are not connected in E2,
          but are connected by an edge in E1\<close>    
  obtain a b e where pe: "(a,b) \<notin> connected E2" and abE2: "e \<notin> E2"
    and abE1: "e \<in> E1" and "joins a b e"
    using findaugmenting_aux[OF e1 e2 pathinE1 nopathinE2]    by auto

  with forest_subE[OF f1] have "e \<in> E" by auto
  from abE1 abE2 have abdif: "e \<in> E1 - E2" by auto
  with e1 have "e \<in> E - E2" by auto

  \<comment> \<open>we can savely add this edge between a and b to E2 and obtain a bigger forest\<close>    
  have "forest (insert e E2)" apply(subst augment_forest)
    by fact+
  then show "\<exists>e\<in>E1-E2. forest (insert e E2)" using abdif
    by blast
qed

sublocale weighted_matroid E forest weight
proof             
  have "forest {}" using forest_empty by auto
  then show "\<exists>X. forest X" by blast 
qed (auto simp: forest_subE forest_mono augment)

end \<comment> \<open>locale @{text Kruskal_interface}\<close>

end