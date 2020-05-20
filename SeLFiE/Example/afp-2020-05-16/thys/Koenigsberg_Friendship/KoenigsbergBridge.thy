(*
Title:KoenigsbergBridge.thy
Author:Wenda Li
*)

theory KoenigsbergBridge imports MoreGraph
begin

section\<open>Definition of Eulerian trails and circuits\<close>

definition (in valid_unMultigraph) is_Eulerian_trail:: "'v\<Rightarrow>('v,'w) path\<Rightarrow>'v\<Rightarrow> bool" where
  "is_Eulerian_trail v ps v'\<equiv> is_trail v ps v' \<and> edges (rem_unPath ps G) = {}"

definition (in valid_unMultigraph) is_Eulerian_circuit:: "'v \<Rightarrow> ('v,'w) path \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_Eulerian_circuit v ps v'\<equiv> (v=v') \<and> (is_Eulerian_trail v ps v')"

section\<open>Necessary conditions for Eulerian trails and circuits\<close>

lemma (in valid_unMultigraph) euclerian_rev:
  "is_Eulerian_trail v' (rev_path ps) v=is_Eulerian_trail v ps v' "
proof -
  have "is_trail v' (rev_path ps) v=is_trail v ps v'"
    by (metis is_trail_rev)
  moreover have "edges (rem_unPath (rev_path ps) G)=edges (rem_unPath ps G)"
    by (metis rem_unPath_graph)
  ultimately show ?thesis unfolding is_Eulerian_trail_def by auto
qed

(*Necessary conditions for Eulerian circuits*)
theorem (in valid_unMultigraph) euclerian_cycle_ex:
  assumes "is_Eulerian_circuit v ps v'" "finite V" "finite E"
  shows "\<forall>v\<in>V. even (degree v G)"
proof -
  obtain v ps v' where cycle:"is_Eulerian_circuit v ps v'" using assms by auto
  hence "edges (rem_unPath ps G) = {}"
    unfolding is_Eulerian_circuit_def is_Eulerian_trail_def
    by simp
  moreover have "nodes (rem_unPath ps G)=nodes G" by auto
  ultimately have "rem_unPath ps G = G \<lparr>edges:={}\<rparr>" by auto
  hence "num_of_odd_nodes (rem_unPath ps G) = 0" by (metis assms(2) odd_nodes_no_edge)
  moreover have "v=v'"
    by (metis \<open>is_Eulerian_circuit v ps v'\<close> is_Eulerian_circuit_def)
  hence "num_of_odd_nodes (rem_unPath ps G)=num_of_odd_nodes G"
    by (metis assms(2) assms(3) cycle is_Eulerian_circuit_def
        is_Eulerian_trail_def rem_UnPath_cycle)
  ultimately have "num_of_odd_nodes G=0" by auto
  moreover have "finite(odd_nodes_set G)"
    using \<open>finite V\<close> unfolding odd_nodes_set_def by auto
  ultimately have "odd_nodes_set G = {}" unfolding num_of_odd_nodes_def by auto
  thus ?thesis unfolding odd_nodes_set_def by auto
qed

(*Necessary conditions for Eulerian trails*)
theorem (in valid_unMultigraph) euclerian_path_ex:
  assumes "is_Eulerian_trail v ps v'" "finite V" "finite E"
  shows "(\<forall>v\<in>V. even (degree v G)) \<or> (num_of_odd_nodes G =2)"
proof -
  obtain v ps v' where path:"is_Eulerian_trail v ps v'" using assms by auto
  hence "edges (rem_unPath ps G) = {}"
    unfolding  is_Eulerian_trail_def
    by simp
  moreover have "nodes (rem_unPath ps G)=nodes G" by auto
  ultimately have "rem_unPath ps G = G \<lparr>edges:={}\<rparr>" by auto
  hence odd_nodes: "num_of_odd_nodes (rem_unPath ps G) = 0"
    by (metis assms(2) odd_nodes_no_edge)
  have "v\<noteq>v' \<Longrightarrow> ?thesis"
    proof (cases "even(degree v' G)")
      case True
      assume "v\<noteq>v'"
      have "is_trail v ps v'" by (metis is_Eulerian_trail_def path)
      hence "num_of_odd_nodes (rem_unPath ps G) = num_of_odd_nodes G
          + (if even (degree v G) then 2 else 0)"
        using rem_UnPath_even True \<open>finite V\<close> \<open>finite E\<close> \<open>v\<noteq>v'\<close> by auto
      hence "num_of_odd_nodes G + (if even (degree v G) then 2 else 0)=0"
        using odd_nodes by auto
      hence "num_of_odd_nodes G = 0" by auto
      moreover have "finite(odd_nodes_set G)"
        using \<open>finite V\<close> unfolding odd_nodes_set_def by auto
      ultimately have "odd_nodes_set G = {}" unfolding num_of_odd_nodes_def by auto
      thus ?thesis unfolding odd_nodes_set_def by auto
    next
      case False
      assume "v\<noteq>v'"
      have "is_trail v ps v'" by (metis is_Eulerian_trail_def path)
      hence "num_of_odd_nodes (rem_unPath ps G) = num_of_odd_nodes G
          + (if odd (degree v G) then -2 else 0)"
        using rem_UnPath_odd False \<open>finite V\<close> \<open>finite E\<close> \<open>v\<noteq>v'\<close> by auto
      hence odd_nodes_if: "num_of_odd_nodes G + (if odd (degree v G) then -2 else 0)=0"
        using odd_nodes by auto
      have "odd (degree v G) \<Longrightarrow> ?thesis"
        proof -
          assume "odd (degree v G)"
          hence "num_of_odd_nodes G = 2" using odd_nodes_if by auto
          thus ?thesis by simp
        qed
      moreover have "even(degree v G) \<Longrightarrow> ?thesis"
        proof -
          assume "even (degree v G)"
          hence "num_of_odd_nodes G = 0" using odd_nodes_if by auto
          moreover have "finite(odd_nodes_set G)"
            using \<open>finite V\<close> unfolding odd_nodes_set_def by auto
          ultimately have "odd_nodes_set G = {}" unfolding num_of_odd_nodes_def by auto
          thus ?thesis unfolding odd_nodes_set_def by auto
        qed
      ultimately show ?thesis by auto
    qed
  moreover have "v=v'\<Longrightarrow> ?thesis"
    by (metis assms(2) assms(3) euclerian_cycle_ex is_Eulerian_circuit_def path)
  ultimately show ?thesis by auto
qed

section\<open>Specific case of the Konigsberg Bridge Problem\<close>

(*to denote the four landmasses*)
datatype kon_node = a | b | c | d

(*to denote the seven bridges*)
datatype kon_bridge = ab1 | ab2 | ac1 | ac2 | ad1 | bd1 | cd1

definition kon_graph :: "(kon_node,kon_bridge) graph" where
  "kon_graph\<equiv>\<lparr>nodes={a,b,c,d},
              edges={(a,ab1,b), (b,ab1,a),
                     (a,ab2,b), (b,ab2,a),
                     (a,ac1,c), (c,ac1,a),
                     (a,ac2,c), (c,ac2,a),
                     (a,ad1,d), (d,ad1,a),
                     (b,bd1,d), (d,bd1,b),
                     (c,cd1,d), (d,cd1,c)} \<rparr>"

instantiation kon_node :: enum
begin
definition [simp]:  "enum_class.enum =[a,b,c,d]"
definition  [simp]: "enum_class.enum_all P \<longleftrightarrow> P a \<and> P b \<and> P c \<and> P d"
definition   [simp]:"enum_class.enum_ex P \<longleftrightarrow> P a \<or> P b \<or> P c \<or> P d"
instance proof qed (auto,(case_tac x,auto)+)
end

instantiation kon_bridge :: enum
begin
definition [simp]:"enum_class.enum =[ab1,ab2,ac1,ac2,ad1,cd1,bd1]"
definition  [simp]:"enum_class.enum_all P \<longleftrightarrow> P ab1 \<and> P ab2 \<and> P ac1 \<and> P ac2 \<and> P ad1  \<and> P bd1
    \<and> P cd1"
definition   [simp]:"enum_class.enum_ex P \<longleftrightarrow>  P ab1 \<or> P ab2 \<or> P ac1 \<or> P ac2 \<or> P ad1  \<or> P bd1
    \<or> P cd1"
instance proof qed (auto,(case_tac x,auto)+)
end

interpretation   kon_graph: valid_unMultigraph kon_graph
proof (unfold_locales)
  show "fst ` edges kon_graph \<subseteq> nodes kon_graph" by eval
next
  show "snd ` snd ` edges kon_graph \<subseteq> nodes kon_graph"  by eval
next
  have " \<forall>v w u'. ((v, w, u') \<in> edges kon_graph) = ((u', w, v) \<in> edges kon_graph)"
    by eval
  thus "\<And>v w u'. ((v, w, u') \<in> edges kon_graph) = ((u', w, v) \<in> edges kon_graph)" by simp
next
  have "\<forall>v w. (v, w, v) \<notin> edges kon_graph"  by eval
  thus "\<And>v w. (v, w, v) \<notin> edges kon_graph" by simp
qed

(*The specific case of the Konigsberg Bridge Problem does not have a solution*)
theorem "\<not>kon_graph.is_Eulerian_trail v1 p v2"
proof
  assume "kon_graph.is_Eulerian_trail  v1 p v2"
  moreover have "finite (nodes kon_graph)" by (metis finite_code)
  moreover have "finite (edges kon_graph)" by (metis finite_code)
  ultimately have contra:
    "(\<forall>v\<in>nodes kon_graph. even (degree v kon_graph)) \<or>(num_of_odd_nodes kon_graph =2)"
    by (metis kon_graph.euclerian_path_ex)
  have "odd(degree a kon_graph)" by eval
  moreover have "odd(degree b kon_graph)" by eval
  moreover have "odd(degree c kon_graph)" by eval
  moreover have "odd(degree d kon_graph)" by eval
  ultimately have "\<not>(num_of_odd_nodes kon_graph =2)" by eval
  moreover have "\<not>(\<forall>v\<in>nodes kon_graph. even (degree v kon_graph))" by eval
  ultimately show False using contra by auto
qed

section\<open>Sufficient conditions for Eulerian trails and circuits\<close>

lemma (in valid_unMultigraph) eulerian_cons:
  assumes
    "valid_unMultigraph.is_Eulerian_trail (del_unEdge v0 w v1 G) v1 ps v2"
    "(v0,w,v1)\<in> E"
  shows "is_Eulerian_trail v0 ((v0,w,v1)#ps) v2"
proof -
  have valid:"valid_unMultigraph (del_unEdge v0 w v1 G)"
    using  valid_unMultigraph_axioms by auto
  hence distinct:"valid_unMultigraph.is_trail (del_unEdge v0 w v1 G) v1 ps v2"
    using assms unfolding valid_unMultigraph.is_Eulerian_trail_def[OF valid]
    by auto
  hence "set ps \<subseteq> edges (del_unEdge v0 w v1 G)"
    using valid_unMultigraph.path_in_edges[OF valid] by auto
  moreover have "(v0,w,v1)\<notin>edges (del_unEdge v0 w v1 G)"
    unfolding del_unEdge_def by auto
  moreover have "(v1,w,v0)\<notin>edges (del_unEdge v0 w v1 G)"
    unfolding del_unEdge_def by auto
  ultimately have "(v0,w,v1)\<notin>set ps" "(v1,w,v0)\<notin>set ps"  by auto
  moreover have "is_trail v1 ps v2"
    using distinct_path_intro[OF distinct] .
  ultimately have "is_trail v0 ((v0,w,v1)#ps) v2"
    using \<open>(v0,w,v1)\<in> E\<close> by auto
  moreover have "edges (rem_unPath ps (del_unEdge v0 w v1 G)) ={}"
    using assms unfolding valid_unMultigraph.is_Eulerian_trail_def[OF valid]
    by auto
  hence "edges (rem_unPath ((v0,w,v1)#ps) G)={}"
    by (metis rem_unPath.simps(2))
  ultimately show ?thesis unfolding is_Eulerian_trail_def by auto
qed

lemma (in valid_unMultigraph) eulerian_cons':
  assumes
    "valid_unMultigraph.is_Eulerian_trail (del_unEdge v2 w v3 G) v1 ps v2"
    "(v2,w,v3)\<in> E"
  shows "is_Eulerian_trail v1 (ps@[(v2,w,v3)]) v3"
proof -
  have valid:"valid_unMultigraph (del_unEdge v3 w v2 G)"
    using valid_unMultigraph_axioms del_unEdge_valid by auto
  have "del_unEdge v2 w v3 G=del_unEdge v3 w v2 G"
    by (metis delete_edge_sym)
  hence "valid_unMultigraph.is_Eulerian_trail (del_unEdge v3 w v2 G) v2
        (rev_path ps) v1" using assms valid_unMultigraph.euclerian_rev[OF valid]
    by auto
  hence "is_Eulerian_trail v3 ((v3,w,v2)#(rev_path ps)) v1"
    using eulerian_cons by (metis assms(2) corres)
  hence "is_Eulerian_trail v1 (rev_path((v3,w,v2)#(rev_path ps))) v3"
    using euclerian_rev by auto
  moreover have "rev_path((v3,w,v2)#(rev_path ps)) = rev_path(rev_path ps)@[(v2,w,v3)]"
    unfolding rev_path_def by auto
  hence "rev_path((v3,w,v2)#(rev_path ps))=ps@[(v2,w,v3)]" by auto
  ultimately show ?thesis by auto
qed

lemma eulerian_split:
  assumes "nodes G1 \<inter> nodes G2 = {}" "edges G1 \<inter> edges G2={}"
    "valid_unMultigraph G1" "valid_unMultigraph G2"
    "valid_unMultigraph.is_Eulerian_trail  G1 v1 ps1 v1'"
    "valid_unMultigraph.is_Eulerian_trail  G2 v2 ps2 v2'"
  shows "valid_unMultigraph.is_Eulerian_trail \<lparr>nodes=nodes G1 \<union> nodes G2,
          edges=edges G1 \<union> edges G2 \<union> {(v1',w,v2),(v2,w,v1')}\<rparr> v1 (ps1@(v1',w,v2)#ps2) v2'"
proof -
  have "valid_graph G1" using \<open>valid_unMultigraph G1\<close> valid_unMultigraph_def by auto
  have "valid_graph G2" using \<open>valid_unMultigraph G2\<close> valid_unMultigraph_def by auto
  obtain G where G:"G=\<lparr>nodes=nodes G1 \<union> nodes G2, edges=edges G1 \<union> edges G2
      \<union> {(v1',w,v2),(v2,w,v1')}\<rparr>"
    by metis
  have "v1'\<in>nodes G1"
    by (metis (full_types) \<open>valid_graph G1\<close> assms(3) assms(5) valid_graph.is_path_memb
        valid_unMultigraph.is_trail_intro valid_unMultigraph.is_Eulerian_trail_def)
  moreover have "v2\<in>nodes G2"
    by (metis (full_types) \<open>valid_graph G2\<close> assms(4) assms(6) valid_graph.is_path_memb
        valid_unMultigraph.is_trail_intro valid_unMultigraph.is_Eulerian_trail_def)
  ultimately have "valid_unMultigraph \<lparr>nodes=nodes G1 \<union> nodes G2, edges=edges G1 \<union> edges G2 \<union>
                   {(v1',w,v2),(v2,w,v1')}\<rparr>"
    using
      valid_unMultigraph.corres[OF \<open>valid_unMultigraph G1\<close>]
      valid_unMultigraph.no_id[OF \<open>valid_unMultigraph G1\<close>]
      valid_unMultigraph.corres[OF \<open>valid_unMultigraph G2\<close>]
      valid_unMultigraph.no_id[OF \<open>valid_unMultigraph G2\<close>]
      valid_graph.E_validD[OF \<open>valid_graph G1\<close>]
      valid_graph.E_validD[OF \<open>valid_graph G2\<close>]
      \<open>nodes G1 \<inter> nodes G2 = {}\<close>
    proof (unfold_locales,auto)
      fix aa ab ba
      assume  "(aa, ab, ba) \<in> edges G1"
      thus "ba \<in> nodes G1" by (metis \<open>\<And>v' v e. (v, e, v') \<in> edges G1 \<Longrightarrow> v' \<in> nodes G1\<close>)
    next
      fix aa ab ba
      assume "ba \<notin> nodes G2"  "(aa, ab, ba) \<in> edges G2"
      thus "ba \<in> nodes G1" by (metis \<open>valid_graph G2\<close> valid_graph.E_validD(2))
    qed
  hence valid: "valid_unMultigraph G" using G by auto
  hence valid':"valid_graph G" using valid_unMultigraph_def by auto
  moreover have "valid_unMultigraph.is_trail G v1 (ps1@((v1',w,v2)#ps2)) v2'"
    proof -
      have ps1_G:"valid_unMultigraph.is_trail G v1 ps1 v1'"
        proof -
          have "valid_unMultigraph.is_trail G1 v1 ps1 v1'" using assms
            by (metis valid_unMultigraph.is_Eulerian_trail_def)
          moreover have "edges G1 \<subseteq> edges G" by (metis G UnI1 Un_assoc select_convs(2) subrelI)
          moreover have "nodes G1 \<subseteq> nodes G" by (metis G inf_sup_absorb le_iff_inf select_convs(1))
          ultimately show ?thesis
            using distinct_path_subset[of G1 G,OF \<open>valid_unMultigraph G1\<close> valid] by auto
        qed
      have ps2_G:"valid_unMultigraph.is_trail G v2 ps2 v2'"
        proof -
          have "valid_unMultigraph.is_trail G2 v2 ps2 v2'" using assms
            by (metis valid_unMultigraph.is_Eulerian_trail_def)
          moreover have "edges G2 \<subseteq> edges G" by (metis G inf_sup_ord(3) le_supE select_convs(2))
          moreover have "nodes G2 \<subseteq> nodes G" by (metis G inf_sup_ord(4) select_convs(1))
          ultimately show ?thesis
            using distinct_path_subset[of G2 G,OF \<open>valid_unMultigraph G2\<close> valid] by auto
        qed
      have "valid_graph.is_path G v1 (ps1@((v1',w,v2)#ps2)) v2'"
        proof -
          have "valid_graph.is_path  G v1 ps1 v1'"
            by (metis ps1_G valid valid_unMultigraph.is_trail_intro)
          moreover have "valid_graph.is_path G v2 ps2 v2'"
            by (metis ps2_G valid valid_unMultigraph.is_trail_intro)
          moreover have "(v1',w,v2) \<in> edges G"
            using G by auto
          ultimately show ?thesis
            using valid_graph.is_path_split'[OF valid',of v1 ps1 v1' w v2 ps2 v2'] by auto
        qed
      moreover have "distinct (ps1@((v1',w,v2)#ps2))"
        proof -
          have "distinct ps1" by (metis ps1_G valid valid_unMultigraph.is_trail_path)
          moreover have "distinct ps2"
            by (metis ps2_G valid valid_unMultigraph.is_trail_path)
          moreover have "set ps1 \<inter> set ps2 = {}"
            proof -
              have "set ps1 \<subseteq>edges G1"
                by (metis assms(3) assms(5) valid_unMultigraph.is_Eulerian_trail_def
                    valid_unMultigraph.path_in_edges)
              moreover have "set ps2 \<subseteq> edges G2"
                by (metis assms(4) assms(6) valid_unMultigraph.is_Eulerian_trail_def
                    valid_unMultigraph.path_in_edges)
              ultimately show ?thesis using \<open>edges G1 \<inter> edges G2={}\<close> by auto
            qed
          moreover have "(v1',w,v2)\<notin>edges G1"
            using \<open>v2 \<in> nodes G2\<close> \<open>valid_graph G1\<close>
            by (metis Int_iff  all_not_in_conv assms(1) valid_graph.E_validD(2))
          hence "(v1',w,v2)\<notin>set ps1"
            by (metis (full_types) assms(3) assms(5) subsetD valid_unMultigraph.path_in_edges
                valid_unMultigraph.is_Eulerian_trail_def )
          moreover have "(v1',w,v2)\<notin>edges G2"
            using \<open>v1' \<in> nodes G1\<close> \<open>valid_graph G2\<close>
            by (metis  assms(1) disjoint_iff_not_equal valid_graph.E_validD(1))
          hence  "(v1',w,v2)\<notin>set ps2"
            by (metis (full_types)  assms(4) assms(6) in_mono valid_unMultigraph.path_in_edges
                valid_unMultigraph.is_Eulerian_trail_def )
          ultimately show ?thesis using distinct_append by auto
        qed
      moreover have "set (ps1@((v1',w,v2)#ps2)) \<inter> set (rev_path (ps1@((v1',w,v2)#ps2))) = {}"
        proof -
          have "set ps1 \<inter> set (rev_path ps1) = {}"
            by (metis ps1_G valid valid_unMultigraph.is_trail_path)
          moreover have "set (rev_path ps2) \<subseteq> edges G2"
            by (metis assms(4) assms(6) valid_unMultigraph.is_trail_rev
                valid_unMultigraph.is_Eulerian_trail_def valid_unMultigraph.path_in_edges)
          hence "set ps1 \<inter> set (rev_path ps2) = {}"
            using assms
              valid_unMultigraph.path_in_edges[OF \<open>valid_unMultigraph G1\<close>, of v1 ps1 v1']
              valid_unMultigraph.path_in_edges[OF \<open>valid_unMultigraph G2\<close>, of v2 ps2 v2']
            unfolding valid_unMultigraph.is_Eulerian_trail_def[OF \<open>valid_unMultigraph G1\<close>]
              valid_unMultigraph.is_Eulerian_trail_def[OF \<open>valid_unMultigraph G2\<close>]
            by auto
          moreover have "set ps2 \<inter> set (rev_path ps2) = {}"
            by (metis ps2_G valid valid_unMultigraph.is_trail_path)
          moreover have "set (rev_path ps1) \<subseteq>edges G1"
            by (metis assms(3) assms(5) valid_unMultigraph.is_Eulerian_trail_def
                valid_unMultigraph.path_in_edges valid_unMultigraph.euclerian_rev)
          hence "set ps2 \<inter> set (rev_path ps1) = {}"
            by (metis calculation(2) distinct_append distinct_rev_path ps1_G ps2_G rev_path_append
              rev_path_double valid valid_unMultigraph.is_trail_path)
          moreover have "(v2,w,v1')\<notin>set (ps1@((v1',w,v2)#ps2))"
            proof -
              have "(v2,w,v1')\<notin>edges G1"
                using \<open>v2 \<in> nodes G2\<close> \<open>valid_graph G1\<close>
                by (metis Int_iff  all_not_in_conv assms(1) valid_graph.E_validD(1))
              hence "(v2,w,v1')\<notin>set ps1"
                by (metis assms(3) assms(5) split_list valid_unMultigraph.is_trail_split'
                    valid_unMultigraph.is_Eulerian_trail_def)
              moreover have "(v2,w,v1')\<notin>edges G2"
                using \<open>v1' \<in> nodes G1\<close> \<open>valid_graph G2\<close>
                by (metis IntI assms(1) empty_iff valid_graph.E_validD(2))
              hence "(v2,w,v1')\<notin>set ps2"
                by (metis (full_types) assms(4) assms(6) in_mono  valid_unMultigraph.path_in_edges
                    valid_unMultigraph.is_Eulerian_trail_def)
              moreover have "(v2,w,v1')\<noteq>(v1',w,v2)"
                using \<open>v1' \<in> nodes G1\<close> \<open>v2 \<in> nodes G2\<close>
                by (metis IntI Pair_inject  assms(1) assms(5) bex_empty)
              ultimately show ?thesis by auto
            qed
          ultimately show ?thesis using rev_path_append by auto
        qed
      ultimately show ?thesis using valid_unMultigraph.is_trail_path[OF valid]
        by auto
    qed
  moreover have "edges (rem_unPath (ps1@((v1',w,v2)#ps2)) G)= {}"
    proof -
      have "edges (rem_unPath (ps1@((v1',w,v2)#ps2)) G)=edges G -
           (set (ps1@((v1',w,v2)#ps2)) \<union> set (rev_path (ps1@((v1',w,v2)#ps2))))"
        by (metis rem_unPath_edges)
      also have "...=edges G - (set ps1 \<union> set ps2 \<union> set (rev_path ps1) \<union> set (rev_path ps2)
                 \<union> {(v1',w,v2),(v2,w,v1')})" using rev_path_append by auto
      finally have "edges (rem_unPath (ps1@((v1',w,v2)#ps2)) G) = edges G - (set ps1 \<union>
                    set ps2 \<union> set (rev_path ps1) \<union> set (rev_path ps2) \<union> {(v1',w,v2),(v2,w,v1')})" .
      moreover have "edges (rem_unPath ps1 G1)={}"
        by (metis assms(3) assms(5) valid_unMultigraph.is_Eulerian_trail_def)
      hence "edges G1 - (set ps1 \<union> set (rev_path ps1))={}"
        by (metis rem_unPath_edges)
      moreover have "edges (rem_unPath ps2 G2)={}"
        by (metis assms(4) assms(6) valid_unMultigraph.is_Eulerian_trail_def)
      hence "edges G2 - (set ps2 \<union> set (rev_path ps2))={}"
        by (metis rem_unPath_edges)
      ultimately show ?thesis using G by auto
    qed
  ultimately show ?thesis by (metis G valid valid_unMultigraph.is_Eulerian_trail_def)
qed

lemma (in valid_unMultigraph) eulerian_sufficient:
  assumes "finite V" "finite E" "connected" "V\<noteq>{}"
  shows "num_of_odd_nodes G = 2 \<Longrightarrow>
      (\<exists>v\<in>V.\<exists>v'\<in>V.\<exists>ps. odd(degree v G)\<and>odd(degree v' G)\<and>(v\<noteq>v')\<and>is_Eulerian_trail v ps v')"
      and "num_of_odd_nodes G=0 \<Longrightarrow> (\<forall>v\<in>V.\<exists>ps. is_Eulerian_circuit v ps v)"
    using \<open>finite E\<close> \<open>finite V\<close> valid_unMultigraph_axioms  \<open>V\<noteq>{}\<close> \<open>connected\<close>
proof (induct "card E" arbitrary: G rule: less_induct)
  case less
  assume "finite (edges G)" and "finite (nodes G)" and "valid_unMultigraph G" and "nodes G\<noteq>{}"
      and "valid_unMultigraph.connected G" and "num_of_odd_nodes G = 2"
  have "valid_graph G" using \<open>valid_unMultigraph G\<close> valid_unMultigraph_def by auto
  obtain n1 n2 where
      n1: "n1\<in>nodes G" "odd(degree n1 G)"
      and n2: "n2\<in>nodes G" "odd(degree n2 G)"
      and "n1\<noteq>n2" unfolding num_of_odd_nodes_def odd_nodes_set_def
    proof -
      have "\<forall>S. card S=2 \<longrightarrow> (\<exists>n1 n2. n1\<in>S\<and>n2\<in>S\<and>n1\<noteq>n2)"
        by (metis card_eq_0_iff equals0I even_card' even_numeral zero_neq_numeral)
      then obtain t1 t2
          where "t1\<in>{v \<in> nodes G. odd (degree v G)}" "t2\<in>{v \<in> nodes G. odd (degree v G)}" "t1\<noteq>t2"
        using \<open>num_of_odd_nodes G = 2\<close> unfolding num_of_odd_nodes_def odd_nodes_set_def
        by force
      thus ?thesis by (metis (lifting) that mem_Collect_eq)
    qed
  have even_except_two:"\<And>n. n\<in>nodes G\<Longrightarrow> n\<noteq>n1 \<Longrightarrow> n\<noteq>n2 \<Longrightarrow> even(degree n G)"
    proof (rule ccontr)
      fix n assume "n \<in> nodes G"  "n \<noteq> n1" "n \<noteq> n2" "odd (degree n G)"
      have "n\<in> odd_nodes_set G"
        by (metis (mono_tags) \<open>n \<in> nodes G\<close> \<open>odd (degree n G)\<close> mem_Collect_eq odd_nodes_set_def)
      moreover have "n1 \<in> odd_nodes_set G"
        by (metis (mono_tags) mem_Collect_eq n1(1) n1(2) odd_nodes_set_def)
      moreover have "n2 \<in> odd_nodes_set G"
        using n2(1) n2(2) unfolding odd_nodes_set_def by auto
      ultimately have "{n,n1,n2}\<subseteq> odd_nodes_set G" by auto
      moreover have "card{n,n1,n2} \<ge>3" using \<open>n1\<noteq>n2\<close> \<open>n\<noteq>n1\<close> \<open>n\<noteq>n2\<close> by auto
      moreover have "finite (odd_nodes_set G)"
        using \<open>finite (nodes G)\<close> unfolding odd_nodes_set_def by auto
      ultimately have "card (odd_nodes_set G) \<ge> 3"
        using card_mono[of "odd_nodes_set G" "{n, n1, n2}"] by auto
      thus False using \<open>num_of_odd_nodes G = 2\<close> unfolding num_of_odd_nodes_def by auto
    qed
  have "{e \<in> edges G. fst e = n1}\<noteq>{}"
    using n1
    by (metis (full_types) degree_def empty_iff finite.emptyI odd_card)
  then obtain v' w where "(n1,w,v')\<in>edges G" by auto
  have "v'=n2 \<Longrightarrow> (\<exists>v\<in>nodes G. \<exists>v'\<in>nodes G.\<exists>ps. odd (degree v G) \<and> odd (degree v' G)  \<and> v \<noteq> v'
      \<and> valid_unMultigraph.is_Eulerian_trail G v ps v')"
    proof (cases "valid_unMultigraph.connected (del_unEdge n1 w n2 G)")
      assume "v'=n2"
      assume conneted':"valid_unMultigraph.connected (del_unEdge n1 w n2 G)"
      moreover have "num_of_odd_nodes (del_unEdge n1 w n2 G) = 0"
        using \<open>(n1, w, v') \<in> edges G\<close> \<open>finite (edges G)\<close> \<open>finite (nodes G)\<close>  \<open>v' = n2\<close>
          \<open>num_of_odd_nodes G = 2\<close> \<open>valid_unMultigraph G\<close> del_UnEdge_odd_odd n1(2) n2(2)
        by force
      moreover have "finite (edges (del_unEdge n1 w n2 G))"
        using \<open>finite (edges G)\<close> by auto
      moreover have "finite (nodes (del_unEdge n1 w n2 G))"
        using \<open>finite (nodes G)\<close> by auto
      moreover have "edges G - {(n1,w,n2),(n2,w,n1)} \<subset> edges G"
        using Diff_iff Diff_subset \<open>(n1, w, v') \<in> edges G\<close> \<open>v' = n2\<close>
        by fast
      hence "card (edges (del_unEdge n1 w n2 G)) < card (edges G)"
        using \<open>finite (edges G)\<close> psubset_card_mono[of "edges G" "edges G - {(n1,w,n2),(n2,w,n1)}"]
        unfolding del_unEdge_def by auto
      moreover have "valid_unMultigraph (del_unEdge n1 w n2 G)"
        using \<open>valid_unMultigraph G\<close> del_unEdge_valid by auto
      moreover have "nodes (del_unEdge n1 w n2 G) \<noteq> {}"
        by (metis (full_types) del_UnEdge_node empty_iff n1(1))
      ultimately have "\<forall>v\<in>nodes (del_unEdge n1 w n2 G). \<exists>ps. valid_unMultigraph.is_Eulerian_circuit
          (del_unEdge n1 w n2 G) v ps v"
        using less.hyps[of "del_unEdge n1 w n2 G"] by auto
      thus ?thesis using eulerian_cons
        by (metis \<open>(n1, w, v') \<in> edges G\<close> \<open>n1 \<noteq> n2\<close> \<open>v' = n2\<close>  \<open>valid_unMultigraph G\<close>
          \<open>valid_unMultigraph (del_unEdge n1 w n2 G)\<close> del_UnEdge_node n1(1) n1(2) n2(1) n2(2)
          valid_unMultigraph.eulerian_cons valid_unMultigraph.is_Eulerian_circuit_def)
    next
      assume "v'=n2"
      assume not_conneted:"\<not>valid_unMultigraph.connected (del_unEdge n1 w n2 G)"
      have valid0:"valid_unMultigraph (del_unEdge n1 w n2 G)"
        using \<open>valid_unMultigraph G\<close> del_unEdge_valid by auto
      hence valid0':"valid_graph (del_unEdge n1 w n2 G)"
        using valid_unMultigraph_def by auto
      have all_even:"\<forall>n\<in>nodes (del_unEdge n1 w n2 G). even(degree n (del_unEdge n1 w n2 G))"
        proof -
          have "even (degree n1 (del_unEdge n1 w n2 G))"
            using \<open>(n1, w, v') \<in> edges G\<close> \<open>finite (edges G)\<close> \<open>v' = n2\<close> \<open>valid_unMultigraph G\<close> n1
            by (auto simp add: valid_unMultigraph.corres)
          moreover have "even (degree n2 (del_unEdge n1 w n2 G))"
            using  \<open>(n1, w, v') \<in> edges G\<close> \<open>finite (edges G)\<close> \<open>v' = n2\<close> \<open>valid_unMultigraph G\<close> n2
            by (auto simp add: valid_unMultigraph.corres)
          moreover have  "\<And>n. n \<in> nodes (del_unEdge n1 w n2 G) \<Longrightarrow> n \<noteq> n1 \<Longrightarrow> n \<noteq> n2 \<Longrightarrow>
              even (degree n (del_unEdge n1 w n2 G))"
            using valid_unMultigraph.degree_frame[OF \<open>valid_unMultigraph G\<close>,
              of _ n1 n2 w] even_except_two
            by (metis (no_types) \<open>finite (edges G)\<close> del_unEdge_def empty_iff insert_iff
              select_convs(1))
          ultimately show ?thesis by auto
        qed
      have "(n1,w,n2)\<in>edges G" by (metis \<open>(n1, w, v') \<in> edges G\<close> \<open>v' = n2\<close>)
      hence "(n2,w,n1)\<in>edges G" by (metis \<open>valid_unMultigraph G\<close> valid_unMultigraph.corres)
      obtain G1 G2 where
          G1_nodes: "nodes G1={n. \<exists>ps. valid_graph.is_path (del_unEdge n1 w n2 G) n ps n1}"
          and G1_edges: "edges G1={(n,e,n'). (n,e,n')\<in>edges (del_unEdge n1 w n2 G)
            \<and> n\<in>nodes G1 \<and> n'\<in>nodes G1}"
          and G2_nodes:"nodes G2={n. \<exists>ps. valid_graph.is_path (del_unEdge n1 w n2 G) n ps n2}"
          and G2_edges:"edges G2={(n,e,n'). (n,e,n')\<in>edges (del_unEdge n1 w n2 G) \<and> n\<in>nodes G2
            \<and> n'\<in>nodes G2}"
          and G1_G2_edges_union:"edges G1 \<union> edges G2 = edges (del_unEdge n1 w n2 G)"
          and "edges G1 \<inter> edges G2={}"
          and G1_G2_nodes_union:"nodes G1 \<union> nodes G2=nodes (del_unEdge n1 w n2 G)"
          and "nodes G1 \<inter> nodes G2={}"
          and "valid_unMultigraph G1"
          and "valid_unMultigraph G2"
          and "valid_unMultigraph.connected G1"
          and "valid_unMultigraph.connected G2"
        using valid_unMultigraph.connectivity_split[OF \<open>valid_unMultigraph G\<close>
          \<open>valid_unMultigraph.connected G\<close> \<open>\<not> valid_unMultigraph.connected (del_unEdge n1 w n2 G)\<close>
          \<open>(n1, w, n2) \<in> edges G\<close> ] .
      have "edges (del_unEdge n1 w n2 G) \<subset> edges G"
        unfolding del_unEdge_def using \<open>(n1, w, n2)\<in>edges G\<close> \<open>(n2, w, n1)\<in>edges G\<close> by auto
      hence "card (edges G1) < card (edges G)" using G1_G2_edges_union
        by (metis (full_types) \<open>finite (edges G)\<close> inf_sup_absorb less_infI2 psubset_card_mono)
      moreover have "finite (edges G1)"
        using G1_G2_edges_union \<open>finite (edges G)\<close>
        by (metis \<open>edges (del_unEdge n1 w n2 G) \<subset> edges G\<close> finite_Un less_imp_le rev_finite_subset)
      moreover have "nodes G1 \<subseteq> nodes (del_unEdge n1 w n2 G)"
        by (metis G1_G2_nodes_union Un_upper1)
      hence "finite (nodes G1)"
        using  \<open>finite (nodes G)\<close> del_UnEdge_node rev_finite_subset  by auto
      moreover have "n1 \<in> nodes G1"
        proof -
          have "n1\<in>nodes (del_unEdge n1 w n2 G)" using \<open>n1\<in>nodes G\<close> by auto
          hence "valid_graph.is_path (del_unEdge n1 w n2 G) n1 [] n1"
            using valid0' by (metis valid_graph.is_path_simps(1))
          thus ?thesis using G1_nodes by auto
        qed
      hence "nodes G1 \<noteq> {}" by auto
      moreover have "num_of_odd_nodes G1 = 0"
        proof -
          have "valid_graph G2" using \<open>valid_unMultigraph G2\<close> valid_unMultigraph_def by auto
          hence "\<forall>n\<in>nodes G1. degree n G1 = degree n (del_unEdge n1 w n2 G)"
          using sub_graph_degree_frame[of G2 G1 "(del_unEdge n1 w n2 G)"]
            by (metis G1_G2_edges_union \<open>nodes G1 \<inter> nodes G2 = {}\<close>)
          hence "\<forall>n\<in>nodes G1. even(degree n G1)" using all_even
            by (metis G1_G2_nodes_union Un_iff)
          thus ?thesis
            unfolding num_of_odd_nodes_def odd_nodes_set_def
            by (metis (lifting) Collect_empty_eq card_eq_0_iff)
        qed
      ultimately have "\<forall>v\<in>nodes G1. \<exists>ps. valid_unMultigraph.is_Eulerian_circuit G1 v ps v"
        using less.hyps[of G1] \<open>valid_unMultigraph G1\<close> \<open>valid_unMultigraph.connected G1\<close>
        by auto
      then obtain ps1 where ps1:"valid_unMultigraph.is_Eulerian_trail G1 n1 ps1 n1"
        using \<open>n1\<in>nodes G1\<close>
        by (metis (full_types) \<open>valid_unMultigraph G1\<close> valid_unMultigraph.is_Eulerian_circuit_def)
      have "card (edges G2) < card (edges G)"
        using G1_G2_edges_union \<open>edges (del_unEdge n1 w n2 G) \<subset> edges G\<close>
        by (metis (full_types) \<open>finite (edges G)\<close> inf_sup_ord(4) le_less_trans psubset_card_mono)
      moreover have "finite (edges G2)"
        using G1_G2_edges_union \<open>finite (edges G)\<close>
        by (metis \<open>edges (del_unEdge n1 w n2 G) \<subset> edges G\<close> finite_Un less_imp_le rev_finite_subset)
      moreover have "nodes G2 \<subseteq> nodes (del_unEdge n1 w n2 G)"
        by (metis G1_G2_nodes_union Un_upper2)
      hence "finite (nodes G2)"
        using  \<open>finite (nodes G)\<close>  del_UnEdge_node rev_finite_subset by auto
      moreover have "n2 \<in> nodes G2"
        proof -
          have "n2\<in>nodes (del_unEdge n1 w n2 G)"
            using \<open>n2\<in>nodes G\<close> by auto
          hence "valid_graph.is_path (del_unEdge n1 w n2 G) n2 [] n2"
            using valid0' by (metis valid_graph.is_path_simps(1))
          thus ?thesis using G2_nodes by auto
        qed
      hence "nodes G2 \<noteq> {}" by auto
      moreover have "num_of_odd_nodes G2 = 0"
        proof -
          have "valid_graph G1" using \<open>valid_unMultigraph G1\<close> valid_unMultigraph_def by auto
          hence "\<forall>n\<in>nodes G2. degree n G2 = degree n (del_unEdge n1 w n2 G)"
            using sub_graph_degree_frame[of G1 G2 "(del_unEdge n1 w n2 G)"]
            by (metis G1_G2_edges_union \<open>nodes G1 \<inter> nodes G2 = {}\<close> inf_commute sup_commute)
          hence "\<forall>n\<in>nodes G2. even(degree n G2)" using all_even
            by (metis G1_G2_nodes_union Un_iff)
          thus ?thesis
            unfolding num_of_odd_nodes_def odd_nodes_set_def
            by (metis (lifting) Collect_empty_eq card_eq_0_iff)
        qed
      ultimately have "\<forall>v\<in>nodes G2. \<exists>ps. valid_unMultigraph.is_Eulerian_circuit G2 v ps v"
        using less.hyps[of G2] \<open>valid_unMultigraph G2\<close> \<open>valid_unMultigraph.connected G2\<close>
        by auto
      then obtain ps2 where ps2:"valid_unMultigraph.is_Eulerian_trail G2 n2 ps2 n2"
        using \<open>n2\<in>nodes G2\<close>
        by (metis (full_types) \<open>valid_unMultigraph G2\<close> valid_unMultigraph.is_Eulerian_circuit_def)
      have "\<lparr>nodes = nodes G1 \<union> nodes G2, edges = edges G1 \<union> edges G2 \<union> {(n1, w, n2),
          (n2, w, n1)}\<rparr>=G"
        proof -
          have "edges (del_unEdge n1 w n2 G) \<union> {(n1, w, n2),(n2, w, n1)} =edges G"
            using \<open>(n1,w,n2)\<in>edges G\<close> \<open>(n2,w,n1)\<in>edges G\<close>
            unfolding del_unEdge_def by auto
          moreover have   "nodes (del_unEdge n1 w n2 G)=nodes G"
            unfolding del_unEdge_def by auto
          ultimately have "\<lparr>nodes = nodes (del_unEdge n1 w n2 G), edges =
              edges (del_unEdge n1 w n2 G) \<union> {(n1, w, n2), (n2, w, n1)}\<rparr>=G"
            by auto
          moreover have "\<lparr>nodes = nodes G1 \<union> nodes G2, edges = edges G1 \<union> edges G2 \<union>
              {(n1, w, n2),(n2, w, n1)}\<rparr>=\<lparr>nodes = nodes (del_unEdge n1 w n2 G),edges
              = edges (del_unEdge n1 w n2 G) \<union> {(n1, w, n2), (n2, w, n1)}\<rparr>"
            by (metis G1_G2_edges_union G1_G2_nodes_union)
          ultimately show ?thesis by auto
        qed
      moreover have "valid_unMultigraph.is_Eulerian_trail \<lparr>nodes = nodes G1 \<union> nodes G2,
          edges = edges G1 \<union> edges G2 \<union> {(n1, w, n2), (n2, w, n1)}\<rparr> n1 (ps1 @ (n1, w, n2) # ps2) n2"
        using eulerian_split[of G1 G2 n1 ps1 n1 n2 ps2 n2 w]
        by (metis \<open>edges G1 \<inter> edges G2 = {}\<close> \<open>nodes G1 \<inter> nodes G2 = {}\<close> \<open>valid_unMultigraph G1\<close>
          \<open>valid_unMultigraph G2\<close> ps1 ps2)
      ultimately show ?thesis by (metis \<open>n1 \<noteq> n2\<close> n1(1) n1(2) n2(1) n2(2))
    qed
  moreover have "v'\<noteq>n2 \<Longrightarrow> (\<exists>v\<in>nodes G. \<exists>v'\<in>nodes G.\<exists>ps. odd (degree v G) \<and> odd (degree v' G)
      \<and> v \<noteq> v' \<and> valid_unMultigraph.is_Eulerian_trail G v ps v')"
    proof (cases "valid_unMultigraph.connected (del_unEdge n1 w v' G)")
      case True
      assume "v' \<noteq> n2"
      assume connected':"valid_unMultigraph.connected (del_unEdge n1 w v' G)"
      have "n1 \<in> nodes (del_unEdge n1 w v' G)" by (metis del_UnEdge_node n1(1))
      hence even_n1:"even(degree n1 (del_unEdge n1 w v' G))"
        using valid_unMultigraph.del_UnEdge_even[OF \<open>valid_unMultigraph G\<close> \<open>(n1, w, v') \<in> edges G\<close>
          \<open>finite (edges G)\<close>] \<open>odd (degree n1 G)\<close>
        unfolding odd_nodes_set_def by auto
      moreover have odd_n2:"odd(degree n2 (del_unEdge n1 w v' G))"
        using valid_unMultigraph.degree_frame[OF \<open>valid_unMultigraph G\<close> \<open>finite (edges G)\<close>,
          of n2 n1 v' w] \<open>n1 \<noteq> n2\<close> \<open>v' \<noteq> n2\<close>
        by (metis empty_iff insert_iff n2(2))
      moreover have "even (degree v' G)"
        using even_except_two[of v']
        by (metis (full_types) \<open>(n1, w, v') \<in> edges G\<close> \<open>v' \<noteq> n2\<close> \<open>valid_graph G\<close>
          \<open>valid_unMultigraph G\<close> valid_graph.E_validD(2) valid_unMultigraph.no_id)
      hence odd_v':"odd(degree v' (del_unEdge n1 w v' G))"
        using valid_unMultigraph.del_UnEdge_even'[OF \<open>valid_unMultigraph G\<close> \<open>(n1, w, v') \<in> edges G\<close>
          \<open>finite (edges G)\<close>]
        unfolding odd_nodes_set_def by auto
      ultimately have two_odds:"num_of_odd_nodes (del_unEdge n1 w v' G) = 2"
        by (metis (lifting) \<open>v' \<noteq> n2\<close> \<open>valid_graph G\<close> \<open>valid_unMultigraph G\<close>
          \<open>(n1, w, v') \<in> edges G\<close> \<open>finite (edges G)\<close> \<open>finite (nodes G)\<close> \<open>num_of_odd_nodes G = 2\<close>
          del_UnEdge_odd_even even_except_two n1(2) valid_graph.E_validD(2))
      moreover have valid0:"valid_unMultigraph (del_unEdge n1 w v' G)"
        using del_unEdge_valid \<open>valid_unMultigraph G\<close> by auto
      moreover have " edges G - {(n1, w, v'), (v', w, n1)} \<subset> edges G"
        using \<open>(n1,w,v')\<in>edges G\<close> by auto
      hence "card (edges (del_unEdge n1 w v' G)) < card (edges G)"
        using \<open>finite (edges G)\<close> unfolding del_unEdge_def
        by (metis (hide_lams, no_types) psubset_card_mono select_convs(2))
      moreover have "finite (edges (del_unEdge n1 w v' G))"
        unfolding del_unEdge_def
        by (metis (full_types) \<open>finite (edges G)\<close> finite_Diff select_convs(2))
      moreover have "finite (nodes (del_unEdge n1 w v' G))"
        unfolding del_unEdge_def by (metis \<open>finite (nodes G)\<close> select_convs(1))
      moreover have "nodes (del_unEdge n1 w v' G) \<noteq> {}"
        by (metis (full_types) del_UnEdge_node empty_iff n1(1))
      ultimately obtain s t ps where
          s: "s\<in>nodes (del_unEdge n1 w v' G)" "odd (degree s (del_unEdge n1 w v' G))"
          and t:"t\<in>nodes (del_unEdge n1 w v' G)" "odd (degree t (del_unEdge n1 w v' G))"
          and "s \<noteq> t"
          and s_ps_t: "valid_unMultigraph.is_Eulerian_trail (del_unEdge n1 w v' G) s ps t"
        using   connected' less.hyps[of "(del_unEdge n1 w v' G)"] by auto
      hence "(s=n2\<and>t=v')\<or>(s=v'\<and>t=n2)"
        using odd_n2 odd_v' two_odds \<open>finite (edges G)\<close>\<open>valid_unMultigraph G\<close>
        by (metis (mono_tags) del_UnEdge_node empty_iff even_except_two even_n1 insert_iff
          valid_unMultigraph.degree_frame)
      moreover have "s=n2\<Longrightarrow>t=v'\<Longrightarrow>?thesis"
        by (metis \<open>(n1, w, v') \<in> edges G\<close> \<open>n1 \<noteq> n2\<close> \<open>valid_unMultigraph G\<close> n1(1) n1(2) n2(1) n2(2)
          s_ps_t valid0 valid_unMultigraph.euclerian_rev valid_unMultigraph.eulerian_cons)
      moreover have "s=v'\<Longrightarrow>t=n2\<Longrightarrow>?thesis"
        by (metis \<open>(n1, w, v') \<in> edges G\<close> \<open>n1 \<noteq> n2\<close> \<open>valid_unMultigraph G\<close> n1(1) n1(2) n2(1) n2(2)
          s_ps_t valid_unMultigraph.eulerian_cons)
      ultimately show ?thesis by auto
    next
      case False
      assume "v'\<noteq>n2"
      assume not_conneted:"\<not>valid_unMultigraph.connected (del_unEdge n1 w v' G)"
      have "(v',w,n1)\<in>edges G" using \<open>(n1,w,v')\<in>edges G\<close>
        by (metis \<open>valid_unMultigraph G\<close>  valid_unMultigraph.corres)
      have valid0:"valid_unMultigraph (del_unEdge n1 w v' G)"
        using \<open>valid_unMultigraph G\<close> del_unEdge_valid by auto
      hence valid0':"valid_graph (del_unEdge n1 w v' G)"
        using valid_unMultigraph_def by auto
      have even_n1:"even(degree n1 (del_unEdge n1 w v' G))"
        using valid_unMultigraph.del_UnEdge_even[OF \<open>valid_unMultigraph G\<close> \<open>(n1,w,v')\<in>edges G\<close>
          \<open>finite (edges G)\<close>] n1
        unfolding odd_nodes_set_def by auto
      moreover have odd_n2:"odd(degree n2 (del_unEdge n1 w v' G))"
        using \<open>n1 \<noteq> n2\<close> \<open>v' \<noteq> n2\<close> n2 valid_unMultigraph.degree_frame[OF \<open>valid_unMultigraph G\<close>
          \<open>finite (edges G)\<close>, of n2 n1 v' w]
        by auto
      moreover have "v'\<noteq>n1"
        using valid_unMultigraph.no_id[OF \<open>valid_unMultigraph G\<close>] \<open>(n1,w,v')\<in>edges G\<close> by auto
      hence odd_v':"odd(degree v' (del_unEdge n1 w v' G))"
        using  \<open>v' \<noteq> n2\<close>   even_except_two[of v']
          valid_graph.E_validD(2)[OF \<open>valid_graph G\<close> \<open>(n1, w, v') \<in> edges G\<close>]
          valid_unMultigraph.del_UnEdge_even'[OF  \<open>valid_unMultigraph G\<close> \<open>(n1, w, v') \<in> edges G\<close>
          \<open>finite (edges G)\<close> ]
        unfolding odd_nodes_set_def by auto
      ultimately have even_except_two':"\<And>n. n\<in>nodes (del_unEdge n1 w v' G)\<Longrightarrow> n\<noteq>n2
          \<Longrightarrow> n\<noteq>v'\<Longrightarrow> even(degree n (del_unEdge n1 w v' G))"
        using del_UnEdge_node[of _ n1 w v' G] even_except_two valid_unMultigraph.degree_frame[OF
          \<open>valid_unMultigraph G\<close> \<open>finite (edges G)\<close>, of _ n1 v' w]
        by force
      obtain G1 G2 where
          G1_nodes: "nodes G1={n. \<exists>ps. valid_graph.is_path (del_unEdge n1 w v' G) n ps n1}"
          and G1_edges: "edges G1={(n,e,n'). (n,e,n')\<in>edges (del_unEdge n1 w v' G) \<and> n\<in>nodes G1
            \<and> n'\<in>nodes G1}"
          and G2_nodes:"nodes G2={n. \<exists>ps. valid_graph.is_path (del_unEdge n1 w v' G) n ps v'}"
          and G2_edges:"edges G2={(n,e,n'). (n,e,n')\<in>edges (del_unEdge n1 w v' G) \<and> n\<in>nodes G2
            \<and> n'\<in>nodes G2}"
          and G1_G2_edges_union:"edges G1 \<union> edges G2 = edges (del_unEdge n1 w v' G)"
          and "edges G1 \<inter> edges G2={}"
          and G1_G2_nodes_union:"nodes G1 \<union> nodes G2=nodes (del_unEdge n1 w v' G)"
          and "nodes G1 \<inter> nodes G2={}"
          and "valid_unMultigraph G1"
          and "valid_unMultigraph G2"
          and "valid_unMultigraph.connected G1"
          and "valid_unMultigraph.connected G2"
        using valid_unMultigraph.connectivity_split[OF \<open>valid_unMultigraph G\<close>
          \<open>valid_unMultigraph.connected G\<close> not_conneted \<open>(n1,w,v')\<in>edges G\<close>]
        .
      have "n2\<in>nodes G2" using extend_distinct_path
        proof -
          have "finite (edges (del_unEdge n1 w v' G))"
            unfolding del_unEdge_def using \<open>finite (edges G)\<close> by auto
          moreover have "num_of_odd_nodes (del_unEdge n1 w v' G) = 2"
            by (metis \<open>(n1, w, v') \<in> edges G\<close> \<open>(v', w, n1) \<in> edges G\<close> \<open>num_of_odd_nodes G = 2\<close>
              \<open>v' \<noteq> n2\<close> \<open>valid_graph G\<close> del_UnEdge_even_odd delete_edge_sym even_except_two
              \<open>finite (edges G)\<close> \<open>finite (nodes G)\<close> \<open>valid_unMultigraph G\<close>
              n1(2) valid_graph.E_validD(2) valid_unMultigraph.no_id)
          ultimately have "\<exists>ps. valid_unMultigraph.is_trail (del_unEdge n1 w v' G) n2 ps v'"
            using valid_unMultigraph.path_between_odds[OF valid0,of n2 v',OF odd_n2 odd_v'] \<open>v'\<noteq>n2\<close>
            by auto
          hence "\<exists>ps. valid_graph.is_path (del_unEdge n1 w v' G) n2 ps v'"
            by (metis valid0 valid_unMultigraph.is_trail_intro)
          thus ?thesis using G2_nodes by auto
        qed
      have "v'\<in>nodes G2"
        proof -
          have "valid_graph.is_path (del_unEdge n1 w v' G) v' [] v'"
            by (metis (full_types) \<open>(n1, w, v') \<in> edges G\<close> \<open>valid_graph G\<close> del_UnEdge_node
                valid0' valid_graph.E_validD(2) valid_graph.is_path_simps(1))
          thus ?thesis by (metis (lifting) G2_nodes mem_Collect_eq)
        qed
      have edges_subset:"edges (del_unEdge n1 w v' G) \<subset> edges G"
        using \<open>(n1,w,v')\<in>edges G\<close> \<open>(v',w,n1)\<in>edges G\<close>
        unfolding del_unEdge_def by auto
      hence "card (edges G1) < card (edges G)"
        by (metis G1_G2_edges_union inf_sup_absorb \<open>finite (edges G)\<close>  less_infI2 psubset_card_mono)
      moreover have "finite (edges G1)"
        by (metis (full_types) G1_G2_edges_union edges_subset finite_Un finite_subset
          \<open>finite (edges G)\<close>  less_imp_le)
      moreover have "finite (nodes G1)"
        using G1_G2_nodes_union  \<open>finite (nodes G)\<close>
        unfolding del_unEdge_def
        by (metis (full_types) finite_Un select_convs(1))
      moreover have "n1\<in>nodes G1"
        proof -
          have "valid_graph.is_path (del_unEdge n1 w v' G) n1 [] n1"
            by (metis (full_types) del_UnEdge_node n1(1) valid0' valid_graph.is_path_simps(1))
          thus ?thesis by (metis (lifting) G1_nodes mem_Collect_eq)
        qed
      moreover hence "nodes G1 \<noteq> {}" by auto
      moreover have "num_of_odd_nodes G1 = 0"
        proof -
          have "\<forall>n\<in>nodes G1. even(degree n (del_unEdge n1 w v' G))"
            using even_except_two' odd_v' odd_n2 \<open>n2\<in>nodes G2\<close> \<open>nodes G1 \<inter> nodes G2 = {}\<close>
              \<open>v'\<in>nodes G2\<close>
            by (metis (full_types) G1_G2_nodes_union Un_iff disjoint_iff_not_equal)
          moreover have "valid_graph G2"
            using \<open>valid_unMultigraph G2\<close> valid_unMultigraph_def
            by auto
          ultimately have "\<forall>n\<in>nodes G1. even(degree n G1)"
            using sub_graph_degree_frame[of G2 G1 "del_unEdge n1 w v' G"]
            by (metis G1_G2_edges_union \<open>nodes G1 \<inter> nodes G2 = {}\<close>)
          thus ?thesis unfolding num_of_odd_nodes_def odd_nodes_set_def
            by (metis (lifting) card_eq_0_iff empty_Collect_eq)
        qed
      ultimately obtain ps1 where ps1:"valid_unMultigraph.is_Eulerian_trail G1 n1 ps1 n1"
        using \<open>valid_unMultigraph G1\<close> \<open>valid_unMultigraph.connected G1\<close> less.hyps[of G1]
        by (metis valid_unMultigraph.is_Eulerian_circuit_def)
      have "card (edges G2) < card (edges G)"
        by (metis G1_G2_edges_union \<open>finite (edges G)\<close> edges_subset inf_sup_absorb less_infI2
          psubset_card_mono sup_commute)
      moreover have "finite (edges G2)"
        by (metis (full_types) G1_G2_edges_union edges_subset finite_Un \<open>finite (edges G)\<close> less_le
          rev_finite_subset)
      moreover have "finite (nodes G2)"
        by (metis (mono_tags) G1_G2_nodes_union del_UnEdge_node le_sup_iff \<open>finite (nodes G)\<close>
          rev_finite_subset subsetI)
      moreover have "nodes G2 \<noteq> {}" using \<open>v'\<in>nodes G2\<close> by auto
      moreover have "num_of_odd_nodes G2 = 2"
        proof -
          have "\<forall>n\<in>nodes G2. n\<notin>{n2,v'}\<longrightarrow>even(degree n (del_unEdge n1 w v' G))"
            using even_except_two'
            by (metis (full_types) G1_G2_nodes_union Un_iff insert_iff)
          moreover have "valid_graph G1"
            using \<open>valid_unMultigraph G1\<close> valid_unMultigraph_def by auto
          ultimately have "\<forall>n\<in>nodes G2. n\<notin>{n2,v'}\<longrightarrow>even(degree n G2)"
            using sub_graph_degree_frame[of G1 G2 "del_unEdge n1 w v' G"]
            by (metis G1_G2_edges_union Int_commute Un_commute \<open>nodes G1 \<inter> nodes G2 = {}\<close>)
          hence "\<forall>n\<in>nodes G2. n\<notin>{n2,v'}\<longrightarrow>n\<notin>{v \<in> nodes G2. odd (degree v G2)}"
            by (metis (lifting) mem_Collect_eq)
          moreover have "odd(degree n2 G2)"
            using sub_graph_degree_frame[of G1 G2 "del_unEdge n1 w v' G"]
            by (metis (hide_lams, no_types) G1_G2_edges_union \<open>nodes G1 \<inter> nodes G2 = {}\<close>
              \<open>valid_graph G1\<close> \<open>n2 \<in> nodes G2\<close> inf_assoc inf_bot_right inf_sup_absorb
               odd_n2 sup_bot_right sup_commute)
          hence "n2\<in>{v \<in> nodes G2. odd (degree v G2)}"
            by (metis (lifting) \<open>n2 \<in> nodes G2\<close> mem_Collect_eq)
          moreover have "odd(degree v' G2)"
            using sub_graph_degree_frame[of G1 G2 "del_unEdge n1 w v' G"]
            by (metis G1_G2_edges_union Int_commute Un_commute \<open>nodes G1 \<inter> nodes G2 = {}\<close>
              \<open>v' \<in> nodes G2\<close> \<open>valid_graph G1\<close> odd_v')
          hence "v'\<in>{v \<in> nodes G2. odd (degree v G2)}"
            by (metis (full_types) Collect_conj_eq Collect_mem_eq Int_Collect \<open>v' \<in> nodes G2\<close>)
          ultimately have "{v \<in> nodes G2. odd (degree v G2)}={n2,v'}"
            using \<open>finite (nodes G2)\<close> by (induct G2,auto)
          thus ?thesis using \<open>v'\<noteq>n2\<close>
            unfolding num_of_odd_nodes_def odd_nodes_set_def by auto
        qed
      ultimately obtain s t ps2 where
          s: "s\<in>nodes G2" "odd (degree s G2)"
          and t:"t\<in>nodes G2" "odd (degree t G2)"
          and "s \<noteq> t"
          and s_ps2_t: "valid_unMultigraph.is_Eulerian_trail G2 s ps2 t"
        using \<open>valid_unMultigraph G2\<close> \<open>valid_unMultigraph.connected G2\<close> less.hyps[of G2]
        by auto
      moreover have "valid_graph G1"
        using \<open>valid_unMultigraph G1\<close> valid_unMultigraph_def by auto
      ultimately have "(s=n2\<and>t=v')\<or>(s=v'\<and>t=n2)"
        using odd_n2 odd_v' even_except_two'
          sub_graph_degree_frame[of G1 G2 "(del_unEdge n1 w v' G)"]
        by (metis G1_G2_edges_union G1_G2_nodes_union UnI1 \<open>nodes G1 \<inter> nodes G2 = {}\<close> inf_commute
          sup.commute)
      moreover have merge_G1_G2:"\<lparr>nodes = nodes G1 \<union> nodes G2, edges = edges G1 \<union> edges G2 \<union>
          {(n1, w,v'),(v', w, n1)}\<rparr>=G"
        proof -
          have "edges (del_unEdge n1 w v' G) \<union> {(n1, w, v'),(v', w, n1)} =edges G"
            using  \<open>(n1,w,v')\<in>edges G\<close> \<open>(v',w,n1)\<in>edges G\<close>
            unfolding del_unEdge_def by auto
          moreover have "nodes (del_unEdge n1 w v' G)=nodes G"
            unfolding del_unEdge_def by auto
          ultimately have "\<lparr>nodes = nodes (del_unEdge n1 w v' G), edges =
              edges (del_unEdge n1 w v' G) \<union> {(n1, w, v'), (v', w, n1)}\<rparr>=G"
            by auto
          moreover have "\<lparr>nodes = nodes G1 \<union> nodes G2, edges = edges G1 \<union> edges G2 \<union>
              {(n1, w, v'),(v', w, n1)}\<rparr>=\<lparr>nodes = nodes (del_unEdge n1 w v' G),edges
              = edges (del_unEdge n1 w v' G) \<union> {(n1, w, v'), (v', w, n1)}\<rparr>"
            by (metis G1_G2_edges_union G1_G2_nodes_union)
          ultimately show ?thesis by auto
        qed
      moreover have "s=n2\<Longrightarrow>t=v'\<Longrightarrow>?thesis"
        using eulerian_split[of G1 G2 n1 ps1 n1 v' "(rev_path ps2)" n2 w] merge_G1_G2
        by (metis \<open>edges G1 \<inter> edges G2 = {}\<close> \<open>n1 \<noteq> n2\<close> \<open>nodes G1 \<inter> nodes G2 = {}\<close>
            \<open>valid_unMultigraph G1\<close> \<open>valid_unMultigraph G2\<close> n1(1) n1(2) n2(1) n2(2) ps1 s_ps2_t
            valid_unMultigraph.euclerian_rev)
      moreover have "s=v'\<Longrightarrow>t=n2\<Longrightarrow>?thesis"
        using eulerian_split[of G1 G2 n1 ps1 n1 v' ps2 n2 w] merge_G1_G2
        by (metis \<open>edges G1 \<inter> edges G2 = {}\<close> \<open>n1 \<noteq> n2\<close> \<open>nodes G1 \<inter> nodes G2 = {}\<close>
          \<open>valid_unMultigraph G1\<close> \<open>valid_unMultigraph G2\<close> n1(1) n1(2) n2(1) n2(2) ps1 s_ps2_t)
      ultimately show ?thesis by auto
    qed
  ultimately show "\<exists>v\<in>nodes G. \<exists>v'\<in>nodes G.\<exists>ps. odd (degree v G) \<and> odd (degree v' G) \<and> v \<noteq> v'
      \<and> valid_unMultigraph.is_Eulerian_trail G v ps v'"
    by auto
next
  case less
  assume "finite (edges G)" and "finite (nodes G)" and "valid_unMultigraph G" and "nodes G\<noteq>{}"
      and "valid_unMultigraph.connected G" and "num_of_odd_nodes G = 0"
  show "\<forall>v\<in>nodes G. \<exists>ps. valid_unMultigraph.is_Eulerian_circuit G v ps v"
    proof (rule,cases "card (nodes G)=1")
      fix v assume "v\<in>nodes G"
      assume " card (nodes G) = 1 "
      hence "nodes G={v}"
        using \<open>v \<in> nodes G\<close>  card_Suc_eq[of "nodes G" 0] empty_iff insert_iff[of _ v]
        by auto
      have "edges G={}"
        proof (rule ccontr)
          assume "edges G \<noteq> {}"
          then obtain e1 e2 e3 where e:"(e1,e2,e3)\<in>edges G" by (metis ex_in_conv prod_cases3)
          hence "e1=e3" using \<open>nodes G={v}\<close>
            by (metis (hide_lams, no_types) append_Nil2 valid_unMultigraph.is_trail_rev
                valid_unMultigraph.is_trail.simps(1) \<open>valid_unMultigraph G\<close> singletonE
                valid_unMultigraph.is_trail_split valid_unMultigraph.singleton_distinct_path)
          thus False by (metis e \<open>valid_unMultigraph G\<close> valid_unMultigraph.no_id)
        qed
      hence "valid_unMultigraph.is_Eulerian_circuit G v [] v"
        by (metis \<open>nodes G = {v}\<close> insert_subset \<open>valid_unMultigraph G\<close> rem_unPath.simps(1)
            subsetI valid_unMultigraph.is_trail.simps(1)
            valid_unMultigraph.is_Eulerian_circuit_def
            valid_unMultigraph.is_Eulerian_trail_def)
      thus "\<exists>ps. valid_unMultigraph.is_Eulerian_circuit G v ps v" by auto
    next
      fix v assume "v\<in>nodes G"
      assume "card (nodes G) \<noteq> 1"
      moreover have "card (nodes G)\<noteq>0" using \<open>nodes G\<noteq>{}\<close>
        by (metis card_eq_0_iff \<open>finite (nodes G)\<close>)
      ultimately have "card (nodes G) \<ge>2" by auto
      then obtain n where "card (nodes G) = Suc (Suc n)"
        by (metis le_iff_add add_2_eq_Suc)
      hence "\<exists>n\<in>nodes G. n\<noteq>v" by (auto dest!: card_eq_SucD)
      then obtain v' w where "(v,w,v')\<in>edges G"
        proof -
          assume pre:"\<And>w v'. (v, w, v') \<in> edges G \<Longrightarrow> thesis"
          assume "\<exists>n\<in>nodes G. n \<noteq> v"
          then obtain ps where  ps:"\<exists>v'. valid_graph.is_path G v ps v' \<and> ps\<noteq>Nil"
            using valid_unMultigraph_def
            by (metis (full_types) \<open>v \<in> nodes G\<close> \<open>valid_unMultigraph G\<close> valid_graph.is_path.simps(1)
              \<open>valid_unMultigraph.connected G\<close> valid_unMultigraph.connected_def)
          then obtain v0 w v' where "\<exists>ps'. ps=Cons (v0,w,v') ps'" by (metis neq_Nil_conv prod_cases3)
          hence "v0=v"
            using valid_unMultigraph_def
            by (metis \<open>valid_unMultigraph G\<close> ps valid_graph.is_path.simps(2))
          hence "(v,w,v')\<in>edges G"
            using valid_unMultigraph_def
            by (metis \<open>\<exists>ps'. ps = (v0, w, v') # ps'\<close> \<open>valid_unMultigraph G\<close> ps
              valid_graph.is_path.simps(2))
          thus ?thesis by (metis pre)
        qed
      have all_even:"\<forall>x\<in>nodes G. even(degree x G)"
        using \<open>finite (nodes G)\<close> \<open>num_of_odd_nodes G = 0\<close>
        unfolding num_of_odd_nodes_def odd_nodes_set_def by auto
      have odd_v: "odd (degree v (del_unEdge v w v' G))"
        using  \<open>v \<in> nodes G\<close> all_even valid_unMultigraph.del_UnEdge_even[OF \<open>valid_unMultigraph G\<close>
          \<open>(v, w, v') \<in> edges G\<close> \<open>finite (edges G)\<close>]
        unfolding odd_nodes_set_def by auto
      have odd_v':  "odd (degree v' (del_unEdge v w v' G))"
        using valid_unMultigraph.del_UnEdge_even'[OF \<open>valid_unMultigraph G\<close> \<open>(v, w, v') \<in> edges G\<close>
          \<open>finite (edges G)\<close>]
            all_even  valid_graph.E_validD(2)[OF _ \<open>(v, w, v') \<in> edges G\<close>]
            \<open>valid_unMultigraph G\<close>
        unfolding valid_unMultigraph_def odd_nodes_set_def
        by auto
      have valid_unMulti:"valid_unMultigraph (del_unEdge v w v' G)"
        by (metis del_unEdge_valid \<open>valid_unMultigraph G\<close>)
      moreover have valid_graph: "valid_graph (del_unEdge v w v' G)"
        using valid_unMultigraph_def del_undirected
        by (metis \<open>valid_unMultigraph G\<close> delete_edge_valid)
      moreover have fin_E': "finite(edges (del_unEdge v w v' G))"
        using \<open>finite(edges G)\<close> unfolding del_unEdge_def by auto
      moreover have fin_V': "finite(nodes (del_unEdge v w v' G))"
        using \<open>finite(nodes G)\<close> unfolding del_unEdge_def by auto
      moreover have less_card:"card(edges (del_unEdge v w v' G))<card(edges G)"
        unfolding del_unEdge_def using \<open>(v,w,v')\<in>edges G\<close>
        by (metis Diff_insert2 card_Diff2_less \<open>finite (edges G)\<close> \<open>valid_unMultigraph G\<close>
          select_convs(2) valid_unMultigraph.corres)
      moreover have "num_of_odd_nodes (del_unEdge v w v' G) = 2"
        using \<open>valid_unMultigraph G\<close> \<open>num_of_odd_nodes G = 0\<close> \<open>v \<in> nodes G\<close> all_even
          del_UnEdge_even_even[OF \<open>valid_unMultigraph G\<close>  \<open>finite (edges G)\<close> \<open>finite (nodes G)\<close>
          \<open>(v, w, v') \<in> edges G\<close>] valid_graph.E_validD(2)[OF _ \<open>(v, w, v') \<in> edges G\<close>]
        unfolding  valid_unMultigraph_def
        by auto
      moreover have "valid_unMultigraph.connected (del_unEdge v w v' G)"
        using \<open>finite (edges G)\<close> \<open>finite (nodes G)\<close> \<open>valid_unMultigraph G\<close>
          \<open>valid_unMultigraph.connected G\<close>
        by (metis \<open>(v, w, v') \<in> edges G\<close> all_even valid_unMultigraph.del_unEdge_even_connectivity)
      moreover have "nodes(del_unEdge v w v' G)\<noteq>{}"
        by (metis \<open>v \<in> nodes G\<close> del_UnEdge_node emptyE)
      ultimately obtain n1 n2 ps where
          n1_n2:
          "n1\<in>nodes (del_unEdge v w v' G)"
          "n2\<in>nodes (del_unEdge v w v' G)"
          "odd (degree n1 (del_unEdge v w v' G))"
          "odd (degree n2 (del_unEdge v w v' G))"
          "n1\<noteq>n2"
          and
          ps_eulerian:
          "valid_unMultigraph.is_Eulerian_trail (del_unEdge v w v' G) n1 ps n2"
        by (metis \<open>num_of_odd_nodes (del_unEdge v w v' G) = 2\<close> less.hyps(1))
      have "n1=v\<Longrightarrow>n2=v'\<Longrightarrow>valid_unMultigraph.is_Eulerian_circuit G v (ps@[(v',w,v)]) v"
        using ps_eulerian
        by (metis \<open>(v, w, v') \<in> edges G\<close> delete_edge_sym \<open>valid_unMultigraph G\<close>
          valid_unMultigraph.corres valid_unMultigraph.eulerian_cons'
          valid_unMultigraph.is_Eulerian_circuit_def)
      moreover have "n1=v'\<Longrightarrow>n2=v\<Longrightarrow>\<exists>ps. valid_unMultigraph.is_Eulerian_circuit G v ps v"
        by (metis \<open>(v, w, v') \<in> edges G\<close> \<open>valid_unMultigraph G\<close> ps_eulerian
          valid_unMultigraph.eulerian_cons valid_unMultigraph.is_Eulerian_circuit_def)
      moreover have "(n1=v\<and>n2=v')\<or>(n2=v\<and>n1=v')"
        by (metis (mono_tags) all_even del_UnEdge_node insert_iff \<open>finite (edges G)\<close>
          \<open>valid_unMultigraph G\<close> n1_n2(1) n1_n2(2) n1_n2(3) n1_n2(4) n1_n2(5) singletonE
          valid_unMultigraph.degree_frame)
      ultimately show "\<exists>ps. valid_unMultigraph.is_Eulerian_circuit G v ps v" by auto
    qed
qed
end
