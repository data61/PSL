(*
Title: MoreGraph.thy
Author:Wenda Li
*)

theory MoreGraph imports Complex_Main Dijkstra_Shortest_Path.Graph
begin
section \<open>Undirected Multigraph and undirected trails\<close>

locale valid_unMultigraph=valid_graph G for G::"('v,'w) graph"+
              assumes corres[simp]: "(v,w,u') \<in> edges G \<longleftrightarrow> (u',w,v) \<in> edges G"
                and   no_id[simp]:"(v,w,v) \<notin> edges G"

fun (in valid_unMultigraph) is_trail :: "'v \<Rightarrow> ('v,'w) path \<Rightarrow> 'v \<Rightarrow> bool" where
      "is_trail v [] v' \<longleftrightarrow> v=v' \<and> v'\<in> V" |
      "is_trail v ((v1,w,v2)#ps) v' \<longleftrightarrow> v=v1 \<and> (v1,w,v2)\<in>E \<and> 
                (v1,w,v2)\<notin>set ps \<and>(v2,w,v1)\<notin>set ps \<and> is_trail v2 ps v'"

(*This section mainly includes lemmas related to degrees of nodes, especially when edges and paths 
are removed from an undirected graph*)
section \<open>Degrees and related properties\<close>

definition degree :: "'v \<Rightarrow> ('v,'w) graph \<Rightarrow> nat" where
    "degree v g\<equiv> card({e. e\<in>edges g \<and> fst e=v})"

definition odd_nodes_set :: "('v,'w) graph \<Rightarrow> 'v set" where
    "odd_nodes_set g \<equiv> {v. v\<in>nodes g \<and> odd(degree v g)}"

  (*return the number of nodes with an odd degree in the current valid multigraph*)
definition num_of_odd_nodes :: "('v, 'w) graph \<Rightarrow> nat" where
    "num_of_odd_nodes g\<equiv> card( odd_nodes_set g)"

definition num_of_even_nodes :: "('v, 'w) graph \<Rightarrow> nat" where
    "num_of_even_nodes g\<equiv> card( {v. v\<in>nodes g \<and> even(degree v g)})"

definition del_unEdge where "del_unEdge v e v' g \<equiv> \<lparr>
    nodes = nodes g, edges = edges g - {(v,e,v'),(v',e,v)} \<rparr>"

definition rev_path :: "('v,'w) path \<Rightarrow> ('v,'w) path" where
    "rev_path ps \<equiv> map (\<lambda>(a,b,c).(c,b,a)) (rev ps)"

fun rem_unPath:: "('v,'w) path \<Rightarrow> ('v,'w) graph \<Rightarrow> ('v,'w) graph" where
    "rem_unPath [] g= g"|
    "rem_unPath ((v,w,v')#ps) g= 
        rem_unPath ps (del_unEdge v w v' g)" 
    
lemma del_undirected: "del_unEdge v e v' g = delete_edge v' e v (delete_edge v e v' g)"
  unfolding del_unEdge_def delete_edge_def by auto

lemma delete_edge_sym: "del_unEdge v e v' g = del_unEdge v' e v g" 
  unfolding del_unEdge_def by auto

lemma del_unEdge_valid[simp]: assumes "valid_unMultigraph g" 
    shows "valid_unMultigraph (del_unEdge v e v' g)"
proof -
  interpret valid_unMultigraph g by fact
  show ?thesis 
    unfolding del_unEdge_def
    by unfold_locales (auto dest: E_validD) 
qed

 
lemma set_compre_diff:"{x \<in> A - B. P x}={x \<in> A. P x} - {x \<in> B . P x}" by blast
lemma set_compre_subset: "B \<subseteq> A \<Longrightarrow> {x \<in> B. P x} \<subseteq> {x \<in> A. P x}" by blast 

lemma del_edge_undirected_degree_plus: "finite (edges g) \<Longrightarrow> (v,e,v') \<in> edges g 
    \<Longrightarrow> (v',e,v) \<in> edges g  \<Longrightarrow> degree v (del_unEdge v e v' g) + 1=degree v g" 
proof -
  assume assms: "finite (edges g)" "(v,e,v') \<in> edges g" "(v',e,v) \<in> edges g "
  have "degree v (del_unEdge v e v' g) + 1
          = card ({ea \<in>  edges g - {(v, e, v'), (v', e, v)}. fst ea = v}) + 1"  
    unfolding del_unEdge_def degree_def by simp
  also have "...=card ({ea \<in>  edges g. fst ea = v} - {ea \<in> {(v, e, v'), (v', e, v)}. 
      fst ea = v})+1" 
    by (metis set_compre_diff) 
  also have "...=card ({ea \<in>  edges g. fst ea = v}) - card({ea \<in> {(v, e, v'), (v', e, v)}. 
      fst ea = v})+1" 
    proof -
      have "{(v, e, v'), (v', e, v)} \<subseteq> edges g" using \<open>(v,e,v') \<in> edges g\<close> \<open>(v',e,v) \<in> edges g\<close> 
        by auto
      hence "{ea \<in> {(v, e, v'), (v', e, v)}. fst ea = v} \<subseteq> {ea \<in>  edges g. fst ea = v}" by auto
      moreover have "finite {ea \<in> {(v, e, v'), (v', e, v)}. fst ea = v}" by auto
      ultimately have "card ({ea \<in> edges g. fst ea = v} - {ea \<in> {(v, e, v'), (v', e, v)}. 
          fst ea = v})=card {ea \<in> edges g. fst ea = v} - card {ea \<in> {(v, e, v'), (v', e, v)}.
          fst ea = v}"
        using card_Diff_subset by blast
      thus ?thesis by auto 
    qed
  also have "...=card ({ea \<in>  edges g. fst ea = v})" 
    proof -
      have "{ea \<in> {(v, e, v'), (v', e, v)}. fst ea = v}={(v,e,v')}" by auto
      hence "card {ea \<in> {(v, e, v'), (v', e, v)}. fst ea = v} = 1" by auto
      moreover have "card {ea \<in> edges g. fst ea = v}\<noteq>0" 
        by (metis (lifting, mono_tags) Collect_empty_eq assms(1) assms(2) 
          card_eq_0_iff fst_conv mem_Collect_eq rev_finite_subset subsetI)
      ultimately show ?thesis by arith
    qed
  finally have "degree v (del_unEdge v e v' g) + 1=card ({ea \<in>  edges g. fst ea = v})" .
  thus ?thesis unfolding degree_def .
qed

lemma del_edge_undirected_degree_plus': "finite (edges g) \<Longrightarrow> (v,e,v') \<in> edges g 
    \<Longrightarrow> (v',e,v) \<in> edges g \<Longrightarrow> degree v' (del_unEdge v e v' g) + 1=degree v' g"
  by (metis del_edge_undirected_degree_plus delete_edge_sym) 

lemma del_edge_undirected_degree_minus[simp]: "finite (edges g) \<Longrightarrow> (v,e,v') \<in> edges g 
    \<Longrightarrow> (v',e,v) \<in> edges g \<Longrightarrow> degree v (del_unEdge v e v' g) =degree v g- (1::nat)" 
  using del_edge_undirected_degree_plus by (metis add_diff_cancel_left' add.commute)

lemma del_edge_undirected_degree_minus'[simp]: "finite (edges g) \<Longrightarrow> (v,e,v') \<in> edges g 
    \<Longrightarrow> (v',e,v) \<in> edges g \<Longrightarrow> degree v' (del_unEdge v e v' g) =degree v' g- (1::nat)"
  by (metis del_edge_undirected_degree_minus delete_edge_sym) 


lemma del_unEdge_com: "del_unEdge v w v' (del_unEdge n e n' g)
          = del_unEdge n e n' (del_unEdge v w v' g)" 
  unfolding del_unEdge_def by auto

lemma rem_unPath_com: "rem_unPath ps (del_unEdge v w v' g) 
            = del_unEdge v w v' (rem_unPath ps g)" 
proof (induct ps arbitrary: g)
  case Nil
  thus ?case by (metis rem_unPath.simps(1))
next
  case (Cons a ps')
  thus ?case using del_unEdge_com 
    by (metis prod_cases3 rem_unPath.simps(1) rem_unPath.simps(2))
qed

lemma rem_unPath_valid[intro]: 
  "valid_unMultigraph g \<Longrightarrow> valid_unMultigraph (rem_unPath ps g)"
proof (induct ps )
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  thus ?case 
    proof -
    have "valid_unMultigraph (rem_unPath (x # xs) g) = valid_unMultigraph 
         (del_unEdge (fst x) (fst (snd x)) (snd (snd x)) (rem_unPath xs g))"
      using rem_unPath_com by (metis prod.collapse rem_unPath.simps(2))
    also have "...=valid_unMultigraph (rem_unPath xs g)" 
      by (metis Cons.hyps Cons.prems del_unEdge_valid)
    also have "...=True" 
      using Cons by auto
    finally have "?case=True" .
    thus ?case by simp
    qed
qed 


lemma (in valid_unMultigraph) degree_frame:
    assumes "finite (edges G)"  "x \<notin> {v, v'}" 
    shows "degree x (del_unEdge v w v' G) = degree x G" (is "?L=?R")
proof (cases "(v,w,v') \<in> edges G")
  case True
  have "?L=card({e. e\<in>edges G - {(v,w,v'),(v',w,v)} \<and> fst e=x})" 
    by (simp add:del_unEdge_def degree_def)
  also have "...=card({e. e\<in>edges G \<and> fst e=x}-{e. e\<in>{(v,w,v'),(v',w,v)} \<and> fst e=x})"
    by (metis  set_compre_diff)
  also have "...=card({e. e\<in>edges G \<and> fst e=x})" using \<open>x \<notin> {v, v'}\<close> 
    proof -
      have "x\<noteq>v \<and> x\<noteq> v'" using \<open>x\<notin>{v,v'}\<close>by simp
      hence "{e. e\<in>{(v,w,v'),(v',w,v)} \<and> fst e=x}={}" by auto
      thus ?thesis by (metis Diff_empty)
    qed
  also have "...=?R" by (simp add:degree_def)
  finally show ?thesis .
next
  case False
  moreover hence "(v',w,v)\<notin>E" using corres by auto
  ultimately have "E- {(v,w,v'),(v',w,v)}=E" by blast   
  hence "del_unEdge v w v' G=G" by (auto simp add:del_unEdge_def)
  thus ?thesis by auto
qed

lemma [simp]: "rev_path [] = []" unfolding rev_path_def by simp
lemma rev_path_append[simp]: "rev_path (xs@ys) = (rev_path ys) @ (rev_path xs)" 
  unfolding rev_path_def rev_append by auto
lemma rev_path_double[simp]: "rev_path(rev_path xs)=xs" 
  unfolding rev_path_def by (induct xs,auto)

lemma del_UnEdge_node[simp]: "v\<in>nodes (del_unEdge u e u' G) \<longleftrightarrow> v\<in>nodes G  " 
    by (metis del_unEdge_def select_convs(1))

lemma [intro!]: "finite (edges G) \<Longrightarrow> finite (edges (del_unEdge u e u' G))"
    by (metis del_unEdge_def finite_Diff select_convs(2))

lemma [intro!]: "finite (nodes G) \<Longrightarrow> finite (nodes (del_unEdge u e u' G))"
    by (metis del_unEdge_def select_convs(1))
 
lemma [intro!]: "finite (edges G) \<Longrightarrow> finite (edges (rem_unPath ps G))"
proof (induct ps arbitrary:G)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  hence "finite (edges (rem_unPath (x # xs) G)) = finite (edges (del_unEdge 
          (fst x) (fst (snd x)) (snd (snd x)) (rem_unPath xs G)))" 
    by (metis rem_unPath.simps(2) rem_unPath_com surjective_pairing)
  also have "...=finite (edges (rem_unPath xs G))" 
    using del_unEdge_def  
    by (metis  finite.emptyI finite_Diff2 finite_Diff_insert select_convs(2))
  also have "...=True" using Cons by auto
  finally have "?case = True" .
  thus ?case by simp
qed

lemma del_UnEdge_frame[intro]: 
  "x\<in>edges g \<Longrightarrow> x\<noteq>(v,e,v') \<Longrightarrow>x\<noteq>(v',e,v) \<Longrightarrow> x\<in>edges (del_unEdge v e v' g)"
  unfolding del_unEdge_def by auto

lemma [intro!]: "finite (nodes G) \<Longrightarrow> finite (odd_nodes_set G)"
    by (metis (lifting) mem_Collect_eq odd_nodes_set_def rev_finite_subset subsetI)

lemma [simp]: "nodes (del_unEdge u e u' G)=nodes G" 
    by (metis del_unEdge_def select_convs(1))

lemma [simp]: "nodes (rem_unPath ps G) = nodes G" 
proof (induct ps)
  case Nil
  show ?case by simp
next 
  case (Cons x xs)
  have "nodes (rem_unPath (x # xs) G)=nodes (del_unEdge 
        (fst x) (fst (snd x)) (snd (snd x)) (rem_unPath xs G))" 
    by (metis rem_unPath.simps(2) rem_unPath_com surjective_pairing)
  also have "...=nodes (rem_unPath xs G)" by auto
  also have "...=nodes G" using Cons by auto
  finally show ?case .
qed

lemma [intro!]: "finite (nodes G) \<Longrightarrow> finite (nodes (rem_unPath ps G))" by auto

lemma in_set_rev_path[simp]: "(v',w,v )\<in>set (rev_path ps) \<longleftrightarrow> (v,w,v')\<in>set ps " 
proof (induct ps)
  case Nil
  thus ?case unfolding rev_path_def by auto
next
  case (Cons x xs)
  obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
  have "set (rev_path (x # xs))=set ((rev_path xs)@[(x3,x2,x1)])" 
    unfolding rev_path_def 
    using x by auto
  also have "...=set (rev_path xs) \<union> {(x3,x2,x1)}" by auto
  finally have "set (rev_path (x # xs)) =set (rev_path xs) \<union> {(x3,x2,x1)}" .
  moreover have "set (x#xs)= set xs \<union> {(x1,x2,x3)}" 
    by (metis List.set_simps(2) insert_is_Un sup_commute x)
  ultimately show ?case using Cons by auto
qed

lemma rem_unPath_edges: 
    "edges(rem_unPath ps G) = edges G - (set ps \<union> set (rev_path ps))" 
proof (induct ps)
  case Nil
  show ?case unfolding rev_path_def by auto
next
  case (Cons x xs)
  obtain x1 x2 x3 where x: "x=(x1,x2,x3)" by (metis prod_cases3)
  hence "edges(rem_unPath (x#xs) G)= edges(del_unEdge x1 x2 x3 (rem_unPath xs G))"
    by (metis rem_unPath.simps(2) rem_unPath_com)
  also have "...=edges(rem_unPath xs G)-{(x1,x2,x3),(x3,x2,x1)}"
    by (metis del_unEdge_def select_convs(2))
  also have "...= edges G - (set xs \<union> set (rev_path xs))-{(x1,x2,x3),(x3,x2,x1)}"
    by (metis Cons.hyps)
  also have "...=edges G - (set (x#xs) \<union> set (rev_path (x#xs)))"  
    proof -
      have "set (rev_path xs) \<union> {(x3,x2,x1)}=set ((rev_path xs)@[(x3,x2,x1)])" 
        by (metis List.set_simps(2) empty_set set_append)
      also have "...=set (rev_path (x#xs))" unfolding rev_path_def using  x by auto
      finally have "set (rev_path xs) \<union> {(x3,x2,x1)}=set (rev_path (x#xs))" .
      moreover have "set xs \<union> {(x1,x2,x3)}=set (x#xs)" 
        by (metis List.set_simps(2) insert_is_Un sup_commute x)
      moreover have "edges G - (set xs \<union> set (rev_path xs))-{(x1,x2,x3),(x3,x2,x1)} =
                      edges G - ((set xs \<union> {(x1,x2,x3)}) \<union> (set (rev_path xs) \<union> {(x3,x2,x1)}))" 
        by auto 
      ultimately show ?thesis by auto
    qed
  finally show ?case .
qed  

lemma rem_unPath_graph [simp]: 
    "rem_unPath (rev_path ps) G=rem_unPath ps G"
proof -
  have "nodes(rem_unPath (rev_path ps) G)=nodes(rem_unPath ps G)" 
    by auto
  moreover have "edges(rem_unPath (rev_path ps) G)=edges(rem_unPath ps G)"  
    proof -
      have "set (rev_path ps) \<union> set (rev_path (rev_path ps)) = set ps \<union>  set (rev_path ps) " 
        by auto
      thus ?thesis by (metis rem_unPath_edges)
    qed
  ultimately show ?thesis by auto
qed 

lemma distinct_rev_path[simp]: "distinct (rev_path ps) \<longleftrightarrow>distinct ps" 
proof (induct ps)
  case Nil
  show ?case by auto
next 
  case (Cons x xs)
  obtain x1 x2 x3 where x: "x=(x1,x2,x3)" by (metis prod_cases3)
  hence "distinct (rev_path (x # xs))=distinct ((rev_path xs)@[(x3,x2,x1)])" 
    unfolding rev_path_def by auto
  also have "...= (distinct (rev_path xs) \<and> (x3,x2,x1)\<notin>set (rev_path xs))" 
    by (metis distinct.simps(2) distinct1_rotate rotate1.simps(2))
  also have "...=distinct (x#xs)" 
    by (metis Cons.hyps distinct.simps(2) in_set_rev_path x)
  finally have "distinct (rev_path (x # xs))=distinct (x#xs)" .
  thus ?case .
qed


lemma (in valid_unMultigraph) is_path_rev: "is_path v' (rev_path ps) v \<longleftrightarrow> is_path v ps v'" 
proof (induct ps arbitrary: v)
  case Nil
  show ?case by auto
next
  case (Cons x xs)
  obtain x1 x2 x3 where x: "x=(x1,x2,x3)" by (metis prod_cases3)
  hence "is_path v' (rev_path (x # xs)) v=is_path v' ((rev_path xs) @[(x3,x2,x1)]) v" 
    unfolding rev_path_def by auto
  also have "...=(is_path v' (rev_path xs) x3 \<and> (x3,x2,x1)\<in>E \<and> is_path x1 [] v)" by auto
  also have "...=(is_path x3 xs v' \<and> (x3,x2,x1)\<in>E \<and> is_path x1 [] v)" using Cons.hyps by auto
  also have "...=is_path v (x#xs) v'" 
    by (metis corres is_path.simps(1) is_path.simps(2) is_path_memb x)
  finally have "is_path v' (rev_path (x # xs)) v=is_path v (x#xs) v'" .
  thus ?case .
qed


lemma (in valid_unMultigraph) singleton_distinct_path [intro]:
   "(v,w,v')\<in>E \<Longrightarrow> is_trail v [(v,w,v')] v'" 
   by (metis E_validD(2) all_not_in_conv is_trail.simps set_empty) 
  
lemma (in valid_unMultigraph) is_trail_path: 
  "is_trail v ps v' \<longleftrightarrow> is_path v ps v' \<and> distinct ps \<and> (set ps \<inter> set (rev_path ps) = {})"
proof (induct ps arbitrary:v)
  case Nil
  show ?case by auto
next
  case (Cons x xs)
  obtain x1 x2 x3 where x: "x=(x1,x2,x3)" by (metis prod_cases3)
  hence "is_trail v (x#xs) v'= (v=x1 \<and> (x1,x2,x3)\<in>E \<and> 
                (x1,x2,x3)\<notin>set xs \<and>(x3,x2,x1)\<notin>set xs \<and> is_trail x3 xs v')" 
    by (metis is_trail.simps(2))
  also have "...=(v=x1 \<and> (x1,x2,x3)\<in>E \<and>  (x1,x2,x3)\<notin>set xs \<and>(x3,x2,x1)\<notin>set xs \<and> is_path x3 xs v' 
                  \<and> distinct xs \<and> (set xs \<inter> set (rev_path xs)={}))" 
    using Cons.hyps by auto
  also have "...=(is_path v (x#xs) v' \<and> (x1,x2,x3) \<noteq> (x3,x2,x1) \<and> (x1,x2,x3)\<notin>set xs 
                  \<and>(x3,x2,x1)\<notin>set xs \<and> distinct xs \<and> (set xs \<inter> set (rev_path xs)={}))"
    by (metis append_Nil is_path.simps(1) is_path_simps(2) is_path_split' no_id x)
  also have "...=(is_path v (x#xs) v' \<and> (x1,x2,x3) \<noteq> (x3,x2,x1) \<and>(x3,x2,x1)\<notin>set xs 
                  \<and> distinct (x#xs) \<and> (set xs \<inter> set (rev_path xs)={}))"
    by (metis (full_types) distinct.simps(2) x)
  also have "...=(is_path v (x#xs) v' \<and> (x1,x2,x3) \<noteq> (x3,x2,x1) \<and> distinct (x#xs) 
                  \<and> (x3,x2,x1)\<notin>set xs \<and> set xs \<inter> set (rev_path (x#xs))={})" 
    proof -
      have "set (rev_path (x#xs)) = set ((rev_path xs)@[(x3,x2,x1)])" using x by auto
      also have "... = set (rev_path xs) \<union> {(x3,x2,x1)}" by auto
      finally have "set (rev_path (x#xs))=set (rev_path xs) \<union> {(x3,x2,x1)}" .
      thus ?thesis by blast
    qed
  also have "...=(is_path v (x#xs) v'\<and> distinct (x#xs) \<and> (set (x#xs) \<inter> set (rev_path (x#xs))={}))"
    proof -
      have "(x3,x2,x1)\<notin>set xs \<longleftrightarrow> (x1,x2,x3)\<notin> set (rev_path xs)" using in_set_rev_path by auto
      moreover have  "set (rev_path (x#xs))=set (rev_path xs) \<union> {(x3,x2,x1)}" 
        unfolding rev_path_def using x by auto
      ultimately have " (x1,x2,x3) \<noteq> (x3,x2,x1)\<and> (x3,x2,x1)\<notin>set xs 
                        \<longleftrightarrow> (x1,x2,x3)\<notin> set (rev_path (x#xs))"  by blast 
      thus ?thesis 
        by (metis (mono_tags) Int_iff Int_insert_left_if0 List.set_simps(2) empty_iff insertI1 x)
    qed
  finally have "is_trail v (x#xs) v'\<longleftrightarrow>(is_path v (x#xs) v'\<and> distinct (x#xs) 
                  \<and> (set (x#xs) \<inter> set (rev_path (x#xs))={}))" .
  thus ?case .
qed      
 
lemma  (in valid_unMultigraph) is_trail_rev: 
    "is_trail v' (rev_path ps) v \<longleftrightarrow> is_trail v ps v' " 
    using rev_path_append is_trail_path  is_path_rev distinct_rev_path
    by (metis Int_commute distinct_append)

lemma (in valid_unMultigraph) is_trail_intro[intro]:
  "is_trail v' ps v \<Longrightarrow> is_path v' ps v" by (induct ps arbitrary:v',auto)   

lemma (in valid_unMultigraph) is_trail_split:
      "is_trail v (p1@p2) v' \<Longrightarrow> (\<exists>u. is_trail v p1 u \<and> is_trail u p2 v')"
apply (induct p1 arbitrary: v,auto) 
apply (metis is_trail_intro is_path_memb)
done

lemma (in valid_unMultigraph) is_trail_split':"is_trail v (p1@(u,w,u')#p2) v' 
    \<Longrightarrow> is_trail v p1 u \<and> (u,w,u')\<in>E \<and> is_trail u' p2 v'"
  by (metis is_trail.simps(2) is_trail_split)

lemma (in valid_unMultigraph) distinct_elim[simp]:
  assumes "is_trail v ((v1,w,v2)#ps) v'" 
  shows "(v1,w,v2)\<in>edges(rem_unPath ps G) \<longleftrightarrow> (v1,w,v2)\<in>E" 
proof 
  assume "(v1, w, v2) \<in> edges (rem_unPath ps G)"
  thus "(v1, w, v2) \<in> E" by (metis assms is_trail.simps(2))
next
  assume "(v1, w, v2) \<in> E"
  have "(v1,w,v2)\<notin>set ps \<and> (v2,w,v1)\<notin>set ps" by (metis assms is_trail.simps(2))
  hence "(v1,w,v2)\<notin>set ps \<and> (v1,w,v2)\<notin>set (rev_path ps)" by simp
  hence "(v1,w,v2)\<notin>set ps \<union> set (rev_path ps)" by simp
  hence "(v1,w,v2)\<in>edges G - (set ps \<union> set (rev_path ps))"
    using \<open>(v1, w, v2) \<in> E\<close> by auto
  thus "(v1,w,v2)\<in>edges(rem_unPath ps G)" 
    by (metis rem_unPath_edges)
qed

lemma distinct_path_subset:
  assumes "valid_unMultigraph G1" "valid_unMultigraph G2" "edges G1 \<subseteq>edges G2" "nodes G1 \<subseteq>nodes G2"
  assumes distinct_G1:"valid_unMultigraph.is_trail G1 v ps v'"
  shows "valid_unMultigraph.is_trail G2 v ps v'" using distinct_G1
proof (induct ps arbitrary:v)
  case Nil
  hence "v=v'\<and>v'\<in>nodes G1" 
    by (metis (full_types) assms(1) valid_unMultigraph.is_trail.simps(1))
  hence "v=v'\<and>v'\<in>nodes G2" using \<open>nodes G1 \<subseteq> nodes G2\<close> by auto
  thus ?case by (metis assms(2) valid_unMultigraph.is_trail.simps(1))
next
  case (Cons x xs)
  obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
  hence "valid_unMultigraph.is_trail G1 x3 xs v'"
    by (metis Cons.prems assms(1) valid_unMultigraph.is_trail.simps(2)) 
  hence "valid_unMultigraph.is_trail G2 x3 xs v'" using Cons by auto
  moreover have "x\<in>edges G1"
    by (metis Cons.prems assms(1) valid_unMultigraph.is_trail.simps(2) x)
  hence "x\<in>edges G2" using \<open>edges G1 \<subseteq> edges G2\<close> by auto
  moreover have "v=x1\<and>(x1,x2,x3)\<notin>set xs\<and>(x3,x2,x1)\<notin>set xs"
    by (metis Cons.prems assms(1) valid_unMultigraph.is_trail.simps(2) x)
  hence "v=x1" "(x1,x2,x3)\<notin>set xs" "(x3,x2,x1)\<notin>set xs" by auto
  ultimately show ?case by (metis assms(2) valid_unMultigraph.is_trail.simps(2) x)
qed

lemma (in valid_unMultigraph) distinct_path_intro':
  assumes "valid_unMultigraph.is_trail (rem_unPath p G) v ps v'"
  shows "is_trail  v ps v'" 
proof -
  have valid:"valid_unMultigraph (rem_unPath p G)"
    using rem_unPath_valid[OF valid_unMultigraph_axioms,of p] by auto
  moreover have "nodes (rem_unPath p G) \<subseteq> V" by auto
  moreover have "edges (rem_unPath p G) \<subseteq> E" 
    using rem_unPath_edges by auto
  ultimately show ?thesis 
    using distinct_path_subset[of "rem_unPath p G" G] valid_unMultigraph_axioms assms 
    by auto
qed

lemma (in valid_unMultigraph) distinct_path_intro:
  assumes "valid_unMultigraph.is_trail (del_unEdge x1 x2 x3 G) v ps v'"
  shows "is_trail  v ps v'" 
by (metis (full_types) assms distinct_path_intro' rem_unPath.simps(1) 
    rem_unPath.simps(2))

lemma (in valid_unMultigraph) distinct_elim_rev[simp]:
  assumes "is_trail v ((v1,w,v2)#ps) v'" 
  shows "(v2,w,v1)\<in>edges(rem_unPath ps G) \<longleftrightarrow> (v2,w,v1)\<in>E"
proof -
  have  "valid_unMultigraph (rem_unPath ps G)" using valid_unMultigraph_axioms by auto            
  hence "(v2,w,v1)\<in>edges(rem_unPath ps G)\<longleftrightarrow>(v1,w,v2)\<in>edges(rem_unPath ps G)"
    by (metis valid_unMultigraph.corres)
  moreover have "(v2,w,v1)\<in>E\<longleftrightarrow>(v1,w,v2)\<in>E" using corres by simp
  ultimately show ?thesis using distinct_elim by (metis assms)
qed
      
lemma (in valid_unMultigraph) del_UnEdge_even:
  assumes "(v,w,v') \<in> E" "finite E"
  shows "v\<in>odd_nodes_set(del_unEdge v w v' G) \<longleftrightarrow> even (degree v G)" 
proof -
  have "degree v (del_unEdge v w v' G) + 1=degree v G" 
    using del_edge_undirected_degree_plus corres by (metis assms)
  from this [symmetric] have "odd (degree v (del_unEdge v w v' G)) = even (degree v G)"
    by simp
  moreover have "v\<in>nodes (del_unEdge v w v' G)" by (metis E_validD(1) assms(1) del_UnEdge_node)
  ultimately show ?thesis unfolding odd_nodes_set_def by auto
qed

lemma (in valid_unMultigraph) del_UnEdge_even':
  assumes "(v,w,v') \<in> E" "finite E"
  shows "v'\<in>odd_nodes_set(del_unEdge v w v' G) \<longleftrightarrow> even (degree v' G)" 
proof -
  show ?thesis by (metis (full_types) assms corres del_UnEdge_even delete_edge_sym)          
qed

lemma del_UnEdge_even_even:
    assumes "valid_unMultigraph G" "finite(edges G)" "finite(nodes G)" "(v, w, v')\<in>edges G"
    assumes parity_assms: "even (degree v G)" "even (degree v' G)"
    shows "num_of_odd_nodes(del_unEdge v w v' G)=num_of_odd_nodes G + 2"
proof -
  interpret G:valid_unMultigraph by fact 
  have  "v\<in>odd_nodes_set(del_unEdge v w v' G)"  
    by (metis G.del_UnEdge_even assms(2) assms(4) parity_assms(1))
  moreover have  "v'\<in>odd_nodes_set(del_unEdge v w v' G)"  
    by (metis G.del_UnEdge_even' assms(2) assms(4) parity_assms(2))
  ultimately have extra_odd_nodes:"{v,v'} \<subseteq> odd_nodes_set(del_unEdge v w v' G)"
    unfolding odd_nodes_set_def by auto
  moreover have "v \<notin>odd_nodes_set G" and "v'\<notin>odd_nodes_set G" 
    using parity_assms unfolding odd_nodes_set_def by auto 
  hence vv'_odd_disjoint: "{v,v'} \<inter> odd_nodes_set G = {}" by auto
  moreover have "odd_nodes_set(del_unEdge v w v' G) -{v,v'}\<subseteq>odd_nodes_set G " 
    proof
      fix x
      assume x_odd_set: "x \<in> odd_nodes_set (del_unEdge v w v' G) - {v, v'}"
      hence "degree x (del_unEdge v w v' G) = degree x G" 
        by (metis Diff_iff G.degree_frame assms(2))
      hence "odd(degree x G)" using x_odd_set
        unfolding odd_nodes_set_def by auto
      moreover have "x \<in> nodes G" using x_odd_set unfolding odd_nodes_set_def by auto
      ultimately show "x \<in> odd_nodes_set G" unfolding odd_nodes_set_def by auto
    qed
  moreover have "odd_nodes_set G \<subseteq> odd_nodes_set(del_unEdge v w v' G)" 
    proof 
      fix x
      assume x_odd_set:  "x \<in> odd_nodes_set G"
      hence "x\<notin>{v,v'} \<Longrightarrow> odd(degree x (del_unEdge v w v' G))" 
        by (metis (lifting) G.degree_frame assms(2) mem_Collect_eq odd_nodes_set_def)
      hence "x\<notin>{v,v'} \<Longrightarrow> x\<in>odd_nodes_set(del_unEdge v w v' G)" 
        using x_odd_set del_UnEdge_node unfolding odd_nodes_set_def by auto 
      moreover have "x\<in>{v,v'} \<Longrightarrow> x\<in>odd_nodes_set(del_unEdge v w v' G)" 
        using extra_odd_nodes by auto
      ultimately show "x \<in> odd_nodes_set (del_unEdge v w v' G)" by auto
    qed
  ultimately have "odd_nodes_set(del_unEdge v w v' G)=odd_nodes_set G \<union> {v,v'}" by auto
  thus "num_of_odd_nodes(del_unEdge v w v' G) = num_of_odd_nodes G + 2"
    proof -
      assume "odd_nodes_set(del_unEdge v w v' G)=odd_nodes_set G \<union> {v,v'}"
      moreover have "v\<noteq>v'" using G.no_id \<open>(v,w,v')\<in>edges G\<close> by auto
      hence "card{v,v'}=2" by simp
      moreover have " odd_nodes_set G \<inter> {v,v'} = {}" 
        using vv'_odd_disjoint by auto
      moreover have "finite(odd_nodes_set G)" 
        by (metis (lifting) assms(3) mem_Collect_eq odd_nodes_set_def rev_finite_subset subsetI)
      moreover have "finite {v,v'}" by auto
      ultimately show ?thesis unfolding num_of_odd_nodes_def using card_Un_disjoint by metis
    qed
qed
  
lemma del_UnEdge_even_odd:
    assumes "valid_unMultigraph G" "finite(edges G)" "finite(nodes G)" "(v, w, v')\<in>edges G"
    assumes parity_assms: "even (degree v G)" "odd (degree v' G)"
    shows "num_of_odd_nodes(del_unEdge v w v' G)=num_of_odd_nodes G"
proof -
  interpret G : valid_unMultigraph by fact
  have odd_v:"v\<in>odd_nodes_set(del_unEdge v w v' G)" 
    by (metis G.del_UnEdge_even assms(2) assms(4) parity_assms(1))
  have  not_odd_v':"v'\<notin>odd_nodes_set(del_unEdge v w v' G)"
    by (metis G.del_UnEdge_even' assms(2) assms(4) parity_assms(2))
  have "odd_nodes_set(del_unEdge v w v' G) \<union> {v'} \<subseteq>odd_nodes_set G \<union> {v}"
    proof 
      fix x 
      assume x_prems:" x \<in> odd_nodes_set (del_unEdge v w v' G) \<union> {v'}"
      have "x=v' \<Longrightarrow>x\<in>odd_nodes_set G \<union> {v}" 
        using parity_assms
        by (metis (lifting) G.E_validD(2) Un_def assms(4) mem_Collect_eq odd_nodes_set_def )
      moreover have "x=v \<Longrightarrow> x\<in>odd_nodes_set G \<union> {v}"  
        by (metis insertI1 insert_is_Un sup_commute)
      moreover have "x\<notin>{v,v'} \<Longrightarrow> x \<in> odd_nodes_set (del_unEdge v w v' G)" 
        using x_prems by auto
      hence "x\<notin>{v,v'} \<Longrightarrow> x \<in> odd_nodes_set G" unfolding odd_nodes_set_def
        using G.degree_frame \<open>finite (edges G)\<close> by auto
      hence "x\<notin>{v,v'} \<Longrightarrow> x\<in>odd_nodes_set G \<union> {v}" by simp 
      ultimately show "x \<in> odd_nodes_set G \<union> {v}" by auto
    qed
  moreover have "odd_nodes_set G \<union> {v} \<subseteq> odd_nodes_set(del_unEdge v w v' G) \<union> {v'}" 
    proof
      fix x
      assume x_prems: "x \<in> odd_nodes_set G \<union> {v}"
      have "x=v \<Longrightarrow> x \<in> odd_nodes_set (del_unEdge v w v' G) \<union> {v'}" 
        by (metis UnI1 odd_v)
      moreover have "x=v' \<Longrightarrow> x \<in> odd_nodes_set (del_unEdge v w v' G) \<union> {v'}" 
        by auto
      moreover have "x\<notin>{v,v'} \<Longrightarrow> x \<in> odd_nodes_set G \<union> {v}" using x_prems by auto
      hence "x\<notin>{v,v'} \<Longrightarrow>  x\<in>odd_nodes_set (del_unEdge v w v' G)" unfolding odd_nodes_set_def
        using G.degree_frame \<open>finite (edges G)\<close> by auto
      hence "x\<notin>{v,v'} \<Longrightarrow> x \<in> odd_nodes_set (del_unEdge v w v' G) \<union> {v'}" by simp
        ultimately show "x \<in> odd_nodes_set (del_unEdge v w v' G) \<union> {v'}" by auto
    qed
  ultimately have "odd_nodes_set(del_unEdge v w v' G) \<union> {v'} = odd_nodes_set G \<union> {v}"
    by auto
  moreover have " odd_nodes_set G \<inter> {v} = {}" 
    using parity_assms unfolding odd_nodes_set_def by auto
  moreover have " odd_nodes_set(del_unEdge v w v' G) \<inter> {v'}={}" 
    by (metis Int_insert_left_if0 inf_bot_left inf_commute not_odd_v')
  moreover have "finite (odd_nodes_set(del_unEdge v w v' G))" 
     using \<open>finite (nodes G)\<close> by auto
  moreover have "finite (odd_nodes_set G)" using \<open>finite (nodes G)\<close> by auto
  ultimately have "card(odd_nodes_set G) + card {v} = 
                   card(odd_nodes_set(del_unEdge v w v' G)) + card {v'}" 
    using card_Un_disjoint[of "odd_nodes_set (del_unEdge v w v' G)" "{v'}"] 
      card_Un_disjoint[of "odd_nodes_set G" "{v}"] 
    by auto 
  thus ?thesis unfolding num_of_odd_nodes_def by simp 
qed  
  
lemma del_UnEdge_odd_even:
    assumes "valid_unMultigraph G" "finite(edges G)" "finite(nodes G)" "(v, w, v')\<in>edges G"
    assumes parity_assms: "odd (degree v G)" "even (degree v' G)"
    shows "num_of_odd_nodes(del_unEdge v w v' G)=num_of_odd_nodes G"  
by (metis assms del_UnEdge_even_odd delete_edge_sym parity_assms valid_unMultigraph.corres)
 
lemma del_UnEdge_odd_odd:
    assumes "valid_unMultigraph G" "finite(edges G)" "finite(nodes G)" "(v, w, v')\<in>edges G"
    assumes parity_assms: "odd (degree v G)" "odd (degree v' G)"
    shows "num_of_odd_nodes G=num_of_odd_nodes(del_unEdge v w v' G)+2"
proof -
  interpret G:valid_unMultigraph by fact
  have  "v\<notin>odd_nodes_set(del_unEdge v w v' G)"  
    by (metis G.del_UnEdge_even assms(2) assms(4) parity_assms(1))
  moreover have  "v'\<notin>odd_nodes_set(del_unEdge v w v' G)"  
    by (metis G.del_UnEdge_even' assms(2) assms(4) parity_assms(2))
  ultimately have vv'_disjoint: "{v,v'} \<inter> odd_nodes_set(del_unEdge v w v' G) = {}" 
    by (metis (full_types) Int_insert_left_if0 inf_bot_left)
  moreover have extra_odd_nodes:"{v,v'} \<subseteq> odd_nodes_set( G)"
    unfolding odd_nodes_set_def 
    using \<open>(v,w,v')\<in>edges G\<close>
    by (metis (lifting) G.E_validD empty_subsetI insert_subset mem_Collect_eq parity_assms)  
  moreover have "odd_nodes_set G -{v,v'}\<subseteq>odd_nodes_set (del_unEdge v w v' G) " 
    proof
      fix x
      assume x_odd_set: "x \<in> odd_nodes_set G - {v, v'}"
      hence "degree x G = degree x (del_unEdge v w v' G)" 
        by (metis Diff_iff G.degree_frame assms(2))
      hence "odd(degree x (del_unEdge v w v' G))" using x_odd_set 
        unfolding odd_nodes_set_def by auto
      moreover have "x \<in> nodes (del_unEdge v w v' G)" 
        using x_odd_set unfolding odd_nodes_set_def by auto
      ultimately show "x \<in> odd_nodes_set (del_unEdge v w v' G)" 
        unfolding odd_nodes_set_def by auto
    qed
  moreover have "odd_nodes_set (del_unEdge v w v' G) \<subseteq> odd_nodes_set G" 
    proof 
      fix x
      assume x_odd_set:  "x \<in> odd_nodes_set (del_unEdge v w v' G)"
      hence "x\<notin>{v,v'} \<Longrightarrow> odd(degree x G)" 
        using assms G.degree_frame unfolding odd_nodes_set_def
        by auto
      hence "x\<notin>{v,v'} \<Longrightarrow> x\<in>odd_nodes_set G" 
        using x_odd_set del_UnEdge_node unfolding odd_nodes_set_def  
        by auto
      moreover have "x\<in>{v,v'} \<Longrightarrow> x\<in>odd_nodes_set G" 
        using extra_odd_nodes by auto
      ultimately show "x \<in> odd_nodes_set G" by auto
    qed
  ultimately have "odd_nodes_set G=odd_nodes_set (del_unEdge v w v' G) \<union> {v,v'}" 
    by auto
  thus ?thesis
    proof -
      assume "odd_nodes_set G=odd_nodes_set (del_unEdge v w v' G) \<union> {v,v'}"
      moreover have " odd_nodes_set (del_unEdge v w v' G) \<inter> {v,v'} = {}" 
        using vv'_disjoint by auto
      moreover have "finite(odd_nodes_set (del_unEdge v w v' G))" 
        using assms del_UnEdge_node finite_subset unfolding odd_nodes_set_def
        by auto
      moreover have "finite {v,v'}" by auto
      ultimately have "card(odd_nodes_set G)
                       = card(odd_nodes_set  (del_unEdge v w v' G)) + card{v,v'}"
        unfolding num_of_odd_nodes_def 
        using card_Un_disjoint 
        by metis 
      moreover have "v\<noteq>v'" using G.no_id \<open>(v,w,v')\<in>edges G\<close> by auto
      hence "card{v,v'}=2" by simp
      ultimately show ?thesis unfolding num_of_odd_nodes_def by simp
    qed
qed 

lemma (in valid_unMultigraph) rem_UnPath_parity_v': 
  assumes "finite E"  "is_trail v ps v'" 
  shows "v\<noteq>v' \<longleftrightarrow> (odd (degree v' (rem_unPath ps G)) = even(degree v' G))" using assms 
proof (induct ps arbitrary:v)
  case Nil
  thus ?case by (metis is_trail.simps(1) rem_unPath.simps(1))
next
  case (Cons x xs) print_cases
  obtain x1 x2 x3 where x: "x=(x1,x2,x3)" by (metis prod_cases3)
  hence rem_x:"odd (degree v' (rem_unPath (x#xs) G)) = odd(degree v' (del_unEdge
            x1 x2 x3 (rem_unPath xs G)))" 
    by (metis  rem_unPath.simps(2) rem_unPath_com)
  have "x3=v' \<Longrightarrow> ?case" 
    proof (cases "v=v'")
      case True 
      assume "x3=v'"
      have "x1=v'" using x by (metis Cons.prems(2) True is_trail.simps(2))
      thus ?thesis using \<open>x3=v'\<close> by (metis Cons.prems(2) is_trail.simps(2) no_id x)
    next
      case False
      assume "x3=v'"
      have "odd (degree v' (rem_unPath (x # xs) G)) =odd(degree v' (
            del_unEdge x1 x2 x3 (rem_unPath xs G)))" using rem_x .
      also have "...=odd(degree v' (rem_unPath xs G) - 1)" 
        proof -
          have "finite (edges (rem_unPath xs G))" 
            by (metis (full_types) assms(1) finite_Diff rem_unPath_edges)
          moreover have "(x1,x2,x3) \<in>edges( rem_unPath xs G)" 
            by (metis Cons.prems(2) distinct_elim is_trail.simps(2) x)
          moreover have "(x3,x2,x1) \<in>edges( rem_unPath xs G)"
            by (metis Cons.prems(2) corres distinct_elim_rev is_trail.simps(2) x)
          ultimately show ?thesis 
            by (metis \<open>x3 = v'\<close> del_edge_undirected_degree_minus delete_edge_sym  x)
        qed
      also have "...=even(degree v' (rem_unPath xs G))"
        proof -
          have "(x1,x2,x3)\<in>E" by (metis Cons.prems(2) is_trail.simps(2) x)
          hence "(x3,x2,x1)\<in>edges (rem_unPath xs G)" 
            by (metis Cons.prems(2) corres distinct_elim_rev x)
          hence "(x3,x2,x1)\<in>{e \<in> edges (rem_unPath xs G). fst e = v'}" 
            using \<open>x3=v'\<close> by (metis (mono_tags) fst_conv mem_Collect_eq)
          moreover have "finite {e \<in> edges (rem_unPath xs G). fst e = v'}"
            using \<open>finite E\<close> by auto
          ultimately have "degree v' (rem_unPath xs G)\<noteq>0" 
            unfolding degree_def by auto
          thus ?thesis by auto
        qed
      also have "...=even (degree v' G)" 
        using \<open>x3 = v'\<close> assms
        by (metis (mono_tags) Cons.hyps Cons.prems(2) is_trail.simps(2) x)
      finally have "odd (degree v' (rem_unPath (x # xs) G))=even (degree v' G)" .
      thus ?thesis by (metis False)
    qed
  moreover have "x3\<noteq>v'\<Longrightarrow>?case" 
    proof (cases "v=v'")
      case True
      assume "x3\<noteq>v'"
      have "odd (degree v' (rem_unPath (x # xs) G)) =odd(degree v' (
            del_unEdge x1 x2 x3 (rem_unPath xs G)))" using rem_x .
      also have "...=odd(degree v' (rem_unPath xs G) - 1)" 
        proof -
          have "finite (edges (rem_unPath xs G))" 
            by (metis (full_types) assms(1) finite_Diff rem_unPath_edges)
          moreover have "(x1,x2,x3) \<in>edges( rem_unPath xs G)" 
            by (metis Cons.prems(2) distinct_elim is_trail.simps(2) x)
          moreover have "(x3,x2,x1) \<in>edges( rem_unPath xs G)"
            by (metis Cons.prems(2) corres distinct_elim_rev is_trail.simps(2) x)
          ultimately show ?thesis 
            using True x
            by (metis Cons.prems(2) del_edge_undirected_degree_minus is_trail.simps(2))
        qed
      also have "...=even(degree v' (rem_unPath xs G))"
        proof -
          have "(x1,x2,x3)\<in>E" by (metis Cons.prems(2) is_trail.simps(2) x)
          hence "(x1,x2,x3)\<in>edges (rem_unPath xs G)" 
            by (metis Cons.prems(2) distinct_elim x)
          hence "(x1,x2,x3)\<in>{e \<in> edges (rem_unPath xs G). fst e = v'}" 
            using \<open>v=v'\<close> x  Cons
            by (metis (lifting, mono_tags) fst_conv is_trail.simps(2) mem_Collect_eq) 
          moreover have "finite {e \<in> edges (rem_unPath xs G). fst e = v'}"
            using \<open>finite E\<close> by auto
          ultimately have "degree v' (rem_unPath xs G)\<noteq>0" 
            unfolding degree_def by auto
          thus ?thesis by auto
        qed
      also have "...\<noteq>even (degree v' G)" 
        using \<open>x3 \<noteq> v'\<close> assms 
        by (metis Cons.hyps Cons.prems(2)is_trail.simps(2) x)
      finally have "odd (degree v' (rem_unPath (x # xs) G))\<noteq>even (degree v' G)" .
      thus ?thesis by (metis True)
    next 
      case False
      assume "x3\<noteq>v'"
      have "odd (degree v' (rem_unPath (x # xs) G)) =odd(degree v' (
            del_unEdge x1 x2 x3 (rem_unPath xs G)))" using rem_x .
      also have "...=odd(degree v' (rem_unPath xs G))" 
        proof -
          have "v=x1" by (metis Cons.prems(2) is_trail.simps(2) x)
          hence "v'\<notin>{x1,x3}" by (metis (mono_tags) False \<open>x3 \<noteq> v'\<close> empty_iff insert_iff) 
          moreover have "valid_unMultigraph (rem_unPath xs G)" 
            using valid_unMultigraph_axioms by auto
          moreover have "finite (edges (rem_unPath xs G))" 
            by (metis (full_types) assms(1) finite_Diff rem_unPath_edges)
          ultimately have "degree v' (del_unEdge x1 x2 x3 (rem_unPath xs G))
                            =degree v' (rem_unPath xs G)" using degree_frame 
            by (metis valid_unMultigraph.degree_frame)
          thus ?thesis by simp
        qed
      also have "...=even (degree v' G)"
        using assms x \<open>x3 \<noteq> v'\<close>
        by (metis Cons.hyps Cons.prems(2)  is_trail.simps(2))
      finally have "odd (degree v' (rem_unPath (x # xs) G))=even (degree v' G)" .
      thus ?thesis by (metis False)
    qed
  ultimately show ?case by auto
qed

lemma (in valid_unMultigraph) rem_UnPath_parity_v: 
  assumes "finite E"  "is_trail v ps v'" 
  shows "v\<noteq>v' \<longleftrightarrow> (odd (degree v (rem_unPath ps G)) = even(degree v G))" 
by (metis assms is_trail_rev rem_UnPath_parity_v' rem_unPath_graph)

lemma (in valid_unMultigraph) rem_UnPath_parity_others:
  assumes "finite E"  "is_trail v ps v'" "n\<notin>{v,v'}"
  shows " even (degree n (rem_unPath ps G)) = even(degree n G)" using assms
proof (induct ps arbitrary: v)
  case Nil
  thus ?case by auto
next
  case (Cons x xs)
  obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3) 
  hence "even (degree n (rem_unPath (x#xs) G))= even (degree n (
          del_unEdge x1 x2 x3 (rem_unPath xs G)))" 
    by (metis rem_unPath.simps(2) rem_unPath_com)
  have "n=x3 \<Longrightarrow>?case" 
    proof - 
      assume "n=x3"
      have "even (degree n (rem_unPath (x#xs) G))= even (degree n (
          del_unEdge x1 x2 x3 (rem_unPath xs G)))" 
        by (metis rem_unPath.simps(2) rem_unPath_com x)
      also have "...=even(degree n (rem_unPath xs G) - 1)" 
        proof -
          have "finite (edges (rem_unPath xs G))" 
            by (metis (full_types) assms(1) finite_Diff rem_unPath_edges)
          moreover have "(x1,x2,x3) \<in>edges( rem_unPath xs G)" 
            by (metis Cons.prems(2) distinct_elim is_trail.simps(2) x)
          moreover have "(x3,x2,x1) \<in>edges( rem_unPath xs G)"
            by (metis Cons.prems(2) corres distinct_elim_rev is_trail.simps(2) x)
          ultimately show ?thesis 
            using \<open>n = x3\<close> del_edge_undirected_degree_minus' 
            by auto
        qed
      also have "...=odd(degree n (rem_unPath xs G))"
        proof -
          have "(x1,x2,x3)\<in>E" by (metis Cons.prems(2) is_trail.simps(2) x)
          hence "(x3,x2,x1)\<in>edges (rem_unPath xs G)" 
            by (metis Cons.prems(2) corres distinct_elim_rev x)
          hence "(x3,x2,x1)\<in>{e \<in> edges (rem_unPath xs G). fst e = n}" 
            using \<open>n=x3\<close> by (metis (mono_tags) fst_conv mem_Collect_eq)
          moreover have "finite {e \<in> edges (rem_unPath xs G). fst e = n}"
            using \<open>finite E\<close> by auto
          ultimately have "degree n (rem_unPath xs G)\<noteq>0" 
            unfolding degree_def by auto
          thus ?thesis by auto
        qed
      also have "...=even(degree n G)" 
        proof -
          have "x3\<noteq>v'" by (metis \<open>n = x3\<close> assms(3) insert_iff)
          hence "odd (degree x3 (rem_unPath xs G)) = even(degree x3 G)"
            using Cons assms
            by (metis is_trail.simps(2) rem_UnPath_parity_v x)
          thus ?thesis using \<open>n=x3\<close> by auto
        qed
      finally have "even (degree n (rem_unPath (x#xs) G))=even(degree n G)" .
      thus ?thesis .
    qed
  moreover have "n\<noteq>x3 \<Longrightarrow>?case" 
    proof -
      assume "n\<noteq>x3"
       have "even (degree n (rem_unPath (x#xs) G))= even (degree n (
          del_unEdge x1 x2 x3 (rem_unPath xs G)))" 
        by (metis rem_unPath.simps(2) rem_unPath_com x)
      also have "...=even(degree n (rem_unPath xs G))" 
        proof -
          have "v=x1" by (metis Cons.prems(2) is_trail.simps(2) x)
          hence "n\<notin>{x1,x3}" by (metis Cons.prems(3) \<open>n \<noteq> x3\<close> insertE insertI1 singletonE)
          moreover have "valid_unMultigraph (rem_unPath xs G)" 
            using valid_unMultigraph_axioms by auto
          moreover have "finite (edges (rem_unPath xs G))" 
            by (metis (full_types) assms(1) finite_Diff rem_unPath_edges)
          ultimately have "degree n (del_unEdge x1 x2 x3 (rem_unPath xs G))
                            =degree n (rem_unPath xs G)" using degree_frame 
            by (metis valid_unMultigraph.degree_frame)
          thus ?thesis by simp
        qed
      also have "...=even(degree n G)" 
        using Cons assms \<open>n \<noteq> x3\<close> x by auto
      finally have "even (degree n (rem_unPath (x#xs) G))=even(degree n G)" .
      thus ?thesis .
    qed
  ultimately show ?case by auto
qed
    
lemma (in valid_unMultigraph) rem_UnPath_even:
  assumes "finite E" "finite V" "is_trail v ps v'" 
  assumes parity_assms:  "even (degree v' G)"
  shows "num_of_odd_nodes (rem_unPath ps G) = num_of_odd_nodes G 
          + (if even (degree v G)\<and> v\<noteq>v' then 2 else 0)" using assms
proof (induct ps arbitrary:v)
  case Nil 
  thus ?case by auto
next
  case (Cons x xs)
  obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3) 
  have fin_nodes: "finite (nodes (rem_unPath xs G))" using Cons by auto
  have fin_edges: "finite (edges (rem_unPath xs G))" using Cons by auto
  have valid_rem_xs: "valid_unMultigraph (rem_unPath xs G)" using valid_unMultigraph_axioms 
    by auto
  have x_in:"(x1,x2,x3)\<in>edges (rem_unPath xs G)" 
    by (metis (full_types) Cons.prems(3) distinct_elim is_trail.simps(2) x)
  have "even (degree x1 (rem_unPath xs G)) 
        \<Longrightarrow> even(degree x3 (rem_unPath xs G)) \<Longrightarrow> ?case" 
    proof -
      assume parity_x1_x3: "even (degree x1 (rem_unPath xs G))" 
                           "even(degree x3 (rem_unPath xs G))"
      have "num_of_odd_nodes (rem_unPath (x#xs) G)= num_of_odd_nodes 
         (del_unEdge x1 x2 x3 (rem_unPath xs G))"
        by (metis rem_unPath.simps(2) rem_unPath_com x)
      also have "... =num_of_odd_nodes (rem_unPath xs G)+2" 
        using  parity_x1_x3  fin_nodes fin_edges valid_rem_xs x_in del_UnEdge_even_even 
        by metis
      also have "...=num_of_odd_nodes G+(if even(degree x3 G) \<and> x3\<noteq>v' then 2 else 0 )+2"
        using Cons.hyps[OF \<open>finite E\<close> \<open>finite V\<close>, of x3] \<open>is_trail v (x # xs) v'\<close>
          \<open>even (degree v' G)\<close> x 
        by auto
      also have "...=num_of_odd_nodes G+2" 
        proof -
          have "even(degree x3 G) \<and> x3\<noteq>v' \<longleftrightarrow> odd (degree x3 (rem_unPath xs G))" 
            using Cons.prems assms
            by (metis  is_trail.simps(2) parity_x1_x3(2) rem_UnPath_parity_v x)
          thus ?thesis using parity_x1_x3(2) by auto
        qed
      also have "...=num_of_odd_nodes G+(if even(degree v G) \<and> v\<noteq>v' then 2 else 0)" 
        proof -
          have "x1\<noteq>x3" by (metis valid_rem_xs valid_unMultigraph.no_id x_in)
          moreover hence "x1\<noteq>v'" 
            using Cons assms  
            by (metis is_trail.simps(2)  parity_x1_x3(1) rem_UnPath_parity_v' x)
          ultimately have "x1\<notin>{x3,v'}" by auto
          hence  "even(degree x1 G)" 
            using Cons.prems(3) assms(1) assms(2) parity_x1_x3(1) 
            by (metis (full_types)  is_trail.simps(2) rem_UnPath_parity_others x)
          hence "even(degree x1 G) \<and> x1\<noteq>v'" using \<open>x1 \<noteq> v'\<close> by auto
          hence "even(degree v G) \<and> v\<noteq>v'" by (metis Cons.prems(3) is_trail.simps(2) x)
          thus ?thesis by auto
        qed
      finally have "num_of_odd_nodes (rem_unPath (x#xs) G)=
                        num_of_odd_nodes G+(if even(degree v G) \<and> v\<noteq>v' then 2 else 0)" .
      thus ?thesis .
    qed       
  moreover have "even (degree x1 (rem_unPath xs G)) \<Longrightarrow> 
                    odd(degree x3 (rem_unPath xs G)) \<Longrightarrow> ?case" 
    proof -
      assume parity_x1_x3: "even (degree x1 (rem_unPath xs G))" 
                           "odd (degree x3 (rem_unPath xs G))"
      have "num_of_odd_nodes (rem_unPath (x#xs) G)= num_of_odd_nodes 
         (del_unEdge x1 x2 x3 (rem_unPath xs G))"
        by (metis rem_unPath.simps(2) rem_unPath_com x)
      also have "... =num_of_odd_nodes (rem_unPath xs G)" 
        using  parity_x1_x3  fin_nodes fin_edges valid_rem_xs x_in 
        by (metis del_UnEdge_even_odd)
      also have "...=num_of_odd_nodes G+(if even(degree x3 G) \<and> x3\<noteq>v' then 2 else 0 )"
        using  Cons.hyps Cons.prems(3) assms(1) assms(2)  parity_assms x
        by auto
      also have "...=num_of_odd_nodes G+2" 
         proof -
          have "even(degree x3 G) \<and> x3\<noteq>v' \<longleftrightarrow> odd (degree x3 (rem_unPath xs G))" 
            using Cons.prems assms
            by (metis  is_trail.simps(2) parity_x1_x3(2) rem_UnPath_parity_v x)
          thus ?thesis using parity_x1_x3(2) by auto
        qed
      also have "...=num_of_odd_nodes G+(if even(degree v G) \<and> v\<noteq>v' then 2 else 0)"
        proof -
          have "x1\<noteq>x3" by (metis valid_rem_xs valid_unMultigraph.no_id x_in)
          moreover hence "x1\<noteq>v'" 
            using Cons assms  
            by (metis is_trail.simps(2)  parity_x1_x3(1) rem_UnPath_parity_v' x)
          ultimately have "x1\<notin>{x3,v'}" by auto
          hence  "even(degree x1 G)" 
            using Cons.prems(3) assms(1) assms(2) parity_x1_x3(1) 
            by (metis (full_types)  is_trail.simps(2) rem_UnPath_parity_others x)
          hence "even(degree x1 G) \<and> x1\<noteq>v'" using \<open>x1 \<noteq> v'\<close> by auto
          hence "even(degree v G) \<and> v\<noteq>v'" by (metis Cons.prems(3) is_trail.simps(2) x)
          thus ?thesis by auto
        qed
      finally have "num_of_odd_nodes (rem_unPath (x#xs) G)=
                        num_of_odd_nodes G+(if even(degree v G) \<and> v\<noteq>v' then 2 else 0)" .
      thus ?thesis .
    qed         
  moreover have "odd (degree x1 (rem_unPath xs G)) \<Longrightarrow> 
                    even(degree x3 (rem_unPath xs G)) \<Longrightarrow> ?case"             
    proof -
      assume parity_x1_x3: "odd (degree x1 (rem_unPath xs G))" 
                           "even (degree x3 (rem_unPath xs G))"
      have "num_of_odd_nodes (rem_unPath (x#xs) G)= num_of_odd_nodes 
         (del_unEdge x1 x2 x3 (rem_unPath xs G))"
        by (metis rem_unPath.simps(2) rem_unPath_com x)
      also have "... =num_of_odd_nodes (rem_unPath xs G)" 
        using  parity_x1_x3  fin_nodes fin_edges valid_rem_xs x_in 
        by (metis del_UnEdge_odd_even)
      also have "...=num_of_odd_nodes G+(if even(degree x3 G) \<and> x3\<noteq>v' then 2 else 0 )"
        using  Cons.hyps Cons.prems(3) assms(1) assms(2) parity_assms x
        by auto
      also have "...=num_of_odd_nodes G" 
        proof -
          have "even(degree x3 G) \<and> x3\<noteq>v' \<longleftrightarrow> odd (degree x3 (rem_unPath xs G))" 
            using Cons.prems assms
            by (metis  is_trail.simps(2) parity_x1_x3(2) rem_UnPath_parity_v x)
          thus ?thesis using parity_x1_x3(2) by auto
        qed
      also have "...=num_of_odd_nodes G+(if even(degree v G) \<and> v\<noteq>v' then 2 else 0)" 
        proof (cases "v\<noteq>v'")
          case True
          have "x1\<noteq>x3" by (metis valid_rem_xs valid_unMultigraph.no_id x_in)
          moreover have "is_trail x3 xs v' " 
            by (metis Cons.prems(3) is_trail.simps(2) x)
          ultimately have  "odd (degree x1 (rem_unPath xs G)) 
                          \<longleftrightarrow> odd(degree x1 G)"  
            using True parity_x1_x3(1) rem_UnPath_parity_others x Cons.prems(3) assms(1) assms(2)
            by auto
          hence "odd(degree x1 G)" by (metis parity_x1_x3(1))
          thus ?thesis 
            by (metis (mono_tags) Cons.prems(3) Nat.add_0_right is_trail.simps(2) x)
        next
          case False
          then show ?thesis by auto
        qed    
      finally have "num_of_odd_nodes (rem_unPath (x#xs) G)=
                        num_of_odd_nodes G+(if even(degree v G) \<and> v\<noteq>v' then 2 else 0)" .
      thus ?thesis .
    qed         
  moreover have "odd (degree x1 (rem_unPath xs G)) \<Longrightarrow> 
                    odd(degree x3 (rem_unPath xs G)) \<Longrightarrow> ?case" 
    proof -
      assume parity_x1_x3: "odd (degree x1 (rem_unPath xs G))" 
                           "odd (degree x3 (rem_unPath xs G))"
      have "num_of_odd_nodes (rem_unPath (x#xs) G)= num_of_odd_nodes 
         (del_unEdge x1 x2 x3 (rem_unPath xs G))"
        by (metis rem_unPath.simps(2) rem_unPath_com x)
      also have "... =num_of_odd_nodes (rem_unPath xs G)-(2::nat)" 
        using del_UnEdge_odd_odd
        by (metis add_implies_diff  fin_edges fin_nodes parity_x1_x3 valid_rem_xs x_in)  
      also have "...=num_of_odd_nodes G+(if even(degree x3 G) \<and> x3\<noteq>v' then 2 else 0 )-(2::nat)"
        using Cons assms 
        by (metis is_trail.simps(2) x)
      also have "...=num_of_odd_nodes G" 
        proof -
          have "even(degree x3 G) \<and> x3\<noteq>v' \<longleftrightarrow> odd (degree x3 (rem_unPath xs G))" 
            using Cons.prems assms
            by (metis  is_trail.simps(2) parity_x1_x3(2) rem_UnPath_parity_v x)
          thus ?thesis using parity_x1_x3(2) by auto
        qed
      also have "...=num_of_odd_nodes G+(if even(degree v G) \<and> v\<noteq>v' then 2 else 0)" 
         proof (cases "v\<noteq>v'")
          case True
          have "x1\<noteq>x3" by (metis valid_rem_xs valid_unMultigraph.no_id x_in)
          moreover have "is_trail x3 xs v' " 
            by (metis Cons.prems(3) is_trail.simps(2) x)
          ultimately have  "odd (degree x1 (rem_unPath xs G)) 
                          \<longleftrightarrow> odd(degree x1 G)"  
            using True Cons.prems(3) assms(1) assms(2) parity_x1_x3(1) rem_UnPath_parity_others x 
            by auto
          hence "odd(degree x1 G)" by (metis parity_x1_x3(1))
          thus ?thesis 
            by (metis (mono_tags) Cons.prems(3) Nat.add_0_right is_trail.simps(2) x)
        next
          case False
          thus ?thesis by (metis (mono_tags) add_0_iff)
        qed    
      finally have "num_of_odd_nodes (rem_unPath (x#xs) G)=
                        num_of_odd_nodes G+(if even(degree v G) \<and> v\<noteq>v' then 2 else 0)" .
      thus ?thesis .
    qed       
  ultimately show ?case by metis
qed 

lemma (in valid_unMultigraph) rem_UnPath_odd:
  assumes "finite E" "finite V" "is_trail v ps v'" 
  assumes parity_assms:  "odd (degree v' G)"
  shows "num_of_odd_nodes (rem_unPath ps G) = num_of_odd_nodes G 
          + (if odd (degree v G)\<and> v\<noteq>v' then -2 else 0)" using assms
proof (induct ps arbitrary:v)
  case Nil 
  thus ?case by auto
next
  case (Cons x xs)
  obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3) 
  have fin_nodes: "finite (nodes (rem_unPath xs G))" using Cons by auto
  have fin_edges: "finite (edges (rem_unPath xs G))" using Cons by auto
  have valid_rem_xs: "valid_unMultigraph (rem_unPath xs G)" using valid_unMultigraph_axioms 
    by auto
  have x_in:"(x1,x2,x3)\<in>edges (rem_unPath xs G)" 
    by (metis (full_types) Cons.prems(3) distinct_elim is_trail.simps(2) x)
  have "even (degree x1 (rem_unPath xs G)) 
        \<Longrightarrow> even(degree x3 (rem_unPath xs G)) \<Longrightarrow> ?case" 
    proof -
      assume parity_x1_x3: "even (degree x1 (rem_unPath xs G))" 
                           "even (degree x3 (rem_unPath xs G))"
      have "num_of_odd_nodes (rem_unPath (x#xs) G)= num_of_odd_nodes 
         (del_unEdge x1 x2 x3 (rem_unPath xs G))"
        by (metis rem_unPath.simps(2) rem_unPath_com x)
      also have "... =num_of_odd_nodes (rem_unPath xs G)+2" 
        using  parity_x1_x3  fin_nodes fin_edges valid_rem_xs x_in del_UnEdge_even_even 
        by metis
      also have "...=num_of_odd_nodes G+(if odd(degree x3 G) \<and> x3\<noteq>v' then - 2 else 0 )+2"
        using Cons.hyps[OF \<open>finite E\<close> \<open>finite V\<close>,of x3] \<open>is_trail v (x # xs) v'\<close>
          \<open>odd (degree v' G)\<close> x
        by auto
      also have "...=num_of_odd_nodes G" 
        proof -
          have "odd (degree x3 G) \<and> x3\<noteq>v' \<longleftrightarrow> even (degree x3 (rem_unPath xs G))" 
            using Cons.prems assms
            by (metis  is_trail.simps(2) parity_x1_x3(2) rem_UnPath_parity_v x)
          thus ?thesis using parity_x1_x3(2) by auto
        qed
      also have "...=num_of_odd_nodes G+(if odd(degree v G) \<and> v\<noteq>v' then -2 else 0)" 
         proof (cases "v\<noteq>v'")
          case True
          have "x1\<noteq>x3" by (metis valid_rem_xs valid_unMultigraph.no_id x_in)
          moreover have "is_trail x3 xs v' " 
            by (metis Cons.prems(3) is_trail.simps(2) x)
          ultimately have  "even (degree x1 (rem_unPath xs G)) 
                          \<longleftrightarrow> even (degree x1 G)"  
            using True Cons.prems(3) assms(1) assms(2) parity_x1_x3(1) 
                rem_UnPath_parity_others x
            by auto
          hence "even (degree x1 G)" by (metis parity_x1_x3(1))
          thus ?thesis 
            by (metis (hide_lams, mono_tags) Cons.prems(3)  is_trail.simps(2)  
                monoid_add_class.add.right_neutral x)
        next
          case False
          then show ?thesis by auto
        qed    
      finally have "num_of_odd_nodes (rem_unPath (x#xs) G)=
                        num_of_odd_nodes G+(if odd(degree v G) \<and> v\<noteq>v' then -2 else 0)" .
      thus ?thesis .
    qed       
  moreover have "even (degree x1 (rem_unPath xs G)) \<Longrightarrow> 
                    odd(degree x3 (rem_unPath xs G)) \<Longrightarrow> ?case" 
    proof -
      assume parity_x1_x3: "even (degree x1 (rem_unPath xs G))" 
                           "odd (degree x3 (rem_unPath xs G))"
      have "num_of_odd_nodes (rem_unPath (x#xs) G)= num_of_odd_nodes 
         (del_unEdge x1 x2 x3 (rem_unPath xs G))"
        by (metis rem_unPath.simps(2) rem_unPath_com x)
      also have "... =num_of_odd_nodes (rem_unPath xs G)" 
        using  parity_x1_x3  fin_nodes fin_edges valid_rem_xs x_in 
        by (metis del_UnEdge_even_odd)
      also have "...=num_of_odd_nodes G+(if odd(degree x3 G) \<and> x3\<noteq>v' then - 2 else 0 )"
        using  Cons.hyps[OF \<open>finite E\<close> \<open>finite V\<close>, of x3] Cons.prems(3) assms(1) assms(2) 
          parity_assms x
        by auto
      also have "...=num_of_odd_nodes G" 
         proof -
          have "odd(degree x3 G) \<and> x3\<noteq>v' \<longleftrightarrow> even (degree x3 (rem_unPath xs G))" 
            using Cons.prems assms
            by (metis  is_trail.simps(2) parity_x1_x3(2) rem_UnPath_parity_v x)
          thus ?thesis using parity_x1_x3(2) by auto
        qed
      also have "...= num_of_odd_nodes G+(if odd(degree v G) \<and> v\<noteq>v' then -2 else 0)"
         proof (cases "v\<noteq>v'")
          case True
          have "x1\<noteq>x3" by (metis valid_rem_xs valid_unMultigraph.no_id x_in)
          moreover have "is_trail x3 xs v' " 
            by (metis Cons.prems(3) is_trail.simps(2) x)
          ultimately have  "even (degree x1 (rem_unPath xs G)) 
                          \<longleftrightarrow> even (degree x1 G)"  
            using True Cons.prems(3) assms(1) assms(2) parity_x1_x3(1) 
                rem_UnPath_parity_others x
            by auto
          hence "even (degree x1 G)" by (metis parity_x1_x3(1))
          with Cons.prems(3) x show ?thesis by auto
        next
          case False
          then show ?thesis by auto
        qed   
      finally have "num_of_odd_nodes (rem_unPath (x#xs) G)=
                        num_of_odd_nodes G+(if odd(degree v G) \<and> v\<noteq>v' then -2 else 0)" .
      thus ?thesis .
    qed         
  moreover have "odd (degree x1 (rem_unPath xs G)) \<Longrightarrow> 
                    even(degree x3 (rem_unPath xs G)) \<Longrightarrow> ?case"             
    proof -
      assume parity_x1_x3: "odd (degree x1 (rem_unPath xs G))" 
                           "even (degree x3 (rem_unPath xs G))"
      have "num_of_odd_nodes (rem_unPath (x#xs) G)= num_of_odd_nodes 
         (del_unEdge x1 x2 x3 (rem_unPath xs G))"
        by (metis rem_unPath.simps(2) rem_unPath_com x)
      also have "... =num_of_odd_nodes (rem_unPath xs G)" 
        using  parity_x1_x3  fin_nodes fin_edges valid_rem_xs x_in 
        by (metis del_UnEdge_odd_even)
      also have "...=num_of_odd_nodes G+(if odd(degree x3 G) \<and> x3\<noteq>v' then -2 else 0 )"
        using  Cons.hyps Cons.prems(3) assms(1) assms(2) parity_assms x
        by auto
      also have "...=num_of_odd_nodes G + (- 2)" 
        proof -
          have "odd(degree x3 G) \<and> x3\<noteq>v' \<longleftrightarrow> even (degree x3 (rem_unPath xs G))" 
            using Cons.prems assms
            by (metis  is_trail.simps(2) parity_x1_x3(2) rem_UnPath_parity_v x)
          hence "odd(degree x3 G) \<and> x3\<noteq>v'" by (metis parity_x1_x3(2))
          thus ?thesis by auto
        qed
      also have "...=num_of_odd_nodes G+(if odd(degree v G) \<and> v\<noteq>v' then -2 else 0)" 
         proof -
          have "x1\<noteq>x3" by (metis valid_rem_xs valid_unMultigraph.no_id x_in)
          moreover hence "x1\<noteq>v'" 
            using Cons assms  
            by (metis is_trail.simps(2)  parity_x1_x3(1) rem_UnPath_parity_v' x)
          ultimately have "x1\<notin>{x3,v'}" by auto
          hence  "odd(degree x1 G)" 
            using Cons.prems(3) assms(1) assms(2) parity_x1_x3(1) 
            by (metis (full_types)  is_trail.simps(2) rem_UnPath_parity_others x)
          hence "odd(degree x1 G) \<and> x1\<noteq>v'" using \<open>x1 \<noteq> v'\<close> by auto
          hence "odd(degree v G) \<and> v\<noteq>v'" by (metis Cons.prems(3) is_trail.simps(2) x)
          thus ?thesis by auto
        qed
      finally have "num_of_odd_nodes (rem_unPath (x#xs) G)=
                        num_of_odd_nodes G+(if odd(degree v G) \<and> v\<noteq>v' then -2 else 0)" .
      thus ?thesis .
    qed         
  moreover have "odd (degree x1 (rem_unPath xs G)) \<Longrightarrow> 
                    odd(degree x3 (rem_unPath xs G)) \<Longrightarrow> ?case" 
    proof -
      assume parity_x1_x3: "odd (degree x1 (rem_unPath xs G))" 
                           "odd (degree x3 (rem_unPath xs G))"
      have "num_of_odd_nodes (rem_unPath (x#xs) G)= num_of_odd_nodes 
         (del_unEdge x1 x2 x3 (rem_unPath xs G))"
        by (metis rem_unPath.simps(2) rem_unPath_com x)
      also have "... =num_of_odd_nodes (rem_unPath xs G)-(2::nat)" 
        using del_UnEdge_odd_odd
        by (metis add_implies_diff  fin_edges fin_nodes parity_x1_x3 valid_rem_xs x_in)  
      also have "...=num_of_odd_nodes G -(2::nat)"
        proof -
          have "odd(degree x3 G) \<and> x3\<noteq>v' \<longleftrightarrow> even (degree x3 (rem_unPath xs G))" 
            using Cons.prems assms
            by (metis  is_trail.simps(2) parity_x1_x3(2) rem_UnPath_parity_v x)
          hence "\<not>(odd(degree x3 G) \<and> x3\<noteq>v')" by (metis parity_x1_x3(2))  
          have "num_of_odd_nodes (rem_unPath xs G)= 
                  num_of_odd_nodes G+(if odd(degree x3 G) \<and> x3\<noteq>v' then -2 else 0)" 
            by (metis Cons.hyps Cons.prems(3) assms(1) assms(2) 
                is_trail.simps(2) parity_assms x)
          thus ?thesis 
            using \<open>\<not> (odd (degree x3 G) \<and> x3 \<noteq> v')\<close> by auto 
        qed
      also have "...=num_of_odd_nodes G+(if odd(degree v G) \<and> v\<noteq>v' then -2 else 0)" 
        proof -
          have "x1\<noteq>x3" by (metis valid_rem_xs valid_unMultigraph.no_id x_in)
          moreover hence "x1\<noteq>v'" 
            using Cons assms  
            by (metis is_trail.simps(2)  parity_x1_x3(1) rem_UnPath_parity_v' x)
          ultimately have "x1\<notin>{x3,v'}" by auto
          hence  "odd(degree x1 G)" 
            using Cons.prems(3) assms(1) assms(2) parity_x1_x3(1) 
            by (metis (full_types)  is_trail.simps(2) rem_UnPath_parity_others x)
          hence "odd(degree x1 G) \<and> x1\<noteq>v'" using \<open>x1 \<noteq> v'\<close> by auto
          hence "odd(degree v G) \<and> v\<noteq>v'" by (metis Cons.prems(3) is_trail.simps(2) x)
          hence "v\<in>odd_nodes_set G" 
            using Cons.prems(3) E_validD(1)  x unfolding odd_nodes_set_def
            by auto
          moreover have "v'\<in>odd_nodes_set G" 
            using  is_path_memb[OF is_trail_intro[OF assms(3)]]  parity_assms
            unfolding odd_nodes_set_def 
            by auto
          ultimately have "{v,v'}\<subseteq>odd_nodes_set G" by auto
          moreover have "v\<noteq>v'" by (metis \<open>odd (degree v G) \<and> v \<noteq> v'\<close>)
          hence "card{v,v'}=2" by auto 
          moreover have "finite(odd_nodes_set G)" 
            using \<open>finite V\<close> unfolding odd_nodes_set_def
            by auto
          ultimately have "num_of_odd_nodes G\<ge>2" by (metis card_mono num_of_odd_nodes_def)  
          thus ?thesis using \<open>odd (degree v G) \<and> v \<noteq> v'\<close> by auto
        qed
      finally have "num_of_odd_nodes (rem_unPath (x#xs) G)=
                        num_of_odd_nodes G+(if odd(degree v G) \<and> v\<noteq>v' then -2 else 0)" .
      thus ?thesis .
    qed       
  ultimately show ?case by metis
qed 

lemma (in valid_unMultigraph) rem_UnPath_cycle:
  assumes "finite E" "finite V" "is_trail v ps v'" "v=v'"
  shows "num_of_odd_nodes (rem_unPath ps G) = num_of_odd_nodes G" (is "?L=?R")
proof  (cases "even(degree v' G)")
  case True
  hence "?L = num_of_odd_nodes G + (if even (degree v G)\<and> v\<noteq>v' then 2 else 0)" 
    by (metis assms(1) assms(2) assms(3) rem_UnPath_even)
  with assms show ?thesis by auto  
next
  case False
  hence "?L = num_of_odd_nodes G + (if odd (degree v G)\<and> v\<noteq>v' then -2 else 0)" 
    by (metis assms(1) assms(2) assms(3) rem_UnPath_odd)
  thus ?thesis using \<open>v = v'\<close> by auto   
qed



section\<open>Connectivity\<close>

definition (in valid_unMultigraph) connected::bool where
  "connected \<equiv> \<forall> v\<in>V. \<forall>v'\<in>V. v\<noteq>v' \<longrightarrow> (\<exists>ps. is_path v ps v')"

lemma (in valid_unMultigraph) "connected \<Longrightarrow> \<forall>v\<in>V. \<forall>v'\<in>V. v\<noteq>v'\<longrightarrow>(\<exists>ps. is_trail v ps v')"
proof (rule,rule,rule)
  fix v v'
  assume "v\<in>V" "v'\<in>V" "v\<noteq>v'"
  assume connected
  obtain ps where "is_path v ps v'" by (metis \<open>connected\<close> \<open>v \<in> V\<close> \<open>v' \<in> V\<close> \<open>v\<noteq>v'\<close>  connected_def)
  then obtain ps' where "is_trail v ps' v'"
    proof (induct ps arbitrary:v )
      case Nil
      thus ?case by (metis is_trail.simps(1) is_path.simps(1))
    next
      case (Cons x xs)
      obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
      have "is_path x3 xs v'" by (metis Cons.prems(2) is_path.simps(2) x)
      moreover have "\<And>ps'. is_trail x3 ps' v' \<Longrightarrow> thesis" 
        proof -
          fix ps'
          assume "is_trail x3 ps' v'"
          hence "(x1,x2,x3)\<notin>set ps' \<and> (x3,x2,x1)\<notin>set ps' \<Longrightarrow>is_trail v (x#ps') v'"
            by (metis Cons.prems(2) is_trail.simps(2) is_path.simps(2) x)
          moreover have "(x1,x2,x3)\<in>set ps' \<Longrightarrow> \<exists>ps1. is_trail v ps1 v'" 
            proof -
              assume "(x1,x2,x3)\<in>set ps'"
              then obtain ps1 ps2 where "ps'=ps1@(x1,x2,x3)#ps2" by (metis split_list)
              hence "is_trail v (x#ps2) v'" 
                using \<open>is_trail x3 ps' v'\<close> x
                by (metis Cons.prems(2) is_trail.simps(2) 
                    is_trail_split is_path.simps(2))
              thus ?thesis by rule
            qed
          moreover have "(x3,x2,x1)\<in>set ps' \<Longrightarrow>  \<exists>ps1. is_trail v ps1 v'" 
             proof -
              assume "(x3,x2,x1)\<in>set ps'"
              then obtain ps1 ps2 where "ps'=ps1@(x3,x2,x1)#ps2" by (metis split_list)
              hence "is_trail v ps2 v'" 
                using \<open>is_trail x3 ps' v'\<close> x
                by (metis Cons.prems(2) is_trail.simps(2) 
                    is_trail_split is_path.simps(2))
              thus ?thesis by rule 
            qed
          ultimately show thesis using Cons by auto
        qed
      ultimately show ?case using Cons by auto
    qed
  thus "\<exists>ps. is_trail v ps v'" by rule
qed

lemma (in valid_unMultigraph) no_rep_length: "is_trail v ps v'\<Longrightarrow>length ps=card(set ps)" 
  by (induct ps arbitrary:v, auto)

lemma (in valid_unMultigraph) path_in_edges:"is_trail v ps v' \<Longrightarrow> set ps \<subseteq> E" 
proof (induct ps arbitrary:v)
  case Nil
  show ?case by auto
next
  case (Cons x xs)
  obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
  hence "is_trail x3 xs v'" using Cons by auto
  hence " set xs \<subseteq> E" using Cons by auto
  moreover have "x\<in>E" using Cons by (metis is_trail_intro is_path.simps(2) x)
  ultimately show ?case by auto
qed


lemma (in valid_unMultigraph) trail_bound: 
    assumes "finite E" " is_trail v ps v'"
    shows "length ps \<le>card E" 
by (metis (hide_lams, no_types) assms(1) assms(2) card_mono no_rep_length path_in_edges)

definition (in valid_unMultigraph) exist_path_length:: "'v \<Rightarrow> nat \<Rightarrow>bool" where
  "exist_path_length v l\<equiv>\<exists>v' ps. is_trail v' ps v \<and> length ps=l"   

lemma (in valid_unMultigraph) longest_path:
  assumes "finite E" "n \<in> V"
  shows "\<exists>v. \<exists>max_path. is_trail v max_path n \<and> 
        (\<forall>v'. \<forall>e\<in>E. \<not>is_trail v' (e#max_path) n)"
proof (rule ccontr)
  assume  contro:"\<not> (\<exists>v max_path. is_trail v max_path n 
           \<and> (\<forall>v'. \<forall>e\<in>E. \<not>is_trail v' (e#max_path) n))"
  hence  induct:"(\<forall>v max_path.  is_trail v max_path n 
           \<longrightarrow> (\<exists>v'. \<exists>e\<in>E. is_trail v' (e#max_path) n))" by auto
  have "is_trail n [] n" using \<open>n \<in> V\<close> by auto 
  hence "exist_path_length n 0" unfolding exist_path_length_def by auto
  moreover have "\<forall>y. exist_path_length n y \<longrightarrow> y \<le> card E" 
    using trail_bound[OF \<open>finite E\<close>] unfolding exist_path_length_def 
    by auto
  hence bound:"\<forall>y. exist_path_length n y \<longrightarrow> y \<le> card E" by auto
  ultimately have "exist_path_length n (GREATEST x. exist_path_length n x)"
    using GreatestI_nat by auto
  then obtain v max_path where 
    max_path:"is_trail v max_path n" "length max_path=(GREATEST x. exist_path_length n x)"
    by (metis exist_path_length_def)
  hence "\<exists> v' e. is_trail v' (e#max_path) n" using induct by metis
  hence "exist_path_length n (length max_path +1)" 
    by (metis One_nat_def exist_path_length_def list.size(4))
  hence "length max_path + 1 \<le> (GREATEST x. exist_path_length n x)"
   by (metis Greatest_le_nat bound)
  hence "length max_path + 1 \<le> length max_path" using max_path by auto
  thus False by auto
qed


lemma even_card':
  assumes "even(card A)" "x\<in>A"
  shows "\<exists>y\<in>A. y\<noteq>x" 
proof (rule ccontr)
  assume "\<not> (\<exists>y\<in>A. y \<noteq> x)"
  hence "\<forall>y\<in>A. y=x" by auto
  hence "A={x}" by (metis all_not_in_conv assms(2) insertI2 mk_disjoint_insert)
  hence "card(A)=1" by auto
  thus False using \<open>even(card A)\<close> by auto
qed

lemma odd_card: 
  assumes "finite A" "odd(card A)"
  shows "\<exists>x. x\<in>A" 
by (metis all_not_in_conv assms(2) card_empty even_zero) 

lemma (in valid_unMultigraph) extend_distinct_path: 
  assumes "finite E"  "is_trail v' ps v" 
  assumes parity_assms:"(even (degree v' G)\<and>v'\<noteq>v)\<or>(odd (degree v' G)\<and>v'=v)"
  shows "\<exists>e v1. is_trail v1 (e#ps) v" 
proof -
  have "(even (degree v' G)\<and>v'\<noteq>v) \<Longrightarrow> odd(degree v' (rem_unPath  ps G))" 
    by (metis assms(1) assms(2) rem_UnPath_parity_v)
  moreover have "(odd (degree v' G)\<and>v'=v) \<Longrightarrow> odd(degree v' (rem_unPath  ps G))" 
    by (metis assms(1) assms(2) rem_UnPath_parity_v')
  ultimately have "odd(degree v' (rem_unPath  ps G))" using parity_assms by auto
  hence "odd (card {e. fst e=v' \<and> e\<in>edges G - (set ps \<union> set (rev_path ps))})" 
    using  rem_unPath_edges unfolding degree_def 
    by (metis (lifting, no_types) Collect_cong)
  hence "{e. fst e=v' \<and> e\<in>E - (set ps \<union> set (rev_path ps))}\<noteq>{}" 
    by (metis empty_iff finite.emptyI odd_card)
  then obtain v0 w where v0w:  "(v',w,v0)\<in>E" "(v',w,v0)\<notin>set ps \<union> set (rev_path ps)" by auto
  hence "is_trail v0 ((v0,w,v')#ps) v" 
    by (metis (hide_lams, mono_tags) Un_iff assms(2) corres in_set_rev_path is_trail.simps(2))  
  thus ?thesis by metis
qed

text\<open>replace an edge (or its reverse in a path) by another path (in an undirected graph)\<close>
fun replace_by_UnPath:: "('v,'w) path \<Rightarrow> 'v \<times>'w \<times>'v \<Rightarrow> ('v,'w) path \<Rightarrow>  ('v,'w) path" where
  "replace_by_UnPath [] _ _ = []" |
  "replace_by_UnPath (x#xs) (v,e,v') ps = 
    (if x=(v,e,v') then ps@replace_by_UnPath xs (v,e,v') ps
     else if x=(v',e,v) then (rev_path ps)@replace_by_UnPath xs (v,e,v') ps
     else x#replace_by_UnPath xs (v,e,v') ps)"

lemma (in valid_unMultigraph) del_unEdge_connectivity:
  assumes "connected" "\<exists>ps. valid_graph.is_path (del_unEdge v e v' G) v ps v'"
  shows "valid_unMultigraph.connected (del_unEdge v e v' G)"
proof -
  have valid_unMulti:"valid_unMultigraph (del_unEdge v e v' G)" 
    using valid_unMultigraph_axioms by simp
  have valid_graph: "valid_graph (del_unEdge v e v' G)" 
    using valid_graph_axioms del_undirected by (metis delete_edge_valid)
  obtain ex_path where ex_path:"valid_graph.is_path (del_unEdge v e v' G) v ex_path v'" 
    by (metis assms(2))
  show ?thesis unfolding valid_unMultigraph.connected_def[OF valid_unMulti]
  proof (rule,rule,rule)
    fix n n' 
    assume  n : "n \<in>nodes (del_unEdge v e v' G)" 
    assume  n': "n'\<in>nodes (del_unEdge v e v' G)"
    assume "n\<noteq>n'"
    obtain ps where ps:"is_path n ps n'" 
      by (metis \<open>n\<noteq>n'\<close> n n' \<open>connected\<close> connected_def del_UnEdge_node)
    hence "valid_graph.is_path (del_unEdge v e v' G) 
           n (replace_by_UnPath ps (v,e,v') ex_path) n'" 
      proof (induct ps arbitrary:n)
        case Nil
        thus ?case by (metis is_path.simps(1) n' replace_by_UnPath.simps(1) valid_graph 
          valid_graph.is_path_simps(1))
      next
        case (Cons x xs)
        obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
        have "x=(v,e,v') \<Longrightarrow> ?case" 
          proof -
            assume "x=(v,e,v')"
            hence "valid_graph.is_path (del_unEdge v e v' G) 
                n (replace_by_UnPath (x#xs) (v,e,v') ex_path) n'
                = valid_graph.is_path (del_unEdge v e v' G) 
                n (ex_path@(replace_by_UnPath xs (v,e,v') ex_path)) n'" 
              by (metis replace_by_UnPath.simps(2))
            also have "...=True" 
              by (metis Cons.hyps Cons.prems \<open>x = (v, e, v')\<close> ex_path is_path.simps(2) valid_graph 
                  valid_graph.is_path_split)
            finally show ?thesis by simp
          qed
        moreover have "x=(v',e,v) \<Longrightarrow> ?case" 
          proof -
            assume "x=(v',e,v)"
            hence "valid_graph.is_path (del_unEdge v e v' G) 
                n (replace_by_UnPath (x#xs) (v,e,v') ex_path) n'
                = valid_graph.is_path (del_unEdge v e v' G) 
                n ((rev_path ex_path)@(replace_by_UnPath xs (v,e,v') ex_path)) n'" 
              by (metis Cons.prems is_path.simps(2) no_id replace_by_UnPath.simps(2))
            also have "...=True" 
              by (metis Cons.hyps Cons.prems \<open>x = (v', e, v)\<close> is_path.simps(2) ex_path valid_graph 
                  valid_graph.is_path_split valid_unMulti valid_unMultigraph.is_path_rev)
            finally show ?thesis by simp
          qed
        moreover have "x\<noteq>(v,e,v')\<and>x\<noteq>(v',e,v)\<Longrightarrow>?case" 
          by (metis Cons.hyps Cons.prems del_UnEdge_frame is_path.simps(2) replace_by_UnPath.simps(2) 
              valid_graph valid_graph.is_path.simps(2) x)
        ultimately show ?case by auto
      qed
    thus "\<exists>ps. valid_graph.is_path (del_unEdge v e v' G) n ps n'" by auto
  qed
qed

lemma (in valid_unMultigraph) path_between_odds:
  assumes "odd(degree v G)" "odd(degree v' G)" "finite E"  "v\<noteq>v'" "num_of_odd_nodes G=2"
  shows "\<exists>ps. is_trail v ps v'"
proof -
   have "v\<in>V" 
    proof (rule ccontr)
      assume "v\<notin>V"
      hence "\<forall>e \<in> E. fst e \<noteq> v" by (metis E_valid(1) imageI subsetD)
      hence "degree v G=0" unfolding degree_def using \<open>finite E\<close> 
        by force
      thus False using \<open>odd(degree v G)\<close> by auto
    qed
  have "v'\<in>V" 
    proof (rule ccontr)
      assume "v'\<notin>V"
      hence "\<forall>e \<in> E. fst e \<noteq> v'" by (metis E_valid(1) imageI subsetD)
      hence "degree v' G=0" unfolding degree_def using \<open>finite E\<close> 
        by force
     thus False using \<open>odd(degree v' G)\<close> by auto
    qed
  then obtain max_path v0 where max_path:
      "is_trail  v0 max_path v'" 
      "(\<forall>n. \<forall>w\<in>E. \<not>is_trail n (w#max_path) v')" 
    using longest_path[of v'] by (metis assms(3)) 
  have "even(degree v0 G)\<Longrightarrow>v0=v' \<Longrightarrow> v0=v" 
    by (metis assms(2))
  moreover have "even(degree v0 G)\<Longrightarrow>v0\<noteq>v' \<Longrightarrow> v0=v" 
    proof -
      assume"even(degree v0 G)" "v0\<noteq>v'"
      hence "\<exists>w v1. is_trail 
            v1 (w#max_path) v'" 
        by (metis assms(3) extend_distinct_path max_path(1))
      thus ?thesis by (metis (full_types) is_trail.simps(2) max_path(2) prod.exhaust)
    qed
  moreover have "odd(degree v0 G)\<Longrightarrow>v0=v'\<Longrightarrow>v0=v" 
    proof -
      assume"odd(degree v0 G)" "v0=v'"
      hence "\<exists>w v1. is_trail v1 (w#max_path) v'" 
        by (metis assms(3) extend_distinct_path max_path(1))
      thus ?thesis by (metis (full_types) List.set_simps(2) insert_subset max_path(2) path_in_edges)
    qed
  moreover have "odd(degree v0 G)\<Longrightarrow>v0\<noteq>v'\<Longrightarrow>v0=v"
    proof (rule ccontr)
      assume "v0 \<noteq> v" "odd(degree v0 G)" "v0\<noteq>v'"
      moreover have "v\<in>odd_nodes_set G" 
        using \<open>v \<in> V\<close> \<open> odd (degree v G)\<close> unfolding odd_nodes_set_def
        by auto
      moreover have "v'\<in>odd_nodes_set G" 
        using \<open>v' \<in> V\<close> \<open>odd (degree v' G)\<close>
        unfolding odd_nodes_set_def
        by auto
      ultimately have "{v,v',v0} \<subseteq> odd_nodes_set G" 
        using   is_path_memb[OF is_trail_intro[OF \<open>is_trail v0 max_path v'\<close>]] max_path(1)
        unfolding odd_nodes_set_def
        by auto
      moreover have "card {v,v',v0}=3" using \<open>v0\<noteq>v\<close> \<open>v\<noteq>v'\<close> \<open>v0\<noteq>v'\<close> by auto
      moreover have "finite (odd_nodes_set G)" 
        using assms(5) card_eq_0_iff[of "odd_nodes_set G"] unfolding num_of_odd_nodes_def 
        by auto
      ultimately have "3\<le>card(odd_nodes_set G)" by (metis card_mono)
      thus False using \<open>num_of_odd_nodes G=2\<close> unfolding num_of_odd_nodes_def by auto
    qed
  ultimately have "v0=v" by auto
  thus ?thesis by (metis max_path(1))
qed

lemma (in valid_unMultigraph) del_unEdge_even_connectivity:
  assumes "finite E" "finite V" "connected" "\<forall>n\<in>V. even(degree n G)" "(v,e,v')\<in>E"
  shows "valid_unMultigraph.connected (del_unEdge v e v' G)" 
proof -
  have valid_unMulti:"valid_unMultigraph (del_unEdge v e v' G)" 
    using valid_unMultigraph_axioms by simp
  have valid_graph: "valid_graph (del_unEdge v e v' G)" 
    using valid_graph_axioms del_undirected by (metis delete_edge_valid)
  have fin_E': "finite(edges (del_unEdge v e v' G))" 
    by (metis (hide_lams, no_types) assms(1) del_undirected delete_edge_def 
        finite_Diff select_convs(2))
  have fin_V': "finite(nodes (del_unEdge v e v' G))" 
    by (metis (mono_tags) assms(2) del_undirected delete_edge_def select_convs(1))
  have all_even: "\<forall>n\<in>nodes (del_unEdge v e v' G). n\<notin>{v,v'}
                  \<longrightarrow>even(degree n (del_unEdge v e v' G))"
    by (metis (full_types) assms(1) assms(4) degree_frame del_UnEdge_node)
  have "even (degree v G)" by (metis (full_types) E_validD(1) assms(4) assms(5))
  moreover have "even (degree v' G)" by (metis (full_types) E_validD(2) assms(4) assms(5))
  moreover have "num_of_odd_nodes G = 0" 
    using \<open>\<forall>n\<in>V. even(degree n G)\<close> \<open>finite V\<close>
    unfolding num_of_odd_nodes_def odd_nodes_set_def by auto
  ultimately have "num_of_odd_nodes (del_unEdge v e v' G) = 2" 
    using del_UnEdge_even_even[of G v e v',OF valid_unMultigraph_axioms] 
    by (metis assms(1) assms(2) assms(5) monoid_add_class.add.left_neutral)
  moreover have " odd (degree v (del_unEdge v e v' G))" 
    using \<open>even (degree v G)\<close> del_UnEdge_even[OF \<open>(v,e,v')\<in>E\<close> \<open>finite E\<close>] 
    unfolding odd_nodes_set_def 
    by auto
  moreover have "odd (degree v' (del_unEdge v e v' G))" 
    using \<open>even (degree v' G)\<close> del_UnEdge_even'[OF \<open>(v,e,v')\<in>E\<close> \<open>finite E\<close>] 
    unfolding odd_nodes_set_def 
    by auto  
  moreover have "finite (edges (del_unEdge v e v' G))" 
    using \<open>finite E\<close> by auto
  moreover have "v\<noteq>v'" using no_id \<open>(v,e,v')\<in>E\<close> by auto
  ultimately have "\<exists>ps. valid_unMultigraph.is_trail (del_unEdge v e v' G) v ps v'"
    using valid_unMultigraph.path_between_odds[OF valid_unMulti,of v v']    
    by auto
  thus ?thesis 
    by (metis (full_types) assms(3) del_unEdge_connectivity valid_unMulti 
      valid_unMultigraph.is_trail_intro)
qed


lemma (in valid_graph) path_end:"ps\<noteq>[] \<Longrightarrow> is_path v ps v' \<Longrightarrow> v'=snd (snd(last ps))" 
  by (induct ps arbitrary:v,auto)

lemma (in valid_unMultigraph) connectivity_split:
  assumes "connected" "\<not>valid_unMultigraph.connected (del_unEdge v w v' G)" 
          "(v,w,v')\<in>E"
  obtains G1 G2 where
         "nodes G1={n. \<exists>ps. valid_graph.is_path (del_unEdge v w v' G) n ps v}"
         and "edges G1={(n,e,n'). (n,e,n')\<in>edges (del_unEdge v w v' G) 
            \<and> n\<in>nodes G1 \<and> n'\<in>nodes G1}"
         and "nodes G2={n. \<exists>ps. valid_graph.is_path (del_unEdge v w v' G) n ps v'}"
         and "edges G2={(n,e,n'). (n,e,n')\<in>edges (del_unEdge v w v' G) 
            \<and> n\<in>nodes G2 \<and> n'\<in>nodes G2}" 
         and "edges G1 \<union> edges G2 = edges (del_unEdge v w v' G)" 
         and "edges G1 \<inter> edges G2={}" 
         and "nodes G1 \<union> nodes G2=nodes (del_unEdge v w v' G)"
         and "nodes G1 \<inter> nodes G2={}" 
         and "valid_unMultigraph G1" 
         and "valid_unMultigraph G2"
         and "valid_unMultigraph.connected G1"  
         and "valid_unMultigraph.connected G2"
proof -
  have valid0:"valid_graph (del_unEdge v w v' G)" using valid_graph_axioms 
    by (metis del_undirected delete_edge_valid)
  have valid0':"valid_unMultigraph (del_unEdge v w v' G)" using valid_unMultigraph_axioms 
    by (metis del_unEdge_valid)
  obtain G1_nodes where G1_nodes:"G1_nodes= 
      {n. \<exists>ps. valid_graph.is_path (del_unEdge v w v' G) n ps v}" 
    by metis
  then obtain G1 where G1:"G1=
      \<lparr>nodes=G1_nodes, edges={(n,e,n'). (n,e,n')\<in>edges (del_unEdge v w v' G) 
      \<and> n\<in>G1_nodes \<and> n'\<in>G1_nodes}\<rparr>"
    by metis
  obtain G2_nodes where G2_nodes:"G2_nodes= 
      {n. \<exists>ps. valid_graph.is_path (del_unEdge v w v' G) n ps v'}" 
    by metis
  then obtain G2 where G2:"G2=
      \<lparr>nodes=G2_nodes, edges={(n,e,n'). (n,e,n')\<in>edges (del_unEdge v w v' G) 
      \<and> n\<in>G2_nodes \<and> n'\<in>G2_nodes}\<rparr>"
    by metis 
  have valid_G1:"valid_unMultigraph G1" 
    using G1 valid_unMultigraph.corres[OF valid0'] valid_unMultigraph.no_id[OF valid0']
    by (unfold_locales,auto)
  hence valid_G1':"valid_graph G1" using valid_unMultigraph_def by auto
  have valid_G2:"valid_unMultigraph G2"  
    using G2 valid_unMultigraph.corres[OF valid0'] valid_unMultigraph.no_id[OF valid0'] 
    by (unfold_locales,auto)
  hence valid_G2': "valid_graph G2" using valid_unMultigraph_def by auto
  have "nodes G1={n. \<exists>ps. valid_graph.is_path (del_unEdge v w v' G) n ps v}" 
    using G1_nodes G1 by auto
  moreover have "edges G1={(n,e,n'). (n,e,n')\<in>edges (del_unEdge v w v' G) 
                 \<and> n\<in>nodes G1 \<and> n'\<in>nodes G1}"
    using G1_nodes G1 by auto
  moreover have "nodes G2={n. \<exists>ps. valid_graph.is_path (del_unEdge v w v' G) n ps v'}"
    using G2_nodes G2 by auto
  moreover have "edges G2={(n,e,n'). (n,e,n')\<in>edges (del_unEdge v w v' G) 
                 \<and> n\<in>nodes G2 \<and> n'\<in>nodes G2}"
    using G2_nodes G2 by auto               
  moreover have "nodes G1 \<union> nodes G2=nodes (del_unEdge v w v' G)" 
    proof (rule ccontr)
      assume "nodes G1 \<union> nodes G2 \<noteq> nodes (del_unEdge v w v' G)"
      moreover have "nodes G1 \<subseteq> nodes (del_unEdge v w v' G)"
        using valid_graph.is_path_memb[OF valid0] G1 G1_nodes by auto
      moreover have "nodes G2 \<subseteq> nodes (del_unEdge v w v' G)"
        using valid_graph.is_path_memb[OF valid0] G2 G2_nodes by auto
      ultimately obtain n where n:
          "n\<in>nodes (del_unEdge v w v' G)" "n\<notin>nodes G1" "n\<notin>nodes G2"
        by auto
      hence n_neg_v : "\<not>(\<exists>ps. valid_graph.is_path (del_unEdge v w v' G) n ps v)" and
            n_neg_v': "\<not>(\<exists>ps. valid_graph.is_path (del_unEdge v w v' G) n ps v')"
        using G1 G1_nodes G2 G2_nodes by auto
      hence "n\<noteq>v" by (metis n(1) valid0 valid_graph.is_path_simps(1))
      then obtain nvs where nvs: "is_path n nvs v" using \<open>connected\<close> 
        by (metis E_validD(1) assms(3) connected_def del_UnEdge_node n(1))
      then obtain nvs' where nvs': "nvs'=takeWhile (\<lambda>x. x\<noteq>(v,w,v')\<and>x\<noteq>(v',w,v)) nvs" by auto
      moreover have nvs_nvs':"nvs=nvs'@dropWhile (\<lambda>x. x\<noteq>(v,w,v')\<and>x\<noteq>(v',w,v)) nvs" 
        using nvs' takeWhile_dropWhile_id by auto
      ultimately obtain n' where is_path_nvs': "is_path n nvs' n'"
          and "is_path n' (dropWhile (\<lambda>x. x\<noteq>(v,w,v')\<and>x\<noteq>(v',w,v)) nvs) v"
        using nvs is_path_split[of n nvs' "dropWhile (\<lambda>x. x\<noteq>(v,w,v')\<and>x\<noteq>(v',w,v)) nvs"] by auto
      have "n'=v \<or> n'=v'" 
        proof (cases "dropWhile (\<lambda>x. x\<noteq>(v,w,v')\<and>x\<noteq>(v',w,v)) nvs")
          case Nil
          hence "nvs=nvs'" using nvs_nvs' by (metis append_Nil2)
          hence "n'=v" using  nvs is_path_nvs' path_end by (metis (mono_tags) is_path.simps(1))
          thus ?thesis  by auto
        next
          case (Cons x xs)
          hence "dropWhile (\<lambda>x. x\<noteq>(v,w,v')\<and>x\<noteq>(v',w,v)) nvs\<noteq>[]" by auto
          hence "hd (dropWhile (\<lambda>x. x\<noteq>(v,w,v')\<and>x\<noteq>(v',w,v)) nvs)=(v,w,v')
                 \<or> hd (dropWhile (\<lambda>x. x\<noteq>(v,w,v')\<and>x\<noteq>(v',w,v)) nvs)=(v',w,v)" 
            by (metis (lifting, full_types) hd_dropWhile)
          hence "x=(v,w,v')\<or>x=(v',w,v)" using Cons by auto
          thus ?thesis
            using \<open>is_path n' (dropWhile (\<lambda>x. x \<noteq> (v, w, v') \<and> x \<noteq> (v', w, v)) nvs) v\<close>
            by (metis Cons  is_path.simps(2))
        qed
      moreover have "valid_graph.is_path (del_unEdge v w v' G) n nvs' n'" 
        using is_path_nvs' nvs'
        proof (induct nvs' arbitrary:n nvs)
          case Nil
          thus ?case by (metis del_UnEdge_node is_path.simps(1) valid0 valid_graph.is_path_simps(1))
        next
          case (Cons x xs)
          obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
          hence "is_path x3 xs n'" using Cons by auto
          moreover have "xs = takeWhile (\<lambda>x. x \<noteq> (v, w, v') \<and> x \<noteq> (v', w, v)) (tl nvs)" 
            using \<open>x # xs = takeWhile (\<lambda>x. x \<noteq> (v, w, v') \<and> x \<noteq> (v', w, v)) nvs\<close> 
            by (metis (lifting, no_types) append_Cons list.distinct(1) takeWhile.simps(2) 
                takeWhile_dropWhile_id list.sel(3))
          ultimately have "valid_graph.is_path (del_unEdge v w v' G) x3 xs n'" 
            using Cons by auto
          moreover have "x\<noteq>(v,w,v') \<and> x\<noteq>(v',w,v)" 
            using Cons(3) set_takeWhileD[of x "(\<lambda>x. x \<noteq> (v, w, v') \<and> x \<noteq> (v', w, v))" nvs] 
            by (metis List.set_simps(2) insertI1)
          hence "x\<in>edges (del_unEdge v w v' G)" 
            by (metis Cons.prems(1) del_UnEdge_frame is_path.simps(2) x)
          ultimately show ?case using x 
            by (metis Cons.prems(1) is_path.simps(2) valid0 valid_graph.is_path.simps(2))
        qed
      ultimately show False using n_neg_v n_neg_v' by auto
    qed
  moreover have "nodes G1 \<inter> nodes G2={}" 
    proof (rule ccontr)
      assume "nodes G1 \<inter> nodes G2 \<noteq> {}"
      then obtain n where n:"n\<in>nodes G1" "n\<in>nodes G2" by auto  
      then obtain nvs nv's where 
          nvs  : "valid_graph.is_path (del_unEdge v w v' G) n nvs v" and
          nv's : "valid_graph.is_path (del_unEdge v w v' G) n nv's v'"
        using G1 G2 G1_nodes G2_nodes by auto
      hence "valid_graph.is_path (del_unEdge v w v' G) v ((rev_path nvs)@nv's) v'"
        using valid_unMultigraph.is_path_rev[OF valid0'] valid_graph.is_path_split[OF valid0] 
        by auto 
      hence "valid_unMultigraph.connected (del_unEdge v w v' G)" 
        by (metis assms(1) del_unEdge_connectivity)
      thus False by (metis assms(2))  
    qed
  moreover have "edges G1 \<union> edges G2 = edges (del_unEdge v w v' G)" 
    proof (rule ccontr)
      assume "edges G1 \<union> edges G2 \<noteq> edges (del_unEdge v w v' G)"
      moreover have "edges G1 \<subseteq> edges (del_unEdge v w v' G)" using G1 by auto
      moreover have "edges G2 \<subseteq> edges (del_unEdge v w v' G)" using G2 by auto
      ultimately obtain n e n' where 
          nen':
          "(n,e,n')\<in>edges (del_unEdge v w v' G)" 
          "(n,e,n')\<notin>edges G1" "(n,e,n')\<notin>edges G2" 
        by auto
      moreover have "n\<in>nodes (del_unEdge v w v' G)" 
        by (metis nen'(1) valid0 valid_graph.E_validD(1))
      moreover have "n'\<in>nodes (del_unEdge v w v' G)" 
        by (metis nen'(1) valid0 valid_graph.E_validD(2))
      ultimately have "(n\<in>nodes G1 \<and> n'\<in>nodes G2)\<or>(n\<in>nodes G2\<and>n'\<in>nodes G1)" 
        using G1 G2 \<open>nodes G1 \<union> nodes G2=nodes (del_unEdge v w v' G)\<close> by auto
      moreover have "n\<in>nodes G1 \<Longrightarrow> n'\<in>nodes G2 \<Longrightarrow> False" 
        proof -
          assume "n\<in>nodes G1" "n'\<in>nodes G2"
          then obtain nvs nv's where 
              nvs  : "valid_graph.is_path (del_unEdge v w v' G) n nvs v" and
              nv's : "valid_graph.is_path (del_unEdge v w v' G) n' nv's v'"
            using G1 G2 G1_nodes G2_nodes by auto
          hence "valid_graph.is_path (del_unEdge v w v' G) v 
                  ((rev_path nvs)@(n,e,n')#nv's) v'"
            using valid_unMultigraph.is_path_rev[OF valid0'] valid_graph.is_path_split'[OF valid0]
                  \<open>(n,e,n')\<in>edges (del_unEdge v w v' G)\<close>
            by auto 
          hence "valid_unMultigraph.connected (del_unEdge v w v' G)" 
            by (metis assms(1) del_unEdge_connectivity)
          thus False by (metis assms(2))
        qed
      moreover have "n\<in>nodes G2 \<Longrightarrow> n'\<in>nodes G1 \<Longrightarrow> False" 
        proof -
          assume "n'\<in>nodes G1" "n\<in>nodes G2"
          then obtain n'vs nvs where 
              n'vs  : "valid_graph.is_path (del_unEdge v w v' G) n' n'vs v" and
              nvs : "valid_graph.is_path (del_unEdge v w v' G) n nvs v'"
            using G1 G2 G1_nodes G2_nodes by auto
          moreover have "(n',e,n)\<in>edges (del_unEdge v w v' G)" 
            by (metis nen'(1) valid0' valid_unMultigraph.corres)
          ultimately have "valid_graph.is_path (del_unEdge v w v' G) v 
                  ((rev_path n'vs)@(n',e,n)#nvs) v'"
            using valid_unMultigraph.is_path_rev[OF valid0'] valid_graph.is_path_split'[OF valid0]
            by auto 
          hence "valid_unMultigraph.connected (del_unEdge v w v' G)" 
            by (metis assms(1) del_unEdge_connectivity)
          thus False by (metis assms(2))
        qed
      ultimately show False by auto
    qed
  moreover have "edges G1 \<inter> edges G2={}" 
    proof (rule ccontr)
      assume "edges G1 \<inter> edges G2 \<noteq> {}"
      then obtain n e n' where "(n,e,n')\<in>edges G1" "(n,e,n')\<in>edges G2" by auto
      hence "n\<in>nodes G1" "n\<in>nodes G2" using G1 G2 by auto
      thus False using \<open>nodes G1 \<inter> nodes G2={}\<close> by auto
    qed
  moreover have "valid_unMultigraph.connected G1" 
    unfolding valid_unMultigraph.connected_def[OF valid_G1]
    proof (rule,rule,rule)
      fix n n' 
      assume  n : "n \<in>nodes G1" 
      assume  n': "n'\<in>nodes G1"
      assume "n\<noteq>n'"
      obtain ps where "valid_graph.is_path (del_unEdge v w v' G) n ps v" 
        using G1 G1_nodes n by auto
      hence ps:"valid_graph.is_path G1 n ps v" 
        proof (induct ps arbitrary:n)
          case Nil
          moreover have "v\<in>nodes G1" using G1 G1_nodes valid0 
            by (metis (lifting, no_types) calculation mem_Collect_eq select_convs(1) 
                valid_graph.is_path.simps(1))
          ultimately show ?case 
            by (metis valid0 valid_G1 valid_unMultigraph.is_trail.simps(1)
                 valid_graph.is_path.simps(1)  valid_unMultigraph.is_trail_intro)
        next
          case (Cons x xs)
          obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
          have "x1\<in>nodes G1" using G1 G1_nodes Cons.prems x 
            by (metis (lifting) mem_Collect_eq select_convs(1) valid0 valid_graph.is_path.simps(2))
          moreover have "(x1,x2,x3)\<in>edges (del_unEdge v w v' G)" 
            by (metis Cons.prems valid0 valid_graph.is_path.simps(2) x)
          ultimately have "(x1,x2,x3)\<in>edges G1" 
            using G1 G2 \<open>nodes G1 \<inter> nodes G2={}\<close> \<open>edges G1 \<union> edges G2=edges (del_unEdge v w v' G)\<close>
            by (metis (full_types) IntI Un_iff  bex_empty   valid_G2' valid_graph.E_validD(1) )
          moreover have "valid_graph.is_path (del_unEdge v w v' G) x3 xs v" 
            by (metis Cons.prems valid0 valid_graph.is_path.simps(2) x)
          hence "valid_graph.is_path G1 x3 xs v" using Cons.hyps by auto
          moreover have "x1=n" by (metis Cons.prems valid0 valid_graph.is_path.simps(2) x)
          ultimately show ?case using x valid_G1' by (metis valid_graph.is_path.simps(2))   
        qed
      obtain ps' where "valid_graph.is_path (del_unEdge v w v' G) n' ps' v" 
        using G1 G1_nodes n' by auto
      hence ps':"valid_graph.is_path G1 n' ps' v" 
        proof (induct ps' arbitrary:n')
          case Nil
          moreover have "v\<in>nodes G1" using G1 G1_nodes valid0 
            by (metis (lifting, no_types) calculation mem_Collect_eq select_convs(1) 
                valid_graph.is_path.simps(1))
          ultimately show ?case 
            by (metis valid0 valid_G1 valid_unMultigraph.is_trail.simps(1)
                 valid_graph.is_path.simps(1)  valid_unMultigraph.is_trail_intro)
        next
          case (Cons x xs)
          obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
          have "x1\<in>nodes G1" using G1 G1_nodes Cons.prems x 
            by (metis (lifting) mem_Collect_eq select_convs(1) valid0 valid_graph.is_path.simps(2))
          moreover have "(x1,x2,x3)\<in>edges (del_unEdge v w v' G)" 
            by (metis Cons.prems valid0 valid_graph.is_path.simps(2) x)
          ultimately have "(x1,x2,x3)\<in>edges G1" 
            using G1 G2 \<open>nodes G1 \<inter> nodes G2={}\<close> 
              \<open>edges G1 \<union> edges G2=edges (del_unEdge v w v' G)\<close>
            by (metis (full_types) IntI Un_iff  bex_empty  valid_G2' valid_graph.E_validD(1))
          moreover have "valid_graph.is_path (del_unEdge v w v' G) x3 xs v" 
            by (metis Cons.prems valid0 valid_graph.is_path.simps(2) x)
          hence "valid_graph.is_path G1 x3 xs v" using Cons.hyps by auto
          moreover have "x1=n'" by (metis Cons.prems valid0 valid_graph.is_path.simps(2) x)
          ultimately show ?case using x valid_G1' by (metis valid_graph.is_path.simps(2))   
        qed
      hence "valid_graph.is_path G1 v (rev_path ps') n'" 
        using valid_unMultigraph.is_path_rev[OF valid_G1]
        by auto
      hence "valid_graph.is_path G1 n (ps@(rev_path ps')) n'" 
        using ps valid_graph.is_path_split[OF valid_G1',of n ps "rev_path ps'" n']
        by auto
      thus "\<exists>ps. valid_graph.is_path G1 n ps n'" by auto
    qed
  moreover have "valid_unMultigraph.connected G2" 
    unfolding valid_unMultigraph.connected_def[OF valid_G2]
    proof (rule,rule,rule)
      fix n n' 
      assume  n : "n \<in>nodes G2" 
      assume  n': "n'\<in>nodes G2"
      assume "n\<noteq>n'"
      obtain ps where "valid_graph.is_path (del_unEdge v w v' G) n ps v'" 
        using G2 G2_nodes n by auto
      hence ps:"valid_graph.is_path G2 n ps v'" 
        proof (induct ps arbitrary:n)
          case Nil
          moreover have "v'\<in>nodes G2" using G2 G2_nodes valid0 
            by (metis (lifting, no_types) calculation mem_Collect_eq select_convs(1) 
                valid_graph.is_path.simps(1))
          ultimately show ?case 
            by (metis valid0 valid_G2 valid_unMultigraph.is_trail.simps(1)
                 valid_graph.is_path.simps(1)  valid_unMultigraph.is_trail_intro)
        next
          case (Cons x xs)
          obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
          have "x1\<in>nodes G2" using G2 G2_nodes Cons.prems x 
            by (metis (lifting) mem_Collect_eq select_convs(1) valid0 valid_graph.is_path.simps(2))
          moreover have "(x1,x2,x3)\<in>edges (del_unEdge v w v' G)" 
            by (metis Cons.prems valid0 valid_graph.is_path.simps(2) x)
          ultimately have "(x1,x2,x3)\<in>edges G2" 
            using \<open>nodes G1 \<inter> nodes G2={}\<close> \<open>edges G1 \<union> edges G2=edges (del_unEdge v w v' G)\<close>
            by (metis IntI Un_iff assms(1) bex_empty connected_def del_UnEdge_node valid0 valid0'
              valid_G1' valid_graph.E_validD(1) valid_graph.E_validD(2) valid_unMultigraph.no_id)
          moreover have "valid_graph.is_path (del_unEdge v w v' G) x3 xs v'" 
            by (metis Cons.prems valid0 valid_graph.is_path.simps(2) x)
          hence "valid_graph.is_path G2 x3 xs v'" using Cons.hyps by auto
          moreover have "x1=n" by (metis Cons.prems valid0 valid_graph.is_path.simps(2) x)
          ultimately show ?case using x valid_G2' by (metis valid_graph.is_path.simps(2))   
        qed
      obtain ps' where "valid_graph.is_path (del_unEdge v w v' G) n' ps' v'" 
        using G2 G2_nodes n' by auto
      hence ps':"valid_graph.is_path G2 n' ps' v'" 
        proof (induct ps' arbitrary:n')
          case Nil
          moreover have "v'\<in>nodes G2" using G2 G2_nodes valid0 
            by (metis (lifting, no_types) calculation mem_Collect_eq select_convs(1) 
                valid_graph.is_path.simps(1))
          ultimately show ?case 
            by (metis valid0 valid_G2 valid_unMultigraph.is_trail.simps(1)
                 valid_graph.is_path.simps(1)  valid_unMultigraph.is_trail_intro)
        next
          case (Cons x xs)
          obtain x1 x2 x3 where x:"x=(x1,x2,x3)" by (metis prod_cases3)
          have "x1\<in>nodes G2" using G2 G2_nodes Cons.prems x 
            by (metis (lifting) mem_Collect_eq select_convs(1) valid0 valid_graph.is_path.simps(2))
          moreover have "(x1,x2,x3)\<in>edges (del_unEdge v w v' G)" 
            by (metis Cons.prems valid0 valid_graph.is_path.simps(2) x)
          ultimately have "(x1,x2,x3)\<in>edges G2" 
            using  \<open>nodes G1 \<inter> nodes G2={}\<close> \<open>edges G1 \<union> edges G2=edges (del_unEdge v w v' G)\<close>
            by (metis IntI Un_iff assms(1) bex_empty connected_def del_UnEdge_node valid0 valid0' 
              valid_G1' valid_graph.E_validD(1) valid_graph.E_validD(2) valid_unMultigraph.no_id)
          moreover have "valid_graph.is_path (del_unEdge v w v' G) x3 xs v'" 
            by (metis Cons.prems valid0 valid_graph.is_path.simps(2) x)
          hence "valid_graph.is_path G2 x3 xs v'" using Cons.hyps by auto
          moreover have "x1=n'" by (metis Cons.prems valid0 valid_graph.is_path.simps(2) x)
          ultimately show ?case using x valid_G2' by (metis valid_graph.is_path.simps(2))   
        qed
      hence "valid_graph.is_path G2 v' (rev_path ps') n'" 
        using valid_unMultigraph.is_path_rev[OF valid_G2]
        by auto
      hence "valid_graph.is_path G2 n (ps@(rev_path ps')) n'" 
        using ps valid_graph.is_path_split[OF valid_G2',of n ps "rev_path ps'" n']
        by auto
      thus "\<exists>ps. valid_graph.is_path G2 n ps n'" by auto
    qed
  ultimately show ?thesis using valid_G1 valid_G2 that by auto
qed


lemma sub_graph_degree_frame:
  assumes "valid_graph G2" "edges G1 \<union> edges G2 =edges G" "nodes G1 \<inter> nodes G2={}" "n\<in>nodes G1"
  shows "degree n G=degree n G1"
proof -
  have "{e \<in> edges G. fst e = n}\<subseteq>{e \<in> edges G1. fst e = n}" 
    proof 
      fix e assume  "e \<in> {e \<in> edges G. fst e = n}"
      hence "e\<in>edges G" "fst e=n" by auto
      moreover have "n\<notin>nodes G2" 
        using \<open>nodes G1 \<inter> nodes G2={}\<close> \<open>n\<in>nodes G1\<close>
        by auto
      hence "e\<notin>edges G2" using valid_graph.E_validD[OF \<open>valid_graph G2\<close>] \<open>fst e=n\<close> 
        by (metis prod.exhaust fst_conv)  
      ultimately have "e\<in>edges G1" using \<open>edges G1 \<union> edges G2 =edges G\<close> by auto
      thus "e \<in> {e \<in> edges G1. fst e = n}" using \<open>fst e=n\<close> by auto
    qed
  moreover have "{e \<in> edges G1. fst e = n}\<subseteq>{e \<in> edges G. fst e = n}" 
    by (metis (lifting) Collect_mono Un_iff assms(2))
  ultimately show ?thesis unfolding degree_def by auto
qed
      
lemma odd_nodes_no_edge[simp]: "finite (nodes g) \<Longrightarrow> num_of_odd_nodes (g \<lparr>edges:={} \<rparr>) = 0" 
  unfolding  num_of_odd_nodes_def odd_nodes_set_def degree_def by simp

section \<open>Adjacent nodes\<close>
  
definition (in valid_unMultigraph) adjacent:: "'v \<Rightarrow> 'v \<Rightarrow> bool" where
    "adjacent v v' \<equiv> \<exists>w. (v,w,v')\<in>E"
    
lemma (in valid_unMultigraph) adjacent_sym: "adjacent v v' \<longleftrightarrow> adjacent v' v" 
    unfolding adjacent_def by auto
  
lemma (in valid_unMultigraph) adjacent_no_loop[simp]: "adjacent v v' \<Longrightarrow> v \<noteq>v'"
     unfolding adjacent_def by auto

lemma (in valid_unMultigraph) adjacent_V[simp]: 
    assumes "adjacent v v'"
    shows "v\<in>V" "v'\<in>V"
  using assms E_validD unfolding adjacent_def by auto


lemma (in valid_unMultigraph) adjacent_finite:
  "finite E \<Longrightarrow> finite {n. adjacent v n}"
proof -
  assume "finite E"
  { fix S v 
    have "finite S \<Longrightarrow> finite {n. \<exists>w. (v,w,n)\<in>S}" 
      proof (induct S rule: finite_induct)
        case empty
        thus ?case by auto
      next
        case (insert x F)
        obtain x1 x2 x3 where x: "x=(x1,x2,x3)" by (metis prod_cases3)
        have "x1=v \<Longrightarrow> ?case"
          proof -
            assume "x1=v"
            hence "{n. \<exists>w. (v, w, n) \<in> insert x F}=insert x3 {n. \<exists>w. (v, w, n) \<in> F}"
              using x by auto
            thus ?thesis using insert by auto
          qed
        moreover have "x1\<noteq>v \<Longrightarrow> ?case"
          proof -
            assume "x1\<noteq>v"
            hence "{n. \<exists>w. (v, w, n) \<in> insert x F}={n. \<exists>w. (v, w, n) \<in> F}" using x by auto
            thus ?thesis using insert by auto
          qed
        ultimately show ?case by auto
      qed }
  note aux=this
  show ?thesis using aux[OF \<open>finite E\<close>, of v]  unfolding adjacent_def by auto
qed

section\<open>Undirected simple graph\<close>

locale valid_unSimpGraph=valid_unMultigraph G for G::"('v,'w) graph"+
              assumes no_multi[simp]: "(v,w,u) \<in> edges G \<Longrightarrow> (v,w',u) \<in>edges G \<Longrightarrow> w = w'"

lemma (in valid_unSimpGraph) finV_to_finE[simp]: 
  assumes "finite V" 
  shows "finite E"
proof (cases "{(v1,v2). adjacent v1 v2}={}")
  case True
  hence "E={}" unfolding adjacent_def by auto
  thus "finite E" by auto
next
  case False
  have "{(v1,v2). adjacent v1 v2} \<subseteq> V \<times> V" using adjacent_V by auto
  moreover have "finite (V \<times> V)" using \<open>finite V\<close> by auto
  ultimately have "finite {(v1,v2). adjacent v1 v2}" using finite_subset by auto
  hence "card {(v1,v2). adjacent v1 v2}\<noteq>0" using False card_eq_0_iff by auto
  moreover have "card E=card {(v1,v2). adjacent v1 v2}" 
    proof -
      have "(\<lambda>(v1,w,v2). (v1,v2))`E = {(v1,v2). adjacent v1 v2}" 
        proof -
          have "\<And>x. x\<in>(\<lambda>(v1,w,v2). (v1,v2))`E \<Longrightarrow> x\<in> {(v1,v2). adjacent v1 v2}" 
            unfolding adjacent_def by auto
          moreover have "\<And>x. x\<in>{(v1,v2). adjacent v1 v2} \<Longrightarrow> x\<in>(\<lambda>(v1,w,v2). (v1,v2))`E" 
            unfolding adjacent_def by force
          ultimately show ?thesis by force
        qed
      moreover have "inj_on (\<lambda>(v1,w,v2). (v1,v2)) E" unfolding inj_on_def by auto
      ultimately show ?thesis by (metis card_image)
    qed
  ultimately show "finite E" by (metis card_infinite)
qed


lemma del_unEdge_valid'[simp]:"valid_unSimpGraph G\<Longrightarrow>
    valid_unSimpGraph (del_unEdge v w u G)" 
proof -
  assume "valid_unSimpGraph G"
  hence "valid_unMultigraph (del_unEdge v w u G)" 
    using valid_unSimpGraph_def[of G] del_unEdge_valid[of G] by auto
  moreover have "valid_unSimpGraph_axioms (del_unEdge v w u G)"
    using valid_unSimpGraph.no_multi[OF \<open>valid_unSimpGraph G\<close>]
    unfolding valid_unSimpGraph_axioms_def del_unEdge_def by auto
  ultimately show "valid_unSimpGraph (del_unEdge v w u G)" using valid_unSimpGraph_def
    by auto
qed

lemma (in valid_unSimpGraph) del_UnEdge_non_adj: 
    "(v,w,u)\<in>E \<Longrightarrow> \<not>valid_unMultigraph.adjacent (del_unEdge v w u G) v u"
proof
  assume "(v, w, u) \<in> E" 
      and ccontr:"valid_unMultigraph.adjacent (del_unEdge v w u G) v u"
  have valid:"valid_unMultigraph (del_unEdge v w u G)" 
    using valid_unMultigraph_axioms by auto
  then obtain w' where vw'u:"(v,w',u)\<in>edges (del_unEdge v w u G)"
    using ccontr unfolding valid_unMultigraph.adjacent_def[OF valid] by auto
  hence "(v,w',u)\<notin>{(v,w,u),(u,w,v)}" unfolding del_unEdge_def by auto
  hence "w'\<noteq>w" by auto
  moreover have "(v,w',u)\<in>E" using vw'u unfolding del_unEdge_def by auto
  ultimately show False using no_multi[of v w u w'] \<open>(v, w, u) \<in> E\<close> by auto
qed

lemma (in valid_unSimpGraph) degree_adjacent: "finite E \<Longrightarrow> degree v G=card {n. adjacent v n}"
  using valid_unSimpGraph_axioms 
proof (induct "degree v G" arbitrary: G)
  case 0
  note valid3=\<open>valid_unSimpGraph G\<close>
  hence valid2: "valid_unMultigraph G" using valid_unSimpGraph_def by auto
  have "{a. valid_unMultigraph.adjacent G v a}={}" 
    proof (rule ccontr)
      assume "{a. valid_unMultigraph.adjacent G v a} \<noteq> {}"
      then obtain w u where "(v,w,u)\<in>edges G" 
        unfolding valid_unMultigraph.adjacent_def[OF valid2] by auto
      hence "degree v G\<noteq>0" using \<open>finite (edges G)\<close> unfolding degree_def by auto
      thus False using \<open>0 = degree v G\<close> by auto
    qed
  thus ?case by (metis "0.hyps" card_empty)
next
  case (Suc n)
  hence "{e \<in> edges G. fst e = v}\<noteq>{}" using card_empty unfolding degree_def  by force
  then obtain w u where "(v,w,u)\<in>edges G" by auto
  have valid:"valid_unMultigraph G" using \<open>valid_unSimpGraph G\<close> valid_unSimpGraph_def by auto
  hence valid':"valid_unMultigraph (del_unEdge v w u G)" by auto
  have "valid_unSimpGraph (del_unEdge v w u G)" 
    using del_unEdge_valid' \<open>valid_unSimpGraph G\<close> by auto
  moreover have "n = degree v (del_unEdge v w u G)" 
    using \<open>Suc n = degree v G\<close>\<open>(v, w, u) \<in> edges G\<close>  del_edge_undirected_degree_plus[of G v w u]
    by (metis Suc.prems(1) Suc_eq_plus1 diff_Suc_1 valid valid_unMultigraph.corres)
  moreover have "finite (edges (del_unEdge v w u G))" 
    using \<open>finite (edges G)\<close> unfolding del_unEdge_def
    by auto
  ultimately have "degree v (del_unEdge v w u G) 
      = card (Collect (valid_unMultigraph.adjacent (del_unEdge v w u G) v))"
    using Suc.hyps  by auto
  moreover have "Suc(card ({n. valid_unMultigraph.adjacent (del_unEdge v w u G)  
      v n})) = card ({n. valid_unMultigraph.adjacent G v n})" 
    using valid_unMultigraph.adjacent_def[OF valid'] 
    proof -
      have "{n. valid_unMultigraph.adjacent (del_unEdge v w u G) v n} \<subseteq> 
          {n. valid_unMultigraph.adjacent G v n}"
        using del_unEdge_def[of v w u G]
        unfolding valid_unMultigraph.adjacent_def[OF valid'] 
          valid_unMultigraph.adjacent_def[OF valid]
        by auto
      moreover have "u\<in>{n. valid_unMultigraph.adjacent G v n}" 
        using \<open>(v,w,u)\<in>edges G\<close> unfolding valid_unMultigraph.adjacent_def[OF valid] by auto
      ultimately have "{n. valid_unMultigraph.adjacent (del_unEdge v w u G) v n} \<union> {u}
          \<subseteq> {n. valid_unMultigraph.adjacent G v n}" by auto
      moreover have "{n. valid_unMultigraph.adjacent G v n} - {u}
          \<subseteq> {n. valid_unMultigraph.adjacent (del_unEdge v w u G) v n}"
        using del_unEdge_def[of v w u G]
        unfolding valid_unMultigraph.adjacent_def[OF valid'] 
          valid_unMultigraph.adjacent_def[OF valid]
        by auto
      ultimately have "{n. valid_unMultigraph.adjacent (del_unEdge v w u G) v n} \<union> {u}
          = {n. valid_unMultigraph.adjacent G v n}" by auto
      moreover have "u\<notin>{n. valid_unMultigraph.adjacent (del_unEdge v w u G) v n}" 
        using valid_unSimpGraph.del_UnEdge_non_adj[OF \<open>valid_unSimpGraph G\<close> \<open>(v,w,u)\<in>edges G\<close>]
        by auto
      moreover have "finite {n. valid_unMultigraph.adjacent G v n}" 
        using valid_unMultigraph.adjacent_finite[OF valid \<open>finite (edges G)\<close>] by simp 
      ultimately show ?thesis 
        by (metis Un_insert_right card_insert_disjoint finite_Un sup_bot_right)
    qed
  ultimately show ?case by (metis Suc.hyps(2) \<open>n = degree v (del_unEdge v w u G)\<close>)
qed 
  
end
