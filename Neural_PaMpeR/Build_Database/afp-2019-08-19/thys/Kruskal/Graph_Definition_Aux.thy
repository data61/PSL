subsection "Auxiliary lemmas for graphs"

theory Graph_Definition_Aux
imports Graph_Definition SeprefUF
begin

context valid_graph
begin

lemma  nodes_connected_sym: "nodes_connected G a b = nodes_connected G b a"
  using is_path_undir_sym by auto

lemma  Domain_nodes_connected: "Domain {(x, y) |x y. nodes_connected G x y} = V"
  apply auto subgoal for x apply(rule exI[where x=x]) apply(rule exI[where x="[]"]) by auto
  done
lemma  Range_nodes_connected: "Range {(x, y) |x y. nodes_connected G x y} = V"
  apply auto subgoal for x apply(rule exI[where x=x]) apply(rule exI[where x="[]"]) by auto
  done

\<comment> \<open>adaptation of a proof by Julian Biendarra\<close>
lemma   nodes_connected_insert_per_union:
  "(nodes_connected (add_edge a w b H) x y) \<longleftrightarrow> (x,y) \<in> per_union {(x,y)| x y. nodes_connected H x y} a b"
  if  "subgraph H G" and PER: "part_equiv {(x,y)| x y. nodes_connected H x y}"
    and V: "a\<in>V" "b\<in>V" for x y
proof -
  let ?uf = "{(x,y)| x y. nodes_connected H x y}"
  from valid_subgraph[OF \<open>subgraph H G\<close>]
  have valid_H: "valid_graph H" .
  from \<open>subgraph H G\<close>
  have nodes_H: "nodes H = V"
    unfolding subgraph_def ..
  with \<open>a\<in>V\<close> \<open>b\<in>V\<close>
  have nodes_add_H: "nodes (add_edge a w b H) = nodes H"
    by auto
  have "Domain ?uf = nodes H" using valid_graph.Domain_nodes_connected[OF valid_H] .
  show ?thesis
  proof 
    assume "nodes_connected (add_edge a w b H) x y"
    then obtain p where p: "is_path_undir (add_edge a w b H) x p y"
      by blast
    from \<open>a\<in>V\<close> \<open>b\<in>V\<close> \<open>Domain {(x,y)| x y. nodes_connected H x y} = nodes H\<close> nodes_H
    have [simp]: "a\<in>Domain (per_union ?uf a b)" "b\<in>Domain (per_union ?uf a b)"
      by auto
    from PER have PER': "part_equiv (per_union ?uf a b)"
      by (auto simp: union_part_equivp)
    show "(x,y) \<in> per_union ?uf a b"
    proof (cases "(a, w, b) \<in> set p \<or> (b, w, a) \<in> set p")
      case True
      from valid_graph.is_path_undir_split_distinct[OF add_edge_valid[OF valid_H] p True]
      obtain p' p'' u u' where
        "is_path_undir (add_edge a w b H) x p' u \<and>
        is_path_undir (add_edge a w b H) u' p'' y" and
        u: "u\<in>{a,b} \<and> u'\<in>{a,b}" and
        "(a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p' \<and>
        (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p''"
        by auto
      with \<open>a\<in>V\<close> \<open>b\<in>V\<close> \<open>Domain ?uf = nodes H\<close> \<open>subgraph H G\<close>
        valid_graph.add_edge_was_path[OF valid_H]
      have "is_path_undir H x p' u \<and> is_path_undir H u' p'' y"
        unfolding subgraph_def by auto
      with V  u nodes_H have comps: "(x,u) \<in> ?uf \<and> (u', y) \<in> ?uf" by auto
      from comps  have "(x,u) \<in> per_union ?uf a b" apply(intro per_union_impl)
        by auto
      also from u \<open>a\<in>V\<close> \<open>b\<in>V\<close> \<open>Domain ?uf = nodes H\<close> nodes_H
        part_equiv_refl'[OF PER' \<open>a\<in>Domain (per_union ?uf a b)\<close>]
        part_equiv_refl'[OF PER' \<open>b\<in>Domain (per_union ?uf a b)\<close>] part_equiv_sym[OF PER']
        per_union_related[OF PER]
      have "(u,u') \<in> per_union ?uf a b"
        by auto
      also (part_equiv_trans[OF PER']) from comps 
      have "(u',y) \<in> per_union ?uf a b" apply(intro per_union_impl)
        by auto
      finally (part_equiv_trans[OF PER']) show ?thesis by simp
    next
      case False
      with \<open>a\<in>V\<close> \<open>b\<in>V\<close> nodes_H valid_graph.add_edge_was_path[OF valid_H p(1)]
      have "is_path_undir H x p y"
        by auto
      with     nodes_add_H have "(x,y)\<in>?uf" by auto
      from per_union_impl[OF this] show ?thesis .
    qed
  next
    assume asm: "(x, y) \<in> per_union ?uf a b"
    show "nodes_connected (add_edge a w b H) x y"
      proof (cases "(x, y) \<in> ?uf")
        case True
        with nodes_add_H have "nodes_connected H x y" 
          by auto
        with valid_graph.add_edge_is_path[OF valid_H] show ?thesis
          by blast
      next
        case False
        with asm part_equiv_sym[OF PER]
        have "(x,a) \<in> ?uf \<and> (b,y) \<in> ?uf \<or>
              (x,b) \<in> ?uf \<and> (a,y) \<in> ?uf"
          unfolding per_union_def
          by auto
        with  \<open>a\<in>V\<close> \<open>b\<in>V\<close> nodes_H nodes_add_H obtain p q p' q'
          where "is_path_undir H x p a \<and> is_path_undir H b q y \<or>
                 is_path_undir H x p' b \<and> is_path_undir H a q' y" 
          by fastforce
        with valid_graph.add_edge_is_path[OF valid_H]
        have "is_path_undir (add_edge a w b H) x p a \<and>
              is_path_undir (add_edge a w b H) b q y \<or>
              is_path_undir (add_edge a w b H) x p' b \<and>
              is_path_undir (add_edge a w b H) a q' y"
          by blast
        with valid_graph.is_path_undir_split'[OF add_edge_valid[OF valid_H]]
        have "is_path_undir (add_edge a w b H) x (p @ (a, w, b) # q) y \<or>
              is_path_undir (add_edge a w b H) x (p' @ (b, w, a) # q') y"
          by auto
        with valid_graph.is_path_undir_sym[OF add_edge_valid[OF valid_H]]
        show ?thesis
          by blast
      qed
    qed
  qed


lemma  is_path_undir_append: "is_path_undir G v p1 u \<Longrightarrow> is_path_undir G u p2 w
      \<Longrightarrow> is_path_undir G v (p1@p2) w"
  using is_path_undir_split by auto


lemma 
  augment_edge:
  assumes sg: "subgraph G1 G" "subgraph G2 G" and
    p: "(u, v) \<in> {(a, b) |a b. nodes_connected G1 a b}"
  and notinE2:  "(u, v) \<notin> {(a, b) |a b. nodes_connected G2 a b}"

shows "\<exists>a b e. (a, b) \<notin> {(a, b) |a b. nodes_connected G2 a b} \<and> e \<notin> edges G2 \<and> e \<in> edges G1 \<and> (case e of (aa, w, ba) \<Rightarrow> a=aa \<and> b=ba \<or> a=ba \<and> b=aa)"
proof -
  from sg have [simp]: "nodes G1 = nodes G" "nodes G2 = nodes G" unfolding subgraph_def by auto
  from p obtain p where a: "is_path_undir G1 u p v" by blast
  from notinE2 have b: "~(\<exists>p. is_path_undir G2 u p v)" by auto
  from a b show ?thesis
  proof (induct p arbitrary: u)
    case Nil 
    then have "u=v" "u\<in>nodes G1" by auto  
    then have "is_path_undir G2 u [] v" by auto
    have "(u, v) \<in> {(a, b) |a b. nodes_connected G2 a b}"  
      apply auto
      apply(rule exI[where x="[]"]) by fact
    with Nil(2) show ?case by blast
next
  case (Cons a p)
  from Cons(2) obtain w x y u' where axy: "a=(u,w,u')" and 2: "(x=u \<and> y=u') \<or> (x=u' \<and> y=u)" and e': "is_path_undir G1 u' p v"
      and uwE1: "(x,w,y) \<in> edges G1" apply(cases a) by auto  
  show ?case
  proof (cases "(x,w,y)\<in>edges G2 \<or> (y,w,x)\<in>edges G2")
    case True
    have e2': "~(\<exists>p. is_path_undir G2 u' p v)"
    proof (rule ccontr, clarsimp)
      fix p2
      assume "is_path_undir G2 u' p2 v"
      with True axy 2 have "is_path_undir G2 u (a#p2) v" by auto
      with Cons(3) show False by blast
    qed 
    from Cons(1)[OF e' e2'] show ?thesis .
  next
    case False
    {
      assume e2': "~(\<exists>p. is_path_undir G2 u' p v)"
      from Cons(1)[OF e' e2'] have ?thesis .
    } moreover {
      assume e2': "\<exists>p. is_path_undir G2 u' p v"
      then obtain p1 where p1: "is_path_undir G2 u' p1 v" by auto  

      from False axy have "(x, w, y)\<notin>edges G2" by auto
      moreover
      have "(u,u') \<notin> {(a, b) |a b. nodes_connected G2 a b}"
      proof(rule ccontr, auto simp add:  )
        fix p2 
        assume "is_path_undir G2 u p2 u'"
        with p1 have "is_path_undir G2 u (p2@p1) v"
          using valid_graph.is_path_undir_append[OF valid_subgraph[OF assms(2)]]
          by auto
        then show "False" using Cons(3) by blast
      qed
      moreover
      note uwE1   
      ultimately have ?thesis 
        apply -
        apply(rule exI[where x="u"])
        apply(rule exI[where x="u'"])
        apply(rule exI[where x="(x,w,y)"])
        using 2 by fastforce
    }
    ultimately show ?thesis by auto
  qed
qed
qed

lemma  nodes_connected_refl: "a\<in>V \<Longrightarrow> nodes_connected G a a" 
  apply(rule exI[where x="[]"]) by auto  


lemma assumes sg: "subgraph H G"
  shows connected_VV: "{(x, y) |x y. nodes_connected H x y} \<subseteq> V\<times>V"
    and connected_refl: "refl_on V {(x, y) |x y. nodes_connected H x y}"
    and connected_trans: "trans {(x, y) |x y. nodes_connected H x y}"
    and connected_sym: "sym {(x, y) |x y. nodes_connected H x y}"
    and connected_equiv: "equiv V {(x, y) |x y. nodes_connected H x y}"
proof -  
  have *: "\<And>R S. Domain R \<subseteq> S \<Longrightarrow> Range R \<subseteq> S \<Longrightarrow> R \<subseteq> S\<times>S" by auto 
  from sg have [simp]: "nodes H = V" by (auto simp: subgraph_def)
  from sg valid_subgraph have v: "valid_graph H"  by auto

  from valid_graph.Domain_nodes_connected[OF this] valid_graph.Range_nodes_connected[OF this]
  show i: "{(x, y) |x y. nodes_connected H x y} \<subseteq> V\<times>V" apply(intro *) by auto 

  have ii: "\<And>x. x \<in> V \<Longrightarrow> (x, x) \<in> {(x, y) |x y. nodes_connected H x y}"
    using valid_graph.nodes_connected_refl[OF v] by auto 
  show "refl_on V {(x, y) |x y. nodes_connected H x y}"
    apply(rule refl_onI) by fact+

  from valid_graph.is_path_undir_append[OF v]
  show "trans {(x, y) |x y. nodes_connected H x y}" unfolding trans_def by fast

  from valid_graph.nodes_connected_sym[OF v]
  show "sym {(x, y) |x y. nodes_connected H x y}" unfolding sym_def by fast

  show "equiv V {(x, y) |x y. nodes_connected H x y}" apply (rule equivI) by fact+
qed

lemma  forest_maximally_connected_incl_max1:
  assumes
    "forest H"
    "subgraph H G"                                                                
  shows "(\<forall>(a,w,b)\<in>edges G - edges H. \<not> (forest (add_edge a w b H))) \<Longrightarrow> maximally_connected H G" 
proof -

  from assms(2) have V[simp]: "nodes H = nodes G" unfolding subgraph_def by auto

  assume pff: "(\<forall>(a,w,b)\<in>E - edges H. \<not> (forest (add_edge a w b H)))"
  { fix u v
    assume uv: "v\<in>V" "u\<in>V" 
    assume "nodes_connected G u v"
    then have i: "(u, v) \<in> {(a, b) |a b. nodes_connected G a b}" by auto    

    have "nodes_connected H u v"
    proof (rule ccontr)
      assume "\<not>nodes_connected H u v"
      then have ii: "(u, v) \<notin> {(a, b) |a b. nodes_connected H a b}" by auto
      have "subgraph G G" by(auto simp: subgraph_def)
      from augment_edge[OF this assms(2) i ii] obtain e a b where
         k: "(a, b) \<notin> {(a, b) |a b. nodes_connected H a b}"
        and nn: "e \<notin> edges H" "e \<in> E" and ee: "(case e of (aa, w, ba) \<Rightarrow> a=aa \<and> b=ba \<or> a=ba \<and> b=aa) "
        by blast
      obtain x w y where e: "e=(x,w,y)" apply(cases e) by auto
      from e ee have "x=a \<and> y=b \<or> x=b \<and> y=a" by auto 
      with k have k': "\<not> nodes_connected H x y"
        using valid_graph.nodes_connected_sym[OF valid_subgraph[OF assms(2)]] by auto
      have xy: "x\<in>V" "y\<in>V" using e nn(2) by (auto dest: E_validD) 
      then have nxy: "x\<in>nodes H"  "y\<in>nodes H" by auto
      from forest.forest_add_edge[OF assms(1) nxy k' ]  have
        "forest (add_edge x w y H)" .
      moreover have "(x,w,y)\<in>E-edges H" using nn e by auto
      ultimately show "False" using pff by blast
    qed       
  }
  then show "maximally_connected H G"
    unfolding maximally_connected_def by auto
qed

lemma   forest_maximally_connected_incl_max2:
  assumes
    "forest H"
    "subgraph H G"
  shows "maximally_connected H G \<Longrightarrow> (\<forall>(a,w,b)\<in>E - edges H. \<not> (forest (add_edge a w b H)))" 
proof -
  from assms(2) have V[simp]: "nodes H = nodes G" unfolding subgraph_def by auto

  assume mc: "maximally_connected H G"
  then have k: "\<And>v v'. v\<in>V \<Longrightarrow>  v'\<in>V \<Longrightarrow> 
          nodes_connected G v v' \<Longrightarrow> nodes_connected H v v'" 
    unfolding maximally_connected_def by auto

  show "(\<forall>(a,w,b)\<in>E - edges H. \<not> (forest (add_edge a w b H)))"
  proof (safe)
    fix x w y
    assume i: "(x, w, y) \<in> E" and ni: "(x, w, y) \<notin> edges H"
      and f: "forest (add_edge x w y H)"
    from i have xy: "x\<in>V" "y\<in>V" by (auto dest: E_validD)
    from f have "\<forall>(a,wa,b)\<in>insert (x, w, y) (edges H). \<not> nodes_connected (delete_edge a wa b (add_edge x w y H)) a b"
      unfolding forest_def forest_axioms_def by auto
    then have "\<not> nodes_connected (delete_edge x w y (add_edge x w y H)) x y"
      by auto
    moreover have "(delete_edge x w y (add_edge x w y H)) = H" 
      using ni xy by(auto simp: add_edge_def delete_edge_def insert_absorb)
    ultimately have "\<not> nodes_connected H x y" by auto
    moreover from i have "nodes_connected G x y" apply - apply(rule exI[where x="[(x,w,y)]"])
      by (auto dest: E_validD) 
    ultimately   show "False" using k[OF xy] by simp
  qed
qed

lemma  forest_maximally_connected_incl_max_conv:
  assumes
    "forest H"
    "subgraph H G"
  shows "maximally_connected H G = (\<forall>(a,w,b)\<in>E - edges H. \<not> (forest (add_edge a w b H)))" 
  using assms forest_maximally_connected_incl_max2 forest_maximally_connected_incl_max1 by blast


end


end