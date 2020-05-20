section\<open>Attic\<close>
theory attic
imports Main "Lib/FiniteGraph"
begin

text\<open>old lemma, mainly unused.\<close>

lemma exists_x1x2_x1notoffending_natLeq: 
  fixes 
    G::"'v graph" and
    f and
    p::"'v \<Rightarrow> nat"
  assumes
    "wf_graph G"
    "\<exists>(e1, e2)\<in>(edges G). \<not> (p e1 \<le> p e2)" and
    "f \<subseteq> edges G \<and> (\<forall>(e1, e2)\<in>f. \<not> p e1 \<le> p e2)" and
    "\<forall>(e1, e2)\<in>(edges G) - f. p e1 \<le> p e2"
  shows "\<exists> x1 x2. (x1,x2)\<in>(edges G) \<and> (x1,x2)\<in> f \<and> x1 \<in> fst ` f \<and> x1 \<notin> snd ` f \<and> ((p x1) = Max (p`fst` f))"
proof -
   from assms have a2: "\<exists>x\<in>(edges G). \<not> (case x of (e1, e2) \<Rightarrow> p e1 \<le> p e2)" by auto
   from assms have a3: "f \<subseteq>(edges G) \<and> (\<forall>(e1, e2)\<in>f. \<not> p e1 \<le> p e2)" by simp
   from assms have a4: "\<forall>(e1, e2)\<in>(edges G) - f. p e1 \<le> p e2" by simp
   from assms(1) have finiteE: "finite (edges G)" using wf_graph.finiteE by fast
   from finiteE conjunct1[OF a3] have  finiteF: "finite f" by (metis rev_finite_subset)

   \<comment> \<open>Find a suitable x1, it is the Max of the firsts\<close>
   from finiteF have x12: "\<forall> x \<in> f. Max (p`fst` f) \<ge> p (fst x)" by (metis Max_ge finite_imageI image_eqI)
   from a2 a4 have x14: "\<exists> x1. (p x1) \<in> p`fst` f \<and> x1 \<in> fst` f" by fast
   from finiteF have "(p`fst` f) \<noteq> {} \<Longrightarrow> Max (p`fst` f) \<in> (p`fst` f)" by simp
   hence x15: "Max (p`fst` f) \<in> (p`fst` f)" using x14 by fastforce
   hence "\<exists> x1. ((p x1) = Max (p`fst` f)) \<and> x1 \<in> fst` f" by force
   from this x14 obtain x1 where x1Cond: "((p x1) = Max (p`fst` f)) \<and> x1 \<in> fst` f" by blast
   
   \<comment> \<open>Thus x1 is not in the seconds, not offending\<close>
   from x1Cond x15 have x1ImportantProp3: "(p x1) \<in> p`fst` f" by presburger
   from x1Cond conjunct2[OF a3] x12 have "\<forall>(e1, e2) \<in> f. p x1 > p e2" by fastforce

   from x1Cond this a2 a3 a4 have x1ImportantProp1: "(p x1) \<notin> p`snd` f" by force
   hence x1ImportantProp2: "x1 \<notin> snd` f" by blast

   \<comment> \<open>Obtain x2\<close>
   from x1ImportantProp3 x1Cond have x1ImportantProp4: "x1 \<in> fst` f" by presburger
   from this x1ImportantProp2 have  "\<exists> x1 x2. (x1,x2) \<in> f \<and> x1 \<notin> snd` f" by fastforce
   from this x1Cond x1ImportantProp2 obtain x2 where x2Cond:"(x1,x2) \<in> f \<and> x1 \<notin> snd` f" by force
   
   from a3 have "\<And> x. x \<in> f \<Longrightarrow> x \<in> (edges G)" by blast
   from this x2Cond have x1x2Cond: "(x1,x2) \<in> (edges G)" by blast

   from x1x2Cond x2Cond x1Cond show ?thesis by auto
qed


lemma exCasePairSimp: "(\<exists>x. x \<in> A \<and> (case x of (e1, e2) \<Rightarrow> P e1 e2)) = (\<exists>(e1, e2) \<in> A. (P e1 e2))"
  by auto

lemma exCasePairNotSimp: "(\<exists>x. x \<in> A \<and> \<not> (case x of (e1, e2) \<Rightarrow> P e1 e2)) = (\<exists>(e1, e2) \<in> A. \<not> (P e1 e2))"
  by auto


(* moved here from FiniteGraph.thy. Currently unused *)
subsection \<open>Paths\<close>
  text \<open>A path is represented by a list of adjacent edges.\<close>
  type_synonym 'v path = "('v \<times> 'v) list"

  context wf_graph
  begin
    text \<open>The following predicate describes a valid path:\<close>
    (* is-path src [src, ...., dst] dst *)
    fun is_path :: "'v \<Rightarrow> 'v path \<Rightarrow> 'v \<Rightarrow> bool" where
      "is_path v [] v' \<longleftrightarrow> v=v' \<and> v'\<in>V" |
      "is_path v ((v1,v2)#p) v' \<longleftrightarrow> v=v1 \<and> (v1,v2)\<in>E \<and> is_path v2 p v'"
  
    lemma is_path_simps[simp, intro!]:
      "is_path v [] v \<longleftrightarrow> v\<in>V"
      "is_path v [(v,v')] v' \<longleftrightarrow> (v,v')\<in>E"
      by (auto dest: E_wfD)
    
    lemma is_path_memb[simp]:
      "is_path v p v' \<Longrightarrow> v\<in>V \<and> v'\<in>V"
      apply (induction p arbitrary: v) 
       apply (auto dest: E_wfD)
      done

    lemma is_path_split:
      "is_path v (p1@p2) v' \<longleftrightarrow> (\<exists>u. is_path v p1 u \<and> is_path u p2 v')"
      by (induct p1 arbitrary: v) auto

    lemma is_path_split'[simp]: 
      "is_path v (p1@(u,u')#p2) v' 
        \<longleftrightarrow> is_path v p1 u \<and> (u,u')\<in>E \<and> is_path u' p2 v'"
      by (auto simp add: is_path_split)
  end

  text \<open>Set of intermediate vertices of a path. These are all vertices but
    the last one. Note that, if the last vertex also occurs earlier on the path,
    it is contained in \<open>int_vertices\<close>.\<close>
  definition int_vertices :: "'v path \<Rightarrow> 'v set" where
    "int_vertices p \<equiv> set (map fst p)"

  lemma int_vertices_simps[simp]:
    "int_vertices [] = {}"
    "int_vertices (vv#p) = insert (fst vv) (int_vertices p)"
    "int_vertices (p1@p2) = int_vertices p1 \<union> int_vertices p2"
    by (auto simp add: int_vertices_def)
  
  lemma (in wf_graph) int_vertices_subset: 
    "is_path v p v' \<Longrightarrow> int_vertices p \<subseteq> V"
    apply (induct p arbitrary: v)
     apply (simp) 
    apply (force dest: E_wfD)
    done

  lemma int_vertices_empty[simp]: "int_vertices p = {} \<longleftrightarrow> p=[]"
    by (cases p) auto

subsubsection \<open>Splitting Paths\<close>
  text \<open>Split a path at the point where it first leaves the set \<open>W\<close>:\<close>
  lemma (in wf_graph) path_split_set:
    assumes "is_path v p v'" and "v\<in>W" and "v'\<notin>W"
    obtains p1 p2 u w u' where
    "p=p1@(u,u')#p2" and
    "int_vertices p1 \<subseteq> W" and "u\<in>W" and "u'\<notin>W"
    using assms
  proof (induct p arbitrary: v thesis)
    case Nil thus ?case by auto
  next
    case (Cons vv p)
    note [simp, intro!] = \<open>v\<in>W\<close> \<open>v'\<notin>W\<close>
    from Cons.prems obtain u' where 
      [simp]: "vv=(v,u')" and
        REST: "is_path u' p v'"
      by (cases vv) auto
    
    txt \<open>Distinguish wether the second node \<open>u'\<close> of the path is 
      in \<open>W\<close>. If yes, the proposition follows by the 
      induction hypothesis, otherwise it is straightforward, as
      the split takes place at the first edge of the path.\<close>
    {
      assume A [simp, intro!]: "u'\<in>W"
      from Cons.hyps[OF _ REST] obtain p1 uu uu' p2 where
        "p=p1@(uu,uu')#p2" "int_vertices p1 \<subseteq> W" "uu \<in> W" "uu' \<notin> W"
        by blast
      with Cons.prems(1)[of "vv#p1" uu uu' p2] have thesis by auto
    } moreover {
      assume "u'\<notin>W"
      with Cons.prems(1)[of "[]" v u' p] have thesis by auto
    } ultimately show thesis by blast
  qed
  
  text \<open>Split a path at the point where it first enters the set \<open>W\<close>:\<close>
  lemma (in wf_graph) path_split_set':
    assumes "is_path v p v'" and "v'\<in>W"
    obtains p1 p2 u where
    "p=p1@p2" and
    "is_path v p1 u" and
    "is_path u p2 v'" and
    "int_vertices p1 \<subseteq> -W" and "u\<in>W"
    using assms
  proof (cases "v\<in>W")
    case True with that[of "[]" p] assms show ?thesis
      by auto
  next
    case False with assms that show ?thesis
    proof (induct p arbitrary: v thesis)
      case Nil thus ?case by auto
    next
      case (Cons vv p)
      note [simp, intro!] = \<open>v'\<in>W\<close> \<open>v\<notin>W\<close>
      from Cons.prems obtain u' where 
        [simp]: "vv=(v,u')" and [simp]: "(v,u')\<in>E" and
          REST: "is_path u' p v'"
        by (cases vv) auto
    
      txt \<open>Distinguish wether the second node \<open>u'\<close> of the path is 
        in \<open>W\<close>. If yes, the proposition is straightforward, otherwise,
        it follows by the induction hypothesis.
\<close>
      {
        assume A [simp, intro!]: "u'\<in>W"
        from Cons.prems(3)[of "[vv]" p u'] REST have ?case by auto
      } moreover {
        assume [simp, intro!]: "u'\<notin>W"
        from Cons.hyps[OF REST] obtain p1 p2 u'' where
          [simp]: "p=p1@p2" and 
            "is_path u' p1 u''" and 
            "is_path u'' p2 v'" and
            "int_vertices p1 \<subseteq> -W" and
            "u''\<in>W" by blast
        with Cons.prems(3)[of "vv#p1"] have ?case by auto
      } ultimately show ?case by blast
    qed
  qed

  text \<open>Split a path at the point where a given vertex is first visited:\<close>
  lemma (in wf_graph) path_split_vertex:
    assumes "is_path v p v'" and "u\<in>int_vertices p"
    obtains p1 p2 where
    "p=p1@p2" and
    "is_path v p1 u" and
    "u \<notin> int_vertices p1"
    using assms
  proof (induct p arbitrary: v thesis)
    case Nil thus ?case by auto
  next
    case (Cons vv p)
    from Cons.prems obtain u' where 
      [simp]: "vv=(v,u')" "v\<in>V" "(v,u')\<in>E" and
        REST: "is_path u' p v'"
      by (cases vv) auto
    
    {
      assume "u=v"
      with Cons.prems(1)[of "[]" "vv#p"] have thesis by auto
    } moreover {
      assume [simp]: "u\<noteq>v"
      with Cons.hyps(1)[OF _ REST] Cons.prems(3) obtain p1 p2 where
        "p=p1@p2" "is_path u' p1 u" "u\<notin>int_vertices p1"
        by auto
      with Cons.prems(1)[of "vv#p1" p2] have thesis
        by auto
    } ultimately show ?case by blast
  qed


end
