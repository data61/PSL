(*  Author:  Gertrud Bauer, Tobias Nipkow  *)

section "Further Plane Graph Properties"

theory PlaneProps
imports Invariants
begin

subsection \<open>@{const final}\<close>

lemma plane_final_facesAt:
assumes "inv g" "final g" "v : \<V> g" "f \<in> set (facesAt g v)" shows "final f"
proof -
  from assms(1,3,4) have "f \<in> \<F> g" by(blast intro: minGraphProps inv_mgp)
  with assms(2) show ?thesis by (rule finalGraph_face)
qed

lemma finalVertexI:
  "\<lbrakk> inv g;  final g;  v \<in> \<V> g \<rbrakk> \<Longrightarrow> finalVertex g v"
by (auto simp add: finalVertex_def nonFinals_def filter_empty_conv plane_final_facesAt)


lemma setFinal_notin_finals:
 "\<lbrakk> f \<in> \<F> g; \<not> final f; minGraphProps g \<rbrakk> \<Longrightarrow> setFinal f \<notin> set (finals g)"
apply(drule minGraphProps11)
apply(cases f)
apply(fastforce simp:finals_def setFinal_def normFaces_def normFace_def
                    verticesFrom_def minVertex_def inj_on_def distinct_map
           split:facetype.splits)
done


subsection \<open>@{const degree}\<close>

lemma planeN4: "inv g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow> 3 \<le> |vertices f|"
apply(subgoal_tac "2 < | vertices f |")
 apply arith
apply(drule inv_mgp)
apply (erule (1) minGraphProps2)
done


lemma degree_eq:
assumes pl: "inv g" and fin: "final g" and v: "v : \<V> g"
shows "degree g v = tri g v + quad g v + except g v"
proof -
  have dist: "distinct(facesAt g v)" using pl v by simp
  have 3: "\<forall>f \<in> set(facesAt g v). |vertices f| = 3 \<or> |vertices f| = 4 \<or>
                                  |vertices f| \<ge> 5"
  proof
    fix f assume f: "f \<in> set (facesAt g v)"
    hence "|vertices f| \<ge> 3"
      using minGraphProps5[OF inv_mgp[OF pl] v f] planeN4[OF pl] by blast
    thus "|vertices f| = 3 \<or> |vertices f| = 4 \<or> |vertices f| \<ge> 5" by arith
  qed
  have "degree g v = |facesAt g v|" by(simp add:degree_def)
  also have "\<dots> = card(set(facesAt g v))" by (simp add:distinct_card[OF dist])
  also have "set(facesAt g v) = {f \<in> set(facesAt g v). |vertices f| = 3} \<union>
                                {f \<in> set(facesAt g v). |vertices f| = 4} \<union>
                                {f \<in> set(facesAt g v). |vertices f| \<ge> 5}"
    (is "_ = ?T \<union> ?Q \<union> ?E")
    using 3 by blast
  also have "card(?T \<union> ?Q \<union> ?E) = card ?T + card ?Q + card ?E"
    apply (subst card_Un_disjoint)
    apply simp
    apply simp
    apply fastforce
    apply (subst card_Un_disjoint)
    apply simp
    apply simp
    apply fastforce
    apply simp
    done
  also have "\<dots> = tri g v + quad g v + except g v" using fin
    by(simp add:tri_def quad_def except_def
                distinct_card[symmetric] distinct_filter[OF dist]
                plane_final_facesAt[OF pl fin v] cong:conj_cong)
  finally show ?thesis .
qed

lemma plane_fin_exceptionalVertex_def:
assumes pl: "inv g" and fin: "final g" and v: "v : \<V> g"
shows "exceptionalVertex g v =
 ( | [f \<leftarrow> facesAt g v . 5 \<le> |vertices f| ] | \<noteq> 0)"
proof -
  have "\<And>f. f \<in> set (facesAt g v) \<Longrightarrow> final f"
    by(rule plane_final_facesAt[OF pl fin v])
  then show ?thesis by (simp add: filter_simp exceptionalVertex_def except_def)
qed

lemma not_exceptional:
  "inv g \<Longrightarrow> final g \<Longrightarrow> v : \<V> g \<Longrightarrow> f \<in> set (facesAt g v) \<Longrightarrow>
  \<not> exceptionalVertex g v \<Longrightarrow> |vertices f| \<le> 4"
by (auto simp add: plane_fin_exceptionalVertex_def except_def filter_empty_conv)


subsection \<open>Misc\<close>

lemma in_next_plane0I:
assumes "g' \<in> set (generatePolygon n v f g)" "f \<in> set (nonFinals g)"
        "v \<in> \<V> f" "3 \<le> n" "n < 4+p"
shows "g' \<in> set (next_plane0\<^bsub>p\<^esub> g)"
proof -
  from assms have
    "\<exists>n\<in>{3..<4 + p}. g' \<in> set (generatePolygon n v f g)"
    by auto
  with assms have 
    "\<exists>v\<in>\<V> f. \<exists>n\<in>{3..<4 + p}. g' \<in> set (generatePolygon n v f g)"
    by auto
  with assms have
    "\<exists>f\<in>set (nonFinals g). \<exists>v\<in>\<V> f. \<exists>n\<in>{3..<4 + p}. g' \<in> set (generatePolygon n v f g)"
    by auto
  moreover have "\<not> final g" using assms(2)
    by (auto simp: nonFinals_def finalGraph_def filter_empty_conv)
  ultimately show ?thesis
    by (simp add: next_plane0_def)
qed


lemma next_plane0_nonfinals: "g [next_plane0\<^bsub>p\<^esub>]\<rightarrow> g' \<Longrightarrow> nonFinals g \<noteq> []"
by(auto simp:next_plane0_def finalGraph_def)


lemma next_plane0_ex:
assumes a: "g [next_plane0\<^bsub>p\<^esub>]\<rightarrow> g'"
shows "\<exists>f\<in> set(nonFinals g). \<exists>v \<in> \<V> f. \<exists>i \<in> set([3..<Suc(maxGon p)]).
       g' \<in> set (generatePolygon i v f g)"
proof -
  from a have "\<not> final g" by (auto simp add: next_plane0_def)
  with a show ?thesis
   by (auto simp add: next_plane0_def nonFinals_def)
qed

lemma step_outside2:
 "inv g \<Longrightarrow> g [next_plane0\<^bsub>p\<^esub>]\<rightarrow> g' \<Longrightarrow> \<not> final g' \<Longrightarrow> |faces g'| \<noteq> 2"
apply(frule inv_two_faces)
apply(frule inv_finals_nonempty)
apply(drule inv_mgp)
apply(insert len_faces_sum[of g] len_faces_sum[of g'])
apply(subgoal_tac "|nonFinals g| \<noteq> 0")
 prefer 2 apply(drule next_plane0_nonfinals) apply simp
apply(subgoal_tac "|nonFinals g'| \<noteq> 0")
 prefer 2 apply(simp add:finalGraph_def)
apply(drule (1) next_plane0_incr_faces)
apply(case_tac "|faces g| = 2")
 prefer 2 apply arith
apply(subgoal_tac "|finals g| \<noteq> 0")
 apply arith
apply simp
done


subsection\<open>Increasing final faces\<close>


lemma set_finals_splitFace[simp]:
 "\<lbrakk> f \<in> \<F> g; \<not> final f \<rbrakk> \<Longrightarrow>
  set(finals(snd(snd(splitFace g u v f vs)))) = set(finals g)"
apply(auto simp add:splitFace_def split_def finals_def
                split_face_def)
 apply(drule replace5)
 apply(clarsimp)
apply(erule replace4)
apply clarsimp
done


lemma next_plane0_finals_incr:
 "g [next_plane0\<^bsub>p\<^esub>]\<rightarrow> g' \<Longrightarrow> f \<in> set(finals g) \<Longrightarrow> f \<in> set(finals g')"
apply(auto simp:next_plane0_def generatePolygon_def split:if_split_asm)
apply(erule subdivFace_pres_finals)
apply (simp add:nonFinals_def)
done

lemma next_plane0_finals_subset:
  "g' \<in> set (next_plane0\<^bsub>p\<^esub> g) \<Longrightarrow>
  set (finals g) \<subseteq> set (finals g')"
  by (auto simp add: next_plane0_finals_incr)


lemma next_plane0_final_mono:
  "\<lbrakk> g' \<in> set (next_plane0\<^bsub>p\<^esub> g); f \<in> \<F> g; final f \<rbrakk> \<Longrightarrow> f \<in> \<F> g'"
apply(drule next_plane0_finals_subset)
apply(simp add:finals_def)
apply blast
done


subsection\<open>Increasing vertices\<close>

lemma next_plane0_vertices_subset:
 "\<lbrakk> g' \<in> set (next_plane0\<^bsub>p\<^esub> g); minGraphProps g \<rbrakk> \<Longrightarrow> \<V> g \<subseteq> \<V> g'"
apply(rule next_plane0_incr)
    apply(erule (1) subset_trans)
   apply(simp add: vertices_makeFaceFinal)
  defer apply assumption+
apply (auto simp: splitFace_def split_def vertices_graph)
done


subsection\<open>Increasing vertex degrees\<close>

lemma next_plane0_incr_faceListAt:
 "\<lbrakk> g' \<in> set (next_plane0\<^bsub>p\<^esub> g); minGraphProps g \<rbrakk>
  \<Longrightarrow> |faceListAt g| \<le> |faceListAt g'| \<and>
      (\<forall>v < |faceListAt g|. |faceListAt g ! v| \<le> |faceListAt g' ! v| )"
 (is "_ \<Longrightarrow> _ \<Longrightarrow> ?Q g g'")
apply(rule next_plane0_incr[where Q = ?Q])
prefer 4 apply assumption
prefer 4 apply assumption
  apply(rule conjI) apply fastforce
  apply(clarsimp)
  apply(erule allE, erule impE, assumption)
  apply(erule_tac x = v in allE, erule impE) apply force
  apply force
 apply(simp add: makeFaceFinal_def makeFaceFinalFaceList_def)
apply (simp add: splitFace_def split_def nth_append nth_list_update)
done


lemma next_plane0_incr_degree:
 "\<lbrakk> g' \<in> set (next_plane0\<^bsub>p\<^esub> g); minGraphProps g; v \<in> \<V> g \<rbrakk>
  \<Longrightarrow> degree g v \<le> degree g' v"
apply(frule (1) next_plane0_incr_faceListAt)
apply(frule (1) next_plane0_vertices_subset)
apply(simp add:degree_def facesAt_def)
apply(frule minGraphProps4)
apply(simp add:vertices_graph)
done


subsection\<open>Increasing @{const except}\<close>

lemma next_plane0_incr_except:
assumes "g' \<in> set (next_plane0\<^bsub>p\<^esub> g)" "inv g" "v \<in> \<V> g"
shows "except g v \<le> except g' v"
proof (unfold except_def)
  note inv' = invariantE[OF inv_inv_next_plane0, OF assms(1,2)]
  note mgp = inv_mgp[OF assms(2)] and mgp' = inv_mgp[OF inv']
  note dist = distinct_filter[OF mgp_dist_facesAt[OF mgp \<open>v : \<V> g\<close>]]
  have "v \<in> \<V> g'"
    using assms(3) next_plane0_vertices_subset[OF assms(1) mgp] by blast
  note dist' = distinct_filter[OF mgp_dist_facesAt[OF mgp' \<open>v : \<V> g'\<close>]]
  have "|[f\<leftarrow>facesAt g v . final f \<and> 5 \<le> |vertices f| ]| =
        card{f\<in> set(facesAt g v) . final f \<and> 5 \<le> |vertices f|}"
    (is "?L = card ?M") using distinct_card[OF dist] by simp
  also have "?M = {f\<in> \<F> g. v \<in> \<V> f \<and> final f \<and> 5 \<le> |vertices f|}"
    by(simp add: minGraphProps_facesAt_eq[OF mgp assms(3)])
  also have "\<dots> = {f \<in> set(finals g) . v \<in> \<V> f \<and> 5 \<le> |vertices f|}"
    by(auto simp:finals_def)
  also have "card \<dots> \<le> card{f \<in> set(finals g'). v \<in> \<V> f \<and> 5 \<le> |vertices f|}"
    (is "_ \<le> card ?M")
    apply(rule card_mono)
    apply simp
    using next_plane0_finals_subset[OF assms(1)] by blast
  also have "?M = {f\<in> \<F> g' . v \<in> \<V> f \<and> final f \<and> 5 \<le> |vertices f|}"
    by(auto simp:finals_def)
  also have "\<dots> = {f \<in> set(facesAt g' v) . final f \<and> 5 \<le> |vertices f|}"
    by(simp add: minGraphProps_facesAt_eq[OF mgp' \<open>v \<in> \<V> g'\<close>])
  also have "card \<dots> =
    |[f \<leftarrow> facesAt g' v . final f \<and> 5 \<le> |vertices f| ]|" (is "_ = ?R")
    using distinct_card[OF dist'] by simp
  finally show "?L \<le> ?R" .
qed


subsection\<open>Increasing edges\<close>

lemma next_plane0_set_edges_subset:
  "\<lbrakk> minGraphProps g;  g [next_plane0\<^bsub>p\<^esub>]\<rightarrow> g' \<rbrakk> \<Longrightarrow> edges g \<subseteq> edges g'"
apply(rule next_plane0_incr)
    apply(erule (1) subset_trans)
   apply(simp add: edges_makeFaceFinal)
  apply(erule snd_snd_splitFace_edges_incr)
 apply assumption+
done


subsection\<open>Increasing final vertices\<close>

(*
This should really be proved via the (unproven) invariant
v : f \<Longrightarrow> ((g,v).f).(f.v) = v
*)

declare  atLeastLessThan_iff[iff]

lemma next_plane0_incr_finV:
 "\<lbrakk>g' \<in> set (next_plane0\<^bsub>p\<^esub> g); minGraphProps g \<rbrakk>
  \<Longrightarrow> \<forall>v \<in> \<V> g. v \<in> \<V> g' \<and>
        ((\<forall>f\<in>\<F> g. v \<in> \<V> f \<longrightarrow> final f) \<longrightarrow>
         (\<forall>f\<in>\<F> g'. v \<in> \<V> f \<longrightarrow> f \<in> \<F> g))" (is "_ \<Longrightarrow> _ \<Longrightarrow> ?Q g g'")
apply(rule next_plane0_incr[where Q = ?Q and g=g and g'=g'])
prefer 4 apply assumption
prefer 4 apply assumption
  apply fast
 apply(clarsimp simp:makeFaceFinal_def vertices_graph makeFaceFinalFaceList_def)
 apply(drule replace5)
 apply(erule disjE)apply blast
 apply(simp add:setFinal_def)
apply(unfold pre_splitFace_def)
apply(clarsimp simp:splitFace_def split_def vertices_graph)
apply(rule conjI)
 apply(clarsimp simp:split_face_def vertices_graph atLeastLessThan_def)
 apply(blast dest:inbetween_inset)
apply(clarsimp)
apply(erule disjE[OF replace5]) apply blast
apply(clarsimp simp:split_face_def vertices_graph)
apply(blast dest:inbetween_inset)
done


lemma next_plane0_finalVertex_mono:
 "\<lbrakk>g' \<in> set (next_plane0\<^bsub>p\<^esub> g); inv g; u \<in> \<V> g; finalVertex g u \<rbrakk>
  \<Longrightarrow> finalVertex g' u"
apply(frule (1) invariantE[OF inv_inv_next_plane0])
apply(subgoal_tac "u \<in> \<V> g'")
 prefer 2 apply(blast dest:next_plane0_vertices_subset inv_mgp)
apply(clarsimp simp:finalVertex_def minGraphProps_facesAt_eq[OF inv_mgp])
apply(blast dest:next_plane0_incr_finV inv_mgp)
done


subsection\<open>Preservation of @{const facesAt} at final vertices\<close>

lemma next_plane0_finalVertex_facesAt_eq:
 "\<lbrakk>g' \<in> set (next_plane0\<^bsub>p\<^esub> g); inv g; v \<in> \<V> g; finalVertex g v \<rbrakk>
  \<Longrightarrow> set(facesAt g' v) = set(facesAt g v)"
apply(frule (1) invariantE[OF inv_inv_next_plane0])
apply(subgoal_tac "v \<in> \<V> g'")
 prefer 2 apply(blast dest:next_plane0_vertices_subset inv_mgp)
apply(clarsimp simp:finalVertex_def minGraphProps_facesAt_eq[OF inv_mgp])
by(blast dest:next_plane0_incr_finV next_plane0_final_mono inv_mgp)


lemma next_plane0_len_filter_eq:
assumes "g' \<in> set (next_plane0\<^bsub>p\<^esub> g)" "inv g" "v \<in> \<V> g" "finalVertex g v"
shows "|filter P (facesAt g' v)| = |filter P (facesAt g v)|"
proof -
  note inv' = invariantE[OF inv_inv_next_plane0, OF assms(1,2)]
  note mgp = inv_mgp[OF assms(2)] and mgp' = inv_mgp[OF inv']
  note dist = distinct_filter[OF mgp_dist_facesAt[OF mgp \<open>v : \<V> g\<close>]]
  have "v \<in> \<V> g'"
    using assms(3) next_plane0_vertices_subset[OF assms(1) mgp] by blast
  note dist' = distinct_filter[OF mgp_dist_facesAt[OF mgp' \<open>v : \<V> g'\<close>]]
  have "|filter P (facesAt g' v)| = card{f \<in> set(facesAt g' v) . P f}"
    using distinct_card[OF dist'] by simp
  also have "\<dots> = card{f \<in> set(facesAt g v) . P f}"
    by(simp add: next_plane0_finalVertex_facesAt_eq[OF assms])
  also have "\<dots> = |filter P (facesAt g v)|"
    using distinct_card[OF dist] by simp
  finally show ?thesis .
qed


subsection\<open>Properties of @{const subdivFace'}\<close>

lemma new_edge_subdivFace':
  "\<And>f v n g.
  pre_subdivFace' g f u v n ovs \<Longrightarrow> minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow>
  subdivFace' g f v n ovs = makeFaceFinal f g \<or>
  (\<forall>f' \<in> \<F> (subdivFace' g f v n ovs) - (\<F> g - {f}).
   \<exists>e \<in> \<E> f'. e \<notin> \<E> g)"
proof (induct ovs)
  case Nil thus ?case by simp
next
  case (Cons ov ovs)
  note IH = Cons(1) and pre = Cons(2) and mgp = Cons(3) and fg = Cons(4)
  have uf: "u \<in> \<V> f" and vf: "v \<in> \<V> f" and distf: "distinct (vertices f)"
    using pre by(simp add:pre_subdivFace'_def)+
  note distFg = minGraphProps11'[OF mgp]
  show ?case
  proof (cases ov)
    case None
    have pre': "pre_subdivFace' g f u v (Suc n) ovs"
      using None pre by (simp add: pre_subdivFace'_None)
    show ?thesis using None
      by (simp add: IH[OF pre' mgp fg])
  next
    case (Some w)
    note pre = pre[simplified Some]
    have uvw: "before (verticesFrom f u) v w"
      using pre by(simp add:pre_subdivFace'_def)
    have uw: "u \<noteq> w" using pre by(clarsimp simp: pre_subdivFace'_def)
    { assume w: "f \<bullet> v = w" and n: "n = 0"
      have pre': "pre_subdivFace' g f u w 0 ovs"
        using pre Some n using [[simp_depth_limit = 5]] by (simp add: pre_subdivFace'_Some2)
      note IH[OF pre' mgp fg]
    } moreover
    { let ?vs = "[countVertices g..<countVertices g + n]"
      let ?fdg = "splitFace g v w f ?vs"
      let  ?f\<^sub>1 = "fst ?fdg" and ?f\<^sub>2 = "fst(snd ?fdg)" and ?g' = "snd(snd ?fdg)"
      let ?g'' = "subdivFace' ?g' ?f\<^sub>2 w 0 ovs"
      let ?fvw = "between(vertices f) v w" and ?fwv = "between(vertices f) w v"
      assume a: "f \<bullet> v = w \<longrightarrow> 0 < n"
      have fsubg: "\<V> f \<subseteq> \<V> g"
        using mgp fg by(simp add: minGraphProps_def faces_subset_def)
      have pre_fdg: "pre_splitFace g v w f ?vs"
           apply (rule pre_subdivFace'_preFaceDiv[OF pre fg _ fsubg])
           using a by (simp)
      hence "v \<noteq> w" and "w \<in> \<V> f" by(unfold pre_splitFace_def)simp+
      have f\<^sub>1: "?f\<^sub>1= fst(split_face f v w ?vs)"
        and f\<^sub>2: "?f\<^sub>2 = snd(split_face f v w ?vs)"
        by(auto simp add:splitFace_def split_def)
      note pre_split = pre_splitFace_pre_split_face[OF pre_fdg]
      have E\<^sub>1: "\<E> ?f\<^sub>1 = Edges (w # rev ?vs @ [v]) \<union> Edges (v # ?fvw @ [w])"
        using f\<^sub>1 by(simp add:edges_split_face1[OF pre_split])
      have E\<^sub>2: "\<E> ?f\<^sub>2 = Edges (v # ?vs @ [w]) \<union> Edges (w # ?fwv @ [v])"
        by(simp add:splitFace_def split_def
            edges_split_face2[OF pre_split])
      note mgp' = splitFace_holds_minGraphProps[OF pre_fdg mgp]
      note distFg' = minGraphProps11'[OF mgp']
      have pre': "pre_subdivFace' ?g' ?f\<^sub>2 u w 0 ovs"
        by (rule pre_subdivFace'_Some1[OF pre fg _ fsubg HOL.refl HOL.refl])
           (simp add:a)
      note f2inF = splitFace_add_f21'[OF fg]
      have 1: "\<exists>e \<in> \<E> ?f\<^sub>1. e \<notin> \<E> g"
      proof cases
        assume "rev ?vs = []"
        hence "(w,v) \<in> \<E> ?f\<^sub>1 \<and> (w,v) \<notin> \<E> g" using pre_fdg E\<^sub>1
          by(unfold pre_splitFace_def) (auto simp:Edges_Cons)
        thus ?thesis by blast
      next
        assume "rev ?vs \<noteq> []"
        then obtain x xs where rvs: "rev ?vs = x#xs"
          by(auto simp only:neq_Nil_conv)
        hence "(w,x) \<in> \<E> ?f\<^sub>1" using E\<^sub>1 by (auto simp:Edges_Cons)
        moreover have "(w,x) \<notin> \<E> g"
        proof -
          have "x \<in> set(rev ?vs)" using rvs by simp
          hence "x \<ge> countVertices g" by simp
          hence "x \<notin> \<V> g" by(induct g) (simp add:vertices_graph_def)
          thus ?thesis
            by (auto simp:edges_graph_def)
               (blast dest: in_edges_in_vertices minGraphProps9[OF mgp])
        qed
        ultimately show ?thesis by blast
      qed
      have 2: "\<exists>e \<in> \<E> ?f\<^sub>2. e \<notin> \<E> g"
      proof cases
        assume "?vs = []"
        hence "(v,w) \<in> \<E> ?f\<^sub>2 \<and> (v,w) \<notin> \<E> g" using pre_fdg E\<^sub>2
          by(unfold pre_splitFace_def) (auto simp:Edges_Cons)
        thus ?thesis by blast
      next
        assume "?vs \<noteq> []"
        then obtain x xs where vs: "?vs = x#xs"
          by(auto simp only:neq_Nil_conv)
        hence "(v,x) \<in> \<E> ?f\<^sub>2" using E\<^sub>2 by (auto simp:Edges_Cons)
        moreover have "(v,x) \<notin> \<E> g"
        proof -
          have "x \<in> set ?vs" using vs by simp
          hence "x \<ge> countVertices g" by simp
          hence "x \<notin> \<V> g" by(induct g) (simp add:vertices_graph_def)
          thus ?thesis
            by (auto simp:edges_graph_def)
               (blast dest: in_edges_in_vertices minGraphProps9[OF mgp])
        qed
        ultimately show ?thesis by blast
      qed
      have fdg: "(?f\<^sub>1,?f\<^sub>2,?g') = splitFace g v w f ?vs" by auto
      hence Fg': "\<F> ?g' = {?f\<^sub>1,?f\<^sub>2} \<union> (\<F> g - {f})"
        using set_faces_splitFace[OF mgp fg pre_fdg] by blast
      have "\<forall>f' \<in> \<F> ?g'' - (\<F> g - {f}). \<exists>e \<in> \<E> f'. e \<notin> \<E> g"
      proof (clarify)
        fix f' assume f'g'': "f' \<in> \<F> ?g''" and f'ng: "f' \<notin> \<F> g - {f}"
        from IH[OF pre' mgp' f2inF]
        show "\<exists>e \<in> \<E> f'. e \<notin> \<E> g"
        proof
          assume "?g'' = makeFaceFinal ?f\<^sub>2 ?g'"
          hence "f' = setFinal ?f\<^sub>2 \<or> f' = ?f\<^sub>1" (is "?A \<or> ?B")
            using f'g'' Fg' f'ng
            by(auto simp:makeFaceFinal_def makeFaceFinalFaceList_def
              distinct_set_replace[OF distFg'])
          thus ?thesis
          proof
            assume ?A thus ?thesis using 2 by(simp)
          next
            assume ?B thus ?thesis using 1 by blast
          qed
        next
          assume A: "\<forall>f' \<in> \<F> ?g'' - (\<F> ?g' - {?f\<^sub>2}).
                     \<exists>e \<in> \<E> f'. e \<notin> \<E> ?g'"
          show ?thesis
          proof cases
            assume "f' \<in> {?f\<^sub>1,?f\<^sub>2}"
            thus ?thesis using 1 2 by blast
          next
            assume "f' \<notin> {?f\<^sub>1,?f\<^sub>2}"
            hence "\<exists>e\<in>\<E> f'. e \<notin> \<E> ?g'"
              using A f'g'' f'ng Fg' by simp
            with splitFace_edges_incr[OF pre_fdg fdg]
            show ?thesis by blast
          qed
        qed
      qed
    }
    ultimately show ?thesis using Some by(auto simp: split_def)
  qed
qed


lemma dist_edges_subdivFace':
  "pre_subdivFace' g f u v n ovs \<Longrightarrow> minGraphProps g \<Longrightarrow> f \<in> \<F> g \<Longrightarrow>
  subdivFace' g f v n ovs = makeFaceFinal f g \<or>
  (\<forall>f' \<in> \<F> (subdivFace' g f v n ovs) - (\<F> g - {f}). \<E> f' \<noteq> \<E> f)"
apply(drule (2) new_edge_subdivFace')
apply(erule disjE)
 apply blast
apply(rule disjI2)
apply(clarify)
apply(drule bspec)
 apply fast
apply(simp add:edges_graph_def)
by(blast)



lemma between_last: "\<lbrakk> distinct(vertices f); u \<in> \<V> f \<rbrakk> \<Longrightarrow>
   between (vertices f) u (last (verticesFrom f u)) =
   butlast(tl(verticesFrom f u))"
apply(drule split_list)
apply (fastforce dest: last_in_set
  simp: between_def verticesFrom_Def split_def
       last_append butlast_append fst_splitAt_last)
done

(* FIXME move condition to pre_addfacesnd? *)
lemma final_subdivFace': "\<And>f u n g. minGraphProps g \<Longrightarrow>
  pre_subdivFace' g f r u n ovs \<Longrightarrow> f \<in> \<F> g \<Longrightarrow>
  (ovs = [] \<longrightarrow> n=0 \<and> u = last(verticesFrom f r)) \<Longrightarrow>
  \<exists>f' \<in> set(finals(subdivFace' g f u n ovs)) - set(finals g).
   (f\<^bsup>-1\<^esup> \<bullet> r,r) \<in> \<E> f' \<and>  |vertices f'| =
      n + |ovs| + (if r=u then 1 else |between (vertices f) r u| + 2)"
proof (induct ovs)
  case Nil show ?case (is "\<exists>f' \<in> ?F. ?P f'")
  proof
    show "?P (setFinal f)" (is "?A \<and> ?B")
    proof
      show "?A" using Nil
        by(simp add:pre_subdivFace'_def prevVertex_in_edges
          del:is_nextElem_edges_eq)
      show  "?B"
        using Nil mgp_vertices3[OF Nil(1,3)]
        by(simp add:  setFinal_def between_last pre_subdivFace'_def)
    qed
  next
    show "setFinal f \<in> ?F" using Nil
      by(simp add:pre_subdivFace'_def setFinal_notin_finals minGraphProps11')
  qed
next
  case (Cons ov ovs)
  note IH = Cons(1) and mgp = Cons(2) and pre = Cons(3) and fg = Cons(4)
    and mt = Cons(5)
  have "r \<in> \<V> f" and "u \<in> \<V> f" and distf: "distinct (vertices f)"
    using pre by(simp add:pre_subdivFace'_def)+
  show ?case
  proof (cases ov)
    case None
    have pre': "pre_subdivFace' g f r u (Suc n) ovs"
      using None pre by (simp add: pre_subdivFace'_None)
    have "ovs \<noteq> []" using pre None by (auto simp: pre_subdivFace'_def)
    thus ?thesis using None IH[OF mgp pre' fg] by simp
  next
    case (Some v)
    note pre = pre[simplified Some]
      have ruv: "before (verticesFrom f r) u v" and "r \<noteq> v"
        using pre by(simp add:pre_subdivFace'_def)+
    show ?thesis
    proof (cases "f \<bullet> u = v \<and> n = 0")
      case True
      have pre': "pre_subdivFace' g f r v 0 ovs"
        using pre True using [[simp_depth_limit = 5]] by (simp add: pre_subdivFace'_Some2)
      have mt: "ovs = [] \<longrightarrow> 0 = 0 \<and> v = last (verticesFrom f r)"
        using pre by(clarsimp simp:pre_subdivFace'_def)
      show ?thesis using Some True IH[OF mgp pre' fg mt] \<open>r \<noteq> v\<close>
        by(auto simp: between_next_empty[OF distf]
          unroll_between_next2[OF distf \<open>r \<in> \<V> f\<close> \<open>u \<in> \<V> f\<close>])
    next
      case False
      let ?vs = "[countVertices g..<countVertices g + n]"
      let ?fdg = "splitFace g u v f ?vs"
      let ?g' = "snd(snd ?fdg)" and ?f\<^sub>2 = "fst(snd ?fdg)"
      let ?fvu = "between (vertices f) v u"
      have False': "f \<bullet> u = v \<longrightarrow> n \<noteq> 0" using False by auto
      have VfVg: "\<V> f \<subseteq> \<V> g" using mgp fg
          by (simp add: minGraphProps_def faces_subset_def)
      note pre_fdg = pre_subdivFace'_preFaceDiv[OF pre fg False' VfVg]
      hence "u \<noteq> v" and "v \<in> \<V> f" and disj: "\<V> f \<inter> set ?vs = {}"
        by(unfold pre_splitFace_def)simp+
      hence vvs: "v \<notin> set ?vs" by auto
      have vf\<^sub>2: "vertices ?f\<^sub>2 = [v] @ ?fvu @ u # ?vs"
        by(simp add:split_face_def splitFace_def split_def)
      hence betuvf\<^sub>2: "between (vertices ?f\<^sub>2) u v = ?vs"
        using splitFace_distinct1[OF pre_fdg]
        by(simp add: between_back)
      have betrvf\<^sub>2: "r \<noteq> u \<Longrightarrow> between (vertices ?f\<^sub>2) r v =
        between (vertices f) r u @ [u] @ ?vs"
      proof -
        assume "r\<noteq>u"
        have r: "r \<in> set (between (vertices f) v u)"
          using \<open>r\<noteq>u\<close> \<open>r\<noteq>v\<close> \<open>u\<noteq>v\<close> \<open>v \<in> \<V> f\<close> \<open>r \<in> \<V> f\<close> distf ruv
          by(blast intro:rotate_before_vFrom before_between)
        have "between (vertices f) v u =
          between (vertices f) v r @ [r] @ between (vertices f) r u"
          using split_between[OF distf \<open>v \<in> \<V> f\<close> \<open>u \<in> \<V> f\<close> r] \<open>r\<noteq>v\<close>
          by simp
        moreover hence "v \<notin> set (between (vertices f) r u)"
          using between_not_r1[OF distf, of v u] by simp
        ultimately show ?thesis using vf\<^sub>2 \<open>r\<noteq>v\<close> \<open>u\<noteq>v\<close> vvs
          by (simp add: between_back between_not_r2[OF distf])
      qed
      note mgp' = splitFace_holds_minGraphProps[OF pre_fdg mgp]
      note f2g = splitFace_add_f21'[OF fg]
      note pre' = pre_subdivFace'_Some1[OF pre fg False' VfVg HOL.refl HOL.refl]
      from pre_fdg have "v \<in> \<V> f" and disj: "\<V> f \<inter> set ?vs = {}"
        by(unfold pre_splitFace_def, simp)+
      have fr: "?f\<^sub>2\<^bsup>-1\<^esup> \<bullet> r = f\<^bsup>-1\<^esup> \<bullet> r"
      proof -
        note pre_split = pre_splitFace_pre_split_face[OF pre_fdg]
        have rinf\<^sub>2: "r \<in> \<V> ?f\<^sub>2"
        proof cases
          assume "r = u" thus ?thesis by(simp add:vf\<^sub>2)
        next
          assume "r \<noteq> u"
          hence "r \<in> set ?fvu" using distf \<open>v : \<V> f\<close> \<open>r\<noteq>v\<close> \<open>r : \<V> f\<close> ruv
            by(blast intro: before_between rotate_before_vFrom)
          thus ?thesis by(simp add:vf\<^sub>2)
        qed
        have E\<^sub>2: "\<E> ?f\<^sub>2 = Edges (u # ?vs @ [v]) \<union>
                             Edges (v # ?fvu @ [u])"
          by(simp add:splitFace_def split_def
            edges_split_face2[OF pre_split])
        moreover have "(?f\<^sub>2\<^bsup>-1\<^esup> \<bullet> r, r) \<in> \<E> ?f\<^sub>2"
          by(blast intro: prevVertex_in_edges rinf\<^sub>2
            splitFace_distinct1[OF pre_fdg])
        moreover have "(?f\<^sub>2\<^bsup>-1\<^esup> \<bullet> r, r) \<notin> Edges (u # ?vs @ [v])"
        proof -
          have "r \<notin> set ?vs" using \<open>r : \<V> f\<close> disj by blast
          thus ?thesis using \<open>r \<noteq> v\<close>
            by(simp add:Edges_Cons Edges_append notinset_notinEdge2) arith
        qed
        ultimately have "(?f\<^sub>2\<^bsup>-1\<^esup> \<bullet> r, r) \<in> Edges (v # ?fvu @ [u])" by blast
        hence "(?f\<^sub>2\<^bsup>-1\<^esup> \<bullet> r, r) \<in> \<E> f" using pre_split_face_symI[OF pre_split]
          by(blast intro: Edges_between_edges)
        hence eq: "f \<bullet> (?f\<^sub>2\<^bsup>-1\<^esup> \<bullet> r) = r" and inf: "?f\<^sub>2\<^bsup>-1\<^esup> \<bullet> r \<in> \<V> f"
          by(simp add:edges_face_eq)+
        have "?f\<^sub>2\<^bsup>-1\<^esup> \<bullet> r = f\<^bsup>-1\<^esup> \<bullet> (f \<bullet> (?f\<^sub>2\<^bsup>-1\<^esup> \<bullet> r))"
          using prevVertex_nextVertex[OF distf inf] by simp
        also have "\<dots> = f\<^bsup>-1\<^esup> \<bullet> r" using eq by simp
        finally show ?thesis .
      qed
      hence mt: "ovs = [] \<longrightarrow> 0 = 0 \<and> v = last (verticesFrom ?f\<^sub>2 r)"
        using pre' pre by(auto simp:pre_subdivFace'_def splitFace_def
          split_def last_vFrom)
      from IH[OF mgp' pre' f2g mt] \<open>r \<noteq> v\<close> obtain f' :: face where
        f: "f' \<in> set(finals(subdivFace' ?g' ?f\<^sub>2 v 0 ovs)) - set(finals ?g')"
        and ff: "(?f\<^sub>2\<^bsup>-1\<^esup> \<bullet> r, r) \<in> \<E> f'"
        "|vertices f'| = |ovs| + |between (vertices ?f\<^sub>2) r v| + 2"
        by simp blast
      show ?thesis (is "\<exists>f' \<in> ?F. ?P f'")
      proof
        show "f' \<in> ?F" using f pre Some fg
          by(simp add:False split_def pre_subdivFace'_def)
        show "?P f'" using ff fr by(clarsimp simp:betuvf\<^sub>2 betrvf\<^sub>2)
      qed
    qed
  qed
qed


lemma Seed_max_final_ex:
 "\<exists>f\<in>set (finals (Seed p)). |vertices f| = maxGon p"
  by (simp add: Seed_def graph_max_final_ex)

lemma max_face_ex: assumes a: "Seed\<^bsub>p\<^esub> [next_plane0\<^bsub>p\<^esub>]\<rightarrow>* g"
shows "\<exists>f \<in> set (finals g). |vertices f| = maxGon p"
using a
proof (induct rule: RTranCl_induct)
  case refl then show ?case using Seed_max_final_ex by simp
next
  case (succs g g')
  then obtain f where f: "f\<in>set (finals g)" and "|vertices f| = maxGon p"
    by auto
  moreover from succs(1) f have "f\<in>set (finals g')" by (rule next_plane0_finals_incr)
  ultimately show ?case by auto
qed


end
