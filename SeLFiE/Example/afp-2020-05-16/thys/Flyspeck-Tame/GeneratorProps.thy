(*  Author:  Tobias Nipkow  *)

section "Properties of Tame Graph Enumeration (1)"

theory GeneratorProps
imports Plane1Props Generator TameProps LowerBound
begin

lemma genPolyTame_spec:
 "generatePolygonTame n v f g = [g' \<leftarrow> generatePolygon n v f g . \<not> notame g']"
by(simp add:generatePolygonTame_def generatePolygon_def enum_enumerator)

lemma genPolyTame_subset_genPoly:
 "g' \<in> set(generatePolygonTame i v f g) \<Longrightarrow>
  g' \<in> set(generatePolygon i v f g)"
by(auto simp add:generatePolygon_def generatePolygonTame_def enum_enumerator)


lemma next_tame0_subset_plane:
 "set(next_tame0 p g) \<subseteq> set(next_plane p g)"
by(auto simp add:next_tame0_def next_plane_def polysizes_def
           elim!:genPolyTame_subset_genPoly simp del:upt_Suc)


lemma genPoly_new_face:
 "\<lbrakk>g' \<in> set (generatePolygon n v f g); minGraphProps g; f \<in> set (nonFinals g);
   v \<in> \<V> f; n \<ge> 3 \<rbrakk> \<Longrightarrow>
  \<exists>f \<in> set(finals g') - set(finals g). |vertices f| = n"
apply(auto simp add:generatePolygon_def image_def)
apply(rename_tac "is")
apply(frule enumerator_length2)
 apply arith
apply(frule (4) pre_subdivFace_indexToVertexList)
 apply(arith)
apply(subgoal_tac "indexToVertexList f v is \<noteq> []")
 prefer 2 apply(subst length_0_conv[symmetric]) apply simp
apply(simp add: subdivFace_subdivFace'_eq)
apply(clarsimp simp:neq_Nil_conv)
apply(rename_tac "ovs")
apply(subgoal_tac "|indexToVertexList f v is| = |ovs| + 1")
 prefer 2 apply(simp)
apply(drule (1) pre_subdivFace_pre_subdivFace')
apply(drule (1) final_subdivFace')
  apply(simp add:nonFinals_def)
 apply(simp add:pre_subdivFace'_def)
apply (simp (no_asm_use))
apply(simp)
apply blast
done


(* Could prove = instead of \<ge>, but who needs it? *)
lemma genPoly_incr_facesquander_lb:
assumes "g' \<in> set (generatePolygon n v f g)" "inv g"
        "f \<in> set(nonFinals g)" "v \<in> \<V> f" "3 \<le> n"
shows "faceSquanderLowerBound g' \<ge> faceSquanderLowerBound g + \<d> n"
proof -
  from genPoly_new_face[OF assms(1) inv_mgp[OF assms(2)] assms(3-5)] obtain f
    where f: "f \<in> set (finals g') - set(finals g)"
    and size: "|vertices f| = n" by auto
  have g': "g' \<in> set(next_plane0 (n - 3) g)" using assms(5)
    by(rule_tac in_next_plane0I[OF assms(1,3-5)]) simp
  note dist = minGraphProps11'[OF inv_mgp[OF assms(2)]]
  note inv' = invariantE[OF inv_inv_next_plane0, OF g' assms(2)]
  note dist' = minGraphProps11'[OF inv_mgp[OF inv']]
  note subset = next_plane0_finals_subset[OF g']
  have "faceSquanderLowerBound g' \<ge>
        faceSquanderLowerBound g + \<d> |vertices f|"
  proof(unfold faceSquanderLowerBound_def)
    have "(\<Sum>\<^bsub>f\<in>finals g\<^esub> \<d> |vertices f| ) + \<d> |vertices f| =
          (\<Sum>f\<in>set(finals g). \<d> |vertices f| ) + \<d> |vertices f|"
      using dist by(simp add:finals_def ListSum_conv_sum)
    also have "\<dots> = (\<Sum>f\<in>set(finals g) \<union> {f}. \<d> |vertices f| )"
      using f by simp
    also have "\<dots> \<le> (\<Sum>f\<in>set(finals g'). \<d> |vertices f| )"
      using f subset by(fastforce intro!: sum_mono2)
    also have "\<dots> = (\<Sum>\<^bsub>f\<in>finals g'\<^esub> \<d> |vertices f| )"
      using dist' by(simp add:finals_def ListSum_conv_sum)
    finally show "(\<Sum>\<^bsub>f\<in>finals g\<^esub> \<d> |vertices f| ) + \<d> |vertices f|
          \<le> (\<Sum>\<^bsub>f\<in>finals g'\<^esub> \<d> |vertices f| )" .
  qed
  with size show ?thesis by blast
qed


definition close :: "graph \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> bool" where
"close g u v \<equiv>
 \<exists>f \<in> set(facesAt g u). if |vertices f| = 4 then v = f \<bullet> u \<or> v = f \<bullet> (f \<bullet> u)
                        else v = f \<bullet> u"

(* FIXME This should be the def of delAround *)
lemma delAround_def: "deleteAround g u ps = [p \<leftarrow> ps. \<not> close g u (fst p)]"
by (induct ps) (auto simp: deleteAroundCons close_def)


lemma close_sym: assumes mgp: "minGraphProps g" and ug: "u : \<V> g" and cl: "close g u v"
shows "close g v u"
proof -
  obtain f where f: "f \<in> set(facesAt g u)" and
    "if": "if |vertices f| = 4 then v = f \<bullet> u \<or> v = f \<bullet> (f \<bullet> u) else v = f \<bullet> u"
    using cl by (unfold close_def) blast
  note uf = minGraphProps6[OF mgp ug f]
  note distf = minGraphProps3[OF mgp minGraphProps5[OF mgp ug f]]
  show ?thesis
  proof cases
    assume 4: "|vertices f| = 4"
    hence "v = f \<bullet> u \<or> v = f \<bullet> (f \<bullet> u)" using "if" by simp
    thus ?thesis
    proof
      assume "v = f \<bullet> u"
      then obtain f' where "f' \<in> set(facesAt g v)" "f' \<bullet> v = u"
        using mgp_nextVertex_face_ex2[OF mgp ug f] by blast
      thus ?thesis by(auto simp:close_def)
    next
      assume v: "v = f \<bullet> (f \<bullet> u)"
      hence "f \<bullet> (f \<bullet> v) = u" using quad_next4_id[OF 4 distf uf] by simp
      moreover have "f \<in> set(facesAt g v)" using v uf
        by(simp add: minGraphProps7[OF mgp minGraphProps5[OF mgp ug f]])
      ultimately show ?thesis using 4 by(auto simp:close_def)
    qed
  next
    assume "|vertices f| \<noteq> 4"
    hence "v = f \<bullet> u" using "if" by simp
    then obtain f' where "f' \<in> set(facesAt g v)" "f' \<bullet> v = u"
      using mgp_nextVertex_face_ex2[OF mgp ug f] by blast
    thus ?thesis by(auto simp:close_def)
  qed
qed


lemma sep_conv:
assumes mgp: "minGraphProps g" and "V \<subseteq> \<V> g"
shows "separated g V = (\<forall>u\<in>V.\<forall>v\<in>V. u \<noteq> v \<longrightarrow> \<not> close g u v)" (is "?P = ?Q")
proof
  assume sep: ?P
  show ?Q
  proof(clarify)
    fix u v assume uv: "u \<in> V" "v \<in> V" "u \<noteq> v" and cl: "close g u v"
    from cl obtain f where f: "f \<in> set(facesAt g u)" and
      "if": "if |vertices f| = 4 then (v = f \<bullet> u) \<or> (v = f \<bullet> (f \<bullet> u))
                               else (v = f \<bullet> u)"
      by (unfold close_def) blast
    have "u : \<V> g" using \<open>u : V\<close> \<open>V \<subseteq> \<V> g\<close> by blast
    note uf = minGraphProps6[OF mgp \<open>u : \<V> g\<close> f]
    show False
    proof cases
      assume 4: "|vertices f| = 4"
      hence "v = f \<bullet> u \<or> v = f \<bullet> (f \<bullet> u)" using "if" by simp
      thus False
      proof
        assume "v = f \<bullet> u"
        thus False using sep f uv
          by(simp add:separated_def separated\<^sub>2_def separated\<^sub>3_def)
      next
        assume "v = f \<bullet> (f \<bullet> u)"
        moreover hence "v \<in> \<V> f" using \<open>u \<in> \<V> f\<close> by simp
        moreover have "|vertices f| \<le> 4" using 4 by arith
        ultimately show False using sep f uv \<open>u \<in> \<V> f\<close>
          apply(unfold separated_def separated\<^sub>2_def separated\<^sub>3_def)
(* why does blast get stuck? *)
          apply(subgoal_tac "f \<bullet> (f \<bullet> u) \<in> \<V> f \<inter> V")
          prefer 2 apply blast
          by simp
      qed
    next
      assume 4: "|vertices f| \<noteq> 4"
      hence "v = f \<bullet> u" using "if" by simp
      thus False using sep f uv
        by(simp add:separated_def separated\<^sub>2_def separated\<^sub>3_def)
    qed
  qed
next
  assume not_cl: ?Q
  show ?P
  proof(simp add:separated_def, rule conjI)
    show "separated\<^sub>2 g V"
    proof (clarsimp simp:separated\<^sub>2_def)
      fix v f assume a: "v \<in> V" "f \<in> set (facesAt g v)" "f \<bullet> v \<in> V"
      have "v : \<V> g" using a(1) \<open>V \<subseteq> \<V> g\<close> by blast
      show False using a not_cl mgp_facesAt_no_loop[OF mgp \<open>v : \<V> g\<close> a(2)]
        by(fastforce simp: close_def split:if_split_asm)
    qed
    show "separated\<^sub>3 g V"
    proof (clarsimp simp:separated\<^sub>3_def)
      fix v f
      assume "v \<in> V" and f: "f \<in> set (facesAt g v)" and len: "|vertices f| \<le> 4"
      have vg: "v : \<V> g" using \<open>v : V\<close> \<open>V \<subseteq> \<V> g\<close> by blast
      note distf = minGraphProps3[OF mgp minGraphProps5[OF mgp vg f]]
      note vf = minGraphProps6[OF mgp vg f]
      { fix u assume "u \<in> \<V> f" and "u \<in> V"
        have "u = v"
        proof cases
          assume 3: "|vertices f| = 3"
          hence "\<V> f = {v, f \<bullet> v, f \<bullet> (f \<bullet> v)}"
            using vertices_triangle[OF _ vf distf] by simp
          moreover
          { assume "u = f \<bullet> v"
            hence "u = v"
              using not_cl f \<open>u \<in> V\<close> \<open>v \<in> V\<close> 3
              by(force simp:close_def split:if_split_asm)
          }
          moreover
          { assume "u = f \<bullet> (f \<bullet> v)"
            hence fu: "f \<bullet> u = v"
              by(simp add: tri_next3_id[OF 3 distf \<open>v \<in> \<V> f\<close>])
            hence "(u,v) \<in> \<E> f" using nextVertex_in_edges[OF \<open>u \<in> \<V> f\<close>]
              by(simp add:fu)
            then obtain f' where "f' \<in> set(facesAt g v)" "(v,u) \<in>  \<E> f'"
              using mgp_edge_face_ex[OF mgp vg f] by blast
            hence "u = v" using not_cl \<open>u \<in> V\<close> \<open>v \<in> V\<close> 3
              by(force simp:close_def edges_face_eq split:if_split_asm)
          }
          ultimately show "u=v" using \<open>u \<in> \<V> f\<close> by blast
        next
          assume 3: "|vertices f| \<noteq> 3"
          hence 4: "|vertices f| = 4"
            using len mgp_vertices3[OF mgp minGraphProps5[OF mgp vg f]] by arith
          hence "\<V> f = {v, f \<bullet> v, f \<bullet> (f \<bullet> v), f \<bullet> (f \<bullet> (f \<bullet> v))}"
            using vertices_quad[OF _ vf distf] by simp
          moreover
          { assume "u = f \<bullet> v"
            hence "u = v"
              using not_cl f \<open>u \<in> V\<close> \<open>v \<in> V\<close> 4
              by(force simp:close_def split:if_split_asm)
          }
          moreover
          { assume "u = f \<bullet> (f \<bullet> v)"
            hence "u = v"
              using not_cl f \<open>u \<in> V\<close> \<open>v \<in> V\<close> 4
              by(force simp:close_def split:if_split_asm)
          }
          moreover
          { assume "u = f \<bullet> (f \<bullet> (f \<bullet> v))"
            hence fu: "f \<bullet> u = v"
              by(simp add: quad_next4_id[OF 4 distf \<open>v \<in> \<V> f\<close>])
            hence "(u,v) \<in> \<E> f" using nextVertex_in_edges[OF \<open>u \<in> \<V> f\<close>]
              by(simp add:fu)
            then obtain f' where "f' \<in> set(facesAt g v)" "(v,u) \<in>  \<E> f'"
              using mgp_edge_face_ex[OF mgp vg f] by blast
            hence "u = v" using not_cl \<open>u \<in> V\<close> \<open>v \<in> V\<close> 4
              by(force simp:close_def edges_face_eq split:if_split_asm)
          }
          ultimately show "u=v" using \<open>u \<in> \<V> f\<close> by blast
        qed
      }
      thus "\<V> f \<inter> V = {v}" using \<open>v \<in> V\<close> vf by blast
    qed
  qed
qed

lemma sep_ne: "\<exists>P \<subseteq> M. separated g (fst ` P)"
by(unfold separated_def separated\<^sub>2_def separated\<^sub>3_def) blast

lemma ExcessNotAtRec_conv_Max:
assumes mgp: "minGraphProps g"
shows "set(map fst ps) \<subseteq> \<V> g \<Longrightarrow> distinct(map fst ps) \<Longrightarrow>
  ExcessNotAtRec ps g =
  Max{ \<Sum>p\<in>P. snd p |P. P \<subseteq> set ps \<and> separated g (fst ` P)}"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> _ = Max(?M ps)" is "_ \<Longrightarrow> _ \<Longrightarrow> _ = Max{_ |P. ?S ps P}")
proof(induct ps rule: length_induct)
  case (1 ps0)
  note IH = 1(1) and subset = 1(2) and dist = 1(3)
  show ?case
  proof (cases ps0)
    case Nil thus ?thesis by simp
  next
    case (Cons p ps)
    let ?ps = "deleteAround g (fst p) ps"
    have le: "|?ps| \<le> |ps|" by(simp add:delAround_def)
    have dist': "distinct(map fst ?ps)" using dist Cons
      apply (clarsimp simp:delAround_def)
      apply(drule distinct_filter[where P = "Not \<circ> close g (fst p)"])
      apply(simp add: filter_map o_def)
      done
    have "fst p : \<V> g" and "fst ` set ps \<subseteq> \<V> g"
      using subset Cons by auto
    have sub1: "\<And>P Q. P \<subseteq> {x : set ps. Q x} \<Longrightarrow> fst ` P \<subseteq> \<V> g"
      using subset Cons by auto
    have sub2: "\<And>P Q. P \<subseteq> insert p {x : set ps. Q x} \<Longrightarrow> fst ` P \<subseteq> \<V> g"
      using subset Cons by auto
    have sub3: "\<And>P. P \<subseteq> insert p (set ps) \<Longrightarrow> fst ` P \<subseteq> \<V> g"
      using subset Cons by auto
    have "\<And>a. set (map fst (deleteAround g a ps)) \<subseteq> \<V> g"
      using deleteAround_subset[of g _ ps] subset Cons
      by auto
    hence "ExcessNotAtRec ps0 g = max (Max(?M ps)) (Max(?M ?ps) + snd p)"
      using Cons IH subset le dist dist' by (cases p) simp
    also have "Max (?M ?ps) + snd p =
      Max {(\<Sum>p\<in>P. snd p) + snd p | P. ?S ?ps P}"
      by (auto simp add:setcompr_eq_image Max_add_commute[symmetric] sep_ne intro!: arg_cong [where f=Max])
    also have "{(\<Sum>p\<in>P. snd p) + snd p |P. ?S ?ps P} =
      {sum snd (insert p P) |P. ?S ?ps P}"
      using dist Cons
      apply (auto simp:delAround_def)
      apply(rule_tac x=P in exI)
      apply(fastforce intro!: sum.insert[THEN trans,symmetric] elim: finite_subset)
      apply(rule_tac x=P in exI)
      apply(fastforce intro!: sum.insert[THEN trans] elim: finite_subset)
      done
    also have "\<dots> = {sum snd P |P.
            P \<subseteq> insert p (set ?ps) \<and> p \<in> P \<and> separated g (fst ` P)}"
      apply(auto simp add:sep_conv[OF mgp] sub1 sub2 delAround_def cong: conj_cong)
      apply(rule_tac x = "insert p P" in exI)
      apply simp
      apply(rule conjI) apply blast
      using \<open>image fst (set ps) \<subseteq> \<V> g\<close> \<open>fst p : \<V> g\<close>
      apply (blast intro:close_sym[OF mgp])
      apply(rule_tac x = "P-{p}" in exI)
      apply (simp add:insert_absorb)
      apply blast
      done
    also have "\<dots> = {sum snd P |P.
            P \<subseteq> insert p (set ps) \<and> p \<in> P \<and> separated g (fst ` P)}"
      using Cons dist
      apply(auto simp add:sep_conv[OF mgp] sub2 sub3 delAround_def cong: conj_cong)
      apply(rule_tac x = "P" in exI)
      apply simp
      apply auto
      done
    also have "max (Max(?M ps)) (Max \<dots>) = Max(?M ps \<union> {sum snd P |P.
            P \<subseteq> insert p (set ps) \<and> p \<in> P \<and> separated g (fst ` P)})"
      (is "_ = Max ?U")
    proof -
      have "{sum snd P |P.
            P \<subseteq> insert p (set ps) \<and> p \<in> P \<and> separated g (fst ` P)} \<noteq> {}"
        apply simp
        apply(rule_tac x="{p}" in exI)
        using \<open>fst p : \<V> g\<close> by(simp add:sep_conv[OF mgp])
      thus ?thesis by(simp add: Max_Un sep_ne)
    qed
    also have "?U = ?M ps0" using Cons by simp blast
    finally show ?thesis .
  qed
qed


lemma dist_ExcessTab: "distinct (map fst (ExcessTable g (vertices g)))"
by(simp add:ExcessTable_def vertices_graph o_def)



lemma mono_ExcessTab: "\<lbrakk>g' \<in> set (next_plane0\<^bsub>p\<^esub> g); inv g \<rbrakk> \<Longrightarrow>
  set(ExcessTable g (vertices g)) \<subseteq> set(ExcessTable g' (vertices g'))"
apply(clarsimp simp:ExcessTable_def image_def)
apply(rule conjI)
 apply(blast dest:next_plane0_vertices_subset inv_mgp)
apply (clarsimp simp:ExcessAt_def split:if_split_asm)
apply(frule (3) next_plane0_finalVertex_mono)
apply(simp add: next_plane0_len_filter_eq tri_def quad_def except_def)
done


lemma close_antimono:
 "\<lbrakk>g' \<in> set (next_plane0\<^bsub>p\<^esub> g); inv g; u \<in> \<V> g; finalVertex g u \<rbrakk> \<Longrightarrow>
  close g' u v \<Longrightarrow> close g u v"
by(simp add:close_def next_plane0_finalVertex_facesAt_eq)

lemma ExcessTab_final:
 "p \<in> set(ExcessTable g (vertices g)) \<Longrightarrow> finalVertex g (fst p)"
by(clarsimp simp:ExcessTable_def image_def ExcessAt_def split:if_split_asm)

lemma ExcessTab_vertex:
 "p \<in> set(ExcessTable g (vertices g)) \<Longrightarrow> fst p \<in> \<V> g"
by(clarsimp simp:ExcessTable_def image_def ExcessAt_def split:if_split_asm)

lemma fst_set_ExcessTable_subset:
 "fst ` set (ExcessTable g (vertices g)) \<subseteq> \<V> g"
by(clarsimp simp:ExcessTable_def image_def ExcessAt_def split:if_split_asm)

lemma next_plane0_incr_ExcessNotAt:
 "\<lbrakk>g' \<in> set (next_plane0\<^bsub>p\<^esub> g); inv g \<rbrakk> \<Longrightarrow>
  ExcessNotAt g None \<le> ExcessNotAt g' None"
apply(frule (1) invariantE[OF inv_inv_next_plane0])
apply(frule (1) mono_ExcessTab)
apply(simp add: ExcessNotAt_def ExcessNotAtRec_conv_Max[OF _ _ dist_ExcessTab]
  fst_set_ExcessTable_subset)
apply(rule Max_mono)
  prefer 2 apply (simp add: sep_ne)
 prefer 2 apply (simp)
apply auto
apply(rule_tac x=P in exI)
apply auto
apply(subgoal_tac "fst ` P \<subseteq> \<V> g'")
 prefer 2 apply (blast dest: ExcessTab_vertex)
apply(subgoal_tac "fst ` P \<subseteq> \<V> g")
 prefer 2 apply (blast dest: ExcessTab_vertex)
apply(simp add:sep_conv)
apply (blast intro:close_antimono ExcessTab_final ExcessTab_vertex)
done
(* close -> in neibhood ?? *)


lemma next_plane0_incr_squander_lb:
 "\<lbrakk>g' \<in> set (next_plane0\<^bsub>p\<^esub> g); inv g \<rbrakk> \<Longrightarrow>
  squanderLowerBound g \<le> squanderLowerBound g'"
apply(simp add:squanderLowerBound_def)
apply(frule (1) next_plane0_incr_ExcessNotAt)
apply(clarsimp simp add:next_plane0_def split:if_split_asm)
apply(drule (4) genPoly_incr_facesquander_lb)
apply arith
done

lemma inv_notame:
 "\<lbrakk>g' \<in> set (next_plane0\<^bsub>p\<^esub> g); inv g; notame7 g\<rbrakk>
  \<Longrightarrow> notame7 g'"
apply(simp add:notame_def notame7_def tame11b_def is_tame13a_def tame10ub_def del:disj_not1)
apply(frule inv_mgp)
apply(frule (1) next_plane0_vertices_subset)
apply(erule disjE)
 apply(simp add:vertices_graph)
apply(rule disjI2)
apply(erule disjE)
 apply clarify
 apply(frule (2) next_plane0_incr_degree)
 apply(frule (2) next_plane0_incr_except)
 apply (force split:if_split_asm)
apply(frule (1) next_plane0_incr_squander_lb)
apply(arith)
done


lemma inv_inv_notame:
 "invariant(\<lambda>g. inv g \<and> notame7 g) next_plane\<^bsub>p\<^esub>"
apply(simp add:invariant_def)
apply(blast intro: inv_notame mgp_next_plane0_if_next_plane[OF inv_mgp]
       invariantE[OF inv_inv_next_plane])
done


lemma untame_notame:
 "untame (\<lambda>g. inv g \<and> notame7 g)"
proof(clarsimp simp add: notame_def notame7_def untame_def tame11b_def is_tame13a_def tame10ub_def
                         linorder_not_le linorder_not_less)
  fix g assume "final g" "inv g" "tame g"
    and cases: "15 < countVertices g \<or>
                (\<exists>v\<in>\<V> g. (except g v = 0 \<longrightarrow> 7 < degree g v) \<and>
                            (0 < except g v \<longrightarrow> 6 < degree g v))
                \<or> squanderTarget \<le> squanderLowerBound g"
                (is "?A \<or> ?B \<or> ?C" is "_ \<or> (\<exists>v\<in>\<V> g. ?B' v) \<or> _")
  from cases show False
  proof(elim disjE)
    assume ?B
    then obtain v where v: "v \<in>\<V> g" "?B' v" by auto
    show False
    proof cases
      assume "except g v = 0"
      thus False using \<open>tame g\<close> v by(auto simp: tame_def tame11b_def)
    next
      assume "except g v \<noteq> 0"
      thus False using \<open>tame g\<close> v
        by(auto simp: except_def filter_empty_conv tame_def tame11b_def
          minGraphProps_facesAt_eq[OF inv_mgp[OF \<open>inv g\<close>]] split:if_split_asm)
    qed
  next
    assume ?A
    thus False using \<open>tame g\<close>  by(simp add:tame_def tame10_def)
  next
    assume ?C
    thus False using total_weight_lowerbound[OF \<open>inv g\<close> \<open>final g\<close> \<open>tame g\<close>]
      \<open>tame g\<close>  by(force simp add:tame_def tame13a_def)
  qed
qed


lemma polysizes_tame:
 "\<lbrakk> g' \<in> set (generatePolygon n v f g); inv g; f \<in> set(nonFinals g);
   v \<in> \<V> f; 3 \<le> n; n < 4+p; n \<notin> set(polysizes p g) \<rbrakk>
 \<Longrightarrow> notame7 g'"
apply(frule (4) in_next_plane0I)
apply(frule (4) genPoly_incr_facesquander_lb)
apply(frule (1) next_plane0_incr_ExcessNotAt)
apply(simp add: notame_def notame7_def is_tame13a_def faceSquanderLowerBound_def
           polysizes_def squanderLowerBound_def)
done

lemma genPolyTame_notame:
 "\<lbrakk> g' \<in> set (generatePolygon n v f g); g' \<notin> set (generatePolygonTame n v f g);
    inv g; 3 \<le> n \<rbrakk>
  \<Longrightarrow> notame7 g'"
by(fastforce simp:generatePolygon_def generatePolygonTame_def enum_enumerator
                 notame_def notame7_def)

declare upt_Suc[simp del] (* FIXME global? *)
lemma excess_notame:
 "\<lbrakk> inv g; g' \<in> set (next_plane\<^bsub>p\<^esub> g); g' \<notin> set (next_tame0 p g) \<rbrakk>
       \<Longrightarrow> notame7 g'"
apply(frule (1) mgp_next_plane0_if_next_plane[OF inv_mgp])
apply(auto simp add:next_tame0_def next_plane_def split:if_split_asm)
apply(rename_tac n)
apply(case_tac "n \<in> set(polysizes p g)")
 apply(drule bspec) apply assumption
 apply(simp add:genPolyTame_notame)
apply(subgoal_tac "minimalFace (nonFinals g) \<in> set(nonFinals g)")
 prefer 2 apply(simp add:minimalFace_def)
apply(subgoal_tac "minimalVertex g (minimalFace (nonFinals g)) \<in> \<V>(minimalFace (nonFinals g))")
 apply(blast intro:polysizes_tame)
apply(simp add:minimalVertex_def)
apply(rule minimal_in_set)
apply(erule mgp_vertices_nonempty[OF inv_mgp])
apply(simp add:nonFinals_def)
done
declare upt_Suc[simp]


lemma next_tame0_comp: "\<lbrakk> Seed\<^bsub>p\<^esub> [next_plane p]\<rightarrow>* g; final g; tame g \<rbrakk>
 \<Longrightarrow> Seed\<^bsub>p\<^esub> [next_tame0 p]\<rightarrow>* g"
apply(rule filterout_untame_succs[OF inv_inv_next_plane inv_inv_notame
  untame_notame])
    apply(blast intro:excess_notame)
   apply assumption
  apply(rule inv_Seed)
 apply assumption
apply assumption
done

lemma inv_inv_next_tame0: "invariant inv (next_tame0 p)"
by(rule inv_subset[OF inv_inv_next_plane next_tame0_subset_plane])

lemma inv_inv_next_tame: "invariant inv next_tame\<^bsub>p\<^esub>"
apply(simp add:next_tame_def)
apply(rule inv_subset[OF inv_inv_next_tame0])
apply auto
done

lemma mgp_TameEnum: "g \<in> TameEnum\<^bsub>p\<^esub> \<Longrightarrow> minGraphProps g"
by (unfold TameEnumP_def)
   (blast intro: RTranCl_inv[OF inv_inv_next_tame] inv_Seed inv_mgp)


end
