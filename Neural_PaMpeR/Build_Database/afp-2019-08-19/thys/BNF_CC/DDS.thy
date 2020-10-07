(* Author: Andreas Lochbihler, ETH Zurich
   Author: Joshua Schneider, ETH Zurich *)

section \<open>Example: deterministic discrete system\<close>

theory DDS imports
  Concrete_Examples
  "HOL-Library.Rewrite"
  "HOL-Library.FSet"
begin

unbundle lifting_syntax

subsection \<open>Definition and generalised mapper and relator\<close>

codatatype ('a, 'b) dds = DDS (run: "'a \<Rightarrow> 'b \<times> ('a, 'b) dds")
  for map: map_dds'
      rel: rel_dds'

primcorec map_dds :: "('a' \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b') \<Rightarrow> ('a, 'b) dds \<Rightarrow> ('a', 'b') dds" where
  "run (map_dds f g S) = (\<lambda>a. map_prod g (map_dds f g) (run S (f a)))"

lemma map_dds_id: "map_dds id id S = S"
  by(coinduction arbitrary: S)(auto simp add: rel_fun_def prod.rel_map intro: prod.rel_refl_strong)

lemma map_dds_comp: "map_dds f g (map_dds f' g' S) = map_dds (f' \<circ> f) (g \<circ> g') S"
  by(coinduction arbitrary: S)(auto simp add: rel_fun_def prod.rel_map intro: prod.rel_refl_strong)

coinductive rel_dds :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b' \<Rightarrow> bool) \<Rightarrow> ('a, 'b) dds \<Rightarrow> ('a', 'b') dds \<Rightarrow> bool"
  for A B where
  "rel_dds A B S S'" if "rel_fun A (rel_prod B (rel_dds A B)) (run S) (run S')"

lemma rel_dds'_rel_dds: "rel_dds' B = rel_dds (=) B"
  apply (intro ext iffI)
   apply (erule rel_dds.coinduct)
   apply (erule dds.rel_cases)
   apply (simp)
   apply (erule rel_fun_mono[THEN predicate2D, OF order_refl, rotated -1])
   apply (rule prod.rel_mono[OF order_refl])
   apply (blast)
  apply (erule dds.rel_coinduct)
  apply (erule rel_dds.cases)
  apply (simp)
  done

lemma rel_dds_eq [relator_eq]: "rel_dds (=) (=) = (=)"
  apply(rule ext iffI)+
  subgoal by(erule dds.coinduct)(erule rel_dds.cases; simp)
  subgoal by(erule rel_dds.coinduct)(auto simp add: rel_fun_def intro!: prod.rel_refl_strong)
  done

lemma rel_dds_mono [relator_mono]: "rel_dds A B \<le> rel_dds A' B'" if "A' \<le> A" "B \<le> B'"
  apply(rule predicate2I)
  apply(erule rel_dds.coinduct)
  apply(erule rel_dds.cases)
  apply simp
  apply(erule BNF_Def.rel_fun_mono)
   apply(auto intro: that[THEN predicate2D])
  done

lemma rel_dds_conversep: "rel_dds A\<inverse>\<inverse> B\<inverse>\<inverse> = (rel_dds A B)\<inverse>\<inverse>"
  apply(intro ext iffI; simp)
  subgoal
    apply(erule rel_dds.coinduct; erule rel_dds.cases; simp del: conversep_iff)
    apply(rewrite conversep_iff[symmetric])
    apply(fold rel_fun_conversep prod.rel_conversep)
    apply(erule BNF_Def.rel_fun_mono)
     apply(auto simp del: conversep_iff)
    done
  subgoal
    apply(erule rel_dds.coinduct; erule rel_dds.cases; clarsimp simp del: conversep_iff)
    apply(rewrite in asm conversep_iff[symmetric])
    apply(fold rel_fun_conversep prod.rel_conversep)
    apply(erule BNF_Def.rel_fun_mono)
     apply(auto simp del: conversep_iff)
    done
  done

lemma DDS_parametric [transfer_rule]:
  "((A ===> rel_prod B (rel_dds A B)) ===> rel_dds A B) DDS DDS"
  by(auto intro!: rel_dds.intros)

lemma run_parametric [transfer_rule]:
  "(rel_dds A B ===> A ===> rel_prod B (rel_dds A B)) run run"
  by(auto elim: rel_dds.cases)

lemma corec_dds_parametric [transfer_rule]:
  "((S ===> A ===> rel_prod B (rel_sum (rel_dds A B) S)) ===> S ===> rel_dds A B) corec_dds corec_dds"
  apply(rule rel_funI)+
  subgoal premises prems for f g s s' using prems(2)
    apply(coinduction arbitrary: s s')
    apply simp
    apply(rule comp_transfer[THEN rel_funD, THEN rel_funD, rotated])
     apply(erule prems(1)[THEN rel_funD])
    apply(rule prod.map_transfer[THEN rel_funD, THEN rel_funD, OF id_transfer])
    apply(fastforce elim!: rel_sum.cases)
    done
  done

lemma map_dds_parametric [transfer_rule]:
  "((A' ===> A) ===> (B ===> B') ===> rel_dds A B ===> rel_dds A' B') map_dds map_dds"
  unfolding map_dds_def by transfer_prover

lemmas map_dds_rel_cong = map_dds_parametric[unfolded rel_fun_def, rule_format, rotated -1]

lemma rel_dds_Grp:
  "rel_dds (Grp UNIV f)\<inverse>\<inverse> (Grp UNIV g) = Grp UNIV (map_dds f g)"
  apply(rule ext iffI)+
   apply(simp add: Grp_apply)
   apply(rule sym)
   apply(fold rel_dds_eq)
   apply(rewrite in "rel_dds _ _ _ \<hole>" map_dds_id[symmetric])
   apply(erule map_dds_parametric[THEN rel_funD, THEN rel_funD, THEN rel_funD, rotated -1];
      simp add: Grp_apply rel_fun_def)
  apply(erule GrpE; clarsimp)
  apply(rewrite in "rel_dds _ _ \<hole>" map_dds_id[symmetric])
  apply(rule map_dds_parametric[THEN rel_funD, THEN rel_funD, THEN rel_funD, rotated -1])
    apply(subst rel_dds_eq; simp)
   apply(simp_all add: Grp_apply rel_fun_def)
  done

lemma rel_dds_pos_distr [relator_distr]:
  "rel_dds A B OO rel_dds C D \<le> rel_dds (A OO C) (B OO D)"
  apply (rule predicate2I)
  apply (erule relcomppE)
  subgoal for x y z
    apply (coinduction arbitrary: x y z)
    apply (simp)
    apply (rule rel_fun_mono[THEN predicate2D, OF order_refl,
          of "rel_prod B (rel_dds A B) OO rel_prod D (rel_dds C D)"])
     apply (rule order_trans)
      apply (rule prod.rel_compp[symmetric, THEN eq_refl])
     apply (rule prod.rel_mono[OF order_refl])
     apply (blast)
    apply (rule rel_fun_pos_distr[THEN predicate2D])
     apply (simp)
    apply (rule relcomppI)
     apply (auto elim: rel_dds.cases)
    done
  done

lemma Quotient_dds [quot_map]:
  assumes "Quotient R1 Abs1 Rep1 T1" and "Quotient R2 Abs2 Rep2 T2"
  shows "Quotient (rel_dds R1 R2) (map_dds Rep1 Abs2) (map_dds Abs1 Rep2) (rel_dds T1 T2)"
  unfolding Quotient_alt_def5
proof (intro conjI, goal_cases)
  case 1
  have "rel_dds T1 T2 \<le> rel_dds (Grp UNIV Rep1)\<inverse>\<inverse> (Grp UNIV Abs2)"
    apply (rule rel_dds_mono)
     apply (rule assms(1)[unfolded Quotient_alt_def5, THEN conjunct2, THEN conjunct1,
          unfolded conversep_le_swap])
    apply (rule assms(2)[unfolded Quotient_alt_def5, THEN conjunct1])
    done
  also have "... = Grp UNIV (map_dds Rep1 Abs2)" using rel_dds_Grp .
  finally show ?case .
next
  case 2
  have "Grp UNIV (map_dds Abs1 Rep2) = rel_dds (Grp UNIV Abs1)\<inverse>\<inverse> (Grp UNIV Rep2)"
    using rel_dds_Grp[symmetric] .
  also have "... \<le> rel_dds T1\<inverse>\<inverse> T2\<inverse>\<inverse>"
    apply (rule rel_dds_mono)
     apply (simp)
     apply (rule assms(1)[unfolded Quotient_alt_def5, THEN conjunct1])
    apply (rule assms(2)[unfolded Quotient_alt_def5, THEN conjunct2, THEN conjunct1])
    done
  finally show ?case by (simp add: rel_dds_conversep)
next
  case 3
  show ?case
    apply (rule antisym)
     apply (rule predicate2I)
     apply (rule relcomppI)
      apply (subst map_dds_id[symmetric])
      apply (erule map_dds_rel_cong)
       apply (simp_all)[2]
       apply (erule assms(1)[THEN Quotient_rep_equiv1])
      apply (erule assms(2)[THEN Quotient_equiv_abs1])
     apply (subst rel_dds_conversep[symmetric])
    subgoal for x y
      apply (subgoal_tac "map_dds Rep1 Abs2 y = map_dds Rep1 Abs2 x")
       apply (simp)
       apply (subst (3) map_dds_id[symmetric])
       apply (erule map_dds_rel_cong)
        apply (simp_all)
        apply (erule assms(1)[THEN Quotient_rep_equiv2])
       apply (erule assms(2)[THEN Quotient_equiv_abs2])
      apply (rule sym)
      apply (subst rel_dds_eq[symmetric])
      apply (erule map_dds_rel_cong)
       apply (simp, rule assms(1)[THEN Quotient_rep_reflp])
      apply (erule assms(2)[THEN Quotient_rel_abs])
      done
    apply (unfold rel_dds_conversep[symmetric]
        assms[unfolded Quotient_alt_def5, THEN conjunct2, THEN conjunct2])
    apply (rule rel_dds_pos_distr)
    done
qed


text \<open>This is just the co-iterator.\<close>

primcorec dds_of :: "('s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's)) \<Rightarrow> 's \<Rightarrow> ('a, 'b) dds" where
  "run (dds_of f s) = map_prod id (dds_of f) \<circ> f s"

lemma dds_of_parametric [transfer_rule]:
  "((S ===> A ===> rel_prod B S) ===> S ===> rel_dds A B) dds_of dds_of"
  unfolding dds_of_def by transfer_prover


subsection \<open>Evenness of partial sums\<close>

definition even_psum :: "(int, bool) dds" where
  "even_psum = dds_of (\<lambda>psum n. (even (psum + n), psum + n)) 0"

definition even_psum_nat :: "(nat, bool) dds" where
  "even_psum_nat = map_dds int id even_psum"


subsection \<open>Composition\<close>

primcorec compose :: "('a, 'b) dds \<Rightarrow> ('b, 'c) dds \<Rightarrow> ('a, 'c) dds" (infixl "\<bullet>" 120) where
  "run (S1 \<bullet> S2) = (\<lambda>a. let (b, S1') = run S1 a; (c, S2') = run S2 b in (c, S1' \<bullet> S2'))"

lemma compose_parametric [transfer_rule]:
  "(rel_dds A B ===> rel_dds B C ===> rel_dds A C) (\<bullet>) (\<bullet>)"
  unfolding compose_def by transfer_prover

text \<open>
  For the following lemma, a direct proof by induction is easy as the inner functor of
  the @{type dds} codatatype is fairly simple.
\<close>

lemma "map_dds f g S1 \<bullet> S2 = map_dds f id (S1 \<bullet> map_dds g id S2)"
  apply(coinduction arbitrary: S1 S2)
  apply(auto simp add: case_prod_map_prod rel_fun_def split: prod.split)
  done

text \<open>However, we can also follow the systematic route via parametricity:\<close>

lemma compose_map1: "map_dds f g S1 \<bullet> S2 = map_dds f id (S1 \<bullet> map_dds g id S2)"
  for S1 :: "('a, 'b) dds" and S2 :: "('b, 'c) dds"
  using compose_parametric[of "(Grp UNIV f)\<inverse>\<inverse>" "Grp UNIV g" "Grp UNIV id :: 'c \<Rightarrow> 'c \<Rightarrow> bool"]
  apply(rewrite in "_ ===> rel_dds \<hole> _ ===> _" in asm conversep_conversep[symmetric])
  apply(rewrite in "_ ===> rel_dds _ \<hole> ===> _" in asm conversep_Grp_id[symmetric])
  apply(simp only: rel_dds_conversep rel_dds_Grp)
  apply(simp add: rel_fun_def Grp_apply)
  done

lemma compose_map2: "S1 \<bullet> map_dds f g S2 = map_dds id g (map_dds id f S1 \<bullet> S2)"
  for S1 :: "('a, 'b) dds" and S2 :: "('b, 'c) dds"
  using compose_parametric[of "Grp UNIV id :: 'a \<Rightarrow> 'a \<Rightarrow> bool" "(Grp UNIV f)\<inverse>\<inverse>" "Grp UNIV g"]
  apply(rewrite in "rel_dds \<hole> _ ===> _" in asm conversep_conversep[symmetric])
  apply(rewrite in "_ ===> _ ===> rel_dds \<hole> _" in asm conversep_Grp_id[symmetric])
  apply(simp only: rel_dds_conversep rel_dds_Grp)
  apply(simp add: rel_fun_def Grp_apply)
  done

primcorec parallel :: "('a, 'b) dds \<Rightarrow> ('c, 'd) dds \<Rightarrow> ('a + 'c, 'b + 'd) dds" (infixr "\<parallel>" 130) where
  "run (S1 \<parallel> S2) = (\<lambda>x. case x of
     Inl a \<Rightarrow> let (b, S1') = run S1 a in (Inl b, S1' \<parallel> S2)
   | Inr c \<Rightarrow> let (d, S2') = run S2 c in (Inr d, S1 \<parallel> S2'))"

lemma parallel_parametric [transfer_rule]:
  "(rel_dds A B ===> rel_dds C D ===> rel_dds (rel_sum A C) (rel_sum B D)) (\<parallel>) (\<parallel>)"
  unfolding parallel_def by transfer_prover

lemma map_parallel:
  "map_dds f h S1 \<parallel> map_dds g k S2 = map_dds (map_sum f g) (map_sum h k) (S1 \<parallel> S2)"
  using parallel_parametric[where A="(Grp UNIV f)\<inverse>\<inverse>" and B="Grp UNIV h" and
      C="(Grp UNIV g)\<inverse>\<inverse>" and D="Grp UNIV k"]
  by(simp add: sum.rel_conversep sum.rel_Grp rel_dds_Grp)(simp add: rel_fun_def Grp_apply)


subsection \<open>Graph traversal: refinement and quotients\<close>

lemma finite_Image:
  "finite A \<Longrightarrow> finite (R `` A) \<longleftrightarrow> (\<forall>x\<in>A. finite {y. (x, y) \<in> R})"
  by(simp add: Image_def)

context includes fset.lifting begin
lift_definition fImage :: "('a \<times> 'b) fset \<Rightarrow> 'a fset \<Rightarrow> 'b fset" is Image parametric Image_parametric
  by(auto simp add: finite_Image intro: finite_subset[OF _ finite_imageI])

lemmas fImage_iff = Image_iff[Transfer.transferred]
lemmas fImageI [intro] = ImageI[Transfer.transferred]
lemmas fImageE [elim!] = ImageE[Transfer.transferred]
lemmas rev_fImageI = rev_ImageI[Transfer.transferred]
lemmas fImage_mono = Image_mono[Transfer.transferred]

lifting_update fset.lifting
lifting_forget fset.lifting
end

type_synonym 'a graph = "('a \<times> 'a) fset"

definition traverse :: "'a graph \<Rightarrow> ('a fset, 'a fset) dds" where
  "traverse E = dds_of (\<lambda>visited A. ((fImage E A) |-| visited, visited |\<union>| A)) {||}"

type_synonym 'a graph' = "('a \<times> 'a) list"

definition traverse_impl :: "'a graph' \<Rightarrow> ('a list, 'a list) dds" where
  "traverse_impl E =
   dds_of (\<lambda>visited A. (map snd [(x, y)\<leftarrow>E . x \<in> set A \<and> y |\<notin>| visited],
    visited |\<union>| fset_of_list A)) {||}"

definition list_fset_rel :: "'a list \<Rightarrow> 'a fset \<Rightarrow> bool" where
  "list_fset_rel xs A \<longleftrightarrow> fset_of_list xs = A"

lemma traverse_refinement: \<comment> \<open>This is the refinement lemma.\<close>
  "(list_fset_rel ===> rel_dds list_fset_rel list_fset_rel) traverse_impl traverse"
  unfolding traverse_impl_def traverse_def
  apply(rule rel_funI)
  apply(rule dds_of_parametric[where S="(=)", THEN rel_funD, THEN rel_funD])
   apply(auto simp add: rel_fun_def list_fset_rel_def fset_of_list_elem intro: rev_fimage_eqI)
  done

lemma fset_of_list_parametric [transfer_rule]:
  "(list_all2 A ===> rel_fset A) fset_of_list fset_of_list"
  including fset.lifting unfolding rel_fun_def
  by transfer(rule list.set_transfer[unfolded rel_fun_def])

lemma traverse_impl_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(list_all2 (rel_prod A A) ===> rel_dds (list_all2 A) (list_all2 A)) traverse_impl traverse_impl"
  unfolding traverse_impl_def by transfer_prover


text \<open>
  By constructing finite sets as a quotient of lists, we can synthesise an abstract version
  of @{const traverse_impl} automatically, together with a polymorphic refinement lemma.
\<close>

quotient_type 'a fset' = "'a list" / "vimage2p set set (=)"
  by (auto intro: equivpI reflpI sympI transpI simp add: vimage2p_def)

lift_definition traverse'' :: "('a \<times> 'a) fset' \<Rightarrow> ('a fset', 'a fset') dds"
  is "traverse_impl :: 'a graph' \<Rightarrow> _" parametric traverse_impl_parametric
  unfolding traverse_impl_def
  apply (rule dds_of_parametric[where S="(=)", THEN rel_funD, THEN rel_funD])
   apply (auto simp add: rel_fun_def vimage2p_def fset_of_list_elem)
  done

subsection \<open>Generalised rewriting\<close>

definition accumulate :: "('a fset, 'a fset) dds" where
  "accumulate = dds_of (\<lambda>A X. (A |\<union>| X, A |\<union>| X)) {||}"

lemma accumulate_mono: "rel_dds (|\<subseteq>|) (|\<subseteq>|) accumulate accumulate"
  unfolding accumulate_def
  apply (rule dds_of_parametric[THEN rel_funD, THEN rel_funD, of "(|\<subseteq>|)"])
   apply (intro rel_funI rel_prod.intros)
    apply (erule (1) funion_mono)+
  apply (simp)
  done

lemma traverse_mono: "((|\<subseteq>|) ===> rel_dds (=) (|\<subseteq>|)) traverse traverse"
  unfolding traverse_def
  apply (rule rel_funI)
  apply (rule dds_of_parametric[THEN rel_funD, THEN rel_funD, of "(=)"])
   apply (intro rel_funI rel_prod.intros)
    apply (simp)
    apply (rule fminus_mono)
     apply (erule fImage_mono)
     apply (simp_all)
  done

lemma
  assumes "G |\<subseteq>| H"
  shows "rel_dds (=) (|\<subseteq>|) (traverse G \<bullet> accumulate) (traverse H \<bullet> accumulate)"
  apply (rule compose_parametric[THEN rel_funD, THEN rel_funD])
   apply (rule traverse_mono[THEN rel_funD])
   apply (rule assms)
  apply (rule accumulate_mono)
  done

definition seen :: "('a fset, 'a fset) dds" where
  "seen = dds_of (\<lambda>S X. (S |\<inter>| X, S |\<union>| X)) {||}"

lemma seen_mono: "rel_dds (|\<subseteq>|) (|\<subseteq>|) seen seen"
  unfolding seen_def
  apply (rule dds_of_parametric[THEN rel_funD, THEN rel_funD, of "(|\<subseteq>|)"])
   apply (intro rel_funI rel_prod.intros)
    apply (erule (1) finter_mono funion_mono)+
  apply (simp)
  done

lemma
  assumes "G |\<subseteq>| H"
  shows "rel_dds (=) (|\<subseteq>|) (traverse G \<bullet> seen) (traverse H \<bullet> seen)"
  apply (rule compose_parametric[THEN rel_funD, THEN rel_funD])
   apply (rule traverse_mono[THEN rel_funD])
   apply (rule assms)
  apply (rule seen_mono)
  done

end