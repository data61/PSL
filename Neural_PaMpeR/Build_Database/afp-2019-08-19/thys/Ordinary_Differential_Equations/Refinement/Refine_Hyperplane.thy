theory
  Refine_Hyperplane
imports
  Autoref_Misc
  Affine_Arithmetic.Print
  Ordinary_Differential_Equations.Reachability_Analysis
  Refine_Vector_List
begin

lemma convex_halfspace[simp]:
  "convex (below_halfspace sctn)"
  apply (auto simp: below_halfspace_def le_halfspace_def[abs_def])
  using convex_bound_le
  apply (auto intro!: convexI simp: algebra_simps)
  by blast

subsection \<open>Planes\<close>

definition "shows_sctn (sctn::real list sctn) =
  shows ''Sctn '' o shows_paren (shows_words (normal sctn)) o shows_space o
    shows_paren (shows (pstn sctn))"

lemma halfspaces_union:
  "sbelow_halfspaces (a \<union> b) = sbelow_halfspaces a \<inter> sbelow_halfspaces b"
  "below_halfspaces (a \<union> b) = below_halfspaces a \<inter> below_halfspaces b"
  by (auto simp: halfspace_simps)

lemma plane_of_subset_halfspace: "plane_of sctn \<subseteq> below_halfspace sctn"
  by (auto simp: plane_of_def below_halfspace_def le_halfspace_def)

lemma halfspace_subsets: "sbelow_halfspaces sctns \<subseteq> below_halfspaces sctns"
  and halfspace_subset: "sbelow_halfspace sctn \<subseteq> below_halfspace sctn"
  by (force simp: plane_of_def halfspace_simps)+

lemma sbelow_halfspaces_insert:
  "sbelow_halfspaces (insert x2 stop_sctns) = sbelow_halfspace x2 \<inter> sbelow_halfspaces stop_sctns"
  by (auto simp: sbelow_halfspaces_def)

lemma sbelow_halfspaces_antimono:
  assumes "A \<subseteq> B"
  shows "sbelow_halfspaces B \<subseteq> sbelow_halfspaces A"
  using assms
  by (auto simp: halfspace_simps)

lemma plane_in_halfspace[intro, simp]:
  "x \<in> plane_of sctn \<Longrightarrow> x \<in> below_halfspace sctn"
  "x \<in> plane_of sctn \<Longrightarrow> x \<in> above_halfspace sctn"
  by (auto simp: halfspace_simps plane_of_def)

lemma closure_shalfspace[intro, simp]:
  assumes "normal sctn \<noteq> 0"
  shows "closure (sbelow_halfspace sctn) = below_halfspace sctn"
    and "closure (sabove_halfspace sctn) = above_halfspace sctn"
  using closure_halfspace_lt[OF assms] closure_halfspace_gt[OF assms]
  by (auto simp: halfspace_simps inner_commute)

lemma closure_sbelow_halfspaces[intro, simp]:
  assumes "\<And>sctn. sctn \<in> sctns \<Longrightarrow> normal sctn \<noteq> 0"
  shows "closure (sbelow_halfspaces sctns) \<subseteq> below_halfspaces sctns"
proof -
  have *: "{closure S |S. S \<in> sbelow_halfspace ` sctns} = {S |S. S \<in> below_halfspace ` sctns}"
    by (auto simp: assms intro!: closure_shalfspace(1) [symmetric] exI)
  show ?thesis
    unfolding sbelow_halfspaces_def
    by (rule order_trans [OF closure_Int]) (auto simp: halfspace_simps * cong del: image_cong_simp)
qed

lemma halfspaces_empty[simp]: "sbelow_halfspaces {} = UNIV" "below_halfspaces {} = UNIV"
  by (auto simp: halfspace_simps)

lemma halfspaces_planeI:
  assumes "x \<in> below_halfspaces (s)"
  assumes "x \<notin> \<Union>(plane_of ` (s))"
  shows "x \<in> sbelow_halfspaces (s)"
  using assms
  by (force simp: halfspace_simps plane_of_def)


subsection \<open>Section\<close>

definition sctn_rel where sctn_rel_internal: "sctn_rel A = {(a, b). rel_sctn (in_rel A) a b}"
lemma sctn_rel_def: "\<langle>A\<rangle>sctn_rel = {(a, b). rel_sctn (in_rel A) a b}"
  by (auto simp: sctn_rel_internal relAPP_def)

lemma single_valued_sctn_rel[relator_props]: "single_valued A \<Longrightarrow> single_valued (\<langle>A\<rangle>sctn_rel)"
  using sctn.right_unique_rel[of "in_rel A"]
  by (auto simp: single_valued_def right_unique_def sctn_rel_def)

consts i_sctn :: "interface \<Rightarrow> interface" \<comment> \<open>section datatype\<close>

consts i_halfspace :: "interface \<Rightarrow> interface"

lemmas [autoref_rel_intf] = REL_INTFI[of sctn_rel i_sctn]


abbreviation "sctns_rel \<equiv> \<langle>\<langle>lv_rel\<rangle>sctn_rel\<rangle>list_set_rel"

definition plane_rel_internal: "plane_rel A = \<langle>A\<rangle>sctn_rel O br plane_of top"
lemma plane_rel_def: "\<langle>A\<rangle>plane_rel = \<langle>A\<rangle>sctn_rel O br plane_of top"
  by (simp add: plane_rel_internal relAPP_def)
consts i_plane::"interface\<Rightarrow>interface"
lemmas [autoref_rel_intf] = REL_INTFI[of plane_rel i_plane]

definition below_rel_internal: "below_rel A = \<langle>A\<rangle>sctn_rel O br below_halfspace top"
lemma below_rel_def: "\<langle>A\<rangle>below_rel = \<langle>A\<rangle>sctn_rel O br below_halfspace top"
  by (simp add: below_rel_internal relAPP_def)
consts i_below::"interface\<Rightarrow>interface"
lemmas [autoref_rel_intf] = REL_INTFI[of below_rel i_below]

definition sbelow_rel_internal: "sbelow_rel A = \<langle>A\<rangle>sctn_rel O br sbelow_halfspace top"
lemma sbelow_rel_def: "\<langle>A\<rangle>sbelow_rel = \<langle>A\<rangle>sctn_rel O br sbelow_halfspace top"
  by (simp add: sbelow_rel_internal relAPP_def)
consts i_sbelow::"interface\<Rightarrow>interface"
lemmas [autoref_rel_intf] = REL_INTFI[of sbelow_rel i_sbelow]

definition sbelows_rel_internal: "sbelows_rel A = \<langle>\<langle>A\<rangle>sctn_rel\<rangle>list_set_rel O br sbelow_halfspaces top"
lemma sbelows_rel_def: "\<langle>A\<rangle>sbelows_rel = \<langle>\<langle>A\<rangle>sctn_rel\<rangle>list_set_rel O br sbelow_halfspaces top"
  by (simp add: sbelows_rel_internal relAPP_def)
consts i_sbelows::"interface\<Rightarrow>interface"
lemmas [autoref_rel_intf] = REL_INTFI[of sbelows_rel i_sbelows]

context includes autoref_syntax begin

lemma plane_of_autoref[autoref_rules]:
  "(\<lambda>x. x, plane_of) \<in> \<langle>A\<rangle>sctn_rel \<rightarrow> \<langle>A\<rangle>plane_rel"
  by (auto simp: plane_rel_def intro!: brI)

lemma below_halfspace_autoref[autoref_rules]:
  "(\<lambda>x. x, below_halfspace) \<in> \<langle>A\<rangle>sctn_rel \<rightarrow> \<langle>A\<rangle>below_rel"
  by (auto simp: below_rel_def intro!: brI)

lemma sbelow_halfspace_autoref[autoref_rules]:
  "(\<lambda>x. x, sbelow_halfspace) \<in> \<langle>A\<rangle>sctn_rel \<rightarrow> \<langle>A\<rangle>sbelow_rel"
  by (auto simp: sbelow_rel_def intro!: brI)

lemma sbelow_halfspaces_autoref[autoref_rules]:
  "(\<lambda>x. x, sbelow_halfspaces) \<in> \<langle>\<langle>A\<rangle>sctn_rel\<rangle>list_set_rel \<rightarrow> \<langle>A\<rangle>sbelows_rel"
  by (auto simp: sbelows_rel_def intro!: brI)


end


context includes autoref_syntax begin
lemma [autoref_rules]:
  shows
  "(Sctn, Sctn) \<in> A \<rightarrow> rnv_rel \<rightarrow> \<langle>A\<rangle>sctn_rel"
  "(normal, normal) \<in> \<langle>A\<rangle>sctn_rel \<rightarrow> A"
  "(pstn, pstn) \<in> \<langle>A\<rangle>sctn_rel \<rightarrow> rnv_rel"
  by (auto simp: sctn_rel_def sctn.rel_sel)

lemma gen_eq_sctn[autoref_rules]:
  assumes "GEN_OP eq (=) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(\<lambda>sctn1 sctn2. eq (normal sctn1) (normal sctn2) \<and> pstn sctn1 = pstn sctn2, (=)) \<in> \<langle>A\<rangle>sctn_rel \<rightarrow> \<langle>A\<rangle>sctn_rel \<rightarrow> bool_rel"
  apply safe
  subgoal for a b c d
    using assms
    by (cases a; cases b; cases c; cases d) (auto simp: sctn_rel_def dest: fun_relD)
  subgoal for a b c d
    using assms
    by (cases a; cases b; cases c; cases d) (auto simp: sctn_rel_def dest: fun_relD)
  subgoal for a b c d
    using assms
    by (cases a; cases b; cases c; cases d) (auto simp: sctn_rel_def dest: fun_relD)
  done

lemma inter_sctn_specs_inter_sctn_spec:
  "(inter_sctn_specs d, inter_sctn_spec::'a::executable_euclidean_space set\<Rightarrow>_) \<in> \<langle>lv_rel\<rangle>set_rel \<rightarrow> \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>\<langle>lv_rel\<rangle>set_rel\<rangle>nres_rel"
  if "d = DIM('a)"
  apply (auto intro!: nres_relI RES_refine
      simp: inter_sctn_specs_def inter_sctn_spec_def set_rel_sv[OF lv_rel_sv] plane_ofs_def plane_of_def that)
  subgoal for a b c d e f
    apply (cases b; cases c)
    apply (rule ImageI, assumption)
    apply (auto simp: lv_rel_def br_def sctn_rel_def plane_of_def)
    apply (rule subsetD, assumption)
    apply auto
    subgoal for x1
      using lv_rel_inner[param_fo, OF lv_relI lv_relI, of f x1]
      by auto
    done
  subgoal for a b c d e f
    apply (cases b; cases c)
    apply (auto simp: sctn_rel_def lv_rel_def br_def)
    apply (drule rev_subsetD, assumption)
    subgoal for x1 x2
      using lv_rel_inner[where 'a = 'a, param_fo, OF lv_relI lv_relI, of f x1]
      by auto
    done
  by (auto simp: sctn_rel_def lv_rel_def br_def env_len_def)

lemma sctn_rel_comp: "\<langle>A\<rangle>sctn_rel O \<langle>B\<rangle>sctn_rel = \<langle>A O B\<rangle> sctn_rel"
  apply safe
  subgoal for a b c d e
    apply (cases c; cases d; cases d; cases e)
    by (auto simp: sctn_rel_def )
  subgoal for a b
    apply (cases a; cases b)
    apply (auto simp: sctn_rel_def )
    subgoal for c d e f
      apply (rule relcompI[where b="Sctn e c"])
       apply auto
      done
    done
  done

lemma sctn_rel: "\<langle>lv_rel\<rangle>sctn_rel \<subseteq> \<langle>\<langle>rnv_rel\<rangle>list_rel\<rangle>sctn_rel O \<langle>lv_rel\<rangle>sctn_rel"
  "\<langle>\<langle>rnv_rel\<rangle>list_rel\<rangle>sctn_rel O \<langle>lv_rel\<rangle>sctn_rel \<subseteq> \<langle>lv_rel\<rangle>sctn_rel"
  using sctn_rel_comp[of "\<langle>rnv_rel\<rangle>list_rel" lv_rel] by auto

definition halfspace_rel_internal: "halfspaces_rel R = \<langle>\<langle>R\<rangle>sctn_rel\<rangle>list_set_rel O br below_halfspaces top"
lemma halfspaces_rel_def: "\<langle>R\<rangle>halfspaces_rel = \<langle>\<langle>R\<rangle>sctn_rel\<rangle>list_set_rel O br below_halfspaces top"
  by (auto simp: relAPP_def halfspace_rel_internal)

lemmas [autoref_rel_intf] = REL_INTFI[of halfspaces_rel i_halfspace]

lemma below_halfspaces_autoref[autoref_rules]:
  "(\<lambda>x. x, below_halfspaces) \<in> \<langle>\<langle>R\<rangle>sctn_rel\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>halfspaces_rel"
  by (auto simp: halfspaces_rel_def br_def)

end

lemma plane_rel_br: "\<langle>br a I\<rangle>plane_rel = br (plane_of o map_sctn a) (\<lambda>x. I (normal x))"
  apply (auto simp: plane_rel_def sctn_rel_def br_def)
  subgoal for x y z by (cases x; cases y) auto
  subgoal for x y z by (cases x; cases y) auto
  subgoal for x y by (cases x; cases y) auto
  subgoal for a by (cases a; force)
  done


lemma closed_subset_plane[intro]:
  "closed b \<Longrightarrow> closed {x \<in> b. x \<in> plane_of c}"
  "closed b \<Longrightarrow> closed {x \<in> b. x \<bullet> n = d}"
  by (auto simp: plane_of_def intro!: closed_levelset_within continuous_intros)

end