section \<open>\isaheader{Generic Set Algorithms}\<close>
theory Gen_Set
imports "../Intf/Intf_Set" "../../Iterator/Iterator"
begin

  lemma foldli_union: "det_fold_set X (\<lambda>_. True) insert a ((\<union>) a)"
  proof (rule, goal_cases)
    case (1 l) thus ?case
      by (induct l arbitrary: a) auto
  qed

  definition gen_union
    :: "_ \<Rightarrow> ('k \<Rightarrow> 's2 \<Rightarrow> 's2) 
        \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> 's2"
    where 
    "gen_union it ins A B \<equiv> it A (\<lambda>_. True) ins B"

  lemma gen_union[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes INS: "GEN_OP ins Set.insert (Rk\<rightarrow>\<langle>Rk\<rangle>Rs2\<rightarrow>\<langle>Rk\<rangle>Rs2)"
    assumes IT: "SIDE_GEN_ALGO (is_set_to_list Rk Rs1 tsl)"
    shows "(gen_union (\<lambda>x. foldli (tsl x)) ins,(\<union>)) 
    \<in> (\<langle>Rk\<rangle>Rs1) \<rightarrow> (\<langle>Rk\<rangle>Rs2) \<rightarrow> (\<langle>Rk\<rangle>Rs2)"
    apply (intro fun_relI)
    apply (subst Un_commute)
    unfolding gen_union_def 
    apply (rule det_fold_set[OF 
      foldli_union IT[unfolded autoref_tag_defs]])
    using INS
    unfolding autoref_tag_defs
    apply (parametricity)+
    done

  lemma foldli_inter: "det_fold_set X (\<lambda>_. True) 
    (\<lambda>x s. if x\<in>a then insert x s else s) {} (\<lambda>s. s\<inter>a)" 
    (is "det_fold_set _ _ ?f _ _")
  proof -
    {
      fix l s0
      have "foldli l (\<lambda>_. True) 
        (\<lambda>x s. if x\<in>a then insert x s else s) s0 = s0 \<union> (set l \<inter> a)"
        by (induct l arbitrary: s0) auto
    }
    from this[of _ "{}"] show ?thesis apply - by rule simp
  qed

  definition gen_inter :: "_ \<Rightarrow> 
    ('k \<Rightarrow> 's2 \<Rightarrow> bool) \<Rightarrow> _"
    where "gen_inter it1 memb2 ins3 empty3 s1 s2 
    \<equiv> it1 s1 (\<lambda>_. True) 
      (\<lambda>x s. if memb2 x s2 then ins3 x s else s) empty3"

  lemma gen_inter[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_set_to_list Rk Rs1 tsl)"
    assumes MEMB:
      "GEN_OP memb2 (\<in>) (Rk \<rightarrow> \<langle>Rk\<rangle>Rs2 \<rightarrow> Id)"
    assumes INS: 
      "GEN_OP ins3 Set.insert (Rk\<rightarrow>\<langle>Rk\<rangle>Rs3\<rightarrow>\<langle>Rk\<rangle>Rs3)"
    assumes EMPTY: 
      "GEN_OP empty3 {} (\<langle>Rk\<rangle>Rs3)"
    shows "(gen_inter (\<lambda>x. foldli (tsl x)) memb2 ins3 empty3,(\<inter>)) 
    \<in> (\<langle>Rk\<rangle>Rs1) \<rightarrow> (\<langle>Rk\<rangle>Rs2) \<rightarrow> (\<langle>Rk\<rangle>Rs3)"
    apply (intro fun_relI)
    unfolding gen_inter_def
    apply (rule det_fold_set[OF foldli_inter IT[unfolded autoref_tag_defs]])
    using MEMB INS EMPTY
    unfolding autoref_tag_defs
    apply (parametricity)+
    done
 
  lemma foldli_diff: 
    "det_fold_set X (\<lambda>_. True) (\<lambda>x s. op_set_delete x s) s ((-) s)"
  proof (rule, goal_cases)
    case (1 l) thus ?case
      by (induct l arbitrary: s) auto
  qed

  definition gen_diff :: "('k\<Rightarrow>'s1\<Rightarrow>'s1) \<Rightarrow> _ \<Rightarrow> 's2 \<Rightarrow> _ "
    where "gen_diff del1 it2 s1 s2 
    \<equiv> it2 s2 (\<lambda>_. True) (\<lambda>x s. del1 x s) s1"

  lemma gen_diff[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes DEL:
      "GEN_OP del1 op_set_delete (Rk \<rightarrow> \<langle>Rk\<rangle>Rs1 \<rightarrow> \<langle>Rk\<rangle>Rs1)"
    assumes IT: "SIDE_GEN_ALGO (is_set_to_list Rk Rs2 it2)"
    shows "(gen_diff del1 (\<lambda>x. foldli (it2 x)),(-)) 
      \<in> (\<langle>Rk\<rangle>Rs1) \<rightarrow> (\<langle>Rk\<rangle>Rs2) \<rightarrow> (\<langle>Rk\<rangle>Rs1)"
    apply (intro fun_relI)
    unfolding gen_diff_def 
    apply (rule det_fold_set[OF foldli_diff IT[unfolded autoref_tag_defs]])
    using DEL
    unfolding autoref_tag_defs
    apply (parametricity)+
    done

  lemma foldli_ball_aux: 
    "foldli l (\<lambda>x. x) (\<lambda>x _. P x) b \<longleftrightarrow> b \<and> Ball (set l) P"
    by (induct l arbitrary: b) auto

  lemma foldli_ball: "det_fold_set X (\<lambda>x. x) (\<lambda>x _. P x) True (\<lambda>s. Ball s P)"
    apply rule using foldli_ball_aux[where b=True] by simp

  definition gen_ball :: "_ \<Rightarrow> 's \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> _ "
    where "gen_ball it s P \<equiv> it s (\<lambda>x. x) (\<lambda>x _. P x) True"

  lemma gen_ball[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_set_to_list Rk Rs it)"
    shows "(gen_ball (\<lambda>x. foldli (it x)),Ball) \<in> \<langle>Rk\<rangle>Rs \<rightarrow> (Rk\<rightarrow>Id) \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_ball_def
    apply (rule det_fold_set[OF foldli_ball IT[unfolded autoref_tag_defs]])
    apply (parametricity)+
    done

  lemma foldli_bex_aux: "foldli l (\<lambda>x. \<not>x) (\<lambda>x _. P x) b \<longleftrightarrow> b \<or> Bex (set l) P"
    by (induct l arbitrary: b) auto

  lemma foldli_bex: "det_fold_set X (\<lambda>x. \<not>x) (\<lambda>x _. P x) False (\<lambda>s. Bex s P)"
    apply rule using foldli_bex_aux[where b=False] by simp

  definition gen_bex :: "_ \<Rightarrow> 's \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> _ "
    where "gen_bex it s P \<equiv> it s (\<lambda>x. \<not>x) (\<lambda>x _. P x) False"

  lemma gen_bex[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_set_to_list Rk Rs it)"
    shows "(gen_bex (\<lambda>x. foldli (it x)),Bex) \<in> \<langle>Rk\<rangle>Rs \<rightarrow> (Rk\<rightarrow>Id) \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_bex_def 
    apply (rule det_fold_set[OF foldli_bex IT[unfolded autoref_tag_defs]])
    apply (parametricity)+
    done

  lemma ball_subseteq:
    "(Ball s1 (\<lambda>x. x\<in>s2)) \<longleftrightarrow> s1 \<subseteq> s2"
    by blast

  definition gen_subseteq 
    :: "('s1 \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> 's2 \<Rightarrow> bool) \<Rightarrow> _" 
    where "gen_subseteq ball1 mem2 s1 s2 \<equiv> ball1 s1 (\<lambda>x. mem2 x s2)"

  lemma gen_subseteq[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes "GEN_OP ball1 Ball (\<langle>Rk\<rangle>Rs1 \<rightarrow> (Rk\<rightarrow>Id) \<rightarrow> Id)"
    assumes "GEN_OP mem2 (\<in>) (Rk \<rightarrow> \<langle>Rk\<rangle>Rs2 \<rightarrow> Id)"
    shows "(gen_subseteq ball1 mem2,(\<subseteq>)) \<in> \<langle>Rk\<rangle>Rs1 \<rightarrow> \<langle>Rk\<rangle>Rs2 \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_subseteq_def using assms
    unfolding autoref_tag_defs
    apply -
    apply (subst ball_subseteq[symmetric])
    apply parametricity
    done

  definition "gen_equal ss1 ss2 s1 s2 \<equiv> ss1 s1 s2 \<and> ss2 s2 s1"

  lemma gen_equal[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes "GEN_OP ss1 (\<subseteq>) (\<langle>Rk\<rangle>Rs1 \<rightarrow> \<langle>Rk\<rangle>Rs2 \<rightarrow> Id)"
    assumes "GEN_OP ss2 (\<subseteq>) (\<langle>Rk\<rangle>Rs2 \<rightarrow> \<langle>Rk\<rangle>Rs1 \<rightarrow> Id)"
    shows "(gen_equal ss1 ss2, (=)) \<in> \<langle>Rk\<rangle>Rs1 \<rightarrow> \<langle>Rk\<rangle>Rs2 \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_equal_def using assms
    unfolding autoref_tag_defs
    apply -
    apply (subst set_eq_subset)
    apply (parametricity)
    done

  lemma foldli_card_aux: "distinct l \<Longrightarrow> foldli l (\<lambda>_. True) 
    (\<lambda>_ n. Suc n) n = n + card (set l)"
    apply (induct l arbitrary: n) 
    apply auto
    done
  
  lemma foldli_card: "det_fold_set X (\<lambda>_. True) (\<lambda>_ n. Suc n) 0 card"
    apply rule using foldli_card_aux[where n=0] by simp

  definition gen_card where
    "gen_card it s \<equiv> it s (\<lambda>x. True) (\<lambda>_ n. Suc n) 0"

  lemma gen_card[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_set_to_list Rk Rs it)"
    shows "(gen_card (\<lambda>x. foldli (it x)),card) \<in> \<langle>Rk\<rangle>Rs \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_card_def
    apply (rule det_fold_set[OF foldli_card IT[unfolded autoref_tag_defs]])
    apply (parametricity)+
    done

  lemma fold_set: "fold Set.insert l s = s \<union> set l"
    by (induct l arbitrary: s) auto

  definition gen_set :: "'s \<Rightarrow> ('k \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> _" where
    "gen_set emp ins l = fold ins l emp"

  lemma gen_set[autoref_rules_raw]: 
    assumes PRIO_TAG_GEN_ALGO
    assumes EMPTY: 
      "GEN_OP emp {} (\<langle>Rk\<rangle>Rs)"
    assumes INS: 
      "GEN_OP ins Set.insert (Rk\<rightarrow>\<langle>Rk\<rangle>Rs\<rightarrow>\<langle>Rk\<rangle>Rs)"
    shows "(gen_set emp ins,set)\<in>\<langle>Rk\<rangle>list_rel\<rightarrow>\<langle>Rk\<rangle>Rs"
    apply (intro fun_relI)
    unfolding gen_set_def using assms
    unfolding autoref_tag_defs
    apply -
    apply (subst fold_set[where s="{}",simplified,symmetric])
    apply parametricity
    done
    
  lemma ball_isEmpty: "op_set_isEmpty s = (\<forall>x\<in>s. False)"
    by auto

  definition gen_isEmpty :: "('s \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" where
    "gen_isEmpty ball s \<equiv> ball s (\<lambda>_. False)"

  lemma gen_isEmpty[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes "GEN_OP ball Ball (\<langle>Rk\<rangle>Rs \<rightarrow> (Rk\<rightarrow>Id) \<rightarrow> Id)"
    shows "(gen_isEmpty ball,op_set_isEmpty) \<in> \<langle>Rk\<rangle>Rs \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_isEmpty_def using assms
    unfolding autoref_tag_defs
    apply -
    apply (subst ball_isEmpty)
    apply parametricity
    done
  
  lemma foldli_size_abort_aux:
    "\<lbrakk>n0\<le>m; distinct l\<rbrakk> \<Longrightarrow> 
      foldli l (\<lambda>n. n<m) (\<lambda>_ n. Suc n) n0 = min m (n0 + card (set l))"
    apply (induct l arbitrary: n0)
    apply auto
    done

  lemma foldli_size_abort: "
    det_fold_set X (\<lambda>n. n<m) (\<lambda>_ n. Suc n) 0 (op_set_size_abort m)"
    apply rule
    using foldli_size_abort_aux[where ?n0.0=0]
    by simp

  definition gen_size_abort where
    "gen_size_abort it m s \<equiv> it s (\<lambda>n. n<m) (\<lambda>_ n. Suc n) 0"

  lemma gen_size_abort[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_set_to_list Rk Rs it)"
    shows "(gen_size_abort (\<lambda>x. foldli (it x)),op_set_size_abort) 
    \<in> Id \<rightarrow> \<langle>Rk\<rangle>Rs \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_size_abort_def 
    apply (rule det_fold_set[OF foldli_size_abort IT[unfolded autoref_tag_defs]])
    apply (parametricity)+
    done
    
  lemma size_abort_isSng: "op_set_isSng s \<longleftrightarrow> op_set_size_abort 2 s = 1"
    by auto 

  definition gen_isSng :: "(nat \<Rightarrow> 's \<Rightarrow> nat) \<Rightarrow> _" where
    "gen_isSng sizea s \<equiv> sizea 2 s = 1"

  lemma gen_isSng[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes "GEN_OP sizea op_set_size_abort (Id \<rightarrow> (\<langle>Rk\<rangle>Rs) \<rightarrow> Id)"
    shows "(gen_isSng sizea,op_set_isSng) \<in> \<langle>Rk\<rangle>Rs \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_isSng_def using assms
    unfolding autoref_tag_defs
    apply -
    apply (subst size_abort_isSng)
    apply parametricity
    done
    
  lemma foldli_disjoint_aux:
    "foldli l1 (\<lambda>x. x) (\<lambda>x _. \<not>x\<in>s2) b \<longleftrightarrow> b \<and> op_set_disjoint (set l1) s2"
    by (induct l1 arbitrary: b) auto

  lemma foldli_disjoint: 
    "det_fold_set X (\<lambda>x. x) (\<lambda>x _. \<not>x\<in>s2) True (\<lambda>s1. op_set_disjoint s1 s2)"
    apply rule using foldli_disjoint_aux[where b=True] by simp

  definition gen_disjoint 
    :: "_ \<Rightarrow> ('k\<Rightarrow>'s2\<Rightarrow>bool) \<Rightarrow> _"
    where "gen_disjoint it1 mem2 s1 s2 
    \<equiv> it1 s1 (\<lambda>x. x) (\<lambda>x _. \<not>mem2 x s2) True"

  lemma gen_disjoint[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_set_to_list Rk Rs1 it1)"
    assumes MEM: "GEN_OP mem2 (\<in>) (Rk \<rightarrow> \<langle>Rk\<rangle>Rs2 \<rightarrow> Id)"
    shows "(gen_disjoint (\<lambda>x. foldli (it1 x)) mem2,op_set_disjoint) 
    \<in> \<langle>Rk\<rangle>Rs1 \<rightarrow> \<langle>Rk\<rangle>Rs2 \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_disjoint_def 
    apply (rule det_fold_set[OF foldli_disjoint IT[unfolded autoref_tag_defs]])
    using MEM unfolding autoref_tag_defs
    apply (parametricity)+
    done

  lemma foldli_filter_aux:
    "foldli l (\<lambda>_. True) (\<lambda>x s. if P x then insert x s else s) s0 
    = s0 \<union> op_set_filter P (set l)"
    by (induct l arbitrary: s0) auto

  lemma foldli_filter: 
    "det_fold_set X (\<lambda>_. True) (\<lambda>x s. if P x then insert x s else s) {} 
      (op_set_filter P)"
    apply rule using foldli_filter_aux[where ?s0.0="{}"] by simp

  definition gen_filter
    where "gen_filter it1 emp2 ins2 P s1 \<equiv> 
      it1 s1 (\<lambda>_. True) (\<lambda>x s. if P x then ins2 x s else s) emp2"

  lemma gen_filter[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_set_to_list Rk Rs1 it1)"
    assumes INS: 
      "GEN_OP ins2 Set.insert (Rk\<rightarrow>\<langle>Rk\<rangle>Rs2\<rightarrow>\<langle>Rk\<rangle>Rs2)"
    assumes EMPTY: 
      "GEN_OP empty2 {} (\<langle>Rk\<rangle>Rs2)"
    shows "(gen_filter (\<lambda>x. foldli (it1 x)) empty2 ins2,op_set_filter) 
    \<in> (Rk\<rightarrow>Id) \<rightarrow> (\<langle>Rk\<rangle>Rs1) \<rightarrow> (\<langle>Rk\<rangle>Rs2)"
    apply (intro fun_relI)
    unfolding gen_filter_def
    apply (rule det_fold_set[OF foldli_filter IT[unfolded autoref_tag_defs]])
    using INS EMPTY unfolding autoref_tag_defs
    apply (parametricity)+
    done

  lemma foldli_image_aux:
    "foldli l (\<lambda>_. True) (\<lambda>x s. insert (f x) s) s0
    = s0 \<union> f`(set l)"
    by (induct l arbitrary: s0) auto

  lemma foldli_image: 
    "det_fold_set X (\<lambda>_. True) (\<lambda>x s. insert (f x) s) {} 
      ((`) f)"
    apply rule using foldli_image_aux[where ?s0.0="{}"] by simp

  definition gen_image
    where "gen_image it1 emp2 ins2 f s1 \<equiv> 
      it1 s1 (\<lambda>_. True) (\<lambda>x s. ins2 (f x) s) emp2"

  lemma gen_image[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_set_to_list Rk Rs1 it1)"
    assumes INS: 
      "GEN_OP ins2 Set.insert (Rk'\<rightarrow>\<langle>Rk'\<rangle>Rs2\<rightarrow>\<langle>Rk'\<rangle>Rs2)"
    assumes EMPTY: 
      "GEN_OP empty2 {} (\<langle>Rk'\<rangle>Rs2)"
    shows "(gen_image (\<lambda>x. foldli (it1 x)) empty2 ins2,(`)) 
    \<in> (Rk\<rightarrow>Rk') \<rightarrow> (\<langle>Rk\<rangle>Rs1) \<rightarrow> (\<langle>Rk'\<rangle>Rs2)"
    apply (intro fun_relI)
    unfolding gen_image_def
    apply (rule det_fold_set[OF foldli_image IT[unfolded autoref_tag_defs]])
    using INS EMPTY unfolding autoref_tag_defs
    apply (parametricity)+
    done

  (* TODO: Also do sel! *)

  lemma foldli_pick:
    assumes "l\<noteq>[]" 
    obtains x where "x\<in>set l" 
    and "(foldli l (case_option True (\<lambda>_. False)) (\<lambda>x _. Some x) None) = Some x"
    using assms by (cases l) auto

  definition gen_pick where
    "gen_pick it s \<equiv> 
      (the (it s (case_option True (\<lambda>_. False)) (\<lambda>x _. Some x) None))"

context begin interpretation autoref_syn .
  lemma gen_pick[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_set_to_list Rk Rs it)"
    assumes NE: "SIDE_PRECOND (s'\<noteq>{})"
    assumes SREF: "(s,s')\<in>\<langle>Rk\<rangle>Rs"
    shows "(RETURN (gen_pick (\<lambda>x. foldli (it x)) s), 
      (OP op_set_pick ::: \<langle>Rk\<rangle>Rs\<rightarrow>\<langle>Rk\<rangle>nres_rel)$s')\<in>\<langle>Rk\<rangle>nres_rel"
  proof -
    obtain tsl' where
      [param]: "(it s,tsl') \<in> \<langle>Rk\<rangle>list_rel" 
      and IT': "RETURN tsl' \<le> it_to_sorted_list (\<lambda>_ _. True) s'"
      using IT[unfolded autoref_tag_defs is_set_to_list_def] SREF
      by (rule is_set_to_sorted_listE)

    from IT' NE have "tsl'\<noteq>[]" and [simp]: "s'=set tsl'" 
      unfolding it_to_sorted_list_def by simp_all
    then obtain x where "x\<in>s'" and
      "(foldli tsl' (case_option True (\<lambda>_. False)) (\<lambda>x _. Some x) None) = Some x"
      (is "?fld = _")
      by (blast elim: foldli_pick)
    moreover 
    have "(RETURN (gen_pick (\<lambda>x. foldli (it x)) s), RETURN (the ?fld)) 
      \<in> \<langle>Rk\<rangle>nres_rel"
      unfolding gen_pick_def
      apply (parametricity add: the_paramR)
      using \<open>?fld = Some x\<close>
      by simp
    ultimately show ?thesis
      unfolding autoref_tag_defs
      apply -
      apply (drule nres_relD)
      apply (rule nres_relI)
      apply (erule ref_two_step)
      by simp
  qed
end

  definition gen_Sigma
    where "gen_Sigma it1 it2 empX insX s1 f2 \<equiv> 
      it1 s1 (\<lambda>_. True) (\<lambda>x s. 
        it2 (f2 x) (\<lambda>_. True) (\<lambda>y s. insX (x,y) s) s
      ) empX
    "

  lemma foldli_Sigma_aux:
    fixes s :: "'s1_impl" and s':: "'k set"
    fixes f :: "'k_impl \<Rightarrow> 's2_impl" and f':: "'k \<Rightarrow> 'l set"
    fixes s0 :: "'kl_impl" and s0' :: "('k\<times>'l) set"
    assumes IT1: "is_set_to_list Rk Rs1 it1"
    assumes IT2: "is_set_to_list Rl Rs2 it2"
    assumes INS: 
      "(insX, Set.insert) \<in> 
        (\<langle>Rk,Rl\<rangle>prod_rel\<rightarrow>\<langle>\<langle>Rk,Rl\<rangle>prod_rel\<rangle>Rs3\<rightarrow>\<langle>\<langle>Rk,Rl\<rangle>prod_rel\<rangle>Rs3)"
    assumes S0R: "(s0, s0') \<in> \<langle>\<langle>Rk,Rl\<rangle>prod_rel\<rangle>Rs3" 
    assumes SR: "(s, s') \<in> \<langle>Rk\<rangle>Rs1" 
    assumes FR: "(f, f') \<in> Rk \<rightarrow> \<langle>Rl\<rangle>Rs2"
    shows "(foldli (it1 s) (\<lambda>_. True) (\<lambda>x s. 
        foldli (it2 (f x)) (\<lambda>_. True) (\<lambda>y s. insX (x,y) s) s
      ) s0,s0' \<union> Sigma s' f') 
      \<in> \<langle>\<langle>Rk,Rl\<rangle>prod_rel\<rangle>Rs3"
  proof -
    have S: "\<And>x s f. Sigma (insert x s) f = ({x}\<times>f x) \<union> Sigma s f"
      by auto

    obtain l' where 
      IT1L: "(it1 s,l')\<in>\<langle>Rk\<rangle>list_rel" 
      and SL: "s' = set l'"
      apply (rule 
        is_set_to_sorted_listE[OF IT1[unfolded is_set_to_list_def] SR])
      by (auto simp: it_to_sorted_list_def)

    show ?thesis
      unfolding SL
      using IT1L S0R
    proof (induct arbitrary: s0 s0' rule: list_rel_induct)
      case Nil thus ?case by simp
    next
      case (Cons x x' l l')

      obtain l2' where 
        IT2L: "(it2 (f x),l2')\<in>\<langle>Rl\<rangle>list_rel" 
        and FXL: "f' x' = set l2'"
        apply (rule 
          is_set_to_sorted_listE[
            OF IT2[unfolded is_set_to_list_def], of "f x" "f' x'"
          ])
        apply (parametricity add: Cons.hyps(1) FR)
        by (auto simp: it_to_sorted_list_def)

      have "(foldli (it2 (f x)) (\<lambda>_. True) (\<lambda>y. insX (x, y)) s0, 
        s0' \<union> {x'}\<times>f' x') \<in> \<langle>\<langle>Rk,Rl\<rangle>prod_rel\<rangle>Rs3"
        unfolding FXL 
        using IT2L \<open>(s0, s0') \<in> \<langle>\<langle>Rk, Rl\<rangle>prod_rel\<rangle>Rs3\<close>
        apply (induct  arbitrary: s0 s0' rule: list_rel_induct)
        apply simp
        apply simp
        apply (subst Un_insert_left[symmetric])
        apply (rprems)
        apply (parametricity add: INS \<open>(x,x')\<in>Rk\<close>)
        done

      show ?case
        apply simp
        apply (subst S)
        apply (subst Un_assoc[symmetric])
        apply (rule Cons.hyps)
        apply fact
        done
    qed
  qed


  lemma gen_Sigma[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT1: "SIDE_GEN_ALGO (is_set_to_list Rk Rs1 it1)"
    assumes IT2: "SIDE_GEN_ALGO (is_set_to_list Rl Rs2 it2)"
    assumes EMPTY: 
      "GEN_OP empX {} (\<langle>\<langle>Rk,Rl\<rangle>prod_rel\<rangle>Rs3)"
    assumes INS: 
      "GEN_OP insX Set.insert 
         (\<langle>Rk,Rl\<rangle>prod_rel\<rightarrow>\<langle>\<langle>Rk,Rl\<rangle>prod_rel\<rangle>Rs3\<rightarrow>\<langle>\<langle>Rk,Rl\<rangle>prod_rel\<rangle>Rs3)"
    shows "(gen_Sigma (\<lambda>x. foldli (it1 x)) (\<lambda>x. foldli (it2 x)) empX insX,Sigma) 
      \<in> (\<langle>Rk\<rangle>Rs1) \<rightarrow> (Rk \<rightarrow> \<langle>Rl\<rangle>Rs2) \<rightarrow> \<langle>\<langle>Rk,Rl\<rangle>prod_rel\<rangle>Rs3"
    apply (intro fun_relI)
    unfolding gen_Sigma_def
    using foldli_Sigma_aux[OF 
      IT1[unfolded autoref_tag_defs]
      IT2[unfolded autoref_tag_defs]
      INS[unfolded autoref_tag_defs]
      EMPTY[unfolded autoref_tag_defs]
    ]
    by simp

lemma gen_cart:
  assumes PRIO_TAG_GEN_ALGO
  assumes [param]: "(sigma, Sigma) \<in> (\<langle>Rx\<rangle>Rsx \<rightarrow> (Rx \<rightarrow> \<langle>Ry\<rangle>Rsy) \<rightarrow> \<langle>Rx \<times>\<^sub>r Ry\<rangle>Rsp)"
  shows "(\<lambda>x y. sigma x (\<lambda>_. y), op_set_cart) \<in> \<langle>Rx\<rangle>Rsx \<rightarrow> \<langle>Ry\<rangle>Rsy \<rightarrow> \<langle>Rx \<times>\<^sub>r Ry\<rangle>Rsp"
  unfolding op_set_cart_def[abs_def]
  by parametricity
lemmas [autoref_rules] = gen_cart[OF _ GEN_OP_D]


context begin interpretation autoref_syn .

  lemma op_set_to_sorted_list_autoref[autoref_rules]:
    assumes "SIDE_GEN_ALGO (is_set_to_sorted_list ordR Rk Rs tsl)"
    shows "(\<lambda>si. RETURN (tsl si),  OP (op_set_to_sorted_list ordR)) 
      \<in> \<langle>Rk\<rangle>Rs \<rightarrow> \<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel"
    using assms
    apply (intro fun_relI nres_relI)
    apply simp
    apply (rule RETURN_SPEC_refine)
    apply (auto simp: is_set_to_sorted_list_def it_to_sorted_list_def)
    done

  lemma op_set_to_list_autoref[autoref_rules]:
    assumes "SIDE_GEN_ALGO (is_set_to_sorted_list ordR Rk Rs tsl)"
    shows "(\<lambda>si. RETURN (tsl si), op_set_to_list) 
      \<in> \<langle>Rk\<rangle>Rs \<rightarrow> \<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel"
    using assms
    apply (intro fun_relI nres_relI)
    apply simp
    apply (rule RETURN_SPEC_refine)
    apply (auto simp: is_set_to_sorted_list_def it_to_sorted_list_def)
    done

end

lemma foldli_Union: "det_fold_set X (\<lambda>_. True) (\<union>) {} Union"
proof (rule, goal_cases)
  case (1 l)
  have "\<forall>a. foldli l (\<lambda>_. True) (\<union>) a = a \<union> \<Union>(set l)"
    by (induct l) auto
  thus ?case by auto
qed

definition gen_Union
  :: "_ \<Rightarrow> 's3 \<Rightarrow> ('s2 \<Rightarrow> 's3 \<Rightarrow> 's3) 
      \<Rightarrow> 's1 \<Rightarrow> 's3"
  where 
  "gen_Union it emp un X \<equiv> it X (\<lambda>_. True) un emp"

lemma gen_Union[autoref_rules_raw]:
  assumes PRIO_TAG_GEN_ALGO
  assumes EMP: "GEN_OP emp {} (\<langle>Rk\<rangle>Rs3)"
  assumes UN: "GEN_OP un (\<union>) (\<langle>Rk\<rangle>Rs2\<rightarrow>\<langle>Rk\<rangle>Rs3\<rightarrow>\<langle>Rk\<rangle>Rs3)"
  assumes IT: "SIDE_GEN_ALGO (is_set_to_list (\<langle>Rk\<rangle>Rs2) Rs1 tsl)"
  shows "(gen_Union (\<lambda>x. foldli (tsl x)) emp un,Union) \<in> \<langle>\<langle>Rk\<rangle>Rs2\<rangle>Rs1 \<rightarrow> \<langle>Rk\<rangle>Rs3"
  apply (intro fun_relI)
  unfolding gen_Union_def 
  apply (rule det_fold_set[OF 
    foldli_Union IT[unfolded autoref_tag_defs]])
  using EMP UN
  unfolding autoref_tag_defs
  apply (parametricity)+
  done

definition "atLeastLessThan_impl a b \<equiv> do {
  (_,r) \<leftarrow> WHILET (\<lambda>(i,r). i<b) (\<lambda>(i,r). RETURN (i+1, insert i r)) (a,{});
  RETURN r
}"

lemma atLeastLessThan_impl_correct: 
  "atLeastLessThan_impl a b \<le> SPEC (\<lambda>r. r = {a..<b::nat})"
  unfolding atLeastLessThan_impl_def
  apply (refine_rcg refine_vcg WHILET_rule[where 
    I = "\<lambda>(i,r). r = {a..<i} \<and> a\<le>i \<and> ((a<b \<longrightarrow> i\<le>b) \<and> (\<not>a<b \<longrightarrow> i=a))"
    and R = "measure (\<lambda>(i,_). b - i)"
    ])
  by auto

schematic_goal atLeastLessThan_code_aux:
  notes [autoref_rules] = IdI[of a] IdI[of b]
  assumes [autoref_rules]: "(emp,{})\<in>Rs"
  assumes [autoref_rules]: "(ins,insert)\<in>nat_rel \<rightarrow> Rs \<rightarrow> Rs"
  shows "(?c, atLeastLessThan_impl) 
  \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>Rs\<rangle>nres_rel"
  unfolding atLeastLessThan_impl_def[abs_def]
  apply (autoref (keep_goal))
  done
concrete_definition atLeastLessThan_code uses atLeastLessThan_code_aux

schematic_goal atLeastLessThan_tr_aux:
  "RETURN ?c \<le> atLeastLessThan_code emp ins a b"
  unfolding atLeastLessThan_code_def
  by (refine_transfer (post))
concrete_definition atLeastLessThan_tr 
  for emp ins a b uses atLeastLessThan_tr_aux

lemma atLeastLessThan_gen[autoref_rules]: 
  assumes "PRIO_TAG_GEN_ALGO"
  assumes "GEN_OP emp {} Rs"
  assumes "GEN_OP ins insert (nat_rel \<rightarrow> Rs \<rightarrow> Rs)"
  shows "(atLeastLessThan_tr emp ins, atLeastLessThan) 
    \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> Rs"
proof (intro fun_relI, simp)
  fix a b
  from assms have GEN: 
    "(emp,{})\<in>Rs" "(ins,insert)\<in>nat_rel \<rightarrow> Rs \<rightarrow> Rs"
    by auto

  note atLeastLessThan_tr.refine[of emp ins a b]
  also note 
    atLeastLessThan_code.refine[OF GEN,param_fo, OF IdI IdI, THEN nres_relD]
  also note atLeastLessThan_impl_correct
  finally show "(atLeastLessThan_tr emp ins a b, {a..<b}) \<in> Rs"
    by (auto simp: pw_le_iff refine_pw_simps)
qed

end
