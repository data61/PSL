section \<open>\isaheader{Generic Map Algorithms}\<close>
theory Gen_Map
imports "../Intf/Intf_Map" "../../Iterator/Iterator"
begin
  lemma map_to_set_distinct_conv:
    assumes "distinct tsl'" and "map_to_set m' = set tsl'"
    shows "distinct (map fst tsl')"
    apply (rule ccontr)
    apply (drule not_distinct_decomp)
    using assms
    apply (clarsimp elim!: map_eq_appendE)
    by (metis (hide_lams, no_types) insert_iff map_to_set_inj)


  (* TODO: Make foldli explicit, such that it is seen by 
  iterator-optimizations! cf Gen_Set for how to do this! *)
  lemma foldli_add: "det_fold_map X 
    (\<lambda>_. True) (\<lambda>(k,v) m. op_map_update k v m) m ((++) m)"
  proof (rule, goal_cases)
    case (1 l) thus ?case
      apply (induct l arbitrary: m) 
      apply (auto simp: map_of_distinct_upd[symmetric])
      done
  qed

  definition gen_add
    :: "('s2 \<Rightarrow> _) \<Rightarrow> ('k \<Rightarrow> 'v \<Rightarrow> 's1 \<Rightarrow> 's1) \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> 's1"
    where 
    "gen_add it upd A B \<equiv> it B (\<lambda>_. True) (\<lambda>(k,v) m. upd k v m) A"

  lemma gen_add[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes UPD: "GEN_OP ins op_map_update (Rk\<rightarrow>Rv\<rightarrow>\<langle>Rk,Rv\<rangle>Rs1\<rightarrow>\<langle>Rk,Rv\<rangle>Rs1)"
    assumes IT: "SIDE_GEN_ALGO (is_map_to_list Rk Rv Rs2 tsl)"
    shows "(gen_add (foldli o tsl) ins,(++)) 
      \<in> (\<langle>Rk,Rv\<rangle>Rs1) \<rightarrow> (\<langle>Rk,Rv\<rangle>Rs2) \<rightarrow> (\<langle>Rk,Rv\<rangle>Rs1)"
    apply (intro fun_relI)
    unfolding gen_add_def comp_def
    apply (rule det_fold_map[OF foldli_add IT[unfolded autoref_tag_defs]])
    apply (parametricity add: UPD[unfolded autoref_tag_defs])+
    done

  lemma foldli_restrict: "det_fold_map X (\<lambda>_. True) 
    (\<lambda>(k,v) m. if P (k,v) then op_map_update k v m else m) Map.empty
      (op_map_restrict P )" (is "det_fold_map _ _ ?f _ _")
  proof -
    {
      fix l m
      have "distinct (map fst l) \<Longrightarrow>
        foldli l (\<lambda>_. True) ?f m = m ++ op_map_restrict P (map_of l)"
      proof (induction l arbitrary: m) 
        case Nil thus ?case by simp
      next
        case (Cons kv l)
        obtain k v where [simp]: "kv = (k,v)" by fastforce
        from Cons.prems have 
          DL: "distinct (map fst l)" and KNI: "k \<notin> set (map fst l)" 
          by auto

        show ?case proof (cases "P (k,v)")
          case [simp]: True 
          have "foldli (kv#l) (\<lambda>_. True) ?f m = foldli l (\<lambda>_. True) ?f (m(k\<mapsto>v))"
            by simp
          also from Cons.IH[OF DL] have 
            "\<dots> = m(k\<mapsto>v) ++ op_map_restrict P (map_of l)" .
          also have "\<dots> = m ++ op_map_restrict P (map_of (kv#l))"
            using KNI
            by (auto
              split: option.splits
              intro!: ext 
              simp: Map.restrict_map_def Map.map_add_def
              simp: map_of_eq_None_iff[symmetric])
          finally show ?thesis .
        next
          case [simp]: False 
          have "foldli (kv#l) (\<lambda>_. True) ?f m = foldli l (\<lambda>_. True) ?f m"
            by simp
          also from Cons.IH[OF DL] have 
            "\<dots> = m ++ op_map_restrict P (map_of l)" .
          also have "\<dots> = m ++ op_map_restrict P (map_of (kv#l))"
            using KNI
            by (auto 
              intro!: ext
              simp: Map.restrict_map_def Map.map_add_def
              simp: map_of_eq_None_iff[symmetric]
            )
          finally show ?thesis .
        qed
      qed
    } 
    from this[of _ Map.empty] show ?thesis
      by (auto intro!: det_fold_mapI)
  qed

  definition gen_restrict :: "('s1 \<Rightarrow> _) \<Rightarrow> _"
    where "gen_restrict it upd emp P m 
    \<equiv> it m (\<lambda>_. True) (\<lambda>(k,v) m. if P (k,v) then upd k v m else m) emp"

  lemma gen_restrict[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_map_to_list Rk Rv Rs1 tsl)"
    assumes INS: 
      "GEN_OP upd op_map_update (Rk\<rightarrow>Rv\<rightarrow>\<langle>Rk,Rv\<rangle>Rs2\<rightarrow>\<langle>Rk,Rv\<rangle>Rs2)"
    assumes EMPTY: 
      "GEN_OP emp Map.empty (\<langle>Rk,Rv\<rangle>Rs2)"
    shows "(gen_restrict (foldli o tsl) upd emp,op_map_restrict) 
    \<in> (\<langle>Rk,Rv\<rangle>prod_rel \<rightarrow> Id) \<rightarrow> (\<langle>Rk,Rv\<rangle>Rs1) \<rightarrow> (\<langle>Rk,Rv\<rangle>Rs2)"
    apply (intro fun_relI)
    unfolding gen_restrict_def comp_def
    apply (rule det_fold_map[OF foldli_restrict IT[unfolded autoref_tag_defs]])
    using INS EMPTY unfolding autoref_tag_defs
    apply (parametricity)+
    done

  lemma fold_map_of: 
    "fold (\<lambda>(k,v) s. op_map_update k v s) (rev l) Map.empty = map_of l"
  proof -
    {
      fix m
      have "fold (\<lambda>(k,v) s. s(k\<mapsto>v)) (rev l) m = m ++ map_of l"
        apply (induct l arbitrary: m)
        apply auto
        done
    } thus ?thesis by simp
  qed

  definition gen_map_of :: "'m \<Rightarrow> ('k\<Rightarrow>'v\<Rightarrow>'m\<Rightarrow>'m) \<Rightarrow> _" where 
    "gen_map_of emp upd l \<equiv> fold (\<lambda>(k,v) s. upd k v s) (rev l) emp"


  lemma gen_map_of[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes UPD: "GEN_OP upd op_map_update (Rk\<rightarrow>Rv\<rightarrow>\<langle>Rk,Rv\<rangle>Rm\<rightarrow>\<langle>Rk,Rv\<rangle>Rm)"
    assumes EMPTY: "GEN_OP emp Map.empty (\<langle>Rk,Rv\<rangle>Rm)"
    shows "(gen_map_of emp upd,map_of) \<in> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel \<rightarrow> \<langle>Rk,Rv\<rangle>Rm"
    using assms
    apply (intro fun_relI)
    unfolding gen_map_of_def[abs_def]
    unfolding autoref_tag_defs
    apply (subst fold_map_of[symmetric])
    apply parametricity
    done

  lemma foldli_ball_aux: 
    "distinct (map fst l) \<Longrightarrow> foldli l (\<lambda>x. x) (\<lambda>x _. P x) b 
    \<longleftrightarrow> b \<and> op_map_ball (map_of l) P"
    apply (induct l arbitrary: b)
    apply simp
    apply (force simp: map_to_set_map_of image_def)
    done
  
  lemma foldli_ball: 
    "det_fold_map X (\<lambda>x. x) (\<lambda>x _. P x) True (\<lambda>m. op_map_ball m P)"
    apply rule
    using foldli_ball_aux[where b=True] by auto
    
  definition gen_ball :: "('m \<Rightarrow> _) \<Rightarrow> _" where
    "gen_ball it m P \<equiv> it m (\<lambda>x. x) (\<lambda>x _. P x) True"

  lemma gen_ball[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_map_to_list Rk Rv Rm tsl)"
    shows "(gen_ball (foldli o tsl),op_map_ball) 
    \<in> \<langle>Rk,Rv\<rangle>Rm \<rightarrow> (\<langle>Rk,Rv\<rangle>prod_rel \<rightarrow> Id) \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_ball_def comp_def
    apply (rule det_fold_map[OF foldli_ball IT[unfolded autoref_tag_defs]])
    apply (parametricity)+
    done

  lemma foldli_bex_aux: 
    "distinct (map fst l) \<Longrightarrow> foldli l (\<lambda>x. \<not>x) (\<lambda>x _. P x) b 
    \<longleftrightarrow> b \<or> op_map_bex (map_of l) P"
    apply (induct l arbitrary: b)
    apply simp
    apply (force simp: map_to_set_map_of image_def)
    done
  
  lemma foldli_bex: 
    "det_fold_map X (\<lambda>x. \<not>x) (\<lambda>x _. P x) False (\<lambda>m. op_map_bex m P)"
    apply rule
    using foldli_bex_aux[where b=False] by auto

  definition gen_bex :: "('m \<Rightarrow> _) \<Rightarrow> _" where
    "gen_bex it m P \<equiv> it m (\<lambda>x. \<not>x) (\<lambda>x _. P x) False"

  lemma gen_bex[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_map_to_list Rk Rv Rm tsl)"
    shows "(gen_bex (foldli o tsl),op_map_bex) 
    \<in> \<langle>Rk,Rv\<rangle>Rm \<rightarrow> (\<langle>Rk,Rv\<rangle>prod_rel \<rightarrow> Id) \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_bex_def comp_def
    apply (rule det_fold_map[OF foldli_bex IT[unfolded autoref_tag_defs]])
    apply (parametricity)+
    done

  lemma ball_isEmpty: "op_map_isEmpty m = op_map_ball m (\<lambda>_. False)"
    apply (auto intro!: ext)
    by (metis map_to_set_simps(7) option.exhaust)

  definition "gen_isEmpty ball m \<equiv> ball m (\<lambda>_. False)"

  lemma gen_isEmpty[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes BALL: 
      "GEN_OP ball op_map_ball (\<langle>Rk,Rv\<rangle>Rm\<rightarrow>(\<langle>Rk,Rv\<rangle>prod_rel\<rightarrow>Id) \<rightarrow> Id)"
    shows "(gen_isEmpty ball,op_map_isEmpty) 
    \<in> \<langle>Rk,Rv\<rangle>Rm \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_isEmpty_def using assms
    unfolding autoref_tag_defs
    apply -
    apply (subst ball_isEmpty)
    apply parametricity+
    done
  
  lemma foldli_size_aux: "distinct (map fst l) 
    \<Longrightarrow> foldli l (\<lambda>_. True) (\<lambda>_ n. Suc n) n = n + op_map_size (map_of l)"
    apply (induct l arbitrary: n)
    apply (auto simp: dom_map_of_conv_image_fst)
    done

  lemma foldli_size: "det_fold_map X (\<lambda>_. True) (\<lambda>_ n. Suc n) 0 op_map_size"
    apply rule
    using foldli_size_aux[where n=0] by simp

  definition gen_size :: "('m \<Rightarrow> _) \<Rightarrow> _"
    where "gen_size it m \<equiv> it m (\<lambda>_. True) (\<lambda>_ n. Suc n) 0"

  lemma gen_size[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_map_to_list Rk Rv Rm tsl)"
    shows "(gen_size (foldli o tsl),op_map_size) \<in> \<langle>Rk,Rv\<rangle>Rm \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_size_def comp_def
    apply (rule det_fold_map[OF foldli_size IT[unfolded autoref_tag_defs]])
    apply (parametricity)+
    done
  
  lemma foldli_size_abort_aux:
    "\<lbrakk>n0\<le>m; distinct (map fst l)\<rbrakk> \<Longrightarrow> 
      foldli l (\<lambda>n. n<m) (\<lambda>_ n. Suc n) n0 = min m (n0 + card (dom (map_of l)))"
    apply (induct l arbitrary: n0)
    apply (auto simp: dom_map_of_conv_image_fst)
    done

  lemma foldli_size_abort: 
    "det_fold_map X (\<lambda>n. n<m) (\<lambda>_ n. Suc n) 0 (op_map_size_abort m)"
    apply rule
    using foldli_size_abort_aux[where ?n0.0=0]
    by simp

  definition gen_size_abort :: "('s \<Rightarrow> _) \<Rightarrow> _" where
    "gen_size_abort it m s \<equiv> it s (\<lambda>n. n<m) (\<lambda>_ n. Suc n) 0"

  lemma gen_size_abort[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_map_to_list Rk Rv Rm tsl)"
    shows "(gen_size_abort (foldli o tsl),op_map_size_abort) 
      \<in> Id \<rightarrow> \<langle>Rk,Rv\<rangle>Rm \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_size_abort_def comp_def
    apply (rule det_fold_map[OF foldli_size_abort 
      IT[unfolded autoref_tag_defs]])
    apply (parametricity)+
    done
  
  lemma size_abort_isSng: "op_map_isSng s \<longleftrightarrow> op_map_size_abort 2 s = 1"
    by (auto simp: dom_eq_singleton_conv min_def dest!: card_eq_SucD)

  definition gen_isSng :: "(nat \<Rightarrow> 's \<Rightarrow> nat) \<Rightarrow> _" where
    "gen_isSng sizea s \<equiv> sizea 2 s = 1"

  lemma gen_isSng[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes "GEN_OP sizea op_map_size_abort (Id \<rightarrow> (\<langle>Rk,Rv\<rangle>Rm) \<rightarrow> Id)"
    shows "(gen_isSng sizea,op_map_isSng) 
    \<in> \<langle>Rk,Rv\<rangle>Rm \<rightarrow> Id"
    apply (intro fun_relI)
    unfolding gen_isSng_def using assms
    unfolding autoref_tag_defs
    apply -
    apply (subst size_abort_isSng)
    apply parametricity
    done


  (* TODO: Also do sel! *)

  lemma foldli_pick:
    assumes "l\<noteq>[]" 
    obtains k v where "(k,v)\<in>set l" 
    and "(foldli l (case_option True (\<lambda>_. False)) (\<lambda>x _. Some x) None) 
      = Some (k,v)"
    using assms by (cases l) auto

  definition gen_pick where
    "gen_pick it s \<equiv> 
      (the (it s (case_option True (\<lambda>_. False)) (\<lambda>x _. Some x) None))"



context begin interpretation autoref_syn .

  lemma gen_pick[autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes IT: "SIDE_GEN_ALGO (is_map_to_list Rk Rv Rm it)"
    assumes NE: "SIDE_PRECOND (m'\<noteq>Map.empty)"
    assumes SREF: "(m,m')\<in>\<langle>Rk,Rv\<rangle>Rm"
    shows "(RETURN (gen_pick (\<lambda>x. foldli (it x)) m), 
      (OP op_map_pick ::: \<langle>Rk,Rv\<rangle>Rm\<rightarrow>\<langle>Rk\<times>\<^sub>rRv\<rangle>nres_rel)$m')\<in>\<langle>Rk\<times>\<^sub>rRv\<rangle>nres_rel"
  proof -
    thm is_map_to_list_def is_map_to_sorted_listE

    obtain tsl' where
      [param]: "(it m,tsl') \<in> \<langle>Rk\<times>\<^sub>rRv\<rangle>list_rel" 
      and IT': "RETURN tsl' \<le> it_to_sorted_list (\<lambda>_ _. True) (map_to_set m')"
      using IT[unfolded autoref_tag_defs is_map_to_list_def] SREF
      by (auto intro: is_map_to_sorted_listE)

    from IT' NE have "tsl'\<noteq>[]" and [simp]: "m'=map_of tsl'" 
      and DIS': "distinct (map fst tsl')"
      unfolding it_to_sorted_list_def 
      apply simp_all
      apply (metis empty_set map_to_set_empty_iff(1))
      apply (metis map_of_map_to_set map_to_set_distinct_conv)
      apply (metis map_to_set_distinct_conv)
      done

    then obtain k v where "m' k = Some v" and
      "(foldli tsl' (case_option True (\<lambda>_. False)) (\<lambda>x _. Some x) None) 
        = Some (k,v)"
      (is "?fld = _")
      by (cases rule: foldli_pick) auto
    moreover 
    have "(RETURN (gen_pick (\<lambda>x. foldli (it x)) m), RETURN (the ?fld)) 
      \<in> \<langle>Rk\<times>\<^sub>rRv\<rangle>nres_rel"
      unfolding gen_pick_def
      apply (parametricity add: the_paramR)
      using \<open>?fld = Some (k,v)\<close>
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


  definition "gen_map_pick_remove pick del m \<equiv> do {
    (k,v)\<leftarrow>pick m;
    let m = del k m;
    RETURN ((k,v),m)
    }"
  
context begin interpretation autoref_syn .
  lemma gen_map_pick_remove
    [unfolded gen_map_pick_remove_def, autoref_rules_raw]:
    assumes PRIO_TAG_GEN_ALGO
    assumes PICK: "SIDE_GEN_OP (
      (pick m, 
      (OP op_map_pick ::: \<langle>Rk,Rv\<rangle>Rm \<rightarrow> \<langle>Rk\<times>\<^sub>rRv\<rangle>nres_rel)$m') \<in>
      \<langle>Rk\<times>\<^sub>rRv\<rangle>nres_rel)"
    assumes DEL: "GEN_OP del op_map_delete (Rk \<rightarrow> \<langle>Rk,Rv\<rangle>Rm \<rightarrow> \<langle>Rk,Rv\<rangle>Rm)"
    assumes [param]: "(m,m')\<in>\<langle>Rk,Rv\<rangle>Rm"
    shows "(gen_map_pick_remove pick del m, 
      (OP op_map_pick_remove 
        ::: \<langle>Rk,Rv\<rangle>Rm \<rightarrow> \<langle>(Rk\<times>\<^sub>rRv) \<times>\<^sub>r \<langle>Rk,Rv\<rangle>Rm\<rangle>nres_rel)$m')
      \<in> \<langle>(Rk\<times>\<^sub>rRv) \<times>\<^sub>r \<langle>Rk,Rv\<rangle>Rm\<rangle>nres_rel"
  proof -
    note [param] = 
      PICK[unfolded autoref_tag_defs] 
      DEL[unfolded autoref_tag_defs]

    have "(gen_map_pick_remove pick del m, 
      do {    
        (k,v)\<leftarrow>op_map_pick m';
        let m' = op_map_delete k m';
        RETURN ((k,v),m')
      }) \<in> \<langle>(Rk\<times>\<^sub>rRv) \<times>\<^sub>r \<langle>Rk,Rv\<rangle>Rm\<rangle>nres_rel" (is "(_,?h):_")
      unfolding gen_map_pick_remove_def[abs_def]
      apply parametricity
      done
    also have "?h = op_map_pick_remove m'"
      by (auto simp add: pw_eq_iff refine_pw_simps)
    finally show ?thesis by simp
  qed
end


end
