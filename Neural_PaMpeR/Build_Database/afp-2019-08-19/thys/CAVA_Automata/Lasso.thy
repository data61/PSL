section \<open>Lassos\<close>
(* Author: Peter Lammich *)
theory Lasso
imports Automata
begin

  record 'v lasso = 
    lasso_reach :: "'v list"
    lasso_va :: "'v"
    lasso_cysfx :: "'v list"
  
  definition "lasso_v0 L \<equiv> case lasso_reach L of [] \<Rightarrow> lasso_va L | (v0#_) \<Rightarrow> v0"
  definition lasso_cycle where "lasso_cycle L = lasso_va L # lasso_cysfx L"


  definition "lasso_of_prpl prpl \<equiv> case prpl of (pr,pl) \<Rightarrow> \<lparr>
    lasso_reach = pr,
    lasso_va = hd pl,
    lasso_cysfx = tl pl \<rparr>"

  definition "prpl_of_lasso L \<equiv> (lasso_reach L, lasso_va L # lasso_cysfx L)"

  lemma prpl_of_lasso_simps[simp]: 
    "fst (prpl_of_lasso L) = lasso_reach L"
    "snd (prpl_of_lasso L) = lasso_va L # lasso_cysfx L"
    unfolding prpl_of_lasso_def by auto

  lemma lasso_of_prpl_simps[simp]:
    "lasso_reach (lasso_of_prpl prpl) = fst prpl"
    "snd prpl \<noteq> [] \<Longrightarrow> lasso_cycle (lasso_of_prpl prpl) = snd prpl"
    unfolding lasso_of_prpl_def lasso_cycle_def by (auto split: prod.split)


  definition run_of_lasso :: "'q lasso \<Rightarrow> 'q word"
    \<comment> \<open>Run described by a lasso\<close>
    where "run_of_lasso L \<equiv> lasso_reach L \<frown> (lasso_cycle L)\<^sup>\<omega>"

  lemma run_of_lasso_of_prpl: 
    "pl \<noteq> [] \<Longrightarrow> run_of_lasso (lasso_of_prpl (pr, pl)) = pr \<frown> pl\<^sup>\<omega>"
    unfolding run_of_lasso_def lasso_of_prpl_def lasso_cycle_def
    by auto


  definition "map_lasso f L \<equiv> \<lparr>
    lasso_reach = map f (lasso_reach L),
    lasso_va = f (lasso_va L),
    lasso_cysfx = map f (lasso_cysfx L)
  \<rparr>"

  lemma map_lasso_simps[simp]:
    "lasso_reach (map_lasso f L) = map f (lasso_reach L)"
    "lasso_va (map_lasso f L) = f (lasso_va L)"
    "lasso_cysfx (map_lasso f L) = map f (lasso_cysfx L)"
    "lasso_v0 (map_lasso f L) = f (lasso_v0 L)"
    "lasso_cycle (map_lasso f L) = map f (lasso_cycle L)"
    unfolding map_lasso_def lasso_v0_def lasso_cycle_def
    by (auto split: list.split)
  
  lemma map_lasso_run[simp]:
    shows "run_of_lasso (map_lasso f L) = f o (run_of_lasso L)"
    by (auto simp add: map_lasso_def run_of_lasso_def conc_def iter_def
      lasso_cycle_def lasso_v0_def fun_eq_iff not_less nth_Cons'
      nz_le_conv_less)


  context graph begin
    definition is_lasso_pre :: "'v lasso \<Rightarrow> bool" 
      where "is_lasso_pre L \<equiv> 
        lasso_v0 L \<in> V0
      \<and> path E (lasso_v0 L) (lasso_reach L) (lasso_va L) 
      \<and> path E (lasso_va L) (lasso_cycle L) (lasso_va L)"
    
    definition "is_lasso_prpl_pre prpl \<equiv> case prpl of (pr, pl) \<Rightarrow> \<exists>v0 va.
      v0\<in>V0 
      \<and> pl \<noteq> []
      \<and> path E v0 pr va
      \<and> path E va pl va"

    lemma is_lasso_pre_prpl_of_lasso[simp]: 
      "is_lasso_prpl_pre (prpl_of_lasso L) \<longleftrightarrow> is_lasso_pre L"
      unfolding is_lasso_pre_def prpl_of_lasso_def is_lasso_prpl_pre_def
      unfolding lasso_v0_def lasso_cycle_def
      by (auto simp: path_simps split: list.split)
  
    lemma is_lasso_prpl_pre_conv: 
      "is_lasso_prpl_pre prpl 
      \<longleftrightarrow> (snd prpl\<noteq>[] \<and> is_lasso_pre (lasso_of_prpl prpl))"
      unfolding is_lasso_pre_def lasso_of_prpl_def is_lasso_prpl_pre_def
      unfolding lasso_v0_def lasso_cycle_def
      apply (cases prpl)
      apply (rename_tac a b)
      apply (case_tac b)
      apply (auto simp: path_simps split: list.splits)
      done

    lemma is_lasso_pre_empty[simp]: "V0 = {} \<Longrightarrow> \<not>is_lasso_pre L"
      unfolding is_lasso_pre_def by auto


    lemma run_of_lasso_pre: 
      assumes "is_lasso_pre L"  
      shows "is_run (run_of_lasso L)"
      and "run_of_lasso L 0 \<in> V0"
      using assms
      unfolding is_lasso_pre_def is_run_def run_of_lasso_def 
        lasso_cycle_def lasso_v0_def
      by (auto simp: ipath_conc_conv ipath_iter_conv path_cons_conv conc_fst 
        split: list.splits)

  end

  context gb_graph begin
    definition is_lasso
      :: "'Q lasso \<Rightarrow> bool" 
      \<comment> \<open>Predicate that defines a lasso\<close>
      where "is_lasso L \<equiv> 
        is_lasso_pre L
      \<and> (\<forall>A\<in>F. (set (lasso_cycle L)) \<inter> A \<noteq> {})"

    definition "is_lasso_prpl prpl \<equiv> 
      is_lasso_prpl_pre prpl
      \<and> (\<forall>A\<in>F. set (snd prpl) \<inter> A \<noteq> {})"
  

    lemma is_lasso_prpl_of_lasso[simp]: 
      "is_lasso_prpl (prpl_of_lasso L) \<longleftrightarrow> is_lasso L"
      unfolding is_lasso_def is_lasso_prpl_def
      unfolding lasso_v0_def lasso_cycle_def
      by auto
  
    lemma is_lasso_prpl_conv: 
      "is_lasso_prpl prpl \<longleftrightarrow> (snd prpl\<noteq>[] \<and> is_lasso (lasso_of_prpl prpl))"
      unfolding is_lasso_def is_lasso_prpl_def is_lasso_prpl_pre_conv
      apply safe
      apply simp_all
      done
    
    lemma is_lasso_empty[simp]: "V0 = {} \<Longrightarrow> \<not>is_lasso L"
      unfolding is_lasso_def by auto

    lemma lasso_accepted:
      assumes L: "is_lasso L"
      shows "is_acc_run (run_of_lasso L)"
    proof -
      obtain "pr" va pls where 
        [simp]: "L = \<lparr>lasso_reach = pr,lasso_va = va,lasso_cysfx = pls\<rparr>" 
        by (cases L)

      from L have "is_run (run_of_lasso L)" 
        unfolding is_lasso_def by (auto simp: run_of_lasso_pre)
      moreover from L have "(\<forall>A\<in>F. set (va#pls) \<inter> A \<noteq> {})"
        by (auto simp: is_lasso_def lasso_cycle_def)
      moreover from L have "(run_of_lasso L) 0 \<in> V0" 
        unfolding is_lasso_def by (auto simp: run_of_lasso_pre)
      ultimately show "is_acc_run (run_of_lasso L)"
        unfolding is_acc_run_def is_acc_def run_of_lasso_def 
          lasso_cycle_def lasso_v0_def
        by (fastforce intro: limit_inter_INF)
    qed

    lemma lasso_prpl_acc_run:
      "is_lasso_prpl (pr, pl) \<Longrightarrow> is_acc_run (pr \<frown> iter pl)"
      apply (clarsimp simp: is_lasso_prpl_conv)
      apply (drule lasso_accepted)
      apply (simp add: run_of_lasso_of_prpl)
      done

  end
  
  context gb_graph
  begin
    lemma accepted_lasso:
      assumes [simp, intro]: "finite (E\<^sup>* `` V0)"
      assumes A: "is_acc_run r"
      shows "\<exists>L. is_lasso L"
    proof -
      from A have 
        RUN: "is_run r" 
        and ACC: "\<forall>A\<in>F. limit r \<inter> A \<noteq> {}" 
        by (auto simp: is_acc_run_limit_alt)
      from RUN have [simp]: "r 0 \<in> V0" and RUN': "ipath E r" 
        by (simp_all add: is_run_def)

      txt \<open>Choose a node that is visited infinitely often\<close>
      from RUN have RAN_REACH: "range r \<subseteq> E\<^sup>*``V0"
        by (auto simp: is_run_def dest: ipath_to_rtrancl)
      hence "finite (range r)" by (auto intro: finite_subset)
      then obtain u where "u\<in>limit r" using limit_nonempty by blast
      hence U_REACH: "u\<in>E\<^sup>*``V0" using RAN_REACH limit_in_range by force
      then obtain v0 "pr" where PR: "v0\<in>V0" "path E v0 pr u" 
        by (auto intro: rtrancl_is_path)
      moreover
      txt \<open>Build a path from \<open>u\<close> to \<open>u\<close>, that contains nodes from
        each acceptance set\<close>
      have "\<exists>pl. pl\<noteq>[] \<and> path E u pl u \<and> (\<forall>A\<in>F. set pl \<inter> A \<noteq> {})"
        using finite_F ACC
      proof (induction rule: finite_induct)
        case empty
        from run_limit_two_connectedI[OF RUN' \<open>u\<in>limit r\<close> \<open>u\<in>limit r\<close>] 
        obtain p where [simp]: "p\<noteq>[]" and P: "path E u p u" 
          by (rule trancl_is_path) 
        thus ?case by blast
      next
        case (insert A F)
        from insert.IH insert.prems obtain pl where 
          [simp]: "pl\<noteq>[]" 
            and P: "path E u pl u" 
            and ACC: "(\<forall>A'\<in>F. set pl \<inter> A' \<noteq> {})"
          by auto
        from insert.prems obtain v where VACC: "v\<in>A" "v\<in>limit r" by auto
        from run_limit_two_connectedI[OF RUN' \<open>u\<in>limit r\<close> \<open>v\<in>limit r\<close>] 
        obtain p1 where [simp]: "p1\<noteq>[]" 
          and P1: "path E u p1 v" 
          by (rule trancl_is_path) 

        from run_limit_two_connectedI[OF RUN' \<open>v\<in>limit r\<close> \<open>u\<in>limit r\<close>] 
        obtain p2 where [simp]: "p2\<noteq>[]" 
          and P2: "path E v p2 u" 
          by (rule trancl_is_path) 

        note P also note P1 also (path_conc) note P2 finally (path_conc)
        have "path E u (pl@p1@p2) u" by simp
        moreover from P2 have "v\<in>set (p1@p2)" 
          by (cases p2) (auto simp: path_cons_conv)
        with ACC VACC have "(\<forall>A'\<in>insert A F. set (pl@p1@p2) \<inter> A' \<noteq> {})" by auto
        moreover have "pl@p1@p2 \<noteq> []" by auto
        ultimately show ?case by (intro exI conjI)
      qed
      then obtain pl where "pl \<noteq> []" "path E u pl u" "(\<forall>A\<in>F. set pl \<inter> A \<noteq> {})" 
        by blast
      then obtain pls where "path E u (u#pls) u" "\<forall>A\<in>F. set (u#pls) \<inter> A \<noteq> {}"
        by (cases pl) (auto simp add: path_simps)
      ultimately show ?thesis
        apply -
        apply (rule 
          exI[where x="\<lparr>lasso_reach = pr,lasso_va = u,lasso_cysfx = pls\<rparr>"])
        unfolding is_lasso_def lasso_v0_def lasso_cycle_def is_lasso_pre_def
        apply (cases "pr")
        apply (simp_all add: path_simps)
        done
    qed
  end
  

  context b_graph
  begin
    definition is_lasso where "is_lasso L \<equiv> 
      is_lasso_pre L
      \<and> (set (lasso_cycle L)) \<inter> F \<noteq> {}"

    definition is_lasso_prpl where "is_lasso_prpl L \<equiv> 
      is_lasso_prpl_pre L
      \<and> (set (snd L)) \<inter> F \<noteq> {}"
    
    lemma is_lasso_pre_ext[simp]: 
      "gbg.is_lasso_pre T m = is_lasso_pre"
      unfolding gbg.is_lasso_pre_def[abs_def] is_lasso_pre_def[abs_def]
      unfolding to_gbg_ext_def
      by auto

    lemma is_lasso_gbg: 
      "gbg.is_lasso T m = is_lasso"
      unfolding is_lasso_def[abs_def] gbg.is_lasso_def[abs_def]
      apply simp
      apply (auto simp: to_gbg_ext_def lasso_cycle_def)
      done

    lemmas lasso_accepted = gbg.lasso_accepted[unfolded to_gbg_alt is_lasso_gbg]
    lemmas accepted_lasso = gbg.accepted_lasso[unfolded to_gbg_alt is_lasso_gbg]

    lemma is_lasso_prpl_of_lasso[simp]: 
      "is_lasso_prpl (prpl_of_lasso L) \<longleftrightarrow> is_lasso L"
      unfolding is_lasso_def is_lasso_prpl_def
      unfolding lasso_v0_def lasso_cycle_def
      by auto
  
    lemma is_lasso_prpl_conv: 
      "is_lasso_prpl prpl \<longleftrightarrow> (snd prpl\<noteq>[] \<and> is_lasso (lasso_of_prpl prpl))"
      unfolding is_lasso_def is_lasso_prpl_def is_lasso_prpl_pre_conv
      apply safe
      apply auto
      done

    lemma lasso_prpl_acc_run:
      "is_lasso_prpl (pr, pl) \<Longrightarrow> is_acc_run (pr \<frown> iter pl)"
      apply (clarsimp simp: is_lasso_prpl_conv)
      apply (drule lasso_accepted)
      apply (simp add: run_of_lasso_of_prpl)
      done

  end

  context igb_graph begin
    definition "is_lasso L \<equiv>  
      is_lasso_pre L
      \<and> (\<forall>i<num_acc. \<exists>q\<in>set (lasso_cycle L). i\<in>acc q)"

    definition "is_lasso_prpl L \<equiv>  
      is_lasso_prpl_pre L
      \<and> (\<forall>i<num_acc. \<exists>q\<in>set (snd L). i\<in>acc q)"

    lemma is_lasso_prpl_of_lasso[simp]: 
      "is_lasso_prpl (prpl_of_lasso L) \<longleftrightarrow> is_lasso L"
      unfolding is_lasso_def is_lasso_prpl_def
      unfolding lasso_v0_def lasso_cycle_def
      by auto
  
    lemma is_lasso_prpl_conv: 
      "is_lasso_prpl prpl \<longleftrightarrow> (snd prpl\<noteq>[] \<and> is_lasso (lasso_of_prpl prpl))"
      unfolding is_lasso_def is_lasso_prpl_def is_lasso_prpl_pre_conv
      apply safe
      apply auto
      done

    lemma is_lasso_pre_ext[simp]: 
      "gbg.is_lasso_pre T m = is_lasso_pre"
      unfolding gbg.is_lasso_pre_def[abs_def] is_lasso_pre_def[abs_def]
      unfolding to_gbg_ext_def
      by auto

    lemma is_lasso_gbg: "gbg.is_lasso T m = is_lasso"
      unfolding is_lasso_def[abs_def] gbg.is_lasso_def[abs_def]
      apply simp
      apply (simp_all add: to_gbg_ext_def)
      apply (intro ext)
      apply (fo_rule arg_cong | intro ext)+
      apply (auto simp: F_def accn_def intro!: ext)
      done

    lemmas lasso_accepted = gbg.lasso_accepted[unfolded to_gbg_alt is_lasso_gbg]
    lemmas accepted_lasso = gbg.accepted_lasso[unfolded to_gbg_alt is_lasso_gbg]

    lemma lasso_prpl_acc_run:
      "is_lasso_prpl (pr, pl) \<Longrightarrow> is_acc_run (pr \<frown> iter pl)"
      apply (clarsimp simp: is_lasso_prpl_conv)
      apply (drule lasso_accepted)
      apply (simp add: run_of_lasso_of_prpl)
      done

    lemma degen_lasso_sound:
      assumes A: "degen.is_lasso T m L"
      shows "is_lasso (map_lasso fst L)"
    proof -
        
      from A have 
        V0: "lasso_v0 L \<in> degen.V0 T m" and
        REACH: "path (degen.E T m) 
                 (lasso_v0 L) (lasso_reach L) (lasso_va L)" and
        LOOP: "path (degen.E T m) 
                  (lasso_va L) (lasso_cycle L) (lasso_va L)" and
        ACC: "(set (lasso_cycle L)) \<inter> degen.F T m \<noteq> {}"
        unfolding degen.is_lasso_def degen.is_lasso_pre_def by auto

      {
        fix i
        assume "i<num_acc"
        hence "\<exists>q\<in>set (lasso_cycle L). i \<in> local.acc (fst q) \<and> snd q = i"
        proof (induction i)
          case 0
          thus ?case using ACC unfolding degeneralize_ext_def by fastforce
        next
          case (Suc i)
          then obtain q where "(q,i)\<in>set (lasso_cycle L)" and "i\<in>acc q" by auto
          with LOOP obtain pl' where SPL: "set (lasso_cycle L) = set pl'" 
            and PS: "path (degen.E T m) (q,i) pl' (q,i)"
            by (blast elim: path_loop_shift)
          from SPL have "pl'\<noteq>[]" by (auto simp: lasso_cycle_def)
          then obtain pl'' where [simp]: "pl'=(q,i)#pl''" 
            using PS by (cases pl') (auto simp: path_simps)
          then obtain q2 pl''' where 
            [simp]: "pl'' = (q2,(i + 1) mod num_acc)#pl'''"
            using PS \<open>i\<in>acc q\<close> \<open>Suc i < num_acc\<close>
            apply (cases pl'') 
            apply (auto 
              simp: path_simps degeneralize_ext_def 
              split: if_split_asm)
            done
          from PS have 
            "path (degen.E T m) (q2,Suc i) pl'' (q,i)"
            using \<open>Suc i < num_acc\<close>
            by (auto simp: path_simps)
          from degen_visit_acc[OF this] obtain qa 
            where "(qa,Suc i)\<in>set pl''" "Suc i \<in> acc qa" 
            by auto
          thus ?case
            by (rule_tac bexI[where x="(qa,Suc i)"]) (auto simp: SPL)
        qed
      } note aux=this

      from degen_V0_sound[OF V0] 
        degen_path_sound[OF REACH] 
        degen_path_sound[OF LOOP] aux
      show ?thesis
        unfolding is_lasso_def is_lasso_pre_def
        by auto
    qed

  end


  definition lasso_rel_ext_internal_def: "\<And>Re R. lasso_rel_ext Re R \<equiv> {
    (\<lparr> lasso_reach = r', lasso_va = va', lasso_cysfx = cysfx', \<dots>=m' \<rparr>, 
     \<lparr> lasso_reach = r, lasso_va = va, lasso_cysfx = cysfx, \<dots>=m \<rparr>) |
      r' r va' va cysfx' cysfx m' m. 
      (r',r) \<in> \<langle>R\<rangle>list_rel 
    \<and> (va',va)\<in>R
    \<and> (cysfx', cysfx) \<in> \<langle>R\<rangle>list_rel
    \<and> (m',m) \<in> Re
    }"


  lemma lasso_rel_ext_def: "\<And> Re R. \<langle>Re,R\<rangle>lasso_rel_ext = {
    (\<lparr> lasso_reach = r', lasso_va = va', lasso_cysfx = cysfx', \<dots>=m' \<rparr>, 
     \<lparr> lasso_reach = r, lasso_va = va, lasso_cysfx = cysfx, \<dots>=m \<rparr>) |
      r' r va' va cysfx' cysfx m' m. 
      (r',r) \<in> \<langle>R\<rangle>list_rel 
    \<and> (va',va)\<in>R
    \<and> (cysfx', cysfx) \<in> \<langle>R\<rangle>list_rel
    \<and> (m',m) \<in> Re
    }"
    unfolding lasso_rel_ext_internal_def relAPP_def by auto

  lemma lasso_rel_ext_sv[relator_props]: 
    "\<And> Re R. \<lbrakk> single_valued Re; single_valued R \<rbrakk> \<Longrightarrow> single_valued (\<langle>Re,R\<rangle>lasso_rel_ext)"
    unfolding lasso_rel_ext_def
    apply (rule single_valuedI)
    apply safe
    apply (blast dest: single_valuedD list_rel_sv[THEN single_valuedD])+
    done

  lemma lasso_rel_ext_id[relator_props]: 
    "\<And>Re R. \<lbrakk> Re=Id; R=Id \<rbrakk> \<Longrightarrow> \<langle>Re,R\<rangle>lasso_rel_ext = Id"
    unfolding lasso_rel_ext_def
    apply simp
    apply safe
    by (metis lasso.surjective)

  consts i_lasso_ext :: "interface \<Rightarrow> interface \<Rightarrow> interface"

  lemmas [autoref_rel_intf] = REL_INTFI[of lasso_rel_ext i_lasso_ext]

  find_consts "(_,_) lasso_scheme"
  term lasso_reach_update

  lemma lasso_param[param, autoref_rules]:
    "\<And>Re R. (lasso_reach, lasso_reach) \<in> \<langle>Re,R\<rangle>lasso_rel_ext \<rightarrow> \<langle>R\<rangle>list_rel"
    "\<And>Re R. (lasso_va, lasso_va) \<in> \<langle>Re,R\<rangle>lasso_rel_ext \<rightarrow> R"
    "\<And>Re R. (lasso_cysfx, lasso_cysfx) \<in> \<langle>Re,R\<rangle>lasso_rel_ext \<rightarrow> \<langle>R\<rangle>list_rel"
    "\<And>Re R. (lasso_ext, lasso_ext) 
      \<in> \<langle>R\<rangle>list_rel \<rightarrow> R \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> Re \<rightarrow> \<langle>Re,R\<rangle>lasso_rel_ext"
    "\<And>Re R. (lasso_reach_update, lasso_reach_update) 
      \<in> (\<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel) \<rightarrow> \<langle>Re,R\<rangle>lasso_rel_ext \<rightarrow> \<langle>Re,R\<rangle>lasso_rel_ext"
    "\<And>Re R. (lasso_va_update, lasso_va_update) 
      \<in> (R\<rightarrow>R) \<rightarrow> \<langle>Re,R\<rangle>lasso_rel_ext \<rightarrow> \<langle>Re,R\<rangle>lasso_rel_ext"
    "\<And>Re R. (lasso_cysfx_update, lasso_cysfx_update) 
      \<in> (\<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel) \<rightarrow> \<langle>Re,R\<rangle>lasso_rel_ext \<rightarrow> \<langle>Re,R\<rangle>lasso_rel_ext"
    "\<And>Re R. (lasso.more_update, lasso.more_update) 
      \<in> (Re\<rightarrow>Re) \<rightarrow> \<langle>Re,R\<rangle>lasso_rel_ext \<rightarrow> \<langle>Re,R\<rangle>lasso_rel_ext"
    unfolding lasso_rel_ext_def
    by (auto dest: fun_relD)


  lemma lasso_param2[param, autoref_rules]:
    "\<And>Re R. (lasso_v0, lasso_v0) \<in> \<langle>Re,R\<rangle>lasso_rel_ext \<rightarrow> R"
    "\<And>Re R. (lasso_cycle, lasso_cycle) \<in> \<langle>Re,R\<rangle>lasso_rel_ext \<rightarrow> \<langle>R\<rangle>list_rel"
    "\<And>Re R. (map_lasso, map_lasso) 
      \<in> (R\<rightarrow>R') \<rightarrow> \<langle>Re,R\<rangle>lasso_rel_ext \<rightarrow> \<langle>unit_rel,R'\<rangle>lasso_rel_ext"
    unfolding lasso_v0_def[abs_def] lasso_cycle_def[abs_def] map_lasso_def[abs_def]
    by parametricity+


  lemma lasso_of_prpl_param: "\<lbrakk>(l',l)\<in>\<langle>R\<rangle>list_rel \<times>\<^sub>r \<langle>R\<rangle>list_rel; snd l \<noteq> []\<rbrakk> 
    \<Longrightarrow> (lasso_of_prpl l', lasso_of_prpl l) \<in> \<langle>unit_rel,R\<rangle>lasso_rel_ext"
    unfolding lasso_of_prpl_def
    apply (cases l, cases l', clarsimp)
    apply (case_tac b, simp, case_tac ba, clarsimp_all)
    apply parametricity
    done

  context begin interpretation autoref_syn .

  lemma lasso_of_prpl_autoref[autoref_rules]:
    assumes "SIDE_PRECOND (snd l \<noteq> [])"
    assumes "(l',l)\<in>\<langle>R\<rangle>list_rel \<times>\<^sub>r \<langle>R\<rangle>list_rel"
    shows "(lasso_of_prpl l', 
      (OP lasso_of_prpl 
        ::: \<langle>R\<rangle>list_rel \<times>\<^sub>r \<langle>R\<rangle>list_rel \<rightarrow> \<langle>unit_rel,R\<rangle>lasso_rel_ext)$l) 
      \<in> \<langle>unit_rel,R\<rangle>lasso_rel_ext"
    using assms
    apply (simp add: lasso_of_prpl_param)
    done

  end




  subsection \<open>Implementing runs by lassos\<close>
  
  definition lasso_run_rel_def_internal: 
    "lasso_run_rel R \<equiv> br run_of_lasso (\<lambda>_. True) O (nat_rel \<rightarrow> R)"
  lemma lasso_run_rel_def: 
    "\<langle>R\<rangle>lasso_run_rel = br run_of_lasso (\<lambda>_. True) O (nat_rel \<rightarrow> R)"
    unfolding lasso_run_rel_def_internal relAPP_def by simp

  lemma lasso_run_rel_sv[relator_props]: 
    "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>lasso_run_rel)"
    unfolding lasso_run_rel_def
    by tagged_solver

  consts i_run :: "interface \<Rightarrow> interface"

  lemmas [autoref_rel_intf] = REL_INTFI[of lasso_run_rel i_run]

  definition [simp]: "op_map_run \<equiv> (o)"

  lemma [autoref_op_pat]: "(o) \<equiv> op_map_run" by simp

  lemma map_lasso_run_refine[autoref_rules]:
    shows "(map_lasso,op_map_run) \<in> (R\<rightarrow>R') \<rightarrow> \<langle>R\<rangle>lasso_run_rel \<rightarrow> \<langle>R'\<rangle>lasso_run_rel"
    unfolding lasso_run_rel_def op_map_run_def
  proof (intro fun_relI)
    fix f f' l r
    assume [param]: "(f,f')\<in>R\<rightarrow>R'" and 
      "(l, r) \<in> br run_of_lasso (\<lambda>_. True) O (nat_rel \<rightarrow> R)"
    then obtain r' where [param]: "(r',r)\<in>nat_rel \<rightarrow> R" 
      and [simp]: "r' = run_of_lasso l" 
      by (auto simp: br_def)
    
    have "(map_lasso f l, f o r') \<in> br run_of_lasso (\<lambda>_. True)" 
      by (simp add: br_def)
    also have "(f o r', f' o r) \<in> nat_rel \<rightarrow> R'" by parametricity
    finally (relcompI) show 
      "(map_lasso f l, f' o r) \<in> br run_of_lasso (\<lambda>_. True) O (nat_rel \<rightarrow> R')" 
      .
  qed

end
