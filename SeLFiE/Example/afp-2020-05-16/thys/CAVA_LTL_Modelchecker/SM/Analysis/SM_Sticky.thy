theory SM_Sticky
imports 
  SM_Indep
  DFS_Framework.Reachable_Nodes
  DFS_Framework.Feedback_Arcs
  Partial_Order_Reduction.Ample_Analysis
begin

  lemma eq_conv_sym: 
    assumes "(a=b) = c"
    shows "(b=a) = c"
    using assms by auto

  lemma neq_conv_sym: 
    assumes "(a\<noteq>b) = c"
    shows "(b\<noteq>a) = c"
    using assms by auto

  lemmas [iff] = not_None_eq[THEN neq_conv_sym]

  lemma none_notin_set_map_Some_conv: "None \<notin> set w \<longleftrightarrow> (\<exists>w'. w=map Some w')"
    apply rule
      apply (induction w)
      apply (auto simp: map_eq_Cons_conv[THEN eq_conv_sym]) [2]

      apply auto []
    done

  context cprog begin 
    definition "cfgc_V0 \<equiv> comp.\<gamma> ` cfg_V0 prog"
    definition "cfgc_V0_list \<equiv> map comp.\<gamma> (cfg_V0_list prog)"

    lemma cfgc_V0_list_refine: "(cfgc_V0_list, cfgc_V0) \<in> \<langle>Id\<rangle>list_set_rel"
      unfolding cfgc_V0_def cfgc_V0_list_def list_set_rel_def br_def
      using cfg_V0_list_invar cfg_V0_list_refine
      apply (auto simp: distinct_map intro!: inj_onI)
      using comp.\<alpha>_\<gamma>_inverse comp.rl_reachable
      apply auto
      by (meson Image_iff comp.\<gamma>_inj inj_onD inj_on_subset rtrancl.rtrancl_refl)

    definition "cfgc_E \<equiv> {(c,c'). \<exists>a. cfgc c a c'}"
    definition "cfgc_E_succ \<equiv> remdups o map snd o comp.succ_impl"

    lemma cfgc_E_succ_refine: "(cfgc_E_succ, cfgc_E) \<in> \<langle>nat_rel\<rangle>slg_rel"
      unfolding cfgc_E_def cfgc_E_succ_def comp.astep_impl_def
      unfolding slg_rel_def build_rel_def
      apply (rule relcompI[where b="\<lambda>c. snd`set (comp.succ_impl c)"])
      apply (auto simp: list_set_rel_def build_rel_def comp.succ_impl_invar)
      done

    definition "cfgc_G \<equiv> \<lparr> g_V = UNIV, g_E = cfgc_E, g_V0 = cfgc_V0 \<rparr>"
    definition "cfgc_G_impl \<equiv> \<lparr> gi_V = \<lambda> _. True, gi_E = cfgc_E_succ, gi_V0 = cfgc_V0_list \<rparr>"

    lemma cfg_G_simps[simp]:
      "g_V cfgc_G = UNIV"
      "g_E cfgc_G = cfgc_E"
      "g_V0 cfgc_G = cfgc_V0"
      unfolding cfgc_G_def by auto

    lemma cfgc_G_impl_refine: "(cfgc_G_impl, cfgc_G) \<in> \<langle>unit_rel, nat_rel\<rangle>g_impl_rel_ext"
      unfolding cfgc_G_def cfgc_G_impl_def
      by (parametricity add: fun_set_UNIV_refine cfgc_V0_list_refine cfgc_E_succ_refine)

    lemma cfgc_V0_invarc: "c\<in>cfgc_V0 \<Longrightarrow> comp.invar c"
      unfolding cfgc_V0_def comp.invar_def
      apply auto
      apply (rule comp.\<gamma>_invar)
      apply (auto simp: approx_reachable_list_refine cfg_V0_def approx_reachable_prog0)
      done

    lemma cfgc_Estar_invarc: "\<lbrakk>comp.invar c; (c,c')\<in>cfgc_E\<^sup>*\<rbrakk> \<Longrightarrow> comp.invar c'"
      apply (rotate_tac)
      apply (induction rule: rtrancl_induct)
      apply (auto simp: cfgc_E_def comp.astep_impl_invarc)
      done
  
  end

  context visible_prog
  begin

    lemma pid_valid_preserve[simp]: "pid_valid (ga_ex a gc) pid = pid_valid gc pid"  
      by (auto 
        simp: ga_ex_def ga_gex_def stutter_extend_ex_def
        split: option.splits prod.splits
      )

    lemma pid_valid_preserve_fold[simp]: "pid_valid (fold ga_ex w gc) pid = pid_valid gc pid"  
      by (induction w arbitrary: gc) auto

    lemma pid_valid_ga_gen: "(pid,cac)\<in>ga_gen gc \<Longrightarrow> pid_valid gc pid"
      by (auto simp: ga_gen_def)

    lemma pid_valid_ga_en: "Some (pid,cac)\<in>ga_en gc \<Longrightarrow> pid_valid gc pid"
      by (auto simp: some_ga_en_eq pid_valid_ga_gen)

    sublocale sys_graph: fb_graph cfgc_G
      apply unfold_locales
      apply (simp_all add: cfgc_V0_def cfg_V0_def cfgc_E_def)
      done

    lemma finite_cfgE_reachable[simp, intro!]: "finite (cfgc_E\<^sup>* `` cfgc_V0)"
      apply (rule finite_ImageI)
      using sys_graph.finite_V0
      apply simp
      apply (rule finite_subset[where B="Collect comp.invar"])
      apply (auto intro: cfgc_V0_invarc cfgc_Estar_invarc) []
      apply (simp add: comp.invar_def[abs_def])      
      done

    definition "vis_edges \<equiv> {(c,c'). \<exists>a. cfgc c a c' \<and> write_globals a \<inter> vis_vars \<noteq> {}}"

    fun ga_is_pid :: "global_action option \<Rightarrow> pid \<Rightarrow> bool" where
      "ga_is_pid None _ \<longleftrightarrow> True"
    | "ga_is_pid (Some (pid',_)) pid \<longleftrightarrow> pid'=pid"


    lemma 
      assumes "(pid,c,a,c') \<in> ga_gen gc"
      shows 
        ga_gen_cmd: "cmd_of_pid gc pid = c" and 
        ga_gen_cmd': "cmd_of_pid (ga_gex (pid,c,a,c') gc) pid = c'" and 
        ga_gen_edge: "(c,c')\<in>cfgc_E"
      using assms
      apply -
      apply (cases a)
      apply (auto 
        simp: cfgc_E_def
        simp: ga_gen_def la_en'_def
        simp: ga_gex_def la_ex'_def
        split: option.splits
        ) [5]
      apply (cases a)
      apply (auto 
        simp: cfgc_E_def
        simp: ga_gen_def la_en'_def
        simp: ga_gex_def la_ex'_def
        split: option.splits
        ) [5]
      apply (cases a)
      apply (auto 
        simp: cfgc_E_def
        simp: ga_gen_def la_en'_def
        simp: ga_gex_def la_ex'_def
        split: option.splits
        ) [5]
      done      

    lemmas ga_gen_cmd_cfg = ga_gen_cmd ga_gen_cmd' ga_gen_edge

    lemma ga_gex_other: 
      assumes "pid'\<noteq>pid"
      shows "cmd_of_pid (ga_gex (pid',c,a,c') gc) pid = cmd_of_pid gc pid"
      using assms
      apply (cases a)
      apply (auto 
        simp: ga_gex_def la_ex'_def
        split: option.splits
        ) [5]
      done

    lemma proj_word_fin_to_cfg_E:
      assumes "jsys.path (map Some w) gc"
      assumes "fold ga_gex w gc = gc'"
      shows "(cmd_of_pid gc pid, cmd_of_pid gc' pid) 
        \<in> (cfgc_E \<inter> (\<lambda>(_,c,_,c'). (c,c'))`set w)\<^sup>*" (is "_\<in>(?E w)\<^sup>*")
      using assms
    proof (induction w arbitrary: gc)
      case (Cons ga w)
      from Cons.prems have 
        EN: "ga \<in> ga_gen gc" and
        WF': "jsys.path (map Some w) (ga_gex ga gc)" and
        EX': "fold ga_gex w (ga_gex ga gc) = gc'"
        by (auto simp: some_ga_en_eq some_ga_ex_eq)
      obtain pid' c a c' where [simp]: "ga = (pid',c,a,c')"
        by (cases ga)

      have "(cmd_of_pid gc pid, cmd_of_pid (ga_gex ga gc) pid) \<in> (?E (ga#w))\<^sup>*"
      proof (cases "pid'=pid")  
        case True
        note True[simp]
        from EN have "(pid,c,a,c')\<in>ga_gen gc" by simp
        from ga_gen_cmd_cfg[OF this] 
        have "(cmd_of_pid gc pid, cmd_of_pid (ga_gex ga gc) pid) \<in> ?E (ga#w)" 
          by auto
        thus ?thesis ..
      next
        case False
        hence "cmd_of_pid (ga_gex ga gc) pid = cmd_of_pid gc pid"
          by (simp add: ga_gex_other)
        thus ?thesis by auto
      qed
      also from Cons.IH[OF WF' EX'] have 
        "(cmd_of_pid (ga_gex ga gc) pid, cmd_of_pid gc' pid) \<in> (?E (ga#w))\<^sup>*"
        apply (rule set_rev_mp[OF _ rtrancl_mono])
        by auto
      finally show ?case .
    qed simp

    lemma words_fin_None_fmt:
      assumes "jsys.path w gc"
      obtains w' n where "w=map Some w'@replicate n None"
      using assms
    proof (induction arbitrary: thesis)
      case nil thus ?case by simp
    next
      case (cons a gc w)
      from cons.IH obtain w' n where [simp]: "w=map Some w'@replicate n None" .
      show ?case proof (cases a)
        case None
        note None[simp] 
        from cons.hyps have [simp]: "w'=[]" 
          by (cases w') (auto simp: none_ga_en_eq some_ga_en_eq) 
        show ?thesis apply (rule cons.prems[of "[]" "Suc n"]) by simp
      next
        case (Some aa)
        note Some[simp]
        show ?thesis apply (rule cons.prems[of "aa#w'" n]) by simp
      qed
    qed

    lemma proj_reachable_to_cfgE:
      assumes R: "gc\<in>jsys.nodes"
      assumes PIDV: "pid_valid gc pid"
      shows "\<exists>c0\<in>cfgc_V0. (c0,cmd_of_pid gc pid)\<in>cfgc_E\<^sup>*"
    proof -
      from R obtain w where 
        WF: "jsys.path w pid_init_gc"
        and EX: "fold ga_ex w (pid_init_gc) = gc"
        by rule auto
      from words_fin_None_fmt[OF WF] obtain w' n where 
        [simp]: "w = map Some w'@replicate n None" .

      from EX have "fold ga_ex (map Some w') (pid_init_gc) = gc" 
        by simp  
      hence EX': "fold ga_gex w' (pid_init_gc) = gc"
        by (simp add: fold_map some_ga_ex_eq)

      from WF have WF': "jsys.path (map Some w') pid_init_gc" 
        by auto
        
      from proj_word_fin_to_cfg_E[OF WF' EX', of pid] have
        G: "(cmd_of_pid (pid_init_gc) pid,cmd_of_pid gc pid) \<in> cfgc_E\<^sup>*"
        by (rule set_rev_mp[OF _ rtrancl_mono]) auto
        
      show ?thesis proof (cases "pid_valid (pid_init_gc) pid")
        case True 
        hence "cmd_of_pid (pid_init_gc) pid \<in> cfgc_V0"
          by (auto simp: cfgc_V0_def cfg_V0_def pid_init_gc_def init_pc_def)
        with G show ?thesis ..
      next
        case False 
        hence "\<not>pid_valid gc pid"
          unfolding EX[symmetric] by simp 
        with PIDV have False by blast thus ?thesis ..
      qed
    qed

    lemma proj_ne_word_fin_to_cfg_E:
      assumes WF: "jsys.path (map Some w) gc"
      assumes EX: "fold ga_gex w gc = gc'"
      assumes [simp]: "w=(pid,cac)#w'" (is "w=?ga#_")
      shows "(cmd_of_pid gc pid, cmd_of_pid gc' pid) 
        \<in> (cfgc_E \<inter> (\<lambda>(_,c,_,c'). (c,c'))`set w)\<^sup>+" (is "_\<in>?E\<^sup>+")
    proof -
      from WF EX have 
        EN: "?ga \<in> ga_gen gc" and
        WF': "jsys.path (map Some w') (ga_gex ?ga gc)" and
        EX': "fold ga_gex w' (ga_gex ?ga gc) = gc'"
        by (auto simp: some_ga_en_eq some_ga_ex_eq)

      obtain c a c' where [simp]: "cac = (c,a,c')" by (cases cac)

      from EN have "(pid,c,a,c')\<in>ga_gen gc" by simp
      from ga_gen_cmd_cfg[OF this] 
      have "(cmd_of_pid gc pid, cmd_of_pid (ga_gex ?ga gc) pid) \<in> ?E" 
        by auto
      also from proj_word_fin_to_cfg_E[OF WF' EX'] 
      have "(cmd_of_pid (ga_gex ?ga gc) pid, cmd_of_pid gc' pid) \<in> ?E\<^sup>*"
        apply (rule set_rev_mp[OF _ rtrancl_mono])
        by auto
      finally (rtrancl_into_trancl2) show ?thesis .
    qed

  end

  locale sticky_prog = visible_prog +
    fixes sticky_E
    assumes sticky_E_fas: "is_fas cfgc_G sticky_E"  
    assumes sticky_E_vis: "vis_edges \<subseteq> sticky_E"
  begin

    definition "sticky_ga \<equiv> Collect (
      \<lambda>None \<Rightarrow> True 
    | Some (pid,c,a,c') \<Rightarrow> (c,c')\<in>sticky_E)"

    lemma sticky_ga_approx_visible: "jsys.visible \<subseteq> sticky_ga"
    proof -
      have aux: "\<And>s s'. sm_props s \<noteq> sm_props s' \<Longrightarrow> s \<noteq> s'"
        by auto

      show ?thesis
        apply (clarsimp simp: sticky_ga_def split: option.split)
        apply (rule set_mp[OF sticky_E_vis])
        apply (clarsimp 
          elim!: jsys.visibleE 
          simp: sticky_ga_def
          split: option.split)
        apply (clarsimp 
          split: prod.splits
          simp: ga_en_def ga_gen_def ga_ex_def ga_gex_def
          simp: pid_interp_gc_def interp_gs_def
          simp: vis_edges_def)
        apply (intro exI conjI, assumption) 
        apply (drule ex_mod_limit)
        
        apply (drule aux)
        apply (fastforce simp: eq_on_def restrict_map_def)
        done
    qed  

    lemma sticky_ga_breaks_cycles:
      assumes "gc\<in>jsys.nodes"
      assumes "w\<in>jsys.cycles gc"
      assumes "w\<noteq>[]"
      shows "set w \<inter> sticky_ga \<noteq> {}"
    proof (cases "None \<in> set w")
      case True
      thus ?thesis
        by (auto simp: sticky_ga_def)
    next
      case False
      then obtain w' where [simp]: "w=map Some w'"
        by (auto simp: none_notin_set_map_Some_conv)

      have aux1: "Some ` set w' \<inter> sticky_ga 
        = Some ` (set w' \<inter> {(pid,c,a,c'). (c,c')\<in>sticky_E})"
        by (auto simp: sticky_ga_def)
  

      show ?thesis 
      proof (cases "\<exists>(pid,c,a,c')\<in>set w'. (c,c')\<in>sticky_E")
        case True thus ?thesis by (auto simp: aux1)
      next  
        case False 
        let ?E = "(cfgc_E \<inter> (\<lambda>(_, c, _, c'). (c, c')) ` set w')"

        from False have NO_STICKY: "?E \<inter> sticky_E = {}" by auto

        from \<open>w\<noteq>[]\<close> obtain pid cac w'' where W'_FMT[simp]: "w'=(pid,cac)#w''"
          by (auto simp: neq_Nil_conv)

        from \<open>w\<in>jsys.cycles gc\<close> have PIDV: "pid_valid gc pid"
          by (auto simp: pid_valid_ga_en)

        have "(cmd_of_pid gc pid, cmd_of_pid gc pid)\<in> ?E\<^sup>+"
          apply (rule proj_ne_word_fin_to_cfg_E[OF _ _ W'_FMT])
          using \<open>w\<in>jsys.cycles gc\<close>
          by (auto simp: fold_map some_ga_ex_eq)
        hence CYC: "(cmd_of_pid gc pid, cmd_of_pid gc pid) \<in> (cfgc_E-sticky_E)\<^sup>+"
          apply (rule trancl_mono)
          using NO_STICKY by blast

        from proj_reachable_to_cfgE[OF \<open>gc\<in>jsys.nodes\<close> PIDV] obtain
          c0 where C0: "c0\<in>cfgc_V0" and REACH: "(c0,cmd_of_pid gc pid)\<in>cfgc_E\<^sup>*" ..

        from CYC C0 REACH sticky_E_fas[unfolded is_fas_def]
          have False by force
        thus ?thesis ..
      qed
    qed
      
    sublocale jsys: transition_system_sticky 
      ga_ex "\<lambda> a p. a \<in> ga_en p" "\<lambda> p. p = pid_init_gc" pid_interp_gc sticky_ga
      apply unfold_locales
      using sticky_ga_breaks_cycles apply blast
      using sticky_ga_approx_visible apply blast
      done

    sublocale jsys: transition_system_ample ga_ex "\<lambda> a p. a \<in> ga_en p" "\<lambda> p. p = pid_init_gc"
      pid_interp_gc sticky_ga ind
      by unfold_locales

  end

end
