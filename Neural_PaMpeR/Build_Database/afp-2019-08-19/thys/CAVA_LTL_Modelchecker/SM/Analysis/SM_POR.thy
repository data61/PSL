theory SM_POR
imports SM_Sticky
begin

  context transition_system_concurrent begin
    lemma pac_en_blocked':
      assumes A: "s \<in> nodes" "path w s" "pac p \<inter> {a. en a s} \<inter> set w = {}"
      assumes IS: "\<And>s' a. \<lbrakk>pac p \<inter> {a. en a s} = pac p \<inter> {a. en a s'};
        psen p s = psen p s'; en a s'; a\<notin>pac p \<rbrakk> \<Longrightarrow>
        pac p \<inter> {b. en b (ex a s')} = pac p \<inter> {a. en a s'} \<and> psen p (ex a s') = psen p s'"
      shows "pac p \<inter> set w = {}"
    proof (rule words_fin_blocked[OF _ A(2,3)])
      fix w
      assume "path w s" "pac p \<inter> set w = {}"
      hence "pac p \<inter> {a. en a s} = pac p \<inter> {a. en a (target w s)} \<and> psen p s = psen p (fold ex w s)"
      proof (induction w rule: rev_induct)
        case (snoc a w) 
        from snoc have 
          "pac p \<inter> {a. en a s} = pac p \<inter> {a. en a (target w s)}"
          "psen p s = psen p (fold ex w s)"
          by auto
        with IS[OF this] snoc.prems show ?case by auto 
      qed simp
      thus "pac p \<inter> {a. en a (target w s)} \<subseteq> pac p \<inter> {a. en a s}" by blast
    qed
  
  end

  context cprog begin
    definition is_ample_static :: "cmdc \<Rightarrow> bool" where
      "is_ample_static c \<equiv> \<forall>a c'. cfgc c a c' \<longrightarrow>
        read_globals a = {} \<and> write_globals a = {}"

  end      

  context visible_prog 
  begin
    lemma None_ga_en_conv[simp]: 
      "None\<in>ga_en gc \<longleftrightarrow> ga_en gc = {None}"
      by (auto simp: ga_en_def stutter_extend_en_def)

      
    lemma genabled_no_global_read_indep_other_pids:
      assumes "read_globals a = {}" 
      assumes "pid'\<noteq>pid"
      shows "(pid,c,a, c')\<in>ga_gen (ga_gex (pid',cac') gc) 
        \<longleftrightarrow> (pid,c,a, c')\<in>ga_gen gc"
      using assms 
      apply (auto 
        simp: ga_gen_def ga_gex_def ex_pres_en
        split: prod.splits)
      done    


  end

  definition pid_pac :: "pid \<Rightarrow> global_action option set" where
    "pid_pac pid \<equiv> Collect (\<lambda>Some (pid',_) \<Rightarrow> pid'=pid | None \<Rightarrow> True)"

  lemma pid_pac_None[simp]: "None \<in> pid_pac pid"
    by (auto simp: pid_pac_def)


  context visible_prog
  begin  

    definition pid_procs :: "pid_global_config \<Rightarrow> pid set" where
      "pid_procs gc \<equiv> {0..<length (pid_global_config.processes gc)}"

    definition pid_psen :: "pid \<Rightarrow> pid_global_config \<Rightarrow> global_action option set"
      where "pid_psen pid gc \<equiv> insert None 
        (Some`{(pid,c,a,c') | c a c'. c = cmd_of_pid gc pid \<and> cfgc c a c'})"

    sublocale jsys: transition_system_concurrent
      ga_ex "\<lambda> a p. a \<in> ga_en p" "\<lambda> p. p = pid_init_gc"
      pid_procs pid_pac pid_psen
    
      apply unfold_locales
      
      apply (auto simp: pid_procs_def) []

      apply (auto 
        simp: pid_pac_def pid_psen_def ga_en_def ga_gen_def
        simp: stutter_extend_en_def
        split: option.splits
        ) []
      
      apply (auto 
        simp: pid_pac_def pid_psen_def ga_en_def ga_gen_def
        simp: stutter_extend_en_def ga_ex_def ga_gex_def
        split: option.splits if_split_asm prod.splits
        ) []
      done

  end

  locale ample_prog = sticky_prog +
    fixes ga_ample :: "pid_global_config \<Rightarrow> global_action option set"
    assumes ga_ample_approx: 
    "\<lbrakk>gc \<in> (g_E ga_automaton)\<^sup>* `` g_V0 ga_automaton; ga_ample gc \<noteq> ga_en gc\<rbrakk> \<Longrightarrow> 
      ga_ample gc \<inter> sticky_ga = {}
    \<and> ga_ample gc \<noteq> {}
    \<and> (\<exists>pid. 
        ga_ample gc = ga_en gc \<inter> pid_pac pid 
      \<and> is_ample_static (cmd_of_pid gc pid))"

  begin

    lemma pid_enabled_ample:
      assumes REACH[simp, intro!]: "gc \<in> ga.E\<^sup>* `` ga.V0"
      shows "jsys.ample_set gc (ga_ample gc)"
    proof (cases "ga_ample gc = ga_en gc")
      case True thus ?thesis using jsys.ample_en by auto
    next
      case False
      from ga_ample_approx[OF REACH False] obtain pid where 
        AMPLE_SS: "ga_ample gc \<subseteq> ga_en gc"
      and NE: "ga_ample gc \<noteq> {}"  
      and NS: "ga_ample gc \<inter> sticky_ga = {}"
      and AMPLE_FMT: "ga_ample gc = pid_pac pid \<inter> ga_en gc"
      and A_STATIC: "is_ample_static (cmd_of_pid gc pid)"
        by blast
      hence aux1: "ga_ample gc = ga_ample gc \<inter> ga_en gc" by blast
  
      from False NE AMPLE_SS have NN: "None \<notin> ga_en gc" by auto

      
      from A_STATIC have LOC: "
        \<And>c a c'. Some (pid, c,a,c') \<in> pid_psen pid gc 
          \<Longrightarrow> read_globals a = {} \<and> write_globals a = {}"
        unfolding is_ample_static_def pid_psen_def 
        by auto
      from A_STATIC have LOC': "
        \<And>c a c'. Some (pid, c,a,c') \<in> pid_pac pid \<inter> ga_en gc 
          \<Longrightarrow> read_globals a = {} \<and> write_globals a = {}"
        unfolding is_ample_static_def pid_pac_def ga_en_def 
        by (auto split: prod.splits simp:  ga_gen_def)

      from reachable_alt[symmetric] REACH 
      have REACH': "gc \<in> jsys.nodes" by simp  

      have INV': 
        "\<And>c a c'. Some (pid,c,a,c')\<in>ga_en gc 
        \<Longrightarrow> Some (pid,c,a,c') \<notin> jsys.visible"
        using NS sticky_ga_approx_visible
        apply (clarsimp simp: AMPLE_FMT pid_pac_def split: option.splits) 
        apply blast
        done

      { 
        fix ga gc'
        assume en_eq: "pid_pac pid \<inter> ga_en gc = pid_pac pid \<inter> ga_en gc'"
        assume psen_eq: "pid_psen pid gc = pid_psen pid gc'"
        assume ga_en: "ga \<in> ga_en gc'" 
        assume ga_not_pid: "ga \<notin> pid_pac pid"
        
        from en_eq NN have [simp]: "None \<notin> ga_en gc'"
          using pid_pac_None
          by blast

        with ga_en have "ga\<noteq>None" by metis
        then obtain pid' c a c' where [simp]: "ga = Some (pid',c,a,c')"
          by (cases ga) auto
  
        from ga_not_pid have [simp]: "pid'\<noteq>pid" by (auto simp: pid_pac_def)
        
        have [simp]: "\<And>cac. Some (pid,cac) \<in> ga_en gc' 
          \<longleftrightarrow> Some (pid,cac) \<in> ga_en gc"
          using en_eq unfolding pid_pac_def
            by (auto split: option.splits)
        hence pid_gen_gc'_gc: "\<And>cac. (pid,cac) \<in> ga_gen gc' 
          \<longleftrightarrow> (pid,cac) \<in> ga_gen gc"
          unfolding ga_en_def
          by simp
  
        have "cmd_of_pid (ga_gex (pid', c, a, c') gc') pid 
          = cmd_of_pid gc' pid"
          by (auto simp: ga_gex_def split: prod.splits)
        hence G1: "pid_psen pid (ga_ex ga gc') = pid_psen pid gc'"
          by (auto simp: pid_psen_def ga_gex_def ga_ex_def
            split: prod.splits)
  
        have pid_ge_ex_invar: "\<And>cac. 
          (pid,cac)\<in>ga_gen (ga_ex (Some (pid', c, a, c')) gc') \<longleftrightarrow>
          (pid,cac)\<in>ga_gen gc'"
          apply (clarsimp simp: ga_en_def ga_ex_def) 
        proof
          fix c'' a'' c'''
          assume A: "(pid, c'', a'', c''') \<in> ga_gen (ga_gex (pid', c, a, c') gc')"
          hence "Some (pid, c'', a'', c''') \<in> pid_psen pid (ga_gex (pid', c, a, c') gc')"
            by (auto simp: pid_psen_def ga_gen_def)
          hence "Some (pid, c'', a'', c''') \<in> pid_psen pid gc" using G1 psen_eq
            by (simp add: ga_ex_def)
          from LOC[OF this]
            have "read_globals a'' = {}" by simp
          from genabled_no_global_read_indep_other_pids[OF this \<open>pid'\<noteq>pid\<close>] A
          show "((pid, c'', a'', c''') \<in> ga_gen gc')" ..
        next
          fix c'' a'' c'''
          assume A: "((pid, c'', a'', c''') \<in> ga_gen gc')"
          hence "Some (pid, c'', a'', c''') \<in> pid_psen pid gc'"
            by (auto simp: pid_psen_def ga_gen_def)
          hence "Some (pid, c'', a'', c''') \<in> pid_psen pid gc" using psen_eq
            by (simp)
          from LOC[OF this] have "read_globals a'' = {}" by simp
          from genabled_no_global_read_indep_other_pids[OF this \<open>pid'\<noteq>pid\<close>] A
          show "(pid, c'', a'', c''') \<in> ga_gen (ga_gex (pid', c, a, c') gc')" ..
        qed
  
        have [simp]: 
          "ga_gen (ga_ex (Some (pid', c, a, c')) gc') \<noteq> {}"
          "ga_gen gc' \<noteq> {}"
        proof -
          from NN NE obtain cac2 where "Some (pid,cac2) \<in> ga_en gc"
            unfolding AMPLE_FMT
            apply (clarsimp simp: ex_in_conv[symmetric])
            using NN
            apply (auto simp: pid_pac_def split: option.splits)
            done
          hence "(pid,cac2) \<in> ga_gen gc" by (auto simp: ga_en_def)
          hence 1: "(pid,cac2) \<in> ga_gen gc'"
            by (simp add: pid_gen_gc'_gc)
          thus "ga_gen gc' \<noteq> {}" by blast
          from 1 have "(pid,cac2) \<in> ga_gen (ga_ex (Some (pid', c, a, c')) gc')"
            by (simp add: pid_ge_ex_invar pid_gen_gc'_gc)
          thus "ga_gen (ga_ex (Some (pid', c, a, c')) gc') \<noteq> {}" by blast  
        qed
        
        have G2: "pid_pac pid \<inter> ga_en (ga_ex ga gc') =
             pid_pac pid \<inter> ga_en gc'"
          apply (auto simp: pid_pac_def split: option.splits)
          apply (auto simp add: ga_en_def stutter_extend_en_def
              pid_ge_ex_invar
              split: if_split_asm) [2]
          done
        note G1 G2
      } note aux=this

      show ?thesis
        apply (subst AMPLE_FMT)
        apply (rule jsys.restrict_ample_set[unfolded Collect_mem_eq])
        apply (simp add: reachable_alt del: ga_automaton_simps)
        using NE AMPLE_FMT apply blast
        using NS AMPLE_FMT apply blast
        apply safe []
        apply (rename_tac ga1 ga2)
        apply (case_tac "(ga1,ga2)" rule: ind.cases) 
        using NN apply (simp_all) [4]
        apply (simp_all add: pid_pac_def LOC' INV') []
        
        apply (rule jsys.pac_en_blocked'[OF REACH'])
        unfolding Collect_mem_eq
        apply assumption+
        apply (rule conjI)
        apply (rule aux, assumption+)
        apply (rule aux, assumption+)
        done
    qed
  
    sublocale jsys: ample_abstract
      ga_ex "\<lambda> a p. a \<in> ga_en p" "\<lambda> p. p = pid_init_gc" 
      pid_interp_gc ind "jsys.scut\<inverse>\<inverse>" "\<lambda> a p. a \<in> ga_ample p"
      apply unfold_locales
      unfolding Collect_mem_eq
      apply (rule pid_enabled_ample)
      apply (simp add: reachable_alt)
      done

    definition "ample_rel \<equiv> rel_of_enex (ga_ample, ga_ex)"
    definition "ample_succ \<equiv> succ_of_enex (ga_ample, ga_ex)"

    definition reduced_automaton
      where "reduced_automaton =
        \<lparr> g_V = UNIV, g_E = ample_rel, g_V0 = {pid_init_gc}, sa_L = pid_interp_gc \<rparr>"

    lemma reduced_automaton_simps[simp]:
      "g_V reduced_automaton = UNIV"
      "g_E reduced_automaton = ample_rel"
      "g_V0 reduced_automaton = {pid_init_gc}"
      "sa_L reduced_automaton = pid_interp_gc"
      unfolding reduced_automaton_def by auto

    sublocale ample: sa reduced_automaton by unfold_locales auto

    lemma jsys_R_lang_eq: "snth ` jsys.R.language = Collect ample.accept"
      apply (subst system_complete_language_eq_lsystem_accept)
      using ample.sa_axioms
      unfolding reduced_automaton_def ample_rel_def
      apply simp
      apply (auto simp: ample_rel_def sngp_sym_conv)
      done

    lemma ample_accept_subset: "ample.accept w \<Longrightarrow> lv.sa.accept w"
    proof -
      assume "ample.accept w"
      hence "w \<in> snth ` jsys.R.language" by (simp add: jsys_R_lang_eq)
      hence "w \<in> snth ` jsys.language" using jsys.reduction_language_subset by auto
      with jsys_lang_eq show "lv.sa.accept w" by auto
    qed

    lemma ample_accept_stuttering:
      assumes A: "lv.sa.accept w" 
      obtains w' where "w\<approx>w'" "ample.accept w'"
    proof -
      from A have "w \<in> snth ` jsys.language" by (simp add: jsys_lang_eq)
      then obtain w' where "w \<approx> w'" "w' \<in> snth ` jsys.R.language"
        by (auto elim!: jsys.reduction_language_stuttering)
      hence "ample.accept w'" by (simp add: jsys_R_lang_eq)
      thus ?thesis using \<open>w\<approx>w'\<close> by (blast intro: that)
    qed
  end


end

