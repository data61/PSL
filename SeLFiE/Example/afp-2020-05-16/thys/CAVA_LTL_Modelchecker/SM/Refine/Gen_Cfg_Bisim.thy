theory Gen_Cfg_Bisim
imports Gen_Scheduler_Refine
begin

  (* TODO: Move? *)
  (* TODO: we should consistenly use relations here *)

  subsection \<open>Functional Relations\<close>

  definition "build_relp \<alpha> I x y \<equiv> y=\<alpha> x \<and> I x"
  abbreviation "brp \<equiv> build_relp"

  lemma brp_right_unique[simp, intro!]: "right_unique (brp \<alpha> I)"
    apply (rule right_uniqueI)
    unfolding build_relp_def
    by auto

  definition "the_brp_\<alpha> R \<equiv> (\<lambda>x. SOME y. R x y)"
  abbreviation (input) "the_brp_invar \<equiv> Domainp"

  lemma the_brp[simp]: 
    assumes "right_unique R"  
    shows "brp (the_brp_\<alpha> R) (the_brp_invar R) = R"
      apply (rule sym)
      apply (intro ext)
      unfolding build_relp_def the_brp_\<alpha>_def
      apply auto
      apply (metis assms right_uniqueD someI)
      by (blast intro: someI)

  lemma obtain_brp:
    assumes "right_unique R"  
    obtains \<alpha> I where "R=brp \<alpha> I"
    using the_brp[OF assms, THEN sym] ..

  lemma the_brp_brp[simp]: 
    "I x \<Longrightarrow> the_brp_\<alpha> (brp \<alpha> I) x = \<alpha> x"
    "the_brp_invar (brp \<alpha> I) = I"
    unfolding the_brp_\<alpha>_def build_relp_def[abs_def]
    by (auto)

  lemma brp_comp[simp]: "brp \<alpha>1 I1 OO brp \<alpha>2 I2 = brp (\<alpha>2 o \<alpha>1) (\<lambda>x. I1 x \<and> I2 (\<alpha>1 x))"
    unfolding build_relp_def[abs_def] by auto

  lemma rel_of_pred_brp[simp]: "rel_of_pred (brp \<alpha> invar) = br \<alpha> invar"
    unfolding build_relp_def[abs_def] build_rel_def by auto


  lemma rel_option_add_simps[simp]: 
    "rel_option R None c \<longleftrightarrow> c=None"
    "rel_option R d None \<longleftrightarrow> d=None"
    apply (cases c, auto) []
    apply (cases d, auto) []
    done

  lemma rel_option_Some_conv: 
    "rel_option R (Some v) d \<longleftrightarrow> (\<exists>w. R v w \<and> d = Some w)"
    "rel_option R c (Some w) \<longleftrightarrow> (\<exists>v. R v w \<and> c = Some v)"
    apply (cases d, auto)
    apply (cases c, auto)
    done

  lemma rel_mset_plus_conv:
    "rel_mset R ({#a#}+m') n \<longleftrightarrow> (\<exists>b n'. n={#b#}+n' \<and> R a b \<and> rel_mset R m' n')"  
    "rel_mset R m ({#b#}+n') \<longleftrightarrow> (\<exists>a m'. m={#a#}+m' \<and> R a b \<and> rel_mset R m' n')"  
    apply (auto simp: union_mset_add_mset_left)
    apply (metis msed_rel_invL)
    apply (metis rel_mset_Plus)
    apply (metis msed_rel_invR)
    apply (metis rel_mset_Plus)
    done      

  lemma rel_mset_brp: 
    "rel_mset (brp \<alpha> I) = brp (image_mset \<alpha>) (\<lambda>m. \<forall>x. x:#m \<longrightarrow> I x)"
  proof (intro ext iffI)
    fix m m'
    assume "rel_mset (brp \<alpha> I) m m'"
    thus "brp (image_mset \<alpha>) (\<lambda>m. \<forall>x. x:#m \<longrightarrow> I x) m m'"
      apply (induction "(brp \<alpha> I)" _ _ rule: rel_mset_induct)
      apply (auto simp: build_relp_def)
      done
  next
    fix m m'
    assume "brp (image_mset \<alpha>) (\<lambda>m. \<forall>x. x \<in># m \<longrightarrow> I x) m m'"
    hence 1: "m' = image_mset \<alpha> m" 
      and "\<forall>x. x \<in># m \<longrightarrow> I x" by (auto simp: build_relp_def)
    from this(2) show "rel_mset (brp \<alpha> I) m m'"
      unfolding 1
      apply (induction m)
      apply (simp add: rel_mset_Zero)
      apply simp
      apply (rule rel_mset_Plus)
      apply (simp add: build_relp_def)
      .
  qed

  locale Gen_Cfg_Bisim_Pre =
    s1: Gen_Scheduler' cstep1 en ex
  + s2: Gen_Scheduler' cstep2 en ex 
    for rel_c :: "'c \<Rightarrow> 'd \<Rightarrow> bool"
    and cstep1 :: "'c \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool"
    and cstep2 :: "'d \<Rightarrow> 'a \<Rightarrow> 'd \<Rightarrow> bool"
    and en 
    and ex :: "('ls\<times>'gs) \<Rightarrow> 'a \<Rightarrow> ('ls\<times>'gs)" +
    assumes csim1: "\<lbrakk>cstep1 c a c'; rel_c c d \<rbrakk> \<Longrightarrow> \<exists>d'. rel_c c' d' \<and> cstep2 d a d'"
    assumes csim2: "\<lbrakk>cstep2 d a d'; rel_c c d \<rbrakk> \<Longrightarrow> \<exists>c'. rel_c c' d' \<and> cstep1 c a c'"
  begin

    (* TODO: we should consistenly use relations here *)
    definition rel_lc :: "('c,'ls) local_config \<Rightarrow> ('d,'ls) local_config \<Rightarrow> bool"
    where "rel_lc lc ld \<equiv> 
      rel_c (local_config.command lc) (local_config.command ld) 
    \<and> local_config.state lc = local_config.state ld"

    definition rel_gc :: "('c,'ls,'gs)global_config \<Rightarrow> ('d,'ls,'gs)global_config \<Rightarrow> bool"
    where "rel_gc gc gd \<equiv> 
      rel_mset rel_lc (global_config.processes gc) (global_config.processes gd)
    \<and> global_config.state gc = global_config.state gd"

    lemma gstep_sim1: "\<lbrakk>(c, c') \<in> s1.gstep; rel_gc c d\<rbrakk> \<Longrightarrow> \<exists>d'. rel_gc c' d' \<and> (d, d') \<in> s2.gstep"
      apply (cases c, simp_all)
      apply (erule s1.gstep_succE)
      apply (auto 
        simp: rel_option_Some_conv rel_gc_def rel_lc_def
        simp: rel_mset_plus_conv 
        )
      apply (drule (1) csim1, clarsimp)
      apply (drule (3) s2.gstep_succI, force)
      done

    lemma gstep_sim2: "\<lbrakk>(d, d') \<in> s2.gstep; rel_gc c d\<rbrakk> \<Longrightarrow> \<exists>c'. rel_gc c' d' \<and> (c, c') \<in> s1.gstep"
      apply (cases d, simp_all)
      apply (erule s2.gstep_succE)
      apply (auto 
        simp: rel_option_Some_conv rel_gc_def rel_lc_def
        simp: rel_mset_plus_conv
        )
      apply (drule (1) csim2, clarsimp)
      apply (drule (1) s1.gstep_succI, simp_all, force) 
      done

    lemma left_unique_rel_lcI:
      assumes "left_unique rel_c"
      shows "left_unique rel_lc"
    proof (rule left_uniqueI)
      fix lc1 lc2 lc3
      assume "rel_lc lc1 lc2" "rel_lc lc3 lc2"
      thus "lc1=lc3"
        apply (cases lc1, cases lc2, cases lc3, simp_all)
        apply (auto simp: rel_lc_def left_uniqueD[OF assms])
        done
    qed

    lemma right_unique_rel_lcI:
      assumes "right_unique rel_c"
      shows "right_unique rel_lc"
    proof (rule right_uniqueI)
      fix lc1 lc2 lc3
      assume "rel_lc lc2 lc1" "rel_lc lc2 lc3"
      thus "lc1=lc3"
        apply (cases lc1, cases lc2, cases lc3, simp_all)
        apply (auto simp: rel_lc_def right_uniqueD[OF assms])
        done
    qed

    lemma bi_unique_rel_lcI:
      assumes "bi_unique rel_c"
      shows "bi_unique rel_lc"
      using assms 
      by (auto simp: bi_unique_alt_def right_unique_rel_lcI left_unique_rel_lcI)

    lemma left_unique_rel_gcI:
      assumes "left_unique rel_c"
      shows "left_unique rel_gc"
    proof (rule left_uniqueI)
      note A = left_unique_rel_lcI[OF assms, THEN multiset.left_unique_rel]

      fix gc1 gc2 gc3
      assume "rel_gc gc1 gc2" "rel_gc gc3 gc2"
      thus "gc1=gc3"
        apply (cases gc1, cases gc2, cases gc3, simp_all)
        apply (auto simp: rel_gc_def left_uniqueD[OF A])
        done
    qed

    lemma right_unique_rel_gcI:
      assumes "right_unique rel_c"
      shows "right_unique rel_gc"
    proof (rule right_uniqueI)
      note A = right_unique_rel_lcI[OF assms, THEN multiset.right_unique_rel]

      fix gc1 gc2 gc3
      assume "rel_gc gc1 gc2" "rel_gc gc1 gc3"
      thus "gc2=gc3"
        apply (cases gc1, cases gc2, cases gc3, simp_all)
        apply (auto simp: rel_gc_def right_uniqueD[OF A])
        done
    qed

    lemma bi_unique_rel_gcI:
      assumes "bi_unique rel_c"
      shows "bi_unique rel_gc"
      using assms 
      by (auto simp: bi_unique_alt_def right_unique_rel_gcI left_unique_rel_gcI)

  end


  locale Gen_Cfg_LBisim =
    Gen_Cfg_Bisim_Pre rel_c cstep1 cstep2 en ex
    for rel_c :: "'c \<Rightarrow> 'd \<Rightarrow> bool"
    and cstep1 :: "'c \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool"
    and init1 :: "('c,'ls,'gs)global_config set"
    and label1 :: "('c,'ls,'gs)global_config \<Rightarrow> 'l"
    and cstep2 :: "'d \<Rightarrow> 'a \<Rightarrow> 'd \<Rightarrow> bool"
    and init2 :: "('d,'ls,'gs)global_config set"
    and label2 :: "('d,'ls,'gs)global_config \<Rightarrow> 'l"
    and en 
    and ex :: "('ls\<times>'gs) \<Rightarrow> 'a \<Rightarrow> ('ls\<times>'gs)" +
    assumes init_sim1: "\<And>a0. a0 \<in> init1 \<Longrightarrow> \<exists>b0. b0 \<in> init2 \<and> rel_gc a0 b0"
    assumes init_sim2: "\<And>b0. b0 \<in> init2 \<Longrightarrow> \<exists>a0. a0 \<in> init1 \<and> rel_gc a0 b0"
    assumes labeling_consistent: "\<And>a b. rel_gc a b \<Longrightarrow> label1 a = label2 b"
  begin

    sublocale s1: Gen_Scheduler'_linit cstep1 en ex init1 label1 by this
    sublocale s2: Gen_Scheduler'_linit cstep2 en ex init2 label2 by this

    sublocale lbisimulation "rel_of_pred rel_gc" s1.system_automaton s2.system_automaton
    proof -
      interpret bisim:
        lbisimulation "rel_of_pred rel_gc" s1.system_automaton' s2.system_automaton'
        apply unfold_locales
        apply simp_all
        using init_sim1 apply force
        using gstep_sim1 apply force
        using labeling_consistent apply force
        using init_sim2 apply force
        using gstep_sim2 apply force
        using labeling_consistent apply force
        done
      interpret bisim:
        lbisimulation "rel_of_pred rel_gc" s1.system_automaton s2.system_automaton
        unfolding s1.system_automaton_alt_def s2.system_automaton_alt_def
        using bisim.lstutter_extend by this
      show "lbisimulation (rel_of_pred rel_gc) s1.system_automaton s2.system_automaton"
        by unfold_locales
    qed

  end    

end

