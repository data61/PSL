section \<open>Simulation\<close>
theory Simulation
imports Automata
begin

  lemma finite_ImageI:
    assumes "finite A"  
    assumes "\<And>a. a\<in>A \<Longrightarrow> finite (R``{a})"
    shows "finite (R``A)"
  proof -
    note [[simproc add: finite_Collect]]
    have "R``A = \<Union>{R``{a} | a. a:A}"
      by auto
    also have "finite (\<Union>{R``{a} | a. a:A})"
      apply (rule finite_Union)
      apply (simp add: assms)
      apply (clarsimp simp: assms)
      done
    finally show ?thesis .
  qed


  section \<open>Simulation\<close>


  subsection \<open>Functional Relations\<close>

  definition "the_br_\<alpha> R \<equiv> \<lambda> x. SOME y. (x, y) \<in> R"
  abbreviation (input) "the_br_invar R \<equiv> \<lambda> x. x \<in> Domain R"

  lemma the_br[simp]: 
    assumes "single_valued R"  
    shows "br (the_br_\<alpha> R) (the_br_invar R) = R"
    unfolding build_rel_def the_br_\<alpha>_def
    apply auto
    apply (metis someI_ex)
    apply (metis assms someI_ex single_valuedD)
    done

  lemma the_br_br[simp]: 
    "I x \<Longrightarrow> the_br_\<alpha> (br \<alpha> I) x = \<alpha> x"
    "the_br_invar (br \<alpha> I) = I"
    unfolding the_br_\<alpha>_def build_rel_def[abs_def]
    by auto

  subsection \<open>Relation between Runs\<close>

  definition run_rel :: "('a \<times> 'b) set \<Rightarrow> ('a word \<times> 'b word) set" where
    "run_rel R \<equiv> {(ra, rb). \<forall> i. (ra i, rb i) \<in> R}"

  lemma run_rel_converse[simp]: "(ra, rb) \<in> run_rel (R\<inverse>) \<longleftrightarrow> (rb, ra) \<in> run_rel R"  
    unfolding run_rel_def by auto

  lemma run_rel_single_valued: "single_valued R 
    \<Longrightarrow> (ra, rb) \<in> run_rel R \<longleftrightarrow> ((\<forall>i. the_br_invar R (ra i)) \<and> rb = the_br_\<alpha> R o ra)"
    unfolding run_rel_def the_br_\<alpha>_def
    apply (auto intro!: ext)
    apply (metis single_valuedD someI_ex)
    apply (metis DomainE someI_ex)
    done

  subsection \<open>Simulation\<close>
  locale simulation =
    a: graph A +
    b: graph B
    for R :: "('a \<times> 'b) set"
    and A :: "('a, _) graph_rec_scheme"
    and B :: "('b, _) graph_rec_scheme"
    +
    assumes nodes_sim: "a \<in> a.V \<Longrightarrow> (a, b) \<in> R \<Longrightarrow> b \<in> b.V"
    assumes init_sim: "a0 \<in> a.V0 \<Longrightarrow> \<exists> b0. b0 \<in> b.V0 \<and> (a0, b0) \<in> R"
    assumes step_sim: "(a, a') \<in> a.E \<Longrightarrow> (a, b) \<in> R \<Longrightarrow> \<exists> b'. (b, b') \<in> b.E \<and> (a', b') \<in> R"
  begin

    lemma simulation_this: "simulation R A B" by unfold_locales

    lemma run_sim: 
      assumes arun: "a.is_run ra"
      obtains rb where "b.is_run rb" "(ra, rb) \<in> run_rel R"
    proof -
      from arun have ainit: "ra 0 \<in> a.V0" 
        and astep: "\<forall>i. (ra i, ra (Suc i)) \<in> a.E"
        using a.run_V0 a.run_ipath ipathD by blast+
      from init_sim obtain rb0 where rel0: "(ra 0, rb0) \<in> R" and binit: "rb0 \<in> b.V0"
        by (auto intro: ainit)
  
      define rb
        where "rb = rec_nat rb0 (\<lambda>i rbi. SOME rbsi. (rbi, rbsi) \<in> b.E \<and> (ra (Suc i), rbsi) \<in> R)"
      
      have [simp]: 
        "rb 0 = rb0" 
        "\<And>i. rb (Suc i) = (SOME rbsi. (rb i, rbsi) \<in> b.E \<and> (ra (Suc i), rbsi) \<in> R)"
        unfolding rb_def by auto
  
      {
        fix i
        have "(rb i, rb (Suc i)) \<in> b.E \<and> (ra (Suc i), rb (Suc i)) \<in> R"
        proof (induction i)
          case 0
          from step_sim astep rel0 obtain rb1 where "(rb 0, rb1) \<in> b.E" and "(ra 1, rb1) \<in> R"
            by fastforce
          thus ?case by (auto intro!: someI)
        next
          case (Suc i)
          with step_sim astep obtain rbss where "(rb (Suc i), rbss) \<in> b.E" and
            "(ra (Suc (Suc i)), rbss) \<in> R"
            by fastforce
          thus ?case by (auto intro!: someI)
        qed
      } note aux=this
      
      from aux binit have "b.is_run rb"
        unfolding b.is_run_def ipath_def by simp
      moreover from aux rel0 have "(ra, rb) \<in> run_rel R"
        unfolding run_rel_def
        apply safe
        apply (case_tac i)
        by auto
      ultimately show ?thesis by rule
    qed

    lemma stuck_sim: 
      assumes "(a, b) \<in> R"
      assumes "b \<notin> Domain b.E"
      shows "a \<notin> Domain a.E"
      using assms
      by (auto dest: step_sim)

    lemma run_Domain: "a.is_run r \<Longrightarrow> r i \<in> Domain R"
      by (erule run_sim) (auto simp: run_rel_def)

    lemma br_run_sim:
      assumes "R = br \<alpha> I"
      assumes "a.is_run r"
      shows "b.is_run (\<alpha> o r)"
      using assms
      apply -
      apply (erule run_sim)
      apply (auto simp: run_rel_def build_rel_def a.is_run_def b.is_run_def ipath_def)
      done

    lemma is_reachable_sim: "a \<in> a.E\<^sup>* `` a.V0 \<Longrightarrow> \<exists> b. (a, b) \<in> R \<and> b \<in> b.E\<^sup>* `` b.V0"
      apply safe
      apply (erule rtrancl_induct)
      apply (metis ImageI init_sim rtrancl.rtrancl_refl)
      apply (metis rtrancl_image_advance step_sim)
      done

    lemma reachable_sim: "a.E\<^sup>* `` a.V0 \<subseteq> R\<inverse> `` b.E\<^sup>* `` b.V0"
      using is_reachable_sim by blast

    lemma reachable_finite_sim:
      assumes "finite (b.E\<^sup>* `` b.V0)"
      assumes "\<And>b. b \<in> b.E\<^sup>* `` b.V0 \<Longrightarrow> finite (R\<inverse> `` {b})"
      shows "finite (a.E\<^sup>* `` a.V0)"
      apply (rule finite_subset[OF reachable_sim])
      apply (rule finite_ImageI)
      apply fact+
      done

  end  

  lemma simulation_trans[trans]:
    assumes "simulation R1 A B"
    assumes "simulation R2 B C"
    shows "simulation (R1 O R2) A C"
  proof -
    interpret s1: simulation R1 A B by fact
    interpret s2: simulation R2 B C by fact
    show ?thesis
      apply unfold_locales
      using s1.nodes_sim s2.nodes_sim apply blast
      using s1.init_sim s2.init_sim apply blast
      using s1.step_sim s2.step_sim apply blast
      done
  qed

  lemma (in graph) simulation_refl[simp]: "simulation Id G G" by unfold_locales auto

  locale lsimulation = 
    a: sa A +
    b: sa B +
    simulation R A B
    for R :: "('a \<times> 'b) set"
    and A :: "('a, 'l, _) sa_rec_scheme"
    and B :: "('b, 'l, _) sa_rec_scheme"
    +
    assumes labeling_consistent: "(a, b) \<in> R \<Longrightarrow> a.L a = b.L b"
  begin

    lemma lsimulation_this: "lsimulation R A B" by unfold_locales

    lemma run_rel_consistent: "(ra, rb) \<in> run_rel R \<Longrightarrow> a.L o ra = b.L o rb"
      using labeling_consistent unfolding run_rel_def
      by auto

    lemma accept_sim: "a.accept w \<Longrightarrow> b.accept w"
      unfolding a.accept_def b.accept_def
      apply clarsimp
      apply (erule run_sim)
      apply (auto simp: run_rel_consistent)
      done

  end

  lemma lsimulation_trans[trans]: 
    assumes "lsimulation R1 A B"
    assumes "lsimulation R2 B C"
    shows "lsimulation (R1 O R2) A C"
  proof -
    interpret s1: lsimulation R1 A B by fact
    interpret s2: lsimulation R2 B C by fact
    interpret simulation "R1 O R2" A C
      using simulation_trans s1.simulation_this s2.simulation_this by this
    show ?thesis
      apply unfold_locales
      using s1.labeling_consistent s2.labeling_consistent 
      by auto
  qed

  lemma (in sa) lsimulation_refl[simp]: "lsimulation Id G G" by unfold_locales auto


  subsection \<open>Bisimulation\<close>

  locale bisimulation = 
    a: graph A +
    b: graph B +
    s1: simulation "R" A B +
    s2: simulation "R\<inverse>" B A
    for R :: "('a \<times> 'b) set"
    and A :: "('a, _) graph_rec_scheme"
    and B :: "('b, _) graph_rec_scheme"
  begin

    lemma bisimulation_this: "bisimulation R A B" by unfold_locales

    lemma converse: "bisimulation (R\<inverse>) B A"
    proof -
      interpret simulation "(R\<inverse>)\<inverse>" A B by simp unfold_locales
      show ?thesis by unfold_locales
    qed

    lemma br_run_conv:
      assumes "R = br \<alpha> I"
      shows "b.is_run rb \<longleftrightarrow> (\<exists>ra. rb=\<alpha> o ra \<and> a.is_run ra)"
      using assms
      apply safe
      apply (erule s2.run_sim, auto 
        intro!: ext
        simp: run_rel_def build_rel_def) []
      apply (erule s1.br_run_sim, assumption)
      done

    lemma bri_run_conv:
      assumes "R = (br \<gamma> I)\<inverse>"
      shows "a.is_run ra \<longleftrightarrow> (\<exists>rb. ra=\<gamma> o rb \<and> b.is_run rb)"
      using assms
      apply safe
      apply (erule s1.run_sim, auto simp: run_rel_def build_rel_def intro!: ext) []

      apply (erule s2.run_sim, auto simp: run_rel_def build_rel_def)
      by (metis (no_types, hide_lams) fun_comp_eq_conv)
  
    lemma inj_map_run_eq:
      assumes "inj \<alpha>"
      assumes E: "\<alpha> o r1 = \<alpha> o r2"
      shows "r1 = r2"
    proof (rule ext)
      fix i
      from E have "\<alpha> (r1 i) = \<alpha> (r2 i)"
        by (simp add: comp_def) metis
      with \<open>inj \<alpha>\<close> show "r1 i = r2 i" 
        by (auto dest: injD)
    qed

    lemma br_inj_run_conv:
      assumes INJ: "inj \<alpha>"
      assumes [simp]: "R = br \<alpha> I"
      shows "b.is_run (\<alpha> o ra) \<longleftrightarrow> a.is_run ra"
      apply (subst br_run_conv[OF assms(2)])
      apply (auto dest: inj_map_run_eq[OF INJ])
      done

    lemma single_valued_run_conv:
      assumes "single_valued R"
      shows "b.is_run rb 
        \<longleftrightarrow> (\<exists>ra. rb=the_br_\<alpha> R o ra \<and> a.is_run ra)"
      using assms
      apply safe
      apply (erule s2.run_sim)
      apply (auto simp add: run_rel_single_valued)
      apply (erule s1.run_sim)
      apply (auto simp add: run_rel_single_valued)
      done

    lemma stuck_bisim: 
      assumes A: "(a, b) \<in> R"
      shows "a \<in> Domain a.E \<longleftrightarrow> b \<in> Domain b.E"
      using s1.stuck_sim[OF A]
      using s2.stuck_sim[OF A[THEN converseI[of _ _ R]]]
      by blast

  end

  lemma bisimulation_trans[trans]:
    assumes "bisimulation R1 A B" 
    assumes "bisimulation R2 B C"
    shows "bisimulation (R1 O R2) A C"
  proof -
    interpret s1: bisimulation R1 A B by fact
    interpret s2: bisimulation R2 B C by fact
    interpret t1: simulation "(R1 O R2)" A C
      using simulation_trans s1.s1.simulation_this s2.s1.simulation_this by this
    interpret t2: simulation "(R1 O R2)\<inverse>" C A
      using simulation_trans s2.s2.simulation_this s1.s2.simulation_this
      unfolding converse_relcomp
      by this
    show ?thesis by unfold_locales
  qed

  lemma (in graph) bisimulation_refl[simp]: "bisimulation Id G G" by unfold_locales auto

  locale lbisimulation = 
    a: sa A +
    b: sa B +
    s1: lsimulation "R" A B +
    s2: lsimulation "R\<inverse>" B A +
    bisimulation R A B
    for R :: "('a \<times> 'b) set"
    and A :: "('a, 'l, _) sa_rec_scheme"
    and B :: "('b, 'l, _) sa_rec_scheme"
  begin

    lemma lbisimulation_this: "lbisimulation R A B" by unfold_locales

    lemma accept_bisim: "a.accept = b.accept"
      apply (rule ext)
      using s1.accept_sim s2.accept_sim by blast

  end

  lemma lbisimulation_trans[trans]:
    assumes "lbisimulation R1 A B" 
    assumes "lbisimulation R2 B C"
    shows "lbisimulation (R1 O R2) A C"
  proof -
    interpret s1: lbisimulation R1 A B by fact
    interpret s2: lbisimulation R2 B C by fact

    from lsimulation_trans[OF s1.s1.lsimulation_this s2.s1.lsimulation_this]
    interpret t1: lsimulation "(R1 O R2)" A C .

    from lsimulation_trans[OF s2.s2.lsimulation_this s1.s2.lsimulation_this, folded converse_relcomp]
    interpret t2: lsimulation "(R1 O R2)\<inverse>" C A .

    show ?thesis by unfold_locales
  qed

  lemma (in sa) lbisimulation_refl[simp]: "lbisimulation Id G G" by unfold_locales auto

end
