section \<open>Refinement for Transition Systems\<close>

theory Transition_System_Refine
imports
  "Transition_System"
  "Transition_System_Extra"
  "../Basic/Refine"
begin

  lemma path_param[param]: "(transition_system.path, transition_system.path) \<in>
    (T \<rightarrow> S \<rightarrow> S) \<rightarrow> (T \<rightarrow> S \<rightarrow> bool_rel) \<rightarrow> \<langle>T\<rangle> list_rel \<rightarrow> S \<rightarrow> bool_rel"
  proof (rule, rule)
    fix exa exb ena enb
    assume [param]: "(exa, exb) \<in> T \<rightarrow> S \<rightarrow> S" "(ena, enb) \<in> T \<rightarrow> S \<rightarrow> bool_rel"
    interpret A: transition_system exa ena by this
    interpret B: transition_system exb enb by this
    have [param]: "(A.path [] p, B.path [] q) \<in> bool_rel" for p q by auto
    have [param]: "(A.path (a # r) p, B.path (b # s) q) \<in> bool_rel"
      if "(ena a p, enb b q) \<in> bool_rel" "(A.path r (exa a p), B.path s (exb b q)) \<in> bool_rel"
      for a r p b s q
      using that by auto
    show "(A.path, B.path) \<in> \<langle>T\<rangle> list_rel \<rightarrow> S \<rightarrow> bool_rel"
    proof (intro fun_relI)
      show "(A.path r p, B.path s q) \<in> bool_rel" if "(r, s) \<in> \<langle>T\<rangle> list_rel" "(p, q) \<in> S" for r s p q
        using that by (induct arbitrary: p q) (parametricity+)
    qed
  qed
  lemma run_param[param]: "(transition_system.run, transition_system.run) \<in>
    (T \<rightarrow> S \<rightarrow> S) \<rightarrow> (T \<rightarrow> S \<rightarrow> bool_rel) \<rightarrow> \<langle>T\<rangle> stream_rel \<rightarrow> S \<rightarrow> bool_rel"
  proof (rule, rule)
    fix exa exb ena enb
    assume 1: "(exa, exb) \<in> T \<rightarrow> S \<rightarrow> S" "(ena, enb) \<in> T \<rightarrow> S \<rightarrow> bool_rel"
    interpret A: transition_system exa ena by this
    interpret B: transition_system exb enb by this
    show "(A.run, B.run) \<in> \<langle>T\<rangle> stream_rel \<rightarrow> S \<rightarrow> bool_rel"
    proof safe
      show "B.run s q" if "(r, s) \<in> \<langle>T\<rangle> stream_rel" "(p, q) \<in> S" "A.run r p" for r s p q
        using 1[param_fo] that by (coinduction arbitrary: r s p q) (blast elim: stream_rel_cases)
      show "A.run r p" if "(r, s) \<in> \<langle>T\<rangle> stream_rel" "(p, q) \<in> S" "B.run s q" for r s p q
        using 1[param_fo] that by (coinduction arbitrary: r s p q) (blast elim: stream_rel_cases)
    qed
  qed

  lemma paths_param[param]:
    assumes [param]: "(exa, exb) \<in> T \<rightarrow> S \<rightarrow> S"
    assumes "(transition_system.enableds ena, transition_system.enableds enb) \<in> S \<rightarrow> \<langle>T\<rangle> set_rel"
    shows "(transition_system.paths exa ena, transition_system.paths exb enb) \<in> S \<rightarrow> \<langle>\<langle>T\<rangle> list_rel\<rangle> set_rel"
  proof -
    note assms = assms[param_fo, unfolded transition_system.enableds_def]
    interpret A: transition_system exa ena by this
    interpret B: transition_system exb enb by this
    have 1: "\<exists> s. (r, s) \<in> \<langle>T\<rangle> list_rel \<and> B.path s q" if "(p, q) \<in> S" "A.path r p" for p q r
    using that(2, 1)
    proof (induct arbitrary: q)
      case (nil p)
      show ?case by auto
    next
      case (cons a p r)
      obtain b where 1: "(a, b) \<in> T" "enb b q" using assms(2) cons(1, 4) by (blast elim: set_relE1)
      have 2: "(exa a p, exb b q) \<in> S" using cons(4) 1(1) by parametricity
      obtain s where 3: "(r, s) \<in> \<langle>T\<rangle> list_rel" "B.path s (exb b q)" using cons(3) 2 by auto
      show ?case using 1 3 by force
    qed
    have 2: "\<exists> r. (r, s) \<in> \<langle>T\<rangle> list_rel \<and> A.path r p" if "(p, q) \<in> S" "B.path s q" for p q s
    using that(2, 1)
    proof (induct arbitrary: p)
      case (nil q)
      show ?case by auto
    next
      case (cons b q s)
      obtain a where 1: "(a, b) \<in> T" "ena a p" using assms(2) cons(1, 4) by (blast elim: set_relE2)
      have 2: "(exa a p, exb b q) \<in> S" using cons(4) 1(1) by parametricity
      obtain r where 3: "(r, s) \<in> \<langle>T\<rangle> list_rel" "A.path r (exa a p)" using cons(3) 2 by auto
      show ?case using 1 3 by force
    qed
    show ?thesis unfolding transition_system.paths_def set_rel_def using 1 2 by blast
  qed
  lemma runs_param[param]:
    assumes "(exa, exb) \<in> T \<rightarrow> S \<rightarrow> S"
    assumes "(transition_system.enableds ena, transition_system.enableds enb) \<in> S \<rightarrow> \<langle>T\<rangle> set_rel"
    shows "(transition_system.runs exa ena, transition_system.runs exb enb) \<in> S \<rightarrow> \<langle>\<langle>T\<rangle> stream_rel\<rangle> set_rel"
  proof -
    note assms = assms[param_fo, unfolded transition_system.enableds_def]
    interpret A: transition_system exa ena by this
    interpret B: transition_system exb enb by this
    have 1: "\<exists> s. (r, s) \<in> \<langle>T\<rangle> stream_rel \<and> B.run s q" if "(p, q) \<in> S" "A.run r p" for p q r
    proof -
      define P where "P \<equiv> \<lambda> (p, q, r). (p, q) \<in> S \<and> A.run r p"
      define Q where "Q \<equiv> \<lambda> (p :: 'b, q, r) a. (shd r, a) \<in> T \<and> enb a q"
      have 1: "P (p, q, r)" using that unfolding P_def by auto
      have "\<exists> a. Q x a" if "P x" for x
        using assms(2) that unfolding P_def Q_def by (force elim: set_relE1 A.run.cases)
      then obtain f where 2: "\<And> x. P x \<Longrightarrow> Q x (f x)" by metis
      define g where "g \<equiv> \<lambda> (p, q, r). (exa (shd r) p, exb (f (p, q, r)) q, stl r)"
      have 3: "P (g x)" if "P x" for x
        using assms(1) 2 that unfolding P_def Q_def g_def by (auto elim: A.run.cases)
      show ?thesis
      proof (intro exI conjI)
        show "(r, smap f (siterate g (p, q, r))) \<in> \<langle>T\<rangle> stream_rel"
          using 1 2 3 unfolding Q_def g_def by (coinduction arbitrary: p q r) (fastforce)
        show "B.run (smap f (siterate g (p, q, r))) q"
          using 1 2 3 unfolding Q_def g_def by (coinduction arbitrary: p q r) (fastforce)
      qed
    qed
    have 2: "\<exists> r. (r, s) \<in> \<langle>T\<rangle> stream_rel \<and> A.run r p" if "(p, q) \<in> S" "B.run s q" for p q s
    proof -
      define P where "P \<equiv> \<lambda> (p, q, s). (p, q) \<in> S \<and> B.run s q"
      define Q where "Q \<equiv> \<lambda> (p, q :: 'd, s) b. (b, shd s) \<in> T \<and> ena b p"
      have 1: "P (p, q, s)" using that unfolding P_def by auto
      have "\<exists> a. Q x a" if "P x" for x
        using assms(2) that unfolding P_def Q_def by (force elim: set_relE2 B.run.cases)
      then obtain f where 2: "\<And> x. P x \<Longrightarrow> Q x (f x)" by metis
      define g where "g \<equiv> \<lambda> (p, q, s). (exa (f (p, q, s)) p, exb (shd s) q, stl s)"
      have 3: "P (g x)" if "P x" for x
        using assms(1) 2 that unfolding P_def Q_def g_def by (auto elim: B.run.cases)
      show ?thesis
      proof (intro exI conjI)
        show "(smap f (siterate g (p, q, s)), s) \<in> \<langle>T\<rangle> stream_rel"
          using 1 2 3 unfolding Q_def g_def by (coinduction arbitrary: p q s) (fastforce)
        show "A.run (smap f (siterate g (p, q, s))) p"
          using 1 2 3 unfolding Q_def g_def by (coinduction arbitrary: p q s) (fastforce)
      qed
    qed
    show ?thesis unfolding transition_system.runs_def set_rel_def using 1 2 by force
  qed

end