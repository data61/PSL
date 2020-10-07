section \<open>Transition Systems\<close>

theory Transition_System_Extensions
imports
  "Basics/Word_Prefixes"
  "Extensions/Set_Extensions"
  "Extensions/Relation_Extensions"
  Transition_Systems_and_Automata.Transition_System
  Transition_Systems_and_Automata.Transition_System_Extra
  Transition_Systems_and_Automata.Transition_System_Construction
begin

  context transition_system_initial
  begin

    definition cycles :: "'state \<Rightarrow> 'transition list set"
      where "cycles p \<equiv> {w. path w p \<and> target w p = p}"

    lemma cyclesI[intro!]:
      assumes "path w p" "target w p = p"
      shows "w \<in> cycles p"
      using assms unfolding cycles_def by auto
    lemma cyclesE[elim!]:
      assumes "w \<in> cycles p"
      obtains "path w p" "target w p = p"
      using assms unfolding cycles_def by auto

    inductive_set executable :: "'transition set"
      where executable: "p \<in> nodes \<Longrightarrow> enabled a p \<Longrightarrow> a \<in> executable"

    lemma executableI_step[intro!]:
      assumes "p \<in> nodes" "enabled a p"
      shows "a \<in> executable"
      using executable assms by this
    lemma executableI_words_fin[intro!]:
      assumes "p \<in> nodes" "path w p"
      shows "set w \<subseteq> executable"
      using assms by (induct w arbitrary: p, auto del: subsetI)
    lemma executableE[elim?]:
      assumes "a \<in> executable"
      obtains p
      where "p \<in> nodes" "enabled a p"
      using assms by induct auto

  end

  locale transition_system_interpreted =
    transition_system ex en
    for ex :: "'action \<Rightarrow> 'state \<Rightarrow> 'state"
    and en :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    and int :: "'state \<Rightarrow> 'interpretation"
  begin

    definition visible :: "'action set"
      where "visible \<equiv> {a. \<exists> q. en a q \<and> int q \<noteq> int (ex a q)}"

    lemma visibleI[intro]:
      assumes "en a q" "int q \<noteq> int (ex a q)"
      shows "a \<in> visible"
      using assms unfolding visible_def by auto
    lemma visibleE[elim]:
      assumes "a \<in> visible"
      obtains q
      where "en a q" "int q \<noteq> int (ex a q)"
      using assms unfolding visible_def by auto

    abbreviation "invisible \<equiv> - visible"

    lemma execute_fin_word_invisible:
      assumes "path w p" "set w \<subseteq> invisible"
      shows "int (target w p) = int p"
      using assms by (induct w arbitrary: p rule: list.induct, auto)
    lemma execute_inf_word_invisible:
      assumes "run w p" "k \<le> l" "\<And> i. k \<le> i \<Longrightarrow> i < l \<Longrightarrow> w !! i \<notin> visible"
      shows "int ((p ## trace w p) !! k) = int ((p ## trace w p) !! l)"
    proof -
      have "(p ## trace w p) !! l = target (stake l w) p" by simp
      also have "stake l w = stake k w @ stake (l - k) (sdrop k w)" using assms(2) by simp
      also have "target \<dots> p = target (stake (l - k) (sdrop k w)) (target (stake k w) p)"
        unfolding fold_append comp_apply by rule
      also have "int \<dots> = int (target (stake k w) p)"
      proof (rule execute_fin_word_invisible)
        have "w = stake l w @- sdrop l w" by simp
        also have "stake l w = stake k w @ stake (l - k) (sdrop k w)" using assms(2) by simp
        finally have 1: "run (stake k w @- stake (l - k) (sdrop k w) @- sdrop l w) p"
          unfolding shift_append using assms(1) by simp
        show "path (stake (l - k) (sdrop k w)) (target (stake k w) p)" using 1 by auto
        show "set (stake (l - k) (sdrop k w)) \<subseteq> invisible" using assms(3) by (auto simp: set_stake_snth)
      qed
      also have "\<dots> = int ((p ## trace w p) !! k)" by simp
      finally show ?thesis by rule
    qed

  end

  locale transition_system_complete =
    transition_system_initial ex en init +
    transition_system_interpreted ex en int
    for ex :: "'action \<Rightarrow> 'state \<Rightarrow> 'state"
    and en :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    and init :: "'state \<Rightarrow> bool"
    and int :: "'state \<Rightarrow> 'interpretation"
  begin

    definition language :: "'interpretation stream set"
      where "language \<equiv> {smap int (p ## trace w p) |p w. init p \<and> run w p}"

    lemma languageI[intro!]:
      assumes "w = smap int (p ## trace v p)" "init p" "run v p"
      shows "w \<in> language"
      using assms unfolding language_def by auto
    lemma languageE[elim!]:
      assumes "w \<in> language"
      obtains p v
      where "w = smap int (p ## trace v p)" "init p" "run v p"
      using assms unfolding language_def by auto

  end

  locale transition_system_finite_nodes =
    transition_system_initial ex en init
    for ex :: "'action \<Rightarrow> 'state \<Rightarrow> 'state"
    and en :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    and init :: "'state \<Rightarrow> bool"
    +
    assumes reachable_finite: "finite nodes"

  locale transition_system_cut =
    transition_system_finite_nodes ex en init
    for ex :: "'action \<Rightarrow> 'state \<Rightarrow> 'state"
    and en :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    and init :: "'state \<Rightarrow> bool"
    +
    fixes cuts :: "'action set"
    assumes cycles_cut: "p \<in> nodes \<Longrightarrow> w \<in> cycles p \<Longrightarrow> w \<noteq> [] \<Longrightarrow> set w \<inter> cuts \<noteq> {}"
  begin

    inductive scut :: "'state \<Rightarrow> 'state \<Rightarrow> bool"
      where scut: "p \<in> nodes \<Longrightarrow> en a p \<Longrightarrow> a \<notin> cuts \<Longrightarrow> scut p (ex a p)"

    declare scut.intros[intro!]
    declare scut.cases[elim!]

    lemma scut_reachable:
      assumes "scut p q"
      shows "p \<in> nodes" "q \<in> nodes"
      using assms by auto
    lemma scut_trancl:
      assumes "scut\<^sup>+\<^sup>+ p q"
      obtains w
      where "path w p" "target w p = q" "set w \<inter> cuts = {}" "w \<noteq> []"
    using assms
    proof (induct arbitrary: thesis)
      case (base q)
      show ?case using base by force
    next
      case (step q r)
      obtain w where 1: "path w p" "target w p = q" "set w \<inter> cuts = {}" "w \<noteq> []"
        using step(3) by this
      obtain a where 2: "en a q" "a \<notin> cuts" "ex a q = r" using step(2) by auto
      show ?case
      proof (rule step(4))
        show "path (w @ [a]) p" using 1 2 by auto
        show "target (w @ [a]) p = r" using 1 2 by auto
        show "set (w @ [a]) \<inter> cuts = {}" using 1 2 by auto
        show "w @ [a] \<noteq> []" by auto
      qed
    qed

    sublocale wellfounded_relation "scut\<inverse>\<inverse>"
    proof (unfold_locales, intro finite_acyclic_wf_converse[to_pred] acyclicI[to_pred], safe)
      have 1: "{(p, q). scut p q} \<subseteq> nodes \<times> nodes" using scut_reachable by blast
      have 2: "finite (nodes \<times> nodes)"
        using finite_cartesian_product reachable_finite by blast
      show "finite {(p, q). scut p q}" using 1 2 by blast
    next
      fix p
      assume 1: "scut\<^sup>+\<^sup>+ p p"
      have 2: "p \<in> nodes" using 1 tranclE[to_pred] scut_reachable by metis
      obtain w where 3: "path w p" "target w p = p" "set w \<inter> cuts = {}" "w \<noteq> []"
        using scut_trancl 1 by this
      have 4: "w \<in> cycles p" using 3(1, 2) by auto
      have 5: "set w \<inter> cuts \<noteq> {}" using cycles_cut 2 4 3(4) by this
      show "False" using 3(3) 5 by simp
    qed

    lemma no_cut_scut:
      assumes "p \<in> nodes" "en a p" "a \<notin> cuts"
      shows "scut\<inverse>\<inverse> (ex a p) p"
      using assms by auto

  end

  locale transition_system_sticky =
    transition_system_complete ex en init int +
    transition_system_cut ex en init sticky
    for ex :: "'action \<Rightarrow> 'state \<Rightarrow> 'state"
    and en :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    and init :: "'state \<Rightarrow> bool"
    and int :: "'state \<Rightarrow> 'interpretation"
    and sticky :: "'action set"
    +
    assumes executable_visible_sticky: "executable \<inter> visible \<subseteq> sticky"

end
