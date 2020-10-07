section \<open>Transition Systems\<close>

theory Transition_System
imports "../Basic/Sequence"
begin

  subsection \<open>Universal Transition Systems\<close>

  locale transition_system_universal =
    fixes execute :: "'transition \<Rightarrow> 'state \<Rightarrow> 'state"
  begin

    abbreviation "target \<equiv> fold execute"
    abbreviation "states \<equiv> scan execute"
    abbreviation "trace \<equiv> sscan execute"

    lemma target_alt_def: "target r p = last (p # states r p)" using scan_last by rule

  end

  subsection \<open>Transition Systems\<close>

  locale transition_system =
    transition_system_universal execute
    for execute :: "'transition \<Rightarrow> 'state \<Rightarrow> 'state"
    +
    fixes enabled :: "'transition \<Rightarrow> 'state \<Rightarrow> bool"
  begin

    abbreviation "successors p \<equiv> {execute a p |a. enabled a p}"

    inductive path :: "'transition list \<Rightarrow> 'state \<Rightarrow> bool" where
      nil[intro!]: "path [] p" |
      cons[intro!]: "enabled a p \<Longrightarrow> path r (execute a p) \<Longrightarrow> path (a # r) p"

    inductive_cases path_cons_elim[elim!]: "path (a # r) p"

    lemma path_append[intro!]:
      assumes "path r p" "path s (target r p)"
      shows "path (r @ s) p"
      using assms by (induct r arbitrary: p) (auto)
    lemma path_append_elim[elim!]:
      assumes "path (r @ s) p"
      obtains "path r p" "path s (target r p)"
      using assms by (induct r arbitrary: p) (auto)

    coinductive run :: "'transition stream \<Rightarrow> 'state \<Rightarrow> bool" where
      scons[intro!]: "enabled a p \<Longrightarrow> run r (execute a p) \<Longrightarrow> run (a ## r) p"

    inductive_cases run_scons_elim[elim!]: "run (a ## r) p"

    lemma run_shift[intro!]:
      assumes "path r p" "run s (target r p)"
      shows "run (r @- s) p"
      using assms by (induct r arbitrary: p) (auto)
    lemma run_shift_elim[elim!]:
      assumes "run (r @- s) p"
      obtains "path r p" "run s (target r p)"
      using assms by (induct r arbitrary: p) (auto)

    lemma run_coinduct[case_names run, coinduct pred: run]:
      assumes "R r p"
      assumes "\<And> a r p. R (a ## r) p \<Longrightarrow> enabled a p \<and> R r (execute a p)"
      shows "run r p"
      using stream.collapse run.coinduct assms by metis
    lemma run_coinduct_shift[case_names run, consumes 1]:
      assumes "R r p"
      assumes "\<And> r p. R r p \<Longrightarrow> \<exists> s t. r = s @- t \<and> s \<noteq> [] \<and> path s p \<and> R t (target s p)"
      shows "run r p"
    proof -
      have "\<exists> s t. r = s @- t \<and> path s p \<and> R t (target s p)" using assms(1) by force
      then show ?thesis using assms(2) by (coinduct) (force elim: path.cases)
    qed
    lemma run_flat_coinduct[case_names run, consumes 1]:
      assumes "R rs p"
      assumes "\<And> r rs p. R (r ## rs) p \<Longrightarrow> r \<noteq> [] \<and> path r p \<and> R rs (target r p)"
      shows "run (flat rs) p"
    using assms(1)
    proof (coinduction arbitrary: rs p rule: run_coinduct_shift)
      case (run rs p)
      then show ?case using assms(2) by (metis stream.exhaust flat_Stream)
    qed

    inductive_set reachable :: "'state \<Rightarrow> 'state set" for p where
      reflexive[intro!]: "p \<in> reachable p" |
      execute[intro!]: "q \<in> reachable p \<Longrightarrow> enabled a q \<Longrightarrow> execute a q \<in> reachable p"

    inductive_cases reachable_elim[elim]: "q \<in> reachable p"

    lemma reachable_execute'[intro]:
      assumes "enabled a p" "q \<in> reachable (execute a p)"
      shows "q \<in> reachable p"
      using assms(2, 1) by induct auto
    lemma reachable_elim'[elim]:
      assumes "q \<in> reachable p"
      obtains "q = p" | a where "enabled a p" "q \<in> reachable (execute a p)"
      using assms by induct auto

    lemma reachable_target[intro]:
      assumes "q \<in> reachable p" "path r q"
      shows "target r q \<in> reachable p"
      using assms by (induct r arbitrary: q) (auto)
    lemma reachable_target_elim[elim]:
      assumes "q \<in> reachable p"
      obtains r
      where "path r p" "q = target r p"
      using assms by induct force+

    lemma reachable_alt_def: "reachable p = {target r p |r. path r p}" by auto

    lemma reachable_trans[trans]: "q \<in> reachable p \<Longrightarrow> s \<in> reachable q \<Longrightarrow> s \<in> reachable p" by auto

    lemma reachable_successors[intro!]: "successors p \<subseteq> reachable p" by auto

    lemma reachable_step: "reachable p = insert p (\<Union> (reachable ` successors p))" by auto

  end

  subsection \<open>Transition Systems with Initial States\<close>

  locale transition_system_initial =
    transition_system execute enabled
    for execute :: "'transition \<Rightarrow> 'state \<Rightarrow> 'state"
    and enabled :: "'transition \<Rightarrow> 'state \<Rightarrow> bool"
    +
    fixes initial :: "'state \<Rightarrow> bool"
  begin

    inductive_set nodes :: "'state set" where
      initial[intro]: "initial p \<Longrightarrow> p \<in> nodes" |
      execute[intro!]: "p \<in> nodes \<Longrightarrow> enabled a p \<Longrightarrow> execute a p \<in> nodes"

    lemma nodes_target[intro]:
      assumes "p \<in> nodes" "path r p"
      shows "target r p \<in> nodes"
      using assms by (induct r arbitrary: p) (auto)
    lemma nodes_target_elim[elim]:
      assumes "q \<in> nodes"
      obtains r p
      where "initial p" "path r p" "q = target r p"
      using assms by induct force+

    lemma nodes_alt_def: "nodes = \<Union> (reachable ` Collect initial)" by auto

    lemma nodes_trans[trans]: "p \<in> nodes \<Longrightarrow> q \<in> reachable p \<Longrightarrow> q \<in> nodes" by auto

  end

end
