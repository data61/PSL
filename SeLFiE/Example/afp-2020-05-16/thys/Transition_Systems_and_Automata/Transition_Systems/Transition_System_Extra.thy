section \<open>Additional Theorems for Transition Systems\<close>

theory Transition_System_Extra
imports
  "../Basic/Sequence_LTL"
  "Transition_System"
begin

  context transition_system
  begin

    definition "enableds p \<equiv> {a. enabled a p}"
    definition "paths p \<equiv> {r. path r p}"
    definition "runs p \<equiv> {r. run r p}"

    lemma stake_run:
      assumes "\<And> k. path (stake k r) p"
      shows "run r p"
      using assms by (coinduction arbitrary: r p) (force elim: path.cases)
    lemma snth_run:
      assumes "\<And> k. enabled (r !! k) (target (stake k r) p)"
      shows "run r p"
      using assms by (coinduction arbitrary: r p) (metis stream.sel fold_simps snth.simps stake.simps)

    lemma run_stake:
      assumes "run r p"
      shows "path (stake k r) p"
      using assms by (metis run_shift_elim stake_sdrop)
    lemma run_sdrop:
      assumes "run r p"
      shows "run (sdrop k r) (target (stake k r) p)"
      using assms by (metis run_shift_elim stake_sdrop)
    lemma run_snth:
      assumes "run r p"
      shows "enabled (r !! k) (target (stake k r) p)"
      using assms by (metis stream.collapse sdrop_simps(1) run_scons_elim run_sdrop)

    lemma run_alt_def_snth: "run r p \<longleftrightarrow> (\<forall> k. enabled (r !! k) (target (stake k r) p))"
      using snth_run run_snth by blast

    lemma reachable_states:
      assumes "q \<in> reachable p" "path r q"
      shows "set (states r q) \<subseteq> reachable p"
      using assms by (induct r arbitrary: q) (auto)
    lemma reachable_trace:
      assumes "q \<in> reachable p" "run r q"
      shows "sset (trace r q) \<subseteq> reachable p"
      using assms unfolding sset_subset_stream_pred
      by (coinduction arbitrary: r q) (force elim: run.cases)

  end

  context transition_system_initial
  begin

    lemma nodes_states:
      assumes "p \<in> nodes" "path r p"
      shows "set (states r p) \<subseteq> nodes"
      using reachable_states assms by blast
    lemma nodes_trace:
      assumes "p \<in> nodes" "run r p"
      shows "sset (trace r p) \<subseteq> nodes"
      using reachable_trace assms by blast

  end

end