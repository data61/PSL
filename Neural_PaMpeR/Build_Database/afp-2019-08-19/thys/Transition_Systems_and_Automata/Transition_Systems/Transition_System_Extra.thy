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

    lemma reachable_states:
      assumes "q \<in> reachable p" "path r q"
      shows "set (states r q) \<subseteq> reachable p"
      using assms by (induct r arbitrary: q) (auto)
    lemma reachable_trace:
      assumes "q \<in> reachable p" "run r q"
      shows "sset (trace r q) \<subseteq> reachable p"
      using assms unfolding sset_subset_stream_pred
      by (coinduction arbitrary: r q) (force elim: run.cases)

    lemma infs_trace_coinduct[case_names infs_trace, consumes 1]:
      assumes "R r p"
      assumes "\<And> r p. R r p \<Longrightarrow>
        (\<exists> u s. r = u @- s \<and> P (target u p)) \<and>
        (\<exists> u s. r = u @- s \<and> u \<noteq> [] \<and> R s (target u p))"
      shows "infs P (trace r p)"
    proof -
      have "infs P (p ## trace r p)"
      using assms(1)
      proof (coinduction arbitrary: r p)
        case infs
        obtain u r\<^sub>1 v r\<^sub>2 where 1:
          "r = u @- r\<^sub>1" "P (target u p)"
          "r = v @- r\<^sub>2" "v \<noteq> []" "R r\<^sub>2 (target v p)"
          using assms(2) infs by blast
        show ?case
        unfolding ev_stl_alt_def
        proof (intro exI conjI bexI)
          show "P (target u p)" using 1(2) by this
          show "target u p \<in> sset (p ## trace r p)" unfolding target_alt_def 1(1) by simp
          show "R r\<^sub>2 (target v p)" using 1(5) by this
          have "trace r p = states v p @- trace r\<^sub>2 (target v p)" unfolding 1(3) by simp
          also have "states v p = butlast (states v p) @ [target v p]"
            unfolding target_alt_def using 1(4) by simp
          finally show "p ## trace r p =
            (p # butlast (states v p)) @- target v p ## trace r\<^sub>2 (target v p)" by simp
          show "p # butlast (states v p) \<noteq> []" by simp
          show "target v p ## trace r\<^sub>2 (target v p) = target v p ## trace r\<^sub>2 (target v p)" by simp
        qed
      qed
      then show ?thesis by simp
    qed

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