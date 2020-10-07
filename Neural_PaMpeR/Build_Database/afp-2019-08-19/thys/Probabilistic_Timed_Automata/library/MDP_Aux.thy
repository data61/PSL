theory MDP_Aux
  imports "Markov_Models.Markov_Decision_Process"
begin

lemma sets_stream_space_cylinder: 
  "sets (stream_space M) = sigma_sets (streams (space M)) (scylinder (space M) ` lists (sets M))"
proof (rule antisym)
  have closed[simp]: "scylinder (space M) ` lists (sets M) \<subseteq> Pow (streams (space M))"
    using scylinder_streams[of "space M" _] by auto
  have [simp]: "(\<lambda>s. s !! i) \<in> streams (space M) \<rightarrow> space M" for i
    by (auto simp: snth_in)

  interpret sigma_algebra "streams (space M)" "sigma_sets (streams (space M)) (scylinder (space M) ` lists (sets M))"
    by (intro sigma_algebra_sigma_sets) fact

  have *: "(\<lambda>s. s !! i) -` A \<inter> streams (space M) = scylinder (space M) (replicate i (space M) @ [A])"
    if "A \<in> sets M" for i A
  proof (induction i)
    case (Suc n) show ?case
      apply (intro set_eqI)
      subgoal for \<omega> by (cases \<omega>) (auto simp: streams_Stream Suc[symmetric])
      done
  qed (auto simp: streams_stl)

  have "sets (stream_space M) \<le> sets (sigma (streams (space M)) (scylinder (space M) ` lists (sets M)))"
    unfolding sets_stream_space_eq
    by (rule sets_Sup_in_sets)
       (auto simp: sets_vimage_algebra2 PiE_UNIV_domain space_PiM * intro!: sigma_sets.Basic imageI)
  also have "\<dots> = sigma_sets (streams (space M)) (scylinder (space M) ` lists (sets M))"
    by (rule sets_measure_of) fact
  finally show "sets (stream_space M) \<le> sigma_sets (streams (space M)) (scylinder (space M) ` lists (sets M))" .
next
  show "sigma_sets (streams (space M)) (scylinder (space M) ` lists (sets M)) \<subseteq> sets (stream_space M)"
    unfolding space_stream_space[symmetric]
    by (rule sets.sigma_sets_subset) (auto intro!: sets_scylinder)
qed

end
