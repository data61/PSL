theory Transition_System_Degeneralization
imports
  "../Basic/Acceptance"
  "Transition_System_Extra"
begin

  locale transition_system_initial_generalized =
    transition_system_initial execute enabled initial
    for execute :: "'transition \<Rightarrow> 'state \<Rightarrow> 'state"
    and enabled :: "'transition \<Rightarrow> 'state \<Rightarrow> bool"
    and initial :: "'state \<Rightarrow> bool"
    +
    (* TODO: why is this a list and not a set? *)
    fixes condition :: "'state pred gen"
  begin

    (* TODO: make this a definition, prove useful (automation) things about, use opaquely *)
    abbreviation "count p k \<equiv>
      if k < length condition
      then if (condition ! k) p then Suc k mod length condition else k
      else 0"

    definition dexecute :: "'transition \<Rightarrow> 'state degen \<Rightarrow> 'state degen" where
      "dexecute a \<equiv> \<lambda> (p, k). (execute a p, count p k)"
    definition denabled :: "'transition \<Rightarrow> 'state degen \<Rightarrow> bool" where
      "denabled a \<equiv> \<lambda> (p, k). enabled a p"
    definition dinitial :: "'state degen \<Rightarrow> bool" where
      "dinitial \<equiv> \<lambda> (p, k). initial p \<and> k = 0"

    sublocale degen: transition_system_initial dexecute denabled dinitial by this

    lemma degen_run[iff]: "degen.run r (p, k) \<longleftrightarrow> run r p"
    proof
      show "run r p" if "degen.run r (p, k)"
        using that by (coinduction arbitrary: r p k) (auto simp: dexecute_def denabled_def)
      show "degen.run r (p, k)" if "run r p"
        using that by (coinduction arbitrary: r p k) (auto simp: dexecute_def denabled_def)
    qed

    lemma degen_target_fst: "fst (degen.target w (p, k)) = target w p"
      by (induct w arbitrary: p k) (auto simp: dexecute_def)
    lemma degen_target_snd:
      assumes "k < length condition"
      assumes "\<And> q. q \<in> set (butlast (p # states w p)) \<Longrightarrow> \<not> (condition ! k) q"
      shows "snd (degen.target w (p, k)) = k"
      using assms by (induct w arbitrary: p) (auto simp: dexecute_def)
    lemma degen_target_snd':
      assumes "k < length condition"
      assumes "\<And> q l. (q, l) \<in> set (butlast ((p, k) # degen.states w (p, k))) \<Longrightarrow> \<not> (condition ! l) q"
      shows "snd (degen.target w (p, k)) = k"
    using assms
    proof (induct w arbitrary: p k)
      case (Nil)
      show ?case by simp
    next
      case (Cons a w)
      have "snd (degen.target (a # w) (p, k)) = snd (degen.target w (dexecute a (p, k)))" by simp
      also obtain q where 1: "dexecute a (p, k) = (q, k)" unfolding dexecute_def using Cons(2, 3) by auto
      also have "snd (degen.target w \<dots>) = k" using Cons 1 by auto
      finally show ?case by this
    qed
    lemma degen_nodes_fst[simp]: "fst ` degen.nodes = nodes"
    proof (intro equalityI subsetI)
      show "p \<in> fst ` degen.nodes" if "p \<in> nodes" for p
      using that
      proof induct
        case (initial p)
        have 1: "dinitial (p, 0)" using initial unfolding dinitial_def by simp
        show ?case using 1 by (auto intro: rev_image_eqI)
      next
        case (execute p a)
        obtain k where 1: "(p, k) \<in> degen.nodes" using execute(2) by auto
        have 2: "denabled a (p, k)" unfolding denabled_def using execute(3) by simp
        have 3: "execute a p = fst (dexecute a (p, k))" unfolding dexecute_def by simp
        show ?case using 1 2 3 by auto
      qed
      show "p \<in> nodes" if "p \<in> fst ` degen.nodes" for p
      using that
      proof
        fix pk
        assume "pk \<in> degen.nodes" "p = fst pk"
        then show "p \<in> nodes"
          by (induct arbitrary: p) (auto simp: dexecute_def denabled_def dinitial_def)
      qed
    qed
    lemma degen_nodes_snd_empty:
      assumes "condition = []"
      shows "snd ` degen.nodes \<subseteq> {0}"
    proof -
      have 1: "dinitial (p, k) \<Longrightarrow> k = 0" for p k unfolding dinitial_def by simp
      have 2: "snd (dexecute a (p, k)) = 0" for a p k using assms unfolding dexecute_def by simp
      show ?thesis using 1 2 by (auto elim: degen.nodes.cases)
    qed
    lemma degen_nodes_snd_nonempty:
      assumes "condition \<noteq> []"
      shows "snd ` degen.nodes \<subseteq> {0 ..< length condition}"
    proof -
      have 1: "dinitial (p, k) \<Longrightarrow> k < length condition" for p k using assms unfolding dinitial_def by simp
      have 2: "snd (dexecute a (p, k)) < length condition" for a p k using assms unfolding dexecute_def by simp
      show ?thesis using 1 2 by (auto elim: degen.nodes.cases)
    qed
    lemma degen_nodes_empty:
      assumes "condition = []"
      shows "degen.nodes = nodes \<times> {0}"
    proof -
      have "(p, k) \<in> degen.nodes \<longleftrightarrow> p \<in> fst ` degen.nodes \<and> k = 0" for p k
        using degen_nodes_snd_empty assms by (force simp del: degen_nodes_fst)
      then show ?thesis by auto
    qed
    lemma degen_nodes_nonempty:
      assumes "condition \<noteq> []"
      shows "degen.nodes \<subseteq> nodes \<times> {0 ..< length condition}"
      using subset_fst_snd degen_nodes_fst degen_nodes_snd_nonempty[OF assms] by blast
    lemma degen_nodes: "degen.nodes \<subseteq> nodes \<times> {0 ..< max 1 (length condition)}"
      using degen_nodes_empty degen_nodes_nonempty by force

    lemma degen_nodes_finite[iff]: "finite degen.nodes \<longleftrightarrow> finite nodes"
    proof
      show "finite nodes" if "finite degen.nodes" using that by (auto simp flip: degen_nodes_fst)
      show "finite degen.nodes" if "finite nodes" using degen_nodes that by (auto intro: finite_subset)
    qed
    lemma degen_nodes_card: "card degen.nodes \<le> max 1 (length condition) * card nodes"
    proof (cases "finite nodes")
      case True
      have "card degen.nodes \<le> card (nodes \<times> {0 ..< max 1 (length condition)})"
        using degen_nodes True by (blast intro: card_mono)
      also have "\<dots> = max 1 (length condition) * card nodes" unfolding card_cartesian_product by simp
      finally show ?thesis by this
    next
      case False
      then have "card nodes = 0" "card degen.nodes = 0" by auto
      then show ?thesis by simp
    qed

    definition dcondition :: "'state degen pred" where
      "dcondition \<equiv> \<lambda> (p, k). k \<ge> length condition \<or> (condition ! k) p"

    lemma degen_skip_condition:
      assumes "k < length condition"
      assumes "infs dcondition (degen.trace r (p, k))"
      obtains s t q
      where "r = s @- t" "degen.target s (p, k) = (q, k)" "dcondition (q, k)"
    proof -
      have 1: "Collect dcondition \<inter> sset ((p, k) ## degen.trace r (p, k)) \<noteq> {}"
        using infs_any assms(2) by auto
      obtain u q l v where 2:
        "(p, k) ## degen.trace r (p, k) = u @- (q, l) ## v"
        "Collect dcondition \<inter> set u = {}"
        "(q, l) \<in> Collect dcondition"
        using 1 by (force elim!: split_stream_first)
      let ?w = "(p, k) # degen.states (stake (length u) r) (p, k)"
      have "?w = stake (Suc (length u)) ((p, k) ## degen.trace r (p, k))" by simp
      also have "\<dots> = stake (Suc (length u)) (u @- (q, l) ## v)" unfolding 2(1) by rule
      also have "\<dots> = u @ [(q, l)]" unfolding stake_Suc using eq_shift by auto
      finally have 3: "(p, k) # degen.states (stake (length u) r) (p, k) = u @ [(q, l)]" by this
      have 4: "degen.target (stake (length u) r) (p, k) = (q, l)" unfolding degen.target_alt_def 3 by simp
      have 5: "Collect dcondition \<inter> set (butlast ?w) = {}" using 2(2) 3 by simp
      have "l = snd (q, l)" by simp
      also have "\<dots> = snd (degen.target (stake (length u) r) (p, k))" using 4 by simp
      also have "\<dots> = k" using degen_target_snd' assms(1) 5 unfolding dcondition_def by blast
      finally have 6: "k = l" by rule
      show ?thesis
      proof
        show "r = stake (length u) r @- sdrop (length u) r" by simp
        show "degen.target (stake (length u) r) (p, k) = (q, k)" using 4 6 by simp
        show "dcondition (q, k)" using 2(3) 6 by auto
      qed
    qed
    lemma degen_skip_increment:
      assumes "k < length condition"
      assumes "infs dcondition (degen.trace w (p, k))"
      obtains u v q
      where "w = u @- v" "u \<noteq> []" "degen.target u (p, k) = (q, Suc k mod length condition)"
    proof -
      obtain u v q where 1: "w = u @- v" "degen.target u (p, k) = (q, k)" "dcondition (q, k)"
        using degen_skip_condition assms by this
      show ?thesis
      proof
        show "w = (u @ [shd v]) @- stl v" using 1(1) by simp
        show "u @ [shd v] \<noteq> []" by simp
        show "degen.target (u @ [shd v]) (p, k) = (execute (shd v) q, Suc k mod length condition)"
          using assms(1) 1(2, 3) by (simp add: dexecute_def dcondition_def)
      qed
    qed
    lemma degen_skip_arbitrary:
      assumes "k < length condition" "l < length condition"
      assumes "infs dcondition (degen.trace w (p, k))"
      obtains u v q
      where "w = u @- v" "degen.target u (p, k) = (q, l)"
    using assms
    proof (induct "nat ((int l - int k) mod length condition)" arbitrary: thesis l)
      case (0)
      have 1: "length condition > 0" using assms(1) by auto
      have 2: "(int l - int k) mod length condition = 0" using 0(1) 1 by (auto intro: antisym)
      have 3: "int l mod length condition = int k mod length condition" using mod_eq_dvd_iff 2 by force
      have 4: "k = l" using 0(3, 4) 3 by simp
      show ?case
      proof (rule 0(2))
        show "w = [] @- w" by simp
        show "degen.target [] (p, k) = (p, l)" using 4 by simp
      qed
    next
      case (Suc n)
      have 1: "length condition > 0" using assms(1) by auto
      define l' where "l' = nat ((int l - 1) mod length condition)"
      obtain u v q where 2: "w = u @- v" "degen.target u (p, k) = (q, l')"
      proof (rule Suc(1))
        have 2: "Suc n < length condition" using nat_less_iff Suc(2) 1 by simp
        have "n = nat (int n)" by simp
        also have "int n = (int (Suc n) - 1) mod length condition" using 2 by simp
        also have "\<dots> = (int l - int k - 1) mod length condition" using Suc(2) by (simp add: mod_simps)
        also have "\<dots> = (int l - 1 - int k) mod length condition" by (simp add: algebra_simps)
        also have "\<dots> = (int l' - int k) mod length condition" using l'_def 1 by (simp add: mod_simps)
        finally show "n = nat ((int l' - int k) mod length condition)" by this
        show "k < length condition" using Suc(4) by this
        show "l' < length condition" using nat_less_iff l'_def 1 by simp
        show "infs dcondition (degen.trace w (p, k))" using Suc(6) by this
      qed
      obtain vu vv t where 3: "v = vu @- vv" "degen.target vu (q, l') = (t, Suc l' mod length condition)"
      proof (rule degen_skip_increment)
        show "l' < length condition" using nat_less_iff l'_def 1 by simp
        show "infs dcondition (degen.trace v (q, l'))" using Suc(6) 2 by simp
      qed
      show ?case
      proof (rule Suc(3))
        have "l = nat (int l)" by simp
        also have "int l = int l mod length condition" using Suc(5) by simp
        also have "\<dots> = int (Suc l') mod length condition" using l'_def 1 by (simp add: mod_simps)
        finally have 4: "l = Suc l' mod length condition" using nat_mod_as_int by metis
        show "w = (u @ vu) @- vv" unfolding 2(1) 3(1) by simp
        show "degen.target (u @ vu) (p, k) = (t, l)" using 2(2) 3(2) 4 by simp
      qed
    qed
    lemma degen_skip_arbitrary_condition:
      assumes "l < length condition"
      assumes "infs dcondition (degen.trace w (p, k))"
      obtains u v q
      where "w = u @- v" "degen.target u (p, k) = (q, l)" "dcondition (q, l)"
    proof -
      obtain x y where 10: "dexecute (shd w) (p, k) = (x, y)" by force
      have 11: "y < length condition" using mod_Suc assms(1) 10 unfolding dexecute_def by auto
      have 12: "infs dcondition (degen.trace (stl w) (x, y))"
        using 10 by (metis alw_ev_stl assms(2) sscan.simps(2))
      obtain u v q where 1: "stl w = u @- v" "degen.target u (x, y) = (q, l)"
        using degen_skip_arbitrary 11 assms(1) 12 by this
      have 2: "infs dcondition (degen.trace v (q, l))" using 12 1(2) unfolding 1(1) by simp
      obtain vu vv t where 3: "v = vu @- vv" "degen.target vu (q, l) = (t, l)" "dcondition (t, l)"
        using degen_skip_condition assms(1) 2 by this
      show ?thesis
      proof
        show "w = (shd w # u @ vu) @- vv" using 1(1) 3(1)
          by (simp add: "1"(1) "3"(1) stream.expand)
        show "degen.target (shd w # u @ vu) (p, k) = (t, l)" using 1(2) 3(2) 10 by simp
        show "dcondition (t, l)" using 3(3) by this
      qed
    qed

    lemma degen_infs_1:
      assumes "infs dcondition (degen.trace w (p, k))"
      assumes "P \<in> set condition"
      shows "infs P (trace w p)"
    using assms
    proof (coinduction arbitrary: w p k rule: infs_trace_coinduct)
      case (infs_trace w p k)
      obtain l where 1: "P = condition ! l" "l < length condition"
        using infs_trace(2) in_set_conv_nth by metis
      obtain u v q where 2: "w = u @- v" "degen.target  u (p, k) = (q, l)" "dcondition (q, l)"
        using degen_skip_arbitrary_condition 1(2) infs_trace(1) by this
      have 3: "q = target u p" using 2(2) degen_target_fst by (metis fst_conv)
      obtain p' k' where 4: "dexecute (shd w) (p, k) = (p', k')" by force
      have 5: "infs dcondition (degen.trace (shd w ## stl w) (p, k))" using infs_trace(1) by simp
      show ?case
      proof (intro exI conjI)
        show "w = u @- v" using 2(1) by this
        show "P (target u p)" using 1(2) 2(3) unfolding dcondition_def 1(1) 3 by simp
        show "w = [shd w] @- stl w" "[shd w] \<noteq> []" "stl w = stl w" by auto
        show "target [shd w] p = p'" using 4 by (simp add: dexecute_def)
        show "infs dcondition (degen.trace (stl w) (p', k'))" using 4 5 unfolding sscan_scons by simp
        show "P \<in> set condition" using infs_trace(2) by this
      qed
    qed
    lemma degen_infs_2:
      assumes "\<And> P. P \<in> set condition \<Longrightarrow> infs P (trace w p)"
      shows "infs dcondition (degen.trace w (p, k))"
    using assms
    proof (coinduction arbitrary: w p k rule: degen.infs_trace_coinduct)
      case (infs_trace w p k)
      show ?case
      proof (cases "k < length condition")
        case True
        have 1: "infs (condition ! k) (trace w p)" using infs_trace True by simp
        have 2: "{q. (condition ! k) q} \<inter> sset (p ## trace w p) \<noteq> {}" using infs_any 1 by auto
        obtain ys x zs where 3:
          "p ## trace w p = ys @- x ## zs"
          "{q. (condition ! k) q} \<inter> set ys = {}"
          "x \<in> {q. (condition ! k) q}"
          using split_stream_first 2 by this
        define u where "u = stake (length ys) w"
        define v where "v = sdrop (length ys) w"
        obtain q l where 4: "degen.target u (p, k) = (q, l)" by force
        have "p # states u p = stake (length (ys @ [x])) (p ## trace w p)" unfolding u_def by simp
        also have "p ## trace w p = (ys @ [x]) @- zs" using 3(1) by simp
        also have "stake (length (ys @ [x])) \<dots> = ys @ [x]" unfolding stake_shift by simp
        finally have 5: "p # states u p = ys @ [x]" by this
        have 6: "butlast (p # states u p) = ys" using 5 by auto
        have "l = snd (degen.target u (p, k))" unfolding 4 by simp
        also have "\<dots> = k" using degen_target_snd 3(2) 6 True by fast
        finally have 7: "k = l" by rule
        have "q = fst (degen.target u (p, k))" unfolding 4 by simp
        also have "\<dots> = target u p" using degen_target_fst by this
        also have "\<dots> = last (p # states u p)" unfolding scan_last by rule
        also have "\<dots> = x" unfolding 5 by simp
        finally have 8: "q = x" by this
        have 9: "(condition ! l) q" using 3(3) unfolding 7 8 by simp
        obtain x y where 10: "dexecute (shd w) (p, k) = (x, y)" by force
        have 11: "\<forall> P \<in> set condition. infs P (trace (shd w ## stl w) p)" using infs_trace by simp
        have 12: "execute (shd w) p = x" using infs_trace(1) 10 unfolding dexecute_def by auto
        show ?thesis
        proof (intro exI conjI)
          show "w = u @- v" unfolding u_def v_def by simp
          show "dcondition (degen.target u (p, k))" using 4 9 by (auto simp: dcondition_def)
          show "w = [shd w] @- stl w" "[shd w] \<noteq> []" "stl w = stl w" by auto
          show "degen.target [shd w] (p, k) = (x, y)" using 10 by simp
          show "\<forall> P. P \<in> set condition \<longrightarrow> infs P (trace (stl w) x)"
            using 11 12 unfolding sscan_scons by simp
        qed
      next
        case False
        obtain x y where 10: "dexecute (shd w) (p, k) = (x, y)" by force
        have 11: "\<forall> P \<in> set condition. infs P (trace (shd w ## stl w) p)" using infs_trace by simp
        have 12: "execute (shd w) p = x" using infs_trace(1) 10 unfolding dexecute_def by auto
        show ?thesis
        proof (intro exI conjI)
          show "w = [] @- w" by simp
          show "dcondition (degen.target [] (p, k))" unfolding dcondition_def using False by simp
          show "w = [shd w] @- stl w" "[shd w] \<noteq> []" "stl w = stl w" by auto
          show "degen.target [shd w] (p, k) = (x, y)" using 10 by simp
          show "\<forall> P. P \<in> set condition \<longrightarrow> infs P (trace (stl w) x)"
            using 11 12 unfolding sscan_scons by simp
        qed
      qed
    qed

    lemma degen_infs: "infs dcondition (degen.trace w (p, k)) \<longleftrightarrow>
      (\<forall> P \<in> set condition. infs P (trace w p))"
      using degen_infs_1 degen_infs_2 by auto

  end

end