theory Degeneralization
imports
  Acceptance
  Sequence_Zip
begin

  type_synonym 'a degen = "'a \<times> nat"

  definition degen :: "'a pred gen \<Rightarrow> 'a degen pred" where
    "degen cs \<equiv> \<lambda> (a, k). k \<ge> length cs \<or> (cs ! k) a"

  lemma degen_simps[iff]: "degen cs (a, k) \<longleftrightarrow> k \<ge> length cs \<or> (cs ! k) a" unfolding degen_def by simp

  definition count :: "'a pred gen \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat" where
    "count cs a k \<equiv>
      if k < length cs
      then if (cs ! k) a then Suc k mod length cs else k
      else if cs = [] then k else 0"

  lemma count_empty[simp]: "count [] a k = k" unfolding count_def by simp
  lemma count_nonempty[simp]: "cs \<noteq> [] \<Longrightarrow> count cs a k < length cs" unfolding count_def by simp
  lemma count_constant_1:
    assumes "k < length cs"
    assumes "\<And> a. a \<in> set w \<Longrightarrow> \<not> (cs ! k) a"
    shows "fold (count cs) w k = k"
    using assms unfolding count_def by (induct w) (auto)
  lemma count_constant_2:
    assumes "k < length cs"
    assumes "\<And> a. a \<in> set (w || k # scan (count cs) w k) \<Longrightarrow> \<not> degen cs a"
    shows "fold (count cs) w k = k"
    using assms unfolding count_def by (induct w) (auto)
  lemma count_step:
    assumes "k < length cs"
    assumes "(cs ! k) a"
    shows "count cs a k = Suc k mod length cs"
    using assms unfolding count_def by simp

  lemma degen_skip_condition:
    assumes "k < length cs"
    assumes "infs (degen cs) (w ||| k ## sscan (count cs) w k)"
    obtains u a v
    where "w = u @- a ## v" "fold (count cs) u k = k" "(cs ! k) a"
  proof -
    have 1: "Collect (degen cs) \<inter> sset (w ||| k ## sscan (count cs) w k) \<noteq> {}"
      using infs_any assms(2) by auto
    obtain ys x zs where 2:
      "w ||| k ## sscan (count cs) w k = ys @- x ## zs"
      "Collect (degen cs) \<inter> set ys = {}"
      "x \<in> Collect (degen cs)"
      using split_stream_first 1 by this
    define u where "u \<equiv> stake (length ys) w"
    define a where "a \<equiv> w !! length ys"
    define v where "v \<equiv> sdrop (Suc (length ys)) w"
    have "ys = stake (length ys) (w ||| k ## sscan (count cs) w k)" using shift_eq 2(1) by auto
    also have "\<dots> = stake (length ys) w || stake (length ys) (k ## sscan (count cs) w k)" by simp
    also have "\<dots> = take (length ys) u || take (length ys) (k # scan (count cs) u k)"
      unfolding u_def
      using append_eq_conv_conj length_stake length_zip stream.sel
      using sscan_stake stake.simps(2) stake_Suc stake_szip take_stake
      by metis
    also have "\<dots> = take (length ys) (u || k # scan (count cs) u k)" using take_zip by rule
    also have "\<dots> = u || k # scan (count cs) u k" unfolding u_def by simp
    finally have 3: "ys = u || k # scan (count cs) u k" by this
    have "x = (w ||| k ## sscan (count cs) w k) !! length ys" unfolding 2(1) by simp
    also have "\<dots> = (w !! length ys, (k ## sscan (count cs) w k) !! length ys)" by simp
    also have "\<dots> = (a, fold (count cs) u k)" unfolding u_def a_def by simp
    finally have 4: "x = (a, fold (count cs) u k)" by this
    have 5: "fold (count cs) u k = k" using count_constant_2 assms(1) 2(2) unfolding 3 by blast
    show ?thesis
    proof
      show "w = u @- a ## v" unfolding u_def a_def v_def using id_stake_snth_sdrop by this
      show "fold (count cs) u k = k" using 5 by this
      show "(cs ! k) a" using assms(1) 2(3) unfolding 4 5 by simp
    qed
  qed
  lemma degen_skip_arbitrary:
    assumes "k < length cs" "l < length cs"
    assumes "infs (degen cs) (w ||| k ## sscan (count cs) w k)"
    obtains u v
    where "w = u @- v" "fold (count cs) u k = l"
  using assms
  proof (induct "nat ((int l - int k) mod length cs)" arbitrary: l thesis)
    case (0)
    have 1: "length cs > 0" using assms(1) by auto
    have 2: "(int l - int k) mod length cs = 0" using 0(1) 1 by (auto intro: antisym)
    have 3: "int l mod length cs = int k mod length cs" using mod_eq_dvd_iff 2 by force
    have 4: "k = l" using 0(3, 4) 3 by simp
    show ?case
    proof (rule 0(2))
      show "w = [] @- w" by simp
      show "fold (count cs) [] k = l" using 4 by simp
    qed
  next
    case (Suc n)
    have 1: "length cs > 0" using assms(1) by auto
    define l' where "l' = nat ((int l - 1) mod length cs)"
    obtain u v where 2: "w = u @- v" "fold (count cs) u k = l'"
    proof (rule Suc(1))
      have 2: "Suc n < length cs" using nat_less_iff Suc(2) 1 by simp
      have "n = nat (int n)" by simp
      also have "int n = (int (Suc n) - 1) mod length cs" using 2 by simp
      also have "\<dots> = (int l - int k - 1) mod length cs" using Suc(2) by (simp add: mod_simps)
      also have "\<dots> = (int l - 1 - int k) mod length cs" by (simp add: algebra_simps)
      also have "\<dots> = (int l' - int k) mod length cs" using l'_def 1 by (simp add: mod_simps)
      finally show "n = nat ((int l' - int k) mod length cs)" by this
      show "k < length cs" using Suc(4) by this
      show "l' < length cs" using nat_less_iff l'_def 1 by simp
      show "infs (degen cs) (w ||| k ## sscan (count cs) w k)" using Suc(6) by this
    qed
    have 3: "l' < length cs" using nat_less_iff l'_def 1 by simp
    have 4: "v ||| l' ## sscan (count cs) v l' = sdrop (length u) (w ||| k ## sscan (count cs) w k)"
      using 2 eq_scons eq_shift
      by (metis sdrop.simps(2) sdrop_simps sdrop_szip sscan_scons_snth sscan_sdrop stream.sel(2))
    have 5: "infs (degen cs) (v ||| l' ## sscan (count cs) v l')" using Suc(6) unfolding 4 by blast
    obtain vu a vv where 6: "v = vu @- a ## vv" "fold (count cs) vu l' = l'" "(cs ! l') a"
      using degen_skip_condition 3 5 by this
    have "l = nat (int l)" by simp
    also have "int l = int l mod length cs" using Suc(5) by simp
    also have "\<dots> = int (Suc l') mod length cs" using l'_def 1 by (simp add: mod_simps)
    finally have 7: "l = Suc l' mod length cs" using nat_mod_as_int by metis
    show ?case
    proof (rule Suc(3))
      show "w = (u @ vu @ [a]) @- vv" unfolding 2(1) 6(1) by simp
      show "fold (count cs) (u @ vu @ [a]) k = l" using 2(2) 3 6(2, 3) 7 count_step by simp
    qed
  qed
  lemma degen_skip_arbitrary_condition:
    assumes "l < length cs"
    assumes "infs (degen cs) (w ||| k ## sscan (count cs) w k)"
    obtains u a v
    where "w = u @- a ## v" "fold (count cs) u k = l" "(cs ! l) a"
  proof -
    have 0: "cs \<noteq> []" using assms(1) by auto
    have 1: "count cs (shd w) k < length cs" using 0 by simp
    have 2: "infs (degen cs) (stl w ||| count cs (shd w) k ## sscan (count cs) (stl w) (count cs (shd w) k))"
      using assms(2) by (metis alw.cases sscan.code stream.sel(2) szip.simps(2))
    obtain u v where 3: "stl w = u @- v" "fold (count cs) u (count cs (shd w) k) = l"
      using degen_skip_arbitrary 1 assms(1) 2 by this
    have 4: "v ||| l ## sscan (count cs) v l =
      sdrop (length u) (stl w ||| count cs (shd w) k ## sscan (count cs) (stl w) (count cs (shd w) k))"
      using 3 eq_scons eq_shift
      by (metis sdrop.simps(2) sdrop_simps sdrop_szip sscan_scons_snth sscan_sdrop stream.sel(2))
    have 5: "infs (degen cs) (v ||| l ## sscan (count cs) v l)" using 2 unfolding 4 by blast
    obtain vu a vv where 6: "v = vu @- a ## vv" "fold (count cs) vu l = l" "(cs ! l) a"
      using degen_skip_condition assms(1) 5 by this
    show ?thesis
    proof
      show "w = (shd w # u @ vu) @- a ## vv" using 3(1) 6(1) by (simp add: eq_scons)
      show "fold (count cs) (shd w # u @ vu) k = l" using 3(2) 6(2) by simp
      show "(cs ! l) a" using 6(3) by this
    qed
  qed
  lemma gen_degen_step:
    assumes "gen infs cs w"
    obtains u a v
    where "w = u @- a ## v" "degen cs (a, fold (count cs) u k)"
  proof (cases "k < length cs")
    case True
    have 1: "infs (cs ! k) w" using assms True by auto
    have 2: "{a. (cs ! k) a} \<inter> sset w \<noteq> {}" using infs_any 1 by auto
    obtain u a v where 3: "w = u @- a ## v" "{a. (cs ! k) a} \<inter> set u = {}" "a \<in> {a. (cs ! k) a}"
      using split_stream_first 2 by this
    have 4: "fold (count cs) u k = k" using count_constant_1 True 3(2) by auto
    show ?thesis using 3(1, 3) 4 that by simp
  next
    case False
    show ?thesis
    proof
      show "w = [] @- shd w ## stl w" by simp
      show "degen cs (shd w, fold (count cs) [] k)" using False by simp
    qed
  qed

  lemma degen_infs[iff]: "infs (degen cs) (w ||| k ## sscan (count cs) w k) \<longleftrightarrow> gen infs cs w"
  proof
    show "gen infs cs w" if "infs (degen cs) (w ||| k ## sscan (count cs) w k)"
    proof
      fix c
      assume 1: "c \<in> set cs"
      obtain l where 2: "c = cs ! l" "l < length cs" using in_set_conv_nth 1 by metis
      show "infs c w"
      using that unfolding 2(1)
      proof (coinduction arbitrary: w k rule: infs_set_coinduct)
        case (infs_set w k)
        obtain u a v where 3: "w = u @- a ## v" "(cs ! l) a"
          using degen_skip_arbitrary_condition 2(2) infs_set by this
        let ?k = "fold (count cs) u k"
        let ?l = "fold (count cs) (u @ [a]) k"
        have 4: "a ## v ||| ?k ## sscan (count cs) (a ## v) ?k =
          sdrop (length u) (w ||| k ## sscan (count cs) w k)"
          using 3(1) eq_shift scons_eq
          by (metis sdrop_simps(1) sdrop_stl sdrop_szip sscan_scons_snth sscan_sdrop stream.sel(2))
        have 5: "infs (degen cs) (a ## v ||| ?k ## sscan (count cs) (a ## v) ?k)"
          using infs_set unfolding 4 by blast
        show ?case
        proof (intro exI conjI bexI)
          show "w = (u @ [a]) @- v" "(cs ! l) a" "a \<in> set (u @ [a])" "v = v" using 3 by auto
          show "infs (degen cs) (v ||| ?l ## sscan (count cs) v ?l)" using 5 by simp
        qed
      qed
    qed
    show "infs (degen cs) (w ||| k ## sscan (count cs) w k)" if "gen infs cs w"
    using that
    proof (coinduction arbitrary: w k rule: infs_set_coinduct)
      case (infs_set w k)
      obtain u a v where 1: "w = u @- a ## v" "degen cs (a, fold (count cs) u k)"
        using gen_degen_step infs_set by this
      let ?u = "u @ [a] || k # scan (count cs) u k"
      let ?l = "fold (count cs) (u @ [a]) k"
      show ?case
      proof (intro exI conjI bexI)
        have "w ||| k ## sscan (count cs) w k =
          (u @ [a]) @- v ||| k ## scan (count cs) u k @- ?l ## sscan (count cs) v ?l"
          unfolding 1(1) by simp
        also have "\<dots> = ?u @- (v ||| ?l ## sscan (count cs) v ?l)"
          by (metis length_Cons length_append_singleton scan_length shift.simps(2) szip_shift)
        finally show "w ||| k ## sscan (count cs) w k = ?u @- (v ||| ?l ## sscan (count cs) v ?l)" by this
        show "degen cs (a, fold (count cs) u k)" using 1(2) by this
        have "(a, fold (count cs) u k) = (last (u @ [a]), last (k # scan (count cs) u k))"
          unfolding scan_last by simp
        also have "\<dots> = last ?u" by (simp add: zip_eq_Nil_iff)
        also have "\<dots> \<in> set ?u" by (fastforce intro: last_in_set simp: zip_eq_Nil_iff)
        finally show "(a, fold (count cs) u k) \<in> set ?u" by this
        show "v ||| ?l ## sscan (count cs) v ?l = v ||| ?l ## sscan (count cs) v ?l" by rule
        show "gen infs cs v" using infs_set unfolding 1(1) by auto
      qed
    qed
  qed

end
