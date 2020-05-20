(* Title: GPV_Bisim.thy
  Author: Andreas Lochbihler, ETH Zurich *)

theory GPV_Bisim imports
  GPV_Expectation
begin

subsection \<open>Bisimulation for oracles\<close>

text \<open>Bisimulation is a consequence of parametricity\<close>

lemma exec_gpv_oracle_bisim':
  assumes *: "X s1 s2"
  and bisim: "\<And>s1 s2 x. X s1 s2 \<Longrightarrow> rel_spmf (\<lambda>(a, s1') (b, s2'). a = b \<and> X s1' s2') (oracle1 s1 x) (oracle2 s2 x)"
  shows "rel_spmf (\<lambda>(a, s1') (b, s2'). a = b \<and> X s1' s2') (exec_gpv oracle1 gpv s1) (exec_gpv oracle2 gpv s2)"
by(rule exec_gpv_parametric[of X "(=)" "(=)", unfolded gpv.rel_eq rel_prod_conv, THEN rel_funD, THEN rel_funD, THEN rel_funD, OF rel_funI refl, OF rel_funI *])(simp add: bisim)

lemma exec_gpv_oracle_bisim:
  assumes *: "X s1 s2"
  and bisim: "\<And>s1 s2 x. X s1 s2 \<Longrightarrow> rel_spmf (\<lambda>(a, s1') (b, s2'). a = b \<and> X s1' s2') (oracle1 s1 x) (oracle2 s2 x)"
  and R: "\<And>x s1' s2'. \<lbrakk> X s1' s2'; (x, s1') \<in> set_spmf (exec_gpv oracle1 gpv s1); (x, s2') \<in> set_spmf (exec_gpv oracle2 gpv s2) \<rbrakk> \<Longrightarrow> R (x, s1') (x, s2')"
  shows "rel_spmf R (exec_gpv oracle1 gpv s1) (exec_gpv oracle2 gpv s2)"
apply(rule spmf_rel_mono_strong)
apply(rule exec_gpv_oracle_bisim'[OF * bisim])
apply(auto dest: R)
done

lemma run_gpv_oracle_bisim:
  assumes  "X s1 s2"
  and "\<And>s1 s2 x. X s1 s2 \<Longrightarrow> rel_spmf (\<lambda>(a, s1') (b, s2'). a = b \<and> X s1' s2') (oracle1 s1 x) (oracle2 s2 x)"
  shows "run_gpv oracle1 gpv s1 = run_gpv oracle2 gpv s2"
using exec_gpv_oracle_bisim'[OF assms]
by(fold spmf_rel_eq)(fastforce simp add: spmf_rel_map intro: rel_spmf_mono)

context
  fixes joint_oracle :: "('s1 \<times> 's2) \<Rightarrow> 'a \<Rightarrow> (('b \<times> 's1) \<times> ('b \<times> 's2)) spmf"
  and oracle1 :: "'s1 \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's1) spmf"
  and bad1 :: "'s1 \<Rightarrow> bool"
  and oracle2 :: "'s2 \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's2) spmf"
  and bad2 :: "'s2 \<Rightarrow> bool"
begin

partial_function (spmf) exec_until_bad :: "('x, 'a, 'b) gpv \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> (('x \<times> 's1) \<times> ('x \<times> 's2)) spmf"
where
  "exec_until_bad gpv s1 s2 = 
  (if bad1 s1 \<or> bad2 s2 then pair_spmf (exec_gpv oracle1 gpv s1) (exec_gpv oracle2 gpv s2)
  else bind_spmf (the_gpv gpv) (\<lambda>generat.
     case generat of Pure x \<Rightarrow> return_spmf ((x, s1), (x, s2))
     | IO out f \<Rightarrow> bind_spmf (joint_oracle (s1, s2) out) (\<lambda>((x, s1'), (y, s2')). 
       if bad1 s1' \<or> bad2 s2' then pair_spmf (exec_gpv oracle1 (f x) s1') (exec_gpv oracle2 (f y) s2')
       else exec_until_bad (f x) s1' s2')))"

lemma exec_until_bad_fixp_induct [case_names adm bottom step]:
  assumes "ccpo.admissible (fun_lub lub_spmf) (fun_ord (ord_spmf (=))) (\<lambda>f. P (\<lambda>gpv s1 s2. f ((gpv, s1), s2)))"
  and "P (\<lambda>_ _ _. return_pmf None)"
  and "\<And>exec_until_bad'. P exec_until_bad' \<Longrightarrow> 
     P (\<lambda>gpv s1 s2. if bad1 s1 \<or> bad2 s2 then pair_spmf (exec_gpv oracle1 gpv s1) (exec_gpv oracle2 gpv s2)
     else bind_spmf (the_gpv gpv) (\<lambda>generat.
     case generat of Pure x \<Rightarrow> return_spmf ((x, s1), (x, s2))
     | IO out f \<Rightarrow> bind_spmf (joint_oracle (s1, s2) out) (\<lambda>((x, s1'), (y, s2')). 
       if bad1 s1' \<or> bad2 s2' then pair_spmf (exec_gpv oracle1 (f x) s1') (exec_gpv oracle2 (f y) s2') 
       else exec_until_bad' (f x) s1' s2')))"
  shows "P exec_until_bad"
using assms by(rule exec_until_bad.fixp_induct[unfolded curry_conv[abs_def]])

end

lemma exec_gpv_oracle_bisim_bad_plossless:
  fixes s1 :: 's1 and s2 :: 's2 and X :: "'s1 \<Rightarrow> 's2 \<Rightarrow> bool"
  and oracle1 :: "'s1 \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's1) spmf"
  and oracle2 :: "'s2 \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's2) spmf"
  assumes *: "if bad2 s2 then X_bad s1 s2 else X s1 s2"
  and bad: "bad1 s1 = bad2 s2"
  and bisim: "\<And>s1 s2 x. \<lbrakk> X s1 s2; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> rel_spmf (\<lambda>(a, s1') (b, s2'). bad1 s1' = bad2 s2' \<and> (if bad2 s2' then X_bad s1' s2' else a = b \<and> X s1' s2')) (oracle1 s1 x) (oracle2 s2 x)"
  and bad_sticky1: "\<And>s2. bad2 s2 \<Longrightarrow> callee_invariant_on oracle1 (\<lambda>s1. bad1 s1 \<and> X_bad s1 s2) \<I>"
  and bad_sticky2: "\<And>s1. bad1 s1 \<Longrightarrow> callee_invariant_on oracle2 (\<lambda>s2. bad2 s2 \<and> X_bad s1 s2) \<I>"
  and lossless1: "\<And>s1 x. \<lbrakk> bad1 s1; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> lossless_spmf (oracle1 s1 x)"
  and lossless2: "\<And>s2 x. \<lbrakk> bad2 s2; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> lossless_spmf (oracle2 s2 x)"
  and lossless: "plossless_gpv \<I> gpv"
  and WT_oracle1: "\<And>s1. \<I> \<turnstile>c oracle1 s1 \<surd>" (* stronger than the invariants above because unconditional *)
  and WT_oracle2: "\<And>s2. \<I> \<turnstile>c oracle2 s2 \<surd>"
  and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
  shows "rel_spmf (\<lambda>(a, s1') (b, s2'). bad1 s1' = bad2 s2' \<and> (if bad2 s2' then X_bad s1' s2' else a = b \<and> X s1' s2')) (exec_gpv oracle1 gpv s1) (exec_gpv oracle2 gpv s2)"
  (is "rel_spmf ?R ?p ?q")
proof -
  let ?R' = "\<lambda>(a, s1') (b, s2'). bad1 s1' = bad2 s2' \<and> (if bad2 s2' then X_bad s1' s2' else a = b \<and> X s1' s2')"
  from bisim have "\<forall>s1 s2. \<forall>x \<in> outs_\<I> \<I>. X s1 s2 \<longrightarrow> rel_spmf ?R' (oracle1 s1 x) (oracle2 s2 x)" by blast
  then obtain joint_oracle
    where oracle1 [symmetric]: "\<And>s1 s2 x. \<lbrakk> X s1 s2; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> map_spmf fst (joint_oracle s1 s2 x) = oracle1 s1 x"
    and oracle2 [symmetric]: "\<And>s1 s2 x. \<lbrakk> X s1 s2; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> map_spmf snd (joint_oracle s1 s2 x) = oracle2 s2 x"
    and 3 [rotated 2]: "\<And>s1 s2 x y y' s1' s2'. \<lbrakk> X s1 s2; x \<in> outs_\<I> \<I>; ((y, s1'), (y', s2')) \<in> set_spmf (joint_oracle s1 s2 x) \<rbrakk>
      \<Longrightarrow> bad1 s1' = bad2 s2' \<and> (if bad2 s2' then X_bad s1' s2' else y = y' \<and> X s1' s2')"
    apply atomize_elim
    apply(unfold rel_spmf_simps all_conj_distrib[symmetric] all_simps(6) imp_conjR[symmetric])
    apply(subst choice_iff[symmetric] ex_simps(6))+
    apply fastforce
    done
  let ?joint_oracle = "\<lambda>(s1, s2). joint_oracle s1 s2"
  let ?pq = "exec_until_bad ?joint_oracle oracle1 bad1 oracle2 bad2 gpv s1 s2"

  have setD: "\<And>s1 s2 x y y' s1' s2'. \<lbrakk> X s1 s2; x \<in> outs_\<I> \<I>; ((y, s1'), (y', s2')) \<in> set_spmf (joint_oracle s1 s2 x) \<rbrakk>
    \<Longrightarrow> (y, s1') \<in> set_spmf (oracle1 s1 x) \<and> (y', s2') \<in> set_spmf (oracle2 s2 x)"
    unfolding oracle1 oracle2 by(auto intro: rev_image_eqI)
  show ?thesis
  proof
    show "map_spmf fst ?pq = exec_gpv oracle1 gpv s1"
    proof(rule spmf.leq_antisym)
      show "ord_spmf (=) (map_spmf fst ?pq) (exec_gpv oracle1 gpv s1)" using * bad WT_gpv lossless
      proof(induction arbitrary: s1 s2 gpv rule: exec_until_bad_fixp_induct)
        case adm show ?case by simp
        case bottom show ?case by simp
        case (step exec_until_bad')
        show ?case
        proof(cases "bad2 s2")
          case True
          then have "weight_spmf (exec_gpv oracle2 gpv s2) = 1"
            using callee_invariant_on.weight_exec_gpv[OF bad_sticky2 lossless2, of s1 gpv s2]
              step.prems weight_spmf_le_1[of "exec_gpv oracle2 gpv s2"]
            by(simp add: pgen_lossless_gpv_def weight_gpv_def)
          then show ?thesis using True by simp
        next
          case False
          hence "\<not> bad1 s1" using step.prems(2) by simp
          moreover {
            fix out c r1 s1' r2 s2'
            assume IO: "IO out c \<in> set_spmf (the_gpv gpv)"
              and joint: "((r1, s1'), (r2, s2')) \<in> set_spmf (joint_oracle s1 s2 out)"
            from step.prems(3) IO have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpvD)
            from setD[OF _ out joint] step.prems(1) False
            have 1: "(r1, s1') \<in> set_spmf (oracle1 s1 out)"
              and 2: "(r2, s2') \<in> set_spmf (oracle2 s2 out)" by simp_all
            hence r1: "r1 \<in> responses_\<I> \<I> out" and r2: "r2 \<in> responses_\<I> \<I> out"
              using WT_oracle1 WT_oracle2 out by(blast dest: WT_calleeD)+
            have *: "plossless_gpv \<I> (c r2)" using step.prems(4) IO r2 step.prems(3)
              by(rule plossless_gpv_ContD)
            then have "bad2 s2' \<Longrightarrow> weight_spmf (exec_gpv oracle2 (c r2) s2') = 1"
              and "\<not> bad2 s2' \<Longrightarrow> ord_spmf (=) (map_spmf fst (exec_until_bad' (c r2) s1' s2')) (exec_gpv oracle1 (c r2) s1')"
              using callee_invariant_on.weight_exec_gpv[OF bad_sticky2 lossless2, of s1' "c r2" s2'] 
                weight_spmf_le_1[of "exec_gpv oracle2 (c r2) s2'"] WT_gpv_ContD[OF step.prems(3) IO r2]
                3[OF joint _ out] step.prems(1) False
              by(simp_all add: pgen_lossless_gpv_def weight_gpv_def step.IH) }
          ultimately show ?thesis using False step.prems(1)
            by(rewrite in "ord_spmf _ _ \<hole>" exec_gpv.simps)
              (fastforce simp add: split_def bind_map_spmf map_spmf_bind_spmf oracle1 WT_gpv_OutD[OF step.prems(3)] intro!: ord_spmf_bind_reflI split!: generat.split dest: 3)
        qed
      qed
      show "ord_spmf (=) (exec_gpv oracle1 gpv s1) (map_spmf fst ?pq)" using * bad WT_gpv lossless
      proof(induction arbitrary: gpv s1 s2 rule: exec_gpv_fixp_induct_strong)
        case adm show ?case by simp
        case bottom show ?case by simp
        case (step exec_gpv')
        then show ?case
        proof(cases "bad2 s2")
          case True
          then have "weight_spmf (exec_gpv oracle2 gpv s2) = 1"
            using callee_invariant_on.weight_exec_gpv[OF bad_sticky2 lossless2, of s1 gpv s2]
              step.prems weight_spmf_le_1[of "exec_gpv oracle2 gpv s2"]
            by(simp add: pgen_lossless_gpv_def weight_gpv_def)
          then show ?thesis using True
            by(rewrite exec_until_bad.simps; rewrite exec_gpv.simps)
              (clarsimp intro!: ord_spmf_bind_reflI split!: generat.split simp add: step.hyps)
        next
          case False
          hence "\<not> bad1 s1" using step.prems(2) by simp
          moreover {
            fix out c r1 s1' r2 s2'
            assume IO: "IO out c \<in> set_spmf (the_gpv gpv)"
              and joint: "((r1, s1'), (r2, s2')) \<in> set_spmf (joint_oracle s1 s2 out)"
            from step.prems(3) IO have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpvD)
            from setD[OF _ out joint] step.prems(1) False
            have 1: "(r1, s1') \<in> set_spmf (oracle1 s1 out)"
              and 2: "(r2, s2') \<in> set_spmf (oracle2 s2 out)" by simp_all
            hence r1: "r1 \<in> responses_\<I> \<I> out" and r2: "r2 \<in> responses_\<I> \<I> out"
              using WT_oracle1 WT_oracle2 out by(blast dest: WT_calleeD)+
            have *: "plossless_gpv \<I> (c r2)" using step.prems(4) IO r2 step.prems(3)
              by(rule plossless_gpv_ContD)
            then have "bad2 s2' \<Longrightarrow> weight_spmf (exec_gpv oracle2 (c r2) s2') = 1" 
              and "\<not> bad2 s2' \<Longrightarrow> ord_spmf (=) (exec_gpv' (c r2) s1') (map_spmf fst (exec_until_bad (\<lambda>(x, y). joint_oracle x y) oracle1 bad1 oracle2 bad2 (c r2) s1' s2'))"
              using callee_invariant_on.weight_exec_gpv[OF bad_sticky2 lossless2, of s1' "c r2" s2'] 
                weight_spmf_le_1[of "exec_gpv oracle2 (c r2) s2'"] WT_gpv_ContD[OF step.prems(3) IO r2]
                3[OF joint _ out] step.prems(1) False
              by(simp_all add: pgen_lossless_gpv_def weight_gpv_def step.IH) }
          ultimately show ?thesis using False step.prems(1)
            by(rewrite exec_until_bad.simps)
              (fastforce simp add: map_spmf_bind_spmf WT_gpv_OutD[OF step.prems(3)] oracle1 bind_map_spmf step.hyps intro!: ord_spmf_bind_reflI split!: generat.split dest: 3)
        qed
      qed
    qed

    show "map_spmf snd ?pq = exec_gpv oracle2 gpv s2"
    proof(rule spmf.leq_antisym)
      show "ord_spmf (=) (map_spmf snd ?pq) (exec_gpv oracle2 gpv s2)" using * bad WT_gpv lossless
      proof(induction arbitrary: s1 s2 gpv rule: exec_until_bad_fixp_induct)
        case adm show ?case by simp
        case bottom show ?case by simp
        case (step exec_until_bad')
        show ?case
        proof(cases "bad2 s2")
          case True
          then have "weight_spmf (exec_gpv oracle1 gpv s1) = 1"
            using callee_invariant_on.weight_exec_gpv[OF bad_sticky1 lossless1, of s2 gpv s1]
              step.prems weight_spmf_le_1[of "exec_gpv oracle1 gpv s1"]
            by(simp add: pgen_lossless_gpv_def weight_gpv_def)
          then show ?thesis using True by simp
        next
          case False
          hence "\<not> bad1 s1" using step.prems(2) by simp
          moreover {
            fix out c r1 s1' r2 s2'
            assume IO: "IO out c \<in> set_spmf (the_gpv gpv)"
              and joint: "((r1, s1'), (r2, s2')) \<in> set_spmf (joint_oracle s1 s2 out)"
            from step.prems(3) IO have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpvD)
            from setD[OF _ out joint] step.prems(1) False
            have 1: "(r1, s1') \<in> set_spmf (oracle1 s1 out)"
              and 2: "(r2, s2') \<in> set_spmf (oracle2 s2 out)" by simp_all
            hence r1: "r1 \<in> responses_\<I> \<I> out" and r2: "r2 \<in> responses_\<I> \<I> out"
              using WT_oracle1 WT_oracle2 out by(blast dest: WT_calleeD)+
            have *: "plossless_gpv \<I> (c r1)" using step.prems(4) IO r1 step.prems(3)
              by(rule plossless_gpv_ContD)
            then have "bad2 s2' \<Longrightarrow> weight_spmf (exec_gpv oracle1 (c r1) s1') = 1"
              and "\<not> bad2 s2' \<Longrightarrow> ord_spmf (=) (map_spmf snd (exec_until_bad' (c r2) s1' s2')) (exec_gpv oracle2 (c r2) s2')"
              using callee_invariant_on.weight_exec_gpv[OF bad_sticky1 lossless1, of s2' "c r1" s1'] 
                weight_spmf_le_1[of "exec_gpv oracle1 (c r1) s1'"] WT_gpv_ContD[OF step.prems(3) IO r1]
                3[OF joint _ out] step.prems(1) False
              by(simp_all add: pgen_lossless_gpv_def weight_gpv_def step.IH) }
          ultimately show ?thesis using False step.prems(1)
            by(rewrite in "ord_spmf _ _ \<hole>" exec_gpv.simps)
              (fastforce simp add: split_def bind_map_spmf map_spmf_bind_spmf oracle2 WT_gpv_OutD[OF step.prems(3)] intro!: ord_spmf_bind_reflI split!: generat.split dest: 3)
        qed
      qed
      show "ord_spmf (=) (exec_gpv oracle2 gpv s2) (map_spmf snd ?pq)" using * bad WT_gpv lossless
      proof(induction arbitrary: gpv s1 s2 rule: exec_gpv_fixp_induct_strong)
        case adm show ?case by simp
        case bottom show ?case by simp
        case (step exec_gpv')
        then show ?case
        proof(cases "bad2 s2")
          case True
          then have "weight_spmf (exec_gpv oracle1 gpv s1) = 1"
            using callee_invariant_on.weight_exec_gpv[OF bad_sticky1 lossless1, of s2 gpv s1]
              step.prems weight_spmf_le_1[of "exec_gpv oracle1 gpv s1"]
            by(simp add: pgen_lossless_gpv_def weight_gpv_def)
          then show ?thesis using True
            by(rewrite exec_until_bad.simps; subst (2) exec_gpv.simps)
              (clarsimp intro!: ord_spmf_bind_reflI split!: generat.split simp add: step.hyps)
        next
          case False
          hence "\<not> bad1 s1" using step.prems(2) by simp
          moreover {
            fix out c r1 s1' r2 s2'
            assume IO: "IO out c \<in> set_spmf (the_gpv gpv)"
              and joint: "((r1, s1'), (r2, s2')) \<in> set_spmf (joint_oracle s1 s2 out)"
            from step.prems(3) IO have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpvD)
            from setD[OF _ out joint] step.prems(1) False
            have 1: "(r1, s1') \<in> set_spmf (oracle1 s1 out)"
              and 2: "(r2, s2') \<in> set_spmf (oracle2 s2 out)" by simp_all
            hence r1: "r1 \<in> responses_\<I> \<I> out" and r2: "r2 \<in> responses_\<I> \<I> out"
              using WT_oracle1 WT_oracle2 out by(blast dest: WT_calleeD)+
            have *: "plossless_gpv \<I> (c r1)" using step.prems(4) IO r1 step.prems(3)
              by(rule plossless_gpv_ContD)
            then have "bad2 s2' \<Longrightarrow> weight_spmf (exec_gpv oracle1 (c r1) s1') = 1" 
              and "\<not> bad2 s2' \<Longrightarrow> ord_spmf (=) (exec_gpv' (c r2) s2') (map_spmf snd (exec_until_bad (\<lambda>(x, y). joint_oracle x y) oracle1 bad1 oracle2 bad2 (c r2) s1' s2'))"
              using callee_invariant_on.weight_exec_gpv[OF bad_sticky1 lossless1, of s2' "c r1" s1'] 
                weight_spmf_le_1[of "exec_gpv oracle1 (c r1) s1'"] WT_gpv_ContD[OF step.prems(3) IO r1]
                3[OF joint _ out] step.prems(1) False
              by(simp_all add: pgen_lossless_gpv_def step.IH weight_gpv_def) }
          ultimately show ?thesis using False step.prems(1)
            by(rewrite exec_until_bad.simps)
              (fastforce simp add: map_spmf_bind_spmf WT_gpv_OutD[OF step.prems(3)] oracle2 bind_map_spmf step.hyps intro!: ord_spmf_bind_reflI split!: generat.split dest: 3)
        qed
      qed
    qed

    have "set_spmf ?pq \<subseteq> {(as1, bs2). ?R' as1 bs2}" using * bad WT_gpv
    proof(induction arbitrary: gpv s1 s2 rule: exec_until_bad_fixp_induct)
      case adm show ?case by(intro cont_intro ccpo_class.admissible_leI)
      case bottom show ?case by simp
      case step
      have switch: "set_spmf (exec_gpv oracle1 (c r1) s1') \<times> set_spmf (exec_gpv oracle2 (c r2) s2')
            \<subseteq> {((a, s1'), b, s2'). bad1 s1' = bad2 s2' \<and> (if bad2 s2' then X_bad s1' s2' else a = b \<and> X s1' s2')}"
        if "\<not> bad1 s1" "\<I> \<turnstile>g gpv \<surd>" "\<not> bad2 s2" and X: "X s1 s2" and out: "IO out c \<in> set_spmf (the_gpv gpv)"
        and joint: "((r1, s1'), (r2, s2')) \<in> set_spmf (joint_oracle s1 s2 out)" 
        and bad2: "bad2 s2'"
        for out c r1 s1' r2 s2'
      proof(clarify; rule conjI)
        from step.prems(3) out have outs: "out \<in> outs_\<I> \<I>" by(rule WT_gpv_OutD)
        from bad2 3[OF joint X this] have bad1: "bad1 s1' \<and> X_bad s1' s2'" by simp_all

        have s1': "(r1, s1') \<in> set_spmf (oracle1 s1 out)" and s2': "(r2, s2') \<in> set_spmf (oracle2 s2 out)"
          using setD[OF X outs joint] by simp_all
        have resp: "r1 \<in> responses_\<I> \<I> out" using WT_oracle1 s1' outs by(rule WT_calleeD)
        with step.prems(3) out have WT1: "\<I> \<turnstile>g c r1 \<surd>" by(rule WT_gpv_ContD)
        have resp: "r2 \<in> responses_\<I> \<I> out" using WT_oracle2 s2' outs by(rule WT_calleeD)
        with step.prems(3) out have WT2: "\<I> \<turnstile>g c r2 \<surd>" by(rule WT_gpv_ContD)

        fix r1' s1'' r2' s2''
        assume s1'': "(r1', s1'') \<in> set_spmf (exec_gpv oracle1 (c r1) s1')"
          and s2'': "(r2', s2'') \<in> set_spmf (exec_gpv oracle2 (c r2) s2')"
        have *: "bad1 s1'' \<and> X_bad s1'' s2'" using bad2 s1'' bad1 WT1
          by(rule callee_invariant_on.exec_gpv_invariant[OF bad_sticky1])
        have "bad2 s2'' \<and> X_bad s1'' s2''" using _ s2'' _ WT2
          by(rule callee_invariant_on.exec_gpv_invariant[OF bad_sticky2])(simp_all add: bad2 *)
        then show "bad1 s1'' = bad2 s2''" "if bad2 s2'' then X_bad s1'' s2'' else r1' = r2' \<and> X s1'' s2''"
          using * by(simp_all)
      qed
      show ?case using step.prems
        apply(clarsimp simp add: bind_UNION step.IH 3 WT_gpv_OutD WT_gpv_ContD del: subsetI intro!: UN_least split: generat.split if_split_asm)
        subgoal by(auto 4 3 dest: callee_invariant_on.exec_gpv_invariant[OF bad_sticky1, rotated] callee_invariant_on.exec_gpv_invariant[OF bad_sticky2, rotated] 3)
        apply(intro strip conjI)
        subgoal by(drule (6) switch) auto
        subgoal by(auto 4 3 intro!: step.IH[THEN order.trans] del: subsetI dest: 3 setD[rotated 2] simp add: WT_gpv_OutD WT_gpv_ContD intro: WT_gpv_ContD intro!: WT_calleeD[OF WT_oracle1])
        done
    qed
    then show "\<And>x y. (x, y) \<in> set_spmf ?pq \<Longrightarrow> ?R x y" by auto
  qed
qed

lemma exec_gpv_oracle_bisim_bad':
  fixes s1 :: 's1 and s2 :: 's2 and X :: "'s1 \<Rightarrow> 's2 \<Rightarrow> bool"
  and oracle1 :: "'s1 \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's1) spmf"
  and oracle2 :: "'s2 \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's2) spmf"
  assumes *: "if bad2 s2 then X_bad s1 s2 else X s1 s2"
  and bad: "bad1 s1 = bad2 s2"
  and bisim: "\<And>s1 s2 x. \<lbrakk> X s1 s2; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> rel_spmf (\<lambda>(a, s1') (b, s2'). bad1 s1' = bad2 s2' \<and> (if bad2 s2' then X_bad s1' s2' else a = b \<and> X s1' s2')) (oracle1 s1 x) (oracle2 s2 x)"
  and bad_sticky1: "\<And>s2. bad2 s2 \<Longrightarrow> callee_invariant_on oracle1 (\<lambda>s1. bad1 s1 \<and> X_bad s1 s2) \<I>"
  and bad_sticky2: "\<And>s1. bad1 s1 \<Longrightarrow> callee_invariant_on oracle2 (\<lambda>s2. bad2 s2 \<and> X_bad s1 s2) \<I>"
  and lossless1: "\<And>s1 x. \<lbrakk> bad1 s1; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> lossless_spmf (oracle1 s1 x)"
  and lossless2: "\<And>s2 x. \<lbrakk> bad2 s2; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> lossless_spmf (oracle2 s2 x)"
  and lossless: "lossless_gpv \<I> gpv"
  and WT_oracle1: "\<And>s1. \<I> \<turnstile>c oracle1 s1 \<surd>" (* stronger than the invariants above because unconditional *)
  and WT_oracle2: "\<And>s2. \<I> \<turnstile>c oracle2 s2 \<surd>"
  and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
  shows "rel_spmf (\<lambda>(a, s1') (b, s2'). bad1 s1' = bad2 s2' \<and> (if bad2 s2' then X_bad s1' s2' else a = b \<and> X s1' s2')) (exec_gpv oracle1 gpv s1) (exec_gpv oracle2 gpv s2)"
using assms(1-7) lossless_imp_plossless_gpv[OF lossless WT_gpv] assms(9-)
by(rule exec_gpv_oracle_bisim_bad_plossless)

lemma exec_gpv_oracle_bisim_bad_invariant:
  fixes s1 :: 's1 and s2 :: 's2 and X :: "'s1 \<Rightarrow> 's2 \<Rightarrow> bool" and I1 :: "'s1 \<Rightarrow> bool" and I2 :: "'s2 \<Rightarrow> bool"
  and oracle1 :: "'s1 \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's1) spmf"
  and oracle2 :: "'s2 \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's2) spmf"
  assumes *: "if bad2 s2 then X_bad s1 s2 else X s1 s2"
  and bad: "bad1 s1 = bad2 s2"
  and bisim: "\<And>s1 s2 x. \<lbrakk> X s1 s2; x \<in> outs_\<I> \<I>; I1 s1; I2 s2 \<rbrakk> \<Longrightarrow> rel_spmf (\<lambda>(a, s1') (b, s2'). bad1 s1' = bad2 s2' \<and> (if bad2 s2' then X_bad s1' s2' else a = b \<and> X s1' s2')) (oracle1 s1 x) (oracle2 s2 x)"
  and bad_sticky1: "\<And>s2. \<lbrakk> bad2 s2; I2 s2 \<rbrakk> \<Longrightarrow> callee_invariant_on oracle1 (\<lambda>s1. bad1 s1 \<and> X_bad s1 s2) \<I>"
  and bad_sticky2: "\<And>s1. \<lbrakk> bad1 s1; I1 s1 \<rbrakk> \<Longrightarrow> callee_invariant_on oracle2 (\<lambda>s2. bad2 s2 \<and> X_bad s1 s2) \<I>"
  and lossless1: "\<And>s1 x. \<lbrakk> bad1 s1; I1 s1; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> lossless_spmf (oracle1 s1 x)"
  and lossless2: "\<And>s2 x. \<lbrakk> bad2 s2; I2 s2; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> lossless_spmf (oracle2 s2 x)"
  and lossless: "lossless_gpv \<I> gpv"
  and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
  and I1: "callee_invariant_on oracle1 I1 \<I>"
  and I2: "callee_invariant_on oracle2 I2 \<I>"
  and s1: "I1 s1"
  and s2: "I2 s2"
  shows "rel_spmf (\<lambda>(a, s1') (b, s2'). bad1 s1' = bad2 s2' \<and> (if bad2 s2' then X_bad s1' s2' else a = b \<and> X s1' s2')) (exec_gpv oracle1 gpv s1) (exec_gpv oracle2 gpv s2)"
  including lifting_syntax
proof -
  interpret I1: callee_invariant_on oracle1 I1 \<I> by(fact I1)
  interpret I2: callee_invariant_on oracle2 I2 \<I> by(fact I2)
  from s1 have nonempty1: "{s. I1 s} \<noteq> {}" by auto
  { assume "\<exists>(Rep1 :: 's1' \<Rightarrow> 's1) Abs1. type_definition Rep1 Abs1 {s. I1 s}"
      and "\<exists>(Rep2 :: 's2' \<Rightarrow> 's2) Abs2. type_definition Rep2 Abs2 {s. I2 s}"
    then obtain Rep1 :: "'s1' \<Rightarrow> 's1" and Abs1 and Rep2 :: "'s2' \<Rightarrow> 's2" and Abs2
      where td1: "type_definition Rep1 Abs1 {s. I1 s}" and td2: "type_definition Rep2 Abs2 {s. I2 s}"
      by blast
    interpret td1: type_definition Rep1 Abs1 "{s. I1 s}" by(rule td1)
    interpret td2: type_definition Rep2 Abs2 "{s. I2 s}" by(rule td2)
    define cr1 where "cr1 \<equiv> \<lambda>x y. x = Rep1 y"
    have [transfer_rule]: "bi_unique cr1" "right_total cr1" using td1 cr1_def by(rule typedef_bi_unique typedef_right_total)+
    have [transfer_domain_rule]: "Domainp cr1 = I1" using type_definition_Domainp[OF td1 cr1_def] by simp
    define cr2 where "cr2 \<equiv> \<lambda>x y. x = Rep2 y"
    have [transfer_rule]: "bi_unique cr2" "right_total cr2" using td2 cr2_def by(rule typedef_bi_unique typedef_right_total)+
    have [transfer_domain_rule]: "Domainp cr2 = I2" using type_definition_Domainp[OF td2 cr2_def] by simp

    let ?C = "eq_onp (\<lambda>out. out \<in> outs_\<I> \<I>)"

    define oracle1' where "oracle1' \<equiv> (Rep1 ---> id ---> map_spmf (map_prod id Abs1)) oracle1"
    have [transfer_rule]: "(cr1 ===> ?C ===> rel_spmf (rel_prod (=) cr1)) oracle1 oracle1'"
      by(auto simp add: oracle1'_def rel_fun_def cr1_def spmf_rel_map prod.rel_map td1.Abs_inverse eq_onp_def intro!: rel_spmf_reflI intro: td1.Rep[simplified] dest: I1.callee_invariant)
    define oracle2' where "oracle2' \<equiv> (Rep2 ---> id ---> map_spmf (map_prod id Abs2)) oracle2"
    have [transfer_rule]: "(cr2 ===> ?C ===> rel_spmf (rel_prod (=) cr2)) oracle2 oracle2'"
      by(auto simp add: oracle2'_def rel_fun_def cr2_def spmf_rel_map prod.rel_map td2.Abs_inverse eq_onp_def intro!: rel_spmf_reflI intro: td2.Rep[simplified] dest: I2.callee_invariant)

    define s1' where "s1' \<equiv> Abs1 s1"
    have [transfer_rule]: "cr1 s1 s1'" using s1 by(simp add: cr1_def s1'_def td1.Abs_inverse)
    define s2' where "s2' \<equiv> Abs2 s2"
    have [transfer_rule]: "cr2 s2 s2'" using s2 by(simp add: cr2_def s2'_def td2.Abs_inverse)

    define bad1' where "bad1' \<equiv> (Rep1 ---> id) bad1"
    have [transfer_rule]: "(cr1 ===> (=)) bad1 bad1'" by(simp add: rel_fun_def bad1'_def cr1_def)
    define bad2' where "bad2' \<equiv> (Rep2 ---> id) bad2"
    have [transfer_rule]: "(cr2 ===> (=)) bad2 bad2'" by(simp add: rel_fun_def bad2'_def cr2_def)

    define X' where "X' \<equiv> (Rep1 ---> Rep2 ---> id) X"
    have [transfer_rule]: "(cr1 ===> cr2 ===> (=)) X X'" by(simp add: rel_fun_def X'_def cr1_def cr2_def)
    define X_bad' where "X_bad' \<equiv> (Rep1 ---> Rep2 ---> id) X_bad"
    have [transfer_rule]: "(cr1 ===> cr2 ===> (=)) X_bad X_bad'" by(simp add: rel_fun_def X_bad'_def cr1_def cr2_def)

    define gpv' where "gpv' \<equiv> restrict_gpv \<I> gpv"
    have [transfer_rule]: "rel_gpv (=) ?C gpv' gpv'"
      by(fold eq_onp_top_eq_eq)(auto simp add: gpv.rel_eq_onp eq_onp_same_args pred_gpv_def gpv'_def dest: in_outs'_restrict_gpvD)

    have "if bad2' s2' then X_bad' s1' s2' else X' s1' s2'" using * by transfer
    moreover have "bad1' s1' \<longleftrightarrow> bad2' s2'" using bad by transfer
    moreover have x: "?C x x" if "x \<in> outs_\<I> \<I>" for x using that by(simp add: eq_onp_def)
    have "rel_spmf (\<lambda>(a, s1') (b, s2'). (bad1' s1' \<longleftrightarrow> bad2' s2') \<and> (if bad2' s2' then X_bad' s1' s2' else a = b \<and> X' s1' s2')) (oracle1' s1 x) (oracle2' s2 x)"
      if "X' s1 s2" and "x \<in> outs_\<I> \<I>" for s1 s2 x using that(1) supply that(2)[THEN x, transfer_rule]
      by(transfer)(rule bisim[OF _ that(2)])
    moreover have [transfer_rule]: "rel_\<I> ?C (=) \<I> \<I>" by(rule rel_\<I>I)(auto simp add: set_relator_eq_onp eq_onp_same_args rel_set_eq dest: eq_onp_to_eq)
    have "callee_invariant_on oracle1' (\<lambda>s1. bad1' s1 \<and> X_bad' s1 s2) \<I>" if "bad2' s2" for s2
      using that unfolding callee_invariant_on_alt_def apply(transfer)
      using bad_sticky1[unfolded callee_invariant_on_alt_def] by blast
    moreover have "callee_invariant_on oracle2' (\<lambda>s2. bad2' s2 \<and> X_bad' s1 s2) \<I>" if "bad1' s1" for s1
      using that unfolding callee_invariant_on_alt_def apply(transfer)
      using bad_sticky2[unfolded callee_invariant_on_alt_def] by blast
    moreover have "lossless_spmf (oracle1' s1 x)" if "bad1' s1" "x \<in> outs_\<I> \<I>" for s1 x
      using that supply that(2)[THEN x, transfer_rule] by transfer(rule lossless1)
    moreover have "lossless_spmf (oracle2' s2 x)" if "bad2' s2" "x \<in> outs_\<I> \<I>" for s2 x
      using that supply that(2)[THEN x, transfer_rule] by transfer(rule lossless2)
    moreover have "lossless_gpv \<I> gpv'" using WT_gpv lossless by(simp add: gpv'_def lossless_restrict_gpvI)
    moreover have "\<I> \<turnstile>c oracle1' s1 \<surd>" for s1 using I1.WT_callee by transfer
    moreover have "\<I> \<turnstile>c oracle2' s2 \<surd>" for s2 using I2.WT_callee by transfer
    moreover have "\<I> \<turnstile>g gpv' \<surd>" by(simp add: gpv'_def)
    ultimately have **: "rel_spmf (\<lambda>(a, s1') (b, s2'). bad1' s1' = bad2' s2' \<and> (if bad2' s2' then X_bad' s1' s2' else a = b \<and> X' s1' s2')) (exec_gpv oracle1' gpv' s1') (exec_gpv oracle2' gpv' s2')"
      by(rule exec_gpv_oracle_bisim_bad')
    have [transfer_rule]: "((=) ===> ?C ===> rel_spmf (rel_prod (=) (=))) oracle2 oracle2"
      "((=) ===> ?C ===> rel_spmf (rel_prod (=) (=))) oracle1 oracle1"
      by(simp_all add: rel_fun_def eq_onp_def prod.rel_eq)
    note [transfer_rule] = bi_unique_eq_onp bi_unique_eq
    from ** have "rel_spmf (\<lambda>(a, s1') (b, s2'). bad1 s1' = bad2 s2' \<and> (if bad2 s2' then X_bad s1' s2' else a = b \<and> X s1' s2')) (exec_gpv oracle1 gpv' s1) (exec_gpv oracle2 gpv' s2)"
      by(transfer)
    also have "exec_gpv oracle1 gpv' s1 = exec_gpv oracle1 gpv s1"
      unfolding gpv'_def using WT_gpv s1 by(rule I1.exec_gpv_restrict_gpv_invariant)
    also have "exec_gpv oracle2 gpv' s2 = exec_gpv oracle2 gpv s2"
      unfolding gpv'_def using WT_gpv s2 by(rule I2.exec_gpv_restrict_gpv_invariant)
    finally have ?thesis . }
  from this[cancel_type_definition, OF nonempty1, cancel_type_definition] s2 show ?thesis by blast
qed

lemma exec_gpv_oracle_bisim_bad:
  assumes *: "if bad2 s2 then X_bad s1 s2 else X s1 s2"
  and bad: "bad1 s1 = bad2 s2"
  and bisim: "\<And>s1 s2 x. X s1 s2 \<Longrightarrow> rel_spmf (\<lambda>(a, s1') (b, s2'). bad1 s1' = bad2 s2' \<and> (if bad2 s2' then X_bad s1' s2' else a = b \<and> X s1' s2')) (oracle1 s1 x) (oracle2 s2 x)"
  and bad_sticky1: "\<And>s2. bad2 s2 \<Longrightarrow> callee_invariant_on oracle1 (\<lambda>s1. bad1 s1 \<and> X_bad s1 s2) \<I>"
  and bad_sticky2: "\<And>s1. bad1 s1 \<Longrightarrow> callee_invariant_on oracle2 (\<lambda>s2. bad2 s2 \<and> X_bad s1 s2) \<I>"
  and lossless1: "\<And>s1 x. bad1 s1 \<Longrightarrow> lossless_spmf (oracle1 s1 x)"
  and lossless2: "\<And>s2 x. bad2 s2 \<Longrightarrow> lossless_spmf (oracle2 s2 x)"
  and lossless: "lossless_gpv \<I> gpv"
  and WT_oracle1: "\<And>s1. \<I> \<turnstile>c oracle1 s1 \<surd>"
  and WT_oracle2: "\<And>s2. \<I> \<turnstile>c oracle2 s2 \<surd>"
  and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
  and R: "\<And>a s1 b s2. \<lbrakk> bad1 s1 = bad2 s2; \<not> bad2 s2 \<Longrightarrow> a = b \<and> X s1 s2; bad2 s2 \<Longrightarrow> X_bad s1 s2 \<rbrakk> \<Longrightarrow> R (a, s1) (b, s2)"
  shows "rel_spmf R (exec_gpv oracle1 gpv s1) (exec_gpv oracle2 gpv s2)"
using exec_gpv_oracle_bisim_bad'[OF * bad bisim bad_sticky1 bad_sticky2 lossless1 lossless2 lossless WT_oracle1 WT_oracle2 WT_gpv]
by(rule rel_spmf_mono)(auto intro: R)

lemma exec_gpv_oracle_bisim_bad_full:
  assumes "X s1 s2"
  and "bad1 s1 = bad2 s2"
  and "\<And>s1 s2 x. X s1 s2 \<Longrightarrow> rel_spmf (\<lambda>(a, s1') (b, s2'). bad1 s1' = bad2 s2' \<and> (\<not> bad2 s2' \<longrightarrow> a = b \<and> X s1' s2')) (oracle1 s1 x) (oracle2 s2 x)"
  and "callee_invariant oracle1 bad1"
  and "callee_invariant oracle2 bad2"
  and "\<And>s1 x. bad1 s1 \<Longrightarrow> lossless_spmf (oracle1 s1 x)"
  and "\<And>s2 x. bad2 s2 \<Longrightarrow> lossless_spmf (oracle2 s2 x)"
  and "lossless_gpv \<I>_full gpv"
  and R: "\<And>a s1 b s2. \<lbrakk> bad1 s1 = bad2 s2; \<not> bad2 s2 \<Longrightarrow> a = b \<and> X s1 s2 \<rbrakk> \<Longrightarrow> R (a, s1) (b, s2)"
  shows "rel_spmf R (exec_gpv oracle1 gpv s1) (exec_gpv oracle2 gpv s2)"
using assms
by(intro exec_gpv_oracle_bisim_bad[of bad2 s2 "\<lambda>_ _. True" s1 X bad1 oracle1 oracle2 \<I>_full gpv R])(auto intro: rel_spmf_mono)

lemma max_enn2ereal: "max (enn2ereal x) (enn2ereal y) = enn2ereal (max x y)"
including ennreal.lifting unfolding max_def by transfer simp

lemma identical_until_bad:
  assumes bad_eq: "map_spmf bad p = map_spmf bad q"
  and not_bad: "measure (measure_spmf (map_spmf (\<lambda>x. (f x, bad x)) p)) (A \<times> {False}) = measure (measure_spmf (map_spmf (\<lambda>x. (f x, bad x)) q)) (A \<times> {False})"
  shows "\<bar>measure (measure_spmf (map_spmf f p)) A - measure (measure_spmf (map_spmf f q)) A\<bar> \<le> spmf (map_spmf bad p) True"
proof -
  have "\<bar>enn2ereal (measure (measure_spmf (map_spmf f p)) A) - enn2ereal (measure (measure_spmf (map_spmf f q)) A)\<bar> = 
    \<bar>enn2ereal (\<integral>\<^sup>+ x. indicator A (f x) \<partial>measure_spmf p) - enn2ereal (\<integral>\<^sup>+ x. indicator A (f x) \<partial>measure_spmf q)\<bar>"
    unfolding measure_spmf.emeasure_eq_measure[symmetric]
    by(simp add: nn_integral_indicator[symmetric] indicator_vimage[abs_def] o_def)
  also have "\<dots> =
    \<bar>enn2ereal (\<integral>\<^sup>+ x. indicator (A \<times> {False}) (f x, bad x) + indicator (A \<times> {True}) (f x, bad x) \<partial>measure_spmf p) -
     enn2ereal (\<integral>\<^sup>+ x. indicator (A \<times> {False}) (f x, bad x) + indicator (A \<times> {True}) (f x, bad x) \<partial>measure_spmf q)\<bar>"
    by(intro arg_cong[where f=abs] arg_cong2[where f="(-)"] arg_cong[where f=enn2ereal] nn_integral_cong)(simp_all split: split_indicator)
  also have "\<dots> = 
    \<bar>enn2ereal (emeasure (measure_spmf (map_spmf (\<lambda>x. (f x, bad x)) p)) (A \<times> {False}) + (\<integral>\<^sup>+ x. indicator (A \<times> {True}) (f x, bad x) \<partial>measure_spmf p)) -
     enn2ereal (emeasure (measure_spmf (map_spmf (\<lambda>x. (f x, bad x)) q)) (A \<times> {False}) + (\<integral>\<^sup>+ x. indicator (A \<times> {True}) (f x, bad x) \<partial>measure_spmf q))\<bar>"
    by(subst (1 2) nn_integral_add)(simp_all add: indicator_vimage[abs_def] o_def nn_integral_indicator[symmetric])
  also have "\<dots> = \<bar>enn2ereal (\<integral>\<^sup>+ x. indicator (A \<times> {True}) (f x, bad x) \<partial>measure_spmf p) - enn2ereal (\<integral>\<^sup>+ x. indicator (A \<times> {True}) (f x, bad x) \<partial>measure_spmf q)\<bar>"
    (is "_ = \<bar>?x - ?y\<bar>")
    by(simp add: measure_spmf.emeasure_eq_measure not_bad plus_ennreal.rep_eq ereal_diff_add_eq_diff_diff_swap ereal_diff_add_assoc2 ereal_add_uminus_conv_diff)
  also have "\<dots> \<le> max ?x ?y"
  proof(rule ereal_abs_leI)
    have "?x - ?y \<le> ?x - 0" by(rule ereal_minus_mono)(simp_all)
    also have "\<dots> \<le> max ?x ?y" by simp
    finally show "?x - ?y \<le> \<dots>" .

    have "- (?x - ?y) = ?y - ?x"
      by(rule ereal_minus_diff_eq)(simp_all add: measure_spmf.nn_integral_indicator_neq_top)
    also have "\<dots> \<le> ?y - 0" by(rule ereal_minus_mono)(simp_all)
    also have "\<dots> \<le> max ?x ?y" by simp
    finally show "- (?x - ?y) \<le> \<dots>" .
  qed
  also have "\<dots> \<le> enn2ereal (max (\<integral>\<^sup>+ x. indicator {True} (bad x) \<partial>measure_spmf p) (\<integral>\<^sup>+ x. indicator {True} (bad x) \<partial>measure_spmf q))"
    unfolding max_enn2ereal less_eq_ennreal.rep_eq[symmetric]
    by(intro max.mono nn_integral_mono)(simp_all split: split_indicator)
  also have "\<dots> = enn2ereal (spmf (map_spmf bad p) True)"
    using arg_cong2[where f=spmf, OF bad_eq refl, of True, THEN arg_cong[where f=ennreal]]
    unfolding ennreal_spmf_map_conv_nn_integral indicator_vimage[abs_def] by simp
  finally show ?thesis by simp
qed

lemma (in callee_invariant_on) exec_gpv_bind_materialize:
  fixes f :: "'s \<Rightarrow> 'r spmf"
  and g :: "'x \<times> 's \<Rightarrow> 'r \<Rightarrow> 'y spmf"
  and s :: "'s"
  defines "exec_gpv2 \<equiv> exec_gpv"
  assumes cond: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s \<rbrakk> \<Longrightarrow> f s = f s'"
  and \<I>: "\<I> = \<I>_full" (* TODO: generalize *)
  shows "bind_spmf (exec_gpv callee gpv s) (\<lambda>as. bind_spmf (f (snd as)) (g as)) =
    exec_gpv2 (\<lambda>(r, s) x. bind_spmf (callee s x) (\<lambda>(y, s'). if I s' \<and> r = None then map_spmf (\<lambda>r. (y, (Some r, s'))) (f s') else return_spmf (y, (r, s')))) gpv (None, s)
    \<bind> (\<lambda>(a, r, s). case r of None \<Rightarrow> bind_spmf (f s) (g (a, s)) | Some r' \<Rightarrow> g (a, s) r')"
    (is "?lhs = ?rhs" is "_ = bind_spmf (exec_gpv2 ?callee2 _ _) _")
proof -
  define exec_gpv1 :: "('a, 'b, 's option \<times> 's) callee \<Rightarrow> ('x, 'a, 'b) gpv \<Rightarrow> _"
    where [simp]: "exec_gpv1 = exec_gpv"
  let ?X = "\<lambda>s (ss, s'). s = s'"
  let ?callee = "\<lambda>(ss, s) x. map_spmf (\<lambda>(y, s'). (y, if I s' \<and> ss = None then Some s' else ss, s')) (callee s x)"
  let ?track = "exec_gpv1 ?callee gpv (None, s)"
  have "rel_spmf (rel_prod (=) ?X) (exec_gpv callee gpv s) ?track" unfolding exec_gpv1_def
    by(rule exec_gpv_oracle_bisim[where X="?X"])(auto simp add: spmf_rel_map intro!: rel_spmf_reflI)
  hence "exec_gpv callee gpv s = map_spmf (\<lambda>(a, ss, s). (a, s)) ?track"
    by(auto simp add: spmf_rel_eq[symmetric] spmf_rel_map elim: rel_spmf_mono)
  hence "?lhs = bind_spmf ?track (\<lambda>(a, s'', s'). bind_spmf (f s') (g (a, s')))"
    by(simp add: bind_map_spmf o_def split_def)
  also let ?inv = "\<lambda>(ss, s). case ss of None \<Rightarrow> True | Some s' \<Rightarrow> f s = f s' \<and> I s' \<and> I s"
  interpret inv: callee_invariant_on "?callee" "?inv" \<I>
    by unfold_locales(auto 4 4 split: option.split if_split_asm dest: cond callee_invariant simp add: \<I>)
  have "bind_spmf ?track (\<lambda>(a, s'', s'). bind_spmf (f s') (g (a, s'))) =
    bind_spmf ?track (\<lambda>(a, ss', s'). bind_spmf (f (case ss' of None \<Rightarrow> s' | Some s'' \<Rightarrow> s'')) (g (a, s')))"
    (is "_ = ?rhs'")
    by(rule bind_spmf_cong[OF refl])(auto dest!: inv.exec_gpv_invariant split: option.split_asm simp add: \<I>)
  also
  have track_Some: "exec_gpv ?callee gpv (Some ss, s) = map_spmf (\<lambda>(a, s). (a, Some ss, s)) (exec_gpv callee gpv s)"
    for s ss :: 's and gpv :: "('x, 'a, 'b) gpv"
  proof -
    let ?X = "\<lambda>(ss', s') s. s = s' \<and> ss' = Some ss"
    have "rel_spmf (rel_prod (=) ?X) (exec_gpv ?callee gpv (Some ss, s)) (exec_gpv callee gpv s)"
      by(rule exec_gpv_oracle_bisim[where X="?X"])(auto simp add: spmf_rel_map intro!: rel_spmf_reflI)
    thus ?thesis by(auto simp add: spmf_rel_eq[symmetric] spmf_rel_map elim: rel_spmf_mono)
  qed
  have sample_Some: "exec_gpv ?callee2 gpv (Some r, s) = map_spmf (\<lambda>(a, s). (a, Some r, s)) (exec_gpv callee gpv s)" 
    for s :: 's and r :: 'r and gpv :: "('x, 'a, 'b) gpv"
  proof -
    let ?X = "\<lambda>(r', s') s. s' = s \<and> r' = Some r"
    have "rel_spmf (rel_prod (=) ?X) (exec_gpv ?callee2 gpv (Some r, s)) (exec_gpv callee gpv s)"
      by(rule exec_gpv_oracle_bisim[where X="?X"])(auto simp add: spmf_rel_map map_spmf_conv_bind_spmf[symmetric] split_def intro!: rel_spmf_reflI)
    then show ?thesis by(auto simp add: spmf_rel_eq[symmetric] spmf_rel_map elim: rel_spmf_mono)
  qed
  have "?rhs' = ?rhs"
    \<comment> \<open>Actually, parallel fixpoint induction should be used here, but then we cannot use the
      facts @{thm [source] track_Some} and @{thm [source] sample_Some} because fixpoint induction
      replaces @{const exec_gpv} with approximations. So we do two separate fixpoint inductions
      instead and jump from the approximation to the fixpoint when the state has been found.\<close>
  proof(rule spmf.leq_antisym)
    show "ord_spmf (=) ?rhs' ?rhs" unfolding exec_gpv1_def
    proof(induction arbitrary: gpv s rule: exec_gpv_fixp_induct_strong)
      case adm show ?case by simp
      case bottom show ?case by simp
      case (step exec_gpv')
      show ?case unfolding exec_gpv2_def
        apply(rewrite in "ord_spmf _ _ \<hole>" exec_gpv.simps)
        apply(clarsimp split: generat.split simp add: bind_map_spmf intro!: ord_spmf_bind_reflI split del: if_split)
        subgoal for out rpv ret s'
          apply(cases "I s'")
          subgoal
            apply simp
            apply(rule spmf.leq_trans)
             apply(rule ord_spmf_bindI[OF step.hyps])
             apply hypsubst
             apply(rule spmf.leq_refl)
            apply(simp add: track_Some sample_Some bind_map_spmf o_def)
            apply(subst bind_commute_spmf)
            apply(simp add: split_def)
            done
          subgoal
            apply simp
            apply(rule step.IH[THEN spmf.leq_trans])
            apply(simp add: split_def exec_gpv2_def)
            done
          done
        done
    qed
    show "ord_spmf (=) ?rhs ?rhs'" unfolding exec_gpv2_def
    proof(induction arbitrary: gpv s rule: exec_gpv_fixp_induct_strong)
      case adm show ?case by simp
      case bottom show ?case by simp
      case (step exec_gpv')
      show ?case unfolding exec_gpv1_def
        apply(rewrite in "ord_spmf _ _ \<hole>" exec_gpv.simps)
        apply(clarsimp split: generat.split simp add: bind_map_spmf intro!: ord_spmf_bind_reflI split del: if_split)
        subgoal for out rpv ret s'
          apply(cases "I s'")
          subgoal
            apply(simp add: bind_map_spmf o_def)
            apply(rule spmf.leq_trans)
             apply(rule ord_spmf_bind_reflI)
             apply(rule ord_spmf_bindI)
              apply(rule step.hyps)
             apply hypsubst
             apply(rule spmf.leq_refl)
            apply(simp add: track_Some sample_Some bind_map_spmf o_def)
            apply(subst bind_commute_spmf)
            apply(simp add: split_def)
            done
          subgoal
            apply simp
            apply(rule step.IH[THEN spmf.leq_trans])
            apply(simp add: split_def exec_gpv2_def)
            done
          done
        done
    qed
  qed
  finally show ?thesis .
qed

primcorec gpv_stop :: "('a, 'c, 'r) gpv \<Rightarrow> ('a option, 'c, 'r option) gpv"
where
  "the_gpv (gpv_stop gpv) = 
   map_spmf (map_generat Some id (\<lambda>rpv input. case input of None \<Rightarrow> Done None | Some input' \<Rightarrow> gpv_stop (rpv input'))) 
     (the_gpv gpv)"

lemma gpv_stop_Done [simp]: "gpv_stop (Done x) = Done (Some x)"
by(rule gpv.expand) simp

lemma gpv_stop_Fail [simp]: "gpv_stop Fail = Fail"
by(rule gpv.expand) simp

lemma gpv_stop_Pause [simp]: "gpv_stop (Pause out rpv) = Pause out (\<lambda>input. case input of None \<Rightarrow> Done None | Some input' \<Rightarrow> gpv_stop (rpv input'))"
by(rule gpv.expand) simp

lemma gpv_stop_lift_spmf [simp]: "gpv_stop (lift_spmf p) = lift_spmf (map_spmf Some p)"
by(rule gpv.expand)(simp add: spmf.map_comp o_def)

lemma gpv_stop_bind [simp]:
  "gpv_stop (bind_gpv gpv f) = bind_gpv (gpv_stop gpv) (\<lambda>x. case x of None \<Rightarrow> Done None | Some x' \<Rightarrow> gpv_stop (f x'))"
apply(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
apply(auto 4 3 simp add: spmf_rel_map map_spmf_bind_spmf o_def bind_map_spmf bind_gpv.sel generat.rel_map simp del: bind_gpv_sel' intro!: rel_spmf_bind_reflI generat.rel_refl_strong rel_spmf_reflI rel_funI split!: generat.split option.split)
done

context includes lifting_syntax begin

lemma gpv_stop_parametric':
  notes [transfer_rule] = the_gpv_parametric' the_gpv_parametric' Done_parametric' corec_gpv_parametric'
  shows "(rel_gpv'' A C R ===> rel_gpv'' (rel_option A) C (rel_option R)) gpv_stop gpv_stop"
unfolding gpv_stop_def by transfer_prover

lemma gpv_stop_parametric [transfer_rule]:
  shows "(rel_gpv A C ===> rel_gpv (rel_option A) C) gpv_stop gpv_stop"
unfolding gpv_stop_def by transfer_prover

lemma gpv_stop_transfer:
  "(rel_gpv'' A B C ===> rel_gpv'' (pcr_Some A) B (pcr_Some C)) (\<lambda>x. x) gpv_stop"
apply(rule rel_funI)
subgoal for gpv gpv'
  apply(coinduction arbitrary: gpv gpv')
  apply(drule rel_gpv''D)
  apply(auto simp add: spmf_rel_map generat.rel_map rel_fun_def elim!: pcr_SomeE generat.rel_mono_strong rel_spmf_mono)
  done
done

end
  
lemma gpv_stop_map' [simp]:
  "gpv_stop (map_gpv' f g h gpv) = map_gpv' (map_option f) g (map_option h) (gpv_stop gpv)"
apply(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
apply(auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI generat.rel_refl_strong split!: option.split)
done

lemma interaction_bound_gpv_stop [simp]:
  "interaction_bound consider (gpv_stop gpv) = interaction_bound consider gpv"
proof(induction arbitrary: gpv rule: parallel_fixp_induct_strong_1_1[OF complete_lattice_partial_function_definitions complete_lattice_partial_function_definitions interaction_bound.mono interaction_bound.mono interaction_bound_def interaction_bound_def, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
next
  case (step interaction_bound' interaction_bound'')
  have "(SUP x. interaction_bound' (case x of None \<Rightarrow> Done None | Some input \<Rightarrow> gpv_stop (c input))) =
        (SUP input. interaction_bound'' (c input))" (is "?lhs = ?rhs" is "(SUP x. ?f x) = _")
    if "IO out c \<in> set_spmf (the_gpv gpv)" for out c
  proof -
    have "?lhs = sup (interaction_bound' (Done None)) (\<Squnion>x. ?f (Some x))"
      by (simp add: UNIV_option_conv image_comp)
    also have "interaction_bound' (Done None) = 0" using step.hyps(1)[of "Done None"] by simp
    also have "(\<Squnion>x. ?f (Some x)) = ?rhs" by (simp add: step.IH)
    finally show ?thesis by (simp add: bot_enat_def [symmetric])
  qed
  then show ?case
    by (auto simp add: case_map_generat o_def image_comp cong del: generat.case_cong_weak if_weak_cong intro!: SUP_cong split: generat.split)
qed
  
abbreviation exec_gpv_stop :: "('s \<Rightarrow> 'c \<Rightarrow> ('r option \<times> 's) spmf) \<Rightarrow> ('a, 'c, 'r) gpv \<Rightarrow> 's \<Rightarrow> ('a option \<times> 's) spmf"
where "exec_gpv_stop callee gpv \<equiv> exec_gpv callee (gpv_stop gpv)"

abbreviation inline_stop :: "('s \<Rightarrow> 'c \<Rightarrow> ('r option \<times> 's, 'c', 'r') gpv) \<Rightarrow> ('a, 'c, 'r) gpv \<Rightarrow> 's \<Rightarrow> ('a option \<times> 's, 'c', 'r') gpv"
where "inline_stop callee gpv \<equiv> inline callee (gpv_stop gpv)"

context
  fixes joint_oracle :: "'s1 \<Rightarrow> 's2 \<Rightarrow> 'c \<Rightarrow> (('r option \<times> 's1) option \<times> ('r option \<times> 's2) option) pmf"
  and callee1 :: "'s1 \<Rightarrow> 'c \<Rightarrow> ('r option \<times> 's1) spmf"
  notes [[function_internals]]
begin

partial_function (spmf) exec_until_stop :: "('a option, 'c, 'r) gpv \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool \<Rightarrow> ('a option \<times> 's1 \<times> 's2) spmf"
where
  "exec_until_stop gpv s1 s2 b =
  (if b then 
     bind_spmf (the_gpv gpv) (\<lambda>generat. case generat of
       Pure x \<Rightarrow> return_spmf (x, s1, s2)
     | IO out rpv \<Rightarrow> bind_pmf (joint_oracle s1 s2 out) (\<lambda>(a, b).
         case a of None \<Rightarrow> return_pmf None
         | Some (r1, s1') \<Rightarrow> (case b of None \<Rightarrow> undefined | Some (r2, s2') \<Rightarrow>
           (case (r1, r2) of (None, None) \<Rightarrow> exec_until_stop (Done None) s1' s2' True
             | (Some r1', Some r2') \<Rightarrow> exec_until_stop (rpv r1') s1' s2' True
             | (None, Some r2') \<Rightarrow> exec_until_stop (Done None) s1' s2' True
             | (Some r1', None) \<Rightarrow> exec_until_stop (rpv r1') s1' s2' False))))
   else
     bind_spmf (the_gpv gpv) (\<lambda>generat. case generat of
       Pure x \<Rightarrow> return_spmf (None, s1, s2)
     | IO out rpv \<Rightarrow> bind_spmf (callee1 s1 out) (\<lambda>(r1, s1').
         case r1 of None \<Rightarrow> exec_until_stop (Done None) s1' s2 False
           | Some r1' \<Rightarrow> exec_until_stop (rpv r1') s1' s2 False)))"

end

lemma ord_spmf_exec_gpv_stop: (* TODO: generalize ord_spmf to support different type variables *)
  fixes callee1 :: "('c, 'r option, 's) callee"
  and callee2 :: "('c, 'r option, 's) callee"
  and S :: "'s \<Rightarrow> 's \<Rightarrow> bool"
  and gpv :: "('a, 'c, 'r) gpv"
  assumes bisim:
    "\<And>s1 s2 x. \<lbrakk> S s1 s2; \<not> stop s2 \<rbrakk> \<Longrightarrow> 
    ord_spmf (\<lambda>(r1, s1') (r2, s2'). le_option r2 r1 \<and> S s1' s2' \<and> (r2 = None \<and> r1 \<noteq> None \<longleftrightarrow> stop s2'))
      (callee1 s1 x) (callee2 s2 x)"
  and init: "S s1 s2"
  and go: "\<not> stop s2"
  and sticking: "\<And>s1 s2 x y s1'. \<lbrakk> (y, s1') \<in> set_spmf (callee1 s1 x); S s1 s2; stop s2 \<rbrakk> \<Longrightarrow> S s1' s2"
  shows "ord_spmf (rel_prod (ord_option \<top>)\<inverse>\<inverse> S) (exec_gpv_stop callee1 gpv s1) (exec_gpv_stop callee2 gpv s2)"
proof -
  let ?R = "\<lambda>(r1, s1') (r2, s2'). le_option r2 r1 \<and> S s1' s2' \<and> (r2 = None \<and> r1 \<noteq> None \<longleftrightarrow> stop s2')"
  obtain joint :: "'s \<Rightarrow> 's \<Rightarrow> 'c \<Rightarrow> (('r option \<times> 's) option \<times> ('r option \<times> 's) option) pmf"
    where j1: "map_pmf fst (joint s1 s2 x) = callee1 s1 x"
    and j2: "map_pmf snd (joint s1 s2 x) = callee2 s2 x"
    and rel [rule_format, rotated -1]: "\<forall>(a, b) \<in> set_pmf (joint s1 s2 x). ord_option ?R a b"
    if "S s1 s2" "\<not> stop s2" for x s1 s2 using bisim
    apply atomize_elim 
    apply(subst (asm) rel_pmf.simps)
    apply(unfold rel_spmf_simps all_conj_distrib[symmetric] all_simps(6) imp_conjR[symmetric])
    apply(subst all_comm)
    apply(subst (2) all_comm)
    apply(subst choice_iff[symmetric] ex_simps(6))+
    apply fastforce
    done
  note [simp del] = top_apply conversep_iff id_apply
  have "\<not> stop s2 \<Longrightarrow> rel_spmf (rel_prod (ord_option \<top>)\<inverse>\<inverse> S) (exec_gpv_stop callee1 gpv s1) (map_spmf (\<lambda>(x, s1, s2). (x, s2)) (exec_until_stop joint callee1 (map_gpv Some id gpv) s1 s2 True))"
    and "rel_spmf (rel_prod (ord_option \<top>)\<inverse>\<inverse> S) (exec_gpv callee1 (Done None :: ('a option, 'c, 'r option) gpv) s1) (map_spmf (\<lambda>(x, s1, s2). (x, s2)) (exec_until_stop joint callee1 (Done None :: ('a option, 'c, 'r) gpv) s1 s2 b))"
    and "stop s2 \<Longrightarrow> rel_spmf (rel_prod (ord_option \<top>)\<inverse>\<inverse> S) (exec_gpv_stop callee1 gpv s1) (map_spmf (\<lambda>(x, s1, y). (x, y)) (exec_until_stop joint callee1 (map_gpv Some id gpv) s1 s2 False))"
    for b using init
  proof(induction arbitrary: gpv s1 s2 b rule: parallel_fixp_induct_2_4[OF partial_function_definitions_spmf partial_function_definitions_spmf exec_gpv.mono exec_until_stop.mono exec_gpv_def exec_until_stop_def, unfolded lub_spmf_empty, case_names adm bottom step])
    case adm show ?case by simp
    { case bottom case 1 show ?case by simp }
    { case bottom case 2 show ?case by simp }
    { case bottom case 3 show ?case by simp }
  next
    case (step exec_gpv' exec_until_stop') case step: 1
    show ?case using step.prems
      apply(rewrite gpv_stop.sel)
      apply(simp add: map_spmf_bind_spmf bind_map_spmf gpv.map_sel)
      apply(rule rel_spmf_bind_reflI)
      apply(clarsimp split!: generat.split)
      apply(rewrite j1[symmetric], assumption+)
      apply(rewrite bind_spmf_def)
      apply(auto 4 3 split!: option.split dest: rel intro: step.IH intro!: rel_pmf_bind_reflI simp add: map_bind_pmf bind_map_pmf)
      done
  next
    case step case 2
    then show ?case by(simp add: conversep_iff)
  next
    case (step exec_gpv' exec_until_stop') case step: 3
    show ?case using step.prems
      apply(simp add: map_spmf_bind_spmf bind_map_spmf gpv.map_sel)
      apply(rule rel_spmf_bind_reflI)
      apply(clarsimp simp add: map_spmf_bind_spmf split!: generat.split)
      apply(rule rel_spmf_bind_reflI)
      apply clarsimp
      apply(drule (2) sticking)
      apply(auto split!: option.split intro: step.IH)
      done
  qed
  note this(1)[OF go]
  also
  have "\<not> stop s2 \<Longrightarrow> ord_spmf (=) (map_spmf (\<lambda>(x, s1, s2). (x, s2)) (exec_until_stop joint callee1 (map_gpv Some id gpv) s1 s2 True)) (exec_gpv_stop callee2 gpv s2)"
    and "ord_spmf (=) (map_spmf (\<lambda>(x, s1, y). (x, y)) (exec_until_stop joint callee1 (Done None :: ('a option, 'c, 'r) gpv) s1 s2 b)) (return_spmf (None, s2))"
    and "stop s2 \<Longrightarrow> ord_spmf (=) (map_spmf (\<lambda>(x, s1, s2). (x, s2)) (exec_until_stop joint callee1 (map_gpv Some id gpv) s1 s2 False)) (return_spmf (None, s2))"
    for b using init
  proof(induction arbitrary: gpv s1 s2 b rule: exec_until_stop.fixp_induct[case_names adm bottom step])
    case adm show ?case by simp
    { case bottom case 1 show ?case by simp }
    { case bottom case 2 show ?case by simp }
    { case bottom case 3 show ?case by simp }
  next
    case (step exec_until_stop') case step: 1
    show ?case using step.prems
      using [[show_variants]]
      apply(rewrite exec_gpv.simps)
      apply(simp add: map_spmf_bind_spmf bind_map_spmf gpv.map_sel)
      apply(rule ord_spmf_bind_reflI)
      apply(clarsimp split!: generat.split simp add: map_bind_pmf bind_spmf_def)
      apply(rewrite j2[symmetric], assumption+)
      apply(auto 4 3 split!: option.split dest: rel intro: step.IH intro!: rel_pmf_bind_reflI simp add: bind_map_pmf)
      done
  next
    case step case 2 thus ?case by simp
  next
    case (step exec_until_stop') case 3
    thus ?case
      apply(simp add: map_spmf_bind_spmf o_def)
      apply(rule ord_spmf_bind_spmfI1)
      apply(clarsimp split!: generat.split simp add: map_spmf_bind_spmf o_def gpv.map_sel)
      apply(rule ord_spmf_bind_spmfI1)
      apply clarsimp
      apply(drule (2) sticking)
      apply(clarsimp split!: option.split simp add: step.IH)
      done
  qed
  note this(1)[OF go]
  finally show ?thesis by(rule rel_pmf_mono)(auto elim!: option.rel_cases)
qed

end
