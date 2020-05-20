section \<open>Simulations Between Dynamic Executions\<close>

theory Simulation
  imports Semantics Inf Well_founded
begin

locale backward_simulation =
  L1: semantics step1 final1 +
  L2: semantics step2 final2 +
  well_founded "(\<sqsubset>)"
  for
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    final1 :: "'state1 \<Rightarrow> bool" and
    final2 :: "'state2 \<Rightarrow> bool" and
    order :: "'index \<Rightarrow> 'index \<Rightarrow> bool" (infix "\<sqsubset>" 70) +
  fixes
    match :: "'index \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool"
  assumes
    match_final:
      "match i s1 s2 \<Longrightarrow> final2 s2 \<Longrightarrow> final1 s1" and
    simulation:
      "match i1 s1 s2 \<Longrightarrow> step2 s2 s2' \<Longrightarrow>
        (\<exists>i2 s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match i2 s1' s2') \<or> (\<exists>i2. match i2 s1 s2' \<and> i2 \<sqsubset> i1)"
begin

text \<open>
A simulation is defined between two @{locale semantics} L1 and L2.
A @{term match} predicate expresses that two states from L1 and L2 are equivalent.
The @{term match} predicate is also parameterized with an ordering used to avoid stuttering.
The only two assumptions of a backward simulation are that a final state in L2 will also be a final in L1,and that a step in L2 will either represent a non-empty sequence of steps in L1 or will result in an equivalent state.
Stuttering is ruled out by the requirement that the index on the @{term match} predicate decreases with respect to the well-founded @{term order} ordering.
\<close>

end


locale forward_simulation =
  L1: semantics step1 final1 +
  L2: semantics step2 final2 +
  well_founded "(\<sqsubset>)"
  for
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    final1 :: "'state1 \<Rightarrow> bool" and
    final2 :: "'state2 \<Rightarrow> bool" and
    order :: "'index \<Rightarrow> 'index \<Rightarrow> bool" (infix "\<sqsubset>" 70) +
  fixes
    match :: "'index \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool"
  assumes
    match_final:
      "match i s1 s2 \<Longrightarrow> final1 s1 \<Longrightarrow> final2 s2" and
    simulation:
      "match i1 s1 s2 \<Longrightarrow> step1 s1 s1' \<Longrightarrow>
        (\<exists>i' s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> match i' s1' s2') \<or> (\<exists>i'. match i' s1 s2' \<and> i' \<sqsubset> i1)"

locale bisimulation =
  forward_simulation step1 step2 final1 final2 order match +
  backward_simulation step1 step2 final1 final2 order match
  for
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    final1 :: "'state1 \<Rightarrow> bool" and
    final2 :: "'state2 \<Rightarrow> bool" and
    order :: "'index \<Rightarrow> 'index \<Rightarrow> bool" and
    match :: "'index \<Rightarrow> 'state1 \<Rightarrow> 'state2 \<Rightarrow> bool"

context backward_simulation begin

lemma lift_simulation_plus:
  "step2\<^sup>+\<^sup>+ s2 s2' \<Longrightarrow> match i1 s1 s2 \<Longrightarrow>
    (\<exists>i2 s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match i2 s1' s2') \<or>
    (\<exists>i2. match i2 s1 s2' \<and> order\<^sup>+\<^sup>+ i2 i1)"
  thm tranclp_induct
proof(induction s2' arbitrary: i1 s1 rule: tranclp_induct)
  case (base s2')
  from simulation[OF base.prems(1) base.hyps(1)] show ?case
    by auto
next
  case (step s2' s2'')
  show ?case
    using step.IH[OF \<open>match i1 s1 s2\<close>]
  proof
    assume "\<exists>i2 s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match i2 s1' s2'"
    then obtain i2 s1' where "step1\<^sup>+\<^sup>+ s1 s1'" and "match i2 s1' s2'" by auto
    from simulation[OF \<open>match i2 s1' s2'\<close> \<open>step2 s2' s2''\<close>] show ?thesis
    proof
      assume "\<exists>i3 s1''. step1\<^sup>+\<^sup>+ s1' s1'' \<and> match i3 s1'' s2''"
      then obtain i3 s1'' where "step1\<^sup>+\<^sup>+ s1' s1''" and "match i3 s1'' s2''" by auto
      then show ?thesis
        using tranclp_trans[OF \<open>step1\<^sup>+\<^sup>+ s1 s1'\<close>] by auto
    next
      assume "\<exists>i3. match i3 s1' s2'' \<and> i3 \<sqsubset> i2"
      then obtain i3 where "match i3 s1' s2''" and "i3 \<sqsubset> i2" by auto
      then show ?thesis
        using \<open>step1\<^sup>+\<^sup>+ s1 s1'\<close> by auto
    qed
  next
    assume "\<exists>i2. match i2 s1 s2' \<and> (\<sqsubset>)\<^sup>+\<^sup>+ i2 i1"
    then obtain i3 where "match i3 s1 s2'" and "(\<sqsubset>)\<^sup>+\<^sup>+ i3 i1" by auto
    then show ?thesis
      using simulation[OF \<open>match i3 s1 s2'\<close> \<open>step2 s2' s2''\<close>] by auto
  qed
qed

lemma lift_simulation_eval:
  "L2.eval s2 s2' \<Longrightarrow> match i1 s1 s2 \<Longrightarrow> \<exists>i2 s1'. L1.eval s1 s1' \<and> match i2 s1' s2'"
proof(induction s2 arbitrary: i1 s1 rule: converse_rtranclp_induct)
  case (base s2)
  thus ?case by auto
next
  case (step s2 s2'')
  from simulation[OF \<open>match i1 s1 s2\<close> \<open>step2 s2 s2''\<close>] show ?case
  proof
    assume "\<exists>i2 s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match i2 s1' s2''"
    thus ?thesis
      by (meson rtranclp_trans step.IH tranclp_into_rtranclp)
  next
    assume "\<exists>i2. match i2 s1 s2'' \<and> i2 \<sqsubset> i1"
    thus ?thesis
      by (auto intro: step.IH)
  qed
qed

lemma backward_simulation_inf:
  assumes
    "match i s1 s2" and
    "inf step2 s2"
  shows "inf step1 s1"
proof -
  from assms have "inf_wf step1 order i s1"
  proof (coinduction arbitrary: i s1 s2)
    case inf_wf
    obtain s2' where "step2 s2 s2'" and "inf step2 s2'"
      using inf_wf(2) by (auto elim: inf.cases)
    from simulation[OF \<open>match i s1 s2\<close> \<open>step2 s2 s2'\<close>] show ?case
      using \<open>inf step2 s2'\<close> by auto
  qed
  thus ?thesis using inf_wf_to_inf
    by (auto intro: inf_wf_to_inf well_founded_axioms)
qed

subsection \<open>Preservation of behaviour\<close>

text \<open>
The main correctness theorem states that, for any two matching programs, any not wrong behaviour of the later is also a behaviour of the former.
In other words, if the compiled program does not crash, then its behaviour, whether it terminates or not, is a also a valid behaviour of the source program.
\<close>

lemma simulation_behaviour :
  "L2.behaves s\<^sub>2 b\<^sub>2 \<Longrightarrow> \<not>is_wrong b\<^sub>2 \<Longrightarrow> match i s\<^sub>1 s\<^sub>2 \<Longrightarrow>
    \<exists>b\<^sub>1 i'. L1.behaves s\<^sub>1 b\<^sub>1 \<and> rel_behaviour (match i') b\<^sub>1 b\<^sub>2"
proof(induction rule: L2.behaves.cases)
  case (state_terminates s2 s2')
  then obtain i' s1' where "L1.eval s\<^sub>1 s1'" and "match i' s1' s2'"
    using lift_simulation_eval by blast
  hence "final1 s1'"
    by (auto intro: state_terminates.hyps match_final)
  hence "L1.behaves s\<^sub>1 (Terminates s1')"
    using L1.final_finished
    by (simp add: L1.state_terminates \<open>L1.eval s\<^sub>1 s1'\<close>)
  moreover have "rel_behaviour (match i') (Terminates s1') b\<^sub>2"
    by (simp add: \<open>match i' s1' s2'\<close> state_terminates.hyps)
  ultimately show ?case by blast
next
  case (state_diverges s2)
  then show ?case
    using backward_simulation_inf L1.state_diverges by fastforce
next
  case (state_goes_wrong s2 s2')
  then show ?case using \<open>\<not>is_wrong b\<^sub>2\<close> by simp
qed

end

subsection \<open>Composition of backward simulations\<close>

definition rel_comp ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'c \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'd) \<Rightarrow> 'b \<Rightarrow> 'e \<Rightarrow> bool" where
  "rel_comp r1 r2 i \<equiv> (r1 (fst i) OO r2 (snd i))"

lemma backward_simulation_composition:
  assumes
    "backward_simulation step1 step2 final1 final2 order1 match1"
    "backward_simulation step2 step3 final2 final3 order2 match2"
  shows
    "backward_simulation step1 step3 final1 final3
      (lex_prodp order1\<^sup>+\<^sup>+ order2) (rel_comp match1 match2)"
proof intro_locales
  show "semantics step1 final1"
    by (auto intro: backward_simulation.axioms assms)
next
  show "semantics step3 final3"
    by (auto intro: backward_simulation.axioms assms)
next
  show "well_founded (lex_prodp order1\<^sup>+\<^sup>+ order2)"
    using assms[THEN backward_simulation.axioms(3)]
    by (simp add: lex_prodp_well_founded well_founded.intro well_founded.wf wfP_trancl)
next
  show "backward_simulation_axioms step1 step3 final1 final3
    (lex_prodp order1\<^sup>+\<^sup>+ order2) (rel_comp match1 match2)"
  proof
    fix i s1 s3
    assume
      match: "rel_comp match1 match2 i s1 s3" and
      final: "final3 s3"
    obtain i1 i2 s2 where "match1 i1 s1 s2" and "match2 i2 s2 s3" and "i = (i1, i2)"
      using match unfolding rel_comp_def by auto
    thus "final1 s1"
      using final assms[THEN backward_simulation.match_final]
      by simp
  next
    fix i s1 s3 s3'
    assume
      match: "rel_comp match1 match2 i s1 s3" and
      step: "step3 s3 s3'"
    obtain i1 i2 s2 where "match1 i1 s1 s2" and "match2 i2 s2 s3" and i_def: "i = (i1, i2)"
      using match unfolding rel_comp_def by auto
    from backward_simulation.simulation[OF assms(2) \<open>match2 i2 s2 s3\<close> step]
    show "(\<exists>i' s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> rel_comp match1 match2 i' s1' s3') \<or>
       (\<exists>i'. rel_comp match1 match2 i' s1 s3' \<and> lex_prodp order1\<^sup>+\<^sup>+ order2 i' i)"
      (is "(\<exists>i' s1'. ?STEPS i' s1') \<or> ?STALL")
    proof
      assume "\<exists>i2' s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> match2 i2' s2' s3'"
      then obtain i2' s2' where "step2\<^sup>+\<^sup>+ s2 s2'" and "match2 i2' s2' s3'" by auto
      from backward_simulation.lift_simulation_plus[OF assms(1) \<open>step2\<^sup>+\<^sup>+ s2 s2'\<close> \<open>match1 i1 s1 s2\<close>]
      show ?thesis
      proof
        assume "\<exists>i2 s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match1 i2 s1' s2'"
        then obtain i2 s1' where "step1\<^sup>+\<^sup>+ s1 s1'" and "match1 i2 s1' s2'" by auto
        hence "?STEPS (i2, i2') s1'"
          by (auto intro: \<open>match2 i2' s2' s3'\<close> simp: rel_comp_def)
        thus ?thesis by auto
      next
        assume "\<exists>i2. match1 i2 s1 s2' \<and> order1\<^sup>+\<^sup>+ i2 i1"
        then obtain i2'' where "match1 i2'' s1 s2'" and "order1\<^sup>+\<^sup>+ i2'' i1" by auto
        hence ?STALL
          unfolding rel_comp_def i_def lex_prodp_def
          using \<open>match2 i2' s2' s3'\<close> by auto
        thus ?thesis by simp
      qed
    next
      assume "\<exists>i2'. match2 i2' s2 s3' \<and> order2 i2' i2"
      then obtain i2' where "match2 i2' s2 s3'" and "order2 i2' i2" by auto
      hence ?STALL
        unfolding rel_comp_def i_def lex_prodp_def
        using \<open>match1 i1 s1 s2\<close> by auto
      thus ?thesis by simp
    qed
  qed
qed

context
  fixes r :: "'i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

fun rel_comp_pow where
  "rel_comp_pow [] x y = False" |
  "rel_comp_pow [i] x y = r i x y" |
  "rel_comp_pow (i # is) x z = (\<exists>y. r i x y \<and> rel_comp_pow is y z)"

end

lemma backward_simulation_pow:
  assumes
    "backward_simulation step step final final order match"
  shows
    "backward_simulation step step final final (lexp order\<^sup>+\<^sup>+) (rel_comp_pow match)"
proof intro_locales
  show "semantics step final"
    by (auto intro: backward_simulation.axioms assms)
next
  show "well_founded (lexp order\<^sup>+\<^sup>+)"
    using backward_simulation.axioms(3)[OF assms] lex_list_well_founded
    using well_founded.intro well_founded.wf wfP_trancl by blast
next
  show "backward_simulation_axioms step step final final (lexp order\<^sup>+\<^sup>+) (rel_comp_pow match)"
  proof unfold_locales
    fix "is" s1 s2
    assume "rel_comp_pow match is s1 s2" and "final s2"
    thus "final s1" thm rel_comp_pow.induct
    proof (induction "is" s1 s2 rule: rel_comp_pow.induct)
      case (1 x y)
      then show ?case by simp
    next
      case (2 i x y)
      then show ?case
        using backward_simulation.match_final[OF assms(1)] by simp
    next
      case (3 i1 i2 "is" x z)
      from "3.prems"[simplified] obtain y where
        match: "match i1 x y" and "rel_comp_pow match (i2 # is) y z"
        by auto
      hence "final y" using "3.IH" "3.prems" by simp
      thus ?case
        using "3.prems" match backward_simulation.match_final[OF assms(1)] by auto
    qed
  next
    fix "is" s1 s3 s3'
    assume "rel_comp_pow match is s1 s3" and "step s3 s3'"
    hence "(\<exists>is' s1'. step\<^sup>+\<^sup>+ s1 s1' \<and> length is' = length is \<and> rel_comp_pow match is' s1' s3') \<or>
      (\<exists>is'. rel_comp_pow match is' s1 s3' \<and> lexp order\<^sup>+\<^sup>+ is' is)"
    proof (induction "is" s1 s3 arbitrary: s3' rule: rel_comp_pow.induct)
      case 1
      then show ?case by simp
    next
      case (2 i s1 s3)
      from backward_simulation.simulation[OF assms(1) "2.prems"[simplified]] show ?case
      proof
        assume "\<exists>i' s1'. step\<^sup>+\<^sup>+ s1 s1' \<and> match i' s1' s3'"
        then obtain i' s1' where "step\<^sup>+\<^sup>+ s1 s1'" and "match i' s1' s3'" by auto
        hence "step\<^sup>+\<^sup>+ s1 s1' \<and> rel_comp_pow match [i'] s1' s3'" by simp
        thus ?thesis
          by (metis length_Cons)
      next
        assume "\<exists>i'. match i' s1 s3' \<and> order i' i"
        then obtain i' where "match i' s1 s3'" and "order i' i" by auto
        hence "rel_comp_pow match [i'] s1 s3' \<and> lexp order\<^sup>+\<^sup>+ [i'] [i]"
          by (simp add: lexp_head tranclp.r_into_trancl)
        thus ?thesis by blast
      qed
    next
      case (3 i1 i2 "is" s1 s3)
      from "3.prems"[simplified] obtain s2 where
        "match i1 s1 s2" and 0: "rel_comp_pow match (i2 # is) s2 s3"
        by auto
      from "3.IH"[OF 0 "3.prems"(2)] show ?case
      proof
        assume "\<exists>is' s2'. step\<^sup>+\<^sup>+ s2 s2' \<and> length is' = length (i2 # is) \<and>
          rel_comp_pow match is' s2' s3'"
        then obtain i2' is' s2' where
          "step\<^sup>+\<^sup>+ s2 s2'" and "length is' = length is" and "rel_comp_pow match (i2' # is') s2' s3'"
          by (metis Suc_length_conv)
        from backward_simulation.lift_simulation_plus[OF assms(1) \<open>step\<^sup>+\<^sup>+ s2 s2'\<close> \<open>match i1 s1 s2\<close>]
        show ?thesis
        proof
          assume "\<exists>i2 s1'. step\<^sup>+\<^sup>+ s1 s1' \<and> match i2 s1' s2'"
          thus ?thesis
            using \<open>rel_comp_pow match (i2' # is') s2' s3'\<close>
            by (metis \<open>length is' = length is\<close> length_Cons rel_comp_pow.simps(3))
        next
          assume "\<exists>i2. match i2 s1 s2' \<and> order\<^sup>+\<^sup>+ i2 i1"
          then obtain i1' where "match i1' s1 s2'" and "order\<^sup>+\<^sup>+ i1' i1" by auto
          hence "rel_comp_pow match (i1' # i2' # is') s1 s3'"
            using \<open>rel_comp_pow match (i2' # is') s2' s3'\<close> by auto
          moreover have "lexp order\<^sup>+\<^sup>+ (i1' # i2' # is') (i1 # i2 # is)"
            using \<open>order\<^sup>+\<^sup>+ i1' i1\<close> \<open>length is' = length is\<close>
            by (auto intro: lexp_head)
          ultimately show ?thesis by fast
        qed
      next
        assume "\<exists>i'. rel_comp_pow match i' s2 s3' \<and> lexp order\<^sup>+\<^sup>+ i' (i2 # is)"
        then obtain i2' is' where
          "rel_comp_pow match (i2' # is') s2 s3'" and "lexp order\<^sup>+\<^sup>+ (i2' # is') (i2 # is)"
          by (metis lexp.simps)
        thus ?thesis
          by (metis \<open>match i1 s1 s2\<close> lexp.simps(1) rel_comp_pow.simps(3))
      qed
    qed
    thus "(\<exists>is' s1'. step\<^sup>+\<^sup>+ s1 s1' \<and> rel_comp_pow match is' s1' s3') \<or>
      (\<exists>is'. rel_comp_pow match is' s1 s3' \<and> lexp order\<^sup>+\<^sup>+ is' is)"
      by auto
  qed
qed

definition lockstep_backward_simulation where
  "lockstep_backward_simulation step1 step2 match \<equiv>
    \<forall>s1 s2 s2'. match s1 s2 \<longrightarrow> step2 s2 s2' \<longrightarrow> (\<exists>s1'. step1 s1 s1' \<and> match s1' s2')"

definition plus_backward_simulation where
  "plus_backward_simulation step1 step2 match \<equiv>
    \<forall>s1 s2 s2'. match s1 s2 \<longrightarrow> step2 s2 s2' \<longrightarrow> (\<exists>s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match s1' s2')"

lemma
  assumes "lockstep_backward_simulation step1 step2 match"
  shows "plus_backward_simulation step1 step2 match"
unfolding plus_backward_simulation_def
proof safe
  fix s1 s2 s2'
  assume "match s1 s2" and "step2 s2 s2'"
  then obtain s1' where "step1 s1 s1'" and "match s1' s2'"
    using assms(1) unfolding lockstep_backward_simulation_def by blast
  then show "\<exists>s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match s1' s2'"
    by auto
qed

lemma lockstep_to_plus_backward_simulation:
  fixes
    match :: "'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool"
  assumes
    lockstep_simulation: "\<And>s1 s2 s2'. match s1 s2 \<Longrightarrow> step2 s2 s2' \<Longrightarrow> (\<exists>s1'. step1 s1 s1' \<and> match s1' s2')" and
    match: "match s1 s2" and
    step: "step2 s2 s2'"
  shows "\<exists>s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match s1' s2'"
proof -
  obtain s1' where "step1 s1 s1'" and "match s1' s2'"
    using lockstep_simulation[OF match step] by auto
  thus ?thesis by auto
qed

lemma lockstep_to_option_backward_simulation:
  fixes
    match :: "'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    measure :: "'state2 \<Rightarrow> nat"
  assumes
    lockstep_simulation: "\<And>s1 s2 s2'. match s1 s2 \<Longrightarrow> step2 s2 s2' \<Longrightarrow> (\<exists>s1'. step1 s1 s1' \<and> match s1' s2')" and
    match: "match s1 s2" and
    step: "step2 s2 s2'"
  shows "(\<exists>s1'. step1 s1 s1' \<and> match s1' s2') \<or> match s1 s2' \<and> measure s2' < measure s2"
  using lockstep_simulation[OF match step] ..

lemma plus_to_star_backward_simulation:
  fixes
    match :: "'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    measure :: "'state2 \<Rightarrow> nat"
  assumes
    star_simulation: "\<And>s1 s2 s2'. match s1 s2 \<Longrightarrow> step2 s2 s2' \<Longrightarrow> (\<exists>s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match s1' s2')" and
    match: "match s1 s2" and
    step: "step2 s2 s2'"
  shows "(\<exists>s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match s1' s2') \<or> match s1 s2' \<and> measure s2' < measure s2"
  using star_simulation[OF match step] ..

lemma lockstep_to_plus_forward_simulation:
  fixes
    match :: "'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool"
  assumes
    lockstep_simulation: "\<And>s1 s2 s2'. match s1 s2 \<Longrightarrow> step1 s1 s1' \<Longrightarrow> (\<exists>s2'. step2 s2 s2' \<and> match s1' s2')" and
    match: "match s1 s2" and
    step: "step1 s1 s1'"
  shows "\<exists>s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> match s1' s2'"
proof -
  obtain s2' where "step2 s2 s2'" and "match s1' s2'"
    using lockstep_simulation[OF match step] by auto
  thus ?thesis by auto
qed

end