section \<open>Basic facts about rings and modules\<close>

theory RingModuleFacts
imports Main
  "HOL-Algebra.Module"
  "HOL-Algebra.Coset"
  (*MonoidSums*)
begin

subsection \<open>Basic facts\<close>
text \<open>In a field, every nonzero element has an inverse.\<close> (* Add to Ring.*)
lemma (in field) inverse_exists [simp, intro]: 
  assumes h1: "a\<in>carrier R"  and h2: "a\<noteq>\<zero>\<^bsub>R\<^esub>"
  shows "inv\<^bsub>R\<^esub> a\<in> carrier R"
proof - 
  have 1: "Units R = carrier R - {\<zero>\<^bsub>R\<^esub>} " by (rule field_Units)
  from h1 h2 1 show ?thesis by auto
qed

text \<open>Multiplication by 0 in $R$ gives 0. (Note that this fact encompasses smult-l-null 
as this is for module while that is for algebra, so smult-l-null is redundant.)\<close>
(*Add to Module. *)
lemma (in module) lmult_0 [simp]:
  assumes 1: "m\<in>carrier M"
  shows "\<zero>\<^bsub>R\<^esub>\<odot>\<^bsub>M\<^esub> m=\<zero>\<^bsub>M\<^esub>"
proof - 
  from 1 have 0: "\<zero>\<^bsub>R\<^esub>\<odot>\<^bsub>M\<^esub> m\<in>carrier M" by simp
  from 1 have 2: "\<zero>\<^bsub>R\<^esub>\<odot>\<^bsub>M\<^esub> m = (\<zero>\<^bsub>R\<^esub> \<oplus>\<^bsub>R\<^esub> \<zero>\<^bsub>R\<^esub>) \<odot>\<^bsub>M\<^esub> m" by simp
  from 1 have 3: "(\<zero>\<^bsub>R\<^esub> \<oplus>\<^bsub>R\<^esub> \<zero>\<^bsub>R\<^esub>) \<odot>\<^bsub>M\<^esub> m=(\<zero>\<^bsub>R\<^esub>\<odot>\<^bsub>M\<^esub> m) \<oplus>\<^bsub>M\<^esub> (\<zero>\<^bsub>R\<^esub>\<odot>\<^bsub>M\<^esub> m)"  using [[simp_trace, simp_trace_depth_limit=3]]
    by (simp add: smult_l_distr del: R.add.r_one R.add.l_one)
  from 2 3 have 4: "\<zero>\<^bsub>R\<^esub>\<odot>\<^bsub>M\<^esub> m =(\<zero>\<^bsub>R\<^esub>\<odot>\<^bsub>M\<^esub> m) \<oplus>\<^bsub>M\<^esub> (\<zero>\<^bsub>R\<^esub>\<odot>\<^bsub>M\<^esub> m)" by auto
  from 0 4 show ?thesis
    using M.l_neg M.r_neg1 by fastforce
qed

text \<open>Multiplication by 0 in $M$ gives 0.\<close> (*Add to Module.*)
lemma (in module) rmult_0 [simp]:
  assumes 0: "r\<in>carrier R"
  shows "r\<odot>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub>=\<zero>\<^bsub>M\<^esub>"
by (metis M.zero_closed R.zero_closed assms lmult_0 r_null smult_assoc1)

text \<open>Multiplication by $-1$ is the same as negation. May be useful as a simp rule.\<close>
(*Add to module.*)
lemma (in module) smult_minus_1:
  fixes v
  assumes 0:"v\<in>carrier M"
  shows "(\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<odot>\<^bsub>M\<^esub> v= (\<ominus>\<^bsub>M\<^esub>  v)"
(*(simp add: M.l_neg)*)
proof -
  from 0 have a0: "\<one>\<^bsub>R\<^esub> \<odot>\<^bsub>M\<^esub> v = v" by simp
  from 0 have 1: "((\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>)\<oplus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<odot>\<^bsub>M\<^esub> v=\<zero>\<^bsub>M\<^esub>" 
    by (simp add:R.l_neg)
  from 0 have 2: "((\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>)\<oplus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<odot>\<^bsub>M\<^esub> v=(\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>) \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub> \<one>\<^bsub>R\<^esub>\<odot>\<^bsub>M\<^esub> v"
    by (simp add: smult_l_distr)
  from 1 2 show ?thesis by (metis M.minus_equality R.add.inv_closed 
    a0 assms one_closed smult_closed) 
qed

text \<open>The version with equality reversed.\<close>
lemmas (in module)  smult_minus_1_back = smult_minus_1[THEN sym]

text\<open>-1 is not 0\<close>
lemma (in field) neg_1_not_0 [simp]: "\<ominus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub> \<noteq> \<zero>\<^bsub>R\<^esub>"
by (metis minus_minus minus_zero one_closed zero_not_one) 

text \<open>Note smult-assoc1 is the wrong way around for simplification.
This is the reverse of smult-assoc1.\<close>(*Add to Module. *)
lemma (in module) smult_assoc_simp:
"[| a \<in> carrier R; b \<in> carrier R; x \<in> carrier M |] ==>
      a \<odot>\<^bsub>M\<^esub> (b \<odot>\<^bsub>M\<^esub> x) = (a \<otimes> b) \<odot>\<^bsub>M\<^esub> x "
by (auto simp add: smult_assoc1)
  
(* Add to Ring? *)
lemmas (in abelian_group) show_r_zero= add.l_cancel_one
lemmas (in abelian_group) show_l_zero= add.r_cancel_one

text \<open>A nontrivial ring has $0\neq 1$.\<close>(*Add to Ring.*)
lemma (in ring) nontrivial_ring [simp]:
  assumes "carrier R\<noteq>{\<zero>\<^bsub>R\<^esub>}"
  shows "\<zero>\<^bsub>R\<^esub>\<noteq>\<one>\<^bsub>R\<^esub>"
proof (rule ccontr)
  assume 1: "\<not>(\<zero>\<^bsub>R\<^esub>\<noteq>\<one>\<^bsub>R\<^esub>)"
  {
    fix r
    assume 2: "r\<in>carrier R"
    from 1 2 have 3: "\<one>\<^bsub>R\<^esub>\<otimes>\<^bsub>R\<^esub> r = \<zero>\<^bsub>R\<^esub>\<otimes>\<^bsub>R\<^esub> r" by auto
    from 2 3 have "r = \<zero>\<^bsub>R\<^esub>" by auto
  }
  from this assms show False by auto
qed

text \<open>Use as simp rule. To show $a-b=0$, it suffices to show $a=b$.\<close>(*Add to Ring.*)
lemma (in abelian_group) minus_other_side [simp]:
  "\<lbrakk>a\<in>carrier G; b\<in>carrier G\<rbrakk> \<Longrightarrow> (a\<ominus>\<^bsub>G\<^esub>b = \<zero>\<^bsub>G\<^esub>) = (a=b)"
  by (metis a_minus_def add.inv_closed add.m_comm r_neg r_neg2)

subsection \<open>Units group\<close>
text \<open>Define the units group $R^{\times}$ and show it is actually a group.\<close>(* Add to Ring.*)
definition units_group::"('a,'b) ring_scheme \<Rightarrow> 'a monoid"
  where "units_group R = \<lparr>carrier = Units R, mult = (\<lambda>x y. x\<otimes>\<^bsub>R\<^esub> y), one = \<one>\<^bsub>R\<^esub>\<rparr>"

text \<open>The units form a group.\<close>(*Add to Ring.*)
lemma (in ring) units_form_group: "group (units_group R)"
  apply (intro groupI)
  apply (unfold units_group_def, auto)
  apply (intro m_assoc) 
  apply auto
  apply (unfold Units_def) 
  apply auto
  done

text \<open>The units of a \<open>cring\<close> form a commutative group.\<close>(* Add to Ring.*)
lemma (in cring) units_form_cgroup: "comm_group (units_group R)"
  apply (intro comm_groupI)
  apply (unfold units_group_def) apply auto
  apply (intro m_assoc) apply auto
  apply (unfold Units_def) apply auto
  apply (rule m_comm) apply auto
  done



end
