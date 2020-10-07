section \<open>The direct sum of modules.\<close>

theory SumSpaces
imports Main
  "HOL-Algebra.Module"
  "HOL-Algebra.Coset"
  RingModuleFacts
  MonoidSums
  FunctionLemmas
  LinearCombinations
begin

text \<open>We define the direct sum $M_1\oplus M_2$ of 2 vector spaces as the set $M_1\times M_2$ under
componentwise addition and scalar multiplication.\<close>
definition direct_sum:: "('a,'b, 'd) module_scheme \<Rightarrow> ('a, 'c, 'e) module_scheme \<Rightarrow>('a, ('b\<times>'c)) module" (*(infixl "(\<oplus>)" 50)*)
  where  "direct_sum M1 M2 = \<lparr>carrier = carrier M1 \<times> carrier M2, 
                  mult = (\<lambda> v w. (\<zero>\<^bsub>M1\<^esub>, \<zero>\<^bsub>M2\<^esub>)),
                  one =  (\<zero>\<^bsub>M1\<^esub>, \<zero>\<^bsub>M2\<^esub>),
                  zero = (\<zero>\<^bsub>M1\<^esub>, \<zero>\<^bsub>M2\<^esub>),
                  add = (\<lambda> v w. (fst v \<oplus>\<^bsub>M1\<^esub> fst w, snd v \<oplus>\<^bsub>M2\<^esub> snd w)),
                  smult = (\<lambda> c v. (c \<odot>\<^bsub>M1\<^esub> fst v, c \<odot>\<^bsub>M2\<^esub> snd v))\<rparr>"

lemma direct_sum_is_module: 
  fixes R M1 M2
  assumes h1: "module R M1" and h2: "module R M2"
  shows "module R (direct_sum M1 M2)"
proof -
  from h1 have 1: "cring R" by (unfold module_def, auto)
  from h1 interpret v1: module R M1 by auto
  from h2 interpret v2: module R M2 by auto
  from h1 h2 have 2: "abelian_group (direct_sum M1 M2)" 
    apply (intro abelian_groupI, auto)
         apply (unfold direct_sum_def, auto)
       by (auto simp add: v1.a_ac v2.a_ac)
  from h1 h2 assms have 3: "module_axioms R (direct_sum M1 M2)"
    apply (unfold module_axioms_def, auto)
        apply (unfold direct_sum_def, auto)
         by (auto simp add: v1.smult_l_distr v2.smult_l_distr v1.smult_r_distr v2.smult_r_distr
      v1.smult_assoc1 v2.smult_assoc1)
  from 1 2 3  show ?thesis by (unfold module_def, auto)
qed

definition inj1:: "('a,'b) module \<Rightarrow> ('a, 'c) module \<Rightarrow>('b\<Rightarrow>('b\<times>'c))"
  where "inj1 M1 M2 = (\<lambda>v. (v, \<zero>\<^bsub>M2\<^esub>))"

definition inj2:: "('a,'b) module \<Rightarrow> ('a, 'c) module \<Rightarrow>('c\<Rightarrow>('b\<times>'c))"
  where "inj2 M1 M2 = (\<lambda>v. (\<zero>\<^bsub>M1\<^esub>, v))"

lemma inj1_hom:
  fixes R M1 M2
  assumes h1: "module R M1" and h2: "module R M2"
  shows "mod_hom R M1 (direct_sum M1 M2) (inj1 M1 M2)"
proof - 
  from h1 interpret v1:module R M1 by auto
  from h2 interpret v2:module R M2 by auto
  from h1 h2 show ?thesis
    apply (unfold mod_hom_def module_hom_def mod_hom_axioms_def inj1_def, auto)
       apply (rule direct_sum_is_module, auto)
      by (unfold direct_sum_def, auto)
qed

lemma inj2_hom:
  fixes R M1 M2
  assumes h1: "module R M1" and h2: "module R M2"
  shows "mod_hom R M2 (direct_sum M1 M2) (inj2 M1 M2)"
proof - 
  from h1 interpret v1:module R M1 by auto
  from h2 interpret v2:module R M2 by auto
  from h1 h2 show ?thesis
    apply (unfold mod_hom_def module_hom_def mod_hom_axioms_def inj2_def, auto)
       apply (rule direct_sum_is_module, auto)
      by (unfold direct_sum_def, auto)
qed

text \<open>For submodules $M_1,M_2\subseteq M$, the map $M_1\oplus M_2\to M$ given by $(m_1,m_2)\mapsto 
m_1+m_2$ is linear.\<close>
lemma (in module) sum_map_hom: 
  fixes M1 M2
  assumes h1: "submodule R M1 M" and h2: "submodule R M2 M"
  shows "mod_hom R (direct_sum (md M1) (md M2)) M (\<lambda> v. (fst v) \<oplus>\<^bsub>M\<^esub> (snd v))"
proof - 
  have 0: "module R M"..
  from h1 have 1: "module R (md M1)" by (rule submodule_is_module)
  from h2 have 2: "module R (md M2)" by (rule submodule_is_module)
  from h1 interpret w1: module R "(md M1)" by (rule submodule_is_module)
  from h2 interpret w2: module R "(md M2)" by (rule submodule_is_module)
  from 0 h1 h2 1 2 show ?thesis
    apply (unfold mod_hom_def mod_hom_axioms_def module_hom_def, auto)
       apply (rule direct_sum_is_module, auto)
      apply (unfold direct_sum_def, auto)
      apply (unfold submodule_def, auto)
     by (auto simp add: a_ac smult_r_distr ring_subset_carrier) 
      (*key is a_ac, permutative rewrite rule*)
qed

lemma (in module) sum_is_submodule:
  fixes N1 N2
  assumes h1: "submodule R N1 M" and h2: "submodule R N2 M"
  shows "submodule R (submodule_sum N1 N2) M"
proof -
  from h1 h2 interpret l: mod_hom R "(direct_sum (md N1) (md N2))" M "(\<lambda> v. (fst v) \<oplus>\<^bsub>M\<^esub> (snd v))" 
    by (rule sum_map_hom)
  have 1: "l.im =submodule_sum N1 N2"
    apply (unfold l.im_def submodule_sum_def)
    apply (unfold direct_sum_def, auto)
    by (unfold image_def, auto)
  have 2: "submodule R (l.im) M" by (rule l.im_is_submodule)
  from 1 2 show ?thesis by auto
qed

lemma (in module) in_sum:
  fixes N1 N2
  assumes h1: "submodule R N1 M" and h2: "submodule R N2 M"
  shows "N1 \<subseteq> submodule_sum N1 N2"
proof -
  from h1 h2 show ?thesis
    apply auto
    apply (unfold submodule_sum_def image_def, auto)
    apply (rename_tac v)
    apply (rule_tac x="v" in bexI)
     apply (rule_tac x="\<zero>\<^bsub>M\<^esub>" in bexI)
      by (unfold submodule_def, auto)
qed

lemma (in module) msum_comm:
  fixes N1 N2
  assumes h1: "submodule R N1 M" and h2: "submodule R N2 M"
  shows "(submodule_sum N1 N2) = (submodule_sum N2 N1)"
proof - 
  (*have 0: "module R M"..*)
  from h1 h2 show ?thesis
    apply (unfold submodule_sum_def image_def, auto)
     apply (unfold submodule_def)
     apply (rename_tac v w)
     by (metis (full_types) M.add.m_comm subsetD)+
    (* Alternatively, apply (rule_tac x="w" in bexI, rule_tac x="v" in bexI,
      auto simp add: ring_subset_carrier M.a_ac)+ *)
qed

text \<open>If $M_1,M_2\subseteq M$ are submodules, then $M_1+M_2$ is the minimal subspace such that 
both $M_1\subseteq M$ and $M_2\subseteq M$.\<close>
lemma (in module) sum_is_minimal:
  fixes N N1 N2
  assumes h1: "submodule R N1 M" and h2: "submodule R N2 M" and h3: "submodule R N M"
  shows "(submodule_sum N1 N2) \<subseteq> N \<longleftrightarrow> N1 \<subseteq> N \<and> N2 \<subseteq> N"
proof - 
  have 1: "(submodule_sum N1 N2) \<subseteq> N \<Longrightarrow> N1 \<subseteq> N \<and> N2 \<subseteq> N"
  proof -
    assume 10: "(submodule_sum N1 N2) \<subseteq> N"
    from h1 h2 have 11: "N1\<subseteq>submodule_sum N1 N2" by (rule in_sum)
    from h2 h1 have 12: "N2\<subseteq>submodule_sum N2 N1" by (rule in_sum)
    from 12 h1 h2 have 13: "N2\<subseteq>submodule_sum N1 N2" by (metis msum_comm)
    from 10 11 13 show ?thesis by auto
  qed
  have 2: "N1 \<subseteq> N \<and> N2 \<subseteq> N \<Longrightarrow> (submodule_sum N1 N2) \<subseteq> N"
  proof -
    assume 19: "N1 \<subseteq> N \<and> N2 \<subseteq> N"
    {  
    fix v
    assume 20: "v\<in>submodule_sum N1 N2"
    from 20 obtain w1 w2 where 21: "w1\<in>N1" and 22: "w2\<in>N2" and 23: "v=w1\<oplus>\<^bsub>M\<^esub> w2" 
      by (unfold submodule_sum_def image_def, auto)
    from 19 21 22 23 h3 have "v \<in> N" 
      apply (unfold submodule_def, auto)
      by (metis (poly_guards_query)  contra_subsetD)
(*how is an obtain goal rep'd?*) 
    }
    thus ?thesis
      by (metis subset_iff)
  qed
  from 1 2 show ?thesis by metis
qed

text \<open>$\text{span} A\cup B = \text{span} A + \text{span} B$\<close>
lemma (in module) span_union_is_sum: 
  fixes A B
  assumes  h2: "A\<subseteq>carrier M" and h3: "B\<subseteq>carrier M"
  shows "span (A\<union> B) = submodule_sum (span A) (span B)"
proof-
  let ?AplusB="submodule_sum (span A) (span B)"
  from  h2 have s0: "submodule R (span A) M" by (rule span_is_submodule)
  from  h3 have s1: "submodule R (span B) M" by (rule span_is_submodule)
  from s0 have s0_1: "(span A)\<subseteq>carrier M" by (unfold submodule_def, auto)
  from s1 have s1_1: "(span B)\<subseteq>carrier M" by (unfold submodule_def, auto)
  from h2 h3 have 1: "A\<union>B\<subseteq>carrier M" by auto
  from  1 have 2: "submodule R (span (A\<union>B)) M" by (rule span_is_submodule)
  from s0 s1 have 3: "submodule R ?AplusB M" by (rule sum_is_submodule)
  have c1: "span (A\<union>B) \<subseteq> ?AplusB"
(*span(A\<union>B) \<subseteq> span(A) + span(B) *)
  proof -
    from  h2 have a1: "A\<subseteq>span A" by (rule in_own_span)
    from s0 s1 have a2: "span A \<subseteq> ?AplusB" by (rule in_sum) (*M\<subseteq>M+N*)
    from a1 a2 have a3: "A\<subseteq> ?AplusB" by auto
    (*similarly*)
    from  h3 have b1: "B\<subseteq>span B" by (rule in_own_span)
    from s1 s0 have b2: "span B \<subseteq> ?AplusB" by (metis in_sum msum_comm) (*M\<subseteq>M+N*)
    from b1 b2 have b3: "B\<subseteq> ?AplusB" by auto
    from a3 b3 have 5: "A\<union>B\<subseteq> ?AplusB" by auto
      (*by default simp *)
    from 5 3 show ?thesis by (rule span_is_subset)
  qed
  have c2: "?AplusB \<subseteq> span (A\<union>B)" 
  proof - 
    have 11: "A\<subseteq>A\<union>B" by auto
    have 12: "B\<subseteq>A\<union>B" by auto
    from  11 have 21:"span A \<subseteq>span (A\<union>B)" by (rule span_is_monotone)
    from  12 have 22:"span B \<subseteq>span (A\<union>B)" by (rule span_is_monotone)
    from s0 s1 2 21 22 show ?thesis by (auto simp add: sum_is_minimal)
  qed
  from c1 c2 show ?thesis by auto
qed

end
