(*  Title:      A locale for and a characterization of maximal normal subgroups
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory MaximalNormalSubgroups
imports
  SubgroupsAndNormalSubgroups
  SimpleGroups
begin

section \<open>Facts about maximal normal subgroups\<close>

text \<open>A maximal normal subgroup of $G$ is a normal subgroup which is not contained in other any proper
  normal subgroup of $G$.\<close>

locale max_normal_subgroup = normal +
  assumes proper:"H \<noteq> carrier G"
  assumes max_normal:"\<And>J. J \<lhd> G \<Longrightarrow> J \<noteq> H \<Longrightarrow> J \<noteq> carrier G \<Longrightarrow> \<not> (H \<subseteq> J)"

text \<open>Another characterization of maximal normal subgroups: The factor group is simple.\<close>

theorem (in normal) max_normal_simple_quotient:
  assumes finite:"finite (carrier G)"
  shows "max_normal_subgroup H G = simple_group (G Mod H)"
proof
  assume "max_normal_subgroup H G"
  then interpret maxH: max_normal_subgroup H G.
  show "simple_group (G Mod H)" unfolding simple_group_def simple_group_axioms_def
  proof (intro conjI factorgroup_is_group allI impI disjCI)
    from finite factgroup_finite factorgroup_is_group group.finite_pos_order have gt0:"0 < card (rcosets H)"
      unfolding FactGroup_def order_def by force
    from maxH.proper finite have "carrier (G Mod H) \<noteq> {\<one>\<^bsub>G Mod H\<^esub>}" using fact_group_trivial_iff by auto
    hence "1 \<noteq> order (G Mod H)" using factorgroup_is_group group.order_one_triv_iff by metis
    with gt0 show "1 < order (G Mod H)" unfolding order_def FactGroup_def by auto
  next
    fix A'
    assume A'normal:"A' \<lhd> G Mod H" and A'nottriv:"A' \<noteq> {\<one>\<^bsub>G Mod H\<^esub>}"
    define A where "A = \<Union>A'"
    have A2:"A \<lhd> G" using A'normal unfolding A_def by (rule factgroup_subgroup_union_normal)
    have "H \<in> A'" using A'normal normal_imp_subgroup subgroup.one_closed unfolding FactGroup_def by force
    hence "H \<subseteq> A" unfolding A_def by auto
    hence A1:"H \<lhd> (G\<lparr>carrier := A\<rparr>)" using A2 is_normal by (metis is_subgroup maxH.max_normal normal_restrict_supergroup subgroup_self)
    have A3:"A' = rcosets\<^bsub>G\<lparr>carrier := A\<rparr>\<^esub> H"
      unfolding A_def using factgroup_subgroup_union_factor A'normal normal_imp_subgroup by auto
    from A1 interpret normalHA: normal H "(G\<lparr>carrier := A\<rparr>)" by metis
    have "H \<subseteq> A" using normalHA.is_subgroup subgroup.subset by force
    with A2 have "A = H \<or> A = carrier G" using maxH.max_normal by auto
    thus "A' = carrier (G Mod H)"
    proof 
      assume "A = H"
      hence "carrier (G\<lparr>carrier := A\<rparr> Mod H) = {\<one>\<^bsub>(G\<lparr>carrier := A\<rparr> Mod H)\<^esub>}" by (metis finite is_group normalHA.fact_group_trivial_iff normalHA.subgroup_self normalHA.subset subgroup_finite subgroup_of_restricted_group subgroup_of_subgroup subset_antisym)
      also have "... = {\<one>\<^bsub>G Mod H\<^esub>}" unfolding FactGroup_def by auto
      finally have "A' = {\<one>\<^bsub>G Mod H\<^esub>}" using A3 unfolding FactGroup_def by simp
      with A'nottriv show ?thesis..
    next
      assume "A = carrier G"
      hence "(G\<lparr>carrier := A\<rparr> Mod H) = G Mod H" by auto
      thus "A' = carrier (G Mod H)" using A3 unfolding FactGroup_def by simp
    qed
  qed
next
  assume simple:"simple_group (G Mod H)"
  show "max_normal_subgroup H G"
  proof
    from simple have "carrier (G Mod H) \<noteq> {\<one>\<^bsub>G Mod H\<^esub>}" unfolding simple_group_def simple_group_axioms_def order_def by auto
    with finite fact_group_trivial_iff show "H \<noteq> carrier G" by auto
  next
    fix A
    assume A:"A \<lhd> G" "A \<noteq> H" "A \<noteq> carrier G"
    show "\<not> H \<subseteq> A"
    proof
      assume HA:"H \<subseteq> A"
      hence "H \<lhd> (G\<lparr>carrier := A\<rparr>)" by (metis A(1) inv_op_closed2 is_subgroup normal_inv_iff normal_restrict_supergroup)
      then interpret normalHA: normal H "(G\<lparr>carrier := A\<rparr>)" by simp
      from finite have finiteA:"finite A" using A(1) normal_imp_subgroup by (metis subgroup_finite)
      have "rcosets\<^bsub>(G\<lparr>carrier := A\<rparr>)\<^esub> H \<lhd> G Mod H" using normality_factorization is_normal HA A(1) by auto
      with simple have "rcosets\<^bsub>(G\<lparr>carrier := A\<rparr>)\<^esub> H = {\<one>\<^bsub>G Mod H\<^esub>} \<or> rcosets\<^bsub>(G\<lparr>carrier := A\<rparr>)\<^esub> H = carrier (G Mod H)"
        unfolding simple_group_def simple_group_axioms_def by auto
      thus "False"
      proof
        assume "rcosets\<^bsub>G\<lparr>carrier := A\<rparr>\<^esub> H = {\<one>\<^bsub>G Mod H\<^esub>}"
        hence "rcosets\<^bsub>G\<lparr>carrier := A\<rparr>\<^esub> H = {\<one>\<^bsub>(G\<lparr>carrier := A\<rparr>) Mod H\<^esub>}" unfolding FactGroup_def by auto
        with finiteA have "H = A" using normalHA.fact_group_trivial_iff unfolding FactGroup_def by auto
        with A(2) show ?thesis by simp
      next
        assume AHGH:"rcosets\<^bsub>G\<lparr>carrier := A\<rparr>\<^esub> H = carrier (G Mod H)"
        have "A = carrier G" unfolding FactGroup_def RCOSETS_def
        proof
          show "A \<subseteq> carrier G" using A(1) normal_imp_subgroup subgroup.subset by metis
        next
          show "carrier G \<subseteq> A"
          proof
            fix x
            assume x:"x \<in> carrier G"
            hence "H #> x \<in> rcosets H" unfolding RCOSETS_def by auto
            with AHGH have "H #> x \<in> rcosets\<^bsub>G\<lparr>carrier := A\<rparr>\<^esub> H" unfolding FactGroup_def by simp
            then obtain x' where x':"x' \<in> A" "H #>x = H #>\<^bsub>G\<lparr>carrier := A\<rparr>\<^esub> x'" unfolding RCOSETS_def by auto
            hence "H #> x = H #> x'" unfolding r_coset_def by auto
            hence "x \<in> H #> x'" by (metis is_subgroup rcos_self x)
            hence "x \<in> A #> x'" using HA unfolding r_coset_def by auto
            thus "x \<in> A" using x'(1) unfolding r_coset_def using subgroup.m_closed A(1) normal_imp_subgroup by force
          qed
        qed
        with A(3) show ?thesis by simp
      qed
    qed
  qed
qed

end
