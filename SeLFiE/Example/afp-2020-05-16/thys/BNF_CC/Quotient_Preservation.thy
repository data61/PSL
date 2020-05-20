(* Author: Andreas Lochbihler, ETH Zurich
   Author: Joshua Schneider, ETH Zurich *)

section \<open>Quotient preservation\<close>

theory Quotient_Preservation imports
  Axiomatised_BNF_CC
begin

lemma G_Quotient:
  fixes T_l1 :: "'l1 \<Rightarrow> 'l1' \<Rightarrow> bool" and T_l2 :: "'l2 \<Rightarrow> 'l2' \<Rightarrow> bool"
    and tytok :: "('l1 \<times> 'l1' \<times> 'l1 \<times> 'l2 \<times> 'l2' \<times> 'l2 \<times> 'f) itself"
  assumes "Quotient R_l1 Abs_l1 Rep_l1 T_l1" and "Quotient R_l2 Abs_l2 Rep_l2 T_l2"
    and "Quotient R_co1 Abs_co1 Rep_co1 T_co1" and "Quotient R_co2 Abs_co2 Rep_co2 T_co2"
    and "Quotient R_contra1 Abs_contra1 Rep_contra1 T_contra1"
    and "Quotient R_contra2 Abs_contra2 Rep_contra2 T_contra2"
    and "rel_G_pos_distr_cond T_co1 T_co1\<inverse>\<inverse> T_co2 T_co2\<inverse>\<inverse> T_contra1 T_contra1\<inverse>\<inverse> T_contra2 T_contra2\<inverse>\<inverse>
      tytok"
  shows "Quotient (rel_G R_l1 R_l2 R_co1 R_co2 R_contra1 R_contra2)
    (map_G Abs_l1 Abs_l2 Abs_co1 Abs_co2 Rep_contra1 Rep_contra2)                             
    (map_G Rep_l1 Rep_l2 Rep_co1 Rep_co2 Abs_contra1 Abs_contra2)
    (rel_G T_l1 T_l2 T_co1 T_co2 T_contra1 T_contra2 :: (_, _, _, _, _, _, 'f) G \<Rightarrow> _)"
  unfolding Quotient_alt_def5
proof (intro conjI, goal_cases)
  case 1
  have "rel_G T_l1 T_l2 T_co1 T_co2 T_contra1 T_contra2 \<le>
    rel_G (Grp UNIV Abs_l1) (Grp UNIV Abs_l2) (Grp UNIV Abs_co1) (Grp UNIV Abs_co2)
    (Grp UNIV Rep_contra1)\<inverse>\<inverse> (Grp UNIV Rep_contra2)\<inverse>\<inverse>"
    apply (rule rel_G_mono)
         apply (rule assms(1-4)[unfolded Quotient_alt_def5, THEN conjunct1])+
     apply (rule assms(5-6)[unfolded Quotient_alt_def5, THEN conjunct2, THEN conjunct1,
          unfolded conversep_le_swap])+
    done
  also have "... = Grp UNIV (map_G Abs_l1 Abs_l2 Abs_co1 Abs_co2 Rep_contra1 Rep_contra2)"
    using rel_G_Grp_weak .
  finally show ?case .
next
  case 2
  have "Grp UNIV (map_G Rep_l1 Rep_l2 Rep_co1 Rep_co2 Abs_contra1 Abs_contra2) =
    rel_G (Grp UNIV Rep_l1) (Grp UNIV Rep_l2) (Grp UNIV Rep_co1) (Grp UNIV Rep_co2)
    (Grp UNIV Abs_contra1)\<inverse>\<inverse> (Grp UNIV Abs_contra2)\<inverse>\<inverse>"
    using rel_G_Grp_weak[symmetric] .
  also have "... \<le> rel_G T_l1\<inverse>\<inverse> T_l2\<inverse>\<inverse> T_co1\<inverse>\<inverse> T_co2\<inverse>\<inverse> T_contra1\<inverse>\<inverse> T_contra2\<inverse>\<inverse>"
    apply (rule rel_G_mono)
         apply (rule assms(1-4)[unfolded Quotient_alt_def5, THEN conjunct2, THEN conjunct1])+
     apply (simp_all)
     apply (rule assms(5-6)[unfolded Quotient_alt_def5, THEN conjunct1])+
    done
  finally show ?case by (simp add: rel_G_conversep)
next
  case 3
  show ?case
    apply (rule antisym)
     apply (rule predicate2I)
     apply (rule relcomppI)
      apply (subst map_G_id[symmetric])
      apply (erule map_G_rel_cong)
           apply (simp_all)[6]
           apply (erule assms(1-4)[THEN Quotient_equiv_abs1])+
       apply (erule assms(5-6)[THEN Quotient_rep_equiv1])+
     apply (subst rel_G_conversep[symmetric])
    subgoal for x y
      apply (subgoal_tac "map_G Abs_l1 Abs_l2 Abs_co1 Abs_co2 Rep_contra1 Rep_contra2 y =
        map_G Abs_l1 Abs_l2 Abs_co1 Abs_co2 Rep_contra1 Rep_contra2 x")
       apply (simp)
       apply (subst (3) map_G_id[symmetric])
       apply (erule map_G_rel_cong)
            apply (simp_all)
            apply (erule assms(1-4)[THEN Quotient_equiv_abs2])+
        apply (erule assms(5-6)[THEN Quotient_rep_equiv2])+
      apply (rule sym)
      apply (subst rel_G_eq[symmetric])
      apply (erule map_G_rel_cong)
           apply (erule assms(1-4)[THEN Quotient_rel_abs])+
       apply (simp, rule assms(5-6)[THEN Quotient_rep_reflp])+
      done
    apply (unfold rel_G_conversep[symmetric]
        assms(1-6)[unfolded Quotient_alt_def5, THEN conjunct2, THEN conjunct2])
    apply (rule rel_G_pos_distr)
    apply (rule assms(7))
    done
qed

end
