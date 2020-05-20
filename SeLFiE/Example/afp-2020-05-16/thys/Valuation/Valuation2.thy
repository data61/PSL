(**        Valuation2  
                            author Hidetsune Kobayashi
                            Group You Santo
                            Department of Mathematics
                            Nihon University
                            h_coba@math.cst.nihon-u.ac.jp
                            June 24, 2005
                            July 20  2007

   chapter 1. elementary properties of a valuation
     section 8. approximation(continued)
    
   **)

theory Valuation2 
imports Valuation1
begin

lemma (in Corps) OstrowskiTr8:"\<lbrakk>valuation K v; x \<in> carrier K; 
      0 < v (1\<^sub>r \<plusminus> -\<^sub>a x)\<rbrakk> \<Longrightarrow>
      0 < (v (1\<^sub>r \<plusminus> -\<^sub>a (x \<cdot>\<^sub>r ((1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x))\<^bsup>\<hyphen>K\<^esup>))))"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
apply (frule aGroup.ag_mOp_closed[of "K" "x"], assumption+,
       frule Ring.ring_one[of "K"],
       frule aGroup.ag_pOp_closed[of "K" "1\<^sub>r" " -\<^sub>a x"], assumption+, 
       frule OstrowskiTr32[of v x], assumption+)
apply (case_tac "x = 1\<^sub>r\<^bsub>K\<^esub>", simp,
       simp add:aGroup.ag_r_inv1, simp add:Ring.ring_times_x_0,
       simp add:aGroup.ag_r_zero, cut_tac val_field_1_neq_0,
       cut_tac invf_one, simp, simp add:Ring.ring_r_one,
       simp add:aGroup.ag_r_inv1, assumption+)
apply (frule aGroup.ag_pOp_closed[of K "1\<^sub>r" "x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)"], assumption+, 
       rule Ring.ring_tOp_closed, assumption+)
 apply (cut_tac invf_closed[of "1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)"])

 apply (cut_tac field_one_plus_frac3[of x], simp del:npow_suc,
        subst val_t2p[of v], assumption+)
 apply (rule aGroup.ag_pOp_closed, assumption+,
        rule aGroup.ag_mOp_closed, assumption+, rule Ring.npClose, 
        assumption+,
        thin_tac "1\<^sub>r \<plusminus> -\<^sub>a x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x))\<^bsup>\<hyphen> K\<^esup> =
        (1\<^sub>r \<plusminus> -\<^sub>a x^\<^bsup>K (Suc (Suc 0))\<^esup>) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x))\<^bsup>\<hyphen> K\<^esup>",
        subgoal_tac "1\<^sub>r \<plusminus> -\<^sub>a x^\<^bsup>K (Suc (Suc 0))\<^esup> = (1\<^sub>r \<plusminus> x) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)",
        simp del:npow_suc,
        thin_tac "1\<^sub>r \<plusminus> -\<^sub>a x^\<^bsup>K (Suc (Suc 0))\<^esup> = (1\<^sub>r \<plusminus> x) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)")
 apply (subst val_t2p[of v], assumption+,
        rule aGroup.ag_pOp_closed, assumption+,
        subst value_of_inv[of v "1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)"], assumption+)

 apply (rule contrapos_pp, simp+,
        frule Ring.ring_tOp_closed[of K x "(1\<^sub>r \<plusminus> -\<^sub>a x)"], assumption+,
        simp add:aGroup.ag_pOp_commute[of K "1\<^sub>r"],
        frule aGroup.ag_eq_diffzero[THEN sym, of K "x \<cdot>\<^sub>r (-\<^sub>a x \<plusminus> 1\<^sub>r)" "-\<^sub>a 1\<^sub>r"],
        assumption+, rule aGroup.ag_mOp_closed, assumption+)
 apply (simp add:aGroup.ag_inv_inv[of K "1\<^sub>r"],
        frule eq_elems_eq_val[of "x \<cdot>\<^sub>r (-\<^sub>a x \<plusminus> 1\<^sub>r)" "-\<^sub>a 1\<^sub>r" v],
        thin_tac "x \<cdot>\<^sub>r (-\<^sub>a x \<plusminus> 1\<^sub>r) = -\<^sub>a 1\<^sub>r",
        simp add:val_minus_eq value_of_one)
        apply (simp add:val_t2p,
               frule aadd_pos_poss[of "v x" "v (-\<^sub>a x \<plusminus> 1\<^sub>r)"], assumption+,
               simp,
               subst value_less_eq[THEN sym, of v "1\<^sub>r" "x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)"],
               assumption+,
               rule Ring.ring_tOp_closed, assumption+,
               simp add:value_of_one, subst val_t2p[of v], assumption+,
               rule aadd_pos_poss[of "v x" "v (1\<^sub>r \<plusminus> -\<^sub>a x)"], assumption+,
               simp add:value_of_one,
               cut_tac aadd_pos_poss[of "v (1\<^sub>r \<plusminus> x)" "v (1\<^sub>r \<plusminus> -\<^sub>a x)"],
               simp add:aadd_0_r, rule val_axiom4, assumption+)
  apply (subst Ring.ring_distrib2, assumption+, simp add:Ring.ring_l_one,
         subst Ring.ring_distrib1, assumption+, simp add:Ring.ring_r_one,
         subst aGroup.pOp_assocTr43, assumption+, 
         rule Ring.ring_tOp_closed, assumption+,
         simp add:aGroup.ag_l_inv1 aGroup.ag_r_zero,
        subst Ring.ring_inv1_2, assumption+, simp, assumption+)

 apply simp

apply (rule contrapos_pp, simp+,
       frule Ring.ring_tOp_closed[of K x "(1\<^sub>r \<plusminus> -\<^sub>a x)"], assumption+,
       simp add:aGroup.ag_pOp_commute[of K "1\<^sub>r"],
       frule aGroup.ag_eq_diffzero[THEN sym, of K "x \<cdot>\<^sub>r (-\<^sub>a x \<plusminus> 1\<^sub>r)" "-\<^sub>a 1\<^sub>r"],
       assumption+, rule aGroup.ag_mOp_closed, assumption+)
 apply (simp add:aGroup.ag_inv_inv[of K "1\<^sub>r"],
        frule eq_elems_eq_val[of "x \<cdot>\<^sub>r (-\<^sub>a x \<plusminus> 1\<^sub>r)" "-\<^sub>a 1\<^sub>r" v],
        thin_tac "x \<cdot>\<^sub>r (-\<^sub>a x \<plusminus> 1\<^sub>r) = -\<^sub>a 1\<^sub>r",
        simp add:val_minus_eq value_of_one,
        simp add:val_t2p,
        frule aadd_pos_poss[of "v x" "v (-\<^sub>a x \<plusminus> 1\<^sub>r)"], assumption+,
        simp)
done

lemma (in Corps) OstrowskiTr9:"\<lbrakk>valuation K v; x \<in> carrier K; 0 < (v x)\<rbrakk> \<Longrightarrow>
                 0 < (v (x \<cdot>\<^sub>r ((1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x))\<^bsup>\<hyphen>K\<^esup>)))"
apply (subgoal_tac "1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x) \<noteq> \<zero>")
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule aGroup.ag_mOp_closed[of "K" "x"], assumption+,
       frule Ring.ring_one[of "K"], 
       frule aGroup.ag_pOp_closed[of "K" "1\<^sub>r" "-\<^sub>a x"], assumption+,
       subst val_t2p, assumption+,
       cut_tac invf_closed1[of "1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)"], simp) 
apply simp
 apply (rule aGroup.ag_pOp_closed, assumption+,
        rule Ring.ring_tOp_closed, assumption+)
(* 
 apply (rule contrapos_pp, simp+,
       frule Ring.ring_tOp_closed[of K x "(1\<^sub>r \<plusminus> -\<^sub>a x)"], assumption+) apply (
       simp add:aGroup.ag_pOp_commute[of K "1\<^sub>r"],
       frule aGroup.ag_eq_diffzero[THEN sym, of K "x \<cdot>\<^sub>r (-\<^sub>a x \<plusminus> 1\<^sub>r)" "-\<^sub>a 1\<^sub>r"])
       apply (rule Ring.ring_tOp_closed, assumption+,
              rule aGroup.ag_mOp_closed, assumption+)
       apply (simp add:aGroup.ag_inv_inv)
       apply (frule eq_elems_eq_val[of "x \<cdot>\<^sub>r (-\<^sub>a x \<plusminus> 1\<^sub>r)" "-\<^sub>a 1\<^sub>r" v],
        thin_tac "x \<cdot>\<^sub>r (-\<^sub>a x \<plusminus> 1\<^sub>r) = -\<^sub>a 1\<^sub>r",
        simp add:val_minus_eq value_of_one,
        simp add:val_t2p)
        apply (simp add:aadd_commute[of "v x" "v (-\<^sub>a x \<plusminus> 1\<^sub>r)"])
       apply (cut_tac aadd_pos_poss[of "v (-\<^sub>a x \<plusminus> 1\<^sub>r)" "v x"], simp)
       apply (simp add:val_minus_eq[THEN sym, of v x])
       apply (subst aGroup.ag_pOp_commute, assumption+)
       apply (rule val_axiom4[of v "-\<^sub>a x"], assumption+)
       apply (simp add:aless_imp_le, assumption) *)
 apply (subst value_of_inv[of v "1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)"], assumption+,
        rule aGroup.ag_pOp_closed, assumption+,
               rule Ring.ring_tOp_closed, assumption+,
        frule value_less_eq[THEN sym, of v "1\<^sub>r" "-\<^sub>a x"], assumption+,
        simp add:value_of_one, simp add:val_minus_eq,
        subst value_less_eq[THEN sym, of v "1\<^sub>r" "x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)"],
           assumption+, rule Ring.ring_tOp_closed, assumption+,
           simp add:value_of_one, subst val_t2p, assumption+,
           subst aadd_commute,
       rule aadd_pos_poss[of "v (1\<^sub>r \<plusminus> -\<^sub>a x)" "v x"],
       simp, assumption, simp add:value_of_one,
       simp add:aadd_0_r)
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of K],
       frule Ring.ring_one,
       rule contrapos_pp, simp+,
       frule Ring.ring_tOp_closed[of K x "(1\<^sub>r \<plusminus> -\<^sub>a x)"], assumption+,
       rule aGroup.ag_pOp_closed, assumption+,
       rule aGroup.ag_mOp_closed, assumption+,
       frule aGroup.ag_mOp_closed[of K x], assumption+)

apply (simp add:aGroup.ag_pOp_commute[of K "1\<^sub>r"],
       frule aGroup.ag_eq_diffzero[THEN sym, of K "x \<cdot>\<^sub>r (-\<^sub>a x \<plusminus> 1\<^sub>r)" "-\<^sub>a 1\<^sub>r"],
       simp add:aGroup.ag_pOp_commute, 
       rule aGroup.ag_mOp_closed, assumption+,
       simp add:aGroup.ag_inv_inv,
       frule eq_elems_eq_val[of "x \<cdot>\<^sub>r (-\<^sub>a x \<plusminus> 1\<^sub>r)" "-\<^sub>a 1\<^sub>r" v],
        thin_tac "x \<cdot>\<^sub>r (-\<^sub>a x \<plusminus> 1\<^sub>r) = -\<^sub>a 1\<^sub>r",
        simp add:val_minus_eq value_of_one,
        frule_tac aGroup.ag_pOp_closed[of K "-\<^sub>a x" "1\<^sub>r"], assumption+,
        simp add:val_t2p)
  apply (simp add:aadd_commute[of "v x"],
         cut_tac aadd_pos_poss[of "v (-\<^sub>a x \<plusminus> 1\<^sub>r)" "v x"], simp,
         subst aGroup.ag_pOp_commute, assumption+,
         subst value_less_eq[THEN sym, of v "1\<^sub>r" "-\<^sub>a x"], assumption+,
         simp add:value_of_one val_minus_eq, simp add:value_of_one)
   
 apply assumption
done

lemma (in Corps) OstrowskiTr10:"\<lbrakk>valuation K v; x \<in> carrier K; 
       \<not> 0 \<le> v x\<rbrakk> \<Longrightarrow> 0 < (v (x \<cdot>\<^sub>r ((1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x))\<^bsup>\<hyphen>K\<^esup>)))" 
apply (frule OstrowskiTr6[of "v" "x"], assumption+,
       cut_tac invf_closed1[of "1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)"], simp,
       erule conjE, simp add:aneg_le, frule val_neg_nonzero[of "v" "x"], 
       (erule conjE)+, assumption+, erule conjE) 
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule aGroup.ag_mOp_closed[of "K" "x"], assumption+, 
       frule Ring.ring_one[of "K"],
       frule aGroup.ag_pOp_closed[of "K" "1\<^sub>r" "-\<^sub>a x"], assumption+,
       subst val_t2p, assumption+)
apply (subst value_of_inv[of "v" "1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)"],
       assumption+, subst aGroup.ag_pOp_commute[of "K" "1\<^sub>r"], assumption+,
       rule Ring.ring_tOp_closed, assumption+,
       subst value_less_eq[THEN sym, of v 
                                      "x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)" "1\<^sub>r"], assumption+)
apply (rule Ring.ring_tOp_closed, assumption+, simp add:value_of_one,
       frule one_plus_x_nonzero[of "v" "-\<^sub>a x"], assumption,
       simp add:val_minus_eq, erule conjE, simp,
       subst val_t2p[of "v"], assumption+, simp add:aadd_two_negg)

apply (simp add:val_t2p,
       frule value_less_eq[THEN sym, of "v" "-\<^sub>a x" "1\<^sub>r"], assumption+,
       simp add:value_of_one, simp add:val_minus_eq,
       simp add:val_minus_eq, simp add:aGroup.ag_pOp_commute[of "K" "-\<^sub>a x"],
       frule val_nonzero_z[of "v" "x"], assumption+, erule exE,
       simp add:a_zpz aminus, simp add:ant_0[THEN sym] aless_zless,
       assumption)
done

lemma (in Corps) Ostrowski_first:"vals_nonequiv K (Suc 0) vv
         \<Longrightarrow> \<exists>x\<in>carrier K. Ostrowski_elem K (Suc 0) vv x"  
 apply (simp add:vals_nonequiv_def,
        cut_tac Nset_Suc0, (erule conjE)+,
        simp add:valuations_def)
 apply (rotate_tac -1, 
        frule_tac a = 0 in forall_spec, simp,
        rotate_tac -1,
        drule_tac a = "Suc 0" in forall_spec, simp)
 apply (drule_tac a = "Suc 0" in forall_spec, simp,
        rotate_tac -1,
        drule_tac a = 0 in forall_spec, simp, simp)
 apply (frule_tac a = 0 in forall_spec, simp,
        drule_tac a = "Suc 0" in forall_spec, simp,
        frule_tac v = "vv 0" and v' = "vv (Suc 0)" in 
         nonequiv_ex_Ostrowski_elem, assumption+,
         erule bexE) 

 apply (erule conjE,
        frule_tac v = "vv (Suc 0)" and v' = "vv 0" in 
        nonequiv_ex_Ostrowski_elem, assumption+,
        erule bexE,
        thin_tac "\<not> v_equiv K (vv (Suc 0)) (vv 0)",
        thin_tac "\<not> v_equiv K (vv 0) (vv (Suc 0))")

 apply (rename_tac s t) (* we show s and t are non-zero in the following 4
                          lines *) 
 apply (erule conjE,
        frule_tac x = t and v = "vv 0" in val_neg_nonzero, assumption+) 
apply (simp add:less_ant_def, (erule conjE)+,
       frule_tac x = s and v = "vv (Suc 0)" in val_neg_nonzero,
       assumption+, unfold less_ant_def) 
apply (rule conjI, assumption+)  

 apply (frule_tac s = s and t = t and v = "vv 0" in OstrowskiTr2, 
        assumption+, rule ale_neq_less, assumption+)
 apply (frule_tac s = s and t = t and v = "vv (Suc 0)" in OstrowskiTr3,
         assumption+, rule ale_neq_less, assumption+) 
 apply (subgoal_tac "t \<cdot>\<^sub>r (( s \<plusminus> t)\<^bsup>\<hyphen>K\<^esup>) \<in> carrier K",
        simp only:Ostrowski_elem_def,
        simp only: nset_m_m[of "Suc 0"], blast) 
       (* Here simp add:nset_m_m[of "Suc 0"] wouldn't work *)
 apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
        rule Ring.ring_tOp_closed, assumption+,
        frule_tac s = s and t = t and v = "vv 0" in OstrowskiTr1, 
        assumption+, rule ale_neq_less, assumption+,
        frule_tac x = s and y = t in aGroup.ag_pOp_closed[of "K"], assumption+)
    apply (cut_tac x = "s \<plusminus> t" in invf_closed, blast)
    apply assumption     (* in the above two lines, simp wouldn't work *)
done

(** subsection on inequality **)

lemma (in Corps) Ostrowski:"\<forall>vv. vals_nonequiv K (Suc n) vv \<longrightarrow> 
                        (\<exists>x\<in>carrier K. Ostrowski_elem K (Suc n) vv x)" 
apply (induct_tac n,
 rule allI, rule impI, simp add:Ostrowski_first)
(** case (Suc n) **)
 apply (rule allI, rule impI,
       frule_tac n = n and vv = vv in restrict_vals_nonequiv1,
       frule_tac n = n and vv = vv in restrict_vals_nonequiv2,
       frule_tac a = "compose {h. h \<le> Suc n} vv (skip 1)" in forall_spec,
        assumption,
       drule_tac a = "compose {h. h \<le> Suc n} vv (skip 2)" in forall_spec,
         assumption+, (erule bexE)+) 
apply (rename_tac n vv s t,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
(**  case * * *  **)
 apply (frule_tac x = s and y = t in Ring.ring_tOp_closed[of "K"], assumption+,
        case_tac "0 \<le> vv (Suc 0) s \<and> 0 \<le> vv (Suc (Suc 0)) t",
        frule_tac vv = vv and s = s and t = t in OstrowskiTr5, assumption+) 
 apply blast


 (** case * * * **)
apply (simp, 
       case_tac "0 \<le> (vv (Suc 0) s)", simp,
       frule_tac n = "Suc (Suc n)" and m = "Suc (Suc 0)" and vv = vv in 
         vals_nonequiv_valuation,
       simp,
       frule_tac v = "vv (Suc (Suc 0))" and x = t in OstrowskiTr6,
         assumption+,
       frule_tac x = "1\<^sub>r \<plusminus> t \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a t)" in invf_closed1,
       frule_tac x = t and y = "(1\<^sub>r \<plusminus> t \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a t))\<^bsup>\<hyphen>K\<^esup>" in 
               Ring.ring_tOp_closed, assumption+, simp)
apply (subgoal_tac "Ostrowski_elem K (Suc (Suc n)) vv 
                       (t \<cdot>\<^sub>r ((1\<^sub>r \<plusminus> t \<cdot>\<^sub>r (1\<^sub>r \<plusminus> (-\<^sub>a t)))\<^bsup>\<hyphen>K\<^esup>))",
       blast)
apply (subst Ostrowski_elem_def,
       rule conjI,
       thin_tac "Ostrowski_elem K (Suc n)
         (compose {h. h \<le> Suc n} vv (skip (Suc 0))) s",
       thin_tac "vals_nonequiv K (Suc n)
         (compose {h. h \<le> Suc n} vv (skip (Suc 0)))",
       thin_tac "vals_nonequiv K (Suc n) (compose {h. h\<le> Suc n} vv (skip 2))",
       thin_tac "0 \<le> (vv (Suc 0) s)",
       frule_tac n = "Suc (Suc n)" and vv = vv and m = 0 in 
                      vals_nonequiv_valuation, simp,
       rule_tac v = "vv 0" and x = t in 
          OstrowskiTr8, assumption+)

apply (simp add:Ostrowski_elem_def, (erule conjE)+,
       thin_tac "\<forall>j\<in>nset (Suc 0) (Suc n).
            0 < (compose {h. h \<le> (Suc n)} vv (skip 2) j t)",
       simp add:compose_def skip_def,
       rule ballI,
       thin_tac "0 \<le> (vv (Suc 0) s)",
       thin_tac "Ostrowski_elem K (Suc n) 
                    (compose {h. h \<le> (Suc n)} vv (skip (Suc 0))) s",
       frule_tac n = "Suc (Suc n)" and vv = vv and m = j in 
                     vals_nonequiv_valuation,
       simp add:nset_def, simp add:Ostrowski_elem_def, (erule conjE)+)
 (** case * * * **)
 apply (case_tac "j = Suc 0", simp,
        drule_tac x = "Suc 0" in bspec,
        simp add:nset_def,
        simp add:compose_def skip_def,
        rule_tac v = "vv (Suc 0)" and x = t in 
         OstrowskiTr9, assumption+,
        frule_tac j = j and n = n in nset_Tr51, assumption+,
        drule_tac x = "j - Suc 0" in bspec, assumption+,
        simp add:compose_def skip_def)
 (** case * * * **) 
 apply (case_tac "j = Suc (Suc 0)", simp) apply (
       rule_tac v = "vv (Suc (Suc 0))" and x = t in OstrowskiTr10, 
       assumption+) apply (
       subgoal_tac "\<not> j - Suc 0 \<le> Suc 0", simp add:nset_def) apply(
       rule_tac v = "vv j" and x = t in 
                    OstrowskiTr9) apply (simp add:nset_def, assumption+) 
apply (simp add:nset_def, (erule conjE)+, rule nset_Tr52, assumption+,
       thin_tac "vals_nonequiv K (Suc n)
         (compose {h. h \<le> (Suc n)} vv (skip (Suc 0)))",
       thin_tac "vals_nonequiv K (Suc n) 
                   (compose {h. h \<le> (Suc n)} vv (skip 2))",
       thin_tac "Ostrowski_elem K (Suc n) 
                   (compose {h. h \<le>(Suc n)} vv (skip 2)) t")
 apply (subgoal_tac "s \<cdot>\<^sub>r ((1\<^sub>r \<plusminus> s \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a s))\<^bsup>\<hyphen>K\<^esup>) \<in> carrier K",
        subgoal_tac "Ostrowski_elem K (Suc (Suc n)) vv 
                            (s \<cdot>\<^sub>r ((1\<^sub>r \<plusminus> s \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a s))\<^bsup>\<hyphen>K\<^esup>))", blast)
 prefer 2
 apply (frule_tac n = "Suc (Suc n)" and m = "Suc 0" and vv = vv in 
        vals_nonequiv_valuation, simp,
     frule_tac v = "vv (Suc 0)" and x = s in OstrowskiTr6, assumption+,
     rule Ring.ring_tOp_closed, assumption+,
     frule_tac x = "1\<^sub>r \<plusminus> s \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a s)" in invf_closed1, simp,
     simp add:Ostrowski_elem_def)
apply (rule conjI)
apply (rule_tac v = "vv 0" and x = s in OstrowskiTr8,
       simp add:vals_nonequiv_valuation, assumption+) 
       apply (
       thin_tac "vals_nonequiv K (Suc (Suc n)) vv",
       (erule conjE)+,
       thin_tac "\<forall>j\<in>nset (Suc 0) (Suc n).
            0 < (compose {h. h \<le> (Suc n)} vv (skip (Suc 0)) j s)",
       simp add:compose_def skip_def,  rule ballI)
 (** case *** *** **)
 apply (case_tac "j = Suc 0", simp,
     rule_tac v = "vv (Suc 0)" and x = s in OstrowskiTr10,
     simp add:vals_nonequiv_valuation, assumption+,
     rule_tac v = "vv j" and x = s in OstrowskiTr9,
     simp add:vals_nonequiv_valuation nset_def, assumption,
     (erule conjE)+, simp add:compose_def skip_def,
     frule_tac j = j in nset_Tr51, assumption+,
     drule_tac x = "j - Suc 0" in bspec, assumption+)
 apply (simp add:nset_def)
done

lemma (in Corps) val_1_nonzero:"\<lbrakk>valuation K v; x \<in> carrier K; v x = 1\<rbrakk> \<Longrightarrow>
                               x \<noteq> \<zero>"
apply (rule contrapos_pp, simp+,
       simp add:value_of_zero,
       rotate_tac 3, drule sym, simp only:ant_1[THEN sym],
       simp del:ant_1)
done

lemma (in Corps) Approximation1_5Tr1:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
 n_val K (vv 0) = vv 0; a \<in> carrier K; vv 0 a = 1; x \<in> carrier K; 
 Ostrowski_elem K (Suc n) vv x\<rbrakk>  \<Longrightarrow> 
        \<forall>m. 2 \<le> m \<longrightarrow> vv 0 ((1\<^sub>r \<plusminus> -\<^sub>a x)^\<^bsup>K m\<^esup> \<plusminus> a \<cdot>\<^sub>r (x^\<^bsup>K m\<^esup>)) = 1" 
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule Ring.ring_one[of "K"],
       rule allI, rule impI,
       frule vals_nonequiv_valuation[of "Suc n" "vv" "0"],
       simp,
       simp add:Ostrowski_elem_def, frule conjunct1, fold Ostrowski_elem_def,
       frule val_1_nonzero[of "vv 0" "a"], assumption+)
apply (frule vals_nonequiv_valuation[of "Suc n" "vv" "0"], simp,
       frule val_nonzero_noninf[of "vv 0" "a"], assumption+,
       frule val_unit_cond[of "vv 0" "x"], assumption+,
       frule_tac n = m in Ring.npClose[of "K" "x"], assumption+,
       frule aGroup.ag_mOp_closed[of "K" "x"], assumption+,
       frule aGroup.ag_pOp_closed[of "K" "1\<^sub>r" "-\<^sub>a x"], assumption+) 
apply (subgoal_tac "0 < m",
       frule_tac x = "a \<cdot>\<^sub>r (x^\<^bsup>K m\<^esup>)" and y = "(1\<^sub>r \<plusminus> -\<^sub>a x)^\<^bsup>K m\<^esup>" in 
       value_less_eq[of "vv 0"],
       rule Ring.ring_tOp_closed, assumption+,
       rule Ring.npClose, assumption+, simp add: val_t2p,
       frule value_zero_nonzero[of "vv 0" "x"], assumption+,
       simp add:val_exp_ring[THEN sym], simp add:asprod_n_0 aadd_0_r) 
apply (case_tac "x = 1\<^sub>r\<^bsub>K\<^esub>", simp add:aGroup.ag_r_inv1,
       frule_tac n = m in Ring.npZero_sub[of "K"], simp,
       simp add:value_of_zero) 
apply (cut_tac inf_ge_any[of "1"], simp add: less_le)
apply (rotate_tac -1, drule not_sym,
      frule aGroup.ag_neq_diffnonzero[of "K" "1\<^sub>r" "x"],
      simp add:Ring.ring_one[of "K"], assumption+, simp,
      simp add:val_exp_ring[THEN sym],
      cut_tac n1 = m in of_nat_0_less_iff[THEN sym]) 
apply (cut_tac a = "0 < m" and b = "0 < int m" in a_b_exchange, simp,
       assumption)
apply (thin_tac "(0 < m) = (0 < int m)",
      frule val_nonzero_z[of "vv 0" "1\<^sub>r \<plusminus> -\<^sub>a x"], assumption+,
      erule exE, simp, simp add:asprod_amult a_z_z,
      simp only:ant_1[THEN sym], simp only:aless_zless, simp add:ge2_zmult_pos)

apply (subst aGroup.ag_pOp_commute[of "K"], assumption+,
       rule Ring.npClose, assumption+, rule Ring.ring_tOp_closed[of "K"], 
       assumption+,
       rotate_tac -1, drule sym, simp,
       thin_tac "vv 0 (a \<cdot>\<^sub>r x^\<^bsup>K m\<^esup> \<plusminus> (1\<^sub>r \<plusminus> -\<^sub>a x)^\<^bsup>K m\<^esup>) = vv 0 (a \<cdot>\<^sub>r x^\<^bsup>K m\<^esup>)") 
apply (simp add:val_t2p,
       frule value_zero_nonzero[of "vv 0" "x"], assumption+,
       simp add:val_exp_ring[THEN sym], simp add:asprod_n_0,
       simp add:aadd_0_r,
       cut_tac z = m in less_le_trans[of "0" "2"], simp, assumption+)
done

lemma (in Corps) Approximation1_5Tr3:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
      x \<in> carrier K; Ostrowski_elem K (Suc n) vv x; j \<in> nset (Suc 0) (Suc n)\<rbrakk>
        \<Longrightarrow>  vv j ((1\<^sub>r \<plusminus> -\<^sub>a x)^\<^bsup>K m\<^esup>) = 0"
apply (frule Ostrowski_elem_not_one[of "n" "vv" "x"], assumption+,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule Ring.ring_one[of "K"],
       frule aGroup.ag_pOp_closed[of "K" "1\<^sub>r" "-\<^sub>a x"], assumption+)
apply (simp add:aGroup.ag_mOp_closed, simp add:nset_def,
       frule_tac m = j in vals_nonequiv_valuation[of "Suc n" "vv"],
       simp,
       frule_tac v1 = "vv j" and x1 = "1\<^sub>r \<plusminus> -\<^sub>a x" and n1 = m in 
        val_exp_ring[THEN sym], assumption+) 

apply (frule_tac v = "vv j" and x = "1\<^sub>r" and  y = "-\<^sub>a x" in 
       value_less_eq, assumption+, simp add:aGroup.ag_mOp_closed) 
 apply(simp add:value_of_one, simp add:val_minus_eq,
       simp add:Ostrowski_elem_def nset_def)
apply (simp add:value_of_one, rotate_tac -1, drule sym,
       simp add:asprod_n_0)
done

lemma (in Corps) Approximation1_5Tr4:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
     aa \<in> carrier K; x \<in> carrier K;
     Ostrowski_elem K (Suc n) vv x; j \<le> (Suc n)\<rbrakk> \<Longrightarrow>
     vv j (aa \<cdot>\<^sub>r (x^\<^bsup>K m\<^esup>)) = vv j aa + (int m) *\<^sub>a (vv j  x)"
apply (frule Ostrowski_elem_nonzero[of "n" "vv" "x"],
                                          assumption+,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
apply (frule_tac m = j in vals_nonequiv_valuation[of "Suc n" "vv"], assumption)
apply (subst val_t2p[of "vv j"], assumption+,
       rule Ring.npClose, assumption+,
       cut_tac field_is_idom,
       frule_tac v1 = "vv j" and x1 = x and n1 = m in 
       val_exp_ring[THEN sym], assumption+, simp)
done

lemma (in Corps) Approximation1_5Tr5:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
     a \<in> carrier K; a \<noteq> \<zero>; x \<in> carrier K;
     Ostrowski_elem K (Suc n) vv x; j \<in> nset (Suc 0) (Suc n)\<rbrakk> \<Longrightarrow>
               \<exists>l. \<forall>m. l < m \<longrightarrow> 0 < (vv j (a \<cdot>\<^sub>r (x^\<^bsup>K m\<^esup>)))"
apply (frule Ostrowski_elem_nonzero[of "n" "vv" "x"], assumption+,
      subgoal_tac "\<forall>n. vv j (a \<cdot>\<^sub>r (x^\<^bsup>K n\<^esup>)) = vv j a + (int n) *\<^sub>a (vv j  x)",
      simp,
      thin_tac "\<forall>n. vv j (a \<cdot>\<^sub>r x^\<^bsup>K n\<^esup>) = vv j a + int n *\<^sub>a vv j x")
prefer 2
apply (rule allI, rule Approximation1_5Tr4[of _ vv a x j],
         assumption+, simp add:nset_def)
apply (frule_tac m = j in vals_nonequiv_valuation[of "Suc n" "vv"], 
       simp add:nset_def,
       frule val_nonzero_z[of "vv j" "a"], assumption+, erule exE,
       simp add:Ostrowski_elem_def,
       frule conjunct2, fold Ostrowski_elem_def,
       drule_tac x = j in bspec, assumption) 
apply (frule Ostrowski_elem_nonzero[of "n" "vv" "x"], assumption+,
       frule val_nonzero_z[of "vv j" "x"], assumption+, erule exE, simp,
       frule_tac a = za and x = z in zmult_pos_bignumTr,
       simp add:asprod_amult a_z_z a_zpz)
done  

lemma (in Corps) Approximation1_5Tr6:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
      a \<in> carrier K; a \<noteq> \<zero>; x \<in> carrier K;
      Ostrowski_elem K (Suc n) vv x; j \<in> nset (Suc 0) (Suc n)\<rbrakk> \<Longrightarrow>
        \<exists>l. \<forall>m. l < m \<longrightarrow> vv j ((1\<^sub>r \<plusminus> -\<^sub>a x)^\<^bsup>K m\<^esup> \<plusminus> a \<cdot>\<^sub>r (x^\<^bsup>K m\<^esup>)) = 0" 
apply (frule vals_nonequiv_valuation[of "Suc n" "vv" "j"], 
       simp add:nset_def, 
       frule Approximation1_5Tr5[of "n" "vv" "a" "x" "j"],
               assumption+, erule exE,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       subgoal_tac "\<forall>m. l < m \<longrightarrow> vv j ((1\<^sub>r \<plusminus> -\<^sub>a x)^\<^bsup>K m\<^esup> \<plusminus> a \<cdot>\<^sub>r (x^\<^bsup>K m\<^esup>)) = 
       vv j ((1\<^sub>r \<plusminus> -\<^sub>a x)^\<^bsup>K m\<^esup>)")
 apply (simp add:Approximation1_5Tr3, blast)
 apply (rule allI, rule impI, 
        drule_tac a = m in forall_spec, assumption,
        frule_tac x = "(1\<^sub>r \<plusminus> -\<^sub>a x)^\<^bsup>K m\<^esup>" and y = "a \<cdot>\<^sub>r (x^\<^bsup>K m\<^esup>)" in 
           value_less_eq[of "vv j"],
        rule Ring.npClose, assumption+,
        rule aGroup.ag_pOp_closed, assumption+, simp add:Ring.ring_one,
        simp add:aGroup.ag_mOp_closed)
 apply (rule Ring.ring_tOp_closed, assumption+,
        rule Ring.npClose, assumption+,
        simp add:Approximation1_5Tr3,
        frule sym, assumption)
done 

lemma (in Corps) Approximation1_5Tr7:"\<lbrakk>a \<in> carrier K; vv 0 a = 1; 
      x \<in> carrier K\<rbrakk> \<Longrightarrow> 
      vals_nonequiv K (Suc n) vv  \<and> Ostrowski_elem K (Suc n) vv x \<longrightarrow> 
      (\<exists>l. \<forall>m. l < m \<longrightarrow> (\<forall>j\<in>nset (Suc 0) (Suc n). 
                (vv j ((1\<^sub>r \<plusminus> -\<^sub>a x)^\<^bsup>K m\<^esup> \<plusminus> a \<cdot>\<^sub>r (x^\<^bsup>K m\<^esup>)) = 0)))"
apply (induct_tac n,
       rule impI, erule conjE, simp add:nset_m_m[of "Suc 0"],
       frule vals_nonequiv_valuation[of "Suc 0" "vv" "Suc 0"], simp,
       frule Approximation1_5Tr6[of "0" "vv" "a" "x" "Suc 0"], assumption+) 
apply (frule vals_nonequiv_valuation[of "Suc 0" "vv" "0"], simp,
       frule val_1_nonzero[of "vv 0" "a"], assumption+, simp add:nset_def,
       assumption)
(** case n **) 
apply (rule impI, erule conjE,
       frule_tac n = n in  restrict_vals_nonequiv[of _ "vv"],
       frule_tac n = n in restrict_Ostrowski_elem[of "x"  _ "vv"],
          assumption, simp,
       erule exE,
       frule_tac n = "Suc n" and j = "Suc (Suc n)" in Approximation1_5Tr6 
        [of _ "vv" "a" "x"], assumption+,
       frule_tac n = "Suc (Suc n)" in vals_nonequiv_valuation[of _ "vv" 
        "0"],simp,
       rule val_1_nonzero[of "vv 0" "a"], assumption+,
       simp add:nset_def)
apply (erule exE,
       subgoal_tac "\<forall>m. (max l la) < m \<longrightarrow> (\<forall>j\<in>nset (Suc 0) (Suc (Suc n)).
         vv j ((1\<^sub>r \<plusminus> -\<^sub>a x)^\<^bsup>K m\<^esup> \<plusminus> a \<cdot>\<^sub>r (x^\<^bsup>K m\<^esup>)) = 0)",
       blast,
      simp add:nset_Suc)
done   

lemma (in Corps) Approximation1_5P:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
    n_val K (vv 0) = vv 0\<rbrakk> \<Longrightarrow> 
    \<exists>x\<in>carrier K. ((vv 0 x = 1) \<and> (\<forall>j\<in>nset (Suc 0) (Suc n). (vv j x) = 0))"
apply (frule vals_nonequiv_valuation[of "Suc n" "vv" "0"], simp) apply (
       frule n_val_surj[of "vv 0"], erule bexE) apply ( 
       rename_tac aa) apply ( 
       cut_tac n = n in Ostrowski) apply (
       drule_tac a = vv in forall_spec[of "vals_nonequiv K (Suc n)"], simp)
  apply (
       erule bexE,
       frule_tac a = aa and x = x in Approximation1_5Tr1[of "n" "vv"], 
       assumption+,
       simp, assumption+)
apply (frule_tac a = aa and x = x in Approximation1_5Tr7[of _ "vv" _ "n"],
       simp, assumption,
       simp, erule exE,
       cut_tac b = "Suc l" in max.cobounded1[of "2"],
       cut_tac b = "Suc l" in max.cobounded2[of _ "2"],
       cut_tac n = l in lessI,
       frule_tac x = l and y = "Suc l" and z = "max 2 (Suc l)" in 
         less_le_trans, assumption+,
       thin_tac "Suc l \<le> max 2 (Suc l)", thin_tac "l < Suc l",
       drule_tac a = "max 2 (Suc l)" in forall_spec, simp,
       drule_tac a = "max 2 (Suc l)" in forall_spec, assumption) 
 apply (subgoal_tac "(1\<^sub>r \<plusminus> -\<^sub>a x)^\<^bsup>K (max 2 (Suc l))\<^esup> \<plusminus> aa \<cdot>\<^sub>r (x^\<^bsup>K (max 2 (Suc l))\<^esup>) \<in> 
       carrier K",
       blast,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       rule aGroup.ag_pOp_closed, assumption+, rule Ring.npClose, assumption+,
       rule aGroup.ag_pOp_closed, assumption+, simp add:Ring.ring_one,
       simp add:aGroup.ag_mOp_closed, rule Ring.ring_tOp_closed, assumption+,
       rule Ring.npClose, assumption+)
done

lemma K_gamma_hom:"k \<le> n \<Longrightarrow> \<forall>j \<le> n. (\<lambda>l. \<gamma>\<^bsub>k l\<^esub>) j \<in> Zset"
apply (simp add:Zset_def) 
done

lemma transpos_eq:"(\<tau>\<^bsub>0 0\<^esub>) k = k"
by (simp add:transpos_def)

lemma (in Corps) transpos_vals_nonequiv:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
      j \<le> (Suc n)\<rbrakk> \<Longrightarrow> vals_nonequiv K (Suc n) (vv \<circ> (\<tau>\<^bsub>0 j\<^esub>))"
apply (simp add:vals_nonequiv_def)
 apply (frule conjunct1, fold vals_nonequiv_def)
 apply (simp add:valuations_def, rule conjI)
 apply (rule allI, rule impI) 
 apply (case_tac "ja = 0", simp,
        case_tac "j = 0", simp add:transpos_eq)
 apply (subst transpos_ij_1[of "0" "Suc n" "j"], simp, assumption+,
        rule not_sym, assumption, simp)

 apply (case_tac "ja = j", simp) 
 apply (subst transpos_ij_2[of "0" "Suc n" "j"], simp, assumption, simp,
        simp add:vals_nonequiv_valuation)
 apply (case_tac "j = 0", simp add:transpos_eq) 
 apply (cut_tac x = ja in transpos_id_1[of 0 "Suc n" j], simp, assumption+,
        rule not_sym, assumption+)
 apply (simp add:vals_nonequiv_valuation,
        (rule allI, rule impI)+, rule impI)
 apply (case_tac "j = 0", simp add:transpos_eq,
        simp add:vals_nonequiv_def,
        cut_tac transpos_inj[of "0" "Suc n" "j"], simp) 
 apply (frule_tac x = ja and y = l in injective[of "transpos 0 j" 
                       "{j. j \<le> (Suc n)}"], simp, simp, assumption+)
 apply (cut_tac l = ja in transpos_mem[of "0" "Suc n" "j"], simp, assumption+,
        simp, assumption,
       cut_tac l = l in transpos_mem[of "0" "Suc n" "j"], simp, assumption+,
        simp, assumption) 
 apply (simp add:vals_nonequiv_def,
        simp, assumption, rule not_sym, assumption)
done

definition
  Ostrowski_base :: "[_, nat \<Rightarrow> 'b \<Rightarrow> ant, nat] \<Rightarrow> (nat \<Rightarrow> 'b)"
                             ("(\<Omega>\<^bsub>_ _ _\<^esub>)" [90,90,91]90) where
  "Ostrowski_base K vv n = (\<lambda>j\<in>{h. h \<le> n}. (SOME x. x\<in>carrier K \<and>
                            (Ostrowski_elem K n (vv \<circ> (\<tau>\<^bsub>0 j\<^esub>)) x)))"

definition
  App_base :: "[_, nat \<Rightarrow> 'b \<Rightarrow> ant, nat] \<Rightarrow> (nat \<Rightarrow> 'b)" where
  "App_base K vv n = (\<lambda>j\<in>{h. h \<le> n}. (SOME x. x\<in>carrier K \<and> (((vv \<circ> \<tau>\<^bsub>0 j\<^esub>) 0 x 
                      = 1) \<and> (\<forall>k\<in>nset (Suc 0) n. ((vv \<circ> \<tau>\<^bsub>0 j\<^esub>) k x) = 0))))"
  (* Approximation base. *)

lemma (in Corps) Ostrowski_base_hom:"vals_nonequiv K (Suc n) vv \<Longrightarrow> 
      Ostrowski_base K vv (Suc n) \<in> {h. h \<le> (Suc n)} \<rightarrow> carrier K"
apply (rule Pi_I, rename_tac l,
       simp add:Ostrowski_base_def,
       frule_tac j = l in transpos_vals_nonequiv[of n vv], simp,
       cut_tac Ostrowski[of n]) 
apply (drule_tac a = "vv \<circ> \<tau>\<^bsub>0 l\<^esub>" in forall_spec, simp,
       rule someI2_ex, blast, simp)
done

lemma (in Corps) Ostrowski_base_mem:"vals_nonequiv K (Suc n) vv \<Longrightarrow> 
         \<forall>j \<le> (Suc n). Ostrowski_base K vv (Suc n) j \<in> carrier K"
by (rule allI, rule impI,
       frule Ostrowski_base_hom[of "n" "vv"],
       simp add:funcset_mem del:Pi_I')

lemma (in Corps)  Ostrowski_base_mem_1:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
       j \<le> (Suc n)\<rbrakk> \<Longrightarrow> Ostrowski_base K vv (Suc n) j \<in> carrier K"
by (simp add:Ostrowski_base_mem)

lemma (in Corps) Ostrowski_base_nonzero:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
       j \<le> Suc n\<rbrakk>  \<Longrightarrow> (\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j \<noteq> \<zero>"
apply (simp add:Ostrowski_base_def,
       frule_tac j = j in transpos_vals_nonequiv[of "n" "vv"],
                      assumption+,
       cut_tac Ostrowski[of "n"],
       drule_tac a = "vv \<circ> \<tau>\<^bsub>0 j\<^esub>" in forall_spec, assumption,
       rule someI2_ex, blast) 
apply (thin_tac "\<exists>x\<in>carrier K. Ostrowski_elem K (Suc n) (vv \<circ> \<tau>\<^bsub>0 j\<^esub>) x",
       erule conjE)
apply (rule_tac vv = "vv \<circ> \<tau>\<^bsub>0 j\<^esub>" and x = x in Ostrowski_elem_nonzero[of "n"],
       assumption+)
done

lemma (in Corps) Ostrowski_base_pos:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
      j \<le> Suc n; ja \<le> Suc n; ja \<noteq> j\<rbrakk> \<Longrightarrow> 0 < ((vv j) ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) ja))"
apply (simp add:Ostrowski_base_def,
       frule_tac j = ja in transpos_vals_nonequiv[of "n" "vv"],
       assumption+,
       cut_tac Ostrowski[of "n"],
       drule_tac a = "vv \<circ> \<tau>\<^bsub>0 ja\<^esub>" in forall_spec, assumption+) 
apply (rule someI2_ex, blast,
       thin_tac "\<exists>x\<in>carrier K. Ostrowski_elem K (Suc n) (vv \<circ> \<tau>\<^bsub>0 ja\<^esub>) x",
       simp add:Ostrowski_elem_def, (erule conjE)+)
apply (case_tac "ja = 0", simp, cut_tac transpos_eq[of "j"],
       simp add:nset_def, frule Suc_leI[of "0" "j"],
       frule_tac a = j in forall_spec, simp, simp)
apply (case_tac "j = 0", simp,
       frule_tac x = ja in bspec, simp add:nset_def,
       cut_tac  transpos_ij_2[of "0" "Suc n" "ja"], simp, simp+) 
apply (frule_tac x = j in bspec, simp add:nset_def,
       cut_tac transpos_id[of "0" "Suc n" "ja" "j"], simp+) 
done

lemma (in Corps) App_base_hom:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
      \<forall>j \<le> (Suc n). n_val K (vv j) = vv j\<rbrakk> \<Longrightarrow>
        \<forall>j \<le> (Suc n). App_base K vv (Suc n) j \<in> carrier K"
apply (rule allI, rule impI,
       rename_tac k,
       subst App_base_def)
 apply (case_tac "k = 0", simp, simp add:transpos_eq,
        frule Approximation1_5P[of "n" "vv"], simp,
        rule someI2_ex, blast, simp)
 apply (frule_tac j = k in transpos_vals_nonequiv[of "n" "vv"],
                 simp add:nset_def,
        frule_tac vv = "vv \<circ> \<tau>\<^bsub>0 k\<^esub>" in Approximation1_5P[of "n"])
 apply (simp add:cmp_def, subst transpos_ij_1[of "0" "Suc n"], simp+,
        subst transpos_ij_1[of 0 "Suc n" k], simp+)
 apply (rule someI2_ex, blast, simp)
done

lemma (in Corps) Approzimation1_5P2:"\<lbrakk>vals_nonequiv K (Suc n) vv;
           \<forall>l\<in>{h. h \<le> Suc n}. n_val K (vv l) = vv l; i \<le> Suc n; j \<le> Suc n\<rbrakk>
          \<Longrightarrow> vv i (App_base K vv (Suc n) j) = \<delta>\<^bsub>i j\<^esub> "
apply (simp add:App_base_def) 
apply (case_tac "j = 0", simp add:transpos_eq,
       rule someI2_ex,
       frule Approximation1_5P[of "n" "vv"], simp , blast,
       simp add:Kronecker_delta_def, rule impI, (erule conjE)+,
       frule_tac x = i in bspec, simp add:nset_def, assumption) 

apply (frule_tac j = j in transpos_vals_nonequiv[of "n" "vv"], simp,
       frule Approximation1_5P[of "n" "vv \<circ> \<tau>\<^bsub>0 j\<^esub>"],
       simp add:cmp_def, simp add:transpos_ij_1[of 0 "Suc n" j])
       
apply (simp add:cmp_def,
         case_tac "i = 0", simp add:transpos_eq,
         simp add:transpos_ij_1, simp add:Kronecker_delta_def,
         rule someI2_ex, blast,
         thin_tac "\<exists>x\<in>carrier K.
            vv j x = 1 \<and> (\<forall>ja\<in>nset (Suc 0) (Suc n). vv ((\<tau>\<^bsub>0 j\<^esub>) ja) x = 0)",
        (erule conjE)+,
         drule_tac x = j in bspec, simp add:nset_def,
         simp add:transpos_ij_2)

apply (simp add:Kronecker_delta_def,
       case_tac "i = j", simp add:transpos_ij_1, rule someI2_ex, blast, simp)

apply (simp, rule someI2_ex, blast,
       thin_tac "\<exists>x\<in>carrier K. vv ((\<tau>\<^bsub>0 j\<^esub>) 0) x = 1 \<and> 
                     (\<forall>ja\<in>nset (Suc 0) (Suc n). vv ((\<tau>\<^bsub>0 j\<^esub>) ja) x = 0)",
       (erule conjE)+,
       drule_tac x = i in bspec, simp add:nset_def,
       cut_tac transpos_id[of 0 "Suc n" j i], simp+)
done

(*
lemma (in Corps) Approximation1_5:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
  \<forall>j \<le> (Suc n)}. n_val K (vv j) = vv j\<rbrakk> \<Longrightarrow>
  \<exists>x\<in>{h. h \<le> (Suc n)} \<rightarrow> carrier K. \<forall>i \<le> (Suc n). \<forall>j \<le> (Suc n). 
                              ((vv i)  (x j) = \<delta>\<^bsub>i j\<^esub>)" *)

lemma (in Corps) Approximation1_5:"\<lbrakk>vals_nonequiv K (Suc n) vv;
  \<forall>j \<le> (Suc n). n_val K (vv j) = vv j\<rbrakk> \<Longrightarrow>
  \<exists>x. (\<forall>j \<le> (Suc n). x j \<in> carrier K) \<and> (\<forall>i \<le> (Suc n). \<forall>j \<le> (Suc n). 
                              ((vv i)  (x j) = \<delta>\<^bsub>i j\<^esub>))" 
apply (frule App_base_hom[of n vv], rule allI, simp)
 apply (subgoal_tac "(\<forall>i \<le> (Suc n). \<forall>j \<le> (Suc n). 
                 (vv i) ((App_base K vv (Suc n)) j)  = (\<delta>\<^bsub>i j\<^esub>))",
        blast) 
 apply (rule allI, rule impI)+ 
 apply (rule Approzimation1_5P2, assumption+, simp+) 
done

lemma (in Corps) Ostrowski_baseTr0:"\<lbrakk>vals_nonequiv K (Suc n) vv; l \<le> (Suc n) \<rbrakk>
   \<Longrightarrow>   0 < ((vv l) (1\<^sub>r \<plusminus> -\<^sub>a (Ostrowski_base K vv (Suc n) l))) \<and>
  (\<forall>m\<in>{h. h \<le> (Suc n)} - {l}. 0 < ((vv m) (Ostrowski_base K vv (Suc n) l)))"
apply (simp add:Ostrowski_base_def,
       frule_tac j = l in transpos_vals_nonequiv[of "n" "vv"], assumption,
       cut_tac Ostrowski[of "n"],
       drule_tac a = "vv \<circ> \<tau>\<^bsub>0 l\<^esub>" in forall_spec, assumption) 
apply (erule bexE,
       unfold Ostrowski_elem_def, frule conjunct1,
       fold Ostrowski_elem_def, 
       rule conjI, simp add:Ostrowski_elem_def)
apply (case_tac "l = 0", simp, simp add:transpos_eq,
       rule someI2_ex, blast, simp,
       simp add:transpos_ij_1,
       rule someI2_ex, blast, simp)

apply (simp add:Ostrowski_elem_def,
       case_tac "l = 0", simp, simp add:transpos_eq,
       rule someI2_ex, blast,
       thin_tac "0 < vv 0 (1\<^sub>r \<plusminus> -\<^sub>a x) \<and> 
                      (\<forall>j\<in>nset (Suc 0) (Suc n). 0 < vv j x)",
       rule ballI, simp add:nset_def) 

apply (rule ballI, erule conjE,
       rule someI2_ex, blast,
       thin_tac "\<forall>j\<in>nset (Suc 0) (Suc n). 0 < vv ((\<tau>\<^bsub>0 l\<^esub>) j) x",
       (erule conjE)+)

apply (case_tac "m = 0", simp,
       drule_tac x = l in bspec, simp add:nset_def,
       simp add:transpos_ij_2,
       drule_tac x = m in bspec, simp add:nset_def,
       simp add:transpos_id)
done  

lemma (in Corps) Ostrowski_baseTr1:"\<lbrakk>vals_nonequiv K (Suc n) vv; l \<le> (Suc n)\<rbrakk>
     \<Longrightarrow> 0 < ((vv l) (1\<^sub>r \<plusminus> -\<^sub>a (Ostrowski_base K vv (Suc n) l)))"
by (simp add:Ostrowski_baseTr0)

lemma (in Corps) Ostrowski_baseTr2:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
        l \<le> (Suc n); m \<le> (Suc n); l \<noteq> m\<rbrakk> \<Longrightarrow>
        0 < ((vv m) (Ostrowski_base K vv (Suc n) l))"   
apply (frule Ostrowski_baseTr0[of "n" "vv" "l"], assumption+) 
apply simp
done

lemma Nset_have_two:"j \<in>{h. h \<le> (Suc n)} \<Longrightarrow> \<exists>m \<in> {h. h \<le> (Suc n)}. j \<noteq> m"
apply (rule contrapos_pp, simp+,
       case_tac "j = Suc n", simp,
       drule_tac a = 0 in forall_spec, simp, arith) 
 apply (drule_tac a = "Suc n" in forall_spec, simp, simp)
done  

lemma (in Corps) Ostrowski_base_npow_not_one:"\<lbrakk>0 < N; j \<le> Suc n;
       vals_nonequiv K (Suc n) vv\<rbrakk>  \<Longrightarrow>  
                              1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>) \<noteq> \<zero>"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       rule contrapos_pp, simp+,
       frule Ostrowski_base_mem_1[of "n" "vv" "j"], assumption,
       frule Ring.npClose[of "K" "(\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j" "N"], assumption+,
       frule Ring.ring_one[of "K"],
       frule aGroup.ag_mOp_closed[of K "(\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>"], assumption+,
       frule aGroup.ag_pOp_closed[of "K" "1\<^sub>r" "-\<^sub>a ((\<Omega>\<^bsub>K  vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>)"],
       assumption+) 
apply (frule  aGroup.ag_pOp_add_r[of "K" "1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>)" "\<zero>" 
           "(\<Omega>\<^bsub>K  vv  (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>"], assumption+,
        simp add:aGroup.ag_inc_zero, assumption+, 
        thin_tac "1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>) = \<zero>")
 apply (simp add:aGroup.ag_pOp_assoc[of "K" "1\<^sub>r" "-\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>)"])
 apply (simp add:aGroup.ag_l_inv1, simp add:aGroup.ag_r_zero aGroup.ag_l_zero)
  apply (subgoal_tac "\<forall>m \<le> (Suc n). (j \<noteq> m \<longrightarrow> 
                                 0 < (vv m ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)))") 
 apply (cut_tac Nset_have_two[of "j" "n"],
        erule bexE, drule_tac a = m in forall_spec, simp,
       thin_tac "(\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup> \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>) \<in> carrier K",
       frule_tac f = "vv m" in eq_elems_eq_val[of "1\<^sub>r" "(\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>"],
       thin_tac "1\<^sub>r = (\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>", simp)
 apply (frule_tac m = m in vals_nonequiv_valuation[of "Suc n" "vv"],
        assumption+, 
        frule_tac v1 = "vv m" and n1 = N in val_exp_ring[THEN sym, 
         of  _ "(\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j"], assumption+,
        simp add:Ostrowski_base_nonzero, simp, simp add:value_of_one)
 apply (subgoal_tac "int N \<noteq> 0",
        frule_tac x = "vv m ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)" in asprod_0[of "int N"],
        assumption, simp add:less_ant_def, simp, simp,
        rule allI, rule impI, rule impI,
        rule Ostrowski_baseTr2, assumption+)
done

abbreviation
  CHOOSE :: "[nat, nat] \<Rightarrow> nat"  ("(\<^bsub>_\<^esub>C\<^bsub>_\<^esub>)" [80, 81]80) where
  "\<^bsub>n\<^esub>C\<^bsub>i\<^esub> == n choose i"

lemma (in Ring) expansion_of_sum1:"x \<in> carrier R \<Longrightarrow> 
                (1\<^sub>r \<plusminus> x)^\<^bsup>R n\<^esup> = nsum R (\<lambda>i. \<^bsub>n\<^esub>C\<^bsub>i\<^esub> \<times>\<^bsub>R\<^esub> x^\<^bsup>R i\<^esup>) n"
apply (cut_tac ring_one, frule npeSum2[of "1\<^sub>r" "x" "n"], assumption+,
       simp add:npOne, subgoal_tac "\<forall>(j::nat). (x^\<^bsup>R j\<^esup>) \<in> carrier R")
apply (simp add:ring_l_one, rule allI, simp add:npClose)
done 

lemma (in Ring) tail_of_expansion:"x \<in> carrier R \<Longrightarrow> (1\<^sub>r \<plusminus> x)^\<^bsup>R (Suc n)\<^esup> = 
             (nsum R (\<lambda> i. (\<^bsub>(Suc n)\<^esub>C\<^bsub>(Suc i)\<^esub> \<times>\<^bsub>R\<^esub> x^\<^bsup>R (Suc i)\<^esup>)) n) \<plusminus> 1\<^sub>r"
apply (cut_tac ring_is_ag)
apply (frule expansion_of_sum1[of "x" "Suc n"],
       simp del:nsum_suc binomial_Suc_Suc npow_suc,
       thin_tac "(1\<^sub>r \<plusminus> x)^\<^bsup>R (Suc n)\<^esup> = \<Sigma>\<^sub>e R (\<lambda>i. \<^bsub>(Suc n)\<^esub>C\<^bsub>i\<^esub> \<times>\<^bsub>R\<^esub> x^\<^bsup>R i\<^esup>) (Suc n)")
apply (subst aGroup.nsumTail[of R n "\<lambda>i. \<^bsub>(Suc n)\<^esub>C\<^bsub>i\<^esub> \<times>\<^bsub>R\<^esub> x^\<^bsup>R i\<^esup>"], assumption,
       rule allI, rule impI, rule nsClose, rule npClose, assumption)
apply (cut_tac ring_one,
       simp del:nsum_suc binomial_Suc_Suc npow_suc add:aGroup.ag_l_zero) 
done

lemma (in Ring) tail_of_expansion1:"x \<in> carrier R \<Longrightarrow>
  (1\<^sub>r \<plusminus> x)^\<^bsup>R (Suc n)\<^esup>  = x \<cdot>\<^sub>r (nsum R (\<lambda> i. (\<^bsub>(Suc n)\<^esub>C\<^bsub>(Suc i)\<^esub> \<times>\<^bsub>R\<^esub> x^\<^bsup>R i\<^esup>)) n) \<plusminus> 1\<^sub>r"
apply (frule tail_of_expansion[of "x" "n"], 
       simp del:nsum_suc binomial_Suc_Suc npow_suc,
       subgoal_tac "\<forall>i.  \<^bsub>Suc n\<^esub>C\<^bsub>Suc i\<^esub> \<times>\<^bsub>R\<^esub> x^\<^bsup>R i\<^esup> \<in> carrier R",
       cut_tac ring_one, cut_tac ring_is_ag)
prefer 2  apply(simp add: nsClose npClose)
apply (rule aGroup.ag_pOp_add_r[of "R" _ _ "1\<^sub>r"], assumption+,
       rule aGroup.nsum_mem, assumption+, rule allI, rule impI,
       rule nsClose, rule npClose, assumption)
apply (rule ring_tOp_closed, assumption+,
       rule aGroup.nsum_mem, assumption+, blast, simp add:ring_one)
apply (subst nsumMulEleL[of "\<lambda>i. \<^bsub>Suc n\<^esub>C\<^bsub>Suc i\<^esub> \<times>\<^bsub>R\<^esub> x^\<^bsup>R i\<^esup>" "x"], assumption+)
apply (rule aGroup.nsum_eq, assumption, rule allI, rule impI, rule nsClose,
       rule npClose, assumption, rule allI, rule impI,
       rule ring_tOp_closed, assumption+, rule nsClose, rule npClose,
       assumption) 
apply (rule allI, rule impI)
apply (subst nsMulDistrL, assumption, simp add:npClose, 
       frule_tac n = j in npClose[of x], simp add:ring_tOp_commute[of x])
done 

lemma (in Corps) nsum_in_VrTr:"valuation K v \<Longrightarrow> 
       (\<forall>j \<le> n. f j \<in> carrier K) \<and> (\<forall>j \<le> n. 
       0 \<le> (v (f j))) \<longrightarrow> (nsum K f n) \<in> carrier (Vr K v)"
apply (induct_tac n)
 apply (rule impI, erule conjE, simp add:val_pos_mem_Vr)
apply (rule impI, erule conjE)
apply (frule Vr_ring[of v], frule Ring.ring_is_ag[of "Vr K v"],
       frule_tac  x = "f (Suc n)" and y = "nsum K f n" in 
         aGroup.ag_pOp_closed[of "Vr K v"],
       subst val_pos_mem_Vr[THEN sym, of  "v"], assumption+,
       simp, simp, simp) 
apply (simp, subst Vr_pOp_f_pOp[of "v", THEN sym], assumption+,
       subst val_pos_mem_Vr[THEN sym, of v], assumption+,
       simp+)
apply (subst aGroup.ag_pOp_commute, assumption+, simp add:val_pos_mem_Vr,
       assumption)
done

lemma (in Corps) nsum_in_Vr:"\<lbrakk>valuation K v; \<forall>j \<le> n. f j \<in> carrier K; 
       \<forall>j \<le> n.  0 \<le> (v (f j))\<rbrakk> \<Longrightarrow> (nsum K f n) \<in> carrier (Vr K v)"
apply (simp add:nsum_in_VrTr)
done

lemma (in Corps) nsum_mem_in_Vr:"\<lbrakk>valuation K v; 
       \<forall>j \<le> n. (f j) \<in> carrier K; \<forall>j \<le> n. 0 \<le> (v (f j))\<rbrakk> \<Longrightarrow>
         (nsum K f n) \<in> carrier (Vr K v)"
by (rule nsum_in_Vr)

lemma (in Corps) val_nscal_ge_selfTr:"\<lbrakk>valuation K v; x \<in> carrier K; 0 \<le> v x\<rbrakk>
       \<Longrightarrow>  v x \<le>  v (n \<times>\<^bsub>K\<^esub> x)"
apply (cut_tac field_is_ring, induct_tac n, simp)  
apply (simp add:value_of_zero,
       simp,
       frule_tac y = "n \<times>\<^bsub>K\<^esub> x" in amin_le_plus[of "v" "x"], assumption+,
       rule Ring.nsClose, assumption+) 
apply (simp add:amin_def,
       frule Ring.ring_is_ag[of K],
       frule_tac n = n in Ring.nsClose[of K x], assumption+,
       simp add:aGroup.ag_pOp_commute)
done

lemma (in Corps) ApproximationTr:"\<lbrakk>valuation K v; x \<in> carrier K; 0 \<le> (v x)\<rbrakk> \<Longrightarrow>
             v x \<le> (v (1\<^sub>r \<plusminus> -\<^sub>a ((1\<^sub>r \<plusminus> x)^\<^bsup>K (Suc n)\<^esup>)))"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       case_tac "x = \<zero>\<^bsub>K\<^esub>",
       simp, frule Ring.ring_one[of "K"], simp add:aGroup.ag_r_zero,
       simp add:Ring.npOne, simp add:Ring.ring_l_one,simp add:aGroup.ag_r_inv1,
       subst Ring.tail_of_expansion1[of "K" "x"], assumption+, 
       frule Ring.ring_one[of "K"])
apply (subgoal_tac "(nsum K (\<lambda>i. \<^bsub>Suc n\<^esub>C\<^bsub>Suc i\<^esub> \<times>\<^bsub>K\<^esub> x^\<^bsup>K i\<^esup>) n)\<in>carrier (Vr K v)",
       frule Vr_mem_f_mem[of "v" "(nsum K (\<lambda>i. \<^bsub>Suc n\<^esub>C\<^bsub>Suc i\<^esub> \<times>\<^bsub>K\<^esub> x^\<^bsup>K i\<^esup>) n)"],
       assumption+,
       frule_tac x = x and y = "nsum K (\<lambda>i. \<^bsub>Suc n\<^esub>C\<^bsub>Suc i\<^esub> \<times>\<^bsub>K\<^esub> x^\<^bsup>K i\<^esup>) n" in 
       Ring.ring_tOp_closed[of "K"], assumption+,
       subst aGroup.ag_pOp_commute[of "K" _ "1\<^sub>r"], assumption+,
       subst aGroup.ag_p_inv[of "K" "1\<^sub>r"], assumption+,
       subst aGroup.ag_pOp_assoc[THEN sym], assumption+,
       simp add:aGroup.ag_mOp_closed, rule aGroup.ag_mOp_closed, assumption+,
       simp del:binomial_Suc_Suc add:aGroup.ag_r_inv1, subst aGroup.ag_l_zero,
       assumption+,
       rule aGroup.ag_mOp_closed, assumption+, simp add:val_minus_eq)

apply (subst val_t2p[of v], assumption+) apply (
       simp add:val_pos_mem_Vr[THEN sym, of v 
                  "nsum K (\<lambda>i.(\<^bsub>n\<^esub>C\<^bsub>i\<^esub> + \<^bsub>n\<^esub>C\<^bsub>Suc i\<^esub>) \<times>\<^bsub>K\<^esub> x^\<^bsup>K i\<^esup>) n"],
       frule aadd_le_mono[of "0" "v (nsum K (\<lambda>i.(\<^bsub>n\<^esub>C\<^bsub>i\<^esub> + \<^bsub>n\<^esub>C\<^bsub>Suc i\<^esub>) \<times>\<^bsub>K\<^esub> x^\<^bsup>K i\<^esup>) n)" 
         "v x"], simp add:aadd_0_l, simp add:aadd_commute[of "v x"])

apply (rule nsum_mem_in_Vr[of v n "\<lambda>i.\<^bsub>Suc n\<^esub>C\<^bsub>Suc i\<^esub> \<times>\<^bsub>K\<^esub> x^\<^bsup>K i\<^esup>"], assumption, 
       rule allI, rule impI) apply (rule Ring.nsClose, assumption+) apply (simp add:Ring.npClose)

apply (rule allI, rule impI)
apply (cut_tac i = 0 and j = "v (x^\<^bsup>K j\<^esup>)" and k = "v (\<^bsub>Suc n\<^esub>C\<^bsub>Suc j\<^esub> \<times>\<^bsub>K\<^esub> x^\<^bsup>K j\<^esup>)"
       in ale_trans)
 apply (case_tac "j = 0", simp add:value_of_one)
 apply (simp add: val_exp_ring[THEN sym],
        frule val_nonzero_z[of v x], assumption+,
        erule exE,
        cut_tac m1 = 0 and n1 = j in of_nat_less_iff[THEN sym],
        frule_tac a = "0 < j" and b = "int 0 < int j" in a_b_exchange,
        assumption, thin_tac "0 < j", thin_tac "(0 < j) = (int 0 < int j)")
apply (simp del: of_nat_0_less_iff)

apply (frule_tac w1 = "int j" and x1 = 0 and y1 = "ant z" in 
         asprod_pos_mono[THEN sym],
        simp only:asprod_n_0) 

 apply(rule_tac x = "x^\<^bsup>K j\<^esup>" and n = "\<^bsub>Suc n\<^esub>C\<^bsub>Suc j\<^esub>" in 
       val_nscal_ge_selfTr[of v], assumption+,
       simp add:Ring.npClose, simp add:val_exp_ring[THEN sym],
       frule val_nonzero_z[of "v" "x"], assumption+, erule exE, simp)
 apply (case_tac "j = 0", simp)
 apply (subst asprod_amult, simp, simp add:a_z_z)
apply(
        simp only:ant_0[THEN sym], simp only:ale_zle,
        cut_tac m1 = 0 and n1 = j in of_nat_less_iff[THEN sym])
apply (        frule_tac a = "0 < j" and b = "int 0 < int j" in a_b_exchange, 
        assumption+, thin_tac "0 < j", thin_tac "(0 < j) = (int 0 < int j)",
        frule_tac z = "int 0" and z' = "int j" in zless_imp_zle,
        frule_tac i = "int 0" and j = "int j" and k = z in int_mult_le,
         assumption+, simp add:mult.commute )
 apply assumption
done

lemma (in Corps) ApproximationTr0:"aa \<in> carrier K \<Longrightarrow>
            (1\<^sub>r \<plusminus> -\<^sub>a (aa^\<^bsup>K N\<^esup>))^\<^bsup>K N\<^esup> \<in> carrier K"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       rule Ring.npClose, assumption+, 
       rule aGroup.ag_pOp_closed, assumption+, simp add:Ring.ring_one,
       rule aGroup.ag_mOp_closed, assumption+, rule Ring.npClose, assumption+)
done

lemma (in Corps) ApproximationTr1:"aa \<in> carrier K \<Longrightarrow>
            1\<^sub>r \<plusminus> -\<^sub>a ((1\<^sub>r \<plusminus> -\<^sub>a (aa^\<^bsup>K N\<^esup>))^\<^bsup>K N\<^esup>) \<in> carrier K"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule ApproximationTr0[of aa N],
       frule Ring.ring_one[of "K"], rule aGroup.ag_pOp_closed, assumption+,
       rule aGroup.ag_mOp_closed, assumption+)
done

lemma (in Corps) ApproximationTr2:"\<lbrakk>valuation K v; aa \<in> carrier K; aa \<noteq> \<zero>; 
     0 \<le> (v aa)\<rbrakk> \<Longrightarrow> (int N) *\<^sub>a(v aa) \<le> (v (1\<^sub>r \<plusminus> -\<^sub>a ((1\<^sub>r \<plusminus> -\<^sub>a (aa^\<^bsup>K N\<^esup>))^\<^bsup>K N\<^esup>)))"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       case_tac "N = 0",
       frule val_nonzero_z[of v "aa"], assumption+, erule exE, simp) 
 apply(frule Ring.ring_one[of "K"], simp add:aGroup.ag_r_inv1,
       simp add:value_of_zero)

apply (frule_tac n = N in Ring.npClose[of "K" "aa"], assumption+,
       frule ApproximationTr[of v "-\<^sub>a (aa^\<^bsup>K N\<^esup>)" "N - Suc 0"],
       rule aGroup.ag_mOp_closed, assumption+, simp add:val_minus_eq,
       subst val_exp_ring[THEN sym, of v], assumption+,
       simp add:asprod_pos_pos)
apply (simp add:val_minus_eq, simp add:val_exp_ring[THEN sym])
done

lemma (in Corps) eSum_tr:"
( \<forall>j \<le> n. (x j) \<in> carrier K) \<and> 
 ( \<forall>j \<le> n. (b j) \<in> carrier K) \<and> l \<le> n \<and> 
 ( \<forall>j\<in>({h. h \<le> n} -{l}). (g j = (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (b j)))) \<and> 
  g l = (x l) \<cdot>\<^sub>r (-\<^sub>a (b l))
\<longrightarrow> (nsum K (\<lambda>j \<in> {h. h \<le> n}. (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (b j))) n) \<plusminus> (-\<^sub>a (x l)) = 
                       nsum K g n"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
apply (induct_tac n)
 apply (simp, rule impI, (erule conjE)+, 
       simp, frule Ring.ring_one[of "K"], subst Ring.ring_distrib1, 
       assumption+,
       simp add:aGroup.ag_mOp_closed, simp add:Ring.ring_r_one,
       frule aGroup.ag_mOp_closed[of K "b 0"], assumption+,
       frule Ring.ring_tOp_closed[of "K" "x 0" "-\<^sub>a (b 0)"], assumption+,
       subst aGroup.ag_pOp_commute[of "K" "x 0" _], assumption+,
       subst aGroup.ag_pOp_assoc, assumption+, 
       frule aGroup.ag_mOp_closed[of "K"], 
       assumption+) 
 apply (simp add:aGroup.ag_r_inv1, subst aGroup.ag_r_zero, assumption+, simp)
apply (rule impI, (erule conjE)+)
 apply (subgoal_tac "\<forall>j \<le> (Suc n).  ((x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (b j))) \<in> carrier K")
apply (case_tac "l = Suc n", simp)
 apply (subgoal_tac "\<Sigma>\<^sub>e K g n \<in> carrier K",
        subgoal_tac "{h. h \<le> (Suc n)} - {Suc n} = {h. h \<le> n}", simp,
        subgoal_tac "\<forall>j. j \<le> n \<longrightarrow> j \<le> (Suc n)",
        frule_tac f = "\<lambda>u. if u \<le> Suc n then (x u) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (b u)) else 
        undefined" and n = n in aGroup.nsum_eq[of "K" _ _ "g"])
 apply (rule allI, rule impI, simp,
        rule allI, simp, rule allI, rule impI, simp, simp)

 apply (cut_tac a = "x (Suc n) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (b (Suc n))) \<plusminus> -\<^sub>a (x (Suc n))" and 
       b = "x (Suc n) \<cdot>\<^sub>r (-\<^sub>a (b (Suc n)))" and 
       c = "\<Sigma>\<^sub>e K g n" in aGroup.ag_pOp_add_l[of K], assumption)
 apply (rule aGroup.ag_pOp_closed, assumption+,
        rule Ring.ring_tOp_closed, assumption+, simp,
        rule aGroup.ag_pOp_closed, assumption+, simp add:Ring.ring_one,
        rule aGroup.ag_mOp_closed, assumption, simp,
        rule aGroup.ag_mOp_closed, assumption, simp,
        rule Ring.ring_tOp_closed, assumption+, simp,
        rule aGroup.ag_mOp_closed, assumption+, simp, assumption)

 apply (subst Ring.ring_distrib1, assumption+, simp, simp add:Ring.ring_one,
        simp add:aGroup.ag_mOp_closed,
        simp add:Ring.ring_r_one) apply (
        frule_tac x = "x (Suc n)" and y = "x (Suc n) \<cdot>\<^sub>r (-\<^sub>a (b (Suc n)))" in
        aGroup.ag_pOp_commute [of "K"], simp,
        simp add:Ring.ring_tOp_closed aGroup.ag_mOp_closed,
        simp) apply (
        subst aGroup.ag_pOp_assoc[of "K"], assumption+,
        rule Ring.ring_tOp_closed, assumption+, simp, 
        (simp add:aGroup.ag_mOp_closed)+,
        subst aGroup.ag_r_inv1, assumption+, simp,
        subst aGroup.ag_r_zero, assumption+,
        simp add:Ring.ring_tOp_closed aGroup.ag_mOp_closed, simp,
        rotate_tac -1, drule sym, simp) apply (
        thin_tac "\<Sigma>\<^sub>e K g n \<plusminus> x (Suc n) \<cdot>\<^sub>r (-\<^sub>a (b (Suc n))) =
         \<Sigma>\<^sub>e K g n \<plusminus> (x (Suc n) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (b (Suc n))) \<plusminus> -\<^sub>a (x (Suc n)))")
   apply (subst aGroup.ag_pOp_assoc[THEN sym], assumption+,
          rule Ring.ring_tOp_closed, assumption+, simp, 
          rule aGroup.ag_pOp_closed, assumption+, simp add:Ring.ring_one,
          rule aGroup.ag_mOp_closed, assumption+, simp,
          rule aGroup.ag_mOp_closed, assumption+, simp, simp,
          simp, rule equalityI, rule subsetI, simp, rule subsetI, simp)
  apply (rule aGroup.nsum_mem, assumption+,
         rule allI, rule impI, simp)
defer
  apply (rule allI, rule impI)
  apply (case_tac "j = l", simp,
         rule Ring.ring_tOp_closed, assumption, simp,
         rule aGroup.ag_pOp_closed, assumption+, simp add:Ring.ring_one,
         rule aGroup.ag_mOp_closed, assumption, simp, simp,
         rule Ring.ring_tOp_closed, assumption, simp,
         rule aGroup.ag_pOp_closed, assumption+, simp add:Ring.ring_one,
         rule aGroup.ag_mOp_closed, assumption, simp, simp) (* end defer *)

 apply (subst aGroup.ag_pOp_assoc, assumption+,
        rule aGroup.nsum_mem, assumption+,
        rule allI, simp, rule Ring.ring_tOp_closed, assumption+, simp,
        rule aGroup.ag_pOp_closed, assumption+, simp add:Ring.ring_one,
        rule aGroup.ag_mOp_closed, assumption, simp,
        rule aGroup.ag_mOp_closed, assumption, simp,
        subst aGroup.ag_pOp_commute[of K _ "-\<^sub>a (x l)"], assumption+,
        rule Ring.ring_tOp_closed, assumption, simp,
        rule aGroup.ag_pOp_closed, assumption+, simp add:Ring.ring_one)
 apply (rule aGroup.ag_mOp_closed, assumption+, simp,
        rule aGroup.ag_mOp_closed, assumption+, simp,
        subst aGroup.ag_pOp_assoc[THEN sym], assumption+,
        rule aGroup.nsum_mem, assumption+,
        rule allI, rule impI, simp,
        rule aGroup.ag_mOp_closed, assumption, simp, 
        rule Ring.ring_tOp_closed, assumption, simp,
         rule aGroup.ag_pOp_closed, assumption+, simp add:Ring.ring_one,
         rule aGroup.ag_mOp_closed, assumption, simp)
  apply (subgoal_tac "\<Sigma>\<^sub>e K (\<lambda>a. if a \<le> (Suc n) then x a \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (b a)) 
         else undefined) n \<plusminus> -\<^sub>a (x l) = 
         \<Sigma>\<^sub>e K (\<lambda>a. if a \<le> n then x a \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (b a)) else undefined) n \<plusminus>
         -\<^sub>a (x l)", simp,
         rule aGroup.ag_pOp_add_r[of K _ _ "-\<^sub>a (x l)"], assumption+,
         rule aGroup.nsum_mem, assumption+,
         rule allI, rule impI, simp, 
         rule aGroup.nsum_mem, assumption+,
         rule allI, rule impI, simp,
         rule aGroup.ag_mOp_closed, assumption, simp,
         rule aGroup.nsum_eq, assumption+,
         rule allI, rule impI, simp, rule allI, rule impI) 
   apply simp
   apply (rule allI, rule impI, simp) 
done

lemma (in Corps) eSum_minus_x:"\<lbrakk>\<forall>j \<le> n. (x j) \<in> carrier K; 
       \<forall>j \<le> n. (b j) \<in> carrier K; l \<le> n; 
       \<forall>j\<in>({h. h \<le> n} -{l}). (g j = (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (b j))); 
       g l = (x l) \<cdot>\<^sub>r (-\<^sub>a (b l)) \<rbrakk> \<Longrightarrow>
       (nsum K (\<lambda>j\<in>{h. h \<le> n}. (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (b j))) n) \<plusminus> (-\<^sub>a (x l)) = 
                        nsum K g n"
by (cut_tac eSum_tr[of "n" "x" "b" "l" "g"], simp) 

lemma (in Ring) one_m_x_times:"x \<in> carrier R \<Longrightarrow>
 (1\<^sub>r \<plusminus> -\<^sub>a x) \<cdot>\<^sub>r (nsum R (\<lambda>j. x^\<^bsup>R j\<^esup>) n) = 1\<^sub>r \<plusminus> -\<^sub>a (x^\<^bsup>R (Suc n)\<^esup>)"
apply (cut_tac ring_one, cut_tac ring_is_ag,
       frule aGroup.ag_mOp_closed[of "R" "x"], assumption+,
       frule aGroup.ag_pOp_closed[of "R" "1\<^sub>r" "-\<^sub>a x"], assumption+)

apply (induct_tac n)
 apply (simp add:ring_r_one ring_l_one)
 apply (simp del:npow_suc,
        frule_tac n = "Suc n" in npClose[of "x"],
        subst ring_distrib1, assumption+)
 apply (rule aGroup.nsum_mem, assumption, rule allI, rule impI,
        simp add:npClose, rule npClose, assumption+,
        simp del:npow_suc,
        thin_tac "(1\<^sub>r \<plusminus> -\<^sub>a x) \<cdot>\<^sub>r \<Sigma>\<^sub>e R (npow R x) n = 1\<^sub>r \<plusminus> -\<^sub>a (x^\<^bsup>R (Suc n)\<^esup>)")
 apply (subst ring_distrib2, assumption+,
        simp del:npow_suc add:ring_l_one,
        subst aGroup.pOp_assocTr43[of R], assumption+,
        rule_tac x = "x^\<^bsup>R (Suc n)\<^esup>" in aGroup.ag_mOp_closed[of R], assumption+,
        rule ring_tOp_closed, rule aGroup.ag_mOp_closed, assumption+)
 apply (subst aGroup.ag_l_inv1, assumption+, simp del:npow_suc 
        add:aGroup.ag_r_zero,
        frule_tac x = "-\<^sub>a x" and y = "x^\<^bsup>R (Suc n)\<^esup>" in ring_tOp_closed,
        assumption+)
 apply (rule aGroup.ag_pOp_add_l[of R _ _ "1\<^sub>r"], assumption+,
        rule aGroup.ag_mOp_closed, assumption+,
        rule npClose, assumption+,
        subst ring_inv1_1[THEN sym, of x], assumption,
        rule npClose, assumption,
        simp,
        subst ring_tOp_commute[of x], assumption+, simp)
done

lemma (in Corps) x_pow_fSum_in_Vr:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v)\<rbrakk> \<Longrightarrow>
   (nsum K (npow K x) n) \<in> carrier (Vr K v)" 
apply (frule Vr_ring[of v])
apply (induct_tac n)
 apply simp
 apply (frule Ring.ring_one[of "Vr K v"])
 apply (simp add:Vr_1_f_1)
apply (simp del:npow_suc)
 apply (frule Ring.ring_is_ag[of "Vr K v"])

 apply (subst Vr_pOp_f_pOp[THEN sym, of v], assumption+)
 apply (subst Vr_exp_f_exp[THEN sym, of v], assumption+)
 apply (rule Ring.npClose[of "Vr K v"], assumption+)
 apply (rule aGroup.ag_pOp_closed[of "Vr K v"], assumption+)
 apply (subst Vr_exp_f_exp[THEN sym, of v], assumption+)
 apply (rule Ring.npClose[of "Vr K v"], assumption+)
done

lemma (in Corps) val_1mx_pos:"\<lbrakk>valuation K v; x \<in> carrier K; 
         0 < (v (1\<^sub>r \<plusminus> -\<^sub>a x))\<rbrakk> \<Longrightarrow>  v x = 0"
apply (cut_tac field_is_ring, frule Ring.ring_one[of "K"], 
       frule Ring.ring_is_ag[of "K"])
 apply (frule aGroup.ag_mOp_closed[of "K" "x"], assumption+)
 apply (frule aGroup.ag_pOp_closed[of "K" "1\<^sub>r" "-\<^sub>a x"], assumption+)
 apply (frule aGroup.ag_mOp_closed[of "K" "1\<^sub>r \<plusminus> -\<^sub>a x"], assumption+)
 apply (cut_tac x = x and y = "1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a x)" and f = v in 
        eq_elems_eq_val)
apply (subst aGroup.ag_p_inv, assumption+,
       subst aGroup.ag_pOp_assoc[THEN sym], assumption+,
       rule aGroup.ag_mOp_closed, assumption+,
       subst aGroup.ag_inv_inv, assumption+,
       subst aGroup.ag_r_inv1, assumption+,
       subst aGroup.ag_l_zero, assumption+,
       (simp add:aGroup.ag_inv_inv)+,
       frule  value_less_eq[of v  "1\<^sub>r" "-\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a x)"],
        assumption+)
 apply (simp add:val_minus_eq value_of_one,
        simp add:value_of_one)
done 

lemma (in Corps) val_1mx_pow:"\<lbrakk>valuation K v; x \<in> carrier K; 
       0 < (v (1\<^sub>r \<plusminus> -\<^sub>a x))\<rbrakk> \<Longrightarrow> 0 < (v (1\<^sub>r \<plusminus> -\<^sub>a x^\<^bsup>K (Suc n)\<^esup>))"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
apply (subst Ring.one_m_x_times[THEN sym, of K x n], assumption+)
 apply (frule Ring.ring_one[of "K"],
        frule x_pow_fSum_in_Vr[of v x n],
        subst val_pos_mem_Vr[THEN sym], assumption+,
        frule val_1mx_pos[of "v" "x"], assumption+,
        simp)

 apply (subst val_t2p, assumption+,
        rule aGroup.ag_pOp_closed, assumption+,
        simp add:aGroup.ag_mOp_closed, simp add:Vr_mem_f_mem,
        frule val_pos_mem_Vr[THEN sym, of v "nsum K (npow K x) n"],
        simp add:Vr_mem_f_mem, simp)
 apply(frule aadd_le_mono[of "0" "v (nsum K (npow K x) n)" "v (1\<^sub>r \<plusminus> -\<^sub>a x)"],
       simp add:aadd_0_l, simp add:aadd_commute)
done

lemma (in Corps) ApproximationTr3:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
      \<forall>l \<le> (Suc n). x l \<in> carrier K; j \<le> (Suc n)\<rbrakk> \<Longrightarrow> 
     \<exists>L.(\<forall>N. L < N \<longrightarrow> (an m) \<le> (vv j ((\<Sigma>\<^sub>e K (\<lambda>k\<in>{h. h \<le> (Suc n)}. 
        (x k) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a ((1\<^sub>r \<plusminus> -\<^sub>a (((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) k)^\<^bsup>K N\<^esup>))^\<^bsup>K N\<^esup>))) 
        (Suc n)) \<plusminus> -\<^sub>a (x j))))"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
 apply (frule_tac vals_nonequiv_valuation[of "Suc n" "vv" j], assumption+) 
apply (subgoal_tac "\<forall>N. \<Sigma>\<^sub>e K (\<lambda>j\<in>{h. h \<le> (Suc n)}. (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> 
 -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>)) (Suc n) \<plusminus> -\<^sub>a (x j) = 
 \<Sigma>\<^sub>e K (\<lambda>l\<in>{h. h\<le> (Suc n)}. (if l \<noteq> j then (x l) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a 
 ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) l)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>) else (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus>
        -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) l)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>  \<plusminus> -\<^sub>a 1\<^sub>r))) (Suc n)")
 apply (simp del:nsum_suc)
apply (thin_tac "\<forall>N. \<Sigma>\<^sub>e K (\<lambda>j\<in>{h. h \<le> (Suc n)}. (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> 
 -\<^sub>a (\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>)) (Suc n) \<plusminus> -\<^sub>a (x j) = \<Sigma>\<^sub>e K (\<lambda>l\<in>{h. h \<le> (Suc n)}. if l \<noteq> j then (x l) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a (\<Omega>\<^bsub>K vv (Suc n)\<^esub>) l^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>) else (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a (\<Omega>\<^bsub>K vv (Suc n)\<^esub>) l^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup> \<plusminus> -\<^sub>a 1\<^sub>r)) (Suc n)")
prefer 2 apply (rule allI) 
 apply (rule eSum_minus_x, assumption+)
 apply (rule allI, rule impI) apply (rule ApproximationTr0)
 apply (simp add:Ostrowski_base_mem) apply assumption
 apply (rule ballI, simp)
 apply simp  
 apply (frule Ring.ring_one[of "K"]) 
 apply (cut_tac aa = "(\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j" and N = N in 
                                               ApproximationTr0)
 apply (simp add:Ostrowski_base_mem)
 apply (subst aGroup.ag_pOp_assoc, assumption+)
 apply (rule aGroup.ag_mOp_closed, assumption+)+
 apply (subst aGroup.ag_pOp_commute[of "K" _ "-\<^sub>a 1\<^sub>r"], assumption+)
 apply (rule aGroup.ag_mOp_closed, assumption+)+

 apply (subst aGroup.ag_pOp_assoc[THEN sym], assumption+)
 apply (rule aGroup.ag_mOp_closed, assumption+)+
 apply (simp add:aGroup.ag_r_inv1)
 apply (subst aGroup.ag_l_zero, assumption+) apply (simp add:aGroup.ag_mOp_closed)
 apply simp (* subgoal 2 done **)

 apply (subgoal_tac "\<exists>L. \<forall>N. L < N \<longrightarrow> 
  (\<forall>ja \<le> (Suc n). (an m) \<le> ((vv j \<circ> (\<lambda>l\<in>{h. h \<le> (Suc n)}. if l \<noteq> j then (x l) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) l)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>) else (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) l)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup> \<plusminus> -\<^sub>a 1\<^sub>r))) ja))")

(*
 apply (subgoal_tac "\<exists>L. \<forall>N. L < N \<longrightarrow> (an m) \<le> Amin (Suc n) (vv j \<circ> (\<lambda>l\<in>Nset (Suc n). if l\<noteq>j then (x l) \<cdot>\<^sub>K (1\<^sub>K +\<^sub>K -\<^sub>K (1\<^sub>K +\<^sub>K -\<^sub>K ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) l)^\<^sup>K\<^sup> \<^sup>N)^\<^sup>K\<^sup> \<^sup>N)
 else (x j) \<cdot>\<^sub>K (1\<^sub>K +\<^sub>K  -\<^sub>K (1\<^sub>K +\<^sub>K -\<^sub>K ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) l)^\<^sup>K\<^sup> \<^sup>N)^\<^sup>K\<^sup> \<^sup>N
+\<^sub>K -\<^sub>K 1\<^sub>K)))")
 apply (erule exE)
 apply (subgoal_tac "\<forall>N. L < N \<longrightarrow>
  ((an m) \<le> ((vv j) (e\<Sigma> K (\<lambda>l\<in>Nset (Suc n). (if l \<noteq> j then (x l) \<cdot>\<^sub>K
(1\<^sub>K +\<^sub>K -\<^sub>K (1\<^sub>K +\<^sub>K -\<^sub>K ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) l)^\<^sup>K\<^sup> \<^sup>N)^\<^sup>K\<^sup> \<^sup>N) else (x j) \<cdot>\<^sub>K (1\<^sub>K +\<^sub>K -\<^sub>K 
(1\<^sub>K +\<^sub>K -\<^sub>K ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) l)^\<^sup>K\<^sup> \<^sup>N)^\<^sup>K\<^sup> \<^sup>N +\<^sub>K -\<^sub>K 1\<^sub>K))) (Suc n))))")
apply blast
*)

apply (erule exE)
apply (rename_tac M)
 apply (subgoal_tac "\<forall>N. M < (N::nat) \<longrightarrow>
   (an m) \<le> (vv j (\<Sigma>\<^sub>e K (\<lambda>l\<in>{h. h \<le> (Suc n)}. (if l \<noteq> j then 
   (x l) \<cdot>\<^sub>r  (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) l)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>)
   else (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) l)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>
   \<plusminus> -\<^sub>a 1\<^sub>r))) (Suc n)))")
 apply blast
 apply (rule allI, rule impI)  
apply (drule_tac a = N in forall_spec, assumption)
 apply (rule value_ge_add[of "vv j" "Suc n" _ "an m"], assumption+)
 
apply (rule allI, rule impI)
 apply (frule Ring.ring_one[of "K"])
 apply (case_tac "ja = j", simp)
 apply (rule Ring.ring_tOp_closed, assumption+, simp)
 apply (rule aGroup.ag_pOp_closed, assumption+)+
 apply (rule aGroup.ag_mOp_closed, assumption+)
 apply (rule Ring.npClose, assumption)
 apply (rule aGroup.ag_pOp_closed, assumption+)
 apply (rule aGroup.ag_mOp_closed, assumption)
 apply (rule Ring.npClose, assumption)
 apply (simp add:Ostrowski_base_mem)
 apply (rule aGroup.ag_mOp_closed, assumption+)

apply simp
 apply (rule Ring.ring_tOp_closed, assumption+, simp)
 apply (rule aGroup.ag_pOp_closed, assumption+)+
 apply (rule aGroup.ag_mOp_closed, assumption+)
 apply (rule Ring.npClose, assumption)
 apply (rule aGroup.ag_pOp_closed, assumption+)
 apply (rule aGroup.ag_mOp_closed, assumption)
 apply (rule Ring.npClose, assumption)
 apply (simp add:Ostrowski_base_mem) 

apply assumption

 apply (subgoal_tac "\<forall>N. \<forall>ja \<le> (Suc n). (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a 
 ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) ja)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>) \<in> carrier K")
 apply (subgoal_tac "\<forall>N. (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>
                         \<plusminus> -\<^sub>a 1\<^sub>r) \<in> carrier K")
 apply (simp add:val_t2p) 
 apply (cut_tac multi_inequalityTr0[of "Suc n" "(vv j) \<circ> x" "m"])
 apply (subgoal_tac "\<forall>ja \<le> (Suc n). (vv j \<circ> x) ja \<noteq> - \<infinity>", simp)
 apply (erule exE)
 apply (subgoal_tac "\<forall>N. L < N \<longrightarrow> (\<forall>ja \<le> (Suc n). (ja \<noteq> j \<longrightarrow>
an m \<le> vv j (x ja) + (vv j (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) ja)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>)))
 \<and> (ja = j \<longrightarrow> (an m) \<le> vv j (x j) +  (vv j (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> 
  -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup> \<plusminus> -\<^sub>a (1\<^sub>r)))))")
 apply blast
 apply (rule allI, rule impI)+

apply (case_tac "ja = j", simp)
 apply (thin_tac "\<forall>N. 1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a (\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup> \<plusminus> -\<^sub>a 1\<^sub>r \<in> 
        carrier K")
 apply (thin_tac "\<forall>l\<le>Suc n. x l \<in> carrier K")
 apply (drule_tac x = N in spec)
 apply (drule_tac a = j in forall_spec, assumption,
        thin_tac "\<forall>ja\<le>Suc n. 1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a (\<Omega>\<^bsub>K vv (Suc n)\<^esub>) ja^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup> 
        \<in> carrier K")
apply (cut_tac N = N in ApproximationTr0 [of "(\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j"])
 apply (simp add:Ostrowski_base_mem)
 apply (frule Ring.ring_one[of "K"], frule aGroup.ag_mOp_closed[of "K" "1\<^sub>r"],
         assumption) apply (
        frule_tac x = "(1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>" in  
        aGroup.ag_mOp_closed[of "K"], assumption+)
 apply (simp only:aGroup.ag_pOp_assoc) 
 apply (simp only:aGroup.ag_pOp_commute[of "K" _ "-\<^sub>a 1\<^sub>r"])
 apply (simp only:aGroup.ag_pOp_assoc[THEN sym])
 apply (simp add:aGroup.ag_r_inv1)
 apply (simp add:aGroup.ag_l_zero) apply (simp only:val_minus_eq) 
  apply (thin_tac "(1\<^sub>r \<plusminus> -\<^sub>a (\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup> \<in> carrier K",
         thin_tac "-\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a (\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup> \<in> carrier K")
 apply (subst val_exp_ring[THEN sym, of "vv j"], assumption+)
  apply (rule aGroup.ag_pOp_closed[of "K"], assumption+)
  apply (rule aGroup.ag_mOp_closed[of "K"], assumption)
  apply (rule Ring.npClose, assumption+) apply (simp add:Ostrowski_base_mem)
 apply (rule Ostrowski_base_npow_not_one) apply simp apply assumption+
 apply (drule_tac a = N in forall_spec, assumption) 
 apply (drule_tac a = j in forall_spec, assumption) 
 apply (frule Ostrowski_baseTr1[of "n" "vv" "j"], assumption+)
 apply (frule_tac n = "N - Suc 0" in val_1mx_pow[of "vv j" "(\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j"])
 apply (simp add:Ostrowski_base_mem) apply assumption
 apply (thin_tac "vv j (x j) \<noteq> - \<infinity>")  apply (simp only:Suc_pred)
 apply (thin_tac "0 < vv j (1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j))")
 apply (cut_tac b = "vv j (1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)^\<^bsup>K N\<^esup>)" and N = N in 
        asprod_ge) apply assumption apply simp
 apply (cut_tac x = "an N" and y = "int N *\<^sub>a vv j (1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)^\<^bsup>K N\<^esup>)" in aadd_le_mono[of _ _ "vv j (x j)"], assumption) 
 apply (simp add:aadd_commute)

apply simp
apply (frule_tac aa = "(\<Omega>\<^bsub>K vv (Suc n)\<^esub>) ja" and N = N in 
       ApproximationTr2[of "vv j"])
   apply (simp add:Ostrowski_base_mem)
   apply (rule Ostrowski_base_nonzero, assumption+) 
apply (frule_tac l = ja in Ostrowski_baseTr0[of "n" "vv"], assumption+,
       erule conjE) 
 apply (rotate_tac -1, frule_tac a = j in forall_spec) apply assumption
 apply (frule_tac x = j in bspec, simp)
 apply (rule aless_imp_le) apply blast
 apply (rotate_tac -5, 
        drule_tac a = N in forall_spec, assumption)
 apply (rotate_tac -2, 
        drule_tac a = ja in forall_spec, assumption)  apply (
        drule_tac a = ja in forall_spec, assumption)
 apply (frule_tac l = ja in Ostrowski_baseTr0[of  "n" "vv"], assumption+)
 apply (erule conjE, rotate_tac -1, 
        frule_tac a = j in forall_spec, assumption+)
  apply (thin_tac "vv j (x ja) \<noteq> - \<infinity>")
 apply (cut_tac b = "vv j ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) ja)" and N = N in asprod_ge)
 apply simp apply simp
 apply (frule_tac x = "an N" and y = "int N *\<^sub>a vv j ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) ja)" and 
        z = "vv j (x ja)" in aadd_le_mono)
 apply (frule_tac x = "int N *\<^sub>a vv j ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) ja)" and y = "(vv j)
     (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) ja)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>)" and z = "vv j (x ja)"
      in aadd_le_mono)
 apply (frule_tac i = "an N + vv j (x ja)" and 
       j = "int N *\<^sub>a vv j ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) ja) + vv j (x ja)" and 
       k = "vv j (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) ja)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>) +
          vv j (x ja)" in ale_trans, assumption+)
 apply (subst aadd_commute)
 apply (frule_tac x = "an m" and y = "vv j (x ja) + an N" in aless_imp_le)
 apply (rule_tac j = "vv j (x ja) + an N" in ale_trans[of "an m"],
                  assumption) 
 apply (simp add:aadd_commute)
 apply (rule allI, rule impI, subst comp_def)
 apply (frule_tac a = ja in forall_spec, assumption)
 apply (frule_tac x = "x ja" in value_in_aug_inf[of "vv j"], assumption+)
 apply (simp add:aug_inf_def)

apply (rule allI) 
  apply (rule aGroup.ag_pOp_closed, assumption+) apply blast
 apply (rule aGroup.ag_mOp_closed, assumption, rule Ring.ring_one, assumption)

apply ((rule allI)+, rule impI)
apply (rule_tac aa = "(\<Omega>\<^bsub>K vv (Suc n)\<^esub>) ja" in ApproximationTr1,
       simp add:Ostrowski_base_mem)
done
 
definition
  app_lb :: "[_ , nat, nat \<Rightarrow> 'b \<Rightarrow> ant, nat \<Rightarrow> 'b, nat] \<Rightarrow> 
            (nat \<Rightarrow> nat)"   ("(5\<Psi>\<^bsub>_ _ _ _ _\<^esub>)" [98,98,98,98,99]98) where
  "\<Psi>\<^bsub>K n vv x m\<^esub> = (\<lambda>j\<in>{h. h \<le> n}. (SOME L. (\<forall>N. L < N \<longrightarrow>
  (an m) \<le> (vv j (\<Sigma>\<^sub>e K (\<lambda>j\<in>{h. h \<le> n}. (x j) \<cdot>\<^sub>r\<^bsub>K\<^esub> (1\<^sub>r\<^bsub>K\<^esub> \<plusminus>\<^bsub>K\<^esub> -\<^sub>a\<^bsub>K\<^esub>
  (1\<^sub>r\<^bsub>K\<^esub> \<plusminus>\<^bsub>K\<^esub> -\<^sub>a\<^bsub>K\<^esub> ((\<Omega>\<^bsub>K vv n\<^esub>) j)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>)) n \<plusminus>\<^bsub>K\<^esub> -\<^sub>a\<^bsub>K\<^esub> (x j))))))"
 (** Approximation lower bound **)

lemma (in Corps) app_LB:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
      \<forall>l\<le> (Suc n). x l \<in> carrier K; j \<le> (Suc n)\<rbrakk> \<Longrightarrow>
        \<forall>N. (\<Psi>\<^bsub>K (Suc n) vv x m\<^esub>) j < N \<longrightarrow> (an m) \<le> 
  (vv j (\<Sigma>\<^sub>e K (\<lambda>j\<in>{h. h \<le> (Suc n)}. (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> 
  -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>)) (Suc n) \<plusminus> -\<^sub>a (x j)))"
apply (frule ApproximationTr3[of "n" "vv" "x" "j" "m"], 
                               assumption+)
apply (simp del:nsum_suc add:app_lb_def)  apply (rule allI)
apply (rule someI2_ex) apply assumption+
apply (rule impI) apply blast
done

lemma (in Corps) ApplicationTr4:"\<lbrakk>vals_nonequiv K (Suc n) vv;  
 \<forall>j\<in>{h. h \<le> (Suc n)}. x j \<in> carrier K\<rbrakk> \<Longrightarrow> 
 \<exists>l. \<forall>N. l < N \<longrightarrow> (\<forall>j \<le> (Suc n).  (an m) \<le> 
  (vv j (\<Sigma>\<^sub>e K (\<lambda>j\<in>{h. h \<le> (Suc n)}. (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> 
  -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>)) (Suc n) \<plusminus> -\<^sub>a (x j))))"
apply (subgoal_tac "\<forall>N. (m_max (Suc n) (\<Psi>\<^bsub>K (Suc n) vv x m\<^esub>)) < N \<longrightarrow> 
  (\<forall>j\<le> (Suc n).  (an m) \<le> 
  (vv j (\<Sigma>\<^sub>e K (\<lambda>j\<in>{h. h \<le> (Suc n)}. (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus>  
  -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>)) (Suc n) \<plusminus> -\<^sub>a (x j))))")
apply blast
 apply (rule allI, rule impI)+ 
apply (frule_tac j = j in  app_LB[of  "n" "vv" "x" _ "m"],
       simp, assumption,
       subgoal_tac "(\<Psi>\<^bsub>K (Suc n) vv x m\<^esub>) j < N", blast)
apply (frule_tac l = j and n = "Suc n" and f = "\<Psi>\<^bsub>K (Suc n) vv x m\<^esub>" in m_max_gt,
       frule_tac x = "(\<Psi>\<^bsub>K (Suc n) vv x m\<^esub>) j" and 
       y = "m_max (Suc n) (\<Psi>\<^bsub>K (Suc n) vv x m\<^esub>)" and z = N in le_less_trans, 
       assumption+)
done

theorem (in Corps) Approximation_thm:"\<lbrakk>vals_nonequiv K (Suc n) vv; 
\<forall>j\<le> (Suc n). (x j) \<in> carrier K\<rbrakk>  \<Longrightarrow>
\<exists>y\<in>carrier K. \<forall>j\<le> (Suc n). (an m) \<le> (vv j (y \<plusminus> -\<^sub>a (x j)))"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"]) 
apply (subgoal_tac "\<exists>l. (\<forall>N. l < N \<longrightarrow> (\<forall>j \<le> (Suc n). (an m) \<le> ((vv j) ((nsum K (\<lambda>j\<in>{h. h \<le> (Suc n)}. (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)^\<^bsup>K N\<^esup>)^\<^bsup>K N\<^esup>)) (Suc n)) \<plusminus> -\<^sub>a (x j)))))") 
 apply (erule exE)
 apply (rename_tac M)
 apply (subgoal_tac "\<forall>j\<le> (Suc n). (an m) \<le>
 (vv j ( (\<Sigma>\<^sub>e K (\<lambda>j\<in>{h. h \<le> (Suc n)}. (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a (1\<^sub>r \<plusminus> 
  -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)^\<^bsup>K (Suc M)\<^esup>)^\<^bsup>K (Suc M)\<^esup>)) (Suc n)) \<plusminus> -\<^sub>a (x j)))")
 apply (subgoal_tac "\<Sigma>\<^sub>e K (\<lambda>j\<in>{h. h \<le> (Suc n)}. (x j) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> 
 -\<^sub>a (1\<^sub>r \<plusminus> -\<^sub>a ((\<Omega>\<^bsub>K vv (Suc n)\<^esub>) j)^\<^bsup>K (Suc M)\<^esup>)^\<^bsup>K (Suc M)\<^esup>)) (Suc n) \<in> carrier K")
 apply blast
 apply (rule aGroup.nsum_mem[of "K" "Suc n"], assumption+)
 apply (rule allI, rule impI, simp del:nsum_suc npow_suc)
 apply (rule Ring.ring_tOp_closed, assumption+, simp,
        rule ApproximationTr1, simp add:Ostrowski_base_mem)

 apply (subgoal_tac "M < Suc M") apply blast
 apply simp
 apply (rule ApplicationTr4[of n vv x], assumption+)
 apply simp
done

definition
  distinct_pds :: "[_, nat, nat \<Rightarrow> ('b \<Rightarrow> ant) set] \<Rightarrow> bool" where
  "distinct_pds K n P \<longleftrightarrow> (\<forall>j\<le> n. P j \<in> Pds\<^bsub> K\<^esub>) \<and> 
          (\<forall>l\<le> n. \<forall>m\<le> n. l \<noteq> m \<longrightarrow> P l \<noteq> P m)"

 (** pds --- prime divisors **)
lemma (in Corps) distinct_pds_restriction:"\<lbrakk>distinct_pds K (Suc n) P\<rbrakk> \<Longrightarrow> 
       distinct_pds K n P"  
apply (simp add:distinct_pds_def) 
done

lemma (in Corps) ring_n_distinct_prime_divisors:"distinct_pds K n P \<Longrightarrow>
       Ring (Sr K {x. x\<in>carrier K \<and> (\<forall>j\<le> n. 0 \<le> ((\<nu>\<^bsub> K (P j)\<^esub>) x))})"
apply (simp add:distinct_pds_def) apply (erule conjE)
apply (cut_tac field_is_ring)
apply (rule Ring.Sr_ring, assumption+)
apply (subst sr_def)
 apply (rule conjI)
 apply (rule subsetI) apply simp
 apply (rule conjI)
 apply (simp add:Ring.ring_one)
apply (rule allI, rule impI) 
 apply (cut_tac P = "P j" in representative_of_pd_valuation, simp,
        simp add:value_of_one) 
apply (rule ballI)+
 apply simp
 apply (frule Ring.ring_is_ag[of "K"]) apply (erule conjE)+
 apply (frule_tac x = y in aGroup.ag_mOp_closed[of "K"], assumption+)
 apply (frule_tac x = x and y = "-\<^sub>a y" in aGroup.ag_pOp_closed[of "K"], 
        assumption+)
 apply simp
 apply (rule conjI)
 apply (rule allI, rule impI)
 apply (rotate_tac -4, frule_tac a = j in forall_spec, assumption,
        rotate_tac -3,
        drule_tac a = j in forall_spec, assumption)
 apply (cut_tac P = "P j" in representative_of_pd_valuation, simp)
 apply (frule_tac v = "\<nu>\<^bsub>K (P j)\<^esub>" and x = x and y = "-\<^sub>a y" in amin_le_plus, 
        assumption+) 
 apply (simp add:val_minus_eq)
 apply (frule_tac x = "(\<nu>\<^bsub>K (P j)\<^esub>) x" and y = "(\<nu>\<^bsub>K (P j)\<^esub>) y" in amin_ge1[of "0"])
        apply simp
 apply (rule_tac j = "amin ((\<nu>\<^bsub>K (P j)\<^esub>) x) ((\<nu>\<^bsub>K (P j)\<^esub>) y)" and k = "(\<nu>\<^bsub>K (P j)\<^esub>) (x \<plusminus> -\<^sub>a y)" in ale_trans[of "0"], assumption+)
 apply (simp add:Ring.ring_tOp_closed)
 
apply (rule allI, rule impI,
       cut_tac P = "P j" in representative_of_pd_valuation, simp,
       subst val_t2p [where v="\<nu>\<^bsub>K P j\<^esub>"], assumption+,
       rule aadd_two_pos, simp+)
done

lemma (in Corps) distinct_pds_valuation:"\<lbrakk>j \<le> (Suc n);
       distinct_pds K (Suc n) P\<rbrakk> \<Longrightarrow>  valuation K (\<nu>\<^bsub>K (P j)\<^esub>)"
 apply (rule_tac P = "P j" in representative_of_pd_valuation) 
 apply (simp add:distinct_pds_def)
done

lemma (in Corps) distinct_pds_valuation1:"\<lbrakk>0 < n; j \<le> n; distinct_pds K n P\<rbrakk>
 \<Longrightarrow>  valuation K (\<nu>\<^bsub>K (P j)\<^esub>)"
apply (rule distinct_pds_valuation[of "j" "n - Suc 0" "P"]) 
apply simp+
done

lemma (in Corps) distinct_pds_valuation2:"\<lbrakk>j \<le> n; distinct_pds K n P\<rbrakk> \<Longrightarrow> 
          valuation K (\<nu>\<^bsub>K (P j)\<^esub>)"
apply (case_tac "n = 0",
       simp add:distinct_pds_def,
       subgoal_tac "0 \<in> {0::nat}",
       simp add:representative_of_pd_valuation[of "P 0"],
       simp)
 
 apply (simp add:distinct_pds_valuation1[of "n"])
done

definition
  ring_n_pd :: "[('b, 'm) Ring_scheme, nat \<Rightarrow> ('b \<Rightarrow> ant) set,
                             nat ] \<Rightarrow> ('b, 'm) Ring_scheme"
                 ("(3O\<^bsub>_ _ _\<^esub>)" [98,98,99]98) where
  "O\<^bsub>K P n\<^esub> = Sr K {x. x \<in> carrier K \<and>
           (\<forall>j \<le> n. 0 \<le> ((\<nu>\<^bsub>K (P j)\<^esub>) x))}" 
  (** ring defined by n prime divisors **)

lemma (in Corps) ring_n_pd:"distinct_pds K n P \<Longrightarrow> Ring (O\<^bsub>K P n\<^esub>)"
by (simp add:ring_n_pd_def, simp add:ring_n_distinct_prime_divisors)

lemma (in Corps) ring_n_pd_Suc:"distinct_pds K (Suc n) P \<Longrightarrow> 
          carrier (O\<^bsub> K P (Suc n)\<^esub>) \<subseteq> carrier (O\<^bsub>K P n\<^esub>)"
apply (rule subsetI)
 apply (simp add:ring_n_pd_def Sr_def)
done

lemma (in Corps) ring_n_pd_pOp_K_pOp:"\<lbrakk>distinct_pds K n P; x\<in>carrier (O\<^bsub>K P n\<^esub>);
 y \<in> carrier (O\<^bsub>K P n\<^esub>)\<rbrakk>  \<Longrightarrow> x \<plusminus>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub> y = x \<plusminus> y" 
apply (simp add:ring_n_pd_def Sr_def)
done

lemma (in Corps) ring_n_pd_tOp_K_tOp:"\<lbrakk>distinct_pds K n P; x \<in>carrier (O\<^bsub>K P n\<^esub>);
      y \<in> carrier (O\<^bsub>K P n\<^esub>)\<rbrakk> \<Longrightarrow>  x \<cdot>\<^sub>r\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub> y = x \<cdot>\<^sub>r y" 
apply (simp add:ring_n_pd_def Sr_def)
done

lemma (in Corps) ring_n_eSum_K_eSumTr:"distinct_pds K n P \<Longrightarrow> 
  (\<forall>j\<le>m. f j \<in> carrier (O\<^bsub>K P n\<^esub>)) \<longrightarrow> nsum (O\<^bsub>K P n\<^esub>) f m = nsum K f m"
apply (induct_tac m)
 apply (rule impI, simp)

 apply (rule impI, simp,
        subst ring_n_pd_pOp_K_pOp, assumption+,
        frule_tac n = n in ring_n_pd[of _ "P"],
        frule_tac Ring.ring_is_ag, drule sym, simp)
 apply (rule aGroup.nsum_mem, assumption+, simp+)
done

lemma (in Corps) ring_n_eSum_K_eSum:"\<lbrakk>distinct_pds K n P; 
      \<forall>j \<le> m. f j \<in> carrier (O\<^bsub>K P n\<^esub>)\<rbrakk> \<Longrightarrow> nsum (O\<^bsub>K P n\<^esub>) f m = nsum K f m"
apply (simp add:ring_n_eSum_K_eSumTr)
done

lemma (in Corps) ideal_eSum_closed:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; 
      \<forall>j \<le> m. f j \<in> I\<rbrakk> \<Longrightarrow>  nsum K f m \<in> I"
apply (frule ring_n_pd[of "n" "P"]) thm Ring.ideal_nsum_closed
 apply (frule_tac n = m in 
       Ring.ideal_nsum_closed[of "(O\<^bsub>K P n\<^esub>)" "I" _ "f"], assumption+)
 apply (subst ring_n_eSum_K_eSum [THEN sym, of n P m f], assumption+,
        rule allI, simp add:Ring.ideal_subset)
 apply assumption
done

definition
  prime_n_pd :: "[_, nat \<Rightarrow> ('b \<Rightarrow> ant) set,
                             nat, nat] \<Rightarrow> 'b set"
                 ("(4P\<^bsub>_ _ _\<^esub> _)" [98,98,98,99]98) where
  "P\<^bsub>K P n\<^esub> j = {x. x \<in> (carrier (O\<^bsub>K P n\<^esub>)) \<and> 0 < ((\<nu>\<^bsub>K (P j)\<^esub>) x)}"

lemma (in Corps) zero_in_ring_n_pd_zero_K:"distinct_pds K n P \<Longrightarrow> 
                               \<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub> = \<zero>\<^bsub>K\<^esub>"
apply (simp add:ring_n_pd_def Sr_def)
done

lemma (in Corps) one_in_ring_n_pd_one_K:"distinct_pds K n P \<Longrightarrow>
                                      1\<^sub>r\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub> = 1\<^sub>r"
apply (simp add:ring_n_pd_def Sr_def)
done

lemma (in Corps) mem_ring_n_pd_mem_K:"\<lbrakk>distinct_pds K n P; x \<in>carrier (O\<^bsub>K P n\<^esub>)\<rbrakk>
 \<Longrightarrow> x \<in> carrier K" 
apply (simp add:ring_n_pd_def Sr_def)
done

lemma (in Corps) ring_n_tOp_K_tOp:"\<lbrakk>distinct_pds K n P; x \<in> carrier (O\<^bsub>K P n\<^esub>); 
      y \<in> carrier (O\<^bsub>K P n\<^esub>)\<rbrakk>  \<Longrightarrow> x \<cdot>\<^sub>r\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub> y = x \<cdot>\<^sub>r y"
apply (simp add:ring_n_pd_def Sr_def)
done

lemma (in Corps) ring_n_exp_K_exp:"\<lbrakk>distinct_pds K n P; x \<in> carrier (O\<^bsub>K P n\<^esub>)\<rbrakk>
        \<Longrightarrow> x^\<^bsup>K m\<^esup> = x^\<^bsup>(O\<^bsub>K P n\<^esub>) m\<^esup>" 
apply (frule ring_n_pd[of "n" "P"])
apply (induct_tac m) apply simp
 apply (simp add:one_in_ring_n_pd_one_K)

apply simp
 apply (frule_tac n = na in Ring.npClose[of "O\<^bsub>K P n\<^esub>" "x"], assumption+)
 apply (simp add:ring_n_tOp_K_tOp)
done   

lemma (in Corps) prime_n_pd_prime:"\<lbrakk>distinct_pds K n P; j \<le> n\<rbrakk> \<Longrightarrow>  
              prime_ideal (O\<^bsub>K P n\<^esub>) (P\<^bsub>K P n\<^esub> j)"
apply (subst prime_ideal_def)
 apply (rule conjI)
 apply (simp add:ideal_def)
 apply (rule conjI)
 apply (rule aGroup.asubg_test)
 apply (frule ring_n_pd[of "n" "P"], simp add:Ring.ring_is_ag)
 apply (rule subsetI, simp add:prime_n_pd_def)
 apply (subgoal_tac "\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub> \<in> P\<^bsub>K P n\<^esub> j")
 apply blast
 
 apply (simp add:zero_in_ring_n_pd_zero_K)
 apply (simp add:prime_n_pd_def)
 apply (simp add: ring_n_pd_def Sr_def) 
 apply (cut_tac field_is_ring, simp add:Ring.ring_zero)
 apply (rule conjI) apply (rule allI, rule impI)
 apply (cut_tac P = "P ja" in representative_of_pd_valuation,
        simp add:distinct_pds_def, simp add:value_of_zero)
 apply (cut_tac P = "P j" in representative_of_pd_valuation,
        simp add:distinct_pds_def, simp add:value_of_zero)
 apply (simp add:ant_0[THEN sym]) 

 apply (rule ballI)+  
 apply (simp add:prime_n_pd_def) apply (erule conjE)+ 
 apply (frule ring_n_pd [of "n" "P"], frule Ring.ring_is_ag[of "O\<^bsub>K P n\<^esub>"])
 apply (frule_tac x = b in aGroup.ag_mOp_closed[of "O\<^bsub>K P n\<^esub>"], assumption+)
 apply (simp add:aGroup.ag_pOp_closed)
  apply (thin_tac "Ring (O\<^bsub>K P n\<^esub>)") apply (thin_tac "aGroup (O\<^bsub>K P n\<^esub>)")
 apply (simp add:ring_n_pd_def Sr_def)
 apply (erule conjE)+
 apply (cut_tac v = "\<nu>\<^bsub>K (P j)\<^esub>" and x = a and y = "-\<^sub>a b" in 
        amin_le_plus) 
 apply (rule_tac P = "P j" in representative_of_pd_valuation, 
        simp add:distinct_pds_def)
 apply assumption+
 apply (cut_tac P = "P j" in representative_of_pd_valuation) 
 apply (simp add:distinct_pds_def)
 apply (frule_tac x = "(\<nu>\<^bsub>K (P j)\<^esub>) a" and y = "(\<nu>\<^bsub>K (P j)\<^esub>) (-\<^sub>a b)" in 
         amin_gt[of "0"])
 apply (simp add:val_minus_eq)

apply (frule_tac y = "amin ((\<nu>\<^bsub>K (P j)\<^esub>) a) ((\<nu>\<^bsub>K (P j)\<^esub>) (-\<^sub>a b))" and
 z = "(\<nu>\<^bsub>K (P j)\<^esub>) ( a \<plusminus> -\<^sub>a b)" in aless_le_trans[of "0"], assumption+)

apply (rule ballI)+
 apply (frule ring_n_pd [of "n" "P"])
 apply (frule_tac x = r and y = x in Ring.ring_tOp_closed[of "O\<^bsub>K P n\<^esub>"], 
        assumption+)
 apply (simp add:prime_n_pd_def)
 apply (cut_tac P = "P j" in representative_of_pd_valuation,
        simp add:distinct_pds_def)
 apply (thin_tac "Ring (O\<^bsub>K P n\<^esub>)") 
 apply (simp add:prime_n_pd_def ring_n_pd_def Sr_def, (erule conjE)+,
        simp add:val_t2p)
 apply (subgoal_tac "0 \<le> ((\<nu>\<^bsub>K (P j)\<^esub>) r)")
 apply (simp add:aadd_pos_poss, simp) 

 apply (rule conjI,
        rule contrapos_pp, simp+,
        simp add:prime_n_pd_def,
        (erule conjE)+, simp add: one_in_ring_n_pd_one_K,
        simp add:distinct_pds_def, (erule conjE)+,
        cut_tac representative_of_pd_valuation[of "P j"],
        simp add:value_of_one, simp) 

apply ((rule ballI)+, rule impI)
 apply (rule contrapos_pp, simp+, erule conjE,
        simp add:prime_n_pd_def, (erule conjE)+,
        simp add:ring_n_pd_def Sr_def, (erule conjE)+, 
        simp add:aneg_less,
        frule_tac x = "(\<nu>\<^bsub>K (P j)\<^esub>) x" in ale_antisym[of _ "0"], simp,
        frule_tac x = "(\<nu>\<^bsub>K (P j)\<^esub>) y" in ale_antisym[of _ "0"], simp)

 apply (simp add:distinct_pds_def, (erule conjE)+,
        cut_tac representative_of_pd_valuation[of "P j"],
        simp add:val_t2p aadd_0_l,
        simp)
done 

lemma (in Corps) n_eq_val_eq_idealTr:
"\<lbrakk>distinct_pds K n P; x \<in> carrier (O\<^bsub>K P n\<^esub>); y \<in> carrier (O\<^bsub>K P n\<^esub>); 
\<forall>j \<le> n. ((\<nu>\<^bsub>K (P j)\<^esub>) x) \<le> ((\<nu>\<^bsub>K (P j)\<^esub>) y)\<rbrakk> \<Longrightarrow> Rxa (O\<^bsub>K P n\<^esub>) y \<subseteq> Rxa (O\<^bsub>K P n\<^esub>) x"
apply (subgoal_tac "\<forall>j \<le> n. valuation K (\<nu>\<^bsub>K (P j)\<^esub>)")
 apply (case_tac "x = \<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>",
        simp add:zero_in_ring_n_pd_zero_K)
 apply (simp add:value_of_zero)
 apply (subgoal_tac "y = \<zero>", simp,
        drule_tac a = n in forall_spec, simp,
        drule_tac a=n in forall_spec, simp)
 apply (cut_tac inf_ge_any[of "(\<nu>\<^bsub>K (P n)\<^esub>) y"],
        frule ale_antisym[of "(\<nu>\<^bsub>K (P n)\<^esub>) y" "\<infinity>"], assumption+)
 apply (rule value_inf_zero, assumption+)
 apply (simp add:mem_ring_n_pd_mem_K, assumption)
       
apply (frule ring_n_pd[of n P])
 apply (subgoal_tac "\<forall>j\<le>n. 0 \<le> ((\<nu>\<^bsub>K (P j)\<^esub>) (y \<cdot>\<^sub>r (x\<^bsup>\<hyphen>K\<^esup>)))")
 apply (subgoal_tac "(y \<cdot>\<^sub>r (x\<^bsup>\<hyphen>K\<^esup>)) \<in> carrier (O\<^bsub>K P n\<^esub>)")
 apply (cut_tac field_frac_mul[of "y" "x"],
        frule Ring.rxa_in_Rxa[of "O\<^bsub>K P n\<^esub>" "x" "y \<cdot>\<^sub>r (x\<^bsup>\<hyphen>K\<^esup>)"], assumption+, 
        simp add:ring_n_pd_tOp_K_tOp[THEN sym],
        frule Ring.principal_ideal[of "O\<^bsub>K P n\<^esub>" "x"], assumption+) 
 
 apply (cut_tac Ring.ideal_cont_Rxa[of "O\<^bsub>K P n\<^esub>" "(O\<^bsub>K P n\<^esub>) \<diamondsuit>\<^sub>p x" "y"],
        assumption+,
        simp add:mem_ring_n_pd_mem_K,
        simp add:mem_ring_n_pd_mem_K,
        simp add:zero_in_ring_n_pd_zero_K) 
 apply (frule Ring.rxa_in_Rxa[of "O\<^bsub>K P n\<^esub>" "x" "y \<cdot>\<^sub>r (x\<^bsup>\<hyphen>K\<^esup>)"], assumption+,
        simp add:ring_n_pd_def Sr_def,
        (erule conjE)+,
        cut_tac field_is_ring, rule Ring.ring_tOp_closed, assumption+,
        cut_tac invf_closed1[of x], simp, simp,
        simp add:ring_n_pd_def Sr_def)
 apply (cut_tac Ring.ring_tOp_closed, assumption+,
        cut_tac field_is_ring, assumption+, simp+,
        cut_tac invf_closed1[of x], simp, simp)

 apply (rule allI, rule impI, drule_tac a = j in forall_spec, assumption+,
        cut_tac invf_closed1[of x], simp, erule conjE)
 apply (subst val_t2p [where v="\<nu>\<^bsub>K P j\<^esub>"], simp,
        rule mem_ring_n_pd_mem_K[of "n" "P" "y"], assumption+,
        frule_tac x = j in spec, simp,
        simp add:zero_in_ring_n_pd_zero_K)
 apply (subst value_of_inv [where v="\<nu>\<^bsub>K P j\<^esub>"], simp,
        simp add:ring_n_pd_def Sr_def, assumption+)
 apply (frule_tac x = "(\<nu>\<^bsub>K (P j)\<^esub>) x" and y = "(\<nu>\<^bsub>K (P j)\<^esub>) y" in ale_diff_pos,
        simp add:diff_ant_def,
        simp add:mem_ring_n_pd_mem_K[of "n" "P" "x"] zero_in_ring_n_pd_zero_K)

apply (rule allI, rule impI,
       simp add:distinct_pds_def, (erule conjE)+,
       rule_tac P = "P j" in representative_of_pd_valuation, simp)
done
 
lemma (in Corps) n_eq_val_eq_ideal:"\<lbrakk>distinct_pds K n P; x \<in> carrier (O\<^bsub>K P n\<^esub>);
      y \<in> carrier (O\<^bsub>K P n\<^esub>); \<forall>j \<le> n.((\<nu>\<^bsub>K (P j)\<^esub>) x) = ((\<nu>\<^bsub>K (P j)\<^esub>) y)\<rbrakk> \<Longrightarrow>  
                 Rxa (O\<^bsub>K P n\<^esub>) x = Rxa (O\<^bsub>K P n\<^esub>) y"
apply (rule equalityI)
 apply (subgoal_tac "\<forall>j\<le> n. (\<nu>\<^bsub>K (P j)\<^esub>) y \<le> ((\<nu>\<^bsub>K (P j)\<^esub>) x)")
 apply (rule n_eq_val_eq_idealTr, assumption+)
 apply (rule allI, rule impI, simp)

 apply (subgoal_tac "\<forall>j\<le> n. (\<nu>\<^bsub>K (P j)\<^esub>) x \<le> ((\<nu>\<^bsub>K (P j)\<^esub>) y)")
 apply (rule n_eq_val_eq_idealTr, assumption+)
 apply (rule allI, rule impI)
 apply simp
done  
 
definition
  mI_gen :: "[_ , nat \<Rightarrow> ('r \<Rightarrow> ant) set, nat, 'r set] \<Rightarrow> 'r" where
  "mI_gen K P n I = (SOME x. x \<in> I \<and> 
                             (\<forall>j \<le> n. (\<nu>\<^bsub>K (P j)\<^esub>) x = LI K (\<nu>\<^bsub>K (P j)\<^esub>) I))"

definition
  mL :: "[_, nat \<Rightarrow> ('r \<Rightarrow> ant) set, 'r set, nat] \<Rightarrow> int" where
  "mL K P I j = tna (LI K (\<nu>\<^bsub>K (P j)\<^esub>) I)"

lemma (in Corps) mI_vals_nonempty:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; j\<le>n\<rbrakk>
    \<Longrightarrow> (\<nu>\<^bsub>K (P j)\<^esub>) ` I \<noteq> {}"
apply (frule ring_n_pd[of "n" "P"])
apply (frule Ring.ideal_zero [of "O\<^bsub>K P n\<^esub>" "I"], assumption+)

apply (simp add:image_def)
apply blast
done

lemma (in Corps) mI_vals_LB:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; j \<le> n\<rbrakk> \<Longrightarrow>
       ((\<nu>\<^bsub>K (P j)\<^esub>) `I) \<subseteq> LBset (ant 0)"
apply (rule subsetI)
apply (simp add:image_def, erule bexE)
 apply (frule ring_n_pd[of "n" "P"])
 apply (frule_tac h = xa in Ring.ideal_subset[of "O\<^bsub>K P n\<^esub>" "I"], assumption+)
 apply (thin_tac "ideal (O\<^bsub>K P n\<^esub>) I")
 apply (thin_tac "Ring (O\<^bsub>K P n\<^esub>)")
 apply (simp add: ring_n_pd_def Sr_def) apply (erule conjE)+ 
 apply (drule_tac a = j in forall_spec, simp)
 
apply (simp add:LBset_def ant_0)
done

lemma (in Corps) mL_hom:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; 
      I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>)\<rbrakk> \<Longrightarrow> 
      \<forall>j \<le> n. mL K P I j \<in> Zset" 
apply (rule allI, rule impI)
 apply (simp add:mL_def LI_def)
 apply (simp add:Zset_def)
done

lemma (in Corps) ex_Zleast_in_mI:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; j \<le> n\<rbrakk>
      \<Longrightarrow> \<exists>x\<in>I. (\<nu>\<^bsub>K (P j)\<^esub>) x = LI K (\<nu>\<^bsub>K (P j)\<^esub>) I"
apply (frule_tac j = j in mI_vals_nonempty[of "n" "P" "I"], assumption+)
 apply (frule_tac j = j in mI_vals_LB[of "n" "P" "I"], assumption+)
 apply (frule_tac A = "(\<nu>\<^bsub>K (P j)\<^esub>) ` I" and z = 0 in AMin_mem, assumption+)
 apply (simp add:LI_def)
 apply (thin_tac "(\<nu>\<^bsub>K (P j)\<^esub>) ` I \<subseteq> LBset (ant 0)")
 apply (simp add:image_def, erule bexE)
 apply (drule sym)
 apply blast
done 

lemma (in Corps) val_LI_pos:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; 
       I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; j \<le> n\<rbrakk> \<Longrightarrow> 0 \<le> LI K (\<nu>\<^bsub>K (P j)\<^esub>) I"
apply (frule_tac j = j in mI_vals_nonempty[of n P I], assumption+)
 apply (frule_tac j = j in mI_vals_LB[of n P I], assumption+)
 apply (frule_tac A = "(\<nu>\<^bsub>K (P j)\<^esub>) ` I" and z = 0 in AMin_mem, assumption+)
 apply (simp add:LI_def)
apply (frule subsetD[of "(\<nu>\<^bsub>K (P j)\<^esub>) ` I" "LBset (ant 0)" "AMin ((\<nu>\<^bsub>K (P j)\<^esub>) ` I)"], assumption+)
apply (simp add:LBset_def ant_0)
done

lemma (in Corps) val_LI_noninf:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; 
       I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; j \<le> n\<rbrakk> \<Longrightarrow> LI K (\<nu>\<^bsub>K (P j)\<^esub>) I \<noteq> \<infinity>"
 apply (frule_tac j = j in mI_vals_nonempty[of "n" "P" "I"], assumption+)
 apply (frule_tac j = j in mI_vals_LB[of "n" "P" "I"], assumption+)
 apply (frule_tac A = "(\<nu>\<^bsub>K (P j)\<^esub>) ` I" and z = 0 in AMin, assumption+)
 apply (thin_tac "(\<nu>\<^bsub>K (P j)\<^esub>) ` I \<subseteq> LBset (ant 0)", 
        thin_tac "(\<nu>\<^bsub>K (P j)\<^esub> ) ` I \<noteq> {}")
 apply (frule ring_n_pd[of "n" "P"])
 apply (frule Ring.ideal_zero[of "O\<^bsub>K P n\<^esub>" "I"], assumption+)
 apply (erule conjE, simp add:LI_def)
 apply (frule singleton_sub[of "\<zero>\<^bsub>O\<^bsub>K P n\<^esub>\<^esub>" "I"])
 apply (frule sets_not_eq[of "I" "{\<zero>\<^bsub>O\<^bsub>K P n\<^esub>\<^esub>}"],
        assumption+, erule bexE)
 apply (simp add:zero_in_ring_n_pd_zero_K)
 apply (subgoal_tac "\<exists>x\<in>I. AMin ((\<nu>\<^bsub>K (P j)\<^esub>) ` I) = (\<nu>\<^bsub>K (P j)\<^esub>) x",
        erule bexE) apply simp
 apply (drule_tac x = a in bspec, assumption)
 apply (thin_tac "AMin ((\<nu>\<^bsub>K (P j)\<^esub>) ` I) = (\<nu>\<^bsub>K (P j)\<^esub>) x")

 apply (frule_tac h = a in Ring.ideal_subset[of "O\<^bsub>K P n\<^esub>" "I"], assumption+)
 apply (frule_tac x = a in mem_ring_n_pd_mem_K[of n P], assumption+)
 apply (simp add:distinct_pds_def, (erule conjE)+)
 apply (cut_tac representative_of_pd_valuation[of "P j"])
 defer apply simp apply blast
 apply (frule_tac x = a in val_nonzero_z[of "\<nu>\<^bsub>K (P j)\<^esub>"], assumption+,
        erule exE, simp)
 apply (thin_tac "\<forall>l \<le> n. \<forall>m \<le> n. l \<noteq> m \<longrightarrow> P l \<noteq> P m",
        thin_tac "(\<nu>\<^bsub>K (P j)\<^esub>) a = ant z")

 apply (rule contrapos_pp, simp+)
 apply (cut_tac x = "ant z" in inf_ge_any) 
 apply (frule_tac x = "ant z" in ale_antisym[of _ "\<infinity>"], assumption+)
 apply simp 
done 

lemma (in Corps) Zleast_in_mI_pos:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; 
       I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; j \<le> n\<rbrakk> \<Longrightarrow> 0 \<le> mL K P I j"
apply (simp add:mL_def)
apply (frule ex_Zleast_in_mI[of "n" "P" "I" "j"], assumption+,
       erule bexE, frule sym, thin_tac "(\<nu>\<^bsub>K (P j)\<^esub>) x = LI K (\<nu>\<^bsub>K (P j)\<^esub>) I")
apply (subgoal_tac "LI K (\<nu>\<^bsub>K (P j)\<^esub>) I \<noteq> \<infinity>", simp)
apply (thin_tac "LI K (\<nu>\<^bsub>K (P j)\<^esub>) I = (\<nu>\<^bsub>K (P j)\<^esub>) x")

 apply (frule ring_n_pd[of "n" "P"])
 apply (frule_tac h = x in Ring.ideal_subset[of "O\<^bsub>K P n\<^esub>" "I"], assumption+)
 apply (thin_tac "ideal (O\<^bsub>K P n\<^esub>) I")
 apply (thin_tac "Ring (O\<^bsub>K P n\<^esub>)")
 apply (simp add: ring_n_pd_def Sr_def) apply (erule conjE)
 apply (drule_tac a = j in forall_spec, assumption)
 apply (simp add:apos_tna_pos)
apply (rule val_LI_noninf, assumption+)
done 

lemma (in Corps) Zleast_mL_I:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; j \<le> n;
   I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; x \<in> I\<rbrakk> \<Longrightarrow> ant (mL K P I j) \<le> ((\<nu>\<^bsub>K (P j)\<^esub>) x)"
apply (frule val_LI_pos[of "n" "P" "I" "j"], assumption+)
apply (frule apos_neq_minf[of "LI K (\<nu>\<^bsub>K (P j)\<^esub>) I"])
apply (frule val_LI_noninf[of "n" "P" "I" "j"], assumption+)
apply (simp add:mL_def LI_def)
apply (simp add:ant_tna)
apply (frule Zleast_in_mI_pos[of "n" "P" "I" "j"], assumption+)

apply (frule mI_vals_nonempty[of "n" "P" "I" "j"], assumption+)
apply (frule mI_vals_LB[of "n" "P" "I" "j"], assumption+)
apply (frule AMin[of "(\<nu>\<^bsub>K (P j)\<^esub>) `I" "0"], assumption+)
 apply (erule conjE)
apply (frule Zleast_in_mI_pos[of "n" "P" "I" "j"], assumption+)
 apply (simp add:mL_def LI_def)
done 

lemma (in Corps) Zleast_LI:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; j \<le> n;
   I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; x \<in> I\<rbrakk> \<Longrightarrow> (LI K (\<nu>\<^bsub>K (P j)\<^esub>) I) \<le> ((\<nu>\<^bsub>K (P j)\<^esub>) x)"
apply (frule mI_vals_nonempty[of "n" "P" "I" "j"], assumption+)
apply (frule mI_vals_LB[of "n" "P" "I" "j"], assumption+)
apply (frule AMin[of "(\<nu>\<^bsub>K (P j)\<^esub>) `I" "0"], assumption+)
 apply (erule conjE)
apply (simp add:LI_def)
done

lemma (in Corps) mpdiv_vals_nonequiv:"distinct_pds K n P \<Longrightarrow> 
             vals_nonequiv K n (\<lambda>j. \<nu>\<^bsub>K (P j)\<^esub>) "  
apply (simp add:vals_nonequiv_def)
 apply (rule conjI)
 apply (simp add:valuations_def)
 apply (rule allI, rule impI)
 apply (rule representative_of_pd_valuation, 
        simp add:distinct_pds_def) 
apply  ((rule allI, rule impI)+, rule impI)
 apply (simp add:distinct_pds_def, erule conjE)
 apply (rotate_tac 4) apply (
        drule_tac a = j in forall_spec, assumption)
 apply (rotate_tac -1,
        drule_tac a = l in forall_spec, assumption, simp)
 apply (simp add:distinct_p_divisors)
done

definition
  KbaseP :: "[_, nat \<Rightarrow> ('r \<Rightarrow> ant) set, nat] \<Rightarrow> 
                                          (nat \<Rightarrow> 'r) \<Rightarrow> bool"  where
  "KbaseP K P n f \<longleftrightarrow> (\<forall>j \<le> n. f j \<in> carrier K) \<and> 
     (\<forall>j \<le> n. \<forall>l \<le> n. (\<nu>\<^bsub>K (P j)\<^esub>) (f l) =  (\<delta>\<^bsub>j l\<^esub>))"

definition
  Kbase :: "[_, nat, nat \<Rightarrow> ('r \<Rightarrow> ant) set] 
               \<Rightarrow> (nat \<Rightarrow> 'r)" ("(3Kb\<^bsub>_ _ _\<^esub>)" [95,95,96]95) where
  "Kb\<^bsub>K n P \<^esub> = (SOME f. KbaseP K P n f)"

lemma (in Corps) KbaseTr:"distinct_pds K n P \<Longrightarrow>  \<exists>f. KbaseP K P n f"
apply (simp add: KbaseP_def)
 apply (frule mpdiv_vals_nonequiv[of "n" "P"])
 apply (case_tac "n = 0")
  apply (simp add:vals_nonequiv_def valuations_def)
  apply (simp add:distinct_pds_def) 
  apply (frule n_val_n_val1[of "P 0"])
  apply (frule n_val_surj[of "\<nu>\<^bsub>K (P 0)\<^esub>"])
  apply (erule bexE)
  apply (subgoal_tac " ((\<lambda>j\<in>{0::nat}. x) (0::nat)) \<in> carrier K \<and> 
         (\<nu>\<^bsub>K (P 0)\<^esub>) ((\<lambda>j\<in>{0::nat}. x) (0::nat)) = (\<delta>\<^bsub>0 0\<^esub>)") 
  apply blast
  apply (rule conjI)
 apply simp apply (simp add:Kronecker_delta_def)
 apply (cut_tac Approximation1_5[of "n - Suc 0" "\<lambda>j. \<nu>\<^bsub>K (P j)\<^esub>"])
 apply simp 
 apply simp+
 apply (rule allI, rule impI)
 apply (rule n_val_n_val1 )
 apply (simp add:distinct_pds_def)
done

lemma (in Corps) KbaseTr1:"distinct_pds K n P \<Longrightarrow>  KbaseP K P n (Kb\<^bsub>K n P \<^esub>)"
apply (subst Kbase_def)
apply (frule KbaseTr[of n P])
apply (erule exE)
apply (simp add:someI)
done 

lemma (in Corps) Kbase_hom:"distinct_pds K n P \<Longrightarrow> 
                       \<forall>j \<le> n. (Kb\<^bsub>K n P\<^esub>) j \<in> carrier K"       
apply (frule KbaseTr1[of "n" "P"])
apply (simp add:KbaseP_def)
done

lemma (in Corps) Kbase_Kronecker:"distinct_pds K n P \<Longrightarrow> 
      \<forall>j \<le> n. \<forall>l \<le> n. (\<nu>\<^bsub>K (P j)\<^esub>) ((Kb\<^bsub>K n P\<^esub>) l) = \<delta>\<^bsub>j l\<^esub>"     
apply (frule KbaseTr1[of n P])
apply (simp add:KbaseP_def)
done   

lemma (in Corps) Kbase_nonzero:"distinct_pds K n P \<Longrightarrow> 
                        \<forall>j \<le> n. (Kb\<^bsub>K n P\<^esub>) j \<noteq> \<zero>"
apply (rule allI, rule impI)
 apply (frule Kbase_Kronecker[of n P])
 apply (subgoal_tac "(\<nu>\<^bsub>K (P j)\<^esub>) ((Kb\<^bsub>K n P\<^esub>) j) = \<delta>\<^bsub>j j\<^esub>")
 apply (thin_tac "\<forall>j\<le>n. (\<forall>l\<le>n. ((\<nu>\<^bsub>K P j\<^esub>) ((Kb\<^bsub>K n P\<^esub>) l)) = \<delta>\<^bsub>j l\<^esub>)")
 apply (simp add:Kronecker_delta_def)
 apply (rule contrapos_pp, simp+)
 apply (cut_tac P = "P j" in representative_of_pd_valuation)  
 apply (simp add:distinct_pds_def)
 apply (simp only:value_of_zero, simp only:ant_1[THEN sym],
        frule sym, thin_tac " \<infinity> = ant 1", simp del:ant_1)
apply simp
done

lemma (in Corps) Kbase_hom1:"distinct_pds K n P \<Longrightarrow> 
                    \<forall>j \<le> n. (Kb\<^bsub>K n P\<^esub>) j \<in> carrier K - {\<zero>}"
by(simp add:Kbase_nonzero Kbase_hom)

definition
  Zl_mI :: "[_, nat \<Rightarrow> ('b \<Rightarrow> ant) set, 'b set]
                         \<Rightarrow> nat \<Rightarrow> 'b" where
  "Zl_mI K P I j = (SOME x. (x \<in> I \<and> ( (\<nu>\<^bsub>K (P j)\<^esub>) x = LI K (\<nu>\<^bsub>K (P j)\<^esub>) I)))"

lemma (in Corps) value_Zl_mI:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; j \<le> n\<rbrakk>
 \<Longrightarrow>  (Zl_mI K P I j \<in> I) \<and> (\<nu>\<^bsub>K (P j)\<^esub>) (Zl_mI K P I j) = LI K (\<nu>\<^bsub>K (P j)\<^esub>) I"
apply (subgoal_tac "\<exists>x. (x \<in> I \<and> ((\<nu>\<^bsub>K (P j)\<^esub>) x = LI K (\<nu>\<^bsub>K (P j)\<^esub>) I))")
apply (subst Zl_mI_def)+
apply (rule someI2_ex, assumption+) 
apply (frule ex_Zleast_in_mI[of "n" "P" "I" "j"], assumption+)
apply (erule bexE, blast) 
done

lemma (in Corps) Zl_mI_nonzero:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; 
      I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; j \<le> n\<rbrakk> \<Longrightarrow>  Zl_mI K P I j \<noteq> \<zero>"
apply (case_tac "n = 0")
apply (simp add:distinct_pds_def) 
 apply (frule representative_of_pd_valuation[of "P 0"])
 apply (subgoal_tac "O\<^bsub>K P 0\<^esub> = Vr K (\<nu>\<^bsub>K (P 0)\<^esub>)")
 apply (subgoal_tac "Zl_mI K P I 0 = Ig K (\<nu>\<^bsub>K (P 0)\<^esub>) I")  
 apply simp apply (simp add:Ig_nonzero)
 apply (simp add:Ig_def Zl_mI_def)
 apply (simp add:ring_n_pd_def Vr_def)

 apply (simp)
 apply (frule value_Zl_mI[of n P I j], assumption+)
 apply (erule conjE)
 apply (rule contrapos_pp, simp+)
 apply (frule distinct_pds_valuation1[of n j P], assumption+)
 apply (simp add:value_of_zero)
 apply (simp add:zero_in_ring_n_pd_zero_K)
 apply (frule singleton_sub[of "\<zero>" "I"], 
        frule sets_not_eq[of "I" "{\<zero>}"], assumption,
        erule bexE, simp)
 apply (frule_tac x = a in Zleast_mL_I[of "n" "P" "I" "j"], assumption+)
 apply (frule_tac x = a in val_nonzero_z[of "\<nu>\<^bsub>K (P j)\<^esub>"])
 apply (frule ring_n_pd[of "n" "P"])
 apply (frule_tac h = a in Ring.ideal_subset[of "O\<^bsub>K P n\<^esub>" "I"], assumption+)
 apply (simp add:mem_ring_n_pd_mem_K) apply assumption

apply (simp add:zero_in_ring_n_pd_zero_K) apply assumption
apply (frule val_LI_noninf[THEN not_sym, of "n" "P" "I" "j"], assumption+)
 apply (simp add:zero_in_ring_n_pd_zero_K) apply assumption
 apply simp
done
 
lemma (in Corps) Zl_mI_mem_K:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; l \<le> n\<rbrakk>
       \<Longrightarrow> (Zl_mI K P I l) \<in> carrier K"
apply (frule value_Zl_mI[of "n" "P" "I" "l"], assumption+)
apply (erule conjE) 
 apply (frule ring_n_pd[of "n" "P"])
 apply (frule Ring.ideal_subset[of "O\<^bsub>K P n\<^esub>" "I" "Zl_mI K P I l"], assumption+)
 apply (simp add:mem_ring_n_pd_mem_K[of "n" "P" "Zl_mI K P I l"])
done

definition
  mprod_exp :: "[_, nat \<Rightarrow> int, nat \<Rightarrow> 'b, nat] 
              \<Rightarrow> 'b" where
  "mprod_exp K e f n = nprod K (\<lambda>j. ((f j)\<^bsub>K\<^esub>\<^bsup>(e j)\<^esup>)) n"

lemma (in Corps) mprod_expR_memTr:"(\<forall>j\<le>n. f j \<in> carrier K)  \<longrightarrow>  
                      mprod_expR K e f n \<in> carrier K"
apply (cut_tac field_is_ring)
apply (induct_tac n)
 apply (rule impI, simp) 
 apply (simp add:mprod_expR_def)
 apply (cut_tac Ring.npClose[of K "f 0" "e 0"], assumption+)

apply (rule impI) 
 apply simp
 apply (subst Ring.mprodR_Suc, assumption+)
 apply (simp)
 apply (simp)
 apply (rule Ring.ring_tOp_closed[of K], assumption+)
 apply (rule Ring.npClose, assumption+) 
 apply simp 
done

lemma (in Corps) mprod_expR_mem:"\<forall>j \<le> n. f j \<in> carrier K \<Longrightarrow> 
           mprod_expR K e f n \<in> carrier K"
apply (cut_tac field_is_ring) 
apply (cut_tac Ring.mprod_expR_memTr[of K e n f])
apply simp
apply (subgoal_tac "f \<in> {j. j \<le> n} \<rightarrow> carrier K", simp+)
done 

lemma (in Corps) mprod_Suc:"\<lbrakk> \<forall>j\<le>(Suc n). e j \<in> Zset; 
                \<forall>j \<le> (Suc n). f j \<in> (carrier K - {\<zero>})\<rbrakk> \<Longrightarrow> 
 mprod_exp K e f (Suc n) = (mprod_exp K e f n) \<cdot>\<^sub>r ((f (Suc n))\<^bsub>K\<^esub>\<^bsup>(e (Suc n))\<^esup>)"
apply (simp add:mprod_exp_def)
done

lemma (in Corps) mprod_memTr:"
 (\<forall>j \<le> n. e j \<in> Zset) \<and> (\<forall>j \<le> n. f j \<in> ((carrier K) - {\<zero>})) \<longrightarrow> 
       (mprod_exp K e f n) \<in> ((carrier K) - {\<zero>})" 
apply (induct_tac n)
 apply (simp, rule impI, (erule conjE)+,
        simp add:mprod_exp_def, simp add:npowf_mem,
        simp add:field_potent_nonzero1) 
apply (rule impI, simp, erule conjE,
       cut_tac field_is_ring, cut_tac field_is_idom,
       erule conjE, simp add:mprod_Suc)
 apply (rule conjI)
 apply (rule Ring.ring_tOp_closed[of "K"], assumption+,
        simp add:npowf_mem)
 apply (rule Idomain.idom_tOp_nonzeros, assumption+,
        simp add:npowf_mem, assumption,
        simp add:field_potent_nonzero1) 
done

lemma (in Corps) mprod_mem:"\<lbrakk>\<forall>j \<le> n. e j \<in> Zset; \<forall>j \<le> n. f j \<in> ((carrier K) - {\<zero>})\<rbrakk> \<Longrightarrow>  (mprod_exp K e f n) \<in> ((carrier K) - {\<zero>})"
apply (cut_tac mprod_memTr[of n e f]) apply simp
done

lemma (in Corps) mprod_mprodR:"\<lbrakk>\<forall>j \<le> n. e j \<in> Zset; \<forall>j \<le> n. 0 \<le> (e j); 
 \<forall>j \<le> n. f j \<in> ((carrier K) - {\<zero>})\<rbrakk> \<Longrightarrow> 
              mprod_exp K e f n = mprod_expR K (nat o e) f n"
apply (cut_tac field_is_ring)
apply (simp add:mprod_exp_def mprod_expR_def) 
apply (rule Ring.nprod_eq, assumption+)
 apply (rule allI, rule impI, simp add:npowf_mem)
 apply (rule allI, rule impI, rule Ring.npClose, assumption+, simp)
apply (rule allI, rule impI)
 apply (simp add:npowf_def)
done

subsection "Representation of an ideal I as a product of prime ideals"

lemma (in Corps) ring_n_mprod_mprodRTr:"distinct_pds K n P \<Longrightarrow> 
       (\<forall>j \<le> m. e j \<in> Zset) \<and> (\<forall>j \<le> m. 0 \<le> (e j)) \<and> 
       (\<forall>j \<le> m. f j \<in> carrier (O\<^bsub>K P n\<^esub>)-{\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}) \<longrightarrow> 
        mprod_exp K e f m = mprod_expR (O\<^bsub>K P n\<^esub>) (nat o e) f m"
apply (frule ring_n_pd[of n P])
apply (induct_tac m) 
 apply (rule impI, (erule conjE)+,
        simp add:mprod_exp_def mprod_expR_def)
 apply (erule conjE, simp add:npowf_def, simp add:ring_n_exp_K_exp) 

apply (rule impI, (erule conjE)+, simp)  
 apply (subst mprod_Suc, assumption+,
        rule allI, rule impI,
        simp add:mem_ring_n_pd_mem_K,
        simp add:zero_in_ring_n_pd_zero_K)
  apply (subst Ring.mprodR_Suc, assumption+,
         simp add:cmp_def,
         simp)
  apply (simp add:ring_n_pd, simp add:npowf_def, 
         simp add:ring_n_exp_K_exp) 
 apply (subst ring_n_tOp_K_tOp, assumption+,
        rule Ring.mprod_expR_mem, simp add:ring_n_pd,
        simp,
        simp)
 apply (rule Ring.npClose, simp add:ring_n_pd, simp, simp)
done

lemma (in Corps) ring_n_mprod_mprodR:"\<lbrakk>distinct_pds K n P; \<forall>j \<le> m. e j \<in> Zset;
 \<forall>j \<le> m. 0 \<le> (e j); \<forall>j \<le> m. f j \<in> carrier (O\<^bsub>K P n\<^esub>)-{\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}\<rbrakk> 
 \<Longrightarrow>  mprod_exp K e f m = mprod_expR (O\<^bsub>K P n\<^esub>) (nat o e) f m"
apply (simp add:ring_n_mprod_mprodRTr)
done

lemma (in Corps) value_mprod_expTr:"valuation K v  \<Longrightarrow> 
 (\<forall>j \<le> n. e j \<in> Zset) \<and> (\<forall>j \<le> n. f j \<in> (carrier K - {\<zero>})) \<longrightarrow>
 v (mprod_exp K e f n) =  ASum  (\<lambda>j. (e j) *\<^sub>a (v (f j))) n"  
apply (induct_tac n)
 apply simp
 apply (rule impI, erule conjE)
 apply(simp add:mprod_exp_def val_exp) 

apply (rule impI, erule conjE)
 apply simp
 apply (subst mprod_Suc, assumption+)
 apply (rule allI, rule impI, simp)
 apply (subst val_t2p[of v], assumption+)
 apply (cut_tac n = "n" in mprod_mem[of _ e f],
        (rule allI, rule impI, simp)+, simp)
 apply (simp add:npowf_mem, simp add:field_potent_nonzero1)
 apply (simp add:val_exp[THEN sym, of "v"]) 
done 

lemma (in Corps) value_mprod_exp:"\<lbrakk>valuation K v; \<forall>j \<le> n. e j \<in> Zset; 
       \<forall>j \<le> n. f j \<in> (carrier K - {\<zero>})\<rbrakk> \<Longrightarrow> 
     v (mprod_exp K e f n) = ASum (\<lambda>j. (e j) *\<^sub>a (v (f j))) n"  
apply (simp add:value_mprod_expTr)
done

lemma (in Corps) mgenerator0_1:"\<lbrakk>distinct_pds K (Suc n) P; 
 ideal (O\<^bsub>K P (Suc n)\<^esub>) I; I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P (Suc n)\<^esub>)\<^esub>}; 
 I \<noteq> carrier (O\<^bsub>K P (Suc n)\<^esub>); j \<le> (Suc n)\<rbrakk> \<Longrightarrow>
((\<nu>\<^bsub>K (P j)\<^esub>) (mprod_exp K (mL K P I) (Kb\<^bsub>K (Suc n) P\<^esub>) (Suc n))) = 
                   ((\<nu>\<^bsub>K (P j)\<^esub>) (Zl_mI K P I j))" 
apply (frule distinct_pds_valuation[of j n P], assumption+)
 apply (frule mL_hom[of "Suc n" "P" "I"], assumption+)
 apply (frule Kbase_hom1[of "Suc n" "P"]) 
 apply (frule value_mprod_exp[of "\<nu>\<^bsub>K (P j)\<^esub>" "Suc n" "mL K P I" 
           "Kb\<^bsub>K (Suc n) P\<^esub>"], assumption+)

 apply (simp del:ASum_Suc)
 apply (thin_tac "(\<nu>\<^bsub>K (P j)\<^esub>) (mprod_exp K (mL K P I) (Kb\<^bsub>K (Suc n) P\<^esub>) (Suc n)) =
     ASum (\<lambda>ja. (mL K P I ja) *\<^sub>a (\<nu>\<^bsub>K (P j)\<^esub>) ((Kb\<^bsub>K (Suc n) P\<^esub>) ja)) (Suc n)")
apply (subgoal_tac "ASum (\<lambda>ja. (mL K P I ja) *\<^sub>a 
      ((\<nu>\<^bsub>K (P j)\<^esub>) ((Kb\<^bsub>K (Suc n) P\<^esub>) ja))) (Suc n) = 
                ASum (\<lambda>ja. (mL K P I ja) *\<^sub>a (\<delta>\<^bsub>j ja\<^esub>)) (Suc n)")
apply (simp del:ASum_Suc)
apply (subgoal_tac "\<forall>h \<le> (Suc n). (\<lambda>ja. (mL K P I ja) *\<^sub>a (\<delta>\<^bsub>j ja\<^esub>)) h \<in> Z\<^sub>\<infinity>")
apply (cut_tac eSum_single[of "Suc n" "\<lambda>ja. (mL K P I ja) *\<^sub>a (\<delta>\<^bsub>j ja\<^esub>)" "j"])
 apply simp
 apply (simp add:Kronecker_delta_def asprod_n_0)
 apply (rotate_tac -1, drule not_sym) 
apply (simp add:mL_def[of "K" "P" "I" "j"])

apply (frule val_LI_noninf[of "Suc n" "P" "I" "j"], assumption+)
 apply (rule not_sym, simp, simp)
apply (frule val_LI_pos[of "Suc n" "P" "I" "j"], assumption+,
       rotate_tac -2, frule not_sym, simp, simp)

apply (frule apos_neq_minf[of "LI K (\<nu>\<^bsub>K (P j)\<^esub>) I"])
apply (simp add:ant_tna) 
apply (simp add:value_Zl_mI[of "Suc n" "P" "I" "j"])
apply (rule allI, rule impI)
 apply (simp add:Kdelta_in_Zinf, simp)
 apply (rule ballI, simp)
 apply (simp add:Kronecker_delta_def, erule conjE)
 apply (simp add:asprod_n_0)

apply (rule allI, rule impI) 
 apply (simp add:Kdelta_in_Zinf)

apply (frule  Kbase_Kronecker[of "Suc n" "P"])
 apply (rule ASum_eq,
        rule allI, rule impI,
        simp add:Kdelta_in_Zinf,
        rule allI, rule impI,
        simp add:Kdelta_in_Zinf)
apply (rule allI, rule impI) apply simp
done

lemma (in Corps) mgenerator0_2:"\<lbrakk> 0 < n; distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; 
 I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>); j \<le> n\<rbrakk>  \<Longrightarrow>
((\<nu>\<^bsub>K (P j)\<^esub>) (mprod_exp K (mL K P I) (Kb\<^bsub>K n P\<^esub>) n)) =  ((\<nu>\<^bsub>K (P j)\<^esub>) (Zl_mI K P I j))"
apply (cut_tac mgenerator0_1[of  "n - Suc 0" "P" "I" "j"])
 apply simp+
done

lemma (in Corps) mgenerator1:"\<lbrakk>distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; 
 I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>); j \<le> n\<rbrakk> \<Longrightarrow>
((\<nu>\<^bsub>K (P j)\<^esub>) (mprod_exp K (mL K P I) (Kb\<^bsub>K n P\<^esub>) n)) = ((\<nu>\<^bsub>K (P j)\<^esub>) (Zl_mI K P I j))"
apply (case_tac "n = 0",
       frule value_Zl_mI[of "n" "P" "I" "j"], assumption+,
       frule val_LI_noninf[of "n" "P" "I" "j"], assumption+,
       frule val_LI_pos[of  "n" "P" "I" "j"], assumption+,
       frule apos_neq_minf[of "LI K (\<nu>\<^bsub>K (P j)\<^esub>) I"],
       simp add:distinct_pds_def, erule conjE)  
 apply (cut_tac representative_of_pd_valuation[of "P j"], simp+,
        simp add:mprod_exp_def,
        subst val_exp[THEN sym, of "\<nu>\<^bsub>K (P 0)\<^esub>" "(Kb\<^bsub>K 0 P\<^esub>) 0"], assumption+,
        cut_tac Kbase_hom[of "0" "P"], simp,
        simp add:distinct_pds_def,
        cut_tac Kbase_nonzero[of "0" "P"], simp+,
        simp add:distinct_pds_def) 
 apply (cut_tac Kbase_nonzero[of "0" "P"], simp add:distinct_pds_def) 
 apply (cut_tac Kbase_Kronecker[of "0" "P"], simp add:distinct_pds_def) 
 apply (simp add:Kronecker_delta_def, simp add:mL_def, simp add:ant_tna)
 apply (simp add:distinct_pds_def)+
apply (cut_tac mgenerator0_2[of "n" "P" "I" "j"], simp+)
 apply (simp add:distinct_pds_def) apply simp+
done
    
lemma (in Corps) mgenerator2Tr1:"\<lbrakk>0 < n; j \<le> n; k \<le> n; distinct_pds K n P\<rbrakk> \<Longrightarrow>
      (\<nu>\<^bsub>K (P j)\<^esub>) (mprod_exp K (\<lambda>l. \<gamma>\<^bsub>k l\<^esub> ) (Kb\<^bsub>K n P\<^esub>) n) = (\<gamma>\<^bsub>k j\<^esub>) *\<^sub>a (\<delta>\<^bsub>j j\<^esub>)"
apply (frule distinct_pds_valuation1[of "n" "j" "P"], assumption+)
apply (frule K_gamma_hom[of k n]) 
apply (subgoal_tac "\<forall>j \<le> n. (Kb\<^bsub>K n P\<^esub>) j \<in> carrier K - {\<zero>}")
apply (simp add:value_mprod_exp[of "\<nu>\<^bsub>K (P j)\<^esub>" n "K_gamma k" "(Kb\<^bsub>K n P\<^esub>)"])
apply (subgoal_tac "ASum (\<lambda>ja. (\<gamma>\<^bsub>k ja\<^esub>) *\<^sub>a (\<nu>\<^bsub>K (P j)\<^esub>) ((Kb\<^bsub>K n P\<^esub>) ja)) n
       = ASum (\<lambda>ja. (((\<gamma>\<^bsub>k ja\<^esub>) *\<^sub>a (\<delta>\<^bsub>j ja\<^esub>)))) n")
 apply simp
 apply (subgoal_tac "\<forall>j \<le> n. (\<lambda>ja. (\<gamma>\<^bsub>k ja\<^esub>) *\<^sub>a (\<delta>\<^bsub>j ja\<^esub>)) j \<in> Z\<^sub>\<infinity>")
 apply (cut_tac eSum_single[of n "\<lambda>ja. ((\<gamma>\<^bsub>k ja\<^esub>) *\<^sub>a (\<delta>\<^bsub>j ja\<^esub>))"  "j"], simp)
 apply (rule allI, rule impI, simp add:Kronecker_delta_def, 
        rule impI, simp add:asprod_n_0 Zero_in_aug_inf, assumption+)
 apply (rule ballI, simp)
  apply (simp add:K_gamma_def, rule impI, simp add:Kronecker_delta_def) 
  apply (rule allI, rule impI)
  apply (simp add:Kronecker_delta_def, simp add:K_gamma_def)
 apply (simp add:ant_0 Zero_in_aug_inf)
 apply (cut_tac z_in_aug_inf[of 1], simp add:ant_1) 

 apply (rule ASum_eq)
  apply (rule allI, rule impI)
  apply (simp add:K_gamma_def, simp add:Zero_in_aug_inf) 
  apply (rule impI, rule value_in_aug_inf, assumption+, simp)
  apply (simp add:K_gamma_def Zero_in_aug_inf Kdelta_in_Zinf1)
  apply (rule allI, rule impI)
  apply (simp add:Kbase_Kronecker[of "n" "P"])
  apply (rule Kbase_hom1, assumption+)
done

lemma (in Corps) mgenerator2Tr2:"\<lbrakk>0 < n; j \<le> n; k \<le> n; distinct_pds K n P\<rbrakk> \<Longrightarrow>
     (\<nu>\<^bsub>K (P j)\<^esub>) ((mprod_exp K (\<lambda>l. \<gamma>\<^bsub>k l\<^esub> ) (Kb\<^bsub>K n P\<^esub>) n)\<^bsub>K\<^esub>\<^bsup>m\<^esup>)= ant (m * (\<gamma>\<^bsub>k j\<^esub>))"

apply (frule K_gamma_hom[of k n])
apply (frule Kbase_hom1[of "n" "P"])
apply (frule mprod_mem[of n "K_gamma k" "Kb\<^bsub>K n P\<^esub>"], assumption+)
apply (frule distinct_pds_valuation1[of "n" "j" "P"], assumption+)
apply (simp, erule conjE)
apply (simp add:val_exp[THEN sym])
apply (simp add:mgenerator2Tr1)
 apply (simp add:K_gamma_def Kronecker_delta_def)
 apply (rule impI)
 apply (simp add:asprod_def a_z_z)
done

lemma (in Corps) mgenerator2Tr3_1:"\<lbrakk>0 < n; j \<le> n; k \<le> n; j = k; 
      distinct_pds K n P\<rbrakk> \<Longrightarrow>
          (\<nu>\<^bsub>K (P j)\<^esub>) ((mprod_exp K (\<lambda>l. (\<gamma>\<^bsub>k l\<^esub>)) (Kb\<^bsub>K n P\<^esub>) n)\<^bsub>K\<^esub>\<^bsup>m\<^esup>) = 0"
apply (simp add:mgenerator2Tr2) apply (simp add:K_gamma_def)
done

lemma (in Corps) mgenerator2Tr3_2:"\<lbrakk>0 < n; j \<le> n; k \<le> n; j \<noteq> k; 
      distinct_pds K n P\<rbrakk> \<Longrightarrow>
      (\<nu>\<^bsub>K (P j)\<^esub>) ((mprod_exp K (\<lambda>l. (\<gamma>\<^bsub>k l\<^esub>)) (Kb\<^bsub>K n P\<^esub>) n)\<^bsub>K\<^esub>\<^bsup>m\<^esup>) = ant m"
apply (simp add:mgenerator2Tr2) apply (simp add:K_gamma_def)
done

lemma (in Corps) mgeneratorTr4:"\<lbrakk>0 < n; distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; 
      I \<noteq> {\<zero>\<^bsub>O\<^bsub>K P n\<^esub>\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>)\<rbrakk> \<Longrightarrow> 
       mprod_exp K (mL K P I) (Kb\<^bsub>K n P\<^esub>) n \<in> carrier (O\<^bsub>K P n\<^esub>)"
apply (subst ring_n_pd_def)
apply (simp add:Sr_def)
 apply (frule mL_hom[of  "n" "P" "I"], assumption+)
 apply (frule mprod_mem[of n "mL K P I" "Kb\<^bsub>K n P\<^esub>"])
 apply (rule Kbase_hom1, assumption+)

 apply (simp add:mprod_mem)

apply (rule allI, rule impI)
 apply (simp add:mgenerator1)
 apply (simp add:value_Zl_mI)
 apply (simp add:val_LI_pos)
done

definition
  m_zmax_pdsI_hom :: "[_, nat \<Rightarrow> ('b \<Rightarrow> ant) set, 'b set] \<Rightarrow> nat \<Rightarrow> int" where
  "m_zmax_pdsI_hom K P I = (\<lambda>j. tna (AMin ((\<nu>\<^bsub>K (P j)\<^esub>) ` I)))"

definition
  m_zmax_pdsI :: "[_, nat, nat \<Rightarrow> ('b \<Rightarrow> ant) set, 'b set] \<Rightarrow> int" where
  "m_zmax_pdsI K n P I = (m_zmax n (m_zmax_pdsI_hom K P I)) + 1"
 
lemma (in Corps) value_Zl_mI_pos:"\<lbrakk>0 < n; distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I;
     I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>); j \<le> n; l \<le> n\<rbrakk> \<Longrightarrow>
     0 \<le> ((\<nu>\<^bsub>K (P j)\<^esub>) (Zl_mI K P I l))"
apply (frule value_Zl_mI[of "n" "P" "I" "l"], assumption+)
apply (erule conjE) 
 apply (frule ring_n_pd[of "n" "P"])
 apply (frule Ring.ideal_subset[of "O\<^bsub>K P n\<^esub>" "I" "Zl_mI K P I l"], assumption+)
 apply (thin_tac "ideal (O\<^bsub>K P n\<^esub>) I")
 apply (thin_tac "I \<noteq> {\<zero>\<^bsub>O\<^bsub>K P n\<^esub>\<^esub>}")
 apply (thin_tac "I \<noteq> carrier (O\<^bsub>K P n\<^esub>)")
 apply (thin_tac "Ring (O\<^bsub>K P n\<^esub>)")
 apply (simp add:ring_n_pd_def Sr_def) 
done

lemma (in Corps) value_mI_genTr1:"\<lbrakk>0 < n; distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I;
 I \<noteq> {\<zero>\<^bsub>O\<^bsub>K P n\<^esub>\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>); j \<le> n\<rbrakk> \<Longrightarrow>
 (mprod_exp K (K_gamma j) (Kb\<^bsub>K n P\<^esub>) n)\<^bsub>K\<^esub>\<^bsup>(m_zmax_pdsI K n P I)\<^esup> \<in> carrier K"
apply (frule K_gamma_hom[of "j" "n"])
apply (frule mprod_mem[of n "K_gamma j" "Kb\<^bsub>K n P\<^esub>"])
 apply (rule Kbase_hom1, assumption+)
apply (rule npowf_mem)
 apply simp+
done

lemma (in Corps) value_mI_genTr1_0:"\<lbrakk>0 < n; distinct_pds K n P; 
 ideal (O\<^bsub>K P n\<^esub>) I; I \<noteq> {\<zero>\<^bsub>O\<^bsub>K P n\<^esub>\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>); j \<le> n\<rbrakk>
 \<Longrightarrow> (mprod_exp K (K_gamma j) (Kb\<^bsub>K n P\<^esub>) n) \<in> carrier K" 
apply (frule K_gamma_hom[of "j" "n"])
apply (frule mprod_mem[of n "K_gamma j" "Kb\<^bsub>K n P\<^esub>"])
 apply (rule Kbase_hom1, assumption+)
 apply simp
done


lemma (in Corps) value_mI_genTr2:"\<lbrakk>0 < n; distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I;
 I \<noteq> {\<zero>\<^bsub>O\<^bsub>K P n\<^esub>\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>); j \<le> n\<rbrakk> \<Longrightarrow>
 (mprod_exp K (K_gamma j) (Kb\<^bsub>K n P\<^esub>) n)\<^bsub>K\<^esub>\<^bsup>(m_zmax_pdsI K n P I)\<^esup> \<noteq> \<zero>"
 apply (frule K_gamma_hom[of "j" "n"])
 apply (frule mprod_mem[of n "K_gamma j" "Kb\<^bsub>K n P\<^esub>"])
 apply (rule Kbase_hom1, assumption+) apply simp apply (erule conjE)
 apply (simp add: field_potent_nonzero1)
done

lemma (in Corps) value_mI_genTr3:"\<lbrakk>0 < n; distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I;
 I \<noteq> {\<zero>\<^bsub>O\<^bsub>K P n\<^esub>\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>); j \<le> n\<rbrakk> \<Longrightarrow>
 (Zl_mI K P I j) \<cdot>\<^sub>r ((mprod_exp K (K_gamma j) (Kb\<^bsub>K n P\<^esub>) n)\<^bsub>K\<^esub>\<^bsup>(m_zmax_pdsI K n P I)\<^esup>)
  \<in> carrier K"
apply (cut_tac field_is_ring)
apply (rule Ring.ring_tOp_closed, assumption+)
apply (simp add:Zl_mI_mem_K)
apply (simp add:value_mI_genTr1)
done

lemma (in Corps) value_mI_gen:"\<lbrakk>0 < n; distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I;
 I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>); j \<le> n\<rbrakk> \<Longrightarrow>  
(\<nu>\<^bsub>K (P j)\<^esub>) (nsum K (\<lambda>k. ((Zl_mI K P I k) \<cdot>\<^sub>r ((mprod_exp K (\<lambda>l. (\<gamma>\<^bsub>k l\<^esub>)) (Kb\<^bsub>K n P\<^esub>) n)\<^bsub>K\<^esub>\<^bsup>(m_zmax_pdsI K n P I)\<^esup>))) n) = LI K (\<nu>\<^bsub>K (P j)\<^esub>) I"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
apply (case_tac "j = n", simp) 
 apply (cut_tac nsum_suc[of K "\<lambda>k. Zl_mI K P I k \<cdot>\<^sub>r 
        mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>" "n - Suc 0"], 
        simp,
        thin_tac "\<Sigma>\<^sub>e K (\<lambda>k. Zl_mI K P I k \<cdot>\<^sub>r
               mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>) n =
     \<Sigma>\<^sub>e K (\<lambda>k. Zl_mI K P I k \<cdot>\<^sub>r
               mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>)
                n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>) (n - Suc 0) \<plusminus>
     Zl_mI K P I n \<cdot>\<^sub>r
     mprod_exp K (K_gamma n) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>")
 apply (cut_tac distinct_pds_valuation[of "n" "n - Suc 0" "P"])
prefer 2 apply simp 
prefer 2 apply simp 
 apply (subst value_less_eq1[THEN sym, of "\<nu>\<^bsub>K (P n)\<^esub>" 
 "(Zl_mI K P I n)\<cdot>\<^sub>r (mprod_exp K (K_gamma n) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>)"
 "nsum K (\<lambda>k.(Zl_mI K P I k)\<cdot>\<^sub>r (mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>)) (n - Suc 0)"], assumption+) 

 apply (simp add:value_mI_genTr3)
 apply (frule Ring.ring_is_ag[of K])
 apply (rule aGroup.nsum_mem[of _ "n - Suc 0"], assumption+)
 apply (rule allI, rule impI)
 apply (simp add:value_mI_genTr3) 

 apply (subst val_t2p[of "\<nu>\<^bsub>K (P n)\<^esub>"], assumption+)
 apply (simp add:Zl_mI_mem_K)
 apply (simp add:value_mI_genTr1) 

 apply (simp add:mgenerator2Tr3_1[of "n" "n" "n" "P"])
 apply (simp add:aadd_0_r) 
apply (frule value_Zl_mI[of "n" "P" "I" "n"], assumption+, simp)
 apply (erule conjE) 
 apply (frule_tac f = "\<lambda>k. (Zl_mI K P I k) \<cdot>\<^sub>r 
       (mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>)" in 
       value_ge_add[of "\<nu>\<^bsub>K (P n)\<^esub>" "n - Suc 0" _ 
      "ant (m_zmax_pdsI K n P I)"])
 apply (rule allI, rule impI) 
 apply (rule Ring.ring_tOp_closed, assumption+)
 apply (simp add:Zl_mI_mem_K)
 apply (simp add:value_mI_genTr1)  

 apply (rule allI, rule impI) apply (simp add:cmp_def)
 apply (subst val_t2p [where v="\<nu>\<^bsub>K P n\<^esub>"], assumption+)
 apply (simp add:Zl_mI_mem_K)
 apply (simp add:value_mI_genTr1) 

 apply (cut_tac e = "K_gamma ja" in mprod_mem[of n  _  "Kb\<^bsub>K n P\<^esub>"])
 apply (simp add:Zset_def) apply (rule Kbase_hom1, assumption+)
 apply (subst val_exp[of "\<nu>\<^bsub>K (P n)\<^esub>", THEN sym], assumption+) 
 apply simp+ 

 apply (subst mgenerator2Tr1[of "n" "n" _ "P"], assumption+, simp, simp,
        assumption+) 
 apply (simp add:K_gamma_def Kronecker_delta_def)
 apply (frule_tac l = ja in value_Zl_mI_pos[of "n" "P" "I" "n"],
        assumption+, simp, simp)
 apply (simp add:Nset_preTr1)
 apply (frule_tac y = "(\<nu>\<^bsub>K (P n)\<^esub>) (Zl_mI K P I ja)" in 
  aadd_le_mono[of "0" _ "ant (m_zmax_pdsI K n P I)"]) apply (simp add:aadd_0_l)
 apply (subgoal_tac "LI K (\<nu>\<^bsub>K (P n)\<^esub>) I < ant (m_zmax_pdsI K n P I)")
 apply simp
 apply (rule aless_le_trans[of "LI K (\<nu>\<^bsub>K (P n)\<^esub>) I" 
                           "ant (m_zmax_pdsI K n P I)"])

 apply (simp add:m_zmax_pdsI_def)
 apply (cut_tac aless_zless[of "tna (LI K (\<nu>\<^bsub>K (P n)\<^esub>) I)" 
                   "m_zmax n (m_zmax_pdsI_hom K P I) + 1"])
apply (frule val_LI_noninf[of "n" "P" "I" "n"], assumption+, simp, simp) 
apply (frule val_LI_pos[of "n" "P" "I" "n"], assumption+, simp,
       frule apos_neq_minf[of "LI K (\<nu>\<^bsub>K (P n)\<^esub>) I"], simp add:ant_tna)
 apply (subst m_zmax_pdsI_hom_def)
 apply (subst LI_def)
 apply (cut_tac m_zmax_gt_each[of n "\<lambda>u.(tna (AMin ((\<nu>\<^bsub>K (P u)\<^esub>) ` I)))"])
 apply simp

 apply (rule allI, rule impI)
 apply (simp add:Zset_def, simp) 

 apply (subst val_t2p[of "\<nu>\<^bsub>K (P n)\<^esub>"], assumption+)
 apply (rule Zl_mI_mem_K, assumption+, simp)
 apply (simp add:value_mI_genTr1)
 apply (simp add:mgenerator2Tr3_1[of "n" "n" "n" "P" "m_zmax_pdsI K n P I"])
 apply (simp add:aadd_0_r)
 apply (simp add:value_Zl_mI[of "n" "P" "I" "n"])

(*** case j = n done ***)
 apply (frule aGroup.addition3[of "K" "n - Suc 0" "\<lambda>k. (Zl_mI K P I k) \<cdot>\<^sub>r
((mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>) n)\<^bsub>K\<^esub>\<^bsup>(m_zmax_pdsI K n P I)\<^esup>)" "j"])
 
 apply simp
 apply (rule allI, rule impI) 
 apply (simp add:value_mI_genTr3) apply simp+

 apply (thin_tac "\<Sigma>\<^sub>e K (\<lambda>k. Zl_mI K P I k \<cdot>\<^sub>r
     mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>) n =
     \<Sigma>\<^sub>e K (cmp (\<lambda>k. Zl_mI K P I k \<cdot>\<^sub>r
            mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>) (\<tau>\<^bsub>j n\<^esub>)) n")
 apply (cut_tac nsum_suc[of K "cmp (\<lambda>k. Zl_mI K P I k \<cdot>\<^sub>r
     mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>) (\<tau>\<^bsub>j n\<^esub>)" "n - Suc 0"])
 apply (simp del:nsum_suc) apply (
        thin_tac "\<Sigma>\<^sub>e K (cmp (\<lambda>k. Zl_mI K P I k \<cdot>\<^sub>r
         mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>) (\<tau>\<^bsub>j n\<^esub>)) n =
     \<Sigma>\<^sub>e K (cmp (\<lambda>k. Zl_mI K P I k \<cdot>\<^sub>r
        mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>) (\<tau>\<^bsub>j n\<^esub>))
         (n - Suc 0) \<plusminus>  (cmp (\<lambda>k. Zl_mI K P I k \<cdot>\<^sub>r
         mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>) (\<tau>\<^bsub>j n\<^esub>)) n")
 apply (cut_tac distinct_pds_valuation[of "j" "n - Suc 0" "P"])
 prefer 2 apply simp prefer 2 apply simp
 apply (simp add:cmp_def)

 apply (cut_tac n_in_Nsetn[of "n"])
 apply (simp add:transpos_ij_2)
 apply (subst value_less_eq1[THEN sym, of "\<nu>\<^bsub>K (P j)\<^esub>"
 "(Zl_mI K P I j) \<cdot>\<^sub>r (mprod_exp K (K_gamma j) (Kb\<^bsub>K n P\<^esub>)
  n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>)" "\<Sigma>\<^sub>e K (\<lambda>x.(Zl_mI K P I ((\<tau>\<^bsub>j n\<^esub>) x)) \<cdot>\<^sub>r
 (mprod_exp K (K_gamma ((\<tau>\<^bsub>j n\<^esub>) x)) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>)) (n - Suc 0)"], assumption+)
 apply (simp add:value_mI_genTr3)
 apply (rule aGroup.nsum_mem[of "K" "n - Suc 0"], assumption+)
 apply (rule allI, rule impI) 
 apply (frule_tac l = ja in transpos_mem[of "j" "n" "n"], simp+)
 apply (simp add:value_mI_genTr3) 

 apply (subst val_t2p[of "\<nu>\<^bsub>K (P j)\<^esub>"], assumption+)
 apply (simp add:Zl_mI_mem_K) 
 apply (simp add:value_mI_genTr1)

 apply (simp add:mgenerator2Tr3_1[of "n" "j" "j" "P"])

 apply (frule value_Zl_mI[of "n" "P" "I" "j"], assumption+)
 apply (erule conjE)
 apply (simp add:aadd_0_r)
 apply (cut_tac f = "\<lambda>x. (Zl_mI K P I ((\<tau>\<^bsub>j n\<^esub>) x)) \<cdot>\<^sub>r
       (mprod_exp K (K_gamma ((\<tau>\<^bsub>j n\<^esub>) x)) (Kb\<^bsub>K n P\<^esub>) n\<^bsub>K\<^esub>\<^bsup>m_zmax_pdsI K n P I\<^esup>)" in 
        value_ge_add[of "\<nu>\<^bsub>K (P j)\<^esub>"
        "n - Suc 0" _ "ant (m_zmax_pdsI K n P I)"], assumption+)
 apply (rule allI, rule impI) 
 apply (frule_tac l = ja in transpos_mem[of "j" "n" "n"], simp+)
 apply (simp add:value_mI_genTr3)
 apply (rule allI, rule impI) apply (simp add:cmp_def)

 apply (frule_tac l = ja in transpos_mem[of "j" "n" "n"], simp+)

 apply (subst val_t2p [where v="\<nu>\<^bsub>K P j\<^esub>"], assumption+) 
 apply (simp add:Zl_mI_mem_K)
 apply (simp add:value_mI_genTr1)
 apply (cut_tac k = ja in transpos_noteqTr[of "n" _ "j"], simp+) 
 apply (subst mgenerator2Tr3_2[of "n" "j" _ "P"], simp+)
 apply (cut_tac l = "(\<tau>\<^bsub>j n\<^esub>) ja" in value_Zl_mI_pos[of "n" "P" "I" "j"],
        simp+)
 apply (frule_tac y = "(\<nu>\<^bsub>K (P j)\<^esub>) (Zl_mI K P I ((\<tau>\<^bsub>j n\<^esub>) ja))" in 
 aadd_le_mono[of "0"  _ "ant (m_zmax_pdsI K n P I)"])
 apply (simp add:aadd_0_l)
apply (subgoal_tac "LI K (\<nu>\<^bsub>K (P j)\<^esub>) I < ant (m_zmax_pdsI K n P I)")
 apply (rule aless_le_trans[of "LI K (\<nu>\<^bsub>K (P j)\<^esub>) I" 
                           "ant (m_zmax_pdsI K n P I)"], assumption+)

 apply (simp add:m_zmax_pdsI_def)
 apply (cut_tac aless_zless[of "tna (LI K (\<nu>\<^bsub>K (P j)\<^esub>) I)" 
                   "m_zmax n (m_zmax_pdsI_hom K P I) + 1"])
apply (frule val_LI_noninf[of  "n" "P" "I" "j"], assumption+,
       frule val_LI_pos[of  "n" "P" "I" "j"], assumption+,
       frule apos_neq_minf[of "LI K (\<nu>\<^bsub>K (P j)\<^esub>) I"], simp add:ant_tna)
 apply (subst m_zmax_pdsI_hom_def)
 apply (subst LI_def)
 apply (subgoal_tac "\<forall>h \<le> n. (\<lambda>u. (tna (AMin ((\<nu>\<^bsub>K (P u)\<^esub>) ` I)))) h \<in> Zset")
 apply (frule m_zmax_gt_each[of n "\<lambda>u.(tna (AMin ((\<nu>\<^bsub>K (P u)\<^esub>) ` I)))"])
 apply simp
 apply (rule allI, rule impI)
 apply (simp add:Zset_def)
apply (subst val_t2p[of "\<nu>\<^bsub>K (P j)\<^esub>"], assumption+)
 apply (rule Zl_mI_mem_K, assumption+)
 apply (simp add:value_mI_genTr1)
  
 apply (simp add:mgenerator2Tr3_1[of  "n" "j" "j" "P" 
                                         "m_zmax_pdsI K n P I"])
 apply (simp add:aadd_0_r)
 apply (simp add:value_Zl_mI[of "n" "P" "I" "j"])
done

lemma (in Corps) mI_gen_in_I:"\<lbrakk>0 < n; distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; 
  I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>)\<rbrakk> \<Longrightarrow>
  (nsum K (\<lambda>k. ((Zl_mI K P I k) \<cdot>\<^sub>r 
  ((mprod_exp K (\<lambda>l. (\<gamma>\<^bsub>k l\<^esub>)) (Kb\<^bsub>K n P\<^esub>) n)\<^bsub>K\<^esub>\<^bsup>(m_zmax_pdsI K n P I)\<^esup>))) n) \<in> I"
apply (cut_tac field_is_ring, frule ring_n_pd[of n P])
apply (rule ideal_eSum_closed[of n P I n], assumption+)
apply (rule allI, rule impI)
 apply (frule_tac j = j in value_Zl_mI[of  "n" "P" "I"], assumption+) 
 apply (erule conjE)
 apply (thin_tac "(\<nu>\<^bsub>K (P j)\<^esub>) (Zl_mI K P I j) = LI K (\<nu>\<^bsub>K (P j)\<^esub>) I")
 apply (subgoal_tac "(mprod_exp K (K_gamma j) (Kb\<^bsub>K n P\<^esub>) n)\<^bsub>K\<^esub>\<^bsup>(m_zmax_pdsI K n P I)\<^esup>
 \<in> carrier (O\<^bsub>K P n\<^esub>)") 
 apply (frule_tac x = "Zl_mI K P I j" and 
   r = "(mprod_exp K (K_gamma j) (Kb\<^bsub>K n P\<^esub>) n)\<^bsub>K\<^esub>\<^bsup>(m_zmax_pdsI K n P I)\<^esup>"
   in Ring.ideal_ring_multiple1[of "(O\<^bsub>K P n\<^esub>)" "I"], assumption+) 
 apply (frule_tac h = "Zl_mI K P I j" in 
               Ring.ideal_subset[of "O\<^bsub>K P n\<^esub>" "I"], assumption+)
 apply (simp add:ring_n_pd_tOp_K_tOp[of "n" "P"])
 
apply (subst ring_n_pd_def) apply (simp add:Sr_def)
 apply (simp add:value_mI_genTr1)

 apply (rule allI, rule impI)
 apply (case_tac "j = ja") 
 apply (simp add:mgenerator2Tr3_1)

 apply (simp add:mgenerator2Tr3_2)
 apply (simp add:m_zmax_pdsI_def) apply (simp add:m_zmax_pdsI_hom_def)
 apply (simp only:ant_0[THEN sym])
 apply (simp add:aless_zless)
 apply (subgoal_tac "\<forall>l \<le> n. (\<lambda>j. tna (AMin ((\<nu>\<^bsub>K (P j)\<^esub>) ` I))) l \<in> Zset")
 apply (frule m_zmax_gt_each[of n "\<lambda>j. tna (AMin ((\<nu>\<^bsub>K (P j)\<^esub>) ` I))"]) 
 apply (rotate_tac -1, drule_tac a = ja in forall_spec, simp+)
 apply (frule_tac j = ja in val_LI_pos[of  "n" "P" "I"], assumption+) 
 apply (cut_tac j = "tna (LI K (\<nu>\<^bsub>K (P ja)\<^esub>) I)" in ale_zle[of "0"]) 
apply (frule_tac j = ja in val_LI_noninf[of "n" "P" "I"], assumption+,
       frule_tac j = ja in val_LI_pos[of "n" "P" "I"], assumption+,
       frule_tac a = "LI K (\<nu>\<^bsub>K (P ja)\<^esub>) I" in apos_neq_minf, simp add:ant_tna,
       simp add:ant_0) apply (unfold LI_def)
 apply (frule_tac y = "tna (AMin (\<nu>\<^bsub>K (P ja)\<^esub> ` I))" and z = "m_zmax n (\<lambda>j. tna (AMin (\<nu>\<^bsub>K (P j)\<^esub> ` I)))" in order_trans[of "0"], assumption+)
 apply (rule_tac y = "m_zmax n (\<lambda>j. tna (AMin (\<nu>\<^bsub>K (P j)\<^esub> ` I)))" and 
        z = "m_zmax n (\<lambda>j. tna (AMin (\<nu>\<^bsub>K (P j)\<^esub> ` I))) + 1" in order_trans[of "0"],
        assumption+) apply simp

 apply (rule allI, rule impI) apply (simp add:Zset_def)
done


text\<open>We write the element 
        \<open>e\<Sigma> K (\<lambda>k. (Zl_mI K P I k) \<cdot>\<^sub>K ((mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>)
                    n)\<^sub>K\<^sup>(m_zmax_pdsI K n P I))) n\<close>
      as \<open>mIg\<^bsub>K G a i n P I\<^esub>\<close>\<close>

definition
  mIg :: "[_, nat, nat \<Rightarrow> ('b \<Rightarrow> ant) set,
             'b set] \<Rightarrow> 'b" ("(4mIg\<^bsub> _ _ _ _\<^esub>)" [82,82,82,83]82) where
  "mIg\<^bsub>K n P I\<^esub> = \<Sigma>\<^sub>e K (\<lambda>k. (Zl_mI K P I k) \<cdot>\<^sub>r\<^bsub>K\<^esub>
             ((mprod_exp K (K_gamma k) (Kb\<^bsub>K n P\<^esub>) n)\<^bsub>K\<^esub>\<^bsup>(m_zmax_pdsI K n P I)\<^esup>)) n"

text\<open>We can rewrite above two lemmas by using \<open>mIg\<^bsub>K G a i n P I\<^esub>\<close>\<close> 

lemma (in Corps) value_mI_gen1:"\<lbrakk>0 < n; distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I;
 I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>)\<rbrakk> \<Longrightarrow> 
                \<forall>j \<le> n.(\<nu>\<^bsub>K (P j)\<^esub>) (mIg\<^bsub>K n P I\<^esub>) = LI K (\<nu>\<^bsub>K (P j)\<^esub>) I" 
apply (rule allI, rule impI)
 apply (simp add:mIg_def value_mI_gen)
done

lemma (in Corps) mI_gen_in_I1:"\<lbrakk>0 < n; distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; 
  I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>)\<rbrakk> \<Longrightarrow>  (mIg\<^bsub>K n P I\<^esub>) \<in> I"
apply (simp add:mIg_def mI_gen_in_I)
done

lemma (in Corps) mI_principalTr:"\<lbrakk>0 < n; distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; 
  I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>); x \<in> I\<rbrakk> \<Longrightarrow> 
 \<forall>j \<le> n. ((\<nu>\<^bsub>K (P j)\<^esub>) (mIg\<^bsub>K n P I\<^esub>)) \<le> ((\<nu>\<^bsub>K (P j)\<^esub>) x)" 
apply (simp add:value_mI_gen1)
 apply (rule allI, rule impI)
 apply (rule Zleast_LI, assumption+)
done

lemma (in Corps) mI_principal:"\<lbrakk>0 < n; distinct_pds K n P; ideal (O\<^bsub>K P n\<^esub>) I; 
 I \<noteq> {\<zero>\<^bsub>(O\<^bsub>K P n\<^esub>)\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>)\<rbrakk> \<Longrightarrow> 
                                        I = Rxa (O\<^bsub>K P n\<^esub>) (mIg\<^bsub>K n P I\<^esub>)"
apply (frule ring_n_pd[of "n" "P"]) 
apply (rule equalityI)
 apply (rule subsetI)
 apply (frule_tac x = x in mI_principalTr[of "n" "P" "I"],
                 assumption+)
 apply (frule_tac y = x in n_eq_val_eq_idealTr[of "n" "P" "mIg\<^bsub>K n P I\<^esub>"])
 apply (frule mI_gen_in_I1[of "n" "P" "I"], assumption+)
 apply (simp add:Ring.ideal_subset)+
 apply (thin_tac "\<forall>j\<le>n. (\<nu>\<^bsub>K (P j)\<^esub>) (mIg\<^bsub> K n P I\<^esub>) \<le> (\<nu>\<^bsub>K (P j)\<^esub>) x")
 apply (frule_tac h = x in Ring.ideal_subset[of "O\<^bsub>K P n\<^esub>" "I"], assumption+)
 apply (frule_tac a = x in Ring.a_in_principal[of "O\<^bsub>K P n\<^esub>"], assumption+)
 apply (simp add:subsetD)
 apply (rule Ring.ideal_cont_Rxa[of "O\<^bsub>K P n\<^esub>" "I" "mIg\<^bsub> K n P I\<^esub>"], assumption+)
 apply (rule mI_gen_in_I1[of  "n" "P" "I"], assumption+)
done

subsection \<open>\<open>prime_n_pd\<close>\<close>

lemma (in Corps) prime_n_pd_principal:"\<lbrakk>distinct_pds K n P; j \<le> n\<rbrakk> \<Longrightarrow>  
       (P\<^bsub>K P n\<^esub> j) = Rxa (O\<^bsub>K P n\<^esub>) (((Kb\<^bsub>K n P\<^esub>) j))"
apply (frule ring_n_pd[of "n" "P"])
apply (frule prime_n_pd_prime[of "n" "P" "j"], assumption+)
apply (simp add:prime_ideal_def, frule conjunct1)
 apply (fold prime_ideal_def)
 apply (thin_tac "prime_ideal (O\<^bsub>K P n\<^esub>) (P\<^bsub>K P n\<^esub> j)")
apply (rule equalityI)
 apply (rule subsetI)
 apply (frule_tac y = x in n_eq_val_eq_idealTr[of n P "(Kb\<^bsub>K n P\<^esub>) j"])
 apply (thin_tac "Ring (O\<^bsub>K P n\<^esub>)", thin_tac "ideal (O\<^bsub>K P n\<^esub>) (P\<^bsub>K P n\<^esub> j)")
 apply (simp add:ring_n_pd_def Sr_def)
 apply (frule Kbase_hom[of  "n" "P"], simp)
 apply (rule allI, rule impI)
 apply (frule Kbase_Kronecker[of "n" "P"])
 apply (simp add:Kronecker_delta_def, rule impI)
 apply (simp only:ant_0[THEN sym], simp only:ant_1[THEN sym])
 apply (simp del:ant_1)
 apply (simp add:prime_n_pd_def)


 apply (rule allI, rule impI)
 apply (frule Kbase_Kronecker[of "n" "P"])
 apply simp
 apply (thin_tac "\<forall>j\<le>n. \<forall>l\<le>n. (\<nu>\<^bsub>K (P j)\<^esub>) ((Kb\<^bsub>K n P\<^esub>) l) = \<delta>\<^bsub>j l\<^esub>")
 apply (case_tac "ja = j", simp add:Kronecker_delta_def)
 apply (thin_tac "ideal (O\<^bsub>K P n\<^esub>) (P\<^bsub>K P n\<^esub> j)")
 apply (simp add:prime_n_pd_def, erule conjE)
 apply (frule_tac x = x in  mem_ring_n_pd_mem_K[of "n" "P"],
                                         assumption+)
 apply (case_tac "x = \<zero>\<^bsub>K\<^esub>")
 apply (frule distinct_pds_valuation2[of "j" "n" "P"], assumption+)
 apply (rule gt_a0_ge_1, assumption)+

 apply (simp add:Kronecker_delta_def)
 apply (frule_tac j = ja in distinct_pds_valuation2[of  _ "n" "P"],
         assumption+)
 apply (simp add:prime_n_pd_def, erule conjE)
 apply (thin_tac "ideal (O\<^bsub>K P n\<^esub>) {x. x \<in> carrier (O\<^bsub>K P n\<^esub>) \<and> 0 < (\<nu>\<^bsub>K (P j)\<^esub>) x}")
 apply (simp add:ring_n_pd_def Sr_def)
 apply (cut_tac h = x in Ring.ideal_subset[of "O\<^bsub>K P n\<^esub>" "P\<^bsub>K P n\<^esub> j"])
 apply (frule_tac a = x in Ring.a_in_principal[of "O\<^bsub>K P n\<^esub>"])
 apply (simp add:Ring.ideal_subset, assumption+)


apply (rule_tac c = x and A = "(O\<^bsub>K P n\<^esub>) \<diamondsuit>\<^sub>p x" and B = "(O\<^bsub>K P n\<^esub>) \<diamondsuit>\<^sub>p (Kb\<^bsub>K n P\<^esub>) j"
       in subsetD, assumption+)
apply (simp add:Ring.a_in_principal)
 apply (rule Ring.ideal_cont_Rxa[of "O\<^bsub>K P n\<^esub>" "P\<^bsub>K P n\<^esub> j" "(Kb\<^bsub>K n P\<^esub>) j"], assumption+)
 apply (subst prime_n_pd_def, simp)
 apply (frule Kbase_Kronecker[of "n" "P"])
 apply (simp add:Kronecker_delta_def) 
 apply (simp only:ant_1[THEN sym], simp only:ant_0[THEN sym])
 apply (simp del:ant_1 add:aless_zless)
apply (subst ring_n_pd_def, simp add:Sr_def)
 apply (frule Kbase_hom[of "n" "P"])
 apply simp
 apply (rule allI) 
 apply (simp add:ant_0)
 apply (rule impI)
  apply (simp only:ant_1[THEN sym], simp only:ant_0[THEN sym])
  apply (simp del:ant_1)
done

lemma (in Corps) ring_n_prod_primesTr:"\<lbrakk>0 < n; distinct_pds K n P; 
 ideal (O\<^bsub>K P n\<^esub>) I; I \<noteq> {\<zero>\<^bsub>O\<^bsub>K P n\<^esub>\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>)\<rbrakk> \<Longrightarrow>
 \<forall>j \<le> n.(\<nu>\<^bsub>K (P j)\<^esub>) (mprod_exp K (mL K P I) (Kb\<^bsub>K n P\<^esub>) n) = 
                   (\<nu>\<^bsub>K (P j)\<^esub>) (mIg\<^bsub>K n P I\<^esub>)"
apply (rule allI, rule impI)
 apply (simp add:mgenerator1)
 apply (simp add:value_mI_gen1)

 apply (simp add:value_Zl_mI)
done

lemma (in Corps) ring_n_prod_primesTr1:"\<lbrakk>0 < n; distinct_pds K n P;  
      ideal (O\<^bsub>K P n\<^esub>) I; I \<noteq> {\<zero>\<^bsub>O\<^bsub>K P n\<^esub>\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>)\<rbrakk> \<Longrightarrow> 
       I = (O\<^bsub>K P n\<^esub>) \<diamondsuit>\<^sub>p (mprod_exp K (mL K P I) (Kb\<^bsub>K n P\<^esub>) n)"
apply (frule ring_n_pd[of "n" "P"])
apply (subst n_eq_val_eq_ideal[of "n" "P" "mprod_exp K (mL K P I)
       (Kb\<^bsub>K n P\<^esub>) n" "mIg\<^bsub>K n P I\<^esub>"], assumption+)
apply (simp add:mgeneratorTr4) 
apply (frule mI_gen_in_I1[of "n" "P" "I"], assumption+)
apply (simp add:Ring.ideal_subset)
apply (simp add:ring_n_prod_primesTr)
apply (simp add:mI_principal)
done

lemma (in Corps) ring_n_prod_primes:"\<lbrakk>0 < n; distinct_pds K n P;  
      ideal (O\<^bsub>K P n\<^esub>) I; I \<noteq> {\<zero>\<^bsub>O\<^bsub>K P n\<^esub>\<^esub>}; I \<noteq> carrier (O\<^bsub>K P n\<^esub>); 
     \<forall>k \<le> n. J k = (P\<^bsub>K P n\<^esub> k)\<^bsup>\<diamondsuit>(O\<^bsub>K P n\<^esub>) (nat ((mL K P I) k))\<^esup>\<rbrakk> \<Longrightarrow> 
       I = i\<Pi>\<^bsub>(O\<^bsub>K P n\<^esub>),n\<^esub> J" 
apply (simp add:prime_n_pd_principal[of "n" "P"])
apply (subst ring_n_prod_primesTr1[of "n" "P" "I"], assumption+)
apply (frule ring_n_pd[of "n" "P"])
apply (frule Ring.prod_n_principal_ideal[of "O\<^bsub>K P n\<^esub>" "nat o (mL K P I)" "n" 
       "Kb\<^bsub>K n P\<^esub>" "J"])
 apply (frule Kbase_hom[of "n" "P"])
 apply (simp add:nat_def)
 apply (subst ring_n_pd_def) apply (simp add:Sr_def) 
 apply (rule Pi_I, simp)
 apply (simp add:Kbase_Kronecker[of  "n" "P"])
 apply (simp add:Kronecker_delta_def) 
  apply (simp only:ant_1[THEN sym], simp only:ant_0[THEN sym])
  apply (simp del:ant_1)
  apply (simp add:Kbase_hom) apply simp 

 apply simp
 apply (frule ring_n_mprod_mprodR[of "n" "P" n "mL K P I"  "Kb\<^bsub>K n P\<^esub>"])
  apply (rule allI, rule impI, simp add:Zset_def)
  apply (rule allI, rule impI) 
  apply (simp add: Zleast_in_mI_pos)

 apply (rule allI, rule impI)
 apply (subst ring_n_pd_def) apply (simp add:Sr_def)
 apply (frule Kbase_hom1[of  "n" "P"], simp)
 apply (simp add:zero_in_ring_n_pd_zero_K)
 apply (frule Kbase_Kronecker[of  "n" "P"])
 apply (simp add:Kronecker_delta_def) 
  apply (simp only:ant_1[THEN sym], simp only:ant_0[THEN sym])
  apply (simp del:ant_1)
apply simp
done

end
