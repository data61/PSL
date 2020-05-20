(**        Algebra6  
                            author Hidetsune Kobayashi
                            Group You Santo
                            Department of Mathematics
                            Nihon University
                            hikoba@math.cst.nihon-u.ac.jp
                            May 3, 2004.
                            April 6, 2007 (revised)

   chapter 4. Ring theory
    section 14. the degree of a polynomial(continued)
    section 15. homomorphism of polynomial rings
    section 16. relatively prime polynomials
    **)

theory Algebra6 imports Algebra5 begin

definition
  s_cf :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a, 'a]  
                                           \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a)" where
  "s_cf R S X p = (if p = \<zero>\<^bsub>R\<^esub> then (0, \<lambda>j. \<zero>\<^bsub>S\<^esub>) else 
              SOME c. (pol_coeff S c \<and> p = polyn_expr R X (fst c) c \<and>
              (snd c) (fst c) \<noteq> \<zero>\<^bsub>S\<^esub>))"
  (* special coefficients for p  *)

definition
  lcf :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a, 'a]  \<Rightarrow> 'a" where
  "lcf R S X p = (snd (s_cf R S X p)) (fst (s_cf R S X p))"
  
 
lemma (in PolynRg) lcf_val_0:"lcf R S X \<zero> = \<zero>\<^bsub>S\<^esub>"
by (simp add:lcf_def s_cf_def)

lemma (in PolynRg) lcf_val:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero> \<rbrakk> \<Longrightarrow> 
                    lcf R S X p = (snd (s_cf R S X p)) (fst (s_cf R S X p))"
by (simp add:lcf_def) 

lemma (in PolynRg) s_cf_pol_coeff:"p \<in> carrier R \<Longrightarrow>
                         pol_coeff S (s_cf R S X p)"
apply (simp add:s_cf_def) 
 apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp) 
 apply (cut_tac subring, frule subring_Ring, 
             simp add:pol_coeff_def Ring.ring_zero)
apply simp
 apply (rule someI2_ex)
 apply (frule ex_polyn_expr[of p], erule exE, erule conjE)
 apply (frule_tac c = c in coeff_max_bddTr)
 apply (frule_tac c = c and n = "c_max S c" in pol_coeff_le, assumption)
 apply (subgoal_tac "p = polyn_expr R X (fst (c_max S c, snd c))
                                                  (c_max S c, snd c) \<and>
                     snd (c_max S c, snd c) (fst (c_max S c, snd c)) \<noteq> \<zero>\<^bsub>S\<^esub>",
        blast)
 apply (rule conjI, simp)
 apply (subst polyn_expr_short[THEN sym], assumption+)
 apply (simp add:polyn_c_max)

 apply simp
 apply (rule coeff_max_nonzeroTr, assumption)
 apply (simp add:coeff_0_pol_0[THEN sym])

 apply simp
done

lemma (in PolynRg) lcf_mem:"p \<in> carrier R \<Longrightarrow> (lcf R S X p) \<in> carrier S"
apply (cut_tac subring, frule subring_Ring) 
apply (simp add:lcf_def) 
 apply (cut_tac pol_coeff_mem[of "s_cf R S X p" "fst (s_cf R S X p)"],
          assumption,
        rule s_cf_pol_coeff, assumption, simp)
done

lemma (in PolynRg) s_cf_expr0:"p \<in> carrier R \<Longrightarrow>
      pol_coeff S (s_cf R S X p) \<and>
      p = polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p)"
apply (cut_tac subring, frule subring_Ring)
apply (simp add:s_cf_def)
 apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp)
 apply (rule conjI, simp add:pol_coeff_def, simp add:Ring.ring_zero)
 apply (simp add:polyn_expr_def,
        simp add:Subring_zero_ring_zero, simp add:ring_r_one)

apply simp
 apply (rule someI2_ex)
 apply (frule ex_polyn_expr[of p], erule exE, erule conjE)
 apply (frule_tac c = c in coeff_max_bddTr)
 apply (frule_tac c = c and n = "c_max S c" in pol_coeff_le, assumption)
 apply (subgoal_tac "p = polyn_expr R X (fst (c_max S c, snd c))
                                                  (c_max S c, snd c) \<and>
                     snd (c_max S c, snd c) (fst (c_max S c, snd c)) \<noteq> \<zero>\<^bsub>S\<^esub>",
        blast)
 apply (rule conjI, simp)
 apply (subst polyn_expr_short[THEN sym], assumption+)
 apply (simp add:polyn_c_max)

 apply simp
 apply (rule coeff_max_nonzeroTr, assumption)
 apply (simp add:coeff_0_pol_0[THEN sym])
 apply simp
done 

lemma (in PolynRg) pos_deg_nonzero:"\<lbrakk>p \<in> carrier R; 0 < deg_n R S X p\<rbrakk> \<Longrightarrow>
                     p \<noteq> \<zero>"
apply (cut_tac s_cf_expr0[of p], (erule conjE)+)
 apply (frule pol_deg_eq_c_max[of p "s_cf R S X p"], assumption+)
 apply (simp, thin_tac "deg_n R S X p = c_max S (s_cf R S X p)")
 apply (simp add:c_max_def) 
 apply (case_tac "\<forall>x\<le>fst (s_cf R S X p). snd (s_cf R S X p) x = \<zero>\<^bsub>S\<^esub> ", simp)
 apply (thin_tac "0 < (if \<forall>x\<le>fst (s_cf R S X p). snd (s_cf R S X p) x = \<zero>\<^bsub>S\<^esub> 
   then 0 else n_max
                {j. j \<le> fst (s_cf R S X p) \<and> snd (s_cf R S X p) j \<noteq> \<zero>\<^bsub>S\<^esub>})")
 apply (simp add:coeff_0_pol_0[of "s_cf R S X p" "fst (s_cf R S X p)"])
 apply assumption
done

lemma (in PolynRg) s_cf_expr:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
      pol_coeff S (s_cf R S X p) \<and>
      p = polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p) \<and>
      (snd (s_cf R S X p)) (fst (s_cf R S X p)) \<noteq> \<zero>\<^bsub>S\<^esub>" 
apply (simp add:s_cf_def)
 apply (rule someI2_ex)

 apply (frule ex_polyn_expr[of p], erule exE, erule conjE)
 apply (frule_tac c = c in coeff_max_bddTr)
 apply (frule_tac c = c and n = "c_max S c" in pol_coeff_le, assumption)
 apply (subgoal_tac "p = polyn_expr R X (fst (c_max S c, snd c))
                                                  (c_max S c, snd c) \<and>
                     snd (c_max S c, snd c) (fst (c_max S c, snd c)) \<noteq> \<zero>\<^bsub>S\<^esub>",
        blast)
 apply (rule conjI, simp)
 apply (subst polyn_expr_short[THEN sym], assumption+)
 apply (simp add:polyn_c_max)

 apply simp
 apply (rule coeff_max_nonzeroTr, assumption)
 apply (simp add:coeff_0_pol_0[THEN sym])
 apply simp
done

lemma (in PolynRg) lcf_nonzero:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero> \<rbrakk> \<Longrightarrow> 
                                          lcf R S X p \<noteq> \<zero>\<^bsub>S\<^esub>"
apply (frule s_cf_expr[of p], assumption)
apply (simp add:lcf_def)
done

lemma (in PolynRg) s_cf_deg:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
                  deg_n R S X p = fst (s_cf R S X p)"
apply (frule s_cf_expr[of p], assumption, (erule conjE)+)
apply (simp add:pol_deg_n[of p "s_cf R S X p" "fst (s_cf R S X p)"])
done

lemma (in PolynRg) pol_expr_edeg:"\<lbrakk>p \<in> carrier R; deg R S X p \<le> (an d)\<rbrakk> \<Longrightarrow> 
       \<exists>f. (pol_coeff S f \<and> fst f = d \<and> p = polyn_expr R X d f)"
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>")
 apply (subgoal_tac "pol_coeff S (d, \<lambda>j. \<zero>\<^bsub>S\<^esub>) \<and> fst (d, \<lambda>j. \<zero>\<^bsub>S\<^esub>) = d \<and> 
              p = polyn_expr R X d (d, \<lambda>j. \<zero>\<^bsub>S\<^esub>)", blast)
 apply (rule conjI)
 apply (simp add:pol_coeff_def, cut_tac Ring.ring_zero[of S], simp,
        cut_tac subring, simp add:subring_Ring) 
 apply (cut_tac coeff_0_pol_0[of "(d, \<lambda>j. \<zero>\<^bsub>S\<^esub>)" d], simp)
 apply (simp add:pol_coeff_def, cut_tac Ring.ring_zero[of S], simp,
        cut_tac subring, simp add:subring_Ring) 
 apply simp
 apply (frule s_cf_expr[of p], assumption+, (erule conjE)+)
 apply (simp add:deg_def na_an, simp add:ale_natle)
 apply (simp add:s_cf_deg)
 apply (subgoal_tac "pol_coeff S (d, \<lambda>j. (if j \<le> (fst (s_cf R S X p)) then
         (snd (s_cf R S X p) j) else \<zero>\<^bsub>S\<^esub>)) \<and>
         p = polyn_expr R X d (d, \<lambda>j. (if j \<le> (fst (s_cf R S X p)) then
         (snd (s_cf R S X p) j) else \<zero>\<^bsub>S\<^esub>))", blast)
 apply (rule conjI)
  apply (simp add:pol_coeff_def, rule allI, rule impI, rule impI)
  apply (cut_tac subring, simp add:subring_Ring, simp add:subring_Ring[of S]
         Ring.ring_zero)
  apply (case_tac "fst (s_cf R S X p) = d", simp)
  apply (subst polyn_exprs_eq[of "(d, \<lambda>j. if j \<le> d then snd (s_cf R S X p) j 
         else \<zero>\<^bsub>S\<^esub>)" "s_cf R S X p" d])
   apply (simp add:pol_coeff_def, cut_tac Ring.ring_zero[of S], simp,
          cut_tac subring, simp add:subring_Ring, simp) 
   apply (rule allI, rule impI, simp, assumption+)
   apply (drule noteq_le_less[of "fst (s_cf R S X p)" d], assumption+)
 apply (cut_tac polyn_n_m1[of "(d, \<lambda>j. if j \<le> fst (s_cf R S X p) then 
        snd (s_cf R S X p) j else \<zero>\<^bsub>S\<^esub>)" "fst (s_cf R S X p)" d], simp)
 apply (cut_tac higher_part_zero[of "(d, \<lambda>j. if j \<le> fst (s_cf R S X p) then 
     snd (s_cf R S X p) j else \<zero>\<^bsub>S\<^esub>)" "fst (s_cf R S X p)"], simp,
     thin_tac "polyn_expr R X d
      (d, \<lambda>j. if j \<le> fst (s_cf R S X p) then snd (s_cf R S X p) j else \<zero>\<^bsub>S\<^esub>) =
     polyn_expr R X (fst (s_cf R S X p)) (d, \<lambda>j. if j \<le> fst (s_cf R S X p) 
      then snd (s_cf R S X p) j else \<zero>\<^bsub>S\<^esub>) \<plusminus> \<zero>",
     thin_tac "\<Sigma>\<^sub>f R (\<lambda>j. (if j \<le> fst (s_cf R S X p) then snd (s_cf R S X p) j
                else \<zero>\<^bsub>S\<^esub>) \<cdot>\<^sub>r X^\<^bsup>R j\<^esup>) (Suc (fst (s_cf R S X p))) d = \<zero>")
apply (subst polyn_exprs_eq[of "(d, \<lambda>j. if j \<le> fst (s_cf R S X p) then 
       snd (s_cf R S X p) j else \<zero>\<^bsub>S\<^esub>)" "s_cf R S X p" "fst (s_cf R S X p)"])
  apply (simp add:pol_coeff_def, rule allI, rule impI, rule impI,
         cut_tac subring, simp add:subring_Ring, simp add:subring_Ring[of S]
         Ring.ring_zero, assumption+) apply (simp)
  apply (rule allI, rule impI, simp)
  apply (frule polyn_mem[of "s_cf R S X p" "fst (s_cf R S X p)"], simp+)
  apply (cut_tac ring_is_ag, simp add:aGroup.ag_r_zero)
  apply (simp add:pol_coeff_def, rule allI, rule impI, rule impI,
         cut_tac subring, simp add:subring_Ring, simp add:subring_Ring[of S]
         Ring.ring_zero)
  apply simp
  apply (rule ballI, simp add:nset_def)
  apply (simp add:pol_coeff_def, rule allI, rule impI, rule impI,
         cut_tac subring, simp add:subring_Ring, simp add:subring_Ring[of S]
         Ring.ring_zero)
  apply assumption apply simp
done

lemma (in PolynRg) cf_scf:"\<lbrakk>pol_coeff S c; k \<le> fst c; polyn_expr R X k c \<noteq> \<zero>\<rbrakk>
    \<Longrightarrow>  \<forall>j \<le> fst (s_cf R S X (polyn_expr R X k c)).
              snd (s_cf R S X (polyn_expr R X k c)) j = snd c j"
apply (frule polyn_mem[of c k], assumption+)
apply (simp add:polyn_expr_short[of c k],
       rule allI, rule impI)
apply (cut_tac pol_deg_le_n1[of "polyn_expr R X k c" c k],
       frule s_cf_expr0[of "polyn_expr R X k (k, snd c)"], erule conjE)
apply (rotate_tac -1, drule sym)
apply (case_tac "fst (s_cf R S X (polyn_expr R X k (k, snd c))) = k",
       simp,
       cut_tac c = "s_cf R S X (polyn_expr R X k (k, snd c))" and 
       d = "(k, snd c)" in pol_expr_unique2,
       simp add:s_cf_pol_coeff, simp add:split_pol_coeff, simp,
        simp, simp add:polyn_expr_short[THEN sym, of c k])

 apply (simp add:s_cf_deg[of "polyn_expr R X k c"],
        drule noteq_le_less[of "fst (s_cf R S X (polyn_expr R X k c))" k],
        assumption) 
 apply (frule pol_expr_unique3[of "s_cf R S X (polyn_expr R X k c)" 
         "(k, snd c)"], simp add:split_pol_coeff, simp,
        simp add:polyn_expr_short[THEN sym, of c k])
apply (simp add:polyn_expr_short[THEN sym, of c k], assumption+, simp)
done

definition
  scf_cond :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a, 'a, 
                  nat, nat \<times> (nat \<Rightarrow> 'a)] \<Rightarrow> bool" where
  "scf_cond R S X p d c \<longleftrightarrow> pol_coeff S c \<and> fst c = d \<and> p = polyn_expr R X d c"

definition
  scf_d :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a, 'a, nat]
                \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a)" where
  "scf_d R S X p d = (SOME f. scf_cond R S X p d f)" 
 
  (** system of coefficients, coeff_length d **)

lemma (in PolynRg) scf_d_polTr:"\<lbrakk>p \<in> carrier R; deg R S X p \<le> an d\<rbrakk> \<Longrightarrow> 
           scf_cond R S X p d (scf_d R S X p d)" 
apply (simp add:scf_d_def) 
apply (rule_tac P = "scf_cond R S X p d" in someI2_ex)
apply (frule pol_expr_edeg[of "p" "d"], assumption+)
apply (simp add:scf_cond_def, assumption)
done

lemma (in PolynRg) scf_d_pol:"\<lbrakk>p \<in> carrier R; deg R S X p \<le> an d\<rbrakk> \<Longrightarrow> 
      pol_coeff S (scf_d R S X p d) \<and> fst (scf_d R S X p d) = d \<and>
       p = polyn_expr R X d (scf_d R S X p d)"
apply (frule scf_d_polTr[of "p" "d"], assumption+)
apply (simp add:scf_cond_def)
done

lemma (in PolynRg) pol_expr_of_X:
       "X = polyn_expr R X (Suc 0) (ext_cf S (Suc 0) (C\<^sub>0 S))"
apply (cut_tac X_mem_R, cut_tac subring)
apply (cut_tac X_to_d[of "Suc 0"])
 apply (simp add:ring_l_one)
done

lemma (in PolynRg) deg_n_of_X:"deg_n R S X X = Suc 0"
apply (cut_tac X_mem_R, cut_tac polyn_ring_S_nonzero,
       cut_tac subring)
apply (cut_tac pol_expr_of_X)
apply (cut_tac special_cf_pol_coeff)
apply (frule ext_cf_pol_coeff[of "C\<^sub>0 S" "Suc 0"])
 apply (frule pol_deg_eq_c_max[of X "ext_cf S (Suc 0) (C\<^sub>0 S)"], assumption)
        apply (simp add:ext_cf_len special_cf_len)
 apply (simp add:c_max_ext_special_cf)
done

lemma (in PolynRg) pol_X:"cf_sol R S X X c \<Longrightarrow>
              snd c 0 = \<zero>\<^bsub>S\<^esub> \<and> snd c (Suc 0) = 1\<^sub>r\<^bsub>S\<^esub>" 

apply (simp add:cf_sol_def, erule conjE)
apply (cut_tac pol_expr_of_X) 
apply (cut_tac special_cf_pol_coeff,
               frule ext_cf_pol_coeff[of "C\<^sub>0 S" "Suc 0"])
apply (cut_tac X_mem_R, cut_tac polyn_ring_X_nonzero,
       cut_tac subring)
apply (frule pol_deg_le_n[of X c], assumption+, simp add:deg_n_of_X)
apply (case_tac "fst c = Suc 0")
apply (frule box_equation[of X "polyn_expr R X (Suc 0) 
       (ext_cf S (Suc 0) (C\<^sub>0 S))" "polyn_expr R X (fst c) c"], assumption+,
       thin_tac "X = polyn_expr R X (Suc 0) (ext_cf S (Suc 0) (C\<^sub>0 S))",
       thin_tac "X = polyn_expr R X (fst c) c")
apply (cut_tac pol_expr_unique2[of "ext_cf S (Suc 0) (C\<^sub>0 S)" c],
       simp, simp add:ext_cf_len special_cf_len, rule conjI,
       drule_tac a = 0 in forall_spec, simp,
       simp add:ext_special_cf_lo_zero)
apply( drule_tac a = "Suc 0" in forall_spec, simp,
       simp add:ext_special_cf_hi, assumption+,
       simp add:ext_cf_len special_cf_len)

apply (frule noteq_le_less[of "Suc 0" "fst c"],rule not_sym, assumption,
       cut_tac pol_expr_unique3[of "ext_cf S (Suc 0) (C\<^sub>0 S)" c],
       simp add:ext_cf_len special_cf_len,
       erule conjE,
       thin_tac "\<forall>j\<in>nset (Suc (Suc 0)) (fst c). snd c j = \<zero>\<^bsub>S\<^esub>")
 apply (rule conjI,
        drule_tac a = 0 in forall_spec, simp,
        simp add:ext_special_cf_lo_zero,
        drule_tac a = "Suc 0" in forall_spec, simp,
        simp add:ext_special_cf_hi,
        assumption+)
 apply (simp add:ext_cf_len special_cf_len)
done

lemma (in PolynRg) pol_of_deg0:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>\<rbrakk>
      \<Longrightarrow>  (deg_n R S X p = 0) = (p \<in> carrier S)"
apply (cut_tac subring,
       frule subring_Ring,
       cut_tac ring_is_ag,
       frule Ring.ring_is_ag[of S])
apply (rule iffI)
 apply (frule s_cf_expr[of p], assumption) 
 apply (simp add:s_cf_deg, (erule conjE)+, simp add:polyn_expr_def)
 apply (frule pol_coeff_mem[of "s_cf R S X p" 0], simp) 
 apply (cut_tac mem_subring_mem_ring[of S "snd (s_cf R S X p) 0"],
        simp add:ring_r_one, assumption+)

apply (frule s_cf_expr[of p], assumption+, (erule conjE)+,
       simp add:s_cf_deg)
apply (rule contrapos_pp, simp+)
apply (subgoal_tac "pol_coeff S (0, (\<lambda>j. p)) \<and> 
                      p = polyn_expr R X 0 (0, (\<lambda>j. p))", erule conjE)
apply (cut_tac a = "polyn_expr R X 0 (0, \<lambda>j. p)" and 
               b = "polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p)" in 
               aGroup.ag_eq_diffzero[of R],  assumption+, simp, simp)

 apply (frule_tac c = "polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p)" in 
         box_equation[of p "polyn_expr R X 0 (0, \<lambda>j. p)"], assumption,
        thin_tac "p = polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p)",
        thin_tac "p = polyn_expr R X 0 (0, \<lambda>j. p)", simp)

 apply (simp only:polyn_minus_m_cf) 
  apply (rotate_tac -2, drule sym, simp,
        thin_tac "polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p) = 
                 polyn_expr R X 0 (0, \<lambda>j. p)")
 apply (frule_tac c = "s_cf R S X p" in m_cf_pol_coeff)
 
 apply (frule_tac d = "m_cf S (s_cf R S X p)" in polyn_add1[of "(0, \<lambda>j. p)"],
        assumption,
        simp add:m_cf_len,
        thin_tac "polyn_expr R X 0 (0, \<lambda>j. p) \<plusminus>
     polyn_expr R X (fst (s_cf R S X p)) (m_cf S (s_cf R S X p)) =
     polyn_expr R X (fst (s_cf R S X p))
      (add_cf S (0, \<lambda>j. p) (m_cf S (s_cf R S X p)))")
     apply (rotate_tac -1, drule sym, simp)

       
 apply (frule_tac d = "m_cf S (s_cf R S X p)" in 
                      add_cf_pol_coeff[of "(0, \<lambda>j. p)"], assumption)
 apply (frule_tac c1 = "add_cf S (0, \<lambda>j. p) (m_cf S (s_cf R S X p))" and 
        k1 = "fst (s_cf R S X p)" in
         coeff_0_pol_0[THEN sym],
       simp add:add_cf_len m_cf_len, simp,
       thin_tac "pol_coeff S (add_cf S (0, \<lambda>j. p) (m_cf S (s_cf R S X p)))",
       thin_tac "polyn_expr R X (fst (s_cf R S X p))
      (add_cf S (0, \<lambda>j. p) (m_cf S (s_cf R S X p))) = \<zero>")
 apply (drule_tac a = "fst (s_cf R S X p)" in forall_spec, simp,
        simp add:add_cf_def m_cf_len m_cf_def)
 apply (frule_tac c = "s_cf R S X p" and j = "fst (s_cf R S X p)" in 
        pol_coeff_mem, simp,
        frule_tac x = "snd (s_cf R S X p) (fst (s_cf R S X p))" in 
        aGroup.ag_inv_inv[of S],
        assumption, simp add:aGroup.ag_inv_zero)
 apply (subst polyn_expr_def, simp add:ring_r_one)
 apply (simp add:pol_coeff_def)
done

lemma (in PolynRg) pols_const:"\<lbrakk>p \<in> carrier R; (deg R S X p) \<le> 0\<rbrakk>  \<Longrightarrow> 
                         p \<in> carrier S"  
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>")
 apply (cut_tac subring)
 apply (frule Subring_zero_ring_zero[THEN sym, of S], simp,
       cut_tac subring,
       frule subring_Ring[of S],
       rule Ring.ring_zero[of S], assumption)
apply (subst pol_of_deg0[THEN sym], assumption+,
       simp add:deg_def,
       simp only:an_0[THEN sym],
       simp add:an_inj)
done  

lemma (in PolynRg) less_deg_add_nonzero:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>; 
       q \<in> carrier R; q \<noteq> \<zero>; 
       (deg_n R S X p) < (deg_n R S X q)\<rbrakk>  \<Longrightarrow> p \<plusminus> q \<noteq> \<zero>"  
apply (frule ex_polyn_expr[of p], erule exE, erule conjE,
       frule ex_polyn_expr[of q], erule exE, erule conjE,
       rename_tac c d)
apply (frule_tac c = c in pol_deg_eq_c_max[of p], assumption+,
       frule_tac c = d in pol_deg_eq_c_max[of q], assumption+,
       frule_tac c = c in coeff_max_bddTr, 
       frule_tac c = d in coeff_max_bddTr)
apply (frule_tac c = c and n = "c_max S c" in pol_coeff_le, assumption,
       frule_tac c = d and n = "c_max S d" in pol_coeff_le, assumption+)
apply simp
apply (subst polyn_c_max, assumption,
       subst polyn_c_max, assumption,
       subst polyn_expr_short, assumption+)
 apply (frule_tac c = d and k = "c_max S d" in polyn_expr_short, assumption+,
       simp,
       thin_tac "polyn_expr R X (c_max S d) d =
           polyn_expr R X (c_max S d) (c_max S d, snd d)",
       thin_tac "deg_n R S X (polyn_expr R X (fst c) c) = c_max S c",
       thin_tac "deg_n R S X (polyn_expr R X (fst d) d) = c_max S d")
 
  apply (subst polyn_add, assumption+, simp add: max.absorb1 max.absorb2)
         
  apply (rule contrapos_pp, simp+,
         frule_tac c = "(c_max S c, snd c)" and d = "(c_max S d, snd d)" in 
         add_cf_pol_coeff, assumption+,
         frule_tac c1 = "add_cf S (c_max S c, snd c) (c_max S d, snd d)" and 
         k1 = "c_max S d" in coeff_0_pol_0[THEN sym],
         simp add:add_cf_len, simp,
       thin_tac "pol_coeff S (add_cf S (c_max S c, snd c) (c_max S d, snd d))",
       thin_tac "polyn_expr R X (c_max S d)
            (add_cf S (c_max S c, snd c) (c_max S d, snd d)) = \<zero>")
  apply (drule_tac a = "c_max S d" in forall_spec, simp,
         simp add:add_cf_def,
         frule_tac c = d and k = "fst d" in coeff_nonzero_polyn_nonzero,
         simp, simp,
         frule_tac c = d in coeff_max_nonzeroTr, assumption+, simp)
done

lemma (in PolynRg) polyn_deg_add1:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>; q \<in> carrier R; 
      q \<noteq> \<zero>; (deg_n R S X p) < (deg_n R S X q)\<rbrakk>  \<Longrightarrow>  
            deg_n R S X (p \<plusminus> q) = (deg_n R S X q)"
apply (cut_tac subring)
apply (frule less_deg_add_nonzero[of p q], assumption+)
apply (frule ex_polyn_expr[of p], erule exE, erule conjE,
       frule ex_polyn_expr[of q], erule exE, erule conjE,
       rename_tac c d)
      apply (simp only:pol_deg_eq_c_max)
apply (frule_tac c = c in coeff_max_bddTr,
       frule_tac c = d in coeff_max_bddTr)
apply (frule_tac c = c and n = "c_max S c" in pol_coeff_le, assumption,
       frule_tac c = d and n = "c_max S d" in pol_coeff_le, assumption)
apply (simp add:polyn_c_max)

apply (frule_tac c = c and k = "c_max S c" in polyn_expr_short, simp,
       frule_tac c = d and k = "c_max S d" in polyn_expr_short, simp,
       simp)
  apply (frule_tac c = "(c_max S c, snd c)" and d = "(c_max S d, snd d)" in 
         polyn_add1, assumption+, simp,
        thin_tac "polyn_expr R X (c_max S c) c =
           polyn_expr R X (c_max S c) (c_max S c, snd c)",
        thin_tac "polyn_expr R X (c_max S d) d =
           polyn_expr R X (c_max S d) (c_max S d, snd d)")
  apply (simp add: max.absorb1 max.absorb2)
  apply (frule_tac c = "(c_max S c, snd c)" and d = "(c_max S d, snd d)" in 
                  add_cf_pol_coeff, assumption+,
         rule_tac p = "polyn_expr R X (c_max S d)
            (add_cf S (c_max S c, snd c) (c_max S d, snd d))" and
          c = "add_cf S (c_max S c, snd c) (c_max S d, snd d)" and 
          n = "c_max S d" in pol_deg_n)
  apply (rule_tac polyn_mem, simp, simp add:add_cf_len,
         assumption,
         simp add:add_cf_len, simp,
         subst add_cf_def, simp)

  apply (frule_tac c1 = "(c_max S d, snd d)" and k1 = "c_max S d" in 
         coeff_0_pol_0[THEN sym], simp, simp,
         rule coeff_max_nonzeroTr, assumption+,
         erule exE, erule conjE,
         frule_tac i = j and j = "c_max S d" and k = "fst d" in
                le_trans, assumption+, blast)
done

lemma (in PolynRg) polyn_deg_add2:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>; q \<in> carrier R; 
      q \<noteq> \<zero>; p \<plusminus> q \<noteq> \<zero>; (deg_n R S X p) = (deg_n R S X q)\<rbrakk>  \<Longrightarrow> 
          deg_n R S X (p \<plusminus> q) \<le> (deg_n R S X q)"
apply (cut_tac subring)
apply (frule ex_polyn_expr[of p], erule exE, erule conjE,
       frule ex_polyn_expr[of q], erule exE, erule conjE,
       rename_tac c d)
      apply (simp only:pol_deg_eq_c_max)
apply (frule_tac c = c in coeff_max_bddTr,
       frule_tac c = d in coeff_max_bddTr)
apply (frule_tac c = c and n = "c_max S c" in pol_coeff_le, assumption,
       frule_tac c = d and n = "c_max S d" in pol_coeff_le, assumption)
apply (simp add:polyn_c_max)

apply (frule_tac c = c and k = "c_max S c" in polyn_expr_short, simp,
       frule_tac c = d and k = "c_max S d" in polyn_expr_short, simp,
       simp,
       frule_tac c = "(c_max S d, snd c)" and d = "(c_max S d, snd d)" in 
         polyn_add1, simp)
 apply (thin_tac "polyn_expr R X (c_max S d) d =
           polyn_expr R X (c_max S d) (c_max S d, snd d)",
        thin_tac "polyn_expr R X (c_max S d) c =
           polyn_expr R X (c_max S d) (c_max S d, snd c)", simp)
 apply (thin_tac "polyn_expr R X (c_max S d) (c_max S d, snd c) \<plusminus>
           polyn_expr R X (c_max S d) (c_max S d, snd d) =
           polyn_expr R X (c_max S d)
            (add_cf S (c_max S d, snd c) (c_max S d, snd d))")
  apply (frule_tac c = "(c_max S d, snd c)" and d = "(c_max S d, snd d)" in 
                  add_cf_pol_coeff, assumption+) 
 apply (cut_tac p = "polyn_expr R X (c_max S d)
                (add_cf S (c_max S d, snd c) (c_max S d, snd d))"
        and c = "add_cf S (c_max S d, snd c) (c_max S d, snd d)" in
        pol_deg_eq_c_max)
   apply (rule_tac polyn_mem, simp) 
      apply (simp add:add_cf_len,
              assumption,
             simp add:add_cf_len, simp)
      apply (thin_tac "deg_n R S X
            (polyn_expr R X (c_max S d)
              (add_cf S (c_max S d, snd c) (c_max S d, snd d))) =
           c_max S (add_cf S (c_max S d, snd c) (c_max S d, snd d))",
             thin_tac "polyn_expr R X (c_max S d)
            (add_cf S (c_max S d, snd c) (c_max S d, snd d)) \<noteq>
           \<zero>")

  apply (frule_tac c = "add_cf S (c_max S d, snd c) (c_max S d, snd d)" in 
         coeff_max_bddTr)
  apply (simp add:add_cf_len)
done

lemma (in PolynRg) polyn_deg_add3:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>; q \<in> carrier R; 
       q \<noteq> \<zero>; p \<plusminus> q \<noteq> \<zero>; (deg_n R S X p) \<le> n; (deg_n R S X q) \<le> n\<rbrakk>  \<Longrightarrow> 
          deg_n R S X (p \<plusminus> q) \<le> n"
apply (case_tac "(deg_n R S X p) = (deg_n R S X q)",
       frule polyn_deg_add2[of "p" "q"], assumption+,
       simp)
apply (cut_tac less_linear[of "deg_n R S X p" "deg_n R S X q"],
       simp, thin_tac "deg_n R S X p \<noteq> deg_n R S X q",
       erule disjE, simp add:polyn_deg_add1,
       cut_tac ring_is_ag, simp add:aGroup.ag_pOp_commute[of "R" "p" "q"],
       simp add:polyn_deg_add1)
done

lemma (in PolynRg) polyn_deg_add4:"\<lbrakk>p \<in> carrier R; q \<in> carrier R; 
      (deg R S X p) \<le> (an n); (deg R S X q) \<le> (an n)\<rbrakk>  \<Longrightarrow> 
                    deg R S X (p \<plusminus> q) \<le> (an n)"
apply (cut_tac ring_is_ag)
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp add:aGroup.ag_l_zero)
apply (case_tac "q =  \<zero>\<^bsub>R\<^esub>", simp add:aGroup.ag_r_zero)
apply (case_tac "p \<plusminus>\<^bsub>R\<^esub> q = \<zero>\<^bsub>R\<^esub>", simp add:deg_def)
apply (frule aGroup.ag_pOp_closed[of R p q], assumption+)
apply (simp add:deg_an)
apply (simp only:ale_natle)
apply (simp add:polyn_deg_add3)
done
   
lemma (in PolynRg) polyn_deg_add5:"\<lbrakk>p \<in> carrier R; q \<in> carrier R; 
       (deg R S X p) \<le> a; (deg R S X q) \<le> a\<rbrakk>  \<Longrightarrow> 
                                deg R S X (p \<plusminus> q) \<le> a"
apply (case_tac "a = \<infinity>", simp)
apply (cut_tac ring_is_ag,
       case_tac "p = \<zero>\<^bsub>R\<^esub>", simp add:aGroup.ag_l_zero[of R],
       case_tac "q = \<zero>\<^bsub>R\<^esub>", simp add:aGroup.ag_r_zero,
       simp add:deg_an[of p])
apply (cut_tac an_nat_pos[of "deg_n R S X p"],
       frule ale_trans[of "0" "an (deg_n R S X p)" "a"], assumption+,
       subgoal_tac "an (deg_n R S X p) \<le> an (na a)",
       simp only:ale_natle[of "deg_n R S X p" "na a"])

apply (simp add:deg_an[of q])
apply (cut_tac an_nat_pos[of "deg_n R S X q"],
       frule ale_trans[of "0" "an (deg_n R S X q)" "a"], assumption+,
       subgoal_tac "an (deg_n R S X q) \<le> an (na a)",
       simp only:ale_natle[of "deg_n R S X q" "na a"])
apply (frule polyn_deg_add4[of p q "na a"], assumption+,
       simp add:an_na, simp add:deg_an,
       simp add:deg_an an_na, simp add:an_na)
apply (simp add:deg_an an_na, simp add:deg_an an_na)
done 

lemma (in PolynRg) lower_deg_part:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>; 0 < deg_n R S X p\<rbrakk>
      \<Longrightarrow>  
 deg R S X (polyn_expr R X (deg_n R S X p - Suc 0)(SOME f. cf_sol R S X p f))
                       < deg R S X p" 
 apply (case_tac "polyn_expr R X (deg_n R S X p - Suc 0) 
                              (SOME f. cf_sol R S X p f) = \<zero>\<^bsub>R\<^esub>")
 apply (simp add:deg_def, cut_tac minf_le_any[of "an (deg_n R S X p)"])
 apply (subst less_le, simp, simp add:an_def)
 apply (rule not_sym, rule contrapos_pp, simp+)

 apply (simp add:deg_def, simp add:aless_natless) 
 apply (frule pol_SOME_2[of p], erule conjE)
 apply (simp add:pol_deg_eq_c_max[of p "SOME c. cf_sol R S X p c"])
 apply (frule_tac c = "SOME c. cf_sol R S X p c" in coeff_max_bddTr)

 apply (cut_tac 
  p = "polyn_expr R X (c_max S (SOME c. cf_sol R S X p c) - Suc 0)
          (Eps (cf_sol R S X p))" and c = "(c_max S (SOME c. cf_sol R S X p c) - Suc 0, snd (SOME c. cf_sol R S X p c))" in pol_deg_eq_c_max)
  
  apply (rule polyn_mem, simp, arith)
  apply (rule pol_coeff_le, assumption, arith)
  apply (subst polyn_expr_short, arith, arith, simp)
  apply simp

  apply (cut_tac c = "(c_max S (SOME c. cf_sol R S X p c) - Suc 0,
         snd (SOME c. cf_sol R S X p c))" in coeff_max_bddTr,
         rule pol_coeff_le, assumption, arith, simp)
done 

definition
  ldeg_p :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a, nat, 'a]
                  \<Rightarrow> 'a" where
  "ldeg_p R S X d p = polyn_expr R X d (scf_d R S X p (Suc d))"
      (** deg R S X p \<le> (Suc d) **)

definition
  hdeg_p :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a, nat, 'a]
                  \<Rightarrow> 'a" where
  "hdeg_p R S X d p = (snd (scf_d R S X p d) d) \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>)"
       (** deg R S X p \<le> d **) 

lemma (in PolynRg) ldeg_p_mem:"\<lbrakk>p \<in> carrier R; deg R S X p \<le> an (Suc d) \<rbrakk> \<Longrightarrow>
                      ldeg_p R S X d p \<in> carrier R"
apply (frule scf_d_pol[of "p" "Suc d"], assumption+, 
       erule conjE)
apply (simp add:ldeg_p_def)
apply (rule polyn_mem[of "scf_d R S X p (Suc d)" d],
         assumption+)
apply simp
done

lemma (in PolynRg) ldeg_p_zero:"p = \<zero>\<^bsub>R\<^esub> \<Longrightarrow> ldeg_p R S X d p = \<zero>\<^bsub>R\<^esub>"
apply (subgoal_tac "deg R S X p \<le> an (Suc d)",
       subgoal_tac "p \<in> carrier R")
apply (frule scf_d_pol[of "p" "Suc d"], assumption+, 
       erule conjE)
apply simp
apply (frule coeff_0_pol_0[of "scf_d R S X \<zero> (Suc d)" "Suc d"], simp)
apply (simp add:ldeg_p_def)
apply (subst coeff_0_pol_0[THEN sym, of "scf_d R S X \<zero> (Suc d)"],
        assumption+, simp)
apply (rule allI, rule impI, simp)
apply (simp, simp add:ring_zero)
apply (simp add:deg_def)
done
 
lemma (in PolynRg) hdeg_p_mem:"\<lbrakk>p \<in> carrier R; deg R S X p \<le> an (Suc d)\<rbrakk> \<Longrightarrow>
                      hdeg_p R S X (Suc d) p \<in> carrier R" 
apply (frule scf_d_pol[of p "Suc d"], assumption+, erule conjE)
apply (simp only:hdeg_p_def, (erule conjE)+)
apply (cut_tac Ring)
apply (rule Ring.ring_tOp_closed[of "R"], assumption)
apply (frule pol_coeff_mem[of "scf_d R S X p (Suc d)" "Suc d"], simp)
apply (cut_tac subring)
apply (simp add:Ring.mem_subring_mem_ring)
apply (rule Ring.npClose[of "R"], assumption+)
apply (rule X_mem_R)
done


   
(*   *****************************************************************
definition ldeg_p :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a, 'a]
                  \<Rightarrow> 'a" where
 "ldeg_p R S X p == if p = \<zero>\<^bsub>R\<^esub> then \<zero>\<^bsub>R\<^esub> 
                       else if deg_n R S X p = 0 then p
                       else polyn_expr R X (fst (s_cf R S X p)  - Suc 0) 
                                                         (s_cf R S X p)" *)
      (** deg R S X p \<le> (Suc d), lower degree part **) (*
definition hdeg_p :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a,'a]
                  \<Rightarrow> 'a" where
 "hdeg_p R S X p == if p = \<zero>\<^bsub>R\<^esub> then \<zero>\<^bsub>R\<^esub> else 
                     (if (deg_n R S X p) = 0 then \<zero>\<^bsub>R\<^esub> else
                      (snd (s_cf R S X p) (fst (s_cf R S X p))) \<cdot>\<^sub>r\<^bsub>R\<^esub> 
                              X^\<^bsup>R (fst (s_cf R S X p))\<^esup>)" *)
       (** deg R S X p \<le> d, the highest degree term  **)

(*
lemma (in PolynRg) ldeg_p_mem:"p \<in> carrier R  \<Longrightarrow> ldeg_p R S X p \<in> carrier R"
apply (simp add:ldeg_p_def)
 apply (simp add:ring_zero)
 apply (rule impI, rule impI)
apply (frule s_cf_pol_coeff[of p])
 apply (simp add:polyn_mem)
done   
    
lemma (in PolynRg) ldeg_p_zero:"ldeg_p R S X \<zero> = \<zero>"
apply (simp add:ldeg_p_def)
done 

lemma (in PolynRg) ldeg_p_zero1:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>; deg_n R S X p = 0\<rbrakk> \<Longrightarrow>
                   ldeg_p R S X p = p"
by (simp add:ldeg_p_def)
 
lemma (in PolynRg) hdeg_p_mem:"p \<in> carrier R  \<Longrightarrow>
                                   hdeg_p R S X p \<in> carrier R"
apply (cut_tac ring_is_ag)
apply (cut_tac subring)
apply (simp add:hdeg_p_def)
 apply (case_tac "deg_n R S X p = 0", simp add:aGroup.ag_inc_zero)
apply simp
 apply (simp add:aGroup.ag_inc_zero)
 apply (rule impI)
 apply (frule s_cf_pol_coeff[of p])
 apply (cut_tac X_mem_R,
        rule ring_tOp_closed) 
 apply (simp add:pol_coeff_mem mem_subring_mem_ring)
 apply (rule npClose, assumption)
done *)

lemma (in PolynRg) hdeg_p_zero:"p = \<zero> \<Longrightarrow> hdeg_p R S X (Suc d) p = \<zero>"
apply (cut_tac X_mem_R)
apply (subgoal_tac "deg R S X p \<le> an (Suc d)",
       subgoal_tac "p \<in> carrier R")
apply (frule scf_d_pol[of p "Suc d"], assumption+, erule conjE)
apply simp
apply (frule coeff_0_pol_0[of "scf_d R S X \<zero> (Suc d)" "Suc d"], 
        (erule conjE)+, simp)
apply (simp only:hdeg_p_def)
 apply (rotate_tac -1, drule sym, simp del:npow_suc)
apply (cut_tac subring, 
       simp del:npow_suc add:Subring_zero_ring_zero,
       rule ring_times_0_x, rule npClose, assumption)
apply (simp add:ring_zero)
apply (simp add:deg_def)
done

lemma (in PolynRg) decompos_p:"\<lbrakk>p \<in> carrier R; deg R S X p \<le> an (Suc d)\<rbrakk> \<Longrightarrow>
                p = (ldeg_p R S X d p) \<plusminus> (hdeg_p R S X (Suc d) p)"
apply (frule scf_d_pol[of  p "Suc d"], assumption+, erule conjE)
apply (cut_tac subring, (erule conjE)+)
 apply (cut_tac polyn_Suc[of d "scf_d R S X p (Suc d)"])
 apply (simp only:ldeg_p_def hdeg_p_def)
 apply (rotate_tac -1, drule sym, simp del:npow_suc)
 apply (thin_tac "polyn_expr R X d (scf_d R S X p (Suc d)) \<plusminus>
     snd (scf_d R S X p (Suc d)) (Suc d) \<cdot>\<^sub>r X^\<^bsup>R (Suc d)\<^esup> =
     polyn_expr R X (Suc d) (Suc d, snd (scf_d R S X p (Suc d)))")
 apply (simp add:polyn_expr_split[of "Suc d" "scf_d R S X p (Suc d)"],
        simp)
done

lemma (in PolynRg) deg_ldeg_p:"\<lbrakk>p \<in> carrier R; deg R S X p \<le> an (Suc d)\<rbrakk>  \<Longrightarrow>  
                deg R S X (ldeg_p R S X d p) \<le> an d"
apply (cut_tac subring,
       frule subring_Ring)
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>")
apply (simp add:ldeg_p_zero, simp add:deg_def)
apply (frule scf_d_pol[of p "Suc d"], assumption+, (erule conjE)+)
apply (simp only:ldeg_p_def)
apply (case_tac "polyn_expr R X d (scf_d R S X p (Suc d)) = \<zero>\<^bsub>R\<^esub>")
apply (simp add:deg_def)

apply (simp add:deg_an)
apply (simp add:ale_natle)
apply (cut_tac pol_deg_le_n1[of "polyn_expr R X d (scf_d R S X p (Suc d))" 
       "scf_d R S X p (Suc d)" d], simp add:deg_def ale_natle)
apply (rule polyn_mem, assumption+, simp+) 
done

lemma (in PolynRg) deg_minus_eq:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>\<rbrakk> \<Longrightarrow>  
                    deg_n R S X (-\<^sub>a p) = deg_n R S X p"
apply (cut_tac subring, 
       cut_tac ring_is_ag,
       frule subring_Ring)
apply (cut_tac ring_is_ag)
 apply (frule s_cf_expr[of p], assumption, (erule conjE)+,
        frule polyn_minus_m_cf[of "s_cf R S X p" "fst (s_cf R S X p)"], simp,
        drule sym, simp)
 apply (frule_tac x = p in aGroup.ag_mOp_closed, assumption+,
        frule m_cf_pol_coeff [of "s_cf R S X p"],
        frule pol_deg_n[of "-\<^sub>a p" "m_cf S (s_cf R S X p)" 
              "fst (s_cf R S X p)"], assumption,
        simp add:m_cf_len, assumption+)
 apply (simp add:m_cf_def,
        frule pol_coeff_mem[of "s_cf R S X p" "fst (s_cf R S X p)"], simp,
        frule Ring.ring_is_ag[of S])
 apply (rule contrapos_pp, simp+)
 apply (frule aGroup.ag_inv_inv[THEN sym, 
          of S "snd (s_cf R S X p) (fst (s_cf R S X p))"], assumption,
        simp add:aGroup.ag_inv_zero)
 apply (drule sym, simp, simp add:s_cf_deg)
done

lemma (in PolynRg) deg_minus_eq1:"p \<in> carrier R \<Longrightarrow> 
                       deg R S X (-\<^sub>a p) = deg R S X p"
apply (cut_tac ring_is_ag)
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>")
apply (simp add:aGroup.ag_inv_zero)
apply (frule deg_minus_eq[of p], assumption+,
       frule aGroup.ag_inv_inj[of "R" "p" "\<zero>"], assumption,
       simp add:ring_zero, assumption, simp add:aGroup.ag_inv_zero)
apply (frule aGroup.ag_mOp_closed[of R p], assumption,
       simp add:deg_an)
done

lemma (in PolynRg) ldeg_p_pOp:"\<lbrakk>p \<in> carrier R; q \<in> carrier R;
      deg R S X p \<le> an (Suc d); deg R S X q \<le> an (Suc d)\<rbrakk> \<Longrightarrow>
      (ldeg_p R S X d p) \<plusminus>\<^bsub>R\<^esub> (ldeg_p R S X d q) =
                              ldeg_p R S X d (p \<plusminus>\<^bsub>R\<^esub> q)"
apply (simp add:ldeg_p_def,
       cut_tac ring_is_ag, cut_tac subring, frule subring_Ring[of S],
       frule scf_d_pol[of p "Suc d"], assumption+,
       frule scf_d_pol[of q "Suc d"], assumption+, (erule conjE)+)
apply (frule polyn_add1[of "scf_d R S X p (Suc d)" "scf_d R S X q (Suc d)"],
       assumption+,
       rotate_tac -2, drule sym,
       frule aGroup.ag_pOp_closed[of "R" "p" "q"], assumption+,
       frule polyn_deg_add4 [of p q "Suc d"], assumption+,
       rotate_tac -5, drule sym) 
apply simp
apply (rotate_tac 4, drule sym, simp) 

apply (rotate_tac -1, drule sym,
       frule scf_d_pol[of "p \<plusminus> q" "Suc d"], assumption+, (erule conjE)+,
       frule box_equation[of "p \<plusminus> q" "polyn_expr R X (Suc d)
        (add_cf S (scf_d R S X p (Suc d)) (scf_d R S X q (Suc d)))" 
        "polyn_expr R X (Suc d) (scf_d R S X (p \<plusminus> q) (Suc d))"], assumption+,
       thin_tac "p \<plusminus> q =
        polyn_expr R X (Suc d) (scf_d R S X (p \<plusminus> q) (Suc d))")
apply (frule add_cf_pol_coeff[of "scf_d R S X p (Suc d)" 
                   "scf_d R S X q (Suc d)"],  assumption+)
apply (frule pol_expr_unique2[of "add_cf S (scf_d R S X p (Suc d)) 
       (scf_d R S X q (Suc d))" "scf_d R S X (p \<plusminus> q) (Suc d)"], assumption+)
 apply (subst add_cf_len[of "scf_d R S X p (Suc d)" "scf_d R S X q (Suc d)"], 
       assumption+) 
 apply (thin_tac "polyn_expr R X (Suc d) (scf_d R S X p (Suc d)) = p",
        thin_tac "polyn_expr R X (Suc d) (scf_d R S X q (Suc d)) = q",
        thin_tac "p \<plusminus> q = polyn_expr R X (Suc d)
          (add_cf S (scf_d R S X p (Suc d)) (scf_d R S X q (Suc d)))",
        thin_tac "polyn_expr R X (Suc d)
          (add_cf S (scf_d R S X p (Suc d)) (scf_d R S X q (Suc d))) =
           polyn_expr R X (Suc d) (scf_d R S X (p \<plusminus> q) (Suc d))")
 apply simp
 apply (thin_tac "polyn_expr R X (Suc d) (scf_d R S X p (Suc d)) = p",
        thin_tac "polyn_expr R X (Suc d) (scf_d R S X q (Suc d)) = q",
        thin_tac "p \<plusminus> q = polyn_expr R X (Suc d)
          (add_cf S (scf_d R S X p (Suc d)) (scf_d R S X q (Suc d)))")

 apply (simp add:add_cf_len,
       thin_tac "polyn_expr R X (Suc d)
      (add_cf S (scf_d R S X p (Suc d)) (scf_d R S X q (Suc d))) =
     polyn_expr R X (Suc d) (scf_d R S X (p \<plusminus> q) (Suc d))")
 apply (subst  polyn_expr_short[of "scf_d R S X p (Suc d)" d], assumption,
        simp)
 apply (subst  polyn_expr_short[of "scf_d R S X q (Suc d)" d], assumption,
        simp)
 apply (subst polyn_add_n[of d "snd (scf_d R S X p (Suc d))" 
               "snd (scf_d R S X q (Suc d))"])
 apply (simp add:split_pol_coeff, simp add:split_pol_coeff,
        subst polyn_expr_def)
 apply (rule aGroup.nsum_eq, assumption+,
        rule allI, rule impI,
        frule_tac j = j in pol_coeff_mem[of "scf_d R S X p (Suc d)"],
               simp,
        frule_tac j = j in pol_coeff_mem[of "scf_d R S X q (Suc d)"],
               simp,
        cut_tac Ring, rule Ring.ring_tOp_closed, assumption+,
        rule Ring.mem_subring_mem_ring[of R S], assumption+,
        frule Ring.ring_is_ag[of S], rule aGroup.ag_pOp_closed[of S],
               assumption+,
        rule Ring.npClose, assumption, simp add:X_mem_R)
 apply (rule allI, rule impI,
        frule_tac j = j in pol_coeff_mem[of "scf_d R S X (p \<plusminus> q) (Suc d)"], 
        simp, cut_tac Ring,
        subst Ring.ring_tOp_closed, assumption,
        rule Ring.mem_subring_mem_ring[of R S], assumption+,
        rule Ring.npClose, assumption, simp add:X_mem_R,
        simp)
 apply (rule allI, rule impI,
        drule_tac a = j in forall_spec, simp,
        thin_tac " pol_coeff S
          (add_cf S (scf_d R S X p (Suc d)) (scf_d R S X q (Suc d)))")
 apply (simp add:add_cf_def)
done

lemma (in PolynRg) hdeg_p_pOp:"\<lbrakk>p \<in> carrier R; q \<in> carrier R;
      deg R S X p \<le> an (Suc d); deg R S X q \<le> an (Suc d)\<rbrakk> \<Longrightarrow>
      (hdeg_p R S X (Suc d) p) \<plusminus> (hdeg_p R S X (Suc d) q) =
                              hdeg_p R S X (Suc d) (p \<plusminus> q)"
apply (cut_tac Ring, frule Ring.ring_is_ag[of "R"])
apply (cut_tac subring, frule subring_Ring[of S])
apply (frule scf_d_pol[of p "Suc d"], assumption+,
       frule scf_d_pol[of q "Suc d"], assumption+,
        (erule conjE)+)
apply (frule polyn_add1[of "scf_d R S X p (Suc d)" "scf_d R S X q (Suc d)"],
       assumption+,
       rotate_tac -2, drule sym,
       frule aGroup.ag_pOp_closed[of "R" "p" "q"], assumption+,
       frule polyn_deg_add4 [of p q "Suc d"], assumption+,
       rotate_tac -5, drule sym) 
apply simp
apply (rotate_tac -13, drule sym, simp)
apply (rotate_tac -1, drule sym)
apply (frule scf_d_pol[of "p \<plusminus> q" "Suc d"], assumption+, (erule conjE)+)
apply (drule box_equation[of "p \<plusminus> q" "polyn_expr R X (Suc d)
       (add_cf S (scf_d R S X p (Suc d)) (scf_d R S X q (Suc d)))" 
       "polyn_expr R X (Suc d) (scf_d R S X (p \<plusminus> q) (Suc d))"],
       assumption+) apply (
      thin_tac "p \<plusminus> q = polyn_expr R X (Suc d) (scf_d R S X (p \<plusminus> q) (Suc d))")
apply (frule add_cf_pol_coeff[of "scf_d R S X p (Suc d)"
        "scf_d R S X q (Suc d)"], assumption+)
apply (cut_tac pol_expr_unique2[of "add_cf S (scf_d R S X p (Suc d)) 
       (scf_d R S X q (Suc d))" "scf_d R S X (p \<plusminus> q) (Suc d)"], 
       simp add:add_cf_len) 
apply (drule_tac a = "Suc d" in forall_spec, simp)
 apply (simp del:npow_suc add:hdeg_p_def)
 apply (rotate_tac -1, drule sym, simp del:npow_suc)
 apply (subst add_cf_def, simp del:npow_suc)
 apply (thin_tac "polyn_expr R X (Suc d) (scf_d R S X p (Suc d)) = p",
        thin_tac "polyn_expr R X (Suc d) (scf_d R S X q (Suc d)) = q",
        thin_tac "polyn_expr R X (Suc d) (add_cf S (scf_d R S X p (Suc d)) 
         (scf_d R S X q (Suc d))) =
          polyn_expr R X (Suc d) (scf_d R S X (p \<plusminus> q) (Suc d))",
        thin_tac "pol_coeff S (add_cf S (scf_d R S X p (Suc d)) 
                  (scf_d R S X q (Suc d)))",
        thin_tac "snd (scf_d R S X (p \<plusminus> q) (Suc d)) (Suc d) =
     snd (add_cf S (scf_d R S X p (Suc d)) (scf_d R S X q (Suc d))) (Suc d)")
 apply (frule pol_coeff_mem[of "scf_d R S X p (Suc d)" "Suc d"], 
        simp del:npow_suc,
        frule pol_coeff_mem[of "scf_d R S X q (Suc d)" "Suc d"], 
        simp del:npow_suc)
 apply (simp del:npow_suc add:Subring_pOp_ring_pOp)
 apply (frule mem_subring_mem_ring[of S "snd (scf_d R S X p (Suc d)) (Suc d)"],
        assumption,
        frule mem_subring_mem_ring[of S "snd (scf_d R S X q (Suc d)) (Suc d)"],
        assumption,
        cut_tac X_mem_R, frule Ring.npClose[of R X "Suc d"], assumption+)
 apply (subst Ring.ring_distrib2[THEN sym], assumption+, simp)

 apply (simp add:add_cf_pol_coeff, simp)
 apply (simp add:add_cf_len)
done

lemma (in PolynRg) ldeg_p_mOp:"\<lbrakk>p \<in> carrier R; deg R S X p \<le> an (Suc d)\<rbrakk> \<Longrightarrow> 
       -\<^sub>a (ldeg_p R S X d p) = ldeg_p R S X d (-\<^sub>a p)"
apply (cut_tac Ring, frule Ring.ring_is_ag[of "R"],
       cut_tac subring, frule subring_Ring[of S],
       frule scf_d_pol[of p "Suc d"], assumption+, (erule conjE)+,
       frule aGroup.ag_mOp_closed[of R p], assumption,
       frule scf_d_pol[of "-\<^sub>a p" "Suc d"])
apply (simp add:deg_minus_eq1, (erule conjE)+)
apply (frule polyn_minus[of "scf_d R S X p (Suc d)"  "Suc d"], simp)
apply (drule box_equation[of "-\<^sub>a p" "polyn_expr R X (Suc d)
       (scf_d R S X (-\<^sub>a p) (Suc d))"
       "polyn_expr R X (Suc d) (fst (scf_d R S X p (Suc d)), 
                \<lambda>j. -\<^sub>a\<^bsub>S\<^esub> snd (scf_d R S X p (Suc d)) j)"])
apply (rotate_tac 8, drule sym, simp,
       thin_tac "-\<^sub>a polyn_expr R X (Suc d) (scf_d R S X p (Suc d)) =
       polyn_expr R X (Suc d)
       (fst (scf_d R S X p (Suc d)), \<lambda>j. -\<^sub>a\<^bsub>S\<^esub> snd (scf_d R S X p (Suc d)) j)")
apply simp
apply (frule pol_expr_unique2[of "scf_d R S X (-\<^sub>a p) (Suc d)" 
       "(Suc d, \<lambda>j. -\<^sub>a\<^bsub>S\<^esub> snd (scf_d R S X p (Suc d)) j)"])
 apply (subst pol_coeff_def, rule allI, rule impI, simp)
 apply (frule_tac j = j in pol_coeff_mem[of "scf_d R S X p (Suc d)"],
        simp,
        frule Ring.ring_is_ag[of S],
        rule aGroup.ag_mOp_closed[of S], assumption+, simp)
 apply simp

 apply (simp add:ldeg_p_def)
 apply (subst polyn_minus[of "scf_d R S X p (Suc d)" d], assumption, simp,
        simp)
 apply (subst polyn_expr_short[of "(Suc d, 
              \<lambda>j. -\<^sub>a\<^bsub>S\<^esub> snd (scf_d R S X p (Suc d)) j)" d])
  apply (subst pol_coeff_def, rule allI, rule impI, simp,
         frule_tac j = j in pol_coeff_mem[of "scf_d R S X p (Suc d)"],
         simp,
         frule Ring.ring_is_ag[of S],
         rule aGroup.ag_mOp_closed[of S], assumption+, simp) 
  apply (subst polyn_expr_short[of "scf_d R S X (-\<^sub>a p) (Suc d)" d], 
          assumption, simp)
 apply (cut_tac pol_expr_unique2[of "(d, snd (Suc d, 
                \<lambda>j. -\<^sub>a\<^bsub>S\<^esub> snd (scf_d R S X p (Suc d)) j))" 
                "(d, snd (scf_d R S X (-\<^sub>a p) (Suc d)))"])
 apply (thin_tac "p = polyn_expr R X (Suc d) (scf_d R S X p (Suc d))",
        thin_tac "polyn_expr R X (Suc d) (scf_d R S X (-\<^sub>a p) (Suc d)) =
     polyn_expr R X (Suc d) (Suc d, \<lambda>j. -\<^sub>a\<^bsub>S\<^esub> snd (scf_d R S X p (Suc d)) j)",
        simp)
  apply (subst pol_coeff_def, rule allI, rule impI, simp,
         frule Ring.ring_is_ag[of S], rule aGroup.ag_mOp_closed, assumption,
         simp add:pol_coeff_mem)
  apply (subst pol_coeff_def, rule allI, rule impI, simp,
         frule Ring.ring_is_ag[of S], rule aGroup.ag_mOp_closed, assumption,
         simp add:pol_coeff_mem)
  apply simp
done

lemma (in PolynRg) hdeg_p_mOp:"\<lbrakk>p \<in> carrier R;deg R S X p \<le> an (Suc d)\<rbrakk> 
  \<Longrightarrow> -\<^sub>a (hdeg_p R S X (Suc d) p) = hdeg_p R S X (Suc d) (-\<^sub>a p)"
apply (cut_tac Ring, frule Ring.ring_is_ag[of "R"],
       cut_tac subring, frule subring_Ring[of S],
       frule scf_d_pol[of p "Suc d"], assumption+, (erule conjE)+,
       frule aGroup.ag_mOp_closed[of R p], assumption) apply (
       frule scf_d_pol[of "-\<^sub>a p" "Suc d"])
apply (simp add:deg_minus_eq1, (erule conjE)+)
apply (frule polyn_minus[of "scf_d R S X p (Suc d)"  "Suc d"], simp)
apply (drule box_equation[of "-\<^sub>a p" "polyn_expr R X (Suc d)
       (scf_d R S X (-\<^sub>a p) (Suc d))"
       "polyn_expr R X (Suc d) (fst (scf_d R S X p (Suc d)), 
                \<lambda>j. -\<^sub>a\<^bsub>S\<^esub> snd (scf_d R S X p (Suc d)) j)"])
apply (rotate_tac 8, drule sym, simp,
       thin_tac "-\<^sub>a polyn_expr R X (Suc d) (scf_d R S X p (Suc d)) =
       polyn_expr R X (Suc d)
       (fst (scf_d R S X p (Suc d)), \<lambda>j. -\<^sub>a\<^bsub>S\<^esub> snd (scf_d R S X p (Suc d)) j)")
apply simp

apply (frule pol_expr_unique2[of "scf_d R S X (-\<^sub>a p) (Suc d)" 
       "(Suc d, \<lambda>j. -\<^sub>a\<^bsub>S\<^esub> snd (scf_d R S X p (Suc d)) j)"])
 apply (subst pol_coeff_def, rule allI, rule impI, simp)
 apply (frule_tac j = j in pol_coeff_mem[of "scf_d R S X p (Suc d)"],
        simp,
        frule Ring.ring_is_ag[of S],
        rule aGroup.ag_mOp_closed[of S], assumption+, simp)
 apply simp
 apply (drule_tac a = "Suc d" in forall_spec, simp)
 apply (simp del:npow_suc add:hdeg_p_def)
 apply (thin_tac "p = polyn_expr R X (Suc d) (scf_d R S X p (Suc d))",
        thin_tac "polyn_expr R X (Suc d) (scf_d R S X (-\<^sub>a p) (Suc d)) =
     polyn_expr R X (Suc d) (Suc d, \<lambda>j. -\<^sub>a\<^bsub>S\<^esub> snd (scf_d R S X p (Suc d)) j)",
        thin_tac "snd (scf_d R S X (-\<^sub>a p) (Suc d)) (Suc d) =
     -\<^sub>a\<^bsub>S\<^esub> snd (scf_d R S X p (Suc d)) (Suc d)")
 apply (frule pol_coeff_mem[of "scf_d R S X p (Suc d)" "Suc d"], simp,
        frule mem_subring_mem_ring[of S "snd (scf_d R S X p (Suc d)) (Suc d)"],
        assumption+,
        frule Ring.npClose[of R X "Suc d"], simp add:X_mem_R)
apply (subst Ring.ring_inv1_1[of "R"], assumption+)
apply (simp del:npow_suc add:Subring_minus_ring_minus)
done

subsection "Multiplication of polynomials"

lemma (in PolynRg) deg_mult_pols:"\<lbrakk>Idomain S;
      p \<in> carrier R; p \<noteq> \<zero>; q \<in> carrier R; q \<noteq> \<zero> \<rbrakk> \<Longrightarrow> 
      p \<cdot>\<^sub>r q \<noteq> \<zero> \<and>
     deg_n R S X (p \<cdot>\<^sub>r q) = deg_n R S X p + deg_n R S X q"
apply (frule Idomain.idom_is_ring[of "S"],
       frule_tac x = p and y = q in ring_tOp_closed, assumption+)
 apply (frule s_cf_expr[of p], assumption,
        frule s_cf_expr[of q], assumption, (erule conjE)+)
 apply (frule_tac c = "s_cf R S X p" and d = "s_cf R S X q" in 
        polyn_expr_tOp_c, assumption, erule exE, (erule conjE)+)
 apply (drule sym, drule sym, simp,
        thin_tac "polyn_expr R X (fst (s_cf R S X q)) (s_cf R S X q) = q",
        thin_tac "polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p) = p")
 apply (rotate_tac -1, drule sym,
        frule ring_tOp_closed[of p q], assumption+,
        frule pol_coeff_mem[of "s_cf R S X p" "fst (s_cf R S X p)"], simp,
        frule pol_coeff_mem[of "s_cf R S X q" "fst (s_cf R S X q)"], simp,
        frule_tac x = "snd (s_cf R S X p) (fst (s_cf R S X p))" and 
        y = "snd (s_cf R S X q) (fst (s_cf R S X q))" in 
        Idomain.idom_tOp_nonzeros[of "S"], assumption+,
        frule_tac c = e in  coeff_nonzero_polyn_nonzero[ of _ 
        "deg_n R S X p + deg_n R S X q"], simp)
 apply (simp add:s_cf_deg, simp add:s_cf_deg)
 apply (cut_tac n = "fst (s_cf R S X p) + fst (s_cf R S X q)" in le_refl)
 apply (subgoal_tac "\<exists>j\<le>fst (s_cf R S X p) + 
                       fst (s_cf R S X q). snd e j \<noteq> \<zero>\<^bsub>S\<^esub>", simp)
 apply (cut_tac c = e in pol_deg_n[of "p \<cdot>\<^sub>r q" _ 
                "fst (s_cf R S X p) + fst (s_cf R S X q)"], simp+)
  apply (thin_tac "(polyn_expr R X (fst (s_cf R S X p) + 
          fst (s_cf R S X q)) e \<noteq> \<zero>) =
         (\<exists>j\<le>fst (s_cf R S X p) + fst (s_cf R S X q). snd e j \<noteq> \<zero>\<^bsub>S\<^esub>)",
        thin_tac "p \<cdot>\<^sub>r q =
         polyn_expr R X (fst (s_cf R S X p) + fst (s_cf R S X q)) e",
        thin_tac "polyn_expr R X (fst (s_cf R S X p) + fst (s_cf R S X q)) e
         \<in> carrier R",
        thin_tac "snd (s_cf R S X p) (fst (s_cf R S X p)) \<in> carrier S",
        thin_tac "snd (s_cf R S X q) (fst (s_cf R S X q)) \<in> carrier S")
 apply (drule sym, drule sym, simp)
 apply (cut_tac n = "fst e" in le_refl, blast)
done
      
lemma (in PolynRg) deg_mult_pols1:"\<lbrakk>Idomain S; p \<in> carrier R; q \<in> carrier R\<rbrakk>
       \<Longrightarrow> 
          deg R S X (p \<cdot>\<^sub>r q) = deg R S X p + deg R S X q"
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp add:ring_times_0_x, simp add:deg_def,
       rule impI) 
 apply (simp add:an_def)
apply (case_tac "q = \<zero>\<^bsub>R\<^esub>", simp add:ring_times_x_0, simp add:deg_def)
 apply (simp add:an_def)

apply (frule deg_mult_pols[of p q], assumption+, erule conjE)
apply (frule Idomain.idom_is_ring[of "S"])
apply (frule ring_tOp_closed[of p q], assumption+)
apply (simp add:deg_an an_def a_zpz)
done
       
lemma (in PolynRg) const_times_polyn:"\<lbrakk>Idomain S; c \<in> carrier S; c \<noteq> \<zero>\<^bsub>S\<^esub>; 
       p \<in> carrier R; p \<noteq> \<zero>\<rbrakk> \<Longrightarrow> (c \<cdot>\<^sub>r p) \<noteq> \<zero>  \<and>
       deg_n R S X (c \<cdot>\<^sub>r p) = deg_n R S X p"
apply (frule Idomain.idom_is_ring[of "S"],
       cut_tac subring,
       frule mem_subring_mem_ring[of S c], assumption+,
       simp add:Subring_zero_ring_zero)
apply (frule deg_mult_pols[of c p], assumption+,
       erule conjE, simp,
       simp add:pol_of_deg0[THEN sym, of "c"])
done

(*lemma (in PolynRg) deg_minus_eq:"\<lbrakk>ring R; integral_domain S; polyn_ring R S X; 
p \<in> carrier R; p \<noteq> 0\<^sub>R\<rbrakk> \<Longrightarrow>   deg_n R S X (-\<^sub>R p) = deg_n R S X p" *)

lemma (in PolynRg) p_times_monomial_nonzero:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
                                                          (X^\<^bsup>R j\<^esup>) \<cdot>\<^sub>r p \<noteq> \<zero>"
apply (cut_tac subring, frule subring_Ring)
apply (frule s_cf_expr[of p], assumption+, (erule conjE)+)
apply (frule low_deg_terms_zero1[THEN sym, of "s_cf R S X p" j])
 apply (drule sym, simp,
        thin_tac "X^\<^bsup>R j\<^esup> \<cdot>\<^sub>r p =
     polyn_expr R X (fst (s_cf R S X p) + j) (ext_cf S j (s_cf R S X p))",
         thin_tac "polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p) = p")
 apply (frule ext_cf_pol_coeff[of "s_cf R S X p" j])
 apply(frule coeff_nonzero_polyn_nonzero[of "ext_cf S j (s_cf R S X p)"
                                      "fst (ext_cf S j (s_cf R S X p))"],
       simp)
 apply (simp add:ext_cf_len add.commute[of j],
     thin_tac "(polyn_expr R X (fst (s_cf R S X p) + j) 
         (ext_cf S j (s_cf R S X p)) \<noteq> \<zero>) =
     (\<exists>ja\<le>fst (s_cf R S X p) + j. snd (ext_cf S j (s_cf R S X p)) ja \<noteq> \<zero>\<^bsub>S\<^esub>)")
 apply (cut_tac ext_cf_hi[of "s_cf R S X p" j], simp,
        thin_tac "snd (s_cf R S X p) (fst (s_cf R S X p)) =
        snd (ext_cf S j (s_cf R S X p)) (j + fst (s_cf R S X p))",
        simp add:add.commute[of _ j])
 apply (cut_tac n = "j + fst (s_cf R S X p)" in le_refl, blast)
 apply assumption
done

lemma (in PolynRg) p_times_monomial_nonzero1:"\<lbrakk>Idomain S; p \<in> carrier R; 
       p \<noteq> \<zero>; c \<in> carrier S; c \<noteq> \<zero>\<^bsub>S\<^esub>\<rbrakk> \<Longrightarrow>(c \<cdot>\<^sub>r (X^\<^bsup>R j\<^esup>)) \<cdot>\<^sub>r p \<noteq> \<zero>"
apply (frule Idomain.idom_is_ring[of "S"],
       cut_tac subring,
       cut_tac X_mem_R ,
       frule mem_subring_mem_ring[of S c], assumption+,
       frule npClose[of X j])
apply (simp add:ring_tOp_commute[of c],
       simp add:ring_tOp_assoc,
       frule const_times_polyn[of c p], assumption+,
       erule conjE,
       frule ring_tOp_closed[of c p], assumption+,
       simp add:p_times_monomial_nonzero[of "c \<cdot>\<^sub>r p"])
done

lemma (in PolynRg) polyn_ring_integral:"Idomain S = Idomain R"
apply (cut_tac subring, frule subring_Ring)
apply (rule iffI)
apply (subst Idomain_def) 
 apply (cut_tac Ring, simp)
 
 apply (rule Idomain_axioms.intro,
        rule contrapos_pp, simp+, erule conjE,
        frule_tac p = a and q = b in deg_mult_pols,
       assumption+, erule conjE, simp)

apply (subst Idomain_def) 
 apply (cut_tac Ring, simp)
 apply (rule Idomain_axioms.intro,
        rule contrapos_pp, simp+, erule conjE)
 apply (simp add:Subring_tOp_ring_tOp)
 apply (frule_tac x = a in mem_subring_mem_ring[of S], assumption,
        frule_tac x = b in mem_subring_mem_ring[of S], assumption)
 apply (frule_tac a = a and b = b in Idomain.idom[of R], assumption+)
        apply (simp add:Subring_zero_ring_zero)
 apply (erule disjE, simp add:Subring_zero_ring_zero)
 apply (simp add:Subring_zero_ring_zero)
done

lemma (in PolynRg) deg_to_X_d:"Idomain S \<Longrightarrow>  deg_n R S X (X^\<^bsup>R d\<^esup>) = d"
apply (cut_tac subring, frule subring_Ring,
       cut_tac polyn_ring_S_nonzero,
       cut_tac X_mem_R,
       cut_tac polyn_ring_X_nonzero,
       cut_tac polyn_ring_integral)
apply (induct_tac d)
 apply (cut_tac ring_one,
        simp add:Subring_one_ring_one[THEN sym],
        simp add:Subring_zero_ring_zero)
 apply (subst pol_of_deg0[of "1\<^sub>r\<^bsub>S\<^esub>"], assumption+, simp add:Ring.ring_one[of S])
 apply simp
 apply (subst deg_mult_pols, assumption+,
        simp add:npClose, 
        rule Idomain.idom_potent_nonzero, assumption+)
 apply (simp add:deg_n_of_X)
done

subsection \<open>Degree with value in \<open>aug_minf\<close>\<close>

lemma (in PolynRg) nonzero_deg_pos:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>\<rbrakk> \<Longrightarrow> 
                                                 0 \<le> deg R S X p"
by (simp add:deg_def) 

lemma (in PolynRg) deg_minf_pol_0:"p \<in> carrier R \<Longrightarrow>
                    (deg R S X p = -\<infinity>) = (p = \<zero>)" 
apply (rule iffI)
 apply (rule contrapos_pp, simp+,
        frule nonzero_deg_pos[of p], assumption+,
        simp add:deg_def an_def) 
apply (simp add:deg_def)
done

lemma (in PolynRg) pol_nonzero:"p \<in> carrier R \<Longrightarrow>
             (0 \<le> deg R S X p) = (p \<noteq> \<zero>)" 
apply (rule iffI)
apply (rule contrapos_pp, simp+, simp add:deg_def,
       cut_tac minf_le_any[of "0"], frule ale_antisym[of "0" "-\<infinity>"], 
       assumption+,
       simp only:an_0[THEN sym], simp only:an_def, simp del:of_nat_0)
apply (simp add:deg_def) 
done

lemma (in PolynRg) minus_deg_in_aug_minf:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
                   - (deg R S X p) \<in> Z\<^sub>-\<^sub>\<infinity>"
apply (frule deg_in_aug_minf[of p],
      frule pol_nonzero[THEN sym, of p],
      simp add:aug_minf_def,
      rule contrapos_pp, simp+,
      cut_tac a_minus_minus[of "deg R S X p"], simp) 

apply (thin_tac "- deg R S X p = \<infinity>", frule sym, 
       thin_tac "- \<infinity> = deg R S X p",
       frule deg_minf_pol_0[of p], simp)
done

lemma (in PolynRg) deg_of_X:"deg R S X X = 1" (* the degree of the polyn. X *)
apply (cut_tac X_mem_R,
       cut_tac polyn_ring_X_nonzero,
       cut_tac subring)
apply (simp add:deg_def, simp only:an_1[THEN sym],
       rule nat_eq_an_eq, simp add:deg_n_of_X)
done

lemma (in PolynRg) pol_deg_0:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>\<rbrakk>
                   \<Longrightarrow>  (deg R S X p = 0) = (p \<in> carrier S)"
apply (simp add:deg_def, simp only:an_0[THEN sym],
       rule iffI,
       frule an_inj[of "deg_n R S X p" "0"], simp,
       simp add:pol_of_deg0,
       rule nat_eq_an_eq, simp add:pol_of_deg0[of p])
done

lemma (in PolynRg) deg_of_X2n:"Idomain S \<Longrightarrow> deg R S X (X^\<^bsup>R n\<^esup>) = an n"
apply (frule Idomain.idom_is_ring[of "S"])
apply (cut_tac subring,
       cut_tac X_mem_R,
       cut_tac polyn_ring_X_nonzero,
       cut_tac polyn_ring_integral, simp)
apply (induct_tac n)
apply simp
 apply (simp add:Subring_one_ring_one[THEN sym, of "S"])
 apply (subst pol_deg_0[of "1\<^sub>r\<^bsub>S\<^esub>"])
 apply (simp add:Subring_one_ring_one, simp add:ring_one)
 apply (simp add:Subring_one_ring_one[of S] polyn_ring_nonzero)
 apply (simp add:Ring.ring_one[of S])

apply (frule_tac n = n in npClose[of X])
apply (simp add:deg_def)
apply (simp add:Idomain.idom_potent_nonzero,
       frule_tac n = "Suc n" in Idomain.idom_potent_nonzero[of R X],
       assumption+, simp)
apply (rule nat_eq_an_eq) 
apply (frule_tac n = n in Idomain.idom_potent_nonzero[of R X], assumption+)
apply (frule_tac n = "deg_n R S X (X^\<^bsup>R n\<^esup>)" and m = n in an_inj,
       thin_tac "an (deg_n R S X (X^\<^bsup>R n\<^esup>)) = an n")
 apply (cut_tac deg_of_X)
 apply (simp add:deg_def, simp only:an_1[THEN sym])
apply (frule_tac n = "deg_n R S X X" and m = 1 in an_inj)
 apply (simp add:deg_mult_pols)
done

lemma (in PolynRg) add_pols_nonzero:"\<lbrakk>p \<in> carrier R; q \<in> carrier R; 
      (deg R S X p) \<noteq> (deg R S X q)\<rbrakk>  \<Longrightarrow>  p \<plusminus> q \<noteq> \<zero>"
apply (cut_tac ring_is_ag,
       cut_tac subring,
       frule subring_Ring)
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp add:deg_minf_pol_0[THEN sym],
       simp add:aGroup.ag_l_zero, rule contrapos_pp, simp+,
       case_tac "q = \<zero>\<^bsub>R\<^esub>", simp add:aGroup.ag_r_zero)
apply (simp add:deg_def, 
       simp only:aneq_natneq[of "deg_n R S X p" "deg_n R S X q"],
       cut_tac less_linear[of "deg_n R S X p" "deg_n R S X q"], simp,
       erule disjE,
       rule less_deg_add_nonzero[of p q],
         assumption+,
       frule less_deg_add_nonzero[of q p], assumption+,
       simp add:aGroup.ag_pOp_commute)
done

lemma (in PolynRg) deg_pols_add1:"\<lbrakk>p \<in> carrier R; q \<in> carrier R; 
                (deg R S X p) < (deg R S X q)\<rbrakk>  \<Longrightarrow>  
                              deg R S X (p \<plusminus> q) = deg R S X q"
apply (cut_tac ring_is_ag,
       case_tac "p = \<zero>\<^bsub>R\<^esub>", simp add:deg_def aGroup.ag_l_zero,
       case_tac "q = \<zero>\<^bsub>R\<^esub>", simp add:deg_def) 
       apply (rule impI) apply (simp add:an_def z_neq_minf)
 apply (fold an_def,
        frule aless_imp_le[of "an (deg_n R S X p)" " - \<infinity>"],
        cut_tac minf_le_any[of "an (deg_n R S X p)"],
        frule ale_antisym[of "an (deg_n R S X p)" "- \<infinity>"], assumption+,
        simp add:an_neq_minf)
apply (simp add:deg_def, simp add:aless_nat_less,
       frule less_deg_add_nonzero[of p q], assumption+,
       simp, frule polyn_deg_add1[of p q], assumption+, simp)
done

lemma (in PolynRg) deg_pols_add2:"\<lbrakk>p \<in> carrier R; q \<in> carrier R; 
       (deg R S X p) = (deg R S X q)\<rbrakk>  \<Longrightarrow> 
               deg R S X (p \<plusminus> q) \<le> (deg R S X q)"
apply (cut_tac ring_is_ag, 
       cut_tac subring, frule subring_Ring)
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp add:aGroup.ag_l_zero)
apply (case_tac "q = \<zero>\<^bsub>R\<^esub>", simp add:aGroup.ag_r_zero)
apply (simp add:deg_def,
       frule an_inj[of "deg_n R S X p" "deg_n R S X q"], simp,
       rule impI, subst ale_natle, simp add:polyn_deg_add2)
done

lemma (in PolynRg) deg_pols_add3:"\<lbrakk>p \<in> carrier R; q \<in> carrier R; 
       (deg R S X p) \<le> an n; (deg R S X q) \<le> an n\<rbrakk>  \<Longrightarrow> 
                  deg R S X (p \<plusminus> q) \<le> an n"
apply (case_tac "(deg R S X p) = (deg R S X q)",
       frule deg_pols_add2[of p q], assumption+,
       simp)
apply (cut_tac aless_linear[of "deg R S X p" "deg R S X q"],
       simp, thin_tac "deg R S X p \<noteq> deg R S X q",
       erule disjE, simp add:deg_pols_add1,
       cut_tac ring_is_ag, simp add:aGroup.ag_pOp_commute[of "R" "p" "q"],
       simp add:deg_pols_add1)
done

lemma (in PolynRg) const_times_polyn1:"\<lbrakk>Idomain S; p\<in> carrier R; c \<in> carrier S;
            c \<noteq> \<zero>\<^bsub>S\<^esub>\<rbrakk> \<Longrightarrow> deg R S X (c \<cdot>\<^sub>r p) = deg R S X p"
apply (frule Idomain.idom_is_ring,
       cut_tac subring,
       frule mem_subring_mem_ring[of S c], assumption,
       simp add:Subring_zero_ring_zero)
apply (subst deg_mult_pols1[of c p], assumption+,
       simp add: pol_deg_0[THEN sym, of "c"],
       simp add:aadd_0_l)
done
 
section "Homomorphism of polynomial rings"

definition
  cf_h :: " ('a \<Rightarrow> 'b) \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<times> (nat \<Rightarrow> 'b)" where
  "cf_h f = (\<lambda>c. (fst c, cmp f (snd c)))"

definition
  polyn_Hom :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a,
              ('b, 'n) Ring_scheme, ('b, 'n1) Ring_scheme, 'b] \<Rightarrow>
              ('a \<Rightarrow> 'b) set"
            ("(pHom _ _ _, _ _ _)" [67,67,67,67,67,68]67) where
  "pHom R S X, A B Y = {f. f \<in> rHom R A \<and> f`(carrier S) \<subseteq> carrier B \<and> 
                          f X = Y}"  (* Hom from a polynomial ring to
                                        a polynomial ring *)

definition
  erh :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a,
           ('b, 'n) Ring_scheme, ('b, 'n1) Ring_scheme, 'b, 'a \<Rightarrow> 'b, 
          nat, nat \<times> (nat \<Rightarrow> 'a)] \<Rightarrow> 'b" where
  "erh R S X A B Y f n c = polyn_expr A Y n (cf_h f c)"
 (* extension of a ring hom. *)

lemma (in PolynRg) cf_h_len:"\<lbrakk>PolynRg A B Y; f \<in> rHom S B; 
                   pol_coeff S c\<rbrakk> \<Longrightarrow> fst (cf_h f c) = fst c"
by (simp add:cf_h_def)

lemma (in PolynRg) cf_h_coeff:"\<lbrakk>PolynRg A B Y; f \<in> rHom S B; 
                   pol_coeff S c\<rbrakk> \<Longrightarrow>  pol_coeff B (cf_h f c)"
apply (subst pol_coeff_def)
 apply (rule allI, rule impI, simp add:cf_h_len cf_h_def)
 apply (frule_tac j = j in pol_coeff_mem[of c], assumption)
 apply (simp add:cmp_def rHom_mem)
done

lemma (in PolynRg) cf_h_cmp:"\<lbrakk>PolynRg A B Y; pol_coeff S (n, f); h \<in> rHom S B;
                    j \<le> n\<rbrakk> \<Longrightarrow>
                 (snd (cf_h h (n, f))) j = (cmp h f) j"
by (simp add:cf_h_def) 

lemma (in PolynRg) cf_h_special_cf:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B\<rbrakk> \<Longrightarrow>
       polyn_expr A Y (Suc 0) (cf_h h (ext_cf S (Suc 0) (C\<^sub>0 S))) =
         polyn_expr A Y (Suc 0) (ext_cf B (Suc 0) (C\<^sub>0 B))"
apply (cut_tac subring, frule subring_Ring,
       frule PolynRg.is_Ring[of A B Y],
       frule PolynRg.subring[of A B Y],
       frule Ring.subring_Ring[of A B], assumption)
apply (cut_tac special_cf_pol_coeff,
       frule ext_cf_pol_coeff[of "C\<^sub>0 S" "Suc 0"],
       frule cf_h_coeff[of A B Y h "ext_cf S (Suc 0) (C\<^sub>0 S)"], assumption+)
apply (frule PolynRg.special_cf_pol_coeff,
       frule PolynRg.ext_cf_pol_coeff[of A B Y "C\<^sub>0 B" "Suc 0"], assumption)
apply (frule PolynRg.pol_expr_unique2[of A B Y 
             "cf_h h (ext_cf S (Suc 0) (C\<^sub>0 S))" "ext_cf B (Suc 0) (C\<^sub>0 B)"],
       assumption+,
       simp add:cf_h_len PolynRg.ext_cf_len,
       simp add:ext_cf_len special_cf_len PolynRg.special_cf_len,
       simp add:cf_h_len PolynRg.ext_cf_len,
       simp add:ext_cf_len special_cf_len PolynRg.special_cf_len,
       thin_tac "(polyn_expr A Y (Suc 0) (cf_h h (ext_cf S (Suc 0) (C\<^sub>0 S))) =
                   polyn_expr A Y (Suc 0) (ext_cf B (Suc 0) (C\<^sub>0 B))) =
                (\<forall>j\<le>Suc 0.
                  snd (cf_h h (ext_cf S (Suc 0) (C\<^sub>0 S))) j =
                  snd (ext_cf B (Suc 0) (C\<^sub>0 B)) j)",
       thin_tac "pol_coeff S (C\<^sub>0 S)",
       thin_tac "pol_coeff S (ext_cf S (Suc 0) (C\<^sub>0 S))",
       thin_tac "pol_coeff B (cf_h h (ext_cf S (Suc 0) (C\<^sub>0 S)))")
apply (rule allI, rule impI)
 apply (case_tac "j = 0", simp add:cf_h_def cmp_def ext_cf_def sliden_def)
 apply (simp add:rHom_0_0)
 apply (simp)
 apply (frule_tac n = j in Suc_leI[of 0],
        frule_tac m = j and n = "Suc 0" in le_antisym, assumption+,
        thin_tac "j \<le> Suc 0", thin_tac "Suc 0 \<le> j",
        simp add:cf_h_def cmp_def ext_cf_def sliden_def special_cf_def,
        simp add:rHom_one)
done

lemma (in PolynRg) polyn_Hom_coeff_to_coeff:
     "\<lbrakk>PolynRg A B Y; f \<in> pHom R S X, A B Y; pol_coeff S c\<rbrakk>
        \<Longrightarrow>  pol_coeff B (cf_h f c)"
apply (subst pol_coeff_def)
 apply (rule allI, rule impI, simp add:cf_h_len cf_h_def)
 apply (frule_tac j = j in pol_coeff_mem[of c], assumption)
 apply (simp add:cmp_def polyn_Hom_def, (erule conjE)+)
 apply (simp add:image_def)
 apply (rule subsetD[of "{y. \<exists>x\<in>carrier S. y = f x}" "carrier B"], assumption,
        simp)
 apply blast
done (* old name is cmp_pol_coeff *)

lemma (in PolynRg) cf_h_len1:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B; 
        f \<in> pHom R S X, A B Y; \<forall>x\<in>carrier S. f x = h x; pol_coeff S c\<rbrakk> \<Longrightarrow> 
        fst (cf_h f c) = fst (cf_h h c)"
by (simp add:cf_h_def)

lemma (in PolynRg) cf_h_len2:"\<lbrakk>PolynRg A B Y; f \<in> pHom R S X, A B Y; 
          pol_coeff S c\<rbrakk> \<Longrightarrow> fst (cf_h f c) = fst c"
by (simp add:cf_h_def)

lemma (in PolynRg) cmp_pol_coeff:"\<lbrakk>f \<in> rHom S B; 
       pol_coeff S (n, c)\<rbrakk>  \<Longrightarrow> pol_coeff B (n,(cmp f c))"
apply (simp add:pol_coeff_def,
      rule allI, rule impI, simp add:cmp_def,
      frule_tac a = j in forall_spec, simp,
      thin_tac "\<forall>j\<le>n. c j \<in> carrier S")
apply (simp add:rHom_mem)
done 

lemma (in PolynRg) cmp_pol_coeff_e:"\<lbrakk>PolynRg A B Y; f \<in> pHom R S X, A B Y; 
         pol_coeff S (n, c)\<rbrakk> \<Longrightarrow> pol_coeff B (n, (cmp f c))"
apply (subst pol_coeff_def)
 apply (rule allI, rule impI, simp)
 apply (frule_tac j = j in pol_coeff_mem[of "(n, c)"], simp)
 apply (simp add:polyn_Hom_def cmp_def, (erule conjE)+)
 apply (simp add:image_def)
 apply (rule_tac c = "f (c j)" in subsetD[of "{y. \<exists>x\<in>carrier S. y = f x}"
                                  "carrier B"], assumption+)
 apply (simp, blast)
done

lemma (in PolynRg) cf_h_pol_coeff:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B;
      pol_coeff S (n, f)\<rbrakk> \<Longrightarrow> cf_h h (n, f) = (n, cmp h f)"
by (simp add:cf_h_def)

lemma (in PolynRg) cf_h_polyn:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B; 
      pol_coeff S (n, f)\<rbrakk> \<Longrightarrow>
      polyn_expr A Y n (cf_h h (n, f)) = polyn_expr A Y n (n, (cmp h f))"
apply (frule cf_h_coeff[of A B Y h "(n, f)"], assumption+,
       frule cmp_pol_coeff[of h B n f], assumption+)
apply (rule PolynRg.polyn_exprs_eq[of A B Y  "cf_h h (n, f)" "(n, cmp h f)" n],
       assumption+,
       simp add:cf_h_len,
       rule allI, rule impI,
       simp add:cf_h_def)
done

lemma (in PolynRg) pHom_rHom:"\<lbrakk>PolynRg A B Y; f \<in> pHom R S X, A B Y\<rbrakk> \<Longrightarrow>
                                 f \<in> rHom R A"
by (simp add:polyn_Hom_def)

lemma (in PolynRg) pHom_X_Y:"\<lbrakk>PolynRg A B Y; f \<in> pHom R S X, A B Y\<rbrakk> \<Longrightarrow>
                                 f X = Y"
by (simp add:polyn_Hom_def)

lemma (in PolynRg) pHom_memTr:"\<lbrakk>PolynRg A B Y; 
      f \<in> pHom R S X, A B Y\<rbrakk> \<Longrightarrow> 
      \<forall>c. pol_coeff S (n, c) \<longrightarrow> 
          f (polyn_expr R X n (n, c)) = polyn_expr A Y n (n, cmp f c)" 
apply (cut_tac subring, frule subring_Ring,
       frule PolynRg.is_Ring[of A B Y],
       frule PolynRg.subring[of A B Y],
       frule Ring.subring_Ring[of A B], assumption)
apply (induct_tac n)
 apply (rule allI, rule impI)
 apply (simp add:polyn_expr_def cmp_def)
 apply (frule_tac c = "(0, c)" and j = 0 in pol_coeff_mem,
           simp, simp,
       frule_tac x = "c 0" in mem_subring_mem_ring, assumption+,
       simp add:polyn_Hom_def, (erule conjE)+,
       frule rHom_func[of f R A],
       frule_tac x = "c 0" in funcset_mem[of f "carrier R" "carrier A"],
              assumption+,
       simp add:ring_r_one, simp add:Ring.ring_r_one)

apply (rule allI, rule impI)
apply (cut_tac n = n and f = c in pol_coeff_pre, assumption) 
       apply (
       drule_tac a = c in forall_spec, assumption)
apply (cut_tac n = n and c = "(Suc n, c)" in polyn_Suc, simp,
        simp del:npow_suc,
        thin_tac "polyn_expr R X (Suc n) (Suc n, c) =
           polyn_expr R X n (Suc n, c) \<plusminus> c (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup>")
apply (frule_tac c = "(Suc n, c)" and k = n in polyn_expr_short, simp)
       apply (simp del:npow_suc,
       thin_tac "polyn_expr R X n (Suc n, c) = polyn_expr R X n (n, c)")
apply (frule_tac c = "(Suc n, c)" in polyn_Hom_coeff_to_coeff[of A B Y f],
       assumption+, simp del:npow_suc add:cf_h_def)
apply (frule_tac c = "(Suc n, cmp f c)" and n = n in 
                  PolynRg.polyn_Suc[of A B Y], simp, simp del:npow_suc,
       thin_tac "polyn_expr A Y (Suc n) (Suc n, cmp f c) =
        polyn_expr A Y n (Suc n, cmp f c) \<plusminus>\<^bsub>A\<^esub>  cmp f c (Suc n) \<cdot>\<^sub>r\<^bsub>A\<^esub> Y^\<^bsup>A (Suc n)\<^esup>")
apply (frule_tac k = n and c = "(n, c)" in polyn_mem, simp) 
apply (frule_tac c = "(Suc n, c)" in monomial_mem,
       drule_tac a = "Suc n" in forall_spec, simp, simp del:npow_suc) 

apply (frule pHom_rHom[of A B Y f], assumption+,
                                       simp del:npow_suc add:rHom_add) 
apply (frule_tac c = "(Suc n, c)" and j = "Suc n" in pol_coeff_mem_R, simp,
         simp del:npow_suc)
apply (cut_tac X_mem_R,
       frule_tac n = "Suc n" in npClose[of X],
       cut_tac Ring,
       subst rHom_tOp[of R A _ _ f], assumption+) 
 apply (frule_tac c = "(Suc n, cmp f c)" and k = n in 
        PolynRg.polyn_expr_short[of A B Y], assumption+, simp,
        simp del:npow_suc)
 apply (cut_tac c = "(Suc n, cmp f c)" and n = n in 
        PolynRg.pol_coeff_le[of A B Y], assumption+, simp,
        simp del:npow_suc add:PolynRg.pol_coeff_le[of A B Y])
apply (subst rHom_npow[of R A X f], assumption+,
       simp del:npow_suc add:pHom_X_Y cmp_def)
done

lemma (in PolynRg) pHom_mem:"\<lbrakk>PolynRg A B Y; 
      f \<in> pHom R S X, A B Y; pol_coeff S (n, c)\<rbrakk> \<Longrightarrow> 
      f (polyn_expr R X n (n, c)) = polyn_expr A Y n (n, cmp f c)"
apply (simp add:pHom_memTr)
done

lemma (in PolynRg) pHom_memc:"\<lbrakk>PolynRg A B Y; f \<in> pHom R S X, A B Y; 
      pol_coeff S c\<rbrakk> \<Longrightarrow> 
      f (polyn_expr R X (fst c) c) = polyn_expr A Y (fst c) (cf_h f c)"
by (cases c) (simp add: cf_h_def pHom_mem)

lemma (in PolynRg) pHom_mem1:"\<lbrakk>PolynRg A B Y; f \<in> pHom R S X, A B Y; 
       p \<in> carrier R\<rbrakk> \<Longrightarrow>  f p \<in> carrier A"
apply (simp add:polyn_Hom_def, (erule conjE)+)
apply (simp add:rHom_mem)
done

lemma (in PolynRg) pHom_pol_mem:"\<lbrakk>PolynRg A B Y; f \<in> pHom R S X, A B Y; 
      p \<in> carrier R; p \<noteq> \<zero>\<rbrakk>  \<Longrightarrow> 
      f p = polyn_expr A Y (deg_n R S X p) (cf_h f (s_cf R S X p))"
apply (frule s_cf_expr[of p], assumption, (erule conjE)+)
apply (subst s_cf_deg[of p], assumption+)
apply (subst pHom_memc[THEN sym, of A B Y f], assumption+)
apply (drule sym, simp)
done

lemma (in PolynRg) erh_rHom_coeff:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B;
       pol_coeff S c\<rbrakk>  \<Longrightarrow>  erh R S X A B Y h 0 c = (cmp h (snd c)) 0"
apply (cut_tac subring,
       frule subring_Ring,
       frule PolynRg.is_Ring[of A B Y],
       frule PolynRg.subring[of A B Y],
       frule Ring.subring_Ring[of A B], assumption) 
apply (simp add:erh_def polyn_expr_def cf_h_def)
 apply (frule pol_coeff_mem [of c 0], simp)
 apply (simp add:cmp_def, frule rHom_mem[of h S B "snd c 0"], assumption)
 apply (frule Ring.mem_subring_mem_ring[of A B "h (snd c 0)"], assumption+,
        simp add:Ring.ring_r_one)
done

lemma (in PolynRg) erh_polyn_exprs:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B;
       pol_coeff S c; pol_coeff S d; 
       polyn_expr R X (fst c) c = polyn_expr R X (fst d) d\<rbrakk>  \<Longrightarrow>  
       erh R S X A B Y h (fst c) c  = erh R S X A B Y h (fst d) d"
apply (cut_tac subring,
       frule subring_Ring,
       frule PolynRg.is_Ring[of A B Y],
       frule PolynRg.subring[of A B Y],
       frule Ring.subring_Ring[of A B], assumption+)
apply (simp add:erh_def)
apply (cut_tac less_linear[of "fst c" "fst d"])
apply (erule disjE,
       frule pol_expr_unique3[of c d], assumption+, simp,
       thin_tac "polyn_expr R X (fst c) c = polyn_expr R X (fst d) d",
       frule cf_h_coeff[of A B Y h c], assumption+,
       frule cf_h_coeff[of A B Y h d], assumption+) 
apply (frule PolynRg.pol_expr_unique3[of A B Y "cf_h h c" "cf_h h d"],
        assumption+, simp add:cf_h_len, simp add:cf_h_len,
       thin_tac "(polyn_expr A Y (fst c) (cf_h h c) =
       polyn_expr A Y (fst d) (cf_h h d)) =
       ((\<forall>j\<le>fst c. snd (cf_h h c) j = snd (cf_h h d) j) \<and>
       (\<forall>j\<in>nset (Suc (fst c)) (fst d). snd (cf_h h d) j = \<zero>\<^bsub>B\<^esub>))",
       simp add:cf_h_def cmp_def, simp add:rHom_0_0)

apply (erule disjE,
       frule pol_expr_unique2[of c d], assumption+, simp,
       thin_tac "polyn_expr R X (fst d) c = polyn_expr R X (fst d) d",
       frule cf_h_coeff[of A B Y h c], assumption+,
       frule cf_h_coeff[of A B Y h d], assumption+) 
apply (frule PolynRg.pol_expr_unique2[of A B Y "cf_h h c" "cf_h h d"],
        assumption+, simp add:cf_h_len, simp add:cf_h_len,
       thin_tac "(polyn_expr A Y (fst d) (cf_h h c) =
        polyn_expr A Y (fst d) (cf_h h d)) =
       (\<forall>j\<le>fst d. snd (cf_h h c) j = snd (cf_h h d) j)",
        simp add:cf_h_def cmp_def)

apply (drule sym, rule sym,
       frule pol_expr_unique3[of d c], assumption+, simp,
       thin_tac "polyn_expr R X (fst d) d = polyn_expr R X (fst c) c",
       frule cf_h_coeff[of A B Y h c], assumption+,
       frule cf_h_coeff[of A B Y h d], assumption+) 
apply (frule PolynRg.pol_expr_unique3[of A B Y "cf_h h d" "cf_h h c"],
        assumption+, simp add:cf_h_len, simp add:cf_h_len,
       thin_tac "(polyn_expr A Y (fst d) (cf_h h d) =
       polyn_expr A Y (fst c) (cf_h h c)) =
       ((\<forall>j\<le>fst d. snd (cf_h h d) j = snd (cf_h h c) j) \<and>
       (\<forall>j\<in>nset (Suc (fst d)) (fst c). snd (cf_h h c) j = \<zero>\<^bsub>B\<^esub>))",
       simp add:cf_h_def cmp_def, simp add:rHom_0_0)
done

definition
  erH :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a,
         ('b, 'n) Ring_scheme, ('b, 'n1) Ring_scheme, 'b, 'a \<Rightarrow> 'b] \<Rightarrow> 
                  'a \<Rightarrow> 'b" where
  "erH R S X A B Y h = (\<lambda>x\<in>carrier R. erh R S X A B Y h 
                              (fst (s_cf R S X x)) (s_cf R S X x))" 
(*
lemma (in PolynRg) erH_phom:"\<lbrakk>PolynRg A B y; h \<in> rHom S B\<rbrakk> \<Longrightarrow>
              erH R S X A B Y h \<in> pHom R S X, A B Y" *)

lemma (in PolynRg) erH_rHom_0:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B\<rbrakk>  \<Longrightarrow> 
                   (erH R S X A B Y h) \<zero> = \<zero>\<^bsub>A\<^esub>"
apply (cut_tac subring, frule subring_Ring,
       cut_tac PolynRg.is_Ring[of A B Y],
       cut_tac PolynRg.subring[of A B Y],
       cut_tac Ring.subring_Ring[of A B])
apply (simp add:erH_def erh_def s_cf_def polyn_expr_def)
 apply (cut_tac ring_zero,
        simp add:cf_h_def cmp_def rHom_0_0,
        simp add:Ring.Subring_zero_ring_zero, 
        frule Ring.ring_zero[of A], simp add:Ring.ring_r_one, assumption+)
done


lemma (in PolynRg) erH_mem:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B; p \<in> carrier R\<rbrakk> \<Longrightarrow>
               erH R S X A B Y h p \<in> carrier A"
apply (cut_tac subring, frule subring_Ring,
       cut_tac PolynRg.is_Ring[of A B Y],
       cut_tac PolynRg.subring[of A B Y],
       cut_tac Ring.subring_Ring[of A B])
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>")
  apply (simp add:erH_rHom_0, simp add:Ring.ring_zero)

apply (simp add:erH_def erh_def)
 apply (frule s_cf_expr[of p], assumption, (erule conjE)+)
 apply (rule PolynRg.polyn_mem[of A B Y "cf_h h (s_cf R S X p)"], assumption+)
 apply (simp add:cf_h_coeff)
 apply (simp add:cf_h_len, assumption+) 
done

lemma (in PolynRg) erH_rHom_nonzero:"\<lbrakk>PolynRg A B Y; f \<in> rHom S B; 
      p \<in> carrier R; (erH R S X A B Y f) p \<noteq> \<zero>\<^bsub>A\<^esub>\<rbrakk> \<Longrightarrow> p \<noteq> \<zero>"
apply (rule contrapos_pp, simp+)
apply (simp add:erH_rHom_0)
done

lemma (in PolynRg) erH_rHomTr2:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B\<rbrakk>  \<Longrightarrow> 
        (erH R S X A B Y h) (1\<^sub>r) = (1\<^sub>r\<^bsub>A\<^esub>)"
apply (cut_tac subring, frule subring_Ring,
       frule PolynRg.is_Ring[of A B Y],
       frule PolynRg.subring[of A B Y],
       frule Ring.subring_Ring[of A B], assumption,
       cut_tac polyn_ring_nonzero)
apply (cut_tac Subring_one_ring_one[THEN sym, of S],
       frule Ring.ring_one[of S],
       cut_tac ring_one)
apply (frule s_cf_expr[of "1\<^sub>r"], assumption+, (erule conjE)+)
 apply (frule s_cf_deg[THEN sym, of "1\<^sub>r"], assumption, simp)
 apply (cut_tac pol_of_deg0[THEN sym, of "1\<^sub>r"], simp,
        simp add:erH_def erh_def cf_h_def polyn_expr_def,
        frule pol_coeff_mem[of "s_cf R S X 1\<^sub>r\<^bsub>S\<^esub>" 0], simp)
 apply (simp add:Subring_tOp_ring_tOp[THEN sym],
        simp add:Ring.ring_r_one cmp_def) 
 apply (simp add:rHom_one,
        simp add:Ring.Subring_one_ring_one[of A B],
               frule Ring.ring_one[of A], simp add:Ring.ring_r_one)
 apply (simp add:ring_one)
 apply simp apply assumption
done

declare max.absorb1 [simp] max.absorb2 [simp]

lemma (in PolynRg) erH_multTr:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B; 
      pol_coeff S c\<rbrakk> \<Longrightarrow> 
 \<forall>f g. pol_coeff S (m, f) \<and> pol_coeff S (((fst c) + m), g) \<and> 
       (polyn_expr R X (fst c) c) \<cdot>\<^sub>r (polyn_expr R X m (m, f)) = 
             (polyn_expr R X ((fst c) + m) ((fst c) + m, g))  \<longrightarrow> 
 (polyn_expr A Y (fst c) (cf_h h c)) \<cdot>\<^sub>r\<^bsub>A\<^esub> (polyn_expr A Y m (cf_h h (m, f))) = 
                 (polyn_expr A Y ((fst c) + m) (cf_h h ((fst c)+m, g)))"
apply (cut_tac subring, frule subring_Ring,
       frule PolynRg.is_Ring[of A B Y],
       frule PolynRg.subring[of A B Y],
       frule Ring.subring_Ring[of A B], assumption)
apply (cases c)
apply (simp only:)
apply (rename_tac l u)
apply (thin_tac "c = (l, u)")
apply (induct_tac m) 
 apply ((rule allI)+, rule impI, (erule conjE)+, simp)
 apply (simp add:cf_h_polyn[of A B Y h])
 apply (simp add:polyn_expr_def[of _ _ 0])
 apply (frule_tac c = "(0, f)" and j = 0 in pol_coeff_mem, simp, simp,
        frule_tac c = "(0, f)" and j = 0 in pol_coeff_mem_R, simp, simp,
        frule_tac c = "(l, u)" and k = l in polyn_mem, simp,
        simp add:ring_r_one,
        simp add:ring_tOp_commute,
        simp add:scalar_times_pol_expr) 
 apply (frule_tac c = "(0, f)" in cf_h_coeff[of A B Y h], assumption+,
        frule_tac c = "(l, u)" in cf_h_coeff[of A B Y h], assumption+)
 apply (frule_tac c = "cf_h h (0, f)" in PolynRg.pol_coeff_mem[of A B Y _ 0],
        assumption+, simp, simp add:cf_h_cmp,
        frule_tac c = "cf_h h (0, f)" in PolynRg.pol_coeff_mem_R[of A B Y _ 0],
        assumption+, simp, simp add:cf_h_cmp,
        frule_tac c = "cf_h h (l, u)" and k = l in PolynRg.polyn_mem, simp,
        simp add:cf_h_len, simp add:cf_h_polyn,
        simp add:Ring.ring_r_one, simp add:Ring.ring_tOp_commute[of A],
        frule_tac n = l and f = u in cf_h_pol_coeff[of A B Y h],
              assumption+, simp)
  apply (simp add:PolynRg.scalar_times_pol_expr,
         frule_tac c = "(l, u)" and a = "f 0" in sp_cf_pol_coeff, assumption+,
         frule_tac c = "(l, cmp h u)" and a = "(cmp h f) 0" in 
           PolynRg.sp_cf_pol_coeff, assumption+,
         frule_tac c = "(l, g)" in cf_h_coeff[of A B Y h], assumption+,
         simp add:cf_h_pol_coeff) 
  apply (rule_tac c = "sp_cf B (cmp h f 0) (l, cmp h u)" and 
         d = "(l, cmp h g)" and k = l in PolynRg.polyn_exprs_eq[of A B Y],
         assumption+, simp add:sp_cf_len, 
         simp add:PolynRg.sp_cf_len)
  apply (rule allI, rule impI)
  apply (frule_tac c = "sp_cf S (f 0) (l, u)" and d = "(l, g)" in 
         pol_expr_unique2, assumption+,
         simp add:sp_cf_len, simp add:sp_cf_len)
  apply (drule_tac a = j in forall_spec, simp)
  apply (simp add:sp_cf_def)
  apply (rotate_tac -1, drule sym, simp add:cmp_def,
        thin_tac "pol_coeff B (l, \<lambda>x. h (g x))",
        thin_tac "pol_coeff B (l, \<lambda>j. h (f 0) \<cdot>\<^sub>r\<^bsub>B\<^esub> h (u j))",
        thin_tac "pol_coeff S (l, \<lambda>j. f 0 \<cdot>\<^sub>r\<^bsub>S\<^esub> u j)",
        thin_tac "polyn_expr A Y l (l, \<lambda>x. h (u x)) \<in> carrier A",
        thin_tac "pol_coeff B (l, \<lambda>x. h (u x))",
        thin_tac "polyn_expr R X l (l, \<lambda>j. f 0 \<cdot>\<^sub>r\<^bsub>S\<^esub> u j) =
                                          polyn_expr R X l (l, g)")
  apply (frule_tac c = "(l, u)" and j = j in pol_coeff_mem, simp, simp)
  apply (simp add:rHom_tOp)

apply ((rule allI)+, (rule impI), (erule conjE)+)
 apply (simp add:cf_h_polyn,
        frule_tac n = n and f = f in pol_coeff_pre, 
        frule_tac n = "l + n" and f = g in pol_coeff_pre,
        frule_tac n = l and f = u and m = n and g = f in polyn_expr_tOp, 
        assumption+, erule exE, (erule conjE)+,
        rotate_tac -1, drule sym)

 apply (drule_tac x = f in spec,
        drule_tac x = e in spec, simp,
        frule_tac n = n and f = f in polyn_Suc_split,
        simp del:npow_suc,
        thin_tac "polyn_expr R X (Suc n) (Suc n, f) =
        polyn_expr R X n (n, f) \<plusminus> f (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup>")
 (* got polyn_expr A Y l (l, cmp h u) \<cdot>\<^sub>r\<^bsub>A\<^esub> polyn_expr A Y n (n, cmp h f) =
        polyn_expr A Y (l + n) (l + n, cmp h e) *)

 apply (frule_tac c = "(Suc n, f)" in cf_h_coeff[of A B Y h], assumption+,
        simp del:npow_suc add:cf_h_pol_coeff)
 apply (frule_tac n = n and f = "cmp h f" in PolynRg.polyn_Suc_split[of A B Y],
        simp add:cf_h_pol_coeff, simp del:npow_suc,
        thin_tac "polyn_expr A Y (Suc n) (Suc n, cmp h f) =
        polyn_expr A Y n (n, cmp h f) \<plusminus>\<^bsub>A\<^esub> cmp h f (Suc n) \<cdot>\<^sub>r\<^bsub>A\<^esub> Y^\<^bsup>A (Suc n)\<^esup>")
   
apply (frule_tac c = "(l, u)" and k = l in polyn_mem, simp,
       frule_tac n = n and f = f in pol_coeff_pre,
       frule_tac c = "(n, f)" and k = n in polyn_mem, simp,
       frule_tac c = "(Suc n, f)" and j = "Suc n" in pol_coeff_mem_R, simp,
       cut_tac X_mem_R, simp del:npow_suc,
       cut_tac n = "Suc n" in npClose[of X], assumption,
       frule_tac x = "f (Suc n)" and y = " X^\<^bsup>R (Suc n)\<^esup>" in ring_tOp_closed,
         assumption+,
       simp del:npow_suc add:ring_distrib1) 
apply (frule_tac c = "(l, u)" in cf_h_coeff[of A B Y h], assumption+,
       frule_tac c = "(Suc n, f)" in cf_h_coeff[of A B Y h], assumption+,
       frule_tac n = n and f = f in pol_coeff_pre,
       frule_tac c = "(n, f)" in cf_h_coeff[of A B Y h], assumption+,
       simp del:npow_suc add:cf_h_pol_coeff)
apply (frule_tac c = "(l, cmp h u)" and k = l in PolynRg.polyn_mem, simp, simp,      frule_tac c = "(n, cmp h f)" and k = n in PolynRg.polyn_mem, simp, simp) 


apply (frule_tac c = "(Suc n, f)" and j = "Suc n" in pol_coeff_mem_R, simp,
       cut_tac X_mem_R, simp del:npow_suc,
       cut_tac n = "Suc n" in npClose[of X], assumption,
       frule_tac x = "f (Suc n)" and y = " X^\<^bsup>R (Suc n)\<^esup>" in ring_tOp_closed,
         assumption+,
       simp del:npow_suc add:ring_distrib1)

apply (frule_tac c = "(Suc n, cmp h f)" and j = "Suc n" in 
       PolynRg.pol_coeff_mem_R[of A B Y], simp del:npow_suc, 
       simp del:npow_suc,
       frule_tac PolynRg.X_mem_R[of A B Y], simp del:npow_suc,
       frule_tac n = "Suc n" in Ring.npClose[of A Y], assumption,
       frule_tac x = "cmp h f (Suc n)" and y = " Y^\<^bsup>A (Suc n)\<^esup>" in 
       Ring.ring_tOp_closed[of A], assumption+,
       simp del:npow_suc add:Ring.ring_distrib1) 

apply (frule_tac x1 = "polyn_expr R X l (l, u)" and y1 = "f (Suc n)" and 
       z1 = " X^\<^bsup>R (Suc n)\<^esup>" in ring_tOp_assoc[THEN sym], assumption+, 
       simp del:npow_suc,
       thin_tac "polyn_expr R X l (l, u) \<cdot>\<^sub>r polyn_expr R X n (n, f) =
        polyn_expr R X (l + n) (l + n, e)",
       thin_tac "polyn_expr R X l (l, u) \<cdot>\<^sub>r (f (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup>) =
        polyn_expr R X l (l, u) \<cdot>\<^sub>r f (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup>",
       simp only:ring_tOp_commute,
       frule_tac c = "(Suc n, f)" and j = "Suc n" in pol_coeff_mem, simp,
       simp del:npow_suc,
       simp del:npow_suc add:scalar_times_pol_expr)
 
  apply (frule_tac c = "(l, u)" and a = "f (Suc n)" in sp_cf_pol_coeff,
                assumption+,
         frule_tac c = "sp_cf S (f (Suc n)) (l, u)" and k = l in polyn_mem,
         simp add:sp_cf_len, simp only:ring_tOp_commute,
         frule_tac c1 = "sp_cf S (f (Suc n)) (l, u)" and j1 = "Suc n" in 
         low_deg_terms_zero1[THEN sym],
         simp only:sp_cf_len, simp del: npow_suc)
   apply (frule_tac c = "sp_cf S (f (Suc n)) (l, u)" and n = "Suc n" in 
          ext_cf_pol_coeff,
          frule_tac c = "(l + n, e)" and d = "ext_cf S (Suc n) (sp_cf S (
           f (Suc n)) (l, u))" in polyn_add1, assumption+,
          simp del:npow_suc add:ext_cf_len sp_cf_len,
          cut_tac a = l and b = n in add.commute,
          simp del:npow_suc,
         thin_tac "polyn_expr R X (n + l) (n + l, e) \<plusminus>
         polyn_expr R X (Suc (n + l))
         (ext_cf S (Suc n) (sp_cf S (f (Suc n)) (l, u))) =
         polyn_expr R X (Suc (n + l))
         (add_cf S (n + l, e)
           (ext_cf S (Suc n) (sp_cf S (f (Suc n)) (l, u))))",
         thin_tac "polyn_expr R X l (l, u) \<in> carrier R",
         thin_tac "polyn_expr R X n (n, f) \<in> carrier R",
         thin_tac "f (Suc n) \<in> carrier R",
         thin_tac "X \<in> carrier R",
         thin_tac "X^\<^bsup>R (Suc n)\<^esup> \<in> carrier R",
         thin_tac "f (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup> \<in> carrier R",
         thin_tac "polyn_expr R X l (sp_cf S (f (Suc n)) (l, u)) \<in> carrier R",
         thin_tac "X^\<^bsup>R (Suc n)\<^esup> \<cdot>\<^sub>r polyn_expr R X l (sp_cf S (f (Suc n)) (l, u)) =
        polyn_expr R X (Suc (n + l))
         (ext_cf S (Suc n) (sp_cf S (f (Suc n)) (l, u)))")
  (* got polyn_expr R X (Suc (n + l)) (Suc (n + l), g) =
        polyn_expr R X (Suc (n + l))
         (add_cf S (n + l, e)
           (ext_cf S (Suc n) (sp_cf S (f (Suc n)) (l, u)))) *)

   apply (subst Ring.ring_tOp_assoc[THEN sym], assumption+,
          subst Ring.ring_tOp_commute, assumption+)
    apply (frule_tac c = "(Suc n, f)" in cf_h_coeff[of A B Y h],
          assumption+,
          simp only:cf_h_pol_coeff)
   apply (frule_tac c = "(Suc n, cmp h f)" and j = "Suc n" in 
         PolynRg.pol_coeff_mem[of A B Y], assumption+, simp, 
         simp del:npow_suc) 
   apply (subst PolynRg.scalar_times_pol_expr[of A B Y], assumption+,
          simp)
   apply (frule_tac a = "cmp h f (Suc n)" and c = "(l, cmp h u)" in 
          PolynRg.sp_cf_pol_coeff[of A B Y], assumption+)
   apply (frule_tac c = "sp_cf B (cmp h f (Suc n)) (l, cmp h u)" and k = l 
          in PolynRg.polyn_mem[of A B Y], assumption, simp)
          apply (simp add:PolynRg.sp_cf_len)
   apply (subst Ring.ring_tOp_commute[of A], assumption+)
  apply (frule_tac c1 = "sp_cf B (cmp h f (Suc n)) (l, cmp h u)" and 
         j1 = "Suc n" in PolynRg.low_deg_terms_zero1[of A B Y, THEN sym],
         assumption+)
   apply (simp del:npow_suc add:sp_cf_len PolynRg.sp_cf_len,
          thin_tac "Y^\<^bsup>A (Suc n)\<^esup> \<cdot>\<^sub>r\<^bsub>A\<^esub>
          polyn_expr A Y l (sp_cf B (cmp h f (Suc n)) (l, cmp h u)) =
          polyn_expr A Y (Suc (l + n))
          (ext_cf B (Suc n) (sp_cf B (cmp h f (Suc n)) (l, cmp h u)))",
          thin_tac "polyn_expr A Y l (sp_cf B (cmp h f (Suc n)) (l, cmp h u))
          \<in> carrier A")
   apply (frule_tac c = "sp_cf B (cmp h f (Suc n)) (l, cmp h u)" and 
          n = "Suc n" in PolynRg.ext_cf_pol_coeff[of A B Y], assumption+)
   apply (frule_tac c = "(l + n, cmp h e)" and 
          d = "ext_cf B (Suc n) (sp_cf B (cmp h f (Suc n)) (l, cmp h u))" in
          PolynRg.polyn_add1[of A B Y])    
   apply (frule_tac c = "(n + l, e)" in cf_h_coeff[of A B Y h], assumption+)
  apply (simp add:cf_h_pol_coeff[of A B Y h] add.commute, assumption)
  apply (simp add:PolynRg.ext_cf_len PolynRg.sp_cf_len)
  apply (cut_tac a = n and b = l in add.commute, simp)
  (** Now we got 
      polyn_expr A Y (max (l + n) (Suc (l + n)))
           (add_cf B (l + n, cmp h e)
             (ext_cf B (Suc n) (sp_cf B (cmp h f (Suc n)) (l, cmp h u)))) =
          polyn_expr A Y (Suc (l + n)) (Suc (l + n), cmp h g) *)

  apply (frule_tac c = "(l + n, e)" and 
         d = "ext_cf S (Suc n) (sp_cf S (f (Suc n)) (l, u))" in 
         add_cf_pol_coeff, assumption+)
  apply (frule_tac c = "(l + n, cmp h e)" and
         d = "ext_cf B (Suc n) (sp_cf B (cmp h f (Suc n)) (l, cmp h u))" in
         PolynRg.add_cf_pol_coeff[of A B Y]) 
  apply (frule_tac c = "(l + n, e)" in cf_h_coeff[of A B Y h], assumption+)
       apply (simp add:cf_h_pol_coeff) apply simp
   apply (thin_tac "polyn_expr A Y l (l, cmp h u) \<cdot>\<^sub>r\<^bsub>A\<^esub> polyn_expr A Y n 
         (n, cmp h f) = polyn_expr A Y (l + n) (l + n, cmp h e)",
        thin_tac "polyn_expr A Y l (l, cmp h u) \<in> carrier A",
        thin_tac "polyn_expr A Y n (n, cmp h f) \<in> carrier A",
        thin_tac "Y \<in> carrier A",
        thin_tac "Y^\<^bsup>A n\<^esup> \<cdot>\<^sub>r\<^bsub>A\<^esub> Y \<in> carrier A",
        thin_tac "cmp h f (Suc n) \<cdot>\<^sub>r\<^bsub>A\<^esub> (Y^\<^bsup>A n\<^esup> \<cdot>\<^sub>r\<^bsub>A\<^esub> Y) \<in> carrier A",
        thin_tac "polyn_expr A Y (l + n) (l + n, cmp h e) \<plusminus>\<^bsub>A\<^esub>
        polyn_expr A Y (Suc (l + n))
         (ext_cf B (Suc n) (sp_cf B (cmp h f (Suc n)) (l, cmp h u))) =
        polyn_expr A Y (Suc (l + n))
         (add_cf B (l + n, cmp h e)
           (ext_cf B (Suc n) (sp_cf B (cmp h f (Suc n)) (l, cmp h u))))")
  apply (frule_tac c = "(Suc (l + n), g)" in cf_h_coeff[of A B Y h], 
          assumption+)
  apply (simp add:cf_h_pol_coeff)
  apply (frule_tac c = "(Suc (l + n), g)" and d = "add_cf S (l + n, e)
         (ext_cf S (Suc n) (sp_cf S (f (Suc n)) (l, u)))" in pol_expr_unique2)
     apply assumption apply (simp add:add_cf_len) 
     apply (simp add:ext_cf_len sp_cf_len)
      apply (simp add:add_cf_len ext_cf_len sp_cf_len)
      apply (cut_tac a = n and b = l in add.commute, simp,
     thin_tac "pol_coeff B
         (add_cf B (l + n, cmp h e)
           (ext_cf B (Suc n) (sp_cf B (cmp h f (Suc n)) (l, cmp h u))))",
     thin_tac "pol_coeff B (Suc (l + n), cmp h g)",
     thin_tac "pol_coeff S
         (add_cf S (l + n, e)
           (ext_cf S (Suc n) (sp_cf S (f (Suc n)) (l, u))))",
     thin_tac "pol_coeff B
         (ext_cf B (Suc n) (sp_cf B (cmp h f (Suc n)) (l, cmp h u)))",
     thin_tac "pol_coeff B (sp_cf B (cmp h f (Suc n)) (l, cmp h u))",
     thin_tac "polyn_expr R X (Suc (l + n)) (Suc (l + n), g) =
        polyn_expr R X (Suc (l + n))
         (add_cf S (l + n, e)
           (ext_cf S (Suc n) (sp_cf S (f (Suc n)) (l, u))))")
    apply (rule sym)
    apply (frule_tac c = "(Suc (l + n), g)" in cf_h_coeff[of A B Y h],
             assumption+,
           frule_tac c = "(l + n, e)" in cf_h_coeff[of A B Y h],
             assumption+) 
    apply (frule_tac c = "(l, cmp h u)" and a = "cmp h f (Suc n)" in 
           PolynRg.sp_cf_pol_coeff[of A B Y], assumption+)
    apply (cut_tac c = "(l + n, cmp h e)" and 
           d = "ext_cf B (Suc n) (sp_cf B (cmp h f (Suc n)) (l, cmp h u))" in
           PolynRg.add_cf_pol_coeff, assumption+)
    apply (simp add:cf_h_pol_coeff) 
    apply (rule PolynRg.ext_cf_pol_coeff, assumption+)
    apply (frule_tac c = "(Suc (l + n), cmp h g)" and 
           d = "add_cf B (l + n, cmp h e)
             (ext_cf B (Suc n) (sp_cf B (cmp h f (Suc n)) (l, cmp h u)))" in 
           PolynRg.pol_expr_unique2[of A B Y])
    apply (simp add:cf_h_pol_coeff) apply assumption
    apply (simp add:add_cf_len)
    apply (frule_tac n = "l + n" and f = e in  cf_h_pol_coeff[of A B Y h],
            assumption+) 
    apply (frule_tac c = "sp_cf B (cmp h f (Suc n)) (l, cmp h u)" and 
           n = "Suc n" in 
           PolynRg.ext_cf_pol_coeff[of A B Y], assumption+)
    apply (simp add:PolynRg.add_cf_len)
           apply (simp add:PolynRg.ext_cf_len)
           apply (simp add:PolynRg.sp_cf_len)
    apply (simp add:PolynRg.add_cf_len)
    apply (frule_tac c = "sp_cf B (cmp h f (Suc n)) (l, cmp h u)" and 
           n = "Suc n" in PolynRg.ext_cf_pol_coeff[of A B Y],
            assumption+)
    apply (frule_tac c = "(l + n, cmp h e)" and
           d = "ext_cf B (Suc n)
                   (sp_cf B (cmp h f (Suc n)) (l, cmp h u))" in 
           PolynRg.add_cf_pol_coeff[of A B Y])
    apply (simp add:cf_h_pol_coeff, assumption)
  apply (simp add:cf_h_pol_coeff)  
    apply (simp add:PolynRg.add_cf_len) 
    apply (simp add:PolynRg.ext_cf_len)
    apply (simp add:PolynRg.sp_cf_len)
    apply (cut_tac a = n and b = l in add.commute, simp)
  (* we got 
     \<forall>j\<le>Suc (l + n).
             cmp h g j =
             snd (add_cf B (l + n, cmp h e)
                   (ext_cf B (Suc n)
                     (sp_cf B (cmp h f (Suc n)) (l, cmp h u)))) j *)

    apply (thin_tac "(polyn_expr A Y (Suc (l + n)) (Suc (l + n), cmp h g) =
         polyn_expr A Y (Suc (l + n))
          (add_cf B (l + n, cmp h e)
            (ext_cf B (Suc n) (sp_cf B (cmp h f (Suc n)) (l, cmp h u))))) =
        (\<forall>j\<le>Suc (l + n).
            cmp h g j =
            snd (add_cf B (l + n, cmp h e)
                  (ext_cf B (Suc n)
                    (sp_cf B (cmp h f (Suc n)) (l, cmp h u))))
             j)")

   apply (rule allI, rule impI)
   apply (subst cmp_def)+
   apply (drule_tac a = j in forall_spec, simp, simp,
          thin_tac "g j = snd (add_cf S (l + n, e)
                     (ext_cf S (Suc n) (sp_cf S (f (Suc n)) (l, u)))) j")
   apply (case_tac "j = Suc (l+n)", simp)
     apply ((subst add_cf_def)+, 
            simp add:ext_cf_len, simp add:sp_cf_len,
            simp add:cmp_def PolynRg.ext_cf_len,
            simp add:PolynRg.sp_cf_len,
            (subst ext_cf_def)+, simp add:sp_cf_len sliden_def,
            (subst sp_cf_def)+, simp,
           frule_tac c = "(l, u)" and j = l in pol_coeff_mem, simp, simp,
           simp add:rHom_tOp)

 apply (frule_tac m = j and n = "Suc (l + n)" in noteq_le_less, assumption,
        thin_tac "j \<le> Suc (l + n)", thin_tac "j \<noteq> Suc (l + n)",
        (subst add_cf_def)+,
        simp add:ext_cf_len sp_cf_len, simp add:cmp_def,
        simp add:PolynRg.ext_cf_len PolynRg.sp_cf_len,
        (subst ext_cf_def)+, simp add:sp_cf_len,
        (subst sp_cf_def)+, simp add:sliden_def,
        frule_tac x = j and n = "l + n" in Suc_less_le)

 apply (rule conjI)
  apply (rule impI,
         frule_tac x = j and y = "Suc (l + n)" in less_imp_le,
         frule_tac m = j and n = "Suc (l + n)" and l = "Suc n" in diff_le_mono,
         simp,
         frule_tac c = "(l, u)" and j = "j - Suc n" in pol_coeff_mem, simp,
         frule_tac c = "(l + n, e)" and j = j in pol_coeff_mem, simp, simp,
         frule_tac x = "f (Suc n)" and y = "u (j - Suc n)" in 
          Ring.ring_tOp_closed[of S], assumption+,
         simp add:rHom_add rHom_tOp)
 apply (rule impI)
  apply (frule_tac c = "(l + n, e)" and j = j in pol_coeff_mem, simp, simp,
         frule_tac Ring.ring_zero[of S],
         simp add:rHom_add rHom_0_0)
done


lemma (in PolynRg) erH_multTr1:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B; 
      pol_coeff S c; pol_coeff S d;  pol_coeff S e; fst e = fst c + fst d; 
    (polyn_expr R X (fst c) c) \<cdot>\<^sub>r (polyn_expr R X (fst d) d) = 
     polyn_expr R X ((fst c) + (fst d)) e \<rbrakk> \<Longrightarrow> 
 (polyn_expr A Y (fst c) (cf_h h c)) \<cdot>\<^sub>r\<^bsub>A\<^esub> (polyn_expr A Y (fst d) (cf_h h d))
  =  (polyn_expr A Y (fst e) (cf_h h e))"
by (cases d, cases e) (simp add: erH_multTr)

lemma (in PolynRg) erHomTr0:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B; x \<in> carrier R\<rbrakk>
      \<Longrightarrow> erH R S X A B Y h (-\<^sub>a x) = -\<^sub>a\<^bsub>A\<^esub> (erH R S X A B Y h x)"
apply (cut_tac ring_is_ag,
       cut_tac subring, frule subring_Ring,
       frule PolynRg.is_Ring[of A B Y],
       frule Ring.ring_is_ag[of A],
       frule PolynRg.subring[of A B Y],
       frule Ring.subring_Ring[of A B], assumption+)   
apply (case_tac "x = \<zero>\<^bsub>R\<^esub>", simp add:aGroup.ag_inv_zero,
       simp add:erH_rHom_0[of A B Y h],
       frule Ring.ring_is_ag[of A], simp add:aGroup.ag_inv_zero)
apply (simp add:erH_def erh_def)
      apply (simp add:aGroup.ag_mOp_closed)
apply (frule_tac p = x in s_cf_expr, assumption+, (erule conjE)+)
apply (frule_tac x = x in aGroup.ag_mOp_closed, assumption+,
       frule_tac p = "-\<^sub>a x" in s_cf_expr,
       thin_tac "x = polyn_expr R X (fst (s_cf R S X x)) (s_cf R S X x)",      
       rule contrapos_pp, simp+,
       frule_tac x = x in aGroup.ag_inv_inv, simp, simp add:aGroup.ag_inv_zero,
       (erule conjE)+)

  apply (frule_tac c = "s_cf R S X (-\<^sub>a x)" in cf_h_coeff[of A B Y h],
         assumption+,
         frule_tac c = "s_cf R S X x" in cf_h_coeff[of A B Y h],
         assumption+)
  apply (frule polyn_minus_m_cf[of "s_cf R S X x" "fst (s_cf R S X x)"],
          simp) 
  apply (cut_tac a = "-\<^sub>a x" and 
          b = "polyn_expr R X (fst (s_cf R S X (-\<^sub>a x))) (s_cf R S X (-\<^sub>a x))"
     and  c = "polyn_expr R X (fst (s_cf R S X x)) (m_cf S (s_cf R S X x))" 
          in box_equation, assumption, simp,
          thin_tac "x = polyn_expr R X (fst (s_cf R S X x)) (s_cf R S X x)",
          thin_tac "-\<^sub>a x =
         polyn_expr R X (fst (s_cf R S X (-\<^sub>a x))) (s_cf R S X (-\<^sub>a x))",
          thin_tac "-\<^sub>a (polyn_expr R X (fst (s_cf R S X x)) (s_cf R S X x)) =
         polyn_expr R X (fst (s_cf R S X x)) (m_cf S (s_cf R S X x))",
         frule m_cf_pol_coeff[of "s_cf R S X x"])

  apply (subst PolynRg.polyn_minus_m_cf[of A B Y], assumption+,
         simp add:cf_h_len)
  apply (frule_tac c = "cf_h h (s_cf R S X x)" in 
                   PolynRg.m_cf_pol_coeff[of A B Y], assumption,
         frule PolynRg.pol_expr_unique2[of A B Y "cf_h h (s_cf R S X (-\<^sub>a x))" 
         "m_cf B (cf_h h (s_cf R S X x))"], assumption+)
  apply (simp add:cf_h_len)
  apply (simp add:PolynRg.m_cf_len cf_h_len)
  apply (simp add:s_cf_deg[THEN sym, of x],
         cut_tac ring_zero,         
         frule aGroup.ag_inv_inj[of R x \<zero>], assumption+, 
         simp only:aGroup.ag_inv_zero,
         subst s_cf_deg[THEN sym, of "-\<^sub>a x"], assumption+,
         simp add:deg_minus_eq)
  apply (simp add:cf_h_len PolynRg.m_cf_len,
         thin_tac "(polyn_expr A Y (fst (s_cf R S X (-\<^sub>a x)))
         (cf_h h (s_cf R S X (-\<^sub>a x))) = polyn_expr A Y (fst (s_cf R S X x))
         (m_cf B (cf_h h (s_cf R S X x)))) =
         (\<forall>j\<le>fst (s_cf R S X (-\<^sub>a x)). snd (cf_h h (s_cf R S X (-\<^sub>a x))) j =
          snd (m_cf B (cf_h h (s_cf R S X x))) j)")
   apply (rule allI, rule impI,
          subst m_cf_def)
   apply ((subst cf_h_def)+, simp add:cmp_def)
   apply (thin_tac "snd (s_cf R S X (-\<^sub>a x)) (fst (s_cf R S X (-\<^sub>a x))) \<noteq> \<zero>\<^bsub>S\<^esub>",
          thin_tac "pol_coeff B (cf_h h (s_cf R S X (-\<^sub>a x)))",
          thin_tac "pol_coeff B (cf_h h (s_cf R S X x))",
          thin_tac "pol_coeff B (m_cf B (cf_h h (s_cf R S X x)))")
   apply (frule m_cf_pol_coeff[of "s_cf R S X x"])
   apply (frule pol_expr_unique2[of "s_cf R S X (-\<^sub>a x)" 
                    "m_cf S (s_cf R S X x)"], assumption+,
          simp add:m_cf_len cf_h_len)
  apply (simp add:s_cf_deg[THEN sym, of x],
         cut_tac ring_zero,         
         frule aGroup.ag_inv_inj[of R x \<zero>], assumption+, 
         simp only:aGroup.ag_inv_zero,
         subst s_cf_deg[THEN sym, of "-\<^sub>a x"], assumption+,
         simp add:deg_minus_eq, simp add:m_cf_len)
  apply (drule_tac a = j in forall_spec, assumption,
         thin_tac "snd (s_cf R S X (-\<^sub>a x)) j = snd (m_cf S (s_cf R S X x)) j",
         thin_tac "polyn_expr R X (fst (s_cf R S X (-\<^sub>a x))) 
         (s_cf R S X (-\<^sub>a x)) =
         polyn_expr R X (fst (s_cf R S X x)) (m_cf S (s_cf R S X x))")
  apply (cut_tac ring_zero,         
         frule aGroup.ag_inv_inj[of R x \<zero>], assumption+, 
         simp only:aGroup.ag_inv_zero,
           (simp add:s_cf_deg[THEN sym, of "-\<^sub>a x"] deg_minus_eq,
             simp add:s_cf_deg[of x]) )
  apply (frule_tac j = j in pol_coeff_mem[of "s_cf R S X x"],
         assumption+)
  apply (subst m_cf_def, simp)
 apply (simp add:rHom_inv_inv)
done

lemma (in PolynRg) erHomTr1:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B; 
      a \<in> carrier R; b \<in> carrier R; a \<noteq> \<zero>; b \<noteq> \<zero>; a \<plusminus> b \<noteq> \<zero>;
      deg_n R S X a = deg_n R S X b\<rbrakk> \<Longrightarrow> 
      erH R S X A B Y h (a \<plusminus> b) = erH R S X A B Y h a \<plusminus>\<^bsub>A\<^esub> 
                                             (erH R S X A B Y h b)" 
apply (cut_tac ring_is_ag,
       cut_tac subring, frule subring_Ring,
       frule PolynRg.subring[of A B Y],
       frule_tac x = a and y = b in aGroup.ag_pOp_closed[of "R"], 
       assumption+,
       simp add:erH_def erh_def) 
apply (frule s_cf_expr[of a], assumption,
       frule s_cf_expr[of b], assumption,
       frule s_cf_expr[of "a \<plusminus> b"], assumption,
       (erule conjE)+,
       simp add:s_cf_deg)
apply (frule polyn_add1[of "s_cf R S X a" "s_cf R S X b"], assumption+)
apply (cut_tac a = "a \<plusminus> b" and 
       b = "polyn_expr R X (fst (s_cf R S X (a \<plusminus> b))) (s_cf R S X (a \<plusminus> b))" and
       c = "polyn_expr R X (max (fst (s_cf R S X a)) (fst (s_cf R S X b)))
       (add_cf S (s_cf R S X a) (s_cf R S X b))" in box_equation, 
       drule sym, drule sym, drule sym, simp,
       drule sym, drule sym, drule sym, simp,
       thin_tac "polyn_expr R X (fst (s_cf R S X a)) (s_cf R S X a) \<plusminus>
        polyn_expr R X (fst (s_cf R S X b)) (s_cf R S X b) =
        polyn_expr R X (max (fst (s_cf R S X a)) (fst (s_cf R S X b)))
        (add_cf S (s_cf R S X a) (s_cf R S X b))",
       thin_tac "a = polyn_expr R X (fst (s_cf R S X b)) (s_cf R S X a)",
       thin_tac "b = polyn_expr R X (fst (s_cf R S X b)) (s_cf R S X b)",
       thin_tac "a \<plusminus> b = 
         polyn_expr R X (fst (s_cf R S X (a \<plusminus> b))) (s_cf R S X (a \<plusminus> b))")
       apply simp

apply (frule cf_h_coeff[of A B Y h "s_cf R S X a"], assumption+,
       frule cf_h_coeff[of A B Y h "s_cf R S X b"], assumption+,
       frule cf_h_coeff[of A B Y h "s_cf R S X (a \<plusminus> b)"], assumption+)
apply (frule PolynRg.polyn_add1[of A B Y "cf_h h (s_cf R S X a)" 
                                "cf_h h (s_cf R S X b)"], assumption+,
       simp add:cf_h_len,
       thin_tac "polyn_expr A Y (fst (s_cf R S X b)) (cf_h h (s_cf R S X a))
        \<plusminus>\<^bsub>A\<^esub> polyn_expr A Y (fst (s_cf R S X b)) (cf_h h (s_cf R S X b)) =
             polyn_expr A Y (fst (s_cf R S X b))
               (add_cf B (cf_h h (s_cf R S X a)) (cf_h h (s_cf R S X b)))",
       frule PolynRg.add_cf_pol_coeff[of A B Y "cf_h h (s_cf R S X a)" 
                "cf_h h (s_cf R S X b)"], assumption+)
apply (case_tac "fst (s_cf R S X (a \<plusminus>\<^bsub>R\<^esub> b)) = fst (s_cf R S X b)")
apply (frule PolynRg.pol_expr_unique2[of A B Y "cf_h h (s_cf R S X (a \<plusminus> b))" 
              "add_cf B (cf_h h (s_cf R S X a)) (cf_h h (s_cf R S X b))"],
       assumption+)
       apply (simp add:cf_h_len add_cf_len,
              simp add:PolynRg.add_cf_len cf_h_len)
       apply (simp add:PolynRg.add_cf_len cf_h_len,
       thin_tac "(polyn_expr A Y (fst (s_cf R S X b)) (cf_h h (s_cf R S X 
        (a \<plusminus> b))) = polyn_expr A Y (fst (s_cf R S X b))
         (add_cf B (cf_h h (s_cf R S X a)) (cf_h h (s_cf R S X b)))) =
         (\<forall>j\<le>fst (s_cf R S X b).
          snd (cf_h h (s_cf R S X (a \<plusminus> b))) j =
          snd (add_cf B (cf_h h (s_cf R S X a)) (cf_h h (s_cf R S X b))) j)")

apply (frule pol_expr_unique2[of "s_cf R S X (a \<plusminus> b)" 
              "add_cf S (s_cf R S X a) (s_cf R S X b)"])
       apply (simp add:add_cf_pol_coeff)
       apply (simp add:add_cf_len, simp add:add_cf_len,
       thin_tac "polyn_expr R X (fst (s_cf R S X b)) (s_cf R S X (a \<plusminus> b)) =
                 polyn_expr R X (fst (s_cf R S X b))
                 (add_cf S (s_cf R S X a) (s_cf R S X b))")
apply (rule allI, rule impI,
       drule_tac a = j in forall_spec, assumption,
       subst add_cf_def, simp add:cf_h_len,
       (subst cf_h_def)+, (subst cmp_def)+, simp,
        thin_tac "snd (s_cf R S X (a \<plusminus> b)) j =
         snd (add_cf S (s_cf R S X a) (s_cf R S X b)) j")
       apply (subst add_cf_def, simp)
apply (frule_tac j = j in pol_coeff_mem[of "s_cf R S X a"], simp, 
       frule_tac j = j in pol_coeff_mem[of "s_cf R S X b"], simp,
       simp add:rHom_add)

apply (frule s_cf_deg[of a], assumption, 
       frule s_cf_deg[of b], assumption,
       frule s_cf_deg[of "a \<plusminus> b"], assumption,
       frule deg_pols_add2[of a b], assumption+,
       simp add:deg_def, simp add:deg_def ale_natle,
       frule_tac m = "fst (s_cf R S X (a \<plusminus> b))" and n = "fst (s_cf R S X b)" 
                 in noteq_le_less, assumption+)
apply (frule pol_expr_unique3[of "s_cf R S X (a \<plusminus> b)"
              "add_cf S (s_cf R S X a) (s_cf R S X b)"],
       simp add:add_cf_pol_coeff,
       simp add:add_cf_len,
       simp add:add_cf_len,
       thin_tac "polyn_expr R X (fst (s_cf R S X (a \<plusminus> b))) (s_cf R S X (a \<plusminus> b))
        =  polyn_expr R X (fst (s_cf R S X b)) 
                           (add_cf S (s_cf R S X a) (s_cf R S X b))")
apply (frule PolynRg.pol_expr_unique3[of A B Y "cf_h h (s_cf R S X (a \<plusminus> b))" 
              "add_cf B (cf_h h (s_cf R S X a)) (cf_h h (s_cf R S X b))"],
         assumption+,
       simp add:cf_h_len PolynRg.add_cf_len,
       simp add:PolynRg.add_cf_len cf_h_len,
       thin_tac "(polyn_expr A Y (fst (s_cf R S X (a \<plusminus> b)))
       (cf_h h (s_cf R S X (a \<plusminus> b))) = polyn_expr A Y (fst (s_cf R S X b))
       (add_cf B (cf_h h (s_cf R S X a)) (cf_h h (s_cf R S X b)))) =
       ((\<forall>j\<le>fst (s_cf R S X (a \<plusminus> b)).
          snd (cf_h h (s_cf R S X (a \<plusminus> b))) j =
          snd (add_cf B (cf_h h (s_cf R S X a)) (cf_h h (s_cf R S X b))) j) \<and>
        (\<forall>j\<in>nset (Suc (fst (s_cf R S X (a \<plusminus> b)))) (fst (s_cf R S X b)).
          snd (add_cf B (cf_h h (s_cf R S X a)) (cf_h h (s_cf R S X b))) j =
          \<zero>\<^bsub>B\<^esub>))",
        thin_tac "pol_coeff B (cf_h h (s_cf R S X a))",
        thin_tac "pol_coeff B (cf_h h (s_cf R S X b))",
        thin_tac "pol_coeff B (cf_h h (s_cf R S X (a \<plusminus> b)))",
        thin_tac "pol_coeff B (add_cf B (cf_h h (s_cf R S X a)) 
                                         (cf_h h (s_cf R S X b)))",
        thin_tac "deg_n R S X a = fst (s_cf R S X b)",
        thin_tac "deg_n R S X b = fst (s_cf R S X b)",
        thin_tac "deg_n R S X (a \<plusminus> b) = fst (s_cf R S X (a \<plusminus> b))")
apply (rule conjI, erule conjE,
      thin_tac "\<forall>j\<in>nset (Suc (fst (s_cf R S X (a \<plusminus> b)))) (fst (s_cf R S X b)).
         snd (add_cf S (s_cf R S X a) (s_cf R S X b)) j = \<zero>\<^bsub>S\<^esub>")
   apply (rule allI, rule impI,
          drule_tac a = j in forall_spec, assumption,
          (subst cf_h_def)+, (subst cmp_def)+, simp,
          (subst add_cf_def)+, simp,
         frule_tac j = j in pol_coeff_mem[of "s_cf R S X a"], simp,
         frule_tac j = j in pol_coeff_mem[of "s_cf R S X b"], simp,
         simp add:rHom_add)
apply (erule conjE,
       thin_tac "\<forall>j\<le>fst (s_cf R S X (a \<plusminus> b)). snd (s_cf R S X (a \<plusminus> b)) j =
        snd (add_cf S (s_cf R S X a) (s_cf R S X b)) j")
  apply (rule ballI,
         drule_tac x = j in bspec, assumption,
         simp add:add_cf_def cf_h_len,
         simp add:cf_h_def cmp_def,
         frule_tac j = j in pol_coeff_mem[of "s_cf R S X a"], 
         simp add:nset_def,
         frule_tac j = j in pol_coeff_mem[of "s_cf R S X b"], 
         simp add:nset_def)
  apply (subst rHom_add[THEN sym, of h S B], assumption+, simp,
         (frule PolynRg.is_Ring[of A B Y],
          frule Ring.subring_Ring[of A B], assumption),
         simp add:rHom_0_0[of S B])
done
      
lemma (in PolynRg) erHomTr2:"\<lbrakk>PolynRg A B Y; h \<in> rHom S B; 
      a \<in> carrier R; b \<in> carrier R; a \<noteq> \<zero>; b \<noteq> \<zero>; a \<plusminus> b \<noteq> \<zero>;
      deg_n R S X a < deg_n R S X b\<rbrakk> \<Longrightarrow> 
      erH R S X A B Y h (a \<plusminus> b) = erH R S X A B Y h a \<plusminus>\<^bsub>A\<^esub> 
                                             (erH R S X A B Y h b)"
apply (cut_tac ring_is_ag,
       cut_tac subring, frule subring_Ring,
       frule PolynRg.subring[of A B Y],
       frule_tac x = a and y = b in aGroup.ag_pOp_closed[of "R"], 
       assumption+,
       simp add:erH_def erh_def) 
apply (frule s_cf_expr[of a], assumption,
       frule s_cf_expr[of b], assumption,
       frule s_cf_expr[of "a \<plusminus> b"], assumption,
       (erule conjE)+,
       frule polyn_deg_add1[of a b], assumption+,
       simp add:s_cf_deg)
apply (frule polyn_add1[of "s_cf R S X a" "s_cf R S X b"], assumption+)
apply (cut_tac a = "a \<plusminus> b" and 
       b = "polyn_expr R X (fst (s_cf R S X b)) (s_cf R S X (a \<plusminus> b))" and
       c = "polyn_expr R X (max (fst (s_cf R S X a)) (fst (s_cf R S X b)))
       (add_cf S (s_cf R S X a) (s_cf R S X b))" in box_equation,
       drule sym, drule sym, drule sym, simp,
       drule sym, drule sym, drule sym, simp,
       thin_tac "polyn_expr R X (fst (s_cf R S X a)) (s_cf R S X a) \<plusminus>
        polyn_expr R X (fst (s_cf R S X b)) (s_cf R S X b) =
        polyn_expr R X (max (fst (s_cf R S X a)) (fst (s_cf R S X b)))
        (add_cf S (s_cf R S X a) (s_cf R S X b))",
       thin_tac "a = polyn_expr R X (fst (s_cf R S X a)) (s_cf R S X a)",
       thin_tac "b = polyn_expr R X (fst (s_cf R S X b)) (s_cf R S X b)",
       thin_tac "a \<plusminus> b = polyn_expr R X (fst (s_cf R S X b)) 
                            (s_cf R S X (a \<plusminus> b))",
       simp)

apply (frule cf_h_coeff[of A B Y h "s_cf R S X a"], assumption+,
       frule cf_h_coeff[of A B Y h "s_cf R S X b"], assumption+,
       frule cf_h_coeff[of A B Y h "s_cf R S X (a \<plusminus> b)"], assumption+)
apply (frule PolynRg.polyn_add1[of A B Y "cf_h h (s_cf R S X a)" 
                                "cf_h h (s_cf R S X b)"], assumption+,
       simp add:cf_h_len)
apply (thin_tac "polyn_expr A Y (fst (s_cf R S X a)) (cf_h h (s_cf R S X a))
        \<plusminus>\<^bsub>A\<^esub> polyn_expr A Y (fst (s_cf R S X b)) (cf_h h (s_cf R S X b)) =
        polyn_expr A Y (fst (s_cf R S X b))
        (add_cf B (cf_h h (s_cf R S X a)) (cf_h h (s_cf R S X b)))",
       frule PolynRg.add_cf_pol_coeff[of A B Y "cf_h h (s_cf R S X a)" 
                "cf_h h (s_cf R S X b)"], assumption+)
apply (frule PolynRg.pol_expr_unique2[of A B Y "cf_h h (s_cf R S X (a \<plusminus> b))" 
              "add_cf B (cf_h h (s_cf R S X a)) (cf_h h (s_cf R S X b))"],
       assumption+,
       simp add:cf_h_len add_cf_len,
       simp add:PolynRg.add_cf_len cf_h_len,
       simp add:PolynRg.add_cf_len cf_h_len,
       thin_tac "(polyn_expr A Y (fst (s_cf R S X b)) 
        (cf_h h (s_cf R S X (a \<plusminus> b))) = polyn_expr A Y (fst (s_cf R S X b))
        (add_cf B (cf_h h (s_cf R S X a)) (cf_h h (s_cf R S X b)))) =
       (\<forall>j\<le>fst (s_cf R S X b).
         snd (cf_h h (s_cf R S X (a \<plusminus> b))) j =
         snd (add_cf B (cf_h h (s_cf R S X a)) (cf_h h (s_cf R S X b))) j)")

apply (frule pol_expr_unique2[of "s_cf R S X (a \<plusminus> b)" 
              "add_cf S (s_cf R S X a) (s_cf R S X b)"],
       simp add:add_cf_pol_coeff,
       simp add:add_cf_len, simp add:add_cf_len) 
apply (thin_tac "polyn_expr R X (fst (s_cf R S X b)) (s_cf R S X (a \<plusminus> b)) =
        polyn_expr R X (fst (s_cf R S X b))
       (add_cf S (s_cf R S X a) (s_cf R S X b))")
apply (rule allI, rule impI,
       drule_tac a = j in forall_spec, assumption,
       subst add_cf_def, simp add:cf_h_len,
       (subst cf_h_def)+, (subst cmp_def)+, simp,
        subst add_cf_def, simp)
apply (case_tac "j \<le> fst (s_cf R S X a)", simp)
apply (frule_tac j = j in pol_coeff_mem[of "s_cf R S X a"], simp, 
       frule_tac j = j in pol_coeff_mem[of "s_cf R S X b"], simp,
       simp add:rHom_add)
    apply simp
   apply (subst add_cf_def, simp)
done

lemma (in PolynRg) erH_rHom:"\<lbrakk>Idomain S; PolynRg A B Y; h \<in> rHom S B\<rbrakk>
   \<Longrightarrow> erH R S X A B Y h \<in> pHom R S X, A B Y"
apply (frule Idomain.idom_is_ring[of "S"],
       cut_tac subring,
       cut_tac polyn_ring_integral, simp,
       frule PolynRg.subring[of A B Y],
       frule PolynRg.is_Ring[of A B Y],
       frule Ring.subring_Ring[of A B], assumption)
apply (simp add:polyn_Hom_def,
       rule conjI)
 prefer 2
apply (cut_tac polyn_ring_X_nonzero,
       cut_tac X_mem_R, rule conjI,
       rule subsetI, simp add:image_def,
       erule bexE)  

apply (case_tac "xa = \<zero>\<^bsub>S\<^esub>", 
       simp add:Subring_zero_ring_zero,
       simp add:erH_rHom_0,
       simp add:Ring.Subring_zero_ring_zero[THEN sym, of A B],
       simp add:Ring.ring_zero[of B])
apply (simp add:Subring_zero_ring_zero,
       frule_tac x = xa in mem_subring_mem_ring, assumption,
       frule_tac p = xa in s_cf_expr, assumption+, (erule conjE)+,
       frule_tac p1 = xa in s_cf_deg[THEN sym], assumption+,
       frule_tac p1 = xa in pol_of_deg0[THEN sym], assumption+, simp)
apply (simp add:erH_def erh_def, subst polyn_expr_def, simp,
       frule_tac c = "s_cf R S X xa" in cf_h_coeff[of A B Y h], assumption+,
       frule_tac c = "cf_h h (s_cf R S X xa)" and j = 0 in 
                         PolynRg.pol_coeff_mem[of A B Y], assumption, simp,
       frule_tac c = "cf_h h (s_cf R S X xa)" and j = 0 in 
                         PolynRg.pol_coeff_mem_R[of A B Y], assumption, simp,
       simp add:Ring.ring_r_one[of A])

apply (cut_tac pol_expr_of_X,
       cut_tac special_cf_pol_coeff,
       frule ext_cf_pol_coeff[of "C\<^sub>0 S" "Suc 0"])
apply (simp add:erH_def erh_def)
apply (cut_tac deg_n_of_X)
 apply (frule s_cf_expr[of X], assumption+, (erule conjE)+,
        frule_tac a = X and 
        b = "polyn_expr R X (Suc 0) (ext_cf S (Suc 0) (C\<^sub>0 S))" and 
        c = "polyn_expr R X (fst (s_cf R S X X)) (s_cf R S X X)" in
        box_equation, assumption+,
        thin_tac "X = polyn_expr R X (Suc 0) (ext_cf S (Suc 0) (C\<^sub>0 S))",
        thin_tac "X = polyn_expr R X (fst (s_cf R S X X)) (s_cf R S X X)")
 apply (rule sym, subst PolynRg.pol_expr_of_X[of A B Y], assumption+,
        frule s_cf_deg[of X], assumption+, simp)
 apply (frule pol_expr_unique2[of "ext_cf S (Suc 0) (C\<^sub>0 S)" "s_cf R S X X"],
        assumption+, simp add:ext_cf_len special_cf_len,
        simp add:ext_cf_len special_cf_len)
 apply (frule cf_h_coeff[of A B Y h "ext_cf S (Suc 0) (C\<^sub>0 S)"], assumption+,
        frule cf_h_coeff[of A B Y h "s_cf R S X X"], assumption+)
 apply (frule PolynRg.pol_expr_unique2[of A B Y 
          "cf_h h (ext_cf S (Suc 0) (C\<^sub>0 S))" "cf_h h (s_cf R S X X)"],
        assumption+,
        simp add:cf_h_len ext_cf_len special_cf_len,
        simp add:cf_h_len ext_cf_len special_cf_len)
 
apply (simp add:cf_h_special_cf)
apply (thin_tac "(polyn_expr A Y (Suc 0) (ext_cf B (Suc 0) (C\<^sub>0 B)) =
        polyn_expr A Y (Suc 0) (cf_h h (s_cf R S X X))) =
         (\<forall>j\<le>Suc 0.
           snd (cf_h h (ext_cf S (Suc 0) (C\<^sub>0 S))) j =
           snd (cf_h h (s_cf R S X X)) j)")
 apply (rule allI, rule impI,
        drule_tac a = j in forall_spec, assumption,
        (subst cf_h_def)+, (subst cmp_def)+, simp)

apply (subst rHom_def, simp,
       cut_tac ring_is_ag,
       frule Ring.ring_is_ag[of A])
apply (rule conjI)
 apply (subst aHom_def, simp)
 apply (rule conjI)
  apply (simp add:erH_mem)
  apply (rule conjI, simp add:erH_def erh_def extensional_def)
  apply (rule ballI)+
  
  apply (case_tac "a = \<zero>\<^bsub>R\<^esub>", 
          case_tac "b = \<zero>\<^bsub>R\<^esub>", simp) 
  apply (simp add:erH_rHom_0,
         frule Ring.ring_is_ag[of A], frule Ring.ring_zero[of A],
         simp add:aGroup.ag_r_zero)
  apply (simp add:erH_rHom_0, simp add:erH_rHom_0)
  apply (frule_tac p = b in erH_mem[of A B Y h], assumption+) 
  apply (simp add:aGroup.ag_l_zero)

   apply (case_tac "b = \<zero>\<^bsub>R\<^esub>", simp) 
   apply (simp add:erH_rHom_0,
          frule_tac p = a in erH_mem[of A B Y h], assumption+,
          simp add:aGroup.ag_r_zero)

   apply (case_tac "a \<plusminus>\<^bsub>R\<^esub> b = \<zero>\<^bsub>R\<^esub>", simp add:erH_rHom_0) 
   apply (frule_tac x = a and y = b in aGroup.ag_inv_unique[of R],
          assumption+, simp,
          thin_tac "b = -\<^sub>a a")
   apply (subst erHomTr0[of A B Y h], assumption+,
          frule_tac p = a in erH_mem[of A B Y h], assumption+,
          simp add:aGroup.ag_r_inv1)
   
   apply (case_tac "deg_n R S X a = deg_n R S X b",
          simp add:erHomTr1[of A B Y h])
   apply (cut_tac y = "deg_n R S X a" and x = "deg_n R S X b" in less_linear,
          simp)
   apply (erule disjE)
   apply (subst aGroup.ag_pOp_commute, assumption+,
          frule_tac p = a in erH_mem[of A B Y h], assumption+,
          frule_tac p = b in erH_mem[of A B Y h], assumption+,
          subst aGroup.ag_pOp_commute[of A], assumption+,
          rule erHomTr2[of A B Y h], assumption+,
          simp add:aGroup.ag_pOp_commute, assumption)
  
    apply(rule erHomTr2[of A B Y h], assumption+)

 apply (simp add:erH_rHomTr2)
 apply (rule ballI)+
 apply (case_tac "x = \<zero>\<^bsub>R\<^esub>", simp add:ring_times_0_x erH_rHom_0,
        frule_tac p = y in erH_mem[of A B Y h], assumption+,
        simp add:Ring.ring_times_0_x[of A])
 apply (case_tac "y = \<zero>\<^bsub>R\<^esub>", simp add:ring_times_x_0 erH_rHom_0,
        frule_tac p = x in erH_mem[of A B Y h], assumption+,
        simp add:Ring.ring_times_x_0[of A])
 
 apply (frule_tac p = x in s_cf_expr, assumption+,
        frule_tac p = y in s_cf_expr, assumption+,
        frule_tac x = x and y = y in ring_tOp_closed, assumption+, 
        frule_tac p = "x \<cdot>\<^sub>r y" in s_cf_expr,
        simp add:Idomain.idom_tOp_nonzeros, (erule conjE)+)

 apply (frule_tac c = "s_cf R S X x" and d = "s_cf R S X y" in 
                  polyn_expr_tOp_c, assumption+, erule exE, (erule conjE)+,
        cut_tac a = "x \<cdot>\<^sub>r y" and 
        b = "polyn_expr R X (fst (s_cf R S X (x \<cdot>\<^sub>r y))) (s_cf R S X (x \<cdot>\<^sub>r y))" 
        and c = "polyn_expr R X (fst e) e" in box_equation)  
       apply assumption
       apply (thin_tac "x \<cdot>\<^sub>r y =
        polyn_expr R X (fst (s_cf R S X (x \<cdot>\<^sub>r y))) (s_cf R S X (x \<cdot>\<^sub>r y))")
       apply (drule sym, drule sym, simp) 
  
   apply (thin_tac "x = polyn_expr R X (fst (s_cf R S X x)) (s_cf R S X x)",
          thin_tac "y = polyn_expr R X (fst (s_cf R S X y)) (s_cf R S X y)",
         thin_tac "x \<cdot>\<^sub>r y =
        polyn_expr R X (fst (s_cf R S X (x \<cdot>\<^sub>r y))) (s_cf R S X (x \<cdot>\<^sub>r y))")

 apply ((subst erH_def)+, (subst erh_def)+, simp)
          
 apply (frule_tac c = "s_cf R S X x" and d = "s_cf R S X y" and e = e in
        erH_multTr1[of A B Y h], assumption+, simp, simp,
     thin_tac "polyn_expr A Y (fst (s_cf R S X x)) (cf_h h (s_cf R S X x)) \<cdot>\<^sub>r\<^bsub>A\<^esub>
     polyn_expr A Y (fst (s_cf R S X y)) (cf_h h (s_cf R S X y)) =
     polyn_expr A Y (fst (s_cf R S X x) + fst (s_cf R S X y)) (cf_h h e)")
 apply (rotate_tac -1, drule sym, simp,
       thin_tac "polyn_expr R X (fst (s_cf R S X x)) (s_cf R S X x) \<cdot>\<^sub>r
        polyn_expr R X (fst (s_cf R S X y)) (s_cf R S X y) =
        polyn_expr R X (fst (s_cf R S X (x \<cdot>\<^sub>r y))) (s_cf R S X (x \<cdot>\<^sub>r y))",
       rotate_tac -1, drule sym) 
  apply (frule_tac p = x in s_cf_deg, assumption,
         frule_tac p = y in s_cf_deg, assumption,
         frule_tac x = x and y = y in Idomain.idom_tOp_nonzeros[of R],
         assumption+,
         frule_tac p = "x \<cdot>\<^sub>r y" in s_cf_deg, assumption+)
  apply (frule_tac p = x and q = y in deg_mult_pols, assumption+,
         (erule conjE)+, simp,
         thin_tac "deg_n R S X x = fst (s_cf R S X x)", 
         thin_tac "deg_n R S X y = fst (s_cf R S X y)", 
         thin_tac "deg_n R S X (x \<cdot>\<^sub>r y) = fst (s_cf R S X (x \<cdot>\<^sub>r y))",
         rotate_tac -2, drule sym)
         apply (simp add:cf_h_len)
  apply (frule_tac c = "s_cf R S X (x \<cdot>\<^sub>r y)" in cf_h_coeff[of A B Y h],
          assumption+,
         frule_tac c = e in cf_h_coeff[of A B Y h], assumption+)
  apply (frule_tac c = "cf_h h (s_cf R S X (x \<cdot>\<^sub>r y))" and d = "cf_h h e" in 
         PolynRg.pol_expr_unique2[of A B Y], assumption+,
         simp add:cf_h_len, simp add:cf_h_len,
         thin_tac "(polyn_expr A Y (fst (s_cf R S X x) + fst (s_cf R S X y))
          (cf_h h (s_cf R S X (x \<cdot>\<^sub>r y))) =
           polyn_expr A Y (fst (s_cf R S X x) + fst (s_cf R S X y))
          (cf_h h e)) =
          (\<forall>j\<le>fst (s_cf R S X x) + fst (s_cf R S X y).
            snd (cf_h h (s_cf R S X (x \<cdot>\<^sub>r y))) j = snd (cf_h h e) j)")
  apply (frule_tac c = "s_cf R S X (x \<cdot>\<^sub>r y)" and d = e in 
         pol_expr_unique2, assumption+, simp, simp,
         thin_tac "polyn_expr R X (fst (s_cf R S X x) + fst (s_cf R S X y))
         (s_cf R S X (x \<cdot>\<^sub>r y)) =
         polyn_expr R X (fst (s_cf R S X x) + fst (s_cf R S X y)) e")
  apply (rule allI, rule impI, drule_tac a = j in forall_spec, assumption,
         subst cf_h_def, subst cmp_def, simp, 
         subst cf_h_def, subst cmp_def, simp)
done  

lemma (in PolynRg) erH_q_rHom:"\<lbrakk>Idomain S; maximal_ideal S P; 
       PolynRg R' (S /\<^sub>r P) Y\<rbrakk> \<Longrightarrow>
       erH R S X R' (S /\<^sub>r P) Y (pj S P) \<in> pHom R S X, R' (S /\<^sub>r P) Y"
apply (frule Idomain.idom_is_ring[of "S"],
       frule Ring.qring_ring[of S P], simp add:Ring.maximal_ideal_ideal,
       rule erH_rHom[of R' "S /\<^sub>r P" Y "pj S P"], assumption+)
apply (rule pj_Hom[of S P], assumption+,
       simp add:Ring.maximal_ideal_ideal)
done 

lemma (in PolynRg) erH_add:"\<lbrakk>Idomain S; PolynRg A B Y; h \<in> rHom S B;
                   p \<in> carrier R; q \<in> carrier R\<rbrakk> \<Longrightarrow> 
          erH R S X A B Y h (p \<plusminus> q) =
                 (erH R S X A B Y h p) \<plusminus>\<^bsub>A\<^esub> (erH R S X A B Y h q)"
apply (frule erH_rHom[of A B Y h], assumption+)
apply (simp add:polyn_Hom_def, (erule conjE)+)
apply (simp add:rHom_add)
done

lemma (in PolynRg) erH_minus:"\<lbrakk>Idomain S; PolynRg A B Y; 
       h \<in> rHom S B; p \<in> carrier R\<rbrakk> \<Longrightarrow>  
        erH R S X A B Y h (-\<^sub>a p) = -\<^sub>a\<^bsub>A\<^esub> (erH R S X A B Y h p)"
apply (frule erH_rHom[of A B Y h], assumption+,
       simp add:polyn_Hom_def, (erule conjE)+)
apply (frule PolynRg.is_Ring[of A B Y])
apply (rule rHom_inv_inv[of R A p "erH R S X A B Y h"])
apply (cut_tac is_Ring, assumption+) 
done

lemma (in PolynRg) erH_mult:"\<lbrakk>Idomain S; PolynRg A B Y; h \<in> rHom S B; 
      p \<in> carrier R; q \<in> carrier R\<rbrakk> \<Longrightarrow>  
      erH R S X A B Y h (p \<cdot>\<^sub>r q) =
                 (erH R S X A B Y h p) \<cdot>\<^sub>r\<^bsub>A\<^esub> (erH R S X A B Y h q)"
apply (frule erH_rHom[of A B Y h], assumption+,
       simp add:polyn_Hom_def, (erule conjE)+,
       frule PolynRg.is_Ring[of A B Y],
       cut_tac is_Ring,
       rule rHom_tOp[of R A p q "erH R S X A B Y h"], assumption+)
done

lemma (in PolynRg) erH_rHom_cf:"\<lbrakk>Idomain S; PolynRg A B Y; h \<in> rHom S B; 
                   s \<in> carrier S\<rbrakk>  \<Longrightarrow> erH R S X A B Y h s = h s"
apply (cut_tac subring, frule subring_Ring,
       frule PolynRg.subring[of A B Y], 
       frule PolynRg.is_Ring[of A B Y],
       frule Ring.subring_Ring[of A B], assumption,
       frule mem_subring_mem_ring[of S s], assumption+)
apply (case_tac "s = \<zero>\<^bsub>S\<^esub>", simp add:Subring_zero_ring_zero,
       simp add:erH_rHom_0,
       simp add:Subring_zero_ring_zero[THEN sym], 
       simp add:rHom_0_0, simp add:Ring.Subring_zero_ring_zero)
apply (frule s_cf_expr[of s],simp add:Subring_zero_ring_zero,
       (erule conjE)+,
       simp add:Subring_zero_ring_zero)
apply (frule s_cf_deg[of s], assumption+,
       frule pol_of_deg0[of s], assumption+, simp)
apply (subst erH_def, simp,
       subst erh_rHom_coeff[of A B Y h "s_cf R S X s"], assumption+,
       simp add:cmp_def polyn_expr_def,
       frule_tac c = "s_cf R S X s" and j = 0 in pol_coeff_mem, simp,
       frule mem_subring_mem_ring[of S "snd (s_cf R S X s) 0"], assumption+,
       simp add:ring_r_one)
done

lemma (in PolynRg) erH_rHom_coeff:"\<lbrakk>Idomain S; PolynRg A B Y; h \<in> rHom S B; 
       pol_coeff S (n, f)\<rbrakk>  \<Longrightarrow> pol_coeff B (n, cmp h f)"
apply (simp add:pol_coeff_def)
 apply (rule allI, rule impI, drule_tac a = j in forall_spec, assumption)
 apply (simp add:cmp_def rHom_mem)
done

lemma (in PolynRg) erH_rHom_unique:"\<lbrakk>Idomain S; PolynRg A B Y; h \<in> rHom S B\<rbrakk>
     \<Longrightarrow>  \<exists>!g. g \<in> pHom R S X, A B Y \<and> (\<forall>x\<in>carrier S. h x = g x)" 
apply (cut_tac subring, frule subring_Ring,
       cut_tac is_Ring,
       frule PolynRg.subring[of A B Y], 
       frule PolynRg.is_Ring[of A B Y],
       frule Ring.subring_Ring[of A B], assumption,
       frule Idomain.idom_is_ring[of S])

apply (rule ex_ex1I)
 apply (frule erH_rHom[of A B Y h], assumption+)
 apply (subgoal_tac "\<forall>x\<in>carrier S. h x = (erH R S X A B Y h) x", blast)
 apply (rule ballI, simp add:erH_rHom_cf, (erule conjE)+)
 apply (frule pHom_rHom[of A B Y], assumption+,
        frule pHom_rHom[of A B Y], assumption+,
        frule_tac f = g in rHom_func[of _ R A],
        frule_tac f = y in rHom_func[of _ R A])
 apply (rule_tac f = g and g = y in funcset_eq[of _ "carrier R"],
        simp add:rHom_def aHom_def, simp add:rHom_def aHom_def)
 apply (rule ballI,
        thin_tac "g \<in> carrier R \<rightarrow> carrier A",
        thin_tac "y \<in> carrier R \<rightarrow> carrier A")

 apply (case_tac "x = \<zero>\<^bsub>R\<^esub>", simp,
        subst rHom_0_0[of R A], assumption+, rule sym, 
        subst rHom_0_0[of R A], assumption+, simp)
 apply (subst pHom_pol_mem[of A B Y], assumption+)
 apply (frule_tac f = y and p = x in pHom_pol_mem[of A B Y], assumption+,
        simp,
        frule_tac f = g and c = "s_cf R S X x" in polyn_Hom_coeff_to_coeff,
        assumption+, simp add:s_cf_pol_coeff,
        frule_tac f = y and c = "s_cf R S X x" in polyn_Hom_coeff_to_coeff,
        assumption+, simp add:s_cf_pol_coeff)
 apply (simp add:s_cf_deg)
  apply (frule_tac f = g and c = "s_cf R S X x" in cf_h_len1[of A B Y h],
         assumption+, rule ballI, rule sym, simp, rule s_cf_pol_coeff, 
         assumption+)
  apply (frule_tac f = y and c = "s_cf R S X x" in cf_h_len1[of A B Y h],
         assumption+, rule ballI, rule sym, simp, rule s_cf_pol_coeff, 
         assumption+)
 apply (frule_tac c = "cf_h g (s_cf R S X x)" and d = "cf_h y (s_cf R S X x)"
         in PolynRg.pol_expr_unique2[of A B Y], assumption+, simp)
 apply (frule_tac p = x in s_cf_pol_coeff, simp add:cf_h_len,
        thin_tac "(polyn_expr A Y (fst (s_cf R S X x)) (cf_h g (s_cf R S X x))
         = polyn_expr A Y (fst (s_cf R S X x)) (cf_h y (s_cf R S X x))) =
        (\<forall>j\<le>fst (s_cf R S X x).
            snd (cf_h g (s_cf R S X x)) j = snd (cf_h y (s_cf R S X x)) j)")
 apply (rule allI, rule impI,
        (subst cf_h_def)+, (subst cmp_def)+, simp,
        frule_tac c = "s_cf R S X x" and j = j in pol_coeff_mem, assumption+)
 apply simp
done

lemma (in PolynRg) erH_rHom_unique1:"\<lbrakk>Idomain S; PolynRg A B Y; h \<in> rHom S B; 
       f \<in> pHom R S X, A B Y; \<forall>x \<in> carrier S. f x = h x\<rbrakk> \<Longrightarrow> 
       f = (erH R S X A B Y h)"
apply (frule erH_rHom_unique[of A B Y h], assumption+,
       erule ex1E,
       frule_tac x = f in spec,
       drule_tac x = "erH R S X A B Y h" in spec)
 apply (frule erH_rHom[of A B Y h], assumption+,
        simp add:erH_rHom_cf[THEN sym])
done

lemma (in PolynRg) pHom_dec_deg:"\<lbrakk>PolynRg A B Y; f \<in> pHom R S X, A B Y; 
       p \<in> carrier R\<rbrakk> \<Longrightarrow> 
                  deg A B Y (f p) \<le> deg R S X p"
apply (cut_tac subring, frule subring_Ring,
       frule PolynRg.subring[of A B Y],
       cut_tac is_Ring)
apply (frule PolynRg.is_Ring[of A B Y], 
       frule Ring.subring_Ring[of A B], assumption) 
apply (case_tac "f p = \<zero>\<^bsub>A\<^esub>",
       case_tac "p = \<zero>\<^bsub>R\<^esub>",
       simp add:deg_def, simp add:deg_def an_def,
       simp add:deg_def, subst ale_natle) 
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>",
       frule pHom_rHom[of A B Y f], assumption+,
       rule conjI, rule impI, frule rHom_0_0[of R A f], assumption+,
       simp, rule impI, simp)

apply simp
 apply (frule pHom_pol_mem[of A B Y f p], assumption+)
 apply (cut_tac polyn_Hom_coeff_to_coeff[of A B Y f "s_cf R S X p"])
 apply (frule PolynRg.pol_deg_le_n[of A B Y "f p" "cf_h f (s_cf R S X p)"],
        frule pHom_rHom[of A B Y f], assumption+,
        rule rHom_mem[of f R A p], assumption+,
        frule s_cf_pol_coeff[of p],
        subst cf_h_len2[of A B Y f "s_cf R S X p"], assumption+,
        simp add:s_cf_deg,
       thin_tac "f p = polyn_expr A Y (deg_n R S X p) (cf_h f (s_cf R S X p))")
       apply (frule s_cf_pol_coeff[of p], simp add:cf_h_len2, 
              simp add:s_cf_deg[THEN sym],
              assumption+,
              simp add:s_cf_pol_coeff)
done
       
lemma (in PolynRg) erH_map:"\<lbrakk>Idomain S; PolynRg A B Y; h \<in> rHom S B; 
       pol_coeff S (n, c)\<rbrakk> \<Longrightarrow> 
      (erH R S X A B Y h) (polyn_expr R X n (n, c)) = 
                           polyn_expr A Y n (n, (cmp h c))"
apply (cut_tac subring, frule subring_Ring,
       frule PolynRg.subring[of A B Y],
       cut_tac is_Ring,
       frule PolynRg.is_Ring[of A B Y], 
       frule Ring.subring_Ring[of A B], assumption) 
apply (case_tac "polyn_expr R X n (n, c) = \<zero>\<^bsub>R\<^esub>", simp add:erH_rHom_0)
 apply (frule coeff_0_pol_0[THEN sym, of "(n, c)" n], simp, simp,
        thin_tac "polyn_expr R X n (n, c) = \<zero>")
 apply (frule cf_h_coeff[of A B Y h "(n, c)"], assumption+,
        simp add:cf_h_pol_coeff)
 apply (rule sym, 
        frule_tac PolynRg.coeff_0_pol_0[THEN sym, of A B Y "(n, cmp h c)" n], 
        simp+)
 apply (rule allI, rule impI, simp add:cmp_def, simp add:rHom_0_0)
 apply (frule erH_rHom[of A B Y h], assumption+)
 apply (subst pHom_mem[of A B Y "erH R S X A B Y h" n c], assumption+)
 apply (frule PolynRg.pol_expr_unique2[of A B Y 
        "(n, cmp (erH R S X A B Y h) c)" "(n, cmp h c)"],
       simp add:cmp_pol_coeff_e, simp add:cmp_pol_coeff)
 apply (simp, simp,
        thin_tac "(polyn_expr A Y n (n, cmp (erH R S X A B Y h) c) =
        polyn_expr A Y n (n, cmp h c)) =
       (\<forall>j\<le>n. cmp (erH R S X A B Y h) c j = cmp h c j)")
 apply (rule allI, rule impI,
        frule_tac j = j in pol_coeff_mem[of "(n, c)"], simp,
        simp add:cmp_def)
 apply (simp add:erH_rHom_cf)
done

section "Relatively prime polynomials"

definition
  rel_prime_pols :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a,
         'a, 'a ] \<Rightarrow> bool" where
  "rel_prime_pols R S X p q \<longleftrightarrow> (1\<^sub>r\<^bsub>R\<^esub>) \<in> ((Rxa R p) \<minusplus>\<^bsub>R\<^esub> (Rxa R q))"

definition
  div_condn :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a, nat, 
                'a, 'a ] \<Rightarrow> bool" where
  "div_condn R S X n g f \<longleftrightarrow> f \<in> carrier R \<and> n = deg_n R S X f \<longrightarrow>
   (\<exists>q.  q \<in> carrier R \<and> ((f \<plusminus>\<^bsub>R\<^esub> (-\<^sub>a\<^bsub>R\<^esub> (q \<cdot>\<^sub>r\<^bsub>R\<^esub> g)) = \<zero>\<^bsub>R\<^esub>) \<or> (deg_n R S X 
    (f \<plusminus>\<^bsub>R\<^esub> (-\<^sub>a\<^bsub>R\<^esub> (q \<cdot>\<^sub>r\<^bsub>R\<^esub> g))) < deg_n R S X g)))"

lemma (in PolynRg) divisionTr0:"\<lbrakk>Idomain S; p \<in> carrier R; 
       c \<in> carrier S; c \<noteq> \<zero>\<^bsub>S\<^esub>\<rbrakk> \<Longrightarrow> 
                     lcf R S X (c \<cdot>\<^sub>r X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p) = c \<cdot>\<^sub>r\<^bsub>S\<^esub> (lcf R S X p)" 
apply (cut_tac polyn_ring_integral, simp,
       cut_tac subring, frule subring_Ring,
       cut_tac polyn_ring_X_nonzero,
       cut_tac X_mem_R)
apply (frule mem_subring_mem_ring[of S c], assumption+,
      frule npClose[of X n])
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp,
       frule ring_tOp_closed[of c "X^\<^bsup>R n\<^esup>"], assumption+,
       simp add:ring_times_x_0 lcf_val_0,
       simp add:Ring.ring_times_x_0[of S])
apply (frule_tac x = c and y = " X^\<^bsup>R n\<^esup>" in Idomain.idom_tOp_nonzeros[of R],
      assumption+,
      simp add:Subring_zero_ring_zero,
      frule Idomain.idom_potent_nonzero[of R X n], assumption+,
      frule_tac x = c and y = " X^\<^bsup>R n\<^esup>" in ring_tOp_closed, assumption+,
      frule_tac x = "c \<cdot>\<^sub>r X^\<^bsup>R n\<^esup>" and y = p in Idomain.idom_tOp_nonzeros[of R],
      assumption+,
      frule_tac x = "c \<cdot>\<^sub>r X^\<^bsup>R n\<^esup>" and y = p in ring_tOp_closed, assumption+)
apply (simp add:lcf_val) 

apply (frule s_cf_expr[of p], assumption, (erule conjE)+,
       simp add:ring_tOp_assoc[of c _ p],
       frule low_deg_terms_zero1[THEN sym, of "s_cf R S X p" n])
apply (cut_tac a = "X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r 
                    polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p)" and 
               b = "X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p" and 
               c = "polyn_expr R X (fst (s_cf R S X p) + n) 
                     (ext_cf S n (s_cf R S X p))" in box_equation,
       simp, assumption,
   thin_tac "p = polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p)",
   thin_tac "X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p) =
     polyn_expr R X (fst (s_cf R S X p) + n) (ext_cf S n (s_cf R S X p))")
apply (frule ext_cf_pol_coeff[of "s_cf R S X p" n],
       frule scalar_times_pol_expr[of c "ext_cf S n (s_cf R S X p)" 
            "fst (s_cf R S X p) + n"], assumption+,
       simp add:ext_cf_len)
   apply (frule sp_cf_pol_coeff[of "ext_cf S n (s_cf R S X p)" c],
          assumption+,
     cut_tac a = "c \<cdot>\<^sub>r
     polyn_expr R X (fst (s_cf R S X p) + n) (ext_cf S n (s_cf R S X p))"
     and b = "c \<cdot>\<^sub>r (X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p)" and 
         c = "polyn_expr R X (fst (s_cf R S X p) + n)
              (sp_cf S c (ext_cf S n (s_cf R S X p)))" in box_equation,
     simp, simp,
     thin_tac "X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p =
        polyn_expr R X (fst (s_cf R S X p) + n) (ext_cf S n (s_cf R S X p))",
     thin_tac "c \<cdot>\<^sub>r
        polyn_expr R X (fst (s_cf R S X p) + n) (ext_cf S n (s_cf R S X p)) =
        polyn_expr R X (fst (s_cf R S X p) + n)
        (sp_cf S c (ext_cf S n (s_cf R S X p)))")
  apply (frule s_cf_expr[of "c \<cdot>\<^sub>r (X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p)"], assumption+,
         (erule conjE)+,
         drule_tac a = "c \<cdot>\<^sub>r (X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p)" and 
         b = "polyn_expr R X (fst (s_cf R S X (c \<cdot>\<^sub>r (X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p))))
                       (s_cf R S X (c \<cdot>\<^sub>r (X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p)))" and 
         c = "polyn_expr R X (fst (s_cf R S X p) + n)
             (sp_cf S c (ext_cf S n (s_cf R S X p)))" in box_equation,
       assumption,
       thin_tac "c \<cdot>\<^sub>r (X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p) =
          polyn_expr R X (fst (s_cf R S X p) + n)
          (sp_cf S c (ext_cf S n (s_cf R S X p)))",
       frule pol_expr_unique2[of "s_cf R S X (c \<cdot>\<^sub>r (X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p))" 
               "sp_cf S c (ext_cf S n (s_cf R S X p))"], assumption+,
       subst s_cf_deg[THEN sym], assumption+,
        frule_tac Idomain.idom_potent_nonzero[of R X n], assumption+,
        frule_tac x = "X^\<^bsup>R n\<^esup>" and y = p in Idomain.idom_tOp_nonzeros[of R],
        assumption+)
 apply (subst deg_mult_pols, assumption+, simp add:Subring_zero_ring_zero,
        simp add:ring_tOp_closed, assumption+,
        subst deg_mult_pols, assumption+,
        simp add:deg_to_X_d,
        cut_tac pol_of_deg0[THEN sym, of c], simp,
        simp add:sp_cf_len ext_cf_len s_cf_deg, assumption+,
        simp add:Subring_zero_ring_zero,
        simp add:sp_cf_len ext_cf_len)

  apply (subst s_cf_deg[THEN sym], assumption+,
        frule_tac Idomain.idom_potent_nonzero[of R X n], assumption+,
        frule_tac x = "X^\<^bsup>R n\<^esup>" and y = p in Idomain.idom_tOp_nonzeros[of R],
        assumption+,
        simp add:s_cf_deg[THEN sym],
        frule_tac x = "X^\<^bsup>R n\<^esup>" and y = p in ring_tOp_closed, assumption+)
  apply (frule deg_mult_pols[of c "X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p"], assumption+,
        simp add:Subring_zero_ring_zero, assumption+, (erule conjE)+, simp,
        thin_tac "deg_n R S X (c \<cdot>\<^sub>r (X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p)) =
                          deg_n R S X c + deg_n R S X (X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p)",
        cut_tac pol_of_deg0[THEN sym, of c], simp,
        frule deg_mult_pols[of "X^\<^bsup>R n\<^esup>" p], assumption+, (erule conjE)+,
             simp,
      thin_tac "deg_n R S X (X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p) = deg_n R S X (X^\<^bsup>R n\<^esup>) + deg_n R S X p",
      simp add:deg_to_X_d, simp add:add.commute[of n],
      thin_tac "polyn_expr R X (deg_n R S X p + n) 
          (s_cf R S X (c \<cdot>\<^sub>r (X^\<^bsup>R n\<^esup> \<cdot>\<^sub>r p))) = polyn_expr R X (deg_n R S X p + n)
                                      (sp_cf S c (ext_cf S n (s_cf R S X p)))")
  apply (subst sp_cf_def, simp)
  apply (subst ext_cf_def, simp add:sliden_def, assumption)
  apply (simp add:Subring_zero_ring_zero)
done

lemma (in PolynRg) divisionTr1:"\<lbrakk>Corps S; g \<in> carrier R; g \<noteq> \<zero>;
      0 < deg_n R S X g; f \<in> carrier R; f \<noteq> \<zero>; deg_n R S X g \<le> deg_n R S X f\<rbrakk>
      \<Longrightarrow> 
      f \<plusminus> -\<^sub>a ((lcf R S X f) \<cdot>\<^sub>r\<^bsub>S\<^esub> ((lcf R S X g)\<^bsup>\<hyphen> S\<^esup>) \<cdot>\<^sub>r 
                     (X^\<^bsup>R ((deg_n R S X f) - (deg_n R S X g))\<^esup>) \<cdot>\<^sub>r g) = \<zero> \<or> 
      deg_n R S X (f \<plusminus> -\<^sub>a ((lcf R S X f) \<cdot>\<^sub>r\<^bsub>S\<^esub> ((lcf R S X g)\<^bsup>\<hyphen> S\<^esup>) \<cdot>\<^sub>r 
                 (X^\<^bsup>R ((deg_n R S X f) - (deg_n R S X g))\<^esup>) \<cdot>\<^sub>r g)) < deg_n R S X f"
apply (cut_tac ring_is_ag,
       cut_tac subring, 
       frule Corps.field_is_idom[of "S"],
       frule subring_Ring,
       cut_tac subring,
       cut_tac polyn_ring_X_nonzero,
       cut_tac X_mem_R,
       cut_tac polyn_ring_integral, simp)
apply (frule npClose[of X "deg_n R S X f - deg_n R S X g"],
       frule_tac Idomain.idom_potent_nonzero[of R X 
                "fst (s_cf R S X f) - fst (s_cf R S X g)"], assumption+,
       frule s_cf_expr[of f], assumption+, (erule conjE)+,
       frule s_cf_expr[of g], assumption+, (erule conjE)+,
       simp add:s_cf_deg, simp add:lcf_val[THEN sym],
       frule Corps.invf_closed1[of S "lcf R S X g"], simp, simp add:lcf_mem,
       frule lcf_mem[of f], simp,
       frule subring_Ring, frule Ring.ring_is_ag[of S], (erule conjE)+,
       frule_tac x = "lcf R S X f" and y = "lcf R S X g\<^bsup>\<hyphen> S\<^esup>" in 
                 Ring.ring_tOp_closed[of S], assumption+,
       frule mem_subring_mem_ring[of S " lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> "],
         assumption+,
       frule_tac x = "lcf R S X f" and y = "lcf R S X g\<^bsup>\<hyphen> S\<^esup>" in 
         Idomain.idom_tOp_nonzeros[of S], assumption+,
       simp add:Subring_zero_ring_zero)
apply(frule_tac x = "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup>" and 
       y = "X^\<^bsup>R (fst (s_cf R S X f) - fst (s_cf R S X g))\<^esup>" in 
      Idomain.idom_tOp_nonzeros[of R], assumption+,
      frule_tac x = "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup>" and 
       y = "X^\<^bsup>R (fst (s_cf R S X f) - fst (s_cf R S X g))\<^esup>" in ring_tOp_closed, 
      assumption+,
      frule_tac x = "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r 
       X^\<^bsup>R (fst (s_cf R S X f) - fst (s_cf R S X g))\<^esup>" and y = g in 
        Idomain.idom_tOp_nonzeros[of R], assumption+,
      frule_tac x = "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r 
       X^\<^bsup>R (fst (s_cf R S X f) - fst (s_cf R S X g))\<^esup>" and y = g in ring_tOp_closed,
      assumption+)

apply (frule pol_diff_deg_less[of f "s_cf R S X f" 
       "s_cf R S X (lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r 
                 X^\<^bsup>R (fst (s_cf R S X f) - fst (s_cf R S X g))\<^esup> \<cdot>\<^sub>r g)"], assumption+,
       simp add:s_cf_pol_coeff)
 apply (simp add:s_cf_deg[THEN sym])
   apply (frule deg_mult_pols[of "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> (lcf R S X g)\<^bsup>\<hyphen> S\<^esup>" 
                   "(X^\<^bsup>R (deg_n R S X f - deg_n R S X g)\<^esup> )\<cdot>\<^sub>r g"], assumption+,
          rule ring_tOp_closed, assumption+,
          rule Idomain.idom_tOp_nonzeros[of R], assumption+,
          (erule conjE)+, 
          subst ring_tOp_assoc[of "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup>" _ g],
                 assumption+, simp,
          cut_tac pol_of_deg0[THEN sym, of "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup>"], 
          simp,
          thin_tac "deg_n R S X (lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r
              (X^\<^bsup>R (deg_n R S X f - deg_n R S X g)\<^esup> \<cdot>\<^sub>r g)) =
               deg_n R S X (X^\<^bsup>R (deg_n R S X f - deg_n R S X g)\<^esup> \<cdot>\<^sub>r g)")
   apply (frule deg_mult_pols[of "(X^\<^bsup>R (deg_n R S X f - deg_n R S X g)\<^esup> )" g], 
          assumption+, simp,
          simp add:deg_to_X_d, assumption+,
          fold lcf_def,
          subst divisionTr0[of g "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup>" 
                        "fst (s_cf R S X f) - fst (s_cf R S X g)"],
          assumption+, simp add:Subring_zero_ring_zero)
   apply (subst Ring.ring_tOp_assoc, assumption+, simp add:lcf_mem,
          frule Corps.invf_inv[of S "lcf R S X g"], simp add:lcf_mem,
          simp add:Subring_zero_ring_zero, simp add:Ring.ring_r_one,
          frule s_cf_expr[of "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r
               X^\<^bsup>R (fst (s_cf R S X f) - fst (s_cf R S X g))\<^esup> \<cdot>\<^sub>r g"],
          rule  Idomain.idom_tOp_nonzeros[of R], assumption+) 
 apply ((erule conjE)+,
        thin_tac "snd (s_cf R S X
           (lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r
            X^\<^bsup>R (fst (s_cf R S X f) - fst (s_cf R S X g))\<^esup> \<cdot>\<^sub>r  g))
           (fst (s_cf R S X (lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r
              X^\<^bsup>R (fst (s_cf R S X f) - fst (s_cf R S X g))\<^esup> \<cdot>\<^sub>r g))) \<noteq> \<zero>\<^bsub>S\<^esub>")
  apply (rotate_tac -1, drule sym, simp)
done
 
lemma (in PolynRg) divisionTr2:"\<lbrakk>Corps S; g \<in> carrier R; g \<noteq> \<zero>; 
                   0 < deg_n R S X g\<rbrakk>  \<Longrightarrow>  \<forall>f. div_condn R S X n g f"
apply (cut_tac ring_is_ag,
       frule Corps.field_is_idom[of "S"],
       cut_tac subring, frule subring_Ring,
       cut_tac polyn_ring_integral, simp,
       cut_tac X_mem_R)

apply (rule nat_less_induct)
apply (rule allI)
apply (subst div_condn_def, rule impI, (erule conjE)+)
apply (case_tac "f = \<zero>\<^bsub>R\<^esub>",
       cut_tac ring_zero,
       subgoal_tac " f \<plusminus> -\<^sub>a (\<zero> \<cdot>\<^sub>r g) = \<zero>",
       blast,
       simp add:ring_times_0_x, simp add:aGroup.ag_inv_zero[of "R"],
       simp add:aGroup.ag_r_zero) 
apply (case_tac "n < deg_n R S X g")
 apply (cut_tac ring_zero,
        subgoal_tac "deg_n R S X (f \<plusminus> -\<^sub>a (\<zero> \<cdot>\<^sub>r g)) < deg_n R S X g", 
        blast) apply ( 
       simp add:ring_times_0_x, simp add:aGroup.ag_inv_zero,
       simp add:aGroup.ag_r_zero)
apply (frule_tac x = n and y = "deg_n R S X g" in leI,
       thin_tac "\<not> n < deg_n R S X g")
   (** deg_n R S X g \<le> deg_n R S X f **)
apply (frule_tac f = f in divisionTr1[of g], assumption+, simp)
apply (frule_tac p = f in lcf_mem,
       frule lcf_mem[of g],
       frule lcf_nonzero[of g], assumption+,
       frule Corps.invf_closed1[of S "lcf R S X g"], simp)
apply (frule_tac x = "lcf R S X f" and y = "lcf R S X g\<^bsup>\<hyphen> S\<^esup>" in 
                 Ring.ring_tOp_closed[of S], assumption+, simp)
 apply (frule_tac x = "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup>" in mem_subring_mem_ring,
        assumption) 
 apply (frule_tac n = "deg_n R S X f - deg_n R S X g" in npClose[of X],
        frule_tac x = "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup>" and 
                  y = "X^\<^bsup>R (deg_n R S X f - deg_n R S X g)\<^esup>" in 
                  ring_tOp_closed, assumption+,
        frule_tac x = "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r 
                       X^\<^bsup>R (deg_n R S X f - deg_n R S X g)\<^esup>"  and 
                  y = g in ring_tOp_closed, assumption+)
 apply (erule disjE, blast)
 apply (drule_tac a = "deg_n R S X (f \<plusminus> -\<^sub>a (lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> 
          lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r X^\<^bsup>R (deg_n R S X f - deg_n R S X g)\<^esup> \<cdot>\<^sub>r g))" in
          forall_spec, simp)
 apply (simp add:div_condn_def)
 apply (drule_tac x = "f \<plusminus>
             -\<^sub>a (lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r
                 X^\<^bsup>R (deg_n R S X f - deg_n R S X g)\<^esup> \<cdot>\<^sub>r
                 g)" in spec)
 apply (frule_tac x = "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r
           X^\<^bsup>R (deg_n R S X f - deg_n R S X g)\<^esup> \<cdot>\<^sub>r g" in aGroup.ag_mOp_closed,
           assumption)
 apply (frule_tac x = f and y = "-\<^sub>a (lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r
               X^\<^bsup>R (deg_n R S X f - deg_n R S X g)\<^esup> \<cdot>\<^sub>r g)" in 
        aGroup.ag_pOp_closed, assumption+, simp,
        thin_tac "deg_n R S X (f \<plusminus>  -\<^sub>a (lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r
                 X^\<^bsup>R (deg_n R S X f - deg_n R S X g)\<^esup> \<cdot>\<^sub>r g)) < deg_n R S X f")
 apply (erule exE,
        thin_tac "f \<plusminus> -\<^sub>a (lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r
            X^\<^bsup>R (deg_n R S X f - deg_n R S X g)\<^esup> \<cdot>\<^sub>r g) \<in> carrier R")
 apply ((erule conjE)+,
        frule_tac x = q and y = g in ring_tOp_closed, assumption+,
        frule_tac x = "q \<cdot>\<^sub>r g" in aGroup.ag_mOp_closed, assumption+,
        simp add:aGroup.ag_pOp_assoc,
        simp add:aGroup.ag_p_inv[THEN sym],
        simp add:ring_distrib2[THEN sym])
 apply (frule_tac x = "lcf R S X f \<cdot>\<^sub>r\<^bsub>S\<^esub> lcf R S X g\<^bsup>\<hyphen> S\<^esup> \<cdot>\<^sub>r
         X^\<^bsup>R (deg_n R S X f - deg_n R S X g)\<^esup>" and y = q in 
                          aGroup.ag_pOp_closed, assumption+)
 apply (erule disjE) 
 apply blast 
 apply blast
done

lemma (in PolynRg) divisionTr3:"\<lbrakk>Corps S; g \<in> carrier R; g \<noteq> \<zero>; 
      0 < deg_n R S X g; f \<in> carrier R\<rbrakk> \<Longrightarrow>  
     \<exists>q\<in>carrier R. (f \<plusminus> -\<^sub>a (q \<cdot>\<^sub>r  g) = \<zero>) \<or> ( f \<plusminus> -\<^sub>a (q \<cdot>\<^sub>r g) \<noteq> \<zero> \<and>
      deg_n R S X (f \<plusminus> -\<^sub>a (q \<cdot>\<^sub>r g)) < (deg_n R S X g))"
apply (frule divisionTr2[of g "deg_n R S X f"], assumption+) 
 apply (drule_tac x = f in spec)
apply (simp add:div_condn_def, blast) 
done

lemma (in PolynRg) divisionTr4:"\<lbrakk>Corps S; g \<in> carrier R; g \<noteq> \<zero>; 
       0 < deg_n R S X g; f \<in> carrier R\<rbrakk> \<Longrightarrow>  
   \<exists>q\<in>carrier R. (f = q \<cdot>\<^sub>r g) \<or> (\<exists>r\<in>carrier R. r \<noteq> \<zero> \<and> (f = (q \<cdot>\<^sub>r g) \<plusminus> r)
     \<and> (deg_n R S X r) < (deg_n R S X g))"
apply (cut_tac is_Ring,
       cut_tac ring_is_ag)
apply (frule divisionTr3[of g f], assumption+,
       erule bexE,
       frule_tac x = q in ring_tOp_closed[of  _ g], assumption+,
       erule disjE) 
apply (simp add:aGroup.ag_eq_diffzero[THEN sym, of "R" "f"], blast)
apply (subgoal_tac "f = q \<cdot>\<^sub>r g \<plusminus> (f \<plusminus> -\<^sub>a (q \<cdot>\<^sub>r g))",
       subgoal_tac "(f \<plusminus> -\<^sub>a (q \<cdot>\<^sub>r g)) \<in> carrier R", blast,
       rule aGroup.ag_pOp_closed, assumption+,
       rule aGroup.ag_mOp_closed, assumption+)
apply (frule_tac x = "q \<cdot>\<^sub>r g" in aGroup.ag_mOp_closed, assumption+,
       subst aGroup.ag_pOp_assoc[THEN sym], assumption+,
       subst aGroup.ag_pOp_commute[of R _ f], assumption+,
       subst aGroup.ag_pOp_assoc, assumption+,
              simp add:aGroup.ag_r_inv1, simp add:aGroup.ag_r_zero)
done

lemma (in PolynRg) divisionTr:"\<lbrakk>Corps S; g \<in> carrier R; 0 < deg R S X g; 
       f \<in> carrier R\<rbrakk> \<Longrightarrow> 
       \<exists>q\<in>carrier R. (\<exists>r\<in>carrier R. (f = (q \<cdot>\<^sub>r g) \<plusminus> r) \<and> 
                                  (deg R S X r) < (deg R S X g))"
apply (subgoal_tac "g \<noteq> \<zero>",
       frule divisionTr4[of g f], assumption+,
       simp add:deg_def, simp only:an_0[THEN sym],
       cut_tac aless_nat_less[of "0" "deg_n R S X g"],  simp, assumption)
apply (erule bexE, erule disjE,
       cut_tac ring_is_ag, frule aGroup.ag_r_zero[of "R" "f"], simp, simp,
       rotate_tac -1, frule sym,
       cut_tac ring_zero,
       subgoal_tac "deg R S X \<zero> < deg R S X g", blast,
       simp add:deg_def an_def)
apply (erule bexE, (erule conjE)+,
       cut_tac n1 = "deg_n R S X r" and m1 = "deg_n R S X g" in 
       aless_natless[THEN sym], simp add:deg_def,
       drule sym, simp, rotate_tac -1, drule sym, blast)
apply (rule contrapos_pp, simp+,
       simp add:deg_def, frule aless_imp_le[of "0" "-\<infinity>"],
       cut_tac minf_le_any[of "0"]) 
 apply (frule ale_antisym[of "0" "-\<infinity>"], assumption)
 apply simp
done

lemma (in PolynRg) rel_prime_equation:"\<lbrakk>Corps S; f \<in> carrier R; g \<in> carrier R;
      0 < deg R S X f; 0 < deg R S X g; rel_prime_pols R S X f g;
      h \<in> carrier R\<rbrakk> \<Longrightarrow> 
     \<exists>u \<in> carrier R. \<exists>v \<in> carrier R.
     (deg R S X u \<le> amax ((deg R S X h) - (deg R S X f)) (deg R S X g)) \<and>
     (deg R S X v \<le> (deg R S X f)) \<and> (u \<cdot>\<^sub>r f \<plusminus> (v \<cdot>\<^sub>r g) = h)"
apply (cut_tac ring_is_ag,
       cut_tac ring_zero, cut_tac subring, frule subring_Ring,
       frule aless_imp_le [of "0" "deg R S X f"],
       frule  pol_nonzero[of f], simp,
       frule aless_imp_le [of "0" "deg R S X g"], 
       frule  pol_nonzero[of g], simp,
       frule Corps.field_is_idom[of "S"],
       cut_tac polyn_ring_integral, simp,
       frule Idomain.idom_tOp_nonzeros[of R f g], assumption+) 
apply (case_tac "h = \<zero>\<^bsub>R\<^esub>")
 apply (cut_tac ring_is_ag,
        cut_tac ring_zero,
        subgoal_tac "deg R S X \<zero> \<le> 
                      amax (deg R S X h - deg R S X f) (deg R S X g)",
        subgoal_tac "deg R S X \<zero> \<le> deg R S X f \<and> 
                     \<zero> \<cdot>\<^sub>r f \<plusminus> \<zero> \<cdot>\<^sub>r g = h", blast)
  apply (simp add:ring_times_0_x, simp add:aGroup.ag_r_zero,
        simp add:deg_def)
  apply (simp add:deg_def amax_def)

apply (simp add:rel_prime_pols_def,
       frule principal_ideal[of f], frule principal_ideal[of g],
       frule ideals_set_sum[of "R \<diamondsuit>\<^sub>p f" "R \<diamondsuit>\<^sub>p g" "1\<^sub>r"], assumption+,
       thin_tac "1\<^sub>r \<in> R \<diamondsuit>\<^sub>p f \<minusplus> R \<diamondsuit>\<^sub>p g",
       (erule bexE)+,
       thin_tac "ideal R (R \<diamondsuit>\<^sub>p f)", thin_tac "ideal R (R \<diamondsuit>\<^sub>p g)",
       simp add:Rxa_def, (erule bexE)+, simp,
       thin_tac "ha = r \<cdot>\<^sub>r f", thin_tac "k = ra \<cdot>\<^sub>r g")
apply (frule_tac x = r in ring_tOp_closed[of _ f], assumption+,
       frule_tac x = ra in ring_tOp_closed[of _ g], assumption+,
       frule_tac y1 = "r \<cdot>\<^sub>r f" and z1 = "ra \<cdot>\<^sub>r g" in ring_distrib1[THEN sym, 
       of "h"], assumption+, simp add:ring_r_one, drule sym,
       simp,
       thin_tac "r \<cdot>\<^sub>r f \<plusminus> ra \<cdot>\<^sub>r g = 1\<^sub>r",
       simp add:ring_tOp_assoc[THEN sym], simp add:ring_r_one)
apply (frule_tac f = "h \<cdot>\<^sub>r r" in divisionTr[of g], assumption+,
       simp add:ring_tOp_closed,
       frule_tac f = "h \<cdot>\<^sub>r ra" in divisionTr[of f], assumption+,
       simp add:ring_tOp_closed,
       (erule bexE)+, (erule conjE)+) 
(** final **) 
apply (thin_tac " r \<in> carrier R",
       thin_tac "ra \<in> carrier R",
       thin_tac "r \<cdot>\<^sub>r f \<in> carrier R",
       thin_tac "ra \<cdot>\<^sub>r g \<in> carrier R")
apply (frule_tac x = q in ring_tOp_closed[of _ g], assumption+,
       frule_tac x = qa in ring_tOp_closed[of _ f], assumption+,
       frule_tac x = "q \<cdot>\<^sub>r g" and y = rb in aGroup.ag_pOp_commute, assumption+,
       simp, 
       thin_tac "q \<cdot>\<^sub>r g \<plusminus> rb = rb \<plusminus> q \<cdot>\<^sub>r g",
       thin_tac  "h \<cdot>\<^sub>r r =  rb \<plusminus> q \<cdot>\<^sub>r g",
       thin_tac "h \<cdot>\<^sub>r ra =  qa \<cdot>\<^sub>r f \<plusminus> rc")
apply (simp add:ring_distrib2[of g],
     frule_tac x = rb and y = "q \<cdot>\<^sub>r g" in aGroup.ag_pOp_closed[of R], 
       assumption+,
     frule_tac x = "rb \<plusminus> q \<cdot>\<^sub>r g" and y = f in ring_tOp_closed, 
      assumption+,
     frule_tac x = "qa \<cdot>\<^sub>r f" and y = g in ring_tOp_closed, assumption+,
     frule_tac x = rc and y = g in ring_tOp_closed, assumption+,
     simp add:aGroup.ag_pOp_assoc[THEN sym, of "R"],
     simp add:ring_tOp_assoc[of _ f g],
     simp add:ring_tOp_commute[of f g],
     simp add:ring_tOp_assoc[THEN sym, of  _ g f],
     frule_tac x = qa and y = g in ring_tOp_closed, assumption+,
     simp add:ring_distrib2[THEN sym],
     simp add:aGroup.ag_pOp_assoc,
     simp add:ring_distrib2[THEN sym],
     case_tac "q \<plusminus>\<^bsub>R\<^esub> qa = \<zero>\<^bsub>R\<^esub>", simp add:ring_times_0_x,
          simp add:aGroup.ag_r_zero,
     subgoal_tac "deg R S X rb \<le> 
                         amax (deg R S X h - deg R S X f) (deg R S X g)",
            subgoal_tac "deg R S X rc \<le> deg R S X f",
            blast,
        simp add:aless_imp_le,
        frule_tac x = "deg R S X rb" and y = "deg R S X g" in
           aless_imp_le,
        rule_tac i = "deg R S X rb" in ale_trans[of _ "deg R S X g" 
          "amax (deg R S X h - deg R S X f) (deg R S X g)"], assumption,
           simp add:amax_def, simp add:aneg_le aless_imp_le)
apply (subgoal_tac "rb \<plusminus> (q \<plusminus> qa) \<cdot>\<^sub>r g \<in> carrier R",
       subgoal_tac "deg R S X (rb \<plusminus> (q \<plusminus> qa) \<cdot>\<^sub>r g) \<le> 
                    amax (deg R S X h - deg R S X f) (deg R S X g)",
       subgoal_tac "deg R S X rc \<le> deg R S X f",  blast,
     simp add:aless_imp_le,
     frule_tac x = q and y = qa in aGroup.ag_pOp_closed[of "R"], assumption+,
     frule_tac p = rb and q = "(q \<plusminus> qa) \<cdot>\<^sub>r g" in deg_pols_add1,
     rule ring_tOp_closed, assumption+, simp add:deg_mult_pols1,
     frule_tac p1 = "q \<plusminus> qa" in pol_nonzero[THEN sym], simp)

apply (frule_tac y = "deg R S X (q \<plusminus> qa)" and z = "deg R S X rb" in 
                                   aadd_le_mono[of "0"], simp add:aadd_0_l)
apply (frule_tac p = "q \<plusminus> qa" in deg_ant_int, assumption+,
       frule_tac x = "deg R S X rb" and y = "deg R S X g" and 
                 z = "int (deg_n R S X ( q \<plusminus> qa))" in aadd_less_mono_z,
       simp add:aadd_commute)

apply (simp add:deg_mult_pols1,
       frule_tac p = "rb \<plusminus> (q \<plusminus> qa) \<cdot>\<^sub>r g" and q = f in 
            deg_mult_pols1, assumption+, simp,
       thin_tac "deg R S X (rb \<plusminus> (q \<plusminus> qa) \<cdot>\<^sub>r g) = 
                       deg R S X (q \<plusminus> qa) + deg R S X g",
       frule_tac x = "rb \<plusminus> (q \<plusminus> qa) \<cdot>\<^sub>r g" and y = f in 
       ring_tOp_closed,  assumption+, simp only:aGroup.ag_pOp_commute,
       frule_tac p = "rc \<cdot>\<^sub>r g" and q = "(rb \<plusminus> (q \<plusminus> qa) \<cdot>\<^sub>r g) \<cdot>\<^sub>r f" in 
        deg_pols_add1, assumption+, simp,
       thin_tac "deg R S X ((rb \<plusminus> (q \<plusminus> qa) \<cdot>\<^sub>r g) \<cdot>\<^sub>r f) =
        deg R S X (q \<plusminus> qa) + deg R S X g + deg R S X f")
apply (simp add:deg_mult_pols1,
       frule_tac p1 = "q \<plusminus> qa" in pol_nonzero[THEN sym], simp,
       simp add:deg_ant_int[of g])
apply (frule_tac x = "deg R S X rc" and y = "deg R S X f" and 
        z = "int (deg_n R S X g)" in aadd_less_mono_z,
       frule_tac a = "deg R S X ( q \<plusminus> qa)" in aadd_pos_le[of _ 
                   "deg R S X f + ant (int (deg_n R S X g))"],
       frule_tac x = "deg R S X rc + ant (int (deg_n R S X g))" and 
        y = "deg R S X f + ant (int (deg_n R S X g))" and 
        z = "deg R S X ( q \<plusminus> qa) + (deg R S X f + ant (int (deg_n R S X g)))" 
       in aless_le_trans, assumption+,
       thin_tac "deg R S X rc + ant (int (deg_n R S X g))
                       < deg R S X f + ant (int (deg_n R S X g))",
       thin_tac "deg R S X f + ant (int (deg_n R S X g))
           \<le> deg R S X ( q \<plusminus> qa) + (deg R S X f + ant (int (deg_n R S X g)))")
apply (simp add:deg_ant_int[THEN sym])
 apply (frule_tac p = "q \<plusminus> qa" in deg_in_aug_minf,
        frule_tac p = "g" in deg_in_aug_minf, 
        frule_tac p = "f" in deg_in_aug_minf, 
        simp add:aadd_commute[of "deg R S X f" "deg R S X g"],
        simp only:aadd_assoc_m[THEN sym], simp)
 apply (frule_tac p = "g" in deg_in_aug_minf,
        frule_tac p = "f" in deg_in_aug_minf,
        frule_tac p = "q \<plusminus> qa" in deg_in_aug_minf,
        simp add:diff_ant_def,
        subgoal_tac "-(deg R S X f) \<in> Z\<^sub>-\<^sub>\<infinity>") 
apply (subst aadd_assoc_m[of _ "deg R S X f" "- deg R S X f"],
       simp add:Zminf_pOp_closed, assumption+,
       (simp add:aadd_minus_r, simp add:aadd_0_r), simp add:amax_ge_l,
       simp add:deg_ant_int, simp add:aminus, simp add:z_in_aug_minf)
 apply (rule aGroup.ag_pOp_closed, assumption+,
        rule ring_tOp_closed,
        rule aGroup.ag_pOp_closed, assumption+)
done 

subsection "Polynomial, coeff mod P"

definition
  P_mod :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme, 'a, 'a set,
          'a] \<Rightarrow> bool" where
  "P_mod R S X P p \<longleftrightarrow> p = \<zero>\<^bsub>R\<^esub> \<or> 
     (\<forall>j \<le> (fst (s_cf R S X p)). (snd (s_cf R S X p) j) \<in> P)"

lemma (in PolynRg) P_mod_whole:"p \<in> carrier R \<Longrightarrow>
                         P_mod R S X (carrier S) p"
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp add:P_mod_def)
apply (simp add:P_mod_def,
       rule allI, rule impI,
       rule pol_coeff_mem,
       simp add:s_cf_pol_coeff,
       assumption)
done

lemma (in PolynRg) zero_P_mod:"ideal S I \<Longrightarrow> P_mod R S X I \<zero>" 
by (simp add:P_mod_def)

lemma (in PolynRg) P_mod_mod:"\<lbrakk>ideal S I; p \<in> carrier R; pol_coeff S c;
                     p = polyn_expr R X (fst c) c\<rbrakk> \<Longrightarrow> 
                     (\<forall>j \<le> (fst c). (snd c) j \<in> I) = (P_mod R S X I p)"
apply (cut_tac subring, frule subring_Ring)
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>")
   apply (simp add:P_mod_def,
          drule sym,
          frule coeff_0_pol_0[THEN sym, of c "fst c"], simp, simp)
   apply (rule impI,
          simp add:Ring.ideal_zero)

apply (frule s_cf_expr[of p],
       simp add:P_mod_def, (erule conjE)+)
apply (frule polyn_c_max[of c])
 apply (frule coeff_nonzero_polyn_nonzero[of c "fst c"], simp)
 apply (frule coeff_max_nonzeroTr[of c], simp)
 apply (thin_tac "(polyn_expr R X (fst c) c \<noteq> \<zero>) = (\<exists>j\<le>fst c. snd c j \<noteq> \<zero>\<^bsub>S\<^esub>)")
 apply (frule coeff_max_bddTr[of c])
 apply (frule polyn_expr_short[of c "c_max S c"], assumption+)
 apply (frule pol_expr_unique[of p "(c_max S c, snd c)" "s_cf R S X p"],
        assumption+, rule split_pol_coeff[of c], assumption+,
        simp, simp, assumption+)
 
 apply (thin_tac "p = polyn_expr R X (fst c) c",
        thin_tac "p = polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p)",
        thin_tac "polyn_expr R X (fst c) c = polyn_expr R X (c_max S c) c",
        thin_tac "polyn_expr R X (c_max S c) c =
                      polyn_expr R X (c_max S c) (c_max S c, snd c)")
 apply (frule coeff_max_zeroTr[of c], (erule conjE)+)
 apply (subst P_mod_def, simp)
 apply (rule iffI, rule allI, rule impI)
 apply (rotate_tac 10,
        drule_tac a = j in forall_spec,
        drule_tac x = j in spec, assumption,
        frule_tac i = j and j = "fst (s_cf R S X p)" and k = "fst c" in 
                  le_trans, assumption+, 
        drule_tac a = j in forall_spec, assumption, simp)
 
 apply (rule allI, rule impI)
 apply (case_tac "fst (s_cf R S X p) < j", 
        drule_tac a = j in forall_spec, simp,
        simp add:Ring.ideal_zero,
        frule_tac x = "fst (s_cf R S X p)" and y = j in leI,
        thin_tac "\<forall>j. j \<le> fst c \<and> fst (s_cf R S X p) < j \<longrightarrow> snd c j = \<zero>\<^bsub>S\<^esub>",
        drule_tac a = j in forall_spec, assumption,
        drule_tac a = j in forall_spec, assumption, simp)
done

lemma (in PolynRg) monomial_P_mod_mod:"\<lbrakk>ideal S I; c \<in> carrier S; 
       p = c \<cdot>\<^sub>r (X^\<^bsup>R d\<^esup>)\<rbrakk> \<Longrightarrow>  (c \<in> I) = (P_mod R S X I p)"
apply (cut_tac subring, frule subring_Ring)
apply (cut_tac monomial_d[THEN sym, of "(0, \<lambda>j. c)" "d"], simp)
apply (drule sym, simp)
apply (subst P_mod_mod[THEN sym, of I p "ext_cf S d (0, \<lambda>j. c)"],
       assumption+)
   apply (frule mem_subring_mem_ring[of S c], assumption,
          cut_tac X_mem_R, 
          frule npClose[of X d], drule sym, simp add:ring_tOp_closed)
   apply (simp add:pol_coeff_def, rule allI, rule impI, 
       simp add:ext_cf_def sliden_def, rule impI, simp add:Ring.ring_zero,
       subst ext_cf_len, simp add:pol_coeff_def,
       simp)
   apply (subst ext_cf_len, simp add:pol_coeff_def,
          simp add:ext_cf_def)
apply (rule iffI)
   apply (simp add:Ring.ideal_zero,
          drule_tac x = d in spec,
          simp, simp add:pol_coeff_def)
done

lemma (in PolynRg) P_mod_add:"\<lbrakk>ideal S I; p \<in> carrier R;
      q \<in> carrier R; P_mod R S X I p; P_mod R S X I q\<rbrakk> \<Longrightarrow> 
               P_mod R S X I (p \<plusminus> q)"
apply (cut_tac subring,
       frule subring_Ring,
       cut_tac ring_is_ag)

apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp add:aGroup.ag_l_zero,
       case_tac "q = \<zero>\<^bsub>R\<^esub>", simp add:aGroup.ag_r_zero)
apply (case_tac "p \<plusminus>\<^bsub>R\<^esub> q = \<zero>\<^bsub>R\<^esub>", simp add:P_mod_def)

apply (frule s_cf_expr[of p], assumption,
       frule s_cf_expr[of q], assumption, (erule conjE)+)
apply (frule polyn_add1[of "s_cf R S X p" "s_cf R S X q"], assumption+,
       drule sym, drule sym, simp, drule sym, simp,
       rotate_tac -1, drule sym)
apply (frule P_mod_mod[THEN sym, of I p "s_cf R S X p"], assumption+, simp,
       thin_tac "polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p) = p",
       frule P_mod_mod[THEN sym, of I q "s_cf R S X q"], assumption+, simp,
       thin_tac "polyn_expr R X (fst (s_cf R S X q)) (s_cf R S X q) = q")
apply (frule aGroup.ag_pOp_closed[of R p q], assumption+)  
apply (subst P_mod_mod[THEN sym, of I "p \<plusminus> q" 
             "add_cf S (s_cf R S X p) (s_cf R S X q)"], assumption+,
       simp add:add_cf_pol_coeff, simp, simp add:add_cf_len,
       thin_tac "p \<plusminus> q =
         polyn_expr R X (max (fst (s_cf R S X p)) (fst (s_cf R S X q)))
         (add_cf S (s_cf R S X p) (s_cf R S X q))")
       apply simp
apply (subst add_cf_len, assumption+)
apply (rule allI, rule impI)

apply (cut_tac x = "fst (s_cf R S X p)" and y = "fst (s_cf R S X q)" in 
       less_linear)
apply (erule disjE)
 apply (simp, subst add_cf_def, simp,
       (rule impI, 
        drule_tac a = j in forall_spec, assumption,
        drule_tac x = j in spec,
        frule_tac x = j and y = "fst (s_cf R S X p)" and 
           z = "fst (s_cf R S X q)" in le_less_trans, assumption+,
        frule_tac x = j and y = "fst (s_cf R S X q)" in less_imp_le, simp))
        apply (rule Ring.ideal_pOp_closed[of S I], assumption+)
apply (erule disjE)
 apply (simp, subst add_cf_def, simp,
        drule_tac a = j in forall_spec, assumption,
        drule_tac a = j in forall_spec, assumption)
        apply (rule Ring.ideal_pOp_closed[of S I], assumption+)

 apply (simp add: max.absorb1 max.absorb2, subst add_cf_def, simp, rule impI,
        drule_tac x = j in spec, 
        drule_tac a = j in forall_spec, assumption,
        frule_tac x = j and y = "fst (s_cf R S X q)" and 
           z = "fst (s_cf R S X p)" in le_less_trans, assumption+,
        frule_tac x = j and y = "fst (s_cf R S X p)" in less_imp_le, simp)
        apply (rule Ring.ideal_pOp_closed[of S I], assumption+)
done

lemma (in PolynRg) P_mod_minus:"\<lbrakk>ideal S I; p \<in> carrier R; P_mod R S X I p\<rbrakk> \<Longrightarrow>
                  P_mod R S X I (-\<^sub>a p)" 
apply (cut_tac ring_is_ag,
       cut_tac subring,
       frule subring_Ring)
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp add:aGroup.ag_inv_zero)

apply (frule s_cf_expr[of p], assumption+, (erule conjE)+,
       frule polyn_minus_m_cf[of "s_cf R S X p" "fst (s_cf R S X p)"],
       simp,
       frule aGroup.ag_inv_inj[of R p \<zero>], assumption,
       simp add:ring_zero, assumption, simp add:aGroup.ag_inv_zero,
       frule m_cf_pol_coeff[of "s_cf R S X p"],
       drule sym, drule sym, simp)
apply (subst P_mod_mod[THEN sym, of I "-\<^sub>a p" "m_cf S (s_cf R S X p)"],
        assumption+,
      rule aGroup.ag_mOp_closed[of R p], assumption+,
      simp add:m_cf_len,
      thin_tac "polyn_expr R X (fst (s_cf R S X p)) 
                                 (m_cf S (s_cf R S X p)) = -\<^sub>a p")
apply (frule P_mod_mod[THEN sym, of I p "s_cf R S X p"], assumption+, simp,
       thin_tac "polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p) = p",
       simp)
apply (rule allI, rule impI,
       drule_tac a = j in forall_spec, simp add:m_cf_len,
       subst m_cf_def, simp,
       rule Ring.ideal_inv1_closed[of S I], assumption+)
done

lemma (in PolynRg) P_mod_pre:"\<lbrakk>ideal S I; pol_coeff S ((Suc n), f); 
       P_mod R S X I (polyn_expr R X (Suc n) (Suc n, f))\<rbrakk> \<Longrightarrow>
       P_mod R S X I (polyn_expr R X n (n, f))" 
apply (frule pol_coeff_pre[of n f],
       frule polyn_mem[of "(n, f)" n],simp,
       frule polyn_mem[of "(Suc n, f)" "Suc n"], simp)
apply (case_tac "polyn_expr R X n (n, f) = \<zero>\<^bsub>R\<^esub>", simp add:P_mod_def)
apply (subst P_mod_mod[THEN sym, of I 
                  "polyn_expr R X n (n, f)" "(n, f)"], assumption+, simp,
       frule P_mod_mod[THEN sym, of I "polyn_expr R X (Suc n) (Suc n, f)"
               "(Suc n, f)"], assumption+, simp, simp)
done

lemma (in PolynRg) P_mod_pre1:"\<lbrakk>ideal S I; pol_coeff S ((Suc n), f); 
       P_mod R S X I (polyn_expr R X (Suc n) (Suc n, f))\<rbrakk> \<Longrightarrow>
       P_mod R S X I (polyn_expr R X n (Suc n, f))" 
by (simp add:polyn_expr_restrict[of n f], simp add:P_mod_pre)

lemma (in PolynRg) P_mod_coeffTr:"\<lbrakk>ideal S I; d \<in> carrier S\<rbrakk> \<Longrightarrow> 
                   (P_mod R S X I d) = (d \<in> I)"
apply (cut_tac subring, frule subring_Ring,
       subst monomial_P_mod_mod[of I d "d \<cdot>\<^sub>r X^\<^bsup>R 0\<^esup>" 0], assumption+,
       simp, simp,
       frule mem_subring_mem_ring[of _ d], assumption+,
       simp add:ring_r_one)
done 

lemma (in PolynRg) P_mod_mult_const:"\<lbrakk>ideal S I; ideal S J; 
     pol_coeff S (n, f); P_mod R S X I (polyn_expr R X n (n, f));
     pol_coeff S (0, g); P_mod R S X J (polyn_expr R X 0 (0, g))\<rbrakk> \<Longrightarrow> 
       P_mod R S X (I \<diamondsuit>\<^sub>r\<^bsub>S\<^esub> J) ((polyn_expr R X n (n, f)) \<cdot>\<^sub>r 
                                        (polyn_expr R X 0 (0, g)))"
apply (cut_tac subring, frule subring_Ring) 
apply (frule_tac c = "(n, f)" in polyn_mem[of _ n], simp)
 apply (frule Ring.ideal_prod_ideal[of S I J], assumption+)
apply (case_tac "polyn_expr R X n (n, f) = \<zero>\<^bsub>R\<^esub>", simp)
 apply (frule_tac c = "(0, g)" in polyn_mem[of _ 0], simp,
        simp add:ring_times_0_x, simp add:P_mod_def)
 apply (simp add:polyn_expr_def [of _ _ "0"])
 apply (frule pol_coeff_mem[of "(0, g)" 0], simp, simp,
        frule mem_subring_mem_ring[of S "g 0"], assumption,
        simp add:ring_r_one,
        simp add:ring_tOp_commute[of _ "g 0"])
 apply (frule sp_cf_pol_coeff[of "(n, f)" "g 0"], assumption+)
 apply (subst scalar_times_pol_expr[of "g 0" "(n, f)" n], assumption+,
        simp)
 apply (subst P_mod_mod[THEN sym, of "I \<diamondsuit>\<^sub>r\<^bsub>S\<^esub> J" 
        "polyn_expr R X n (sp_cf S (g 0) (n, f))" "sp_cf S (g 0) (n, f)"],
         assumption+,
         simp add:polyn_mem, simp add:sp_cf_pol_coeff,
         rule polyn_mem, simp add:sp_cf_pol_coeff,
         simp add:sp_cf_len, simp,
         simp add:sp_cf_len)
 apply (frule P_mod_mod[THEN sym, of I "polyn_expr R X n (n, f)" 
         "(n, f)"], assumption+, simp, simp,
        simp add:sp_cf_len, subst sp_cf_def, simp,
        simp add:P_mod_coeffTr[of J "g 0"])
 apply (rule allI, rule impI,
        drule_tac a = j in forall_spec, assumption,
        frule_tac h = "f j" in Ring.ideal_subset[of S I], assumption+,
        simp add:Ring.ring_tOp_commute[of S "g 0"])
 apply (simp add:Ring.prod_mem_prod_ideals[of S I J])
done

lemma (in PolynRg) P_mod_mult_const1:"\<lbrakk>ideal S I; ideal S J; 
       pol_coeff S (n, f); P_mod R S X I (polyn_expr R X n (n, f));
       d \<in> J\<rbrakk> \<Longrightarrow> 
       P_mod R S X (I \<diamondsuit>\<^sub>r\<^bsub>S\<^esub> J) ((polyn_expr R X n (n, f)) \<cdot>\<^sub>r d)"
apply (cut_tac subring, frule subring_Ring)
apply (frule P_mod_coeffTr[THEN sym, of J d],
       simp add:Ring.ideal_subset, simp)
apply (frule P_mod_mult_const[of I J n f "\<lambda>j. d"], assumption+,
       simp add:pol_coeff_def, simp add:Ring.ideal_subset)
apply (subst polyn_expr_def, simp,
       frule Ring.ideal_subset[of S  J d], assumption+,
       frule mem_subring_mem_ring[of S d], assumption,
       simp add:ring_r_one)
apply (simp add:polyn_expr_def[of _ _ 0],
       frule Ring.ideal_subset[of S  J d], assumption+,
       frule mem_subring_mem_ring[of S d], assumption,
       simp add:ring_r_one)
done
 
lemma (in PolynRg) P_mod_mult_monomial:"\<lbrakk>ideal S I; p \<in> carrier R\<rbrakk> \<Longrightarrow>
           (P_mod R S X I p ) = (P_mod R S X I (p \<cdot>\<^sub>r X^\<^bsup>R m\<^esup>))"
apply (cut_tac X_mem_R,
       cut_tac subring, frule subring_Ring)
apply (frule npClose[of X m],
       simp add:ring_tOp_commute[of p ])
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp add:ring_times_x_0)
apply (rule iffI)
apply (frule s_cf_expr[of p], assumption+, (erule conjE)+,
       cut_tac low_deg_terms_zero[THEN sym, of "fst (s_cf R S X p)" 
               "snd (s_cf R S X p)" m],
       simp add:polyn_expr_split[THEN sym],
       thin_tac "X^\<^bsup>R m\<^esup> \<cdot>\<^sub>r p =
       polyn_expr R X (fst (s_cf R S X p) + m) (ext_cf S m (s_cf R S X p))",
       frule ext_cf_pol_coeff[of "s_cf R S X p" m])
apply (frule P_mod_mod[THEN sym, of I p "s_cf R S X p"], assumption+,
       thin_tac "p = polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p)",
       simp)
apply (frule P_mod_mod[THEN sym, of I "polyn_expr R X (fst (s_cf R S X p) + 
          m) (ext_cf S m (s_cf R S X p))" "ext_cf S m (s_cf R S X p)"],
       rule polyn_mem, assumption, simp add:ext_cf_def,
       assumption, simp add:ext_cf_len add.commute, simp,
       thin_tac "P_mod R S X I (polyn_expr R X (fst (s_cf R S X p) + m)
        (ext_cf S m (s_cf R S X p))) = (\<forall>j\<le>fst (ext_cf S m (s_cf R S X p)).
         snd (ext_cf S m (s_cf R S X p)) j \<in> I)",
       thin_tac "snd (s_cf R S X p) (fst (s_cf R S X p)) \<noteq> \<zero>\<^bsub>S\<^esub>")
apply (rule allI, rule impI, simp add:ext_cf_len) apply (
       subst ext_cf_def, simp add:sliden_def) apply (rule impI,
       simp add:Ring.ideal_zero[of S]) 
apply (simp add:pol_coeff_split[THEN sym])
 
apply (frule s_cf_expr[of p], assumption+, (erule conjE)+,
       cut_tac low_deg_terms_zero[THEN sym, of "fst (s_cf R S X p)" 
               "snd (s_cf R S X p)" m],
       simp add:polyn_expr_split[THEN sym],
       thin_tac "X^\<^bsup>R m\<^esup> \<cdot>\<^sub>r p =
       polyn_expr R X (fst (s_cf R S X p) + m) (ext_cf S m (s_cf R S X p))",
       frule ext_cf_pol_coeff[of "s_cf R S X p" m]) 
apply (frule P_mod_mod[THEN sym, of I "polyn_expr R X (fst (s_cf R S X p) + 
          m) (ext_cf S m (s_cf R S X p))" "ext_cf S m (s_cf R S X p)"],
       rule polyn_mem, assumption, simp add:ext_cf_def,
       assumption, simp add:ext_cf_len add.commute, simp,
       thin_tac "p = polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p)",
       thin_tac "P_mod R S X I
       (polyn_expr R X (fst (s_cf R S X p) + m) (ext_cf S m (s_cf R S X p)))",
       thin_tac "snd (s_cf R S X p) (fst (s_cf R S X p)) \<noteq> \<zero>\<^bsub>S\<^esub>")
apply (subst P_mod_mod[THEN sym, of I p "s_cf R S X p"], assumption+,
       cut_tac s_cf_expr[of p], simp, assumption+,
       rule allI, rule impI,
       thin_tac "pol_coeff S (ext_cf S m (s_cf R S X p))",
       simp add:ext_cf_len, simp add:ext_cf_def)
apply (drule_tac x = "m + j" in spec,
       frule_tac i = j and j = "fst (s_cf R S X p)" and k = m and l = m in 
       add_le_mono, simp, simp only:add.commute[of _ m],
       thin_tac "j \<le> fst (s_cf R S X p)", simp,
       simp add:sliden_def)
apply simp
done

lemma (in PolynRg) P_mod_multTr:"\<lbrakk>ideal S I; ideal S J; pol_coeff S (n, f); 
       P_mod R S X I (polyn_expr R X n (n, f))\<rbrakk> \<Longrightarrow> \<forall>g. ((pol_coeff S (m, g)
       \<and> (P_mod R S X J (polyn_expr R X m (m, g))))  \<longrightarrow>  
          P_mod R S X (I \<diamondsuit>\<^sub>r\<^bsub>S\<^esub> J) 
           ((polyn_expr R X n (n, f)) \<cdot>\<^sub>r (polyn_expr R X m (m, g))))"
apply (cut_tac subring, frule subring_Ring,
       cut_tac ring_is_ag, cut_tac X_mem_R)
apply (frule polyn_mem[of "(n, f)" n], simp)
 apply (frule Ring.ideal_prod_ideal[of "S" "I" "J"], assumption+)
apply (case_tac "polyn_expr R X n (n, f) = \<zero>\<^bsub>R\<^esub>", simp)
 apply (rule allI, rule impI, erule conjE) 
 apply (frule_tac c = "(m, g)" in polyn_mem[of _ m], simp,
        simp add:ring_times_0_x, simp add:P_mod_def)
apply (induct_tac m)
 apply (rule allI, rule impI, erule conjE,
        rule_tac g = g in P_mod_mult_const[of I J n f], assumption+)
             (* case m = 0 done *)
apply (rule allI, rule impI, erule conjE)
apply (frule_tac n = na and f = g in pol_coeff_pre,
       frule_tac n = na and f = g in P_mod_pre[of J], assumption+)
apply (drule_tac a = g in forall_spec, simp)
 apply (frule_tac n = na and f = g in polyn_Suc_split, simp del:npow_suc)
 apply (thin_tac "polyn_expr R X (Suc na) (Suc na, g) =
        polyn_expr R X na (na, g) \<plusminus> g (Suc na) \<cdot>\<^sub>r X^\<^bsup>R (Suc na)\<^esup>")
 apply (frule_tac c = "(na, g)" and k = na in polyn_mem, simp,
       subgoal_tac "(g (Suc na)) \<cdot>\<^sub>r (X^\<^bsup>R (Suc na)\<^esup>) \<in> carrier R",
       subst ring_distrib1, assumption+)  
apply (frule_tac p = "(polyn_expr R X n (n, f)) \<cdot>\<^sub>r (polyn_expr R X na (na, g))"
       and  q = "(polyn_expr R X n (n, f)) \<cdot>\<^sub>r 
                      ((g (Suc na)) \<cdot>\<^sub>r (X^\<^bsup>R (Suc na)\<^esup>))" in 
        P_mod_add[of "I \<diamondsuit>\<^sub>r\<^bsub>S\<^esub> J"])
 apply (simp add:ring_tOp_closed, rule ring_tOp_closed, assumption+)
 apply (frule_tac c = "(Suc na, g)" and j = "Suc na" in pol_coeff_mem_R,
        simp)
 apply (subst ring_tOp_assoc[THEN sym], assumption+, simp,
        rule npClose, assumption+)
 apply (subst P_mod_mult_monomial[THEN sym, of "I \<diamondsuit>\<^sub>r\<^bsub>S\<^esub> J"], assumption,
       rule ring_tOp_closed, assumption+, simp add:pol_coeff_mem_R)
 apply (rule P_mod_mult_const1, assumption+,
       thin_tac "P_mod R S X (I \<diamondsuit>\<^sub>r\<^bsub>S\<^esub> J)
         (polyn_expr R X n (n, f) \<cdot>\<^sub>r polyn_expr R X na (na, g))")
 apply (cut_tac n1 = na and c1 = "(Suc na, g)" in polyn_Suc[THEN sym], simp,
        simp,
        frule_tac c = "(Suc na, g)" and k = na in polyn_expr_short,
        simp,  simp,
              thin_tac "P_mod R S X J (polyn_expr R X na (na, g))",
              thin_tac "polyn_expr R X na (na, g) \<in> carrier R",
              thin_tac "polyn_expr R X na (na, g) \<plusminus> g (Suc na) \<cdot>\<^sub>r (X^\<^bsup>R na\<^esup> \<cdot>\<^sub>r X)
                       =  polyn_expr R X (Suc na) (Suc na, g)",
              thin_tac "polyn_expr R X na (Suc na, g) =
                                         polyn_expr R X na (na, g)")
 apply (frule_tac p1 = "polyn_expr R X (Suc na) (Suc na, g)" and 
                c1 = "(Suc na, g)" in P_mod_mod[THEN sym, of J],
        simp add:polyn_mem, assumption, simp, simp)

 apply (simp,
        rule ring_tOp_closed,
        cut_tac c = "(Suc na, g)" and j = "Suc na" in pol_coeff_mem_R,
               assumption, simp, simp, rule npClose, assumption+)
done

lemma (in PolynRg) P_mod_mult:"\<lbrakk>ideal S I; ideal S J; pol_coeff S (n, c); 
      pol_coeff S (m, d); P_mod R S X I (polyn_expr R X n (n, c)); 
      P_mod R S X J (polyn_expr R X m (m, d))\<rbrakk>  \<Longrightarrow> 
      P_mod R S X (I \<diamondsuit>\<^sub>r\<^bsub>S\<^esub> J) ((polyn_expr R X n (n, c)) \<cdot>\<^sub>r 
                                        (polyn_expr R X m (m, d)))"
apply (simp add:P_mod_multTr)
done

lemma (in PolynRg) P_mod_mult1:"\<lbrakk>ideal S I; ideal S J;
      p \<in> carrier R; q \<in> carrier R; P_mod R S X I p; P_mod R S X J q\<rbrakk>  \<Longrightarrow> 
      P_mod R S X (I \<diamondsuit>\<^sub>r\<^bsub>S\<^esub> J) (p \<cdot>\<^sub>r q)"
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>")
 apply (simp add:ring_times_0_x, simp add:P_mod_def)
apply (case_tac "q = \<zero>\<^bsub>R\<^esub>")
 apply (simp add:ring_times_x_0, simp add:P_mod_def)

apply (frule s_cf_expr[of p], assumption+,
       frule s_cf_expr[of q], assumption+, (erule conjE)+)
apply (cut_tac P_mod_mult[of I J "fst (s_cf R S X p)" "snd (s_cf R S X p)"
       "fst (s_cf R S X q)"  "snd (s_cf R S X q)"])
      apply (simp add:polyn_expr_split[THEN sym], assumption+)
      apply (simp add:pol_coeff_split[THEN sym])
      apply (simp add:polyn_expr_split[THEN sym])+
done

lemma (in PolynRg) P_mod_mult2l:"\<lbrakk>ideal S I; p \<in> carrier R; q \<in> carrier R; 
      P_mod R S X I p\<rbrakk>  \<Longrightarrow> P_mod R S X I (p \<cdot>\<^sub>r q)"
apply (cut_tac subring, frule subring_Ring[of S],
       frule Ring.whole_ideal[of S])
apply (frule P_mod_whole[of q])
apply (frule P_mod_mult1[of I "carrier S" p q], assumption+)
apply (simp add:Ring.idealprod_whole_r)
done

lemma (in PolynRg) P_mod_mult2r:"\<lbrakk>ideal S I; p \<in> carrier R; q \<in> carrier R; 
      P_mod R S X I q\<rbrakk>  \<Longrightarrow> P_mod R S X I (p \<cdot>\<^sub>r q)"
apply (cut_tac subring, frule subring_Ring[of S],
       frule Ring.whole_ideal[of S])
apply (frule P_mod_whole[of p])
apply (frule P_mod_mult1[of "carrier S" I p q], assumption+)
apply (simp add:Ring.idealprod_whole_l)
done

lemma (in PolynRg) csrp_fn_pol_coeff:"\<lbrakk>ideal S P; PolynRg R' (S /\<^sub>r P) Y; 
       pol_coeff (S /\<^sub>r P) (n,  c')\<rbrakk> \<Longrightarrow>
                          pol_coeff S (n, (cmp (csrp_fn S P) c'))"
apply (cut_tac subring, frule subring_Ring)
apply (simp add:pol_coeff_def)
apply (rule allI, rule impI, simp add:cmp_def)
apply (rule Ring.csrp_fn_mem[of S P], assumption+)
apply simp
done

lemma (in PolynRg) pj_csrp_mem_coeff:"\<lbrakk>ideal S P; pol_coeff (S /\<^sub>r P) (n, c')\<rbrakk>
      \<Longrightarrow> \<forall>j \<le> n. (pj S P) ((csrp_fn S P) (c' j)) = c' j"
apply (cut_tac subring, frule subring_Ring)
apply (rule allI, rule impI, simp add:pol_coeff_def)
apply (simp add:Ring.csrp_pj)
done

lemma (in PolynRg) pHom_pj_csrp:"\<lbrakk>Idomain S; ideal S P;
             PolynRg R' (S /\<^sub>r P) Y; pol_coeff (S /\<^sub>r P) (n, c')\<rbrakk> \<Longrightarrow>
              erH R S X R' (S /\<^sub>r P) Y (pj S P) 
                 (polyn_expr R X n (n, (cmp (csrp_fn S P) c')))
                                     = polyn_expr R' Y n (n, c')"
apply (cut_tac subring, frule subring_Ring,
       frule Ring.qring_ring[of "S" "P"], assumption+) 
 
apply (subst pHom_mem[of R' "(S /\<^sub>r P)" Y "erH R S X R' (S /\<^sub>r P) Y (pj S P)" 
      n  "cmp (csrp_fn S P) c'"], assumption+,
      rule erH_rHom[of R' "S /\<^sub>r P" Y "pj S P"],
       assumption+,
      simp add:pj_Hom, simp add:csrp_fn_pol_coeff)
apply (rule PolynRg.polyn_exprs_eq[of R' "S /\<^sub>r P" Y 
       "(n, cmp (erH R S X R' (S /\<^sub>r P) Y (pj S P)) (cmp (csrp_fn S P) c'))"
       "(n, c')" n], assumption+)
apply (frule csrp_fn_pol_coeff[of P R' Y n c'], assumption+,
       frule erH_rHom [of R' "S /\<^sub>r P" Y "pj S P"], assumption+,
       simp add:pj_Hom,
       rule cmp_pol_coeff_e[of R' "S /\<^sub>r P" Y "erH R S X R' (S /\<^sub>r P) Y (pj S P)"
       n "cmp (csrp_fn S P) c'"], assumption+, simp)
apply (rule allI, rule impI, simp add:cmp_def,
       frule_tac c = "(n, c')" and j = j in 
             PolynRg.pol_coeff_mem[of R' "S /\<^sub>r P" Y], assumption+, simp+,
       frule_tac x = "c' j" in Ring.csrp_fn_mem[of S P], assumption+,
       frule_tac s = "csrp_fn S P (c' j)" in 
            erH_rHom_cf[of R' "S /\<^sub>r P" Y "pj S P"], assumption+,
            simp add:pj_Hom, assumption+)
apply (simp add:pj_csrp_mem_coeff)
done

lemma (in PolynRg) ext_csrp_fn_nonzero:"\<lbrakk>Idomain S; ideal S P; 
      PolynRg R' (S /\<^sub>r P) Y; g' \<in> carrier R'; g' \<noteq> \<zero>\<^bsub>R'\<^esub> \<rbrakk> \<Longrightarrow> 
      polyn_expr R X (deg_n R' (S /\<^sub>r P) Y g') ((deg_n R' (S /\<^sub>r P) Y g'),
          (cmp (csrp_fn S P) (snd (s_cf R' (S /\<^sub>r P) Y g')))) \<noteq> \<zero>"
apply (cut_tac subring, frule subring_Ring,
       frule Ring.qring_ring[of "S" "P"], assumption+,
       frule pj_Hom[of "S" "P"], assumption+,
       frule PolynRg.s_cf_expr[of R' "S /\<^sub>r P" Y g'], assumption+,
       (erule conjE)+)
apply (simp add:PolynRg.s_cf_deg[THEN sym, of R' "S /\<^sub>r P" Y g'],
       frule csrp_fn_pol_coeff[of P R' Y "deg_n R' (S /\<^sub>r P) Y g'"
                  "snd (s_cf R' (S /\<^sub>r P) Y g')"], assumption+,
       simp add:PolynRg.s_cf_deg[of R' "S /\<^sub>r P" Y g'])
apply (subst coeff_nonzero_polyn_nonzero[of "(deg_n R' (S /\<^sub>r P) Y g', 
             cmp (csrp_fn S P) (snd (s_cf R' (S /\<^sub>r P) Y g')))" 
             "deg_n R' (S /\<^sub>r P) Y g'"], assumption+, simp)
apply (simp add:cmp_def, rule contrapos_pp, simp+)
apply (drule_tac a = "deg_n R' (S /\<^sub>r P) Y g'" in forall_spec, simp,
       frule pj_csrp_mem_coeff[of P "deg_n R' (S /\<^sub>r P) Y g'" 
                                "snd (s_cf R' (S /\<^sub>r P) Y g')"],
       simp add:PolynRg.s_cf_deg[of R' "S /\<^sub>r P" Y g']) 
apply (drule_tac a = "deg_n R' (S /\<^sub>r P) Y g'" in forall_spec, simp,
       simp,
       frule pj_Hom[of S P], assumption, simp add:rHom_0_0)
done

lemma (in PolynRg) erH_inv:"\<lbrakk>Idomain S; ideal S P; Ring R'; 
       PolynRg R' (S /\<^sub>r P) Y; g' \<in> carrier R'\<rbrakk> \<Longrightarrow> 
      \<exists>g\<in>carrier R. deg R S X g \<le> (deg R' (S /\<^sub>r P) Y g') \<and>
                (erH R S X R' (S /\<^sub>r P) Y (pj S P)) g = g'" 
apply (cut_tac subring, frule subring_Ring,
       frule Ring.qring_ring[of "S" "P"], assumption+,
       frule pj_Hom[of "S" "P"], assumption+)
apply (frule erH_rHom[of R' "S /\<^sub>r P" Y "pj S P"], assumption+)
apply (case_tac "g' = \<zero>\<^bsub>R'\<^esub>", simp,
       frule erH_rHom_0[of R' "S /\<^sub>r P" Y "pj S P"], assumption+,
       cut_tac ring_zero,
       subgoal_tac "deg R S X (\<zero>) \<le> deg R' (S /\<^sub>r P) Y g'", blast,
       simp add:deg_def)
apply (frule PolynRg.s_cf_expr [of R' "S /\<^sub>r P" Y g'], assumption+,
       (erule conjE)+)
apply (frule pHom_pj_csrp[of P R' Y "fst (s_cf R' (S /\<^sub>r P) Y g')" 
                      "snd (s_cf R' (S /\<^sub>r P) Y g')"], assumption+,
       simp add:PolynRg.pol_coeff_split[THEN sym],
       drule sym, simp)
  apply (subgoal_tac "deg R S X (polyn_expr R X (fst (s_cf R' (S /\<^sub>r P) 
           Y g')) (fst (s_cf R' (S /\<^sub>r P) Y g'), cmp (csrp_fn S P) 
          (snd (s_cf R' (S /\<^sub>r P) Y g')))) \<le> deg R' (S /\<^sub>r P) Y g'",
         subgoal_tac "polyn_expr R X (fst (s_cf R' (S /\<^sub>r P) Y g'))
          (fst (s_cf R' (S /\<^sub>r P) Y g'),
           cmp (csrp_fn S P) (snd (s_cf R' (S /\<^sub>r P) Y g'))) \<in> carrier R",
         blast)
  apply(thin_tac " deg R S X
         (polyn_expr R X (fst (s_cf R' (S /\<^sub>r P) Y g'))
         (fst (s_cf R' (S /\<^sub>r P) Y g'),
         cmp (csrp_fn S P) (snd (s_cf R' (S /\<^sub>r P) Y g'))))
         \<le> deg R' (S /\<^sub>r P) Y g'",
     thin_tac "polyn_expr R' Y (fst (s_cf R' (S /\<^sub>r P) Y g')) 
         (s_cf R' (S /\<^sub>r P) Y g') = g'",
     thin_tac "erH R S X R' (S /\<^sub>r P) Y (pj S P)
         (polyn_expr R X (fst (s_cf R' (S /\<^sub>r P) Y g'))
         (fst (s_cf R' (S /\<^sub>r P) Y g'),
         cmp (csrp_fn S P) (snd (s_cf R' (S /\<^sub>r P) Y g')))) = g'",
     thin_tac "snd (s_cf R' (S /\<^sub>r P) Y g') (fst (s_cf R' (S /\<^sub>r P) Y g')) \<noteq>
               \<zero>\<^bsub>S /\<^sub>r P\<^esub>")
  apply (rule_tac c = "(fst (s_cf R' (S /\<^sub>r P) Y g'),
         cmp (csrp_fn S P) (snd (s_cf R' (S /\<^sub>r P) Y g')))" and 
         k = "fst (s_cf R' (S /\<^sub>r P) Y g')" in polyn_mem)
  apply (rule csrp_fn_pol_coeff, assumption+,
         simp, simp,
         cut_tac pol_deg_le_n[of "polyn_expr R X (fst (s_cf R' (S /\<^sub>r P) Y g'))
          (fst (s_cf R' (S /\<^sub>r P) Y g'),
          cmp (csrp_fn S P) (snd (s_cf R' (S /\<^sub>r P) Y g')))"
            "(fst (s_cf R' (S /\<^sub>r P) Y g'),
          cmp (csrp_fn S P) (snd (s_cf R' (S /\<^sub>r P) Y g')))"])
 apply (simp, 
        simp add:PolynRg.s_cf_deg[THEN sym, of R' "S /\<^sub>r P" Y g'],
        frule ext_csrp_fn_nonzero[of P R' Y g'], assumption+,
        simp add:deg_def, simp add:ale_natle,
        rule polyn_mem, simp add:csrp_fn_pol_coeff, simp,
        simp add:csrp_fn_pol_coeff, simp)
done
 
lemma (in PolynRg) P_mod_0:"\<lbrakk>Idomain S; ideal S P; PolynRg R' (S /\<^sub>r P) Y; 
       g \<in> carrier R\<rbrakk> \<Longrightarrow>
      (erH R S X R' (S /\<^sub>r P) Y (pj S P) g = \<zero>\<^bsub>R'\<^esub>) = (P_mod R S X P g)"
apply (cut_tac subring, frule subring_Ring,
       frule Ring.qring_ring[of "S" "P"], assumption+,
       frule pj_Hom[of "S" "P"], assumption+)
apply (case_tac "g = \<zero>\<^bsub>R\<^esub>",
       cut_tac ring_zero, simp add:P_mod_def,
       rule erH_rHom_0[of R' "S /\<^sub>r P" Y "pj S P"], assumption+) 
apply (frule s_cf_expr[of g], assumption+, (erule conjE)+,
       cut_tac polyn_expr_split[of "fst (s_cf R S X g)" "s_cf R S X g"])
apply (frule erH_map[of R' "S /\<^sub>r P" Y "pj S P" "fst (s_cf R S X g)" 
                        "snd (s_cf R S X g)"], assumption+) 
      apply (subst pol_coeff_split[THEN sym], assumption)
      apply (drule sym, simp)
      apply (thin_tac "erH R S X R' (S /\<^sub>r P) Y (pj S P) g =
       polyn_expr R' Y (fst (s_cf R S X g))
      (fst (s_cf R S X g), cmp (pj S P) (snd (s_cf R S X g)))")
      apply (rotate_tac -1, drule sym)
apply (subst P_mod_mod[THEN sym, of P g "s_cf R S X g"], assumption+,
       thin_tac "g = polyn_expr R X (fst (s_cf R S X g)) (s_cf R S X g)",
       frule erH_rHom_coeff[of R' "S /\<^sub>r P" Y "pj S P" "fst (s_cf R S X g)"
       "snd (s_cf R S X g)"], assumption+, simp)
apply (subst PolynRg.coeff_0_pol_0[THEN sym, of R' "S /\<^sub>r P" Y 
        "(fst (s_cf R S X g), cmp (pj S P) (snd (s_cf R S X g)))" 
        "fst (s_cf R S X g)"], assumption+, simp,
       thin_tac "pol_coeff (S /\<^sub>r P)
       (fst (s_cf R S X g), cmp (pj S P) (snd (s_cf R S X g)))")
apply (simp add:cmp_def)
apply (rule iffI)
 apply (rule allI, rule impI,
        drule_tac a = j in forall_spec, assumption,
        frule_tac j = j in pol_coeff_mem[of "s_cf R S X g"], assumption+,
        simp add:pj_zero[of S P])

 apply (rule allI, rule impI,
        drule_tac a = j in forall_spec, assumption,
        frule_tac j = j in pol_coeff_mem[of "s_cf R S X g"], assumption+,
        simp add:pj_zero[THEN sym, of S P])
done
            
lemma (in PolynRg) P_mod_I_J:"\<lbrakk>p \<in> carrier R; ideal S I; ideal S J; 
          I \<subseteq> J;  P_mod R S X I p\<rbrakk> \<Longrightarrow> P_mod R S X J p"
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp)
 apply (simp add:P_mod_def)

apply (frule s_cf_expr[of p], assumption, (erule conjE)+) 
 apply (frule P_mod_mod[THEN sym, of I p "s_cf R S X p"], assumption+) 
 apply (subst P_mod_mod[THEN sym, of J p "s_cf R S X p"], assumption+, 
        thin_tac "p = polyn_expr R X (fst (s_cf R S X p)) (s_cf R S X p)",
        simp)
 apply (rule allI, rule impI, drule_tac a = j in forall_spec, assumption,
        simp add:subsetD)
done
 
lemma (in PolynRg) P_mod_n_1:"\<lbrakk>Idomain S; t \<in> carrier S; g \<in> carrier R; 
       P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc n)\<^esup>)) g\<rbrakk> \<Longrightarrow> P_mod R S X (S \<diamondsuit>\<^sub>p t) g"
apply (cut_tac subring, frule subring_Ring,
       frule Ring.npClose[of S t n], assumption+,
       frule Ring.npClose[of S t "Suc n"], assumption+,
       frule Ring.principal_ideal[of S t], assumption+, 
       frule Ring.principal_ideal[of S "t^\<^bsup>S (Suc n)\<^esup>"], assumption+)
apply (case_tac "g = \<zero>\<^bsub>R\<^esub>", simp add:P_mod_def)
apply (frule s_cf_expr[of g], assumption,
        (erule conjE)+,
       subst P_mod_mod[THEN sym, of "S \<diamondsuit>\<^sub>p t" "g" "s_cf R S X g"],
       assumption+) 
apply (frule_tac P_mod_mod[THEN sym, of "S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc n)\<^esup>)" g "s_cf R S X g"],
       assumption+)
apply (simp del:npow_suc,
       thin_tac "g = polyn_expr R X (fst (s_cf R S X g)) (s_cf R S X g)")
apply (rule allI, rule impI,
       drule_tac a = j in forall_spec, assumption+)
apply (simp add:Rxa_def, erule bexE, simp,
       simp add:Ring.ring_tOp_assoc[THEN sym, of S],
       frule_tac x = r and y = "t^\<^bsup>S n\<^esup>" in Ring.ring_tOp_closed, assumption+,
       blast)
done

lemma (in PolynRg) P_mod_n_m:"\<lbrakk>Idomain S; t \<in> carrier S; g \<in> carrier R; 
      m \<le> n; P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc n)\<^esup>)) g\<rbrakk> \<Longrightarrow> 
               P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc m)\<^esup>)) g"
apply (cut_tac subring, frule subring_Ring)
apply (rule P_mod_I_J[of g "S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc n)\<^esup>)" "S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc m)\<^esup>)"],
       assumption)
 apply (rule Ring.principal_ideal, assumption+,
        rule Ring.npClose, assumption+)
 apply (rule Ring.principal_ideal, assumption+,
        rule Ring.npClose, assumption+)
 apply (thin_tac "P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc n)\<^esup>)) g")
 apply (rule subsetI)
   apply (simp del:npow_suc add:Rxa_def, erule bexE, simp del:npow_suc)
   apply (frule Ring.npMulDistr[THEN sym, of S t "Suc n - Suc m" "Suc m"],
          assumption)
   apply (simp del:npow_suc,
          thin_tac "t^\<^bsup>S (Suc n)\<^esup> = t^\<^bsup>S (n - m)\<^esup> \<cdot>\<^sub>r\<^bsub>S\<^esub> t^\<^bsup>S (Suc m)\<^esup>",
          thin_tac "x = r \<cdot>\<^sub>r\<^bsub>S\<^esub> (t^\<^bsup>S (n - m)\<^esup> \<cdot>\<^sub>r\<^bsub>S\<^esub> t^\<^bsup>S (Suc m)\<^esup>)")
   apply (subst Ring.ring_tOp_assoc[THEN sym, of S], assumption+,
          (rule Ring.npClose, assumption+)+)
   apply (frule_tac x = r and y = "t^\<^bsup>S (n - m)\<^esup>" in Ring.ring_tOp_closed,
           assumption+,
          rule Ring.npClose, assumption+, blast)
   apply assumption
done

lemma (in PolynRg) P_mod_diff:"\<lbrakk>Idomain S; ideal S P; PolynRg R' (S /\<^sub>r P) Y; 
       g \<in> carrier R; h \<in> carrier R\<rbrakk> \<Longrightarrow>
    (erH R S X R' (S /\<^sub>r P) Y (pj S P) g = (erH R S X R' (S /\<^sub>r P) Y (pj S P) h))
     = (P_mod R S X P (g \<plusminus> -\<^sub>a h))"
apply (cut_tac ring_is_ag,
       frule PolynRg.is_Ring[of R'],
       cut_tac subring,
       frule subring_Ring,
       frule Ring.qring_ring[of S P], assumption+,
       frule pj_Hom[of "S" "P"], assumption+,
       frule erH_rHom[of R' "S /\<^sub>r P" Y "pj S P"],
       assumption+,
       frule Ring.ring_is_ag[of R']) 
apply (frule erH_mem[of R' "S /\<^sub>r P" Y "pj S P" g], assumption+,
       frule erH_mem[of R' "S /\<^sub>r P" Y "pj S P" h], assumption+) 
apply (rule iffI)
apply (frule_tac a = "erH R S X R' (S /\<^sub>r P) Y (pj S P) g" and 
                 b = "erH R S X R' (S /\<^sub>r P) Y (pj S P) h" in 
       aGroup.ag_eq_diffzero[of R'], assumption+, simp,
       simp add:erH_minus[THEN sym, of R' "S /\<^sub>r P" Y "pj S P" h],
       drule sym, simp,
       thin_tac "erH R S X R' (S /\<^sub>r P) Y (pj S P) h =
                        erH R S X R' (S /\<^sub>r P) Y (pj S P) g",
       frule_tac x = h in aGroup.ag_mOp_closed, assumption+,
       simp add:erH_add[THEN sym, of  R' "S /\<^sub>r P" Y "pj S P" g "-\<^sub>a h"])
apply (subst P_mod_0[THEN sym, of P R' Y "g \<plusminus> -\<^sub>a h"], assumption+,
         rule aGroup.ag_pOp_closed, assumption+)

apply (frule_tac a = "erH R S X R' (S /\<^sub>r P) Y (pj S P) g" and 
                 b = "erH R S X R' (S /\<^sub>r P) Y (pj S P) h" in 
       aGroup.ag_eq_diffzero[of R'], assumption+, simp,
       simp add:erH_minus[THEN sym, of R' "S /\<^sub>r P" Y "pj S P" h])
   apply (subst erH_add[THEN sym, of  R' "S /\<^sub>r P" Y "pj S P" g "-\<^sub>a h"],
          assumption+,
          rule aGroup.ag_mOp_closed, assumption+)
   apply (subst P_mod_0[of P R' Y "g \<plusminus> -\<^sub>a h"], assumption+,
          rule aGroup.ag_pOp_closed, assumption+,
          rule aGroup.ag_mOp_closed, assumption+)
done

lemma (in PolynRg) P_mod_erH:"\<lbrakk>Idomain S; ideal S P; PolynRg R' (S /\<^sub>r P) Y; 
        g \<in> carrier R; v \<in> carrier R; t \<in> P \<rbrakk> \<Longrightarrow>
        (erH R S X R' (S /\<^sub>r P) Y (pj S P) g = 
                  (erH R S X R' (S /\<^sub>r P) Y (pj S P) (g \<plusminus> (t \<cdot>\<^sub>r v))))" 
apply (cut_tac subring, frule subring_Ring,
       cut_tac ring_is_ag,
       frule Ring.ideal_subset[of S P t], assumption+,
       frule mem_subring_mem_ring[of S t], assumption+,
       frule ring_tOp_closed[of t v], assumption+)
apply (subst P_mod_diff[of P R' Y g "g \<plusminus> (t \<cdot>\<^sub>r v)"], assumption+,
       rule aGroup.ag_pOp_closed, assumption+)
apply (simp add:aGroup.ag_p_inv,
       frule aGroup.ag_mOp_closed[of R g], assumption+,
       frule aGroup.ag_mOp_closed[of R "t \<cdot>\<^sub>r v"], assumption+,
       subst aGroup.ag_pOp_assoc[THEN sym], assumption+,
       simp add:aGroup.ag_r_inv1, simp add:aGroup.ag_l_zero)
apply (rule P_mod_minus[of P "t \<cdot>\<^sub>r v"], assumption+,
       frule P_mod_mult1[of P "carrier S" t v],
       simp add:Ring.whole_ideal, assumption+,
       subst P_mod_coeffTr[of P t], assumption+,
       rule P_mod_whole[of v], assumption+,
       simp add:Ring.idealprod_whole_r[of S P])
done

lemma (in PolynRg) coeff_principalTr:"\<lbrakk>t \<in> carrier S\<rbrakk> \<Longrightarrow>
    \<forall>f. pol_coeff S (n, f) \<and> (\<forall>j \<le> n. f j \<in> S \<diamondsuit>\<^sub>p t) \<longrightarrow>
          (\<exists>f'. pol_coeff S (n, f') \<and> (\<forall>j \<le> n. f j = t \<cdot>\<^sub>r\<^bsub>S\<^esub> (f' j)))"
apply (cut_tac subring, frule subring_Ring,
       cut_tac ring_is_ag)
apply (induct_tac n,
       rule allI, rule impI, erule conjE, 
       simp add:Rxa_def, erule bexE,
       simp add:Ring.ring_tOp_commute[of S _ t],
       subgoal_tac "pol_coeff S (0, (\<lambda>j. r))",
       subgoal_tac "t \<cdot>\<^sub>r\<^bsub>S\<^esub> r = t \<cdot>\<^sub>r\<^bsub>S\<^esub> ((\<lambda>j. r) 0)", blast,
       simp, 
       simp add:pol_coeff_def)

apply (rule allI, rule impI, erule conjE,
       frule_tac n = n and f = f in pol_coeff_pre,
       subgoal_tac "\<forall>j \<le> n. f j \<in> S \<diamondsuit>\<^sub>p t",
       drule_tac a = f in forall_spec, simp,
       erule exE, erule conjE,
       frule_tac c = "(Suc n, f)" and j = "Suc n" in 
        pol_coeff_mem, simp, simp,
        drule_tac x = "Suc n" in spec, simp,
        simp add:Rxa_def,
        erule bexE, simp add:Ring.ring_tOp_commute[of "S" _ "t"])
  apply (subgoal_tac "pol_coeff S ((Suc n), (\<lambda>j. if j \<le> n then (f' j) else r))
         \<and>
        (\<forall>j \<le> (Suc n). f j = t \<cdot>\<^sub>r\<^bsub>S\<^esub> ((\<lambda>j. if j \<le> n then (f' j) else r) j))",
       blast) 
  apply (rule conjI, simp add:pol_coeff_def,
         rule allI, rule impI, 
         case_tac "j \<le> n", simp)
  apply simp
  apply (drule_tac y = j and x = n in not_le_imp_less,
         drule_tac m = n and n = j in Suc_leI)
  apply (frule_tac m = j and n = "Suc n" in le_antisym, assumption, simp,
         thin_tac "\<forall>f. pol_coeff S (n, f) \<and> (\<forall>j\<le>n. f j \<in> S \<diamondsuit>\<^sub>p t) \<longrightarrow>
                  (\<exists>f'. pol_coeff S (n, f') \<and> (\<forall>j\<le>n. f j = t \<cdot>\<^sub>r\<^bsub>S\<^esub> f' j))")
  apply (rule allI, rule impI, 
         drule_tac a = j in forall_spec, simp+)
done

lemma (in PolynRg) coeff_principal:"\<lbrakk>t \<in> carrier S; pol_coeff S (n, f); 
          \<forall>j \<le> n. f j \<in> S \<diamondsuit>\<^sub>p t\<rbrakk> \<Longrightarrow>
          \<exists>f'. pol_coeff S (n, f') \<and> (\<forall>j \<le> n. f j = t \<cdot>\<^sub>r\<^bsub>S\<^esub> (f' j))"
apply (simp add:coeff_principalTr)
done
 
lemma (in PolynRg) Pmod_0_principal:"\<lbrakk>Idomain S; t \<in> carrier S; g \<in> carrier R;
            P_mod R S X (S \<diamondsuit>\<^sub>p t) g\<rbrakk> \<Longrightarrow> \<exists>h\<in> carrier R. g = t \<cdot>\<^sub>r h"
apply (cut_tac subring, frule subring_Ring)
apply (case_tac "g = \<zero>\<^bsub>R\<^esub>",
       cut_tac ring_zero,
       frule mem_subring_mem_ring[of S t], assumption+,
       frule ring_times_x_0[THEN sym, of t], blast)

apply (frule s_cf_expr[of g], assumption+,
        (erule conjE)+, frule Ring.principal_ideal[of S t], assumption,
       simp add:P_mod_mod[THEN sym, of "S \<diamondsuit>\<^sub>p t" g],
       frule coeff_principal[of t "fst (s_cf R S X g)" "snd (s_cf R S X g)"],
         simp add:pol_coeff_split[THEN sym], assumption+, 
       erule exE, erule conjE)
 apply (frule_tac c = "(fst (s_cf R S X g), f')" and k = "fst (s_cf R S X g)"
        in polyn_mem, simp,
        subgoal_tac "g = t \<cdot>\<^sub>r 
        (polyn_expr R X (fst (s_cf R S X g)) (fst (s_cf R S X g), f'))",
        blast)
 apply (subst scalar_times_pol_expr[of  t "(fst (s_cf R S X g), f')" 
           "fst (s_cf R S X g)"], assumption+, simp,
        drule sym,
        subgoal_tac "polyn_expr R X (fst (s_cf R S X g)) (s_cf R S X g) =
     polyn_expr R X (fst (s_cf R S X g)) (sp_cf S t (fst (s_cf R S X g), f'))",
        simp)
 apply (frule_tac c = "(fst (s_cf R S X g), f')" in sp_cf_pol_coeff[of _ t],
        assumption+,
        frule_tac d = "sp_cf S t (fst (s_cf R S X g), f')" in 
         pol_expr_unique2[of "s_cf R S X g"], assumption+,
        simp, simp add:sp_cf_len, simp add:sp_cf_len,
       thin_tac "(g =
           polyn_expr R X (fst (s_cf R S X g))
            (sp_cf S t (fst (s_cf R S X g), f'))) =
          (\<forall>j\<le>fst (s_cf R S X g).
              t \<cdot>\<^sub>r\<^bsub>S\<^esub> f' j = snd (sp_cf S t (fst (s_cf R S X g), f')) j)",
       thin_tac "polyn_expr R X (fst (s_cf R S X g)) (s_cf R S X g) = g",
       thin_tac "polyn_expr R X (fst (s_cf R S X g)) (fst (s_cf R S X g), f')
          \<in> carrier R")
 apply (rule allI, rule impI, 
        drule_tac a = j in forall_spec, assumption+,
        simp add:sp_cf_def)
done
 
lemma (in PolynRg) Pmod0_principal_rev:"\<lbrakk>Idomain S; t \<in> carrier S; 
                     g \<in> carrier R; \<exists>h\<in> carrier R. g = t \<cdot>\<^sub>r  h\<rbrakk> \<Longrightarrow> 
                                       P_mod R S X (S \<diamondsuit>\<^sub>p t) g"
apply (cut_tac subring, frule subring_Ring)
apply (erule bexE)
apply (case_tac "t = \<zero>\<^bsub>S\<^esub>", 
       frule Subring_zero_ring_zero, simp)
       apply (simp add:ring_times_0_x, simp add:P_mod_def)

apply (case_tac "h = \<zero>\<^bsub>R\<^esub>", simp,
       frule mem_subring_mem_ring[of S t], assumption+,
       simp add:ring_times_x_0, simp add:P_mod_def,
       cut_tac polyn_ring_integral, simp)
apply (frule_tac p = h in s_cf_expr, assumption+, (erule conjE)+,
       frule_tac c = "s_cf R S X h" and n = "fst (s_cf R S X h)" in 
       scalar_times_pol_expr[of  t], assumption+, simp,
       thin_tac "g = t \<cdot>\<^sub>r h",
       drule sym, simp)
apply (frule Ring.principal_ideal[of S t], assumption+,
       frule_tac c1 = "sp_cf S t (s_cf R S X h)" and p1 = "t \<cdot>\<^sub>r h" in 
       P_mod_mod[THEN sym],
       frule_tac x = t in mem_subring_mem_ring, assumption,
                 rule ring_tOp_closed, assumption+,
       simp add:sp_cf_pol_coeff, simp add:sp_cf_len)
apply (drule sym, simp,
       thin_tac "P_mod R S X (S \<diamondsuit>\<^sub>p t) (t \<cdot>\<^sub>r h) =
         (\<forall>j\<le>fst (sp_cf S t (s_cf R S X h)).
             snd (sp_cf S t (s_cf R S X h)) j \<in> S \<diamondsuit>\<^sub>p t)",
       thin_tac "polyn_expr R X (fst (s_cf R S X h)) 
                     (sp_cf S t (s_cf R S X h)) = t \<cdot>\<^sub>r h",
       thin_tac "polyn_expr R X (fst (s_cf R S X h)) (s_cf R S X h) = h")
apply (rule allI, rule impI, simp add:sp_cf_len,
       subst sp_cf_def, simp, subst Rxa_def, simp,
       frule_tac c = "s_cf R S X h" and j = j in pol_coeff_mem,
       assumption) 
apply (simp add:Ring.ring_tOp_commute[of S t], blast)
done

(** NOTE. if t \<noteq> 0\<^sub>S then, deg g = deg h, because deg t = 0 **)

lemma (in PolynRg) Pmod0_principal_rev1:"\<lbrakk>Idomain S; t \<in> carrier S; 
                     h \<in> carrier R\<rbrakk> \<Longrightarrow> P_mod R S X (S \<diamondsuit>\<^sub>p t) (t \<cdot>\<^sub>r h)"
apply (rule Pmod0_principal_rev[of t "t \<cdot>\<^sub>r h"], assumption+)
apply (cut_tac subring,
       frule mem_subring_mem_ring[of S t], assumption+,
       simp add:ring_tOp_closed)
apply blast
done

lemma (in PolynRg) Pmod0_principal_erH_vanish_t:"\<lbrakk>Idomain S; ideal S (S \<diamondsuit>\<^sub>p t);
 t \<in> carrier S; t \<noteq> \<zero>\<^bsub>S\<^esub>; PolynRg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y \<rbrakk> \<Longrightarrow>
      erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) t = \<zero>\<^bsub>R'\<^esub>"
apply (cut_tac subring, frule subring_Ring,
       frule mem_subring_mem_ring[of S t], assumption+)
 apply (subst P_mod_0[of "S \<diamondsuit>\<^sub>p t" R' Y t], assumption+)
 apply (rule Pmod0_principal_rev[of t t], assumption+)
 apply (cut_tac ring_one,
        frule ring_r_one[THEN sym, of t], blast)
done

lemma (in PolynRg) P_mod_diffxxx1:"\<lbrakk>Idomain S; t \<in> carrier S; t \<noteq> \<zero>\<^bsub>S\<^esub>; 
        maximal_ideal S (S \<diamondsuit>\<^sub>p t); PolynRg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y; 
        f \<in> carrier R; g \<in> carrier R; h \<in> carrier R;
        f \<noteq> \<zero>; g \<noteq> \<zero>; h \<noteq> \<zero>; u \<in> carrier R; v \<in> carrier R;
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g \<noteq> \<zero>\<^bsub>R'\<^esub>; 
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h \<noteq> \<zero>\<^bsub>R'\<^esub>;
        ra \<in> carrier R;
        f \<plusminus> -\<^sub>a (g \<cdot>\<^sub>r h) = t^\<^bsup>S m\<^esup> \<cdot>\<^sub>r ra; 0 < m; 
        (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) u)
         \<cdot>\<^sub>r\<^bsub>R'\<^esub> erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g \<plusminus>\<^bsub>R'\<^esub>
        (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) v)
         \<cdot>\<^sub>r\<^bsub>R'\<^esub> erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h =
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra\<rbrakk>
       \<Longrightarrow> P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc m)\<^esup>))
           (f \<plusminus> -\<^sub>a ((g \<plusminus> t^\<^bsup>S m\<^esup> \<cdot>\<^sub>r v) \<cdot>\<^sub>r (h \<plusminus> t^\<^bsup>S m\<^esup> \<cdot>\<^sub>r u)))"
apply (cut_tac is_Ring,
       cut_tac subring, frule subring_Ring,
       cut_tac ring_is_ag,
       frule PolynRg.is_Ring[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y],
       frule Ring.ring_is_ag[of R'],
       frule Ring.maximal_ideal_ideal[of "S" "S \<diamondsuit>\<^sub>p t"], assumption+,
       frule Ring.qring_ring[of S "S \<diamondsuit>\<^sub>p t"], assumption+, 
       frule erH_rHom[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y "pj S (S \<diamondsuit>\<^sub>p t)"], assumption+,
       frule mem_subring_mem_ring[of S t], assumption+)
apply (rule pj_Hom[of S "S \<diamondsuit>\<^sub>p t"], assumption+,
       frule pHom_rHom[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y 
        "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))"], assumption+)
apply (simp del:npow_suc add:rHom_tOp[THEN sym])
apply (frule_tac ring_tOp_closed[of u g], assumption,
       frule_tac ring_tOp_closed[of v h], assumption)
apply (simp del:npow_suc add:rHom_add[THEN sym])
 apply (rotate_tac 17, drule sym)
 apply (frule P_mod_diff[of "S \<diamondsuit>\<^sub>p t" R' Y ra  "u \<cdot>\<^sub>r g \<plusminus> v \<cdot>\<^sub>r h"], assumption+) 
 apply (rule aGroup.ag_pOp_closed, assumption+, simp del:npow_suc)
 apply (frule Pmod_0_principal[of t "ra \<plusminus> -\<^sub>a (u \<cdot>\<^sub>r g \<plusminus> v \<cdot>\<^sub>r h)"], assumption+)
 apply (rule aGroup.ag_pOp_closed, assumption+,
        rule aGroup.ag_mOp_closed, assumption,
        rule aGroup.ag_pOp_closed, assumption+, erule bexE)

apply (frule Ring.npClose[of S t m], assumption+,
       frule mem_subring_mem_ring[of S "t^\<^bsup>S m\<^esup>"], assumption+,
       subst ring_distrib1,
       rule aGroup.ag_pOp_closed, assumption+,
       rule ring_tOp_closed, simp add:mem_subring_mem_ring,
       assumption+)
apply (rule ring_tOp_closed, assumption+)
apply (subst ring_distrib2, assumption+,
       rule ring_tOp_closed, assumption+ )
apply (frule_tac x = g and y = h in ring_tOp_closed, assumption+,
       frule_tac x = "t^\<^bsup>S m\<^esup>" and y = v in ring_tOp_closed, assumption+,
       frule_tac x = "t^\<^bsup>S m\<^esup>" and y = u in ring_tOp_closed, assumption+,
       frule_tac x = "t^\<^bsup>S m\<^esup> \<cdot>\<^sub>r v" and y = h in ring_tOp_closed, assumption+)
apply (subst ring_distrib2, assumption+,
      frule_tac x = "t^\<^bsup>S m\<^esup> \<cdot>\<^sub>r v" and y = "t^\<^bsup>S m\<^esup> \<cdot>\<^sub>r u" in ring_tOp_closed, 
      assumption+)
apply (subst aGroup.ag_p_inv, assumption+,
       rule aGroup.ag_pOp_closed, assumption+,
       rule aGroup.ag_pOp_closed, assumption+,
       rule ring_tOp_closed, assumption+)
apply (subst aGroup.ag_p_inv, assumption+,
       frule aGroup.ag_mOp_closed[of R "g \<cdot>\<^sub>r h"], assumption+,
       frule aGroup.ag_mOp_closed[of R "t^\<^bsup>S m\<^esup> \<cdot>\<^sub>r v \<cdot>\<^sub>r h"], assumption+)
apply (subst aGroup.ag_pOp_assoc[of R "-\<^sub>a (g \<cdot>\<^sub>r h)" " -\<^sub>a (t^\<^bsup>S m\<^esup> \<cdot>\<^sub>r v \<cdot>\<^sub>r h)"],
       assumption+)
apply (rule aGroup.ag_mOp_closed, assumption,
       rule aGroup.ag_pOp_closed, assumption,
       rule ring_tOp_closed, assumption+)
apply (subst aGroup.ag_pOp_assoc[THEN sym], assumption+,
       rule aGroup.ag_pOp_closed, assumption,
       rule aGroup.ag_mOp_closed, assumption+,
       rule aGroup.ag_mOp_closed, assumption+,
       rule aGroup.ag_pOp_closed, assumption+,
       rule ring_tOp_closed, assumption+, simp del:npow_suc)

apply (subst aGroup.ag_p_inv, assumption,
       rule ring_tOp_closed, assumption+,
       simp del:npow_suc add:ring_tOp_assoc[of "t^\<^bsup>S m\<^esup>" v h],
       simp add:del:npow_suc add:ring_tOp_commute[of g "t^\<^bsup>S m\<^esup> \<cdot>\<^sub>r u"],
       simp del:npow_suc add:ring_tOp_assoc[of "t^\<^bsup>S m\<^esup>" u g],
       simp del:npow_suc add:ring_inv1_2,
       subst aGroup.ag_pOp_assoc[THEN sym], assumption+,
                            rule ring_tOp_closed, assumption+)
       apply (rule aGroup.ag_pOp_closed, assumption+,
              (rule ring_tOp_closed, assumption+)+,
              rule aGroup.ag_mOp_closed, assumption+,
              (rule ring_tOp_closed, assumption+)+,
              rule aGroup.ag_mOp_closed, assumption+)
      apply (subst ring_distrib1[THEN sym, of "t^\<^bsup>S m\<^esup>" ra  "v \<cdot>\<^sub>r (-\<^sub>a h)"],
             assumption+,
             rule ring_tOp_closed, assumption+, rule aGroup.ag_mOp_closed,
             assumption+)
      apply (subst aGroup.ag_pOp_assoc[THEN sym], assumption+,
             rule ring_tOp_closed, assumption+,
             rule aGroup.ag_pOp_closed, assumption+,
             rule ring_tOp_closed, assumption+, rule aGroup.ag_mOp_closed,
             assumption+)
      apply ((rule ring_tOp_closed, assumption+)+,
              rule aGroup.ag_mOp_closed, assumption+,
             (rule ring_tOp_closed, assumption+)+,
             rule aGroup.ag_mOp_closed, assumption+)
        apply (subst ring_distrib1[THEN sym, of "t^\<^bsup>S m\<^esup>"],
               assumption+,
               rule aGroup.ag_pOp_closed, assumption+,
               rule ring_tOp_closed, assumption+,
               rule aGroup.ag_mOp_closed, assumption+,
               rule ring_tOp_closed, assumption+,
               rule aGroup.ag_mOp_closed, assumption+)
         apply (subst ring_tOp_assoc[of "t^\<^bsup>S m\<^esup>" v], assumption+,
                rule ring_tOp_closed, assumption+,
                rule aGroup.ag_mOp_closed, assumption+)
         apply (subst ring_distrib1[THEN sym, of "t^\<^bsup>S m\<^esup>"],
                assumption+,
                rule aGroup.ag_pOp_closed, assumption+,
                rule aGroup.ag_pOp_closed, assumption+,
                rule ring_tOp_closed, assumption,
                rule aGroup.ag_mOp_closed, assumption+,
                rule ring_tOp_closed, assumption,
                rule aGroup.ag_mOp_closed, assumption+,
                (rule ring_tOp_closed, assumption+)+,
                rule aGroup.ag_mOp_closed, assumption+)
    apply (frule ring_tOp_closed[of u g], assumption+,
           frule ring_tOp_closed[of v h], assumption+,
           simp del:npow_suc add:aGroup.ag_p_inv[of R "u \<cdot>\<^sub>r g" "v \<cdot>\<^sub>r h"],
           simp del:npow_suc add:add:ring_inv1_2,
           frule aGroup.ag_mOp_closed[of R g], assumption+,
                  frule aGroup.ag_mOp_closed[of R h], assumption+,
           frule ring_tOp_closed[of u "-\<^sub>a g"], assumption+,
                  frule ring_tOp_closed[of v "-\<^sub>a h"], assumption+,
           simp del:npow_suc add:aGroup.ag_pOp_commute[of R
                  "u \<cdot>\<^sub>r (-\<^sub>a g)" "v \<cdot>\<^sub>r (-\<^sub>a h)"],
           simp del:npow_suc add:aGroup.ag_pOp_assoc[THEN sym, 
                  of R ra "v \<cdot>\<^sub>r (-\<^sub>a h)" "u \<cdot>\<^sub>r (-\<^sub>a g)"])
  apply (subst ring_tOp_assoc[THEN sym, of v "t^\<^bsup>S m\<^esup>" "-\<^sub>a u"], assumption+,
         rule aGroup.ag_mOp_closed, assumption+,
         simp only:ring_tOp_commute[of v "t^\<^bsup>S m\<^esup>"],
         subgoal_tac "t^\<^bsup>S m\<^esup> \<cdot>\<^sub>r v = t \<cdot>\<^sub>r (t^\<^bsup>S (m - Suc 0)\<^esup> \<cdot>\<^sub>r v)", 
         simp del:npow_suc)
  apply (subst ring_tOp_assoc[of t],
         frule mem_subring_mem_ring[of S t], assumption+,
         rule ring_tOp_closed) 
   apply (frule Ring.npClose[of S t "m - Suc 0"], assumption+,
          simp add:mem_subring_mem_ring, assumption,
          rule aGroup.ag_mOp_closed, assumption+,
          subst ring_distrib1[THEN sym, of t],
          simp add:mem_subring_mem_ring, assumption+)
  apply ((rule ring_tOp_closed)+,
          frule Ring.npClose[of S t "m - Suc 0"], assumption+,
          simp add:mem_subring_mem_ring, assumption,
          rule aGroup.ag_mOp_closed, assumption+)
  apply (subst ring_tOp_assoc[THEN sym],
         frule Ring.npClose[of S t "m - Suc 0"], assumption+,
         simp add:mem_subring_mem_ring)

  apply (rule aGroup.ag_pOp_closed, assumption+,
         rule ring_tOp_closed,
         frule Ring.npClose[of S t "m - Suc 0"], assumption+,
         rule ring_tOp_closed, simp add:mem_subring_mem_ring,
         assumption, rule aGroup.ag_mOp_closed, assumption+,
         simp add:Subring_tOp_ring_tOp[THEN sym],
         simp only:npow_suc[THEN sym, of S t m]) 
  apply (rule Pmod0_principal_rev1[of "t^\<^bsup>S (Suc m)\<^esup>"], assumption+,
         rule Ring.npClose, assumption+,
         rule aGroup.ag_pOp_closed, assumption+,
         (rule ring_tOp_closed)+,
         frule Ring.npClose[of S t "m - Suc 0"], assumption+,
         simp add:mem_subring_mem_ring, assumption,
         rule aGroup.ag_mOp_closed, assumption+)
  apply (frule Ring.npClose[of S t "m - Suc 0"], assumption+,
         frule mem_subring_mem_ring[of S t], assumption,
         frule mem_subring_mem_ring[of S "t^\<^bsup>S (m - Suc 0)\<^esup>"], assumption,
         simp add:ring_tOp_assoc[THEN sym],
         simp add:ring_tOp_commute[of t "t^\<^bsup>S (m - Suc 0)\<^esup>"],
         subgoal_tac "t^\<^bsup>S m\<^esup> = t^\<^bsup>S (Suc (m - Suc 0))\<^esup>",
         simp del:Suc_pred add:Subring_tOp_ring_tOp,
         simp only:Suc_pred)
done

lemma (in PolynRg) P_mod_diffxxx2:"\<lbrakk>Idomain S; t \<in> carrier S; t \<noteq> \<zero>\<^bsub>S\<^esub>;
   maximal_ideal S (S \<diamondsuit>\<^sub>p t); PolynRg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y; 
   f \<in> carrier R; g \<in> carrier R; h \<in> carrier R;
  deg R S X g \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
                          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g);
  deg R S X h + 
  deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) 
                                      \<le> deg R S X f;
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
        (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g);
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
       (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h);
  rel_prime_pols R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
     (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) 
        (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h);
  P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) (f \<plusminus> -\<^sub>a (g \<cdot>\<^sub>r h)); 0 < m\<rbrakk> \<Longrightarrow> 
\<exists>g1 h1. g1 \<in>carrier R \<and> h1 \<in> carrier R \<and> 
     (deg R S X g1 \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
       (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g1)) \<and> 
  P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) (g \<plusminus> -\<^sub>a g1) \<and>  (deg R S X h1 + 
  deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g1)
      \<le> deg R S X f) \<and>
        P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) (h \<plusminus> -\<^sub>a h1) \<and> 
        P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc m)\<^esup>)) (f \<plusminus> (-\<^sub>a (g1 \<cdot>\<^sub>r h1)))" 
apply (cut_tac subring, frule subring_Ring,
       cut_tac ring_is_ag,
       frule Ring.residue_field_cd[of S "S \<diamondsuit>\<^sub>p t"], assumption+,
       frule Ring.maximal_ideal_ideal[of "S" "S \<diamondsuit>\<^sub>p t"], assumption+,
       frule pj_Hom[of "S" "S \<diamondsuit>\<^sub>p t"], assumption+,
       frule mem_subring_mem_ring[of S t], assumption+,
       frule Ring.qring_ring[of S "S \<diamondsuit>\<^sub>p t"], assumption+,
       frule  PolynRg.pol_nonzero[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y 
         "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g"],
       rule erH_mem, assumption+,
       frule erH_rHom_nonzero[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y "pj S (S \<diamondsuit>\<^sub>p t)" "g"], 
       assumption+, simp add:aless_imp_le)
apply (frule PolynRg.pol_nonzero[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y 
        "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h"], 
       rule erH_mem, assumption+,
       frule erH_rHom_nonzero[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y "pj S (S \<diamondsuit>\<^sub>p t)" "h"], 
       assumption+, simp add:aless_imp_le, simp del:npow_suc add:aless_imp_le) 
apply (
       frule pol_nonzero[THEN sym, of "h"], simp del:npow_suc,
       frule aadd_pos_poss[of "deg R S X h" "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)"], assumption+,
       frule aless_le_trans[of "0" "(deg R S X h) +
           (deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
           (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g))"
          "deg R S X f"], assumption+,
       frule pol_nonzero[of f], simp del:npow_suc add:aless_imp_le)
 apply (thin_tac "0 < deg R S X f",
         thin_tac "0 < deg R S X h +
         deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)")
 apply (frule Pmod_0_principal[of "t^\<^bsup>S m\<^esup>" "f \<plusminus> -\<^sub>a (g \<cdot>\<^sub>r h)"],
        rule Ring.npClose, assumption+)
apply (rule aGroup.ag_pOp_closed, assumption+,
       rule aGroup.ag_mOp_closed, assumption+,
       rule ring_tOp_closed, assumption+,
       erule bexE, rename_tac ra) 

(******* deg (t^\<^sup>S\<^sup> \<^sup>m) ra \<le> deg f ******)
apply (frule deg_mult_pols1 [of g h], assumption+,
       frule aadd_le_mono[of "deg R S X g" "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)"
              "deg R S X h"])
apply (simp only:aadd_commute[of "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)"
             "deg R S X h"])
apply (frule ale_trans[of "deg R S X g + deg R S X h" "deg R S X h +
       deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
       (pj S (S \<diamondsuit>\<^sub>p t)) g)"  "deg R S X f"], assumption+)
 apply (thin_tac "deg R S X g + deg R S X h
          \<le> deg R S X h +
            deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)")
 apply (frule_tac ring_tOp_closed[of g h], assumption+,
        frule deg_minus_eq1[of "g \<cdot>\<^sub>r h"],
        frule polyn_deg_add4[of "f" "-\<^sub>a (g \<cdot>\<^sub>r h)" "deg_n R S X f"],
        rule aGroup.ag_mOp_closed, assumption+) 
  apply (subst deg_an[THEN sym], assumption+, simp del:npow_suc)
  apply (simp add:deg_an[THEN sym], simp del:npow_suc add:deg_an[THEN sym],
         thin_tac "deg R S X (g \<cdot>\<^sub>r h) = deg R S X g + deg R S X h",
         thin_tac "deg R S X g + deg R S X h \<le> deg R S X f",
         thin_tac "deg R S X (-\<^sub>a (g \<cdot>\<^sub>r h)) = deg R S X g + deg R S X h")
(******* deg (t^\<^sup>S\<^sup> \<^sup>m) ra \<le> deg f  done *** next show deg ra \<le> deg f ***)
  apply (frule Ring.npClose[of S t m], assumption,
         frule Idomain.idom_potent_nonzero[of S t m], assumption+,
         frule_tac p = ra in const_times_polyn1[of _ "t^\<^bsup>S m\<^esup>"], assumption+,
         simp del:npow_suc)
(******************  got deg ra \<le> deg f ***********************) 

(******  make g1 and h1 ******)
 
apply (frule_tac h = 
       "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra" in 
       PolynRg.rel_prime_equation[of R' "(S /\<^sub>r (S \<diamondsuit>\<^sub>p t))" "Y" 
        "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g" 
        "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h"], 
       assumption+,
       simp del:npow_suc add:erH_mem, simp del:npow_suc add:erH_mem, 
       assumption+,
       simp del:npow_suc add:erH_mem)
apply (erule bexE, erule bexE, (erule conjE)+,
      frule_tac erH_mem[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y
                     "pj S (S \<diamondsuit>\<^sub>p t)" "g"], assumption+,
      frule_tac erH_mem[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y
                      "pj S (S \<diamondsuit>\<^sub>p t)" "h"], assumption+)
apply (rename_tac ra u' v')
 apply (frule_tac g' = v' in erH_inv[of "S \<diamondsuit>\<^sub>p t" R' Y], assumption+,
        simp add:PolynRg.is_Ring[of R'], assumption+)
apply (frule_tac g' = u' in erH_inv[of "S \<diamondsuit>\<^sub>p t" R' Y ], assumption+,
        simp add:PolynRg.is_Ring[of R'], assumption+)
apply ((erule bexE)+, rename_tac ra u' v' v u, (erule conjE)+) 
apply (
    frule_tac p1 = u in erH_mult[THEN sym, of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y 
        "pj S (S \<diamondsuit>\<^sub>p t)"  _ "g"], assumption+,
    frule_tac p1 = v in erH_mult[THEN sym, of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y
        "pj S (S \<diamondsuit>\<^sub>p t)"  _ "h"], assumption+,
    thin_tac "0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)",
    thin_tac "0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h)",
    thin_tac "rel_prime_pols R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h)")
apply (subgoal_tac "g \<plusminus> (t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r v \<in> carrier R \<and>
         h \<plusminus> (t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r u \<in> carrier R \<and>
         deg R S X (g \<plusminus> (t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r v) \<le>  deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
                          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
                            (pj S (S \<diamondsuit>\<^sub>p t)) (g \<plusminus> (t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r v))  \<and>
         P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) (g \<plusminus> -\<^sub>a (g \<plusminus> (t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r v)) \<and>
         deg R S X (h \<plusminus> (t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r u) +  deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) 
            (g \<plusminus> (t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r v)) \<le> deg R S X f \<and>
         P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) ( h \<plusminus> -\<^sub>a (h \<plusminus> (t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r u)) \<and>
         P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc m)\<^esup>))
         ( f \<plusminus> -\<^sub>a ((g \<plusminus> (t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r v) \<cdot>\<^sub>r (h \<plusminus> (t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r u)))")
apply (thin_tac "deg R S X h +
        deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)
        \<le> deg R S X f",
      thin_tac "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y u'
        \<le> amax
           (deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra) -
            deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g))
           (deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h))",
      thin_tac "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y v' \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
           (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)",
      thin_tac "u' \<cdot>\<^sub>r\<^bsub>R'\<^esub> erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g \<plusminus>\<^bsub>R'\<^esub>
        v' \<cdot>\<^sub>r\<^bsub>R'\<^esub> erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h =
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra",
       thin_tac "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g 
         \<in> carrier R'",
       thin_tac "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h 
          \<in> carrier R'",
       thin_tac "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) v = v'",
       thin_tac "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) u = u'",
       thin_tac "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) u \<cdot>\<^sub>r\<^bsub>R'\<^esub>
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g =
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (u \<cdot>\<^sub>r g)",
       thin_tac "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) v \<cdot>\<^sub>r\<^bsub>R'\<^esub>
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h =
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (v \<cdot>\<^sub>r h)")
 apply blast

apply (frule mem_subring_mem_ring[of "S" "t^\<^bsup>S  m\<^esup>"], assumption)
apply (rule conjI)
 apply (rule aGroup.ag_pOp_closed, assumption+,
        rule ring_tOp_closed, assumption+)
 apply (rule conjI,
        rule aGroup.ag_pOp_closed, assumption+,
        rule ring_tOp_closed, assumption+)

apply (frule Ring.a_in_principal[of "S" "t"], assumption+,
       frule Ring.maximal_ideal_ideal[of "S" "S \<diamondsuit>\<^sub>p t"], assumption+,
       frule Ring.ideal_npow_closed[of "S" "S \<diamondsuit>\<^sub>p t" "t" "m"], assumption+,
       frule PolynRg.is_Ring[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y],
       frule Ring.ring_is_ag[of R'],
       frule erH_rHom[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y "pj S (S \<diamondsuit>\<^sub>p t)"], assumption+)

apply (rule conjI)
apply (frule pHom_dec_deg[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y
      "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))" g], assumption+,
       frule_tac i = "deg R S X v" and j = "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y v'" and 
        k = "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)" in ale_trans,
      assumption, 
      thin_tac "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y u' \<le> amax (deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
            (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra) -
            deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g))
           (deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h))",
       thin_tac "u' \<cdot>\<^sub>r\<^bsub>R'\<^esub> erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g \<plusminus>\<^bsub>R'\<^esub>
        v' \<cdot>\<^sub>r\<^bsub>R'\<^esub> erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h =
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra",
        thin_tac "deg R S X h +
        deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)
        \<le> deg R S X f")
apply (subst P_mod_erH[THEN sym, of "S \<diamondsuit>\<^sub>p t" "R'" "Y" "g" _  "t^\<^bsup>S m\<^esup>"], 
       assumption+,
       thin_tac "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
                (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)
                   \<le> deg R S X g")
apply (frule_tac p = v in const_times_polyn1[of _ "t^\<^bsup>S m\<^esup>"], assumption+,
       frule_tac q = "(t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r v" in polyn_deg_add4[of "g" _ 
          "deg_n R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)"])
 apply (rule ring_tOp_closed, assumption+,
        simp del:npow_suc add:PolynRg.deg_an[THEN sym],
        simp add:PolynRg.deg_an[THEN sym],
        simp add:PolynRg.deg_an[THEN sym]) 

 apply (rule conjI)
 apply (frule Ring.principal_ideal[of S "t^\<^bsup>S m\<^esup>"], assumption+,
        frule Ring.a_in_principal[of S "t^\<^bsup>S m\<^esup>"], assumption+)
 apply (frule_tac y = v in ring_tOp_closed[of "t^\<^bsup>S m\<^esup>"], assumption+,
        subst aGroup.ag_p_inv, assumption+,
        frule aGroup.ag_mOp_closed[of "R" "g"], assumption+,
        frule_tac x = "(t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r v" in aGroup.ag_mOp_closed[of "R"], 
        assumption+)
 apply (subst aGroup.ag_pOp_assoc[THEN sym], assumption+,
        subst aGroup.ag_r_inv1[of "R"], assumption+,
        subst aGroup.ag_l_zero[of "R"], assumption+,
        rule P_mod_minus, assumption+)
 apply (rule_tac g = "(t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r v" in Pmod0_principal_rev[of  
       "t^\<^bsup>S m\<^esup>"], assumption+)
 apply blast

apply (rule conjI)
apply (subst P_mod_erH[THEN sym, of "S \<diamondsuit>\<^sub>p t" R' Y g _ "t^\<^bsup>S m\<^esup>"], assumption+,
       thin_tac "P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) (t^\<^bsup>S m\<^esup> \<cdot>\<^sub>r ra)",
       thin_tac "f \<plusminus> -\<^sub>a (g \<cdot>\<^sub>r h) = t^\<^bsup>S m\<^esup> \<cdot>\<^sub>r ra",
       thin_tac 
        "u' \<cdot>\<^sub>r\<^bsub>R'\<^esub> erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g \<plusminus>\<^bsub>R'\<^esub>
         v' \<cdot>\<^sub>r\<^bsub>R'\<^esub> erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h =
         erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra")
apply (case_tac "
         (deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra) -
          deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)) \<le> 
         (deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h))")   
apply (simp add:amax_def)
apply (frule_tac i = "deg R S X u" and j = "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y u'" and 
       k = "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
           (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h)" in ale_trans, 
          assumption+,
       frule pHom_dec_deg[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y
          "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))" h], assumption+,
       frule_tac i = "deg R S X u" and j = "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
        (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h)" and 
           k = "deg R S X h" in ale_trans, assumption+,
       frule_tac p = u and c = "t^\<^bsup>S m\<^esup>" in const_times_polyn1,
             assumption+)
apply (frule_tac q = "(t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r u" in polyn_deg_add4[of h _  "deg_n R S X h"],
       rule ring_tOp_closed, assumption+,
       subst deg_an[THEN sym], assumption+, rule ale_refl,
       subst deg_an[THEN sym], assumption+,
       simp, frule deg_an[THEN sym, of h], assumption+, simp)
 apply (frule_tac x = "deg R S X ( h \<plusminus> (t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r u)" in aadd_le_mono[of _ 
       "deg R S X h" "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)"],
       rule_tac i = "deg R S X ( h \<plusminus> (t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r u) + (deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t))
         Y (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g))" in  
         ale_trans[of _ "deg R S X h + (deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g))" "deg R S X f"], 
         assumption+)
apply (simp add:amax_def)
apply (thin_tac "\<not> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
           (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra) -
          deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
           (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)
          \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h)")

apply (subst aplus_le_aminus[of _ "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
       (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)" "deg R S X f"])
 apply (rule deg_in_aug_minf,
        rule aGroup.ag_pOp_closed, assumption+,
        rule ring_tOp_closed, assumption+,
        rule PolynRg.deg_in_aug_minf, assumption+,
        rule deg_in_aug_minf, assumption+) 
 
 apply (subst PolynRg.deg_an, assumption+, simp add:minus_an_in_aug_minf,
        frule_tac y = u in ring_tOp_closed[of "t^\<^bsup>S m\<^esup>"], assumption+,
        frule_tac q = "(t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r u" in polyn_deg_add5[of h _ 
         "deg R S X f - deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)"],
         assumption+,
        frule deg_in_aug_minf[of h],
        subst aplus_le_aminus[THEN sym, of "deg R S X h" 
         "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)" 
        "deg R S X f"], assumption+,
        rule PolynRg.deg_in_aug_minf, assumption+,
        rule deg_in_aug_minf, assumption+,
        subst PolynRg.deg_an, assumption+,
        simp add:minus_an_in_aug_minf,
        assumption)

 apply (subst const_times_polyn1, assumption+,
        frule_tac i = "deg R S X u" and j = "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y u'" and
         k = "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
              (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra) -
              deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
               (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)" in 
         ale_trans, assumption+,
        frule_tac p = ra in pHom_dec_deg[of R' "S /\<^sub>r (S \<diamondsuit>\<^sub>p t)" Y
         "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))"], assumption+,
        frule_tac i = "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra)" and 
         j = "deg R S X ra" and k = "deg R S X f" in ale_trans, assumption+,
        frule_tac a = "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
           (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra)" and 
          a' = "deg R S X f" and b = "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)" in
          adiff_le_adiff,
        frule_tac i = "deg R S X u" and j = "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
           (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra) -
           deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
           (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)" and 
          k = "deg R S X f - deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
           (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)" in 
           ale_trans, assumption+)

apply (rule conjI) 
 apply (frule Ring.principal_ideal[of "S" "t^\<^bsup>S m\<^esup>"], assumption+,
        frule Ring.a_in_principal[of "S" "t^\<^bsup>S m\<^esup>"], assumption+,
        frule_tac y = u in ring_tOp_closed[of "t^\<^bsup>S m\<^esup>"], assumption+,
        subst aGroup.ag_p_inv, assumption+,
        frule aGroup.ag_mOp_closed[of "R" "g"], assumption+,
        frule_tac x = "(t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r u" in aGroup.ag_mOp_closed[of "R"], 
          assumption+,
        subst aGroup.ag_pOp_assoc[THEN sym], assumption+,
        rule aGroup.ag_mOp_closed, assumption+,
        subst aGroup.ag_r_inv1[of "R"], assumption+,
        subst aGroup.ag_l_zero[of "R"], assumption+,
        rule P_mod_minus, assumption+,
        rule_tac g = "(t^\<^bsup>S m\<^esup>) \<cdot>\<^sub>r u" in Pmod0_principal_rev[of "t^\<^bsup>S m\<^esup>"], 
         assumption+,
        thin_tac "deg R S X g
           \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
              (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)",
        thin_tac "deg R S X h + deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) \<le> deg R S X f",
        thin_tac "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y u' \<le> amax
           (deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra) -
            deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g))
           (deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h))",
        thin_tac "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y v' \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
           (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)",
        thin_tac "
        u' \<cdot>\<^sub>r\<^bsub>R'\<^esub> erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g \<plusminus>\<^bsub>R'\<^esub>
        v' \<cdot>\<^sub>r\<^bsub>R'\<^esub> erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h =
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) ra",
        thin_tac "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) u \<cdot>\<^sub>r\<^bsub>R'\<^esub>
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g =
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (u \<cdot>\<^sub>r g)",
        thin_tac "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) v \<cdot>\<^sub>r\<^bsub>R'\<^esub>
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h =
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (v \<cdot>\<^sub>r h)")
 apply blast
apply (rule_tac u = u and v = v and ra = ra in P_mod_diffxxx1[of t R' Y f g h],
       assumption+)
apply (rotate_tac -12,
       drule sym, drule sym, simp)
done

(** Hensel_next R S X t R' Y f m gh **) 

definition
  Hensel_next :: "[('a, 'b) Ring_scheme, ('a, 'c) Ring_scheme, 'a, 'a,
 ('a set, 'm) Ring_scheme, 'a set,'a, nat] \<Rightarrow> ('a \<times> 'a) \<Rightarrow> ('a \<times> 'a)"
     ("(9Hen\<^bsub> _ _ _ _ _ _ _\<^esub> _ _)"  [67,67,67,67,67,67,67,68]67) where

 "Hen\<^bsub>R S X t R' Y f \<^esub> m gh = (SOME gh1. 
      gh1 \<in> carrier R \<times> carrier R \<and>
      (deg R S X (fst gh1) \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
      (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst gh1))) \<and> 
  P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) ((fst gh) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (fst gh1)) \<and> 
  (deg R S X (snd gh1) + deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' 
      (S /\<^sub>r (S \<diamondsuit>\<^sub>p  t)) Y (pj S (S \<diamondsuit>\<^sub>p  t)) (fst gh1)) \<le> deg R S X f) \<and>
  P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) ((snd gh) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (snd gh1)) \<and> 
  P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc m)\<^esup>)) (f \<plusminus>\<^bsub>R\<^esub> (-\<^sub>a\<^bsub>R\<^esub> ((fst gh1) \<cdot>\<^sub>r\<^bsub>R\<^esub> (snd gh1)))))"

lemma  cart_prod_fst:"x \<in> A \<times> B \<Longrightarrow> fst x \<in> A" 
by auto

lemma  cart_prod_snd:"x \<in> A \<times> B \<Longrightarrow> snd x \<in> B"
by auto

lemma cart_prod_split:"((x,y) \<in> A \<times> B) = (x \<in> A \<and> y \<in> B)"
by auto

lemma (in PolynRg) P_mod_diffxxx3:"\<lbrakk>Idomain S; t \<in> carrier S; t \<noteq> \<zero>\<^bsub>S\<^esub>; 
   maximal_ideal S (S \<diamondsuit>\<^sub>p t); PolynRg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y; 
   f \<in> carrier R; gh \<in> carrier R \<times> carrier R;
   deg R S X (fst gh) \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' 
                            (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst gh));  
   deg R S X (snd gh) + deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' 
         (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst gh)) \<le> deg R S X f;
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
                                           (pj S (S \<diamondsuit>\<^sub>p t)) (fst gh));
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
       (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (snd gh));
  rel_prime_pols R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
    (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst gh)) 
    (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (snd gh));
  P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) (f \<plusminus> -\<^sub>a ((fst gh) \<cdot>\<^sub>r (snd gh))); 0 < m\<rbrakk> \<Longrightarrow> 
  \<exists>gh1. gh1 \<in>carrier R \<times> carrier R \<and> 
       (deg R S X (fst gh1) \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
           (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst gh1))) \<and> 
   P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) ((fst gh) \<plusminus> -\<^sub>a (fst gh1)) \<and> 
       (deg R S X (snd gh1) + deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
           (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst gh1)) \<le> 
                                                              deg R S X f) \<and>
        P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) ((snd gh) \<plusminus> -\<^sub>a (snd gh1)) \<and> 
        P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc m)\<^esup>)) (f \<plusminus> (-\<^sub>a ((fst gh1) \<cdot>\<^sub>r (snd gh1))))"
apply (cases gh)
apply (simp del: npow_suc)
apply (rename_tac g h)
apply (erule conjE,
        frule_tac g = g and h = h and f = f in P_mod_diffxxx2[of t R' Y],
        assumption+)
apply blast
done

lemma (in PolynRg) P_mod_diffxxx4:"\<lbrakk>Idomain S; t \<in> carrier S; t \<noteq> \<zero>\<^bsub>S\<^esub>; 
      maximal_ideal S (S \<diamondsuit>\<^sub>p t); PolynRg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y; f \<in> carrier R; 
      gh \<in> carrier R \<times> carrier R;
      deg R S X (fst gh) \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
            (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst gh));  
   deg R S X (snd gh) + deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' 
                (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst gh)) \<le> deg R S X f;
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
        (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst gh));
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
        (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (snd gh));
  rel_prime_pols R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
    (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst gh)) 
    (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (snd gh));
  P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) (f \<plusminus> -\<^sub>a ((fst gh) \<cdot>\<^sub>r (snd gh))); 0 < m\<rbrakk> \<Longrightarrow> 
  (Hen\<^bsub>R S X t R' Y f \<^esub> m gh) \<in> carrier R \<times> carrier R  \<and> (deg R S X
     (fst (Hen\<^bsub>R S X t R' Y f \<^esub> m gh)) \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) 
                                   (fst (Hen\<^bsub>R S X t R' Y f \<^esub> m gh)))) \<and> 
  P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) ((fst gh) \<plusminus> -\<^sub>a (fst (Hen\<^bsub>R S X t R' Y f \<^esub> m gh))) \<and> 
  (deg R S X (snd (Hen\<^bsub>R S X t R' Y f \<^esub> m gh)) + deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
   (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) 
        (fst (Hen\<^bsub>R S X t R' Y f \<^esub> m gh))) \<le>  deg R S X f) \<and>
  P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) ((snd gh) \<plusminus> -\<^sub>a (snd (Hen\<^bsub>R S X t R' Y f \<^esub> m gh))) \<and> 
    P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc m)\<^esup>)) (f \<plusminus> (-\<^sub>a ((fst (Hen\<^bsub>R S X t R' Y f \<^esub> m gh)) \<cdot>\<^sub>r 
             (snd (Hen\<^bsub>R S X t R' Y f \<^esub> m gh)))))" 
apply (unfold Hensel_next_def)
apply (rule someI2_ex)
apply (rule P_mod_diffxxx3, assumption+)
done

(* Hensel_pair R S X t R' Y f g h m *)

primrec
  Hensel_pair :: "[('a, 'b) Ring_scheme, ('a, 'c) Ring_scheme, 'a, 'a,
    ('a set, 'm) Ring_scheme, 'a set, 'a, 'a, 'a, nat] \<Rightarrow> ('a \<times> 'a)"
      ("(10Hpr\<^bsub> _ _ _ _ _ _ _ _ _\<^esub> _)"  [67,67,67,67,67,67,67,67,67,68]67)
where
  Hpr_0: "Hpr\<^bsub>R S X t R' Y f g h\<^esub> 0 = (g, h)"
| Hpr_Suc: "Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m) = 
            Hen\<^bsub>R S X t R' Y f \<^esub> (Suc m) (Hpr\<^bsub>R S X t R' Y f g h\<^esub> m)" 

lemma (in PolynRg) fst_xxx:" \<lbrakk>t \<in> carrier S; t \<noteq> \<zero>\<^bsub>S\<^esub>; ideal S (S \<diamondsuit>\<^sub>p t);  
   \<forall>(n::nat). (F n) \<in> carrier R \<times> carrier R; 
   \<forall>m. P_mod R S X (S \<diamondsuit>\<^sub>p t) (fst (F m) \<plusminus> -\<^sub>a (fst (F (Suc m))))\<rbrakk> \<Longrightarrow>
       P_mod R S X (S \<diamondsuit>\<^sub>p t) (fst (F 0) \<plusminus> -\<^sub>a (fst (F n)))"
apply (cut_tac subring, frule subring_Ring,
       cut_tac ring_is_ag) 
apply (induct_tac n)
apply (drule_tac x = 0 in spec)
 apply (frule cart_prod_fst[of "F 0" "carrier R" "carrier R"])
apply (simp add:aGroup.ag_r_inv1) apply (simp add:P_mod_def)

apply (frule_tac x = 0 in spec,
       frule_tac x = n in spec,
       drule_tac x = "Suc n" in spec) 
        
 apply (frule_tac x = "F 0" in cart_prod_fst[of _ "carrier R" "carrier R"],
        frule_tac x = "F n" in cart_prod_fst[of _ "carrier R" "carrier R"],
        frule_tac x = "F (Suc n)" in cart_prod_fst[of _ "carrier R" 
                                                             "carrier R"])
apply (drule_tac x = n in spec)
apply (frule_tac p = "fst (F 0) \<plusminus> -\<^sub>a (fst (F n))" and 
                 q = "fst (F n) \<plusminus> -\<^sub>a (fst (F (Suc n)))" in 
       P_mod_add[of  "S \<diamondsuit>\<^sub>p t"])
apply (rule aGroup.ag_pOp_closed, assumption+, rule aGroup.ag_mOp_closed, 
       assumption+)+
apply (frule_tac x = "fst (F n)" in aGroup.ag_mOp_closed, assumption+,
       frule_tac x = "fst (F (Suc n))" in aGroup.ag_mOp_closed, assumption+)
apply (simp add:aGroup.pOp_assocTr41[of "R", THEN sym],
       simp add:aGroup.pOp_assocTr42[of "R"],
       simp add:aGroup.ag_l_inv1,
       simp add:aGroup.ag_r_zero)
done

lemma (in PolynRg) snd_xxx:"\<lbrakk>t \<in> carrier S; t \<noteq> \<zero>\<^bsub>S\<^esub>;
   ideal S (S \<diamondsuit>\<^sub>p t);  \<forall>(n::nat). (F n) \<in> carrier R \<times> carrier R; 
  \<forall>m. P_mod R S X (S \<diamondsuit>\<^sub>p t) (snd (F m) \<plusminus> -\<^sub>a (snd (F (Suc m))))\<rbrakk> \<Longrightarrow>
   P_mod R S X (S \<diamondsuit>\<^sub>p t) (snd (F 0) \<plusminus> -\<^sub>a (snd (F n)))" 
apply (cut_tac subring, frule subring_Ring,
       cut_tac ring_is_ag) 
apply (induct_tac n)
apply (drule_tac x = 0 in spec)
 apply (frule cart_prod_snd[of "F 0" "carrier R" "carrier R"])
apply (simp add:aGroup.ag_r_inv1) apply (simp add:P_mod_def)

apply (frule_tac x = 0 in spec,
       frule_tac x = n in spec,
       drule_tac x = "Suc n" in spec) 
        
 apply (frule_tac x = "F 0" in cart_prod_snd[of _ "carrier R" "carrier R"],
        frule_tac x = "F n" in cart_prod_snd[of _ "carrier R" "carrier R"],
        frule_tac x = "F (Suc n)" in cart_prod_snd[of _ "carrier R" 
                                                             "carrier R"])
apply (drule_tac x = n in spec)
apply (frule_tac p = "snd (F 0) \<plusminus> -\<^sub>a (snd (F n))" and 
                 q = "snd (F n) \<plusminus> -\<^sub>a (snd (F (Suc n)))" in 
       P_mod_add[of  "S \<diamondsuit>\<^sub>p t"])
apply (rule aGroup.ag_pOp_closed, assumption+, rule aGroup.ag_mOp_closed, 
       assumption+)+
apply (frule_tac x = "snd (F n)" in aGroup.ag_mOp_closed, assumption+,
       frule_tac x = "snd (F (Suc n))" in aGroup.ag_mOp_closed, assumption+)
apply (simp add:aGroup.pOp_assocTr41[of "R", THEN sym],
       simp add:aGroup.pOp_assocTr42[of "R"],
       simp add:aGroup.ag_l_inv1,
       simp add:aGroup.ag_r_zero)
done

lemma (in PolynRg) P_mod_diffxxx5:"\<lbrakk>Idomain S; t \<in> carrier S; t \<noteq> \<zero>\<^bsub>S\<^esub>; 
      maximal_ideal S (S \<diamondsuit>\<^sub>p t); PolynRg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y; 
      f \<in> carrier R; (g, h) \<in> carrier R \<times> carrier R;
     deg R S X (fst (g, h)) \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
       (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst (g, h)));  
  deg R S X (snd (g, h)) + deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
  (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst (g, h))) \<le> deg R S X f;
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
                                        (pj S (S \<diamondsuit>\<^sub>p t)) (fst (g, h)));
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
                                         (pj S (S \<diamondsuit>\<^sub>p t)) (snd (g, h)));
  rel_prime_pols R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
    (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst (g, h))) 
    (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (snd (g, h)));
     P_mod R S X (S \<diamondsuit>\<^sub>p t) (f \<plusminus> -\<^sub>a (g \<cdot>\<^sub>r h))\<rbrakk> \<Longrightarrow> 
  (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m)) \<in> carrier R \<times> carrier R  \<and>
   erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) 
                       (fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m))) =  
            erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst (g, h)) \<and>
   erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) 
                       (snd (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m))) =  
            erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (snd (g, h)) \<and>
     (deg R S X (fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m))) \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) 
                                     (fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m))))) \<and> 
  P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc m)\<^esup>)) ((fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> m)) \<plusminus> -\<^sub>a 
                             (fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m)))) \<and> 
(deg R S X (snd (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m))) + deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
   (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m)))) \<le>  deg R S X f) \<and>
P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc m)\<^esup>)) ((snd (Hpr\<^bsub>R S X t R' Y f g h\<^esub> m)) \<plusminus> -\<^sub>a (snd (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m)))) \<and> 
 P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc (Suc m))\<^esup>)) (f \<plusminus> -\<^sub>a ((fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m))) \<cdot>\<^sub>r (snd (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m)))))"
apply (cut_tac subring, frule subring_Ring,
       cut_tac ring_is_ag,
       frule mem_subring_mem_ring[of S t], assumption+,
       frule Ring.maximal_ideal_ideal[of S "S \<diamondsuit>\<^sub>p t"], assumption+)
apply (induct_tac m)
 apply (simp del:Hpr_0 npow_suc)
 apply (simp only:Hpr_0)
 apply (frule P_mod_diffxxx4[of t R' Y f "(g, h)" "Suc 0"],
           assumption+)
 apply (simp add:cart_prod_split, simp+)
 apply (simp add:Ring.ring_l_one, simp)  
 apply (simp add:Ring.ring_l_one, (erule conjE)+) 
 apply (frule P_mod_diff[THEN sym, of "S \<diamondsuit>\<^sub>p t" R' Y g 
                      "fst (Hen\<^bsub> R S X t R' Y f\<^esub> (Suc 0) (g, h))"], assumption+,
        simp add:cart_prod_fst, rotate_tac -1, drule sym, simp)
 apply (frule P_mod_diff[THEN sym, of "S \<diamondsuit>\<^sub>p t" R' Y h 
                      "snd (Hen\<^bsub> R S X t R' Y f\<^esub> (Suc 0) (g, h))"], assumption+,
        simp add:cart_prod_snd, rotate_tac -1, drule sym, simp) 

apply ((erule conjE)+, rename_tac m)
apply (frule_tac m = "Suc (Suc m)" and gh = "Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc m)" in 
       P_mod_diffxxx4[of t R' Y f], assumption+)
apply (simp, simp, simp, simp del:npow_suc, simp)
apply (erule conjE)+
apply (simp del:npow_suc del:Hpr_Suc 
                add:Hpr_Suc[THEN sym, of R S X t R' Y f _ g h])
apply (thin_tac "deg R S X g
         \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
            (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)",
       thin_tac "deg R S X h +
         deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)
         \<le> deg R S X f",
       thin_tac "0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
              (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)",
       thin_tac "0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
              (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h)",
       thin_tac "rel_prime_pols R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h)",
       thin_tac "deg R S X (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc m))
         \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
            (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)",
       thin_tac "deg R S X (snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc m)) +
         deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)
         \<le> deg R S X f",
       thin_tac "deg R S X (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (Suc m)))
         \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
            (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))
              (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (Suc m))))",
       thin_tac "deg R S X (snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (Suc m))) +
         deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))
            (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (Suc m))))
         \<le> deg R S X f")
apply (frule_tac g = "fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc m)) \<plusminus> -\<^sub>a (fst
       (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc (Suc m))))" and n = "Suc m" in P_mod_n_1
       [of t], assumption+,
       (rule aGroup.ag_pOp_closed, assumption+, simp add:cart_prod_fst,
       rule aGroup.ag_mOp_closed, assumption+, simp add:cart_prod_fst,
       assumption),
       (frule_tac x = "Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc m" in cart_prod_fst[of _ 
       "carrier R" "carrier R"],
       frule_tac x = "Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc (Suc m))" in cart_prod_fst[of _ 
       "carrier R" "carrier R"]),
       (frule_tac g1 = "fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc m))" and 
       h1 = "fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc (Suc m)))" in 
       P_mod_diff[THEN sym, of "S \<diamondsuit>\<^sub>p t" R' Y], assumption+))
apply (frule_tac g = "snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc m)) \<plusminus> -\<^sub>a (snd
       (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc (Suc m))))" and n = "Suc m" in P_mod_n_1
       [of t], assumption+,
       (rule aGroup.ag_pOp_closed, assumption+, simp add:cart_prod_snd,
       rule aGroup.ag_mOp_closed, assumption+, simp add:cart_prod_snd,
       assumption),
       (frule_tac x = "Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc m" in cart_prod_snd[of _ 
       "carrier R" "carrier R"],
       frule_tac x = "Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc (Suc m))" in cart_prod_snd[of _ 
       "carrier R" "carrier R"]),
       (frule_tac g1 = "snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc m))" and 
       h1 = "snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc (Suc m)))" in 
       P_mod_diff[THEN sym, of "S \<diamondsuit>\<^sub>p t" R' Y], assumption+))
apply simp
done

(*** Hensel_pair basic ***)
lemma (in PolynRg) P_mod_diffxxx5_1:"\<lbrakk>Idomain S; t \<in> carrier S; t \<noteq> \<zero>\<^bsub>S\<^esub>; 
  maximal_ideal S (S \<diamondsuit>\<^sub>p t); PolynRg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y; 
  f \<in> carrier R; g \<in> carrier R; h \<in> carrier R;
  deg R S X g \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
             (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g);
  deg R S X h + deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' 
                     (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) \<le> deg R S X f;
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
                (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g);
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
                (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h);
  rel_prime_pols R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
    (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) 
    (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h);
  P_mod R S X (S \<diamondsuit>\<^sub>p t) (f \<plusminus> -\<^sub>a (g \<cdot>\<^sub>r h))\<rbrakk> \<Longrightarrow> 
 (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m)) \<in> carrier R \<times> carrier R  \<and>
 erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) 
     (fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m))) = 
           erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst (g, h)) \<and>
 erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) 
     (snd (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m))) =  
           erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (snd (g, h)) \<and>
     (deg R S X (fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m))) \<le> deg R' 
  (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y  
                    (pj S (S \<diamondsuit>\<^sub>p t)) (fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m))))) \<and> 
 P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc m)\<^esup>)) ((fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> m)) \<plusminus> -\<^sub>a 
                                      (fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m)))) \<and> 
 (deg R S X (snd (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m))) + 
   deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
     (pj S (S \<diamondsuit>\<^sub>p t)) (fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m)))) \<le>  deg R S X f) \<and>
 P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc m)\<^esup>)) ((snd (Hpr\<^bsub>R S X t R' Y f g h\<^esub> m)) \<plusminus> -\<^sub>a 
                                      (snd (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m)))) \<and> 
 P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc (Suc m))\<^esup>)) (f \<plusminus> -\<^sub>a 
  ((fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m))) \<cdot>\<^sub>r (snd (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (Suc m)))))"
apply (frule P_mod_diffxxx5[of t R' Y f g h m], assumption+)
apply (simp add:cart_prod_split, simp, simp, simp, simp, simp, assumption+)
done

(*** Hpr sequence of polynomial pair ***)
lemma (in PolynRg) P_mod_diffxxx5_2:"\<lbrakk>Idomain S; t \<in> carrier S; t \<noteq> \<zero>\<^bsub>S\<^esub>; 
  maximal_ideal S (S \<diamondsuit>\<^sub>p t); PolynRg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y; f \<in> carrier R; 
  g \<in> carrier R; h \<in> carrier R;
  deg R S X g \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
               (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g);  
  deg R S X h + deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' 
                      (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) \<le> deg R S X f;
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
      (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g);
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
      (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h);
  rel_prime_pols R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
    (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) 
    (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h);
  P_mod R S X (S \<diamondsuit>\<^sub>p t) (f \<plusminus> -\<^sub>a (g \<cdot>\<^sub>r h))\<rbrakk> \<Longrightarrow> 
                (Hpr\<^bsub>R S X t R' Y f g h\<^esub> m) \<in> carrier R \<times> carrier R"
apply (case_tac "m = 0", simp, simp) 
apply (frule P_mod_diffxxx5_1[of t R' Y f g h 
       "m - Suc 0"], assumption+) apply (erule conjE)+
apply simp
done

(*** Cauchy 1***)
lemma (in PolynRg) P_mod_diffxxx5_3:"\<lbrakk>Idomain S; t \<in> carrier S; t \<noteq> \<zero>\<^bsub>S\<^esub>; 
  maximal_ideal S (S \<diamondsuit>\<^sub>p t); PolynRg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y; f \<in> carrier R; 
  g \<in> carrier R; h \<in> carrier R;
  deg R S X g \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
      (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g);  
  deg R S X h + deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' 
                (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) \<le> deg R S X f;
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
              (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g);
  0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
              (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h);
  rel_prime_pols R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
    (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) 
    (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h);
  P_mod R S X (S \<diamondsuit>\<^sub>p t) (f \<plusminus> -\<^sub>a (g \<cdot>\<^sub>r h))\<rbrakk> \<Longrightarrow> 
  P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) ((fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> m)) \<plusminus>
                                -\<^sub>a (fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (m + n)))) \<and>
  P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)) ((snd (Hpr\<^bsub>R S X t R' Y f g h\<^esub> m)) \<plusminus>
                                -\<^sub>a (snd (Hpr\<^bsub>R S X t R' Y f g h\<^esub> (m + n))))"
apply (cut_tac ring_is_ag,
       cut_tac subring, frule subring_Ring)
apply (induct_tac n)
 apply (simp del:npow_suc Hpr_Suc) 
 apply (frule P_mod_diffxxx5_2[of t R' Y f g h m], assumption+)
 apply (frule cart_prod_fst[of "Hpr\<^bsub> R S X t R' Y f g h\<^esub> m" "carrier R" "carrier R"],
        frule cart_prod_snd[of "Hpr\<^bsub> R S X t R' Y f g h\<^esub> m" "carrier R" "carrier R"])
 apply (simp add:aGroup.ag_r_inv1, simp add:P_mod_def)

 apply (frule_tac m = "m + n" in P_mod_diffxxx5_1[of t R' Y f g h], 
        assumption+, (erule conjE)+)
apply (frule_tac m = m in P_mod_diffxxx5_2[of t R' Y f g h], assumption+)
apply (frule_tac m = "m + n" in P_mod_diffxxx5_2[of t R' Y f g h], assumption+)
apply (thin_tac "deg R S X g
           \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
              (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)",
       thin_tac "deg R S X h + deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) \<le> deg R S X f",
       thin_tac "0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
              (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)",
       thin_tac "0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
              (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h)",
       thin_tac "rel_prime_pols R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h)",
       thin_tac "P_mod R S X (S \<diamondsuit>\<^sub>p t) ( f \<plusminus> -\<^sub>a (g \<cdot>\<^sub>r h))",
       thin_tac "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))
                            (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m + n))) =
         erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) (fst (g, h))",
       thin_tac "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))
                 (snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m + n))) =
                  erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))
          (snd (g, h))",
       thin_tac "deg R S X (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m + n)))
          \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
            (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))
                      (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m + n))))",
      thin_tac "deg R S X (snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m + n))) +
      deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))
           (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m + n)))) \<le> deg R S X f",
      thin_tac "P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc (Suc (m + n)))\<^esup>))
          (f \<plusminus>  -\<^sub>a (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m + n)) \<cdot>\<^sub>r
                      snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m + n))))")
apply (simp del:npow_suc Hpr_Suc)
apply (frule_tac x = "Hpr\<^bsub> R S X t R' Y f g h\<^esub> m" in 
          cart_prod_fst[of _ "carrier R" "carrier R"],
       frule_tac x = "Hpr\<^bsub> R S X t R' Y f g h\<^esub> (m + n)" in 
          cart_prod_fst[of _ "carrier R" "carrier R"],
       frule_tac x = "Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc (m + n))" in 
          cart_prod_fst[of _ "carrier R" "carrier R"],
       frule_tac x = "Hpr\<^bsub> R S X t R' Y f g h\<^esub> m" in 
          cart_prod_snd[of _ "carrier R" "carrier R"],
       frule_tac x = "Hpr\<^bsub> R S X t R' Y f g h\<^esub> (m + n)" in 
          cart_prod_snd[of _ "carrier R" "carrier R"],
       frule_tac x = "Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc (m + n))" in 
          cart_prod_snd[of _ "carrier R" "carrier R"])
apply (case_tac "m = 0", simp del:npow_suc Hpr_Suc)
 apply (simp only:Ring.Rxa_one)
apply (rule conjI)
apply (rule_tac p = "g \<plusminus> -\<^sub>a (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc n)))" in
       P_mod_whole,
       rule aGroup.ag_pOp_closed, assumption+,
       rule aGroup.ag_mOp_closed, assumption+)
apply (rule_tac p = "h \<plusminus> -\<^sub>a (snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (Suc n)))" in
       P_mod_whole,
       rule aGroup.ag_pOp_closed, assumption+,
       rule aGroup.ag_mOp_closed, assumption+)
apply (frule_tac g = "fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (m + n)) \<plusminus> 
     -\<^sub>a (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m + n)))" and n = "m + n" in 
     P_mod_n_m[of t _ "m - Suc 0"], assumption+)
apply (rule aGroup.ag_pOp_closed, assumption+, rule aGroup.ag_mOp_closed, 
       assumption+,
       arith,
       simp del:npow_suc Hpr_Suc, simp del:npow_suc Hpr_Suc)
apply (frule Ring.npClose[of S t m], assumption,
       frule Ring.principal_ideal[of S "t^\<^bsup>S m\<^esup>"], assumption)
apply (frule_tac p = "fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> m) \<plusminus>
           -\<^sub>a (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (m + n)))" and 
       q = "fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (m + n)) \<plusminus>
           -\<^sub>a (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m + n)))" in 
       P_mod_add[of "S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)"],
      (rule aGroup.ag_pOp_closed, assumption+,
             rule aGroup.ag_mOp_closed, assumption+)+,
      simp del:npow_suc Hpr_Suc add:aGroup.pOp_assoc_cancel)
apply (frule_tac g = "snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (m + n)) \<plusminus> 
     -\<^sub>a (snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m + n)))" and n = "m + n" in 
     P_mod_n_m[of t _ "m - Suc 0"], assumption+)
apply (rule aGroup.ag_pOp_closed, assumption+, rule aGroup.ag_mOp_closed, 
       assumption+,
       arith,
       simp del:npow_suc Hpr_Suc, simp del:npow_suc Hpr_Suc)
apply (frule_tac p = "snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> m) \<plusminus>
           -\<^sub>a (snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (m + n)))" and 
       q = "snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (m + n)) \<plusminus>
           -\<^sub>a (snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m + n)))" in 
       P_mod_add[of "S \<diamondsuit>\<^sub>p (t^\<^bsup>S m\<^esup>)"],
      (rule aGroup.ag_pOp_closed, assumption+,
             rule aGroup.ag_mOp_closed, assumption+)+,
      simp del:npow_suc Hpr_Suc add:aGroup.pOp_assoc_cancel)
done
 
(*** Cauchy, deg bounded ****)
lemma (in PolynRg) P_mod_diffxxx5_4:"\<lbrakk>Idomain S; t \<in> carrier S; t \<noteq> \<zero>\<^bsub>S\<^esub>; 
      maximal_ideal S (S \<diamondsuit>\<^sub>p t); PolynRg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y; f \<in> carrier R; 
  g \<in> carrier R; h \<in> carrier R;
  deg R S X g \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
   (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g);  
  deg R S X h + deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (erH R S X R' 
                (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) \<le> deg R S X f;
    0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
        (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g);
    0 < deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
        (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h);
  rel_prime_pols R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y 
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) 
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h);
  P_mod R S X (S \<diamondsuit>\<^sub>p t) (f \<plusminus> -\<^sub>a (g \<cdot>\<^sub>r h))\<rbrakk> \<Longrightarrow> 
       deg R S X (fst (Hpr\<^bsub>R S X t R' Y f g h\<^esub> m)) \<le> deg R S X g \<and>
       deg R S X (snd (Hpr\<^bsub>R S X t R' Y f g h\<^esub> m)) \<le> deg R S X f" 
apply (cut_tac subring, frule subring_Ring,
       frule Ring.maximal_ideal_ideal[of S "S \<diamondsuit>\<^sub>p t"], assumption)
apply (case_tac "m = 0") apply simp
apply (frule aless_imp_le[of "0" "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)"])
apply (frule aadd_le_mono[of "0" "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
       (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)" "deg R S X h"])
 apply (simp add:aadd_0_l, simp add:aadd_commute[of  _ "deg R S X h"])

 apply (frule P_mod_diffxxx5_1[of t R' Y f g h "m - Suc 0"], 
        assumption+, (erule conjE)+)

apply (thin_tac "deg R S X g
     \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
        (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)")
apply (thin_tac "deg R S X h +  deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
      (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) \<le> deg R S X f") 
apply (thin_tac "rel_prime_pols R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
      (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)
      (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h)",
       thin_tac "P_mod R S X (S \<diamondsuit>\<^sub>p t) ( f \<plusminus> -\<^sub>a (g \<cdot>\<^sub>r h))",
       thin_tac "P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc (m - Suc 0))\<^esup>))
        (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (m - Suc 0)) \<plusminus>
         -\<^sub>a (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m - Suc 0))))",
       thin_tac "P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc (m - Suc 0))\<^esup>))
      ( snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> (m - Suc 0)) \<plusminus>
          -\<^sub>a (snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m - Suc 0))))",
       thin_tac "P_mod R S X (S \<diamondsuit>\<^sub>p (t^\<^bsup>S (Suc (Suc (m - Suc 0)))\<^esup>))
      (f \<plusminus>
       -\<^sub>a (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m - Suc 0)) \<cdot>\<^sub>r
           snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> Suc (m - Suc 0))))")
apply (simp del:npow_suc Hpr_Suc)
 apply (thin_tac "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))
         (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> m)) =
         erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g",
        thin_tac "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))
        (snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> m)) =
        erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) h") 
apply (frule_tac p = g in pHom_dec_deg[of R' "(S /\<^sub>r (S \<diamondsuit>\<^sub>p t))" Y
         "erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t))"]) 
apply (frule Ring.qring_ring[of "S" "S \<diamondsuit>\<^sub>p t"], assumption+)
apply (rule erH_rHom[of R' "(S /\<^sub>r (S \<diamondsuit>\<^sub>p t))" Y "pj S (S \<diamondsuit>\<^sub>p t)"], assumption+,
       simp add:pj_Hom, assumption+)
apply (frule ale_trans[of "deg R S X (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> m))" 
        "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)" "deg R S X g"], 
       assumption+)
apply simp

apply (thin_tac "deg R S X (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> m))
                  \<le> deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
                    (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)",
      thin_tac "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
         (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g) \<le> deg R S X g",
      thin_tac "deg R S X (fst (Hpr\<^bsub> R S X t R' Y f g h\<^esub> m)) \<le> deg R S X g")

apply (frule aless_imp_le[of "0" "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
          (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)"])
apply (frule aadd_le_mono[of "0" "deg R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y
              (erH R S X R' (S /\<^sub>r (S \<diamondsuit>\<^sub>p t)) Y (pj S (S \<diamondsuit>\<^sub>p t)) g)" 
           "deg R S X (snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> m))"])
apply (simp add:aadd_0_l, simp add:aadd_commute[of  _ 
                "deg R S X (snd (Hpr\<^bsub> R S X t R' Y f g h\<^esub> m))"])
done

declare max.absorb1 [simp del] max.absorb2 [simp del]

end
