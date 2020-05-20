(**        Valuation3  
                            author Hidetsune Kobayashi
                            Group You Santo
                            Department of Mathematics
                            Nihon University
                            h_coba@math.cst.nihon-u.ac.jp
                            June 24, 2005
                            July 20, 2007

   chapter 1. elementary properties of a valuation
     section 9. completion 
      subsection Hensel's theorem
   **)

theory Valuation3 
imports Valuation2
begin

section "Completion"

text\<open>In this section we formalize "completion" of the ground field K\<close>

definition
  limit :: "[_, 'b \<Rightarrow> ant, nat \<Rightarrow> 'b, 'b]
           \<Rightarrow> bool" ("(4lim\<^bsub> _ _ \<^esub>_ _)" [90,90,90,91]90) where
  "lim\<^bsub>K v\<^esub> f b \<longleftrightarrow> (\<forall>N. \<exists>M. (\<forall>n. M < n \<longrightarrow> 
                ((f n) \<plusminus>\<^bsub>K\<^esub> (-\<^sub>a\<^bsub>K\<^esub> b)) \<in> (vp K v)\<^bsup> (Vr K v) (an N)\<^esup>))"

(* In this definition, f represents a sequence of elements of K, which is
   converging to b. Key lemmas of this section are n_value_x_1 and
   n_value_x_2 *) 


lemma not_in_singleton_noneq:"x \<notin> {a} \<Longrightarrow> x \<noteq> a"
apply simp
done   (* later move this lemma to Algebra1 *) 

lemma noneq_not_in_singleton:"x \<noteq> a \<Longrightarrow> x \<notin> {a}"
apply simp
done

lemma inf_neq_1[simp]:"\<infinity> \<noteq> 1"
by (simp only:ant_1[THEN sym], rule z_neq_inf[THEN not_sym, of 1])

lemma a1_neq_0[simp]:"(1::ant) \<noteq> 0"
by (simp only:an_1[THEN sym], simp only:an_0[THEN sym],
    subst aneq_natneq[of 1 0], simp)

lemma a1_poss[simp]:"(0::ant) < 1"
by (cut_tac zposs_aposss[of 1], simp)

lemma a_p1_gt[simp]:"\<lbrakk>a \<noteq> \<infinity>; a \<noteq> -\<infinity>\<rbrakk>  \<Longrightarrow> a < a + 1"
apply (cut_tac aadd_poss_less[of a 1],
       simp add:aadd_commute, assumption+) 
apply simp
done

lemma (in Corps) vpr_pow_inter_zero:"valuation K v \<Longrightarrow> 
      (\<Inter> {I. \<exists>n. I = (vp K v)\<^bsup>(Vr K v) (an n)\<^esup>}) = {\<zero>}"
apply (frule Vr_ring[of v], frule vp_ideal[of v])
apply (rule equalityI) 
defer
 apply (rule subsetI)
 apply simp
 apply (rule allI, rule impI, erule exE, simp)
 apply (cut_tac n = "an n" in vp_apow_ideal[of v], assumption+)
 apply simp
 apply (cut_tac I = "(vp K v)\<^bsup> (Vr K v) (an n)\<^esup>" in  Ring.ideal_zero[of "Vr K v"],
        assumption+)
 apply (simp add:Vr_0_f_0)

apply (rule subsetI, simp) 
 apply (rule contrapos_pp, simp+)
 apply (subgoal_tac "x \<in> vp K v")
 prefer 2 
 apply (drule_tac x = "vp K v\<^bsup> (Vr K v) (an 1)\<^esup>" in spec)
 apply (subgoal_tac "\<exists>n. vp K v\<^bsup> (Vr K v) (an (Suc 0))\<^esup> = vp K v\<^bsup> (Vr K v) (an n)\<^esup>", 
        simp,
        thin_tac " \<exists>n. vp K v\<^bsup> (Vr K v) (an (Suc 0))\<^esup> = vp K v\<^bsup> (Vr K v) (an n)\<^esup>")
 apply (simp add:r_apow_def an_def) 
 apply (simp only:na_1)
  apply (simp only:Ring.idealpow_1_self[of "Vr K v" "vp K v"])

  apply blast

apply (frule n_val_valuation[of v])

apply (frule_tac x = x in val_nonzero_z[of "n_val K v"],
       frule_tac h = x in Ring.ideal_subset[of "Vr K v" "vp K v"],
       assumption+,
       simp add:Vr_mem_f_mem, assumption+) apply (
       frule_tac h = x in Ring.ideal_subset[of "Vr K v" "vp K v"],
       simp add:Vr_mem_f_mem, assumption+)
apply (cut_tac x = x in val_pos_mem_Vr[of v], assumption) apply(
       simp add:Vr_mem_f_mem, simp) 
       apply (frule_tac x = x in val_pos_n_val_pos[of v],
       simp add:Vr_mem_f_mem, simp)
apply (cut_tac x = "n_val K v x" and y = 1 in aadd_pos_poss, assumption+,
       simp) apply (frule_tac y = "n_val K v x + 1" in aless_imp_le[of 0])
apply (cut_tac x1 = x and n1 = "(n_val K v x) + 1" in n_val_n_pow[THEN sym, 
       of v], assumption+) 
apply (drule_tac a = "vp K v\<^bsup> (Vr K v) (n_val K v x + 1)\<^esup>" in forall_spec)
apply (erule exE, simp)
apply (simp only:ant_1[THEN sym] a_zpz,
       cut_tac z = "z + 1" in z_neq_inf)
 apply (subst an_na[THEN sym], assumption+, blast)
 apply simp
 apply (cut_tac a = "n_val K v x" in a_p1_gt)
 apply (erule exE, simp only:ant_1[THEN sym], simp only:a_zpz z_neq_inf)
 apply (cut_tac i = "z + 1" and j = z in ale_zle, simp)
 apply (erule exE, simp add:z_neq_minf)
 apply (cut_tac y1 = "n_val K v x" and x1 = "n_val K v x + 1" in 
        aneg_le[THEN sym], simp)
done 

lemma (in Corps) limit_diff_n_val:"\<lbrakk>b \<in> carrier K; \<forall>j. f j \<in> carrier K; 
      valuation K v\<rbrakk> \<Longrightarrow>  (lim\<^bsub>K v\<^esub> f b) = (\<forall>N. \<exists>M. \<forall>n. M < n \<longrightarrow> 
       (an N) \<le> (n_val K v ((f n) \<plusminus> (-\<^sub>a b))))" 
apply (rule iffI)
apply (rule allI)
apply (simp add:limit_def) apply (rotate_tac -1)
 apply (drule_tac x = N in spec)
 apply (erule exE)
apply (subgoal_tac "\<forall>n>M. (an N) \<le> (n_val K v (f n \<plusminus> (-\<^sub>a b)))")
apply blast
 apply (rule allI, rule impI) apply (rotate_tac -2)
 apply (drule_tac x = n in spec, simp) 
 apply (rule n_value_x_1[of v], assumption+,
        simp add:an_nat_pos, assumption)

apply (simp add:limit_def)
 apply (rule allI, rotate_tac -1, drule_tac x = N in spec)

 apply (erule exE)
 apply (subgoal_tac "\<forall>n>M. f n \<plusminus> (-\<^sub>a b) \<in> vp K v \<^bsup>(Vr K v) (an N)\<^esup>")
 apply blast
apply (rule allI, rule impI)
apply (rotate_tac -2, drule_tac x = n in spec, simp)
 apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
 apply (rule_tac x = "f n \<plusminus> -\<^sub>a b" and n = "an N" in n_value_x_2[of "v"],
        assumption+) 
 apply (subst val_pos_mem_Vr[THEN sym, of "v"], assumption+)
 apply (drule_tac x = n in spec)
 apply (rule aGroup.ag_pOp_closed[of "K"], assumption+)
 apply (simp add:aGroup.ag_mOp_closed)
 apply (subst val_pos_n_val_pos[of  "v"], assumption+)
 apply (rule aGroup.ag_pOp_closed, assumption+) apply simp
 apply (simp add:aGroup.ag_mOp_closed)
 apply (rule_tac j = "an N" and k = "n_val K v ( f n \<plusminus> -\<^sub>a b)" in 
        ale_trans[of "0"], simp, assumption+)   
        apply simp 
done

lemma (in Corps) an_na_Lv:"valuation K v \<Longrightarrow> an (na (Lv K v)) = Lv K v" 
apply (frule Lv_pos[of "v"])
apply (frule aless_imp_le[of "0" "Lv K v"])
apply (frule apos_neq_minf[of "Lv K v"])
apply (frule Lv_z[of "v"], erule exE)
apply (rule an_na)
 apply (rule contrapos_pp, simp+)
done

lemma (in Corps) limit_diff_val:"\<lbrakk>b \<in> carrier K; \<forall>j. f j \<in> carrier K; 
      valuation K v\<rbrakk> \<Longrightarrow>  (lim\<^bsub>K v\<^esub> f b) = (\<forall>N. \<exists>M. \<forall>n. M < n \<longrightarrow> 
             (an N) \<le> (v ((f n) \<plusminus> (-\<^sub>a b))))" 
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       simp add:limit_diff_n_val[of "b" "f" "v"])
apply (rule iffI)
 apply (rule allI,
   rotate_tac -1, drule_tac x = N in spec, erule exE) 
 apply (subgoal_tac "\<forall>n > M. an N \<le> v( f n \<plusminus> -\<^sub>a b)", blast)
 apply (rule allI, rule impI)
 apply (drule_tac x = n in spec,
        drule_tac x = n in spec, simp) 
 apply (frule aGroup.ag_mOp_closed[of "K" "b"], assumption+,
     frule_tac x = "f n" and y = "-\<^sub>a b" in aGroup.ag_pOp_closed, assumption+)
 apply (frule_tac x = "f n \<plusminus> -\<^sub>a b" in n_val_le_val[of "v"], 
         assumption+)
 apply (cut_tac n = N in an_nat_pos)
 apply (frule_tac j = "an N" and k = "n_val K v ( f n \<plusminus> -\<^sub>a b)" in 
                   ale_trans[of "0"], assumption+)
 apply (subst val_pos_n_val_pos, assumption+)
 apply (rule_tac i = "an N" and j = "n_val K v ( f n \<plusminus> -\<^sub>a b)" and 
        k = "v ( f n \<plusminus> -\<^sub>a b)" in ale_trans, assumption+)
 apply (rule allI)
 apply (rotate_tac 3, drule_tac x = "N * (na (Lv K v))" in spec)
 apply (erule exE)
 apply (subgoal_tac "\<forall>n. M < n \<longrightarrow> (an N) \<le> n_val K v (f n \<plusminus> -\<^sub>a b)", blast)
 apply (rule allI, rule impI)
 apply (rotate_tac -2, drule_tac x = n in spec, simp)

  apply (drule_tac x = n in spec)
  apply (frule aGroup.ag_mOp_closed[of "K" "b"], assumption+,
      frule_tac x = "f n" and y = "-\<^sub>a b" in aGroup.ag_pOp_closed, assumption+)
 apply (cut_tac n = "N * na (Lv K v)" in an_nat_pos)
 apply (frule_tac i = 0 and j = "an (N * na (Lv K v))" and 
                  k = "v ( f n \<plusminus> -\<^sub>a b)" in ale_trans, assumption+)
 apply (simp add:amult_an_an, simp add:an_na_Lv)
 apply (frule Lv_pos[of "v"])
 apply (frule_tac x1 = "f n \<plusminus> -\<^sub>a b" in n_val[THEN sym, of v], 
        assumption+, simp)
 apply (frule Lv_z[of v], erule exE, simp)
 apply (simp add:amult_pos_mono_r)
done

text\<open>uniqueness of the limit is derived from \<open>vp_pow_inter_zero\<close>\<close>
lemma (in Corps) limit_unique:"\<lbrakk>b \<in> carrier K; \<forall>j. f j \<in> carrier K; 
      valuation K v;  c \<in> carrier K; lim\<^bsub>K v\<^esub> f b; lim\<^bsub>K v\<^esub> f c\<rbrakk> \<Longrightarrow>  b = c" 
apply (rule contrapos_pp, simp+, simp add:limit_def,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       simp add:aGroup.ag_neq_diffnonzero[of "K" "b" "c"], 
       frule vpr_pow_inter_zero[THEN sym, of v], 
       frule noneq_not_in_singleton[of "b \<plusminus> -\<^sub>a c" "\<zero>"])
apply simp
apply (rotate_tac -1, erule exE, erule conjE)
apply (erule exE, simp, thin_tac "x = (vp K v)\<^bsup>(Vr K v) (an n)\<^esup>")
apply (rotate_tac 3, drule_tac x = n in spec,
       erule exE,
       drule_tac x = n in spec,
       erule exE)
apply (rename_tac x N M1 M2)
apply (subgoal_tac "M1 < Suc (max M1 M2)",
       subgoal_tac "M2 < Suc (max M1 M2)",
       drule_tac x = "Suc (max M1 M2)" in spec,
       drule_tac x = "Suc (max M1 M2)" in spec,
       drule_tac x = "Suc (max M1 M2)" in spec)
 apply simp

(* We see (f (Suc (max xb xc)) +\<^sub>K -\<^sub>K b) +\<^sub>K (-\<^sub>K (f (Suc (max xb xc)) +\<^sub>K -\<^sub>K c)) \<in> vpr K G a i v \<^bsup>\<diamondsuit>Vr K G a i v xa\<^esup>" *) 
 apply (frule_tac n = "an N" in vp_apow_ideal[of "v"], 
       frule_tac x = "f (Suc (max M1 M2)) \<plusminus> -\<^sub>a b" and N = "an N" in 
       mem_vp_apow_mem_Vr[of "v"], simp,
       frule Vr_ring[of "v"],  simp, simp)
      
apply (frule Vr_ring[of "v"], 
       frule_tac I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" and x = "f (Suc (max M1 M2)) \<plusminus> -\<^sub>a b"
       in Ring.ideal_inv1_closed[of "Vr K v"], assumption+)
 (** mOp of Vring and that of K is the same **)
apply (frule_tac I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" and h = "f (Suc (max M1 M2)) \<plusminus> -\<^sub>a b"
 in Ring.ideal_subset[of "Vr K v"], assumption+)
 apply (simp add:Vr_mOp_f_mOp,
        cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
        frule aGroup.ag_mOp_closed[of "K" "b"], assumption+,
        simp add:aGroup.ag_p_inv, simp add:aGroup.ag_inv_inv)
 (** addition of  -\<^sub>K f (Suc (max xb xc)) +\<^sub>K b  and f (Suc (max xb xc)) +\<^sub>K -\<^sub>K c
    is included in vpr K G a i v \<^bsup>\<diamondsuit>(Vr K G a i v) xa\<^esup> **)
 apply (frule_tac  I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" and x = 
 "-\<^sub>a (f (Suc (max M1 M2))) \<plusminus> b " and y = "f (Suc (max M1 M2)) \<plusminus> (-\<^sub>a c)" in 
  Ring.ideal_pOp_closed[of "Vr K v"], assumption+)
 apply (frule_tac x = "f (Suc (max M1 M2)) \<plusminus> -\<^sub>a c" and N = "an N" in 
        mem_vp_apow_mem_Vr[of v], simp, assumption,
        frule_tac x = "-\<^sub>a (f (Suc (max M1 M2))) \<plusminus> b" and N = "an N" in 
        mem_vp_apow_mem_Vr[of "v"], simp,
        simp add:Vr_pOp_f_pOp, simp add:Vr_pOp_f_pOp,
   frule aGroup.ag_mOp_closed[of "K" "c"], assumption+,
   frule_tac x = "f (Suc (max M1 M2))" in aGroup.ag_mOp_closed[of "K"], 
      assumption+,
   frule_tac x = "f (Suc (max M1 M2))" and y = "-\<^sub>a c" in 
      aGroup.ag_pOp_closed[of "K"], assumption+) 

apply (simp add:aGroup.ag_pOp_assoc[of "K" _ "b" _],
       simp add:aGroup.ag_pOp_assoc[THEN sym, of "K" "b" _ "-\<^sub>a c"],
       simp add:aGroup.ag_pOp_commute[of "K" "b"],
       simp add:aGroup.ag_pOp_assoc[of "K" _ "b" "-\<^sub>a c"],
       frule aGroup.ag_pOp_closed[of "K" "b" "-\<^sub>a c"], assumption+,
       simp add:aGroup.ag_pOp_assoc[THEN sym, of "K" _ _ "b \<plusminus> -\<^sub>a c"],
       simp add:aGroup.ag_l_inv1, simp add:aGroup.ag_l_zero)
apply (simp add:aGroup.ag_pOp_commute[of "K" _ "b"])
apply arith apply arith
done


(** The following lemma will be used to prove lemma limit_t. This lemma and
 them next lemma show that the valuation v is continuous (see lemma 
 n_val **) 
lemma (in Corps) limit_n_val:"\<lbrakk>b \<in> carrier K; b \<noteq> \<zero>; valuation K v; 
       \<forall>j. f j \<in> carrier K; lim\<^bsub>K v\<^esub> f b\<rbrakk> \<Longrightarrow>
       \<exists>N. (\<forall>m. N < m \<longrightarrow> (n_val K v) (f m) = (n_val K v) b)"
apply (simp add:limit_def)
apply (frule n_val_valuation[of "v"])
apply (frule val_nonzero_z[of "n_val K v" "b"], assumption+, erule exE,
       rename_tac L)
apply (rotate_tac -3, drule_tac x = "nat (abs L + 1)" in spec)
apply (erule exE, rename_tac M)

    (* |L| + 1 \<le> (n_val K v ( f n +\<^sub>K -\<^sub>K b)). *) 
 apply (subgoal_tac "\<forall>n. M < n \<longrightarrow> n_val K v (f n) = n_val K v b", blast)
 apply (rule allI, rule impI) 
 apply (rotate_tac -2, 
        drule_tac x = n in spec,
        simp)
apply (frule_tac x = "f n \<plusminus> -\<^sub>a b" and n = "an (nat (\<bar>L\<bar> + 1))" in 
       n_value_x_1[of "v"],
       thin_tac "f n \<plusminus> -\<^sub>a b \<in> vp K v\<^bsup>(Vr K v) (an (nat (\<bar>L\<bar> + 1)))\<^esup>")
apply (simp add:an_def) 
 apply (simp add: zpos_apos [symmetric])
 apply assumption

 apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
 apply (frule aGroup.ag_mOp_closed[of "K" "b"], assumption+)
 
 apply (drule_tac x = n in spec, 
        frule_tac x = "f n" in aGroup.ag_pOp_closed[of "K" _ "-\<^sub>a b"], 
        assumption+,  
        frule_tac x = "b" and y = "(f n) \<plusminus> (-\<^sub>a b)" in value_less_eq[of 
        "n_val K v"], assumption+)
 apply simp 
 apply (rule_tac x = "ant L" and y = "an (nat (\<bar>L\<bar> + 1))" and 
        z = "n_val K v ( f n \<plusminus> -\<^sub>a b)" in aless_le_trans)
 apply (subst an_def)
 apply (subst aless_zless) apply arith apply assumption+
 apply (simp add:aGroup.ag_pOp_commute[of "K" "b"])
 apply (simp add:aGroup.ag_pOp_assoc) apply (simp add:aGroup.ag_l_inv1)
 apply (simp add:aGroup.ag_r_zero)
done 

lemma (in Corps) limit_val:"\<lbrakk>b \<in> carrier K; b \<noteq> \<zero>; \<forall>j. f j \<in> carrier K; 
      valuation K v; lim\<^bsub>K v\<^esub> f b\<rbrakk> \<Longrightarrow> \<exists>N. (\<forall>n. N < n \<longrightarrow> v (f n) = v b)"
apply (frule limit_n_val[of "b" "v" "f"], assumption+)
 apply (erule exE)
 apply (subgoal_tac "\<forall>m. N < m \<longrightarrow> v (f m) = v b")
 apply blast
apply (rule allI, rule impI)
 apply (drule_tac x = m in spec)
 apply (drule_tac x = m in spec)
  apply simp
 apply (frule Lv_pos[of "v"])
 apply (simp add:n_val[THEN sym, of "v"])
done

lemma (in Corps) limit_val_infinity:"\<lbrakk>valuation K v; \<forall>j. f j \<in> carrier K; 
      lim\<^bsub>K v\<^esub> f \<zero>\<rbrakk> \<Longrightarrow> \<forall>N.(\<exists>M. (\<forall>m. M < m \<longrightarrow> (an N) \<le> (n_val K v (f m))))"
apply (simp add:limit_def)
 apply (rule allI)
 apply (drule_tac x = N in spec, 
        erule exE)
       
 apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
        simp only:aGroup.ag_inv_zero[of "K"], simp only:aGroup.ag_r_zero)
apply (subgoal_tac "\<forall>n. M < n \<longrightarrow> an N \<le> n_val K v (f n)", blast)

 apply (rule allI, rule impI)
 apply (drule_tac x = n in spec,
        drule_tac x = n in spec, simp)
 apply (simp add:n_value_x_1)
done

lemma (in Corps) not_limit_zero:"\<lbrakk>valuation K v; \<forall>j. f j \<in> carrier K; 
      \<not> (lim\<^bsub>K v\<^esub> f \<zero>)\<rbrakk> \<Longrightarrow> \<exists>N.(\<forall>M. (\<exists>m. (M < m) \<and> 
                                    ((n_val K v) (f m)) < (an N)))"
apply (simp add:limit_def)
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
apply (simp add:aGroup.ag_inv_zero aGroup.ag_r_zero)
apply (erule exE)
 apply (case_tac "N = 0", simp add:r_apow_def) 
 apply (subgoal_tac "\<forall>M. \<exists>n. M < n \<and> n_val K v (f n) < (an 0)") apply blast
 apply (rule allI, 
        rotate_tac 4, frule_tac x = M in spec,
        erule exE, erule conjE)
 apply (frule_tac x1 = "f n" in val_pos_mem_Vr[THEN sym, of "v"]) apply simp 
 apply simp
 apply (frule_tac x = "f n" in val_pos_n_val_pos[of "v"])
 apply simp apply simp apply (thin_tac "\<not> 0 \<le> v (f n)")
 apply (simp add:aneg_le) apply blast

apply (simp)
 apply (subgoal_tac "\<forall>n. ((f n) \<in> vp K v\<^bsup> (Vr K v) (an N)\<^esup>) = 
                                ((an N) \<le> n_val K v (f n))")
 apply simp
 apply (thin_tac "\<forall>n. (f n \<in> vp K v\<^bsup> (Vr K v) (an N)\<^esup>) = (an N \<le> n_val K v (f n))")
 apply (simp add:aneg_le) apply blast

apply (rule allI)
 apply (thin_tac "\<forall>M. \<exists>n. M < n \<and> f n \<notin> vp K v\<^bsup> (Vr K v) (an N)\<^esup>")
 apply (rule iffI)
 apply (frule_tac x1 = "f n" and n1 = "an N" in n_val_n_pow[THEN sym, of v])
 apply (rule_tac N = "an N" and x = "f n" in mem_vp_apow_mem_Vr[of v],
        assumption+, simp, assumption, simp, simp)
 apply (frule_tac x = "f n" and n = "an N" in n_val_n_pow[of "v"])
 apply (frule_tac x1 = "f n" in val_pos_mem_Vr[THEN sym, of "v"])
 apply simp
 apply (cut_tac n = N in an_nat_pos) 
 apply (frule_tac j = "an N" and k = "n_val K v (f n)" in ale_trans[of "0"],
         assumption+)
 apply (frule_tac x1 = "f n" in val_pos_n_val_pos[THEN sym, of "v"]) 
 apply simp+ 
done

lemma (in Corps) limit_p:"\<lbrakk>valuation K v; \<forall>j. f j  \<in> carrier K; 
   \<forall>j. g j \<in> carrier K; b \<in> carrier K; c \<in> carrier K; lim\<^bsub>K v\<^esub> f b; lim\<^bsub>K v\<^esub> g c\<rbrakk>
   \<Longrightarrow> lim\<^bsub>K v\<^esub> (\<lambda>j. (f j) \<plusminus> (g j)) (b \<plusminus> c)"
apply (simp add:limit_def)
 apply (rule allI) apply (rotate_tac 3,
       drule_tac x = N in spec,
       drule_tac x = N in spec,
       (erule exE)+) 
 apply (frule_tac x = M and y = Ma in two_inequalities, simp,
        subgoal_tac "\<forall>n > (max M  Ma). (f n) \<plusminus> (g n) \<plusminus> -\<^sub>a (b \<plusminus> c)
        \<in> (vp K v)\<^bsup>(Vr K v) (an N)\<^esup>")
 apply (thin_tac "\<forall>n. Ma < n \<longrightarrow> 
                     g n \<plusminus> -\<^sub>a c \<in> (vp K v)\<^bsup>(Vr K v) (an N)\<^esup>",
        thin_tac "\<forall>n. M < n \<longrightarrow> 
                      f n \<plusminus> -\<^sub>a b \<in>(vp K v)\<^bsup>(Vr K v) (an N)\<^esup>", blast)
 apply (frule Vr_ring[of v], 
        frule_tac n = "an N" in vp_apow_ideal[of v])
apply simp 
 apply (rule allI, rule impI)
 apply (thin_tac "\<forall>n>M. f n \<plusminus> -\<^sub>a b \<in> vp K v\<^bsup> (Vr K v) (an N)\<^esup>",
        thin_tac "\<forall>n>Ma. g n \<plusminus> -\<^sub>a c \<in> vp K v\<^bsup> (Vr K v) (an N)\<^esup>",
        frule_tac I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" and x = "f n \<plusminus> -\<^sub>a b" 
        and y = "g n \<plusminus> -\<^sub>a c" in Ring.ideal_pOp_closed[of "Vr K v"], 
        assumption+, simp, simp) 
apply (frule_tac I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" and h = "f n \<plusminus> -\<^sub>a b" 
        in Ring.ideal_subset[of "Vr K v"], assumption+, simp,
        frule_tac I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" and h = "g n \<plusminus> -\<^sub>a c" in
                   Ring.ideal_subset[of "Vr K v"], assumption+, simp)
 apply (simp add:Vr_pOp_f_pOp) 
 apply (thin_tac "f n \<plusminus> -\<^sub>a b \<in> carrier (Vr K v)",
        thin_tac "g n \<plusminus> -\<^sub>a c \<in> carrier (Vr K v)")

 apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
        frule aGroup.ag_mOp_closed[of "K" "b"], assumption+,
        frule aGroup.ag_mOp_closed[of "K" "c"], assumption+,
        frule_tac a = "f n" and b = "-\<^sub>a b" and c = "g n" and d = "-\<^sub>a c" in 
                  aGroup.ag_add4_rel[of "K"], simp+)
 apply (simp add:aGroup.ag_p_inv[THEN sym]) 
done

lemma (in Corps) Abs_ant_abs[simp]:"Abs (ant z) = ant (abs z)"
apply (simp add:Abs_def, simp add:aminus)
apply (simp only:ant_0[THEN sym], simp only:aless_zless)
apply (simp add:zabs_def)
done

lemma (in Corps) limit_t_nonzero:"\<lbrakk>valuation K v; \<forall>(j::nat). (f j) \<in> carrier K; \<forall>(j::nat). g j \<in> carrier K;  b \<in> carrier K; c \<in> carrier K; b \<noteq> \<zero>; c \<noteq> \<zero>;
 lim\<^bsub>K v\<^esub> f b; lim\<^bsub>K v\<^esub> g c\<rbrakk> \<Longrightarrow> lim\<^bsub>K v\<^esub> (\<lambda>j. (f j) \<cdot>\<^sub>r (g j)) (b \<cdot>\<^sub>r c)"
apply (cut_tac field_is_ring, simp add:limit_def, rule allI) 
 apply (subgoal_tac "\<forall>j. (f j) \<cdot>\<^sub>r (g j) \<plusminus> -\<^sub>a (b \<cdot>\<^sub>r c) = 
 ((f j) \<cdot>\<^sub>r (g j) \<plusminus> (f j) \<cdot>\<^sub>r (-\<^sub>a c)) \<plusminus> ((f j) \<cdot>\<^sub>r c \<plusminus> -\<^sub>a (b \<cdot>\<^sub>r c))", simp,
 thin_tac "\<forall>j. f j \<cdot>\<^sub>r g j \<plusminus> -\<^sub>a b \<cdot>\<^sub>r c =
             f j \<cdot>\<^sub>r g j \<plusminus> f j \<cdot>\<^sub>r (-\<^sub>a c) \<plusminus> (f j \<cdot>\<^sub>r c \<plusminus> -\<^sub>a b \<cdot>\<^sub>r c)")
 apply (frule limit_n_val[of  "b" "v" "f"], assumption+,
        simp add:limit_def)
 apply (frule n_val_valuation[of "v"])
 apply (frule val_nonzero_z[of "n_val K v" "b"], assumption+, 
        rotate_tac -1, erule exE,
        frule val_nonzero_z[of "n_val K v" "c"], assumption+,
        rotate_tac -1, erule exE, rename_tac N bz cz)
 apply (rotate_tac 5, 
  drule_tac x = "N + nat (abs cz)" in spec, 
  drule_tac x = "N + nat (abs bz)" in spec)
  apply (erule exE)+ 
  apply (rename_tac N bz cz M M1 M2)
(** three inequalities together **)
apply (subgoal_tac "\<forall>n. (max (max M1 M2) M) < n \<longrightarrow>
 (f n) \<cdot>\<^sub>r (g n) \<plusminus> (f n) \<cdot>\<^sub>r (-\<^sub>a c) \<plusminus> ((f n) \<cdot>\<^sub>r c \<plusminus> (-\<^sub>a (b \<cdot>\<^sub>r c)))
                  \<in> vp K v \<^bsup>(Vr K v) (an N)\<^esup>",  blast)
apply (rule allI, rule impI) apply (simp, (erule conjE)+) 
 apply (rotate_tac 11, drule_tac x = n in spec,
      drule_tac x = n in spec, simp,
      drule_tac x = n in spec, simp)
 apply (frule_tac b = "g n \<plusminus> -\<^sub>a c" and n = "an N" and x = "f n" in 
        convergenceTr1[of v])
 apply simp apply simp apply (simp add:an_def a_zpz[THEN sym]) apply simp
 apply (frule_tac b = "f n \<plusminus> -\<^sub>a b" and n = "an N" in convergenceTr1[of  
  "v" "c"], assumption+, simp) apply (simp add:an_def)
   apply (simp add:a_zpz[THEN sym]) apply simp

 apply (drule_tac x = n in spec, 
        drule_tac x = n in spec)
 apply (simp add:Ring.ring_inv1_1[of "K" "b" "c"],
        cut_tac Ring.ring_is_ag, frule aGroup.ag_mOp_closed[of "K" "c"], 
        assumption+,
        simp add:Ring.ring_distrib1[THEN sym],
        frule aGroup.ag_mOp_closed[of "K" "b"], assumption+,
        simp add:Ring.ring_distrib2[THEN sym],
        subst Ring.ring_tOp_commute[of "K" _ "c"], assumption+,
        rule aGroup.ag_pOp_closed, assumption+) 
apply (cut_tac n = N in an_nat_pos)
apply (frule_tac n = "an N" in vp_apow_ideal[of "v"], assumption+)
apply (frule Vr_ring[of "v"]) 

apply (frule_tac x = "(f n) \<cdot>\<^sub>r (g n \<plusminus> -\<^sub>a c)" and y = "c \<cdot>\<^sub>r (f n \<plusminus> -\<^sub>a b)"
   and I = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" in Ring.ideal_pOp_closed[of "Vr K v"], 
   assumption+)
apply (frule_tac R = "Vr K v" and I = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and 
       h = "(f n) \<cdot>\<^sub>r (g n \<plusminus> -\<^sub>a c)" in Ring.ideal_subset, assumption+,
       frule_tac R = "Vr K v" and I = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and 
       h = "c \<cdot>\<^sub>r (f n \<plusminus> -\<^sub>a b)" in Ring.ideal_subset, assumption+) 
apply (simp add:Vr_pOp_f_pOp, assumption+)
apply (rule allI)
 apply (thin_tac "\<forall>N. \<exists>M. \<forall>n>M. f n \<plusminus> -\<^sub>a b \<in> vp K v\<^bsup> (Vr K v) (an N)\<^esup>",
        thin_tac "\<forall>N. \<exists>M. \<forall>n>M. g n \<plusminus> -\<^sub>a c \<in> vp K v\<^bsup> (Vr K v) (an N)\<^esup>")
 apply (drule_tac x = j in spec,
        drule_tac x = j in spec,
        cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule_tac x = "f j" and y = "g j" in Ring.ring_tOp_closed, assumption+,
       frule_tac x = "b" and y = "c" in Ring.ring_tOp_closed, assumption+,
       frule_tac x = "f j" and y = "c" in Ring.ring_tOp_closed, assumption+,
       frule_tac x = c in aGroup.ag_mOp_closed[of "K"], assumption+,
       frule_tac x = "f j" and y = "-\<^sub>a c" in Ring.ring_tOp_closed, assumption+,
       frule_tac x = "b \<cdot>\<^sub>r c" in aGroup.ag_mOp_closed[of "K"], assumption+)
 apply (subst aGroup.pOp_assocTr41[THEN sym, of "K"], assumption+,
        subst aGroup.pOp_assocTr42[of "K"], assumption+,
        subst Ring.ring_distrib1[THEN sym, of "K"], assumption+)
 apply (simp add:aGroup.ag_l_inv1, simp add:Ring.ring_times_x_0, 
        simp add:aGroup.ag_r_zero)
done

lemma an_npn[simp]:"an (n + m) = an n + an m"
by (simp add:an_def a_zpz) (** move **) 

lemma Abs_noninf:"a \<noteq> -\<infinity> \<and> a \<noteq> \<infinity> \<Longrightarrow> Abs a \<noteq> \<infinity>"
by (cut_tac mem_ant[of "a"], simp, erule exE, simp add:Abs_def,
       simp add:aminus)

lemma (in Corps) limit_t_zero:"\<lbrakk>c \<in> carrier K; valuation K v; 
      \<forall>(j::nat). f j \<in> carrier K; \<forall>(j::nat). g j \<in> carrier K;
      lim\<^bsub>K v\<^esub> f \<zero>; lim\<^bsub>K v\<^esub> g c\<rbrakk> \<Longrightarrow> lim\<^bsub>K v\<^esub> (\<lambda>j. (f j) \<cdot>\<^sub>r (g j)) \<zero>"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"], 
       simp add:limit_def, simp add:aGroup.ag_inv_zero, simp add:aGroup.ag_r_zero)
apply (subgoal_tac "\<forall>j. (f j) \<cdot>\<^sub>r (g j) \<in> carrier K",
       simp add:aGroup.ag_r_zero)
 prefer 2 apply (rule allI, simp add:Ring.ring_tOp_closed)
apply (case_tac "c = \<zero>\<^bsub>K\<^esub>")
 apply (simp add:aGroup.ag_inv_zero, simp add:aGroup.ag_r_zero)
 apply (rule allI,
        rotate_tac 4,
        drule_tac x = N in spec,
        drule_tac x = N in spec, (erule exE)+,
        rename_tac N M1 M2)
 apply (subgoal_tac "\<forall>n>(max M1 M2). (f n) \<cdot>\<^sub>r (g n) \<in> (vp K v)\<^bsup>(Vr K v) (an N)\<^esup>", 
        blast) 
 apply (rule allI, rule impI)
 apply (drule_tac x = M1 and y = M2 in two_inequalities, assumption+,
        thin_tac "\<forall>n>M2. g n \<in> vp K v\<^bsup> (Vr K v) (an N)\<^esup>")
apply (thin_tac "\<forall>j. f j \<cdot>\<^sub>r g j \<in> carrier K",
       thin_tac "\<forall>j. f j \<in> carrier K",
       thin_tac "\<forall>j. g j \<in> carrier K",
       drule_tac x = n in spec, simp, erule conjE,
       erule conjE,
       frule Vr_ring[of v])
 apply (cut_tac n = N in an_nat_pos) 
 apply (frule_tac x = "f n" in mem_vp_apow_mem_Vr[of  "v"], assumption+,
        frule_tac x = "g n" in mem_vp_apow_mem_Vr[of  "v"], assumption+,
       frule_tac n = "an N" in vp_apow_ideal[of  "v"], assumption+)
 apply (frule_tac I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" and x = "g n" and 
        r = "f n" in Ring.ideal_ring_multiple[of "Vr K v"], assumption+,
        simp add:Vr_tOp_f_tOp)


 (** case c \<noteq> 0\<^sub>K **)
 apply (rule allI)
 apply (subgoal_tac "\<forall>j. (f j) \<cdot>\<^sub>r (g j) = 
        (f j) \<cdot>\<^sub>r ((g j) \<plusminus> (-\<^sub>a c)) \<plusminus> (f j) \<cdot>\<^sub>r c", simp,
        thin_tac "\<forall>j. (f j) \<cdot>\<^sub>r (g j) = 
        (f j) \<cdot>\<^sub>r ((g j) \<plusminus> (-\<^sub>a c)) \<plusminus> (f j) \<cdot>\<^sub>r c",
        thin_tac "\<forall>j.  (f j) \<cdot>\<^sub>r ( g j \<plusminus> -\<^sub>a c) \<plusminus> (f j) \<cdot>\<^sub>r c \<in> carrier K")
apply (rotate_tac 4,
       drule_tac x = "N + na (Abs (n_val K v c))" in  spec,
       drule_tac x = N in spec)
 apply (erule exE)+ apply (rename_tac N M1 M2)
apply (subgoal_tac "\<forall>n. (max M1 M2) < n \<longrightarrow> (f n) \<cdot>\<^sub>r (g n \<plusminus> -\<^sub>a c) \<plusminus> 
                     (f n) \<cdot>\<^sub>r  c \<in> vp K v\<^bsup>(Vr K v) (an N)\<^esup>", blast)
apply (rule allI, rule impI, simp, erule conjE,
      drule_tac x = n in spec,
      drule_tac x = n in spec,
      drule_tac x = n in spec) 
apply (frule n_val_valuation[of "v"])
apply (frule value_in_aug_inf[of "n_val K v" "c"], assumption+, 
       simp add:aug_inf_def)
apply (frule val_nonzero_noninf[of "n_val K v" "c"], assumption+)
apply (cut_tac Abs_noninf[of "n_val K v c"])
apply (cut_tac Abs_pos[of "n_val K v c"]) apply (simp add:an_na)

apply (drule_tac x = n in spec, simp)
 apply (frule_tac b = "f n" and n = "an N" in convergenceTr1[of 
                                   "v" "c"], assumption+)
 apply simp

apply (frule_tac x = "f n" and N = "an N + Abs (n_val K v c)" in 
       mem_vp_apow_mem_Vr[of "v"], 
       frule_tac n = "an N" in vp_apow_ideal[of "v"])
      apply simp
apply (rule_tac x = "an N" and y = "Abs (n_val K v c)" in aadd_two_pos)
    apply simp apply (simp add:Abs_pos) apply assumption
   
apply (frule_tac x = "g n \<plusminus> (-\<^sub>a c)" and N = "an N" in mem_vp_apow_mem_Vr[of 
       "v"], simp, assumption+) apply (
       frule_tac x = "c \<cdot>\<^sub>r (f n)" and N = "an N" in mem_vp_apow_mem_Vr[of 
       "v"], simp)  apply simp  
apply (simp add:Ring.ring_tOp_commute[of "K" "c"]) apply (
       frule Vr_ring[of  "v"], 
       frule_tac I = "(vp K v)\<^bsup>(Vr K v) (an N)\<^esup>" and x = "g n \<plusminus> (-\<^sub>a c)" 
       and r = "f n" in Ring.ideal_ring_multiple[of "Vr K v"]) 
apply (simp add:vp_apow_ideal) apply assumption+
apply (frule_tac I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" and 
       x = "(f n) \<cdot>\<^sub>r (g n \<plusminus> -\<^sub>a c)" and y = "(f n) \<cdot>\<^sub>r c" in 
                      Ring.ideal_pOp_closed[of "Vr K v"])
    apply (simp add:vp_apow_ideal)
 apply (simp add:Vr_tOp_f_tOp,  assumption)
 apply (simp add:Vr_tOp_f_tOp Vr_pOp_f_pOp,
       frule_tac x = "(f n) \<cdot>\<^sub>r (g n \<plusminus> -\<^sub>a c)" and N = "an N" in mem_vp_apow_mem_Vr[of "v"], simp add:Vr_pOp_f_pOp, assumption+)
 apply (frule_tac N = "an N" and x = "(f n) \<cdot>\<^sub>r c" in mem_vp_apow_mem_Vr[of 
        "v"]) apply simp apply assumption
 apply (simp add:Vr_pOp_f_pOp) apply simp

 apply (thin_tac "\<forall>N. \<exists>M. \<forall>n>M. f n \<in> vp K v\<^bsup> (Vr K v) (an N)\<^esup>",
        thin_tac "\<forall>N. \<exists>M. \<forall>n>M. g n \<plusminus> -\<^sub>a c \<in> vp K v\<^bsup> (Vr K v) (an N)\<^esup>",
        rule allI)
 apply (drule_tac x = j in spec, 
    drule_tac x = j in spec,
    drule_tac x = j in spec,
    frule  aGroup.ag_mOp_closed[of "K" "c"], assumption+,
    frule_tac x = "f j" in Ring.ring_tOp_closed[of "K" _ "c"], assumption+,
    frule_tac x = "f j" in Ring.ring_tOp_closed[of "K" _ "-\<^sub>a c"], assumption+)
 apply (simp add:Ring.ring_distrib1, simp add:aGroup.ag_pOp_assoc, 
        simp add:Ring.ring_distrib1[THEN sym],
        simp add:aGroup.ag_l_inv1, simp add:Ring.ring_times_x_0, 
        simp add:aGroup.ag_r_zero)
done

lemma (in Corps) limit_minus:"\<lbrakk>valuation K v; \<forall>j. f j \<in> carrier K; 
      b \<in> carrier K; lim\<^bsub>K v\<^esub> f b\<rbrakk> \<Longrightarrow> lim\<^bsub>K v\<^esub> (\<lambda>j. (-\<^sub>a (f j))) (-\<^sub>a b)"
apply (simp add:limit_def)
 apply (rule allI,
       rotate_tac -1, frule_tac x = N in spec,
        thin_tac "\<forall>N. \<exists>M. \<forall>n. M < n \<longrightarrow>  
                   f n \<plusminus> -\<^sub>a b \<in> (vp K v)\<^bsup>(Vr K v) (an N)\<^esup>",
       erule exE,
       subgoal_tac "\<forall>n. M < n \<longrightarrow> 
           (-\<^sub>a (f n)) \<plusminus> (-\<^sub>a (-\<^sub>a b)) \<in> (vp K v)\<^bsup>(Vr K v) (an N)\<^esup>",
      blast) 
 apply (rule allI, rule impI,
        frule_tac x = n in spec,
        frule_tac x = n in spec, simp) 

apply (frule Vr_ring[of "v"],
       frule_tac n = "an N" in vp_apow_ideal[of "v"], simp)
apply (frule_tac x = "f n \<plusminus> -\<^sub>a b" and N = "an N" in 
       mem_vp_apow_mem_Vr[of "v"], simp+,
       frule_tac I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" and x = "f n \<plusminus> (-\<^sub>a b)" in 
       Ring.ideal_inv1_closed[of "Vr K v"], assumption+, simp) 
 apply (simp add:Vr_mOp_f_mOp) 
 apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
        frule aGroup.ag_mOp_closed[of "K" "b"], assumption+)
 apply (simp add:aGroup.ag_p_inv[of "K"])
done

lemma (in Corps) inv_diff:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>; y \<in> carrier K; y \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
                (x\<^bsup>\<hyphen>K\<^esup>) \<plusminus> (-\<^sub>a (y\<^bsup>\<hyphen>K\<^esup>)) = (x\<^bsup>\<hyphen>K\<^esup>) \<cdot>\<^sub>r ( y\<^bsup>\<hyphen>K\<^esup>) \<cdot>\<^sub>r (-\<^sub>a (x \<plusminus> (-\<^sub>a y)))"
apply (cut_tac invf_closed1[of "x"], simp, erule conjE,
       cut_tac invf_closed1[of y], simp, erule conjE,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule Ring.ring_tOp_closed[of "K" "x\<^bsup>\<hyphen>K\<^esup>" "y\<^bsup>\<hyphen>K\<^esup>"], assumption+,
       frule aGroup.ag_mOp_closed[of "K" "x"], assumption+,
       frule aGroup.ag_mOp_closed[of "K" "y"], assumption+,
       frule aGroup.ag_mOp_closed[of "K" "x\<^bsup>\<hyphen>K\<^esup>"], assumption+,
       frule aGroup.ag_mOp_closed[of "K" "y\<^bsup>\<hyphen>K\<^esup>"], assumption+,
       frule aGroup.ag_pOp_closed[of "K" "x" "-\<^sub>a y"], assumption+) 
                                    
apply (simp add:Ring.ring_inv1_2[THEN sym],
       simp only:Ring.ring_distrib1[of "K" "(x\<^bsup>\<hyphen>K\<^esup>) \<cdot>\<^sub>r (y\<^bsup>\<hyphen>K\<^esup>)" "x" "-\<^sub>a y"],
       simp only:Ring.ring_tOp_commute[of "K" _ x],
       simp only:Ring.ring_inv1_2[THEN sym, of "K"], 
       simp only:Ring.ring_tOp_assoc[THEN sym],
       simp only:Ring.ring_tOp_commute[of "K" "x"],
       cut_tac linvf[of  "x"], simp+,
       simp add:Ring.ring_l_one, simp only:Ring.ring_tOp_assoc,
       cut_tac linvf[of "y"], simp+, 
       simp only:Ring.ring_r_one) 
apply (simp add:aGroup.ag_p_inv[of "K"], simp add:aGroup.ag_inv_inv,
       rule aGroup.ag_pOp_commute[of "K" "x\<^bsup>\<hyphen>K\<^esup>" "-\<^sub>a y\<^bsup>\<hyphen>K\<^esup>"], assumption+)
apply simp+
done

lemma times2plus:"(2::nat)*n = n + n"
by simp

lemma (in Corps) limit_inv:"\<lbrakk>valuation K v; \<forall>j. f j \<in> carrier K; 
      b \<in> carrier K; b \<noteq> \<zero>; lim\<^bsub>K v\<^esub> f b\<rbrakk> \<Longrightarrow> 
           lim\<^bsub>K v\<^esub> (\<lambda>j. if (f j) = \<zero> then \<zero> else (f j)\<^bsup>\<hyphen>K\<^esup>) (b\<^bsup>\<hyphen>K\<^esup>)"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
apply (frule limit_n_val[of "b" "v" "f"], assumption+) 
apply (subst limit_def)
 apply (rule allI, erule exE)
 apply (subgoal_tac "\<forall>m>Na. f m \<noteq> \<zero>") 
 prefer 2
 apply (rule allI, rule impI, rotate_tac -2,
        drule_tac x = m in spec, simp)
 apply (frule n_val_valuation[of v]) 
 apply (frule val_nonzero_noninf[of "n_val K v" b], assumption+)
 apply (rule contrapos_pp, simp+, simp add:value_of_zero)
 apply (unfold limit_def)
  apply (rotate_tac 2,
         frule_tac x = "N + 2*(na (Abs (n_val K v b)))" in 
         spec)
  apply (erule exE)
  apply (subgoal_tac "\<forall>n>(max Na M).
          (if f n = \<zero> then \<zero> else f n\<^bsup>\<hyphen>K\<^esup>) \<plusminus> -\<^sub>a b\<^bsup>\<hyphen>K\<^esup> \<in> vp K v\<^bsup>(Vr K v) (an N)\<^esup>", 
         blast) 
  apply (rule allI, rule impI)
  apply (cut_tac x = "Na" and y = "max Na M" and z = n
         in le_less_trans)
  apply simp+
  apply (thin_tac "\<forall>N. \<exists>M. \<forall>n>M. f n \<plusminus> -\<^sub>a b \<in> vp K v\<^bsup> (Vr K v) (an N)\<^esup>")
 apply (drule_tac x = n in spec,
        drule_tac x = n in spec,
        drule_tac x = n in spec,
        drule_tac x = n in spec, simp)
 apply (subst inv_diff, assumption+)
 apply (cut_tac x = "f n" in invf_closed1, simp,
        cut_tac x = b in invf_closed1, simp, simp, (erule conjE)+)
(* apply (frule field_is_idom[of "K"], frule field_iOp_closed[of "K" "b"], 
                                                 simp, simp, erule conjE,
        frule idom_tOp_nonzeros [of "K" "b\<^bsup>\<hyphen>K\<^esup>" "b\<^bsup>\<hyphen>K\<^esup>"], assumption+) *)
 apply (frule_tac n = "an N + an (2 * na (Abs (n_val K v b)))" and 
        x = "f n \<plusminus> -\<^sub>a b" in n_value_x_1[of v])
 apply (simp only:an_npn[THEN sym], rule an_nat_pos) 
 apply assumption
 apply (rule_tac x = "f n\<^bsup>\<hyphen> K\<^esup> \<cdot>\<^sub>r b\<^bsup>\<hyphen> K\<^esup> \<cdot>\<^sub>r (-\<^sub>a (f n \<plusminus> -\<^sub>a b))" and v = v and 
        n = "an N" in n_value_x_2, assumption+)
 apply (frule n_val_valuation[of v])
 apply (subst val_pos_mem_Vr[THEN sym, of "v"], assumption+)
  apply (rule Ring.ring_tOp_closed, assumption+)+
  apply (rule aGroup.ag_mOp_closed, assumption)
  apply (rule aGroup.ag_pOp_closed, assumption+,
         rule aGroup.ag_mOp_closed, assumption+)
  apply (subst val_pos_n_val_pos[of v], assumption+,
         rule Ring.ring_tOp_closed, assumption+,
         rule Ring.ring_tOp_closed, assumption+,
         rule aGroup.ag_mOp_closed, assumption+,
         rule aGroup.ag_pOp_closed, assumption+,
         rule aGroup.ag_mOp_closed, assumption+)
  apply (subst val_t2p[of "n_val K v"], assumption+,
         rule Ring.ring_tOp_closed, assumption+,
         rule aGroup.ag_mOp_closed, assumption+,
         rule aGroup.ag_pOp_closed, assumption+,
         rule aGroup.ag_mOp_closed, assumption+,
         subst val_minus_eq[of "n_val K v"], assumption+,
          (rule aGroup.ag_pOp_closed, assumption+),
          (rule aGroup.ag_mOp_closed, assumption+))
  apply (subst val_t2p[of "n_val K v"], assumption+)
  apply (simp add:value_of_inv)
  apply (frule_tac x = "an N + an (2 * na (Abs (n_val K v b)))" and y = "n_val K v (f n \<plusminus> -\<^sub>a b)" and z = "- n_val K v b + - n_val K v b" in aadd_le_mono)
  apply (cut_tac z = "n_val K v b" in Abs_pos)
  apply (frule val_nonzero_z[of "n_val K v" b], assumption+, erule exE)
  apply (rotate_tac -1, drule sym, cut_tac z = z in z_neq_minf,
         cut_tac z = z in z_neq_inf, simp,
         cut_tac a = "(n_val K v b)" in Abs_noninf, simp)
  apply (simp only:times2plus an_npn, simp add:an_na)
  apply (rotate_tac -4, drule sym, simp)
  apply (thin_tac "f n \<plusminus> -\<^sub>a b \<in> vp K v\<^bsup> (Vr K v) (an N + (ant \<bar>z\<bar> + ant \<bar>z\<bar>))\<^esup>")
  apply (simp add:an_def, simp add:aminus, (simp add:a_zpz)+)
  apply (subst aadd_commute)
  apply (rule_tac i = 0 and j = "ant (int N + 2 * \<bar>z\<bar> - 2 * z)" and 
         k = "n_val K v (f n \<plusminus> -\<^sub>a b) + ant (- (2 * z))" in ale_trans)
  apply (subst ant_0[THEN sym])
  apply (subst ale_zle, simp, assumption)

  apply (frule n_val_valuation[of v])
  apply (subst val_t2p[of "n_val K v"], assumption+)
  apply (rule Ring.ring_tOp_closed, assumption+)+
  apply (rule aGroup.ag_mOp_closed, assumption)
  apply (rule aGroup.ag_pOp_closed, assumption+,
         rule aGroup.ag_mOp_closed, assumption+)
  apply (subst val_t2p[of "n_val K v"], assumption+) 
  apply (subst val_minus_eq[of "n_val K v"], assumption+,
         rule aGroup.ag_pOp_closed, assumption+,
         rule aGroup.ag_mOp_closed, assumption+)

  apply (simp add:value_of_inv)
  apply (frule_tac x = "an N + an (2 * na (Abs (n_val K v b)))" and y = "n_val K v (f n \<plusminus> -\<^sub>a b)" and z = "- n_val K v b + - n_val K v b" in aadd_le_mono)
  apply (cut_tac z = "n_val K v b" in Abs_pos)
  apply (frule val_nonzero_z[of "n_val K v" b], assumption+, erule exE)
  apply (rotate_tac -1, drule sym, cut_tac z = z in z_neq_minf,
         cut_tac z = z in z_neq_inf, simp,
         cut_tac a = "(n_val K v b)" in Abs_noninf, simp)
  apply (simp only:times2plus an_npn, simp add:an_na)
  apply (rotate_tac -4, drule sym, simp)
  apply (thin_tac "f n \<plusminus> -\<^sub>a b \<in> vp K v\<^bsup> (Vr K v) (an N + (ant \<bar>z\<bar> + ant \<bar>z\<bar>))\<^esup>")
  apply (simp add:an_def, simp add:aminus, (simp add:a_zpz)+)
  apply (subst aadd_commute)
  apply (rule_tac i = "ant (int N)" and j = "ant (int N + 2 * \<bar>z\<bar> - 2 * z)" 
        and k = "n_val K v (f n \<plusminus> -\<^sub>a b) + ant (- (2 * z))" in ale_trans)
  apply (subst ale_zle, simp, assumption)
 
  apply simp
done

definition
  Cauchy_seq :: "[_ , 'b \<Rightarrow> ant, nat \<Rightarrow> 'b]
           \<Rightarrow> bool" ("(3Cauchy\<^bsub> _ _ \<^esub>_)" [90,90,91]90) where
  "Cauchy\<^bsub>K v\<^esub> f \<longleftrightarrow> (\<forall>n. (f n) \<in> carrier K) \<and> (
  \<forall>N. \<exists>M. (\<forall>n m. M < n \<and> M < m \<longrightarrow> 
                ((f n) \<plusminus>\<^bsub>K\<^esub> (-\<^sub>a\<^bsub>K\<^esub> (f m))) \<in> (vp K v)\<^bsup>(Vr K v) (an N)\<^esup>))"

definition
  v_complete :: "['b \<Rightarrow> ant, _] \<Rightarrow> bool"
                    ("(2Complete\<^bsub>_\<^esub> _)"  [90,91]90) where
  "Complete\<^bsub>v\<^esub> K \<longleftrightarrow> (\<forall>f. (Cauchy\<^bsub>K v\<^esub> f) \<longrightarrow> 
                           (\<exists>b. b \<in> (carrier K) \<and> lim\<^bsub>K v\<^esub> f b))"

lemma (in Corps) has_limit_Cauchy:"\<lbrakk>valuation K v; \<forall>j. f j \<in> carrier K; 
      b \<in> carrier K; lim\<^bsub>K v\<^esub> f b\<rbrakk> \<Longrightarrow> Cauchy\<^bsub>K v\<^esub> f" 
apply (simp add:Cauchy_seq_def)
apply (rule allI)
apply (simp add:limit_def)
 apply (rotate_tac -1)
 apply (drule_tac x = N in spec)
 apply (erule exE)
 apply (subgoal_tac "\<forall>n m. M < n \<and> M < m \<longrightarrow>
                        f n \<plusminus> -\<^sub>a (f m) \<in> vp K v\<^bsup>(Vr K v) (an N)\<^esup>")
 apply blast
 apply ((rule allI)+, rule impI, erule conjE)
 apply (frule_tac x = n in spec,
        frule_tac x = m in spec,
        thin_tac "\<forall>j. f j \<in> carrier K",
        frule_tac x = n in spec,
        frule_tac x = m in spec,
        thin_tac "\<forall>n. M < n \<longrightarrow>  f n \<plusminus> -\<^sub>a b \<in> vp K v\<^bsup>(Vr K v) (an N)\<^esup>",
        simp)
 apply (frule_tac n = "an N" in vp_apow_ideal[of v], simp)
 apply (frule Vr_ring[of "v"])
 apply (frule_tac x = "f m \<plusminus> -\<^sub>a b" and I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" in 
           Ring.ideal_inv1_closed[of "Vr K v"], assumption+)
 apply (frule_tac h = "f m \<plusminus> -\<^sub>a b" and I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" in 
           Ring.ideal_subset[of "Vr K v"], assumption+,
        frule_tac h = "f n \<plusminus> -\<^sub>a b" and I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" in 
           Ring.ideal_subset[of "Vr K v"], assumption+)  
apply (frule_tac h = "-\<^sub>a\<^bsub>Vr K v\<^esub> (f m \<plusminus> -\<^sub>a b)" and I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" in         Ring.ideal_subset[of "Vr K v"], assumption+,
       frule_tac h = "f n \<plusminus> -\<^sub>a b" and I = "vp K v\<^bsup>(Vr K v) (an N)\<^esup>" in 
        Ring.ideal_subset[of "Vr K v"], assumption+) 
apply (frule_tac I = "(vp K v)\<^bsup> (Vr K v) (an N)\<^esup>" and x = "f n \<plusminus> -\<^sub>a b" and
       y = "-\<^sub>a\<^bsub>(Vr K v)\<^esub> (f m \<plusminus> -\<^sub>a b)" in Ring.ideal_pOp_closed[of "Vr K v"],
       assumption+)
apply (simp add:Vr_pOp_f_pOp) apply (simp add:Vr_mOp_f_mOp)
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
 apply (frule aGroup.ag_mOp_closed[of "K" "b"], assumption+)
 apply (frule_tac x = "f m \<plusminus> -\<^sub>a b" in Vr_mem_f_mem[of "v"], assumption+)
 apply (frule_tac x = "f m \<plusminus> -\<^sub>a b" in aGroup.ag_mOp_closed[of "K"], 
         assumption+)
 apply (simp add:aGroup.ag_pOp_assoc)
 apply (simp add:aGroup.ag_pOp_commute[of "K" "-\<^sub>a b"])
 apply (simp add:aGroup.ag_p_inv[of "K"])
 apply (frule_tac x = "f m" in aGroup.ag_mOp_closed[of "K"], assumption+)
 apply (simp add:aGroup.ag_inv_inv)
 apply (simp add:aGroup.ag_pOp_assoc[of "K" _ "b" "-\<^sub>a b"])
 apply (simp add:aGroup.ag_r_inv1[of "K"], simp add:aGroup.ag_r_zero)
done

lemma (in Corps) no_limit_zero_Cauchy:"\<lbrakk>valuation K v; Cauchy\<^bsub>K v\<^esub> f;
    \<not> (lim\<^bsub>K v\<^esub> f \<zero>)\<rbrakk> \<Longrightarrow> 
 \<exists>N M. (\<forall>m. N < m \<longrightarrow>  ((n_val K v) (f M))  = ((n_val K v) (f m)))"
apply (frule not_limit_zero[of "v" "f"], thin_tac "\<not> lim\<^bsub> K v \<^esub>f \<zero>")
apply (simp add:Cauchy_seq_def, assumption) apply (erule exE)
apply (rename_tac L)
apply (simp add:Cauchy_seq_def, erule conjE,
       rotate_tac -1,
       frule_tac x = L in spec, thin_tac "\<forall>N. \<exists>M. \<forall>n m. 
       M < n \<and> M < m \<longrightarrow> f n \<plusminus> -\<^sub>a (f m) \<in> vp K v\<^bsup>(Vr K v) (an N)\<^esup>")
apply (erule exE)
apply (drule_tac x = M in spec)
apply (erule exE, erule conjE)
apply (rotate_tac -3,
       frule_tac x = m in spec)
    apply (thin_tac "\<forall>n m. M < n \<and> M < m \<longrightarrow>
               f n \<plusminus> -\<^sub>a (f m) \<in> (vp K v)\<^bsup>(Vr K v) (an L)\<^esup>")
   apply (subgoal_tac "M < m \<and> (\<forall>ma. M < ma \<longrightarrow> 
                             n_val K v (f m) = n_val K v (f ma))")
   apply blast
  apply simp
 
 apply (rule allI, rule impI)
 apply (rotate_tac -2)
 apply (drule_tac x = ma in spec)
 apply simp
 (** we have f ma \<plusminus> -\<^sub>a f m \<in> vpr K G a i v \<^bsup>\<diamondsuit>Vr K G a i v L\<^esup> as **) 
 apply (frule Vr_ring[of "v"], 
        frule_tac n = "an L" in vp_apow_ideal[of "v"], simp)
apply (frule_tac I = "vp K v\<^bsup>(Vr K v) (an L)\<^esup>" and x = "f m \<plusminus> -\<^sub>a (f ma)"
        in Ring.ideal_inv1_closed[of "Vr K v"], assumption+) apply (
        frule_tac I = "vp K v\<^bsup>(Vr K v) (an L)\<^esup>" and 
        h = "f m \<plusminus> -\<^sub>a (f ma)" in Ring.ideal_subset[of "Vr K v"], 
        assumption+, simp add:Vr_mOp_f_mOp)
   apply (frule_tac x = m in spec,
          drule_tac x = ma in spec)  apply (
         
          cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
          frule_tac x = "f ma" in aGroup.ag_mOp_closed[of "K"], assumption+,
          frule_tac x = "f m" and y = "-\<^sub>a (f ma)" in aGroup.ag_p_inv[of "K"],
          assumption+, simp only:aGroup.ag_inv_inv,
          frule_tac x = "f m" in aGroup.ag_mOp_closed[of "K"], assumption+,
          simp add:aGroup.ag_pOp_commute,
          thin_tac "-\<^sub>a ( f m \<plusminus> -\<^sub>a (f ma)) =  f ma \<plusminus> -\<^sub>a (f m)",
          thin_tac "f m \<plusminus> -\<^sub>a (f ma) \<in> vp K v\<^bsup>(Vr K v) (an L)\<^esup>")
  (** finally, by f ma = f m \<plusminus> (f ma \<plusminus> -\<^sub>a (f m)) and value_less_eq 
      we have the conclusion **)
   apply (frule_tac x = "f ma \<plusminus> -\<^sub>a (f m)" and n = "an L" in n_value_x_1[of 
         "v" ], simp) apply assumption apply (
         frule n_val_valuation[of "v"], 
         frule_tac x = "f m" and y = "f ma \<plusminus> -\<^sub>a (f m)" in value_less_eq[of 
         "n_val K v"], assumption+) apply (simp add:aGroup.ag_pOp_closed) 
  apply (
         rule_tac x = "n_val K v (f m)" and y = "an L" and
         z = "n_val K v ( f ma \<plusminus> -\<^sub>a (f m))" in  
         aless_le_trans, assumption+) 
  apply (frule_tac x = "f ma \<plusminus> -\<^sub>a (f m)" in Vr_mem_f_mem[of "v"])
  apply (simp add:Ring.ideal_subset)
  apply (frule_tac x = "f m" and y = "f ma \<plusminus> -\<^sub>a (f m)" in 
         aGroup.ag_pOp_commute[of "K"], assumption+) 
  apply (simp add:aGroup.ag_pOp_assoc,
         simp add:aGroup.ag_l_inv1, simp add:aGroup.ag_r_zero)
done 

lemma (in Corps) no_limit_zero_Cauchy1:"\<lbrakk>valuation K v; \<forall>j. f j \<in> carrier K; 
  Cauchy\<^bsub>K v\<^esub> f; \<not> (lim\<^bsub>K v\<^esub> f \<zero>)\<rbrakk> \<Longrightarrow> \<exists>N M. (\<forall>m. N < m \<longrightarrow>  v (f M) = v (f m))"
apply (frule no_limit_zero_Cauchy[of "v" "f"], assumption+)
 apply (erule exE)+
 apply (subgoal_tac "\<forall>m. N < m \<longrightarrow> v (f M) = v (f m)") apply blast
 apply (rule allI, rule impI)
 apply (frule_tac x = M in spec,
        drule_tac x = m in spec,
        drule_tac x = m in spec, simp)
 apply (simp add:n_val[THEN sym, of "v"])
done
 
definition
  subfield :: "[_, ('b, 'm1) Ring_scheme] \<Rightarrow> bool" where
  "subfield K K' \<longleftrightarrow> Corps K' \<and> carrier K \<subseteq> carrier K' \<and> 
                   idmap (carrier K) \<in> rHom K K'"

definition
  v_completion :: "['b \<Rightarrow> ant, 'b \<Rightarrow> ant, _, ('b, 'm) Ring_scheme] \<Rightarrow> bool" 
               ("(4Completion\<^bsub>_ _\<^esub> _ _)" [90,90,90,91]90) where
  "Completion\<^bsub>v v'\<^esub> K K' \<longleftrightarrow> subfield K K' \<and>
      Complete\<^bsub>v'\<^esub> K' \<and> (\<forall>x \<in> carrier K. v x = v' x) \<and>
      (\<forall>x \<in> carrier K'. (\<exists>f. Cauchy\<^bsub>K v\<^esub> f \<and> lim\<^bsub>K' v'\<^esub> f x))"

lemma (in Corps) subfield_zero:"\<lbrakk>Corps K'; subfield K K'\<rbrakk> \<Longrightarrow> \<zero>\<^bsub>K\<^esub> = \<zero>\<^bsub>K'\<^esub>"
apply (simp add:subfield_def, (erule conjE)+)
apply (simp add:rHom_def, (erule conjE)+)
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule Corps.field_is_ring[of "K'"], frule Ring.ring_is_ag[of "K'"])
apply (frule aHom_0_0[of "K" "K'" "I\<^bsub>K\<^esub>"], assumption+)
apply (frule aGroup.ag_inc_zero[of "K"], simp add:idmap_def)
done

lemma (in Corps) subfield_pOp:"\<lbrakk>Corps K'; subfield K K'; x \<in> carrier K;
      y \<in> carrier K\<rbrakk> \<Longrightarrow> x \<plusminus> y = x \<plusminus>\<^bsub>K'\<^esub> y"
apply (cut_tac field_is_ring, frule Corps.field_is_ring[of "K'"],
       frule Ring.ring_is_ag[of "K"], frule Ring.ring_is_ag[of "K'"])
apply (simp add:subfield_def, erule conjE, simp add:rHom_def,
       frule conjunct1)
apply (thin_tac "I\<^bsub>K\<^esub> \<in> aHom K K' \<and>
     (\<forall>x\<in>carrier K. \<forall>y\<in>carrier K. I\<^bsub>K\<^esub> (x \<cdot>\<^sub>r y) = I\<^bsub>K\<^esub> x \<cdot>\<^sub>r\<^bsub>K'\<^esub> I\<^bsub>K\<^esub> y) \<and>
     I\<^bsub>K\<^esub> 1\<^sub>r = 1\<^sub>r\<^bsub>K'\<^esub>")
apply (frule aHom_add[of "K" "K'" "I\<^bsub>K\<^esub>" "x" "y"], assumption+,
       frule aGroup.ag_pOp_closed[of "K" "x" "y"], assumption+, 
       simp add:idmap_def)
done

lemma (in Corps) subfield_mOp:"\<lbrakk>Corps K'; subfield K K'; x \<in> carrier K\<rbrakk> \<Longrightarrow> 
                     -\<^sub>a x = -\<^sub>a\<^bsub>K'\<^esub> x"
apply (cut_tac field_is_ring, frule Corps.field_is_ring[of "K'"],
       frule Ring.ring_is_ag[of "K"], frule Ring.ring_is_ag[of "K'"])
apply (simp add:subfield_def, erule conjE, simp add:rHom_def,
       frule conjunct1)
apply (thin_tac "I\<^bsub>K\<^esub> \<in> aHom K K' \<and>
     (\<forall>x\<in>carrier K. \<forall>y\<in>carrier K. I\<^bsub>K\<^esub> (x \<cdot>\<^sub>r y) = I\<^bsub>K\<^esub> x \<cdot>\<^sub>r\<^bsub>K'\<^esub> I\<^bsub>K\<^esub> y) \<and>
     I\<^bsub>K\<^esub> 1\<^sub>r = 1\<^sub>r\<^bsub>K'\<^esub>")
apply (frule aHom_inv_inv[of "K" "K'" "I\<^bsub>K\<^esub>" "x"], assumption+,
       frule aGroup.ag_mOp_closed[of "K" "x"], assumption+)
apply (simp add:idmap_def)
done

lemma (in Corps) completion_val_eq:"\<lbrakk>Corps K'; valuation K v; valuation K' v'; 
 x \<in> carrier K;  Completion\<^bsub>v v'\<^esub> K K'\<rbrakk> \<Longrightarrow> v x = v' x"
apply (unfold v_completion_def, (erule conjE)+)
apply simp
done

lemma (in Corps) completion_subset:"\<lbrakk>Corps K'; valuation K v; valuation K' v'; 
 Completion\<^bsub>v v'\<^esub> K K'\<rbrakk> \<Longrightarrow>  carrier K \<subseteq> carrier K'"
apply (unfold v_completion_def, (erule conjE)+)
apply (simp add:subfield_def)
done

lemma (in Corps) completion_subfield:"\<lbrakk>Corps K'; valuation K v; 
       valuation K' v'; Completion\<^bsub>v v'\<^esub> K K'\<rbrakk> \<Longrightarrow>  subfield K K'"
apply (simp add:v_completion_def)
done

lemma (in Corps) subfield_sub:"subfield K K' \<Longrightarrow> carrier K \<subseteq> carrier K'"
apply (simp add:subfield_def)
done

lemma (in Corps) completion_Vring_sub:"\<lbrakk>Corps K'; valuation K v; 
  valuation K' v'; Completion\<^bsub>v v'\<^esub> K K'\<rbrakk> \<Longrightarrow> 
                     carrier (Vr K v) \<subseteq> carrier (Vr K' v')"
apply (rule subsetI,
      frule completion_subset[of  "K'" "v" "v'"], assumption+,
      frule_tac x = x in Vr_mem_f_mem[of "v"], assumption+,
      frule_tac x = x in completion_val_eq[of "K'" "v" "v'"],
        assumption+)
apply (frule_tac x1 = x in val_pos_mem_Vr[THEN sym, of  "v"],
       assumption+, simp,
       frule_tac c = x in subsetD[of "carrier K" "carrier K'"], assumption+,
      simp add:Corps.val_pos_mem_Vr[of "K'" "v'"])
done

lemma (in Corps) completion_idmap_rHom:"\<lbrakk>Corps K'; valuation K v; 
  valuation K' v';  Completion\<^bsub>v v'\<^esub> K K'\<rbrakk> \<Longrightarrow> 
             I\<^bsub>(Vr K v)\<^esub> \<in> rHom (Vr K v) (Vr K' v')"
apply (frule completion_Vring_sub[of  "K'" "v" "v'"],
         assumption+,
       frule completion_subfield[of "K'" "v" "v'"], 
         assumption+,
       frule Vr_ring[of "v"],
        frule Ring.ring_is_ag[of "Vr K v"],
       frule Corps.Vr_ring[of "K'" "v'"], assumption+,
       frule Ring.ring_is_ag[of "Vr K' v'"])
apply (simp add:rHom_def)
apply (rule conjI) 
 apply (simp add:aHom_def,
        rule conjI,
        simp add:idmap_def, simp add:subsetD)
apply (rule conjI)
 apply (simp add:idmap_def extensional_def)
 apply ((rule ballI)+) apply (
        frule_tac x = a and y = b in aGroup.ag_pOp_closed, assumption+,
        simp add:idmap_def, 
   frule_tac c = a in subsetD[of "carrier (Vr K v)" 
                         "carrier (Vr K' v')"], assumption+,
   frule_tac c = b in subsetD[of "carrier (Vr K v)" 
                         "carrier (Vr K' v')"], assumption+,
   simp add:Vr_pOp_f_pOp,
   frule_tac x = a in Vr_mem_f_mem[of v], assumption,
   frule_tac x = b in Vr_mem_f_mem[of v], assumption,
   simp add:Corps.Vr_pOp_f_pOp,
   simp add:subfield_pOp)
apply (rule conjI)
 apply ((rule ballI)+, 
        frule_tac x = x and y = y in Ring.ring_tOp_closed, assumption+,
        simp add:idmap_def, simp add:subfield_def, erule conjE)
 apply (frule_tac c = x in subsetD[of "carrier (Vr K v)" 
            "carrier (Vr K' v')"], assumption+,
        frule_tac c = y in subsetD[of "carrier (Vr K v)" 
            "carrier (Vr K' v')"], assumption+)
 apply (simp add:Vr_tOp_f_tOp Corps.Vr_tOp_f_tOp)
apply (frule_tac x = x in Vr_mem_f_mem[of "v"], assumption+,
       frule_tac x = y in Vr_mem_f_mem[of "v"], assumption+,
     frule_tac x = x in Corps.Vr_mem_f_mem[of "K'" "v'"], assumption+,
     frule_tac x = y in Corps.Vr_mem_f_mem[of "K'" "v'"], assumption+,
       cut_tac field_is_ring, frule Corps.field_is_ring[of "K'"],
       frule_tac x = x and y = y in Ring.ring_tOp_closed[of "K"], assumption+)
apply (frule_tac x = x and y = y in rHom_tOp[of "K" "K'" _ _ "I\<^bsub>K\<^esub>"], 
                 assumption+, simp add:idmap_def)
apply (frule Ring.ring_one[of "Vr K v"], simp add:idmap_def)
apply (simp add:Vr_1_f_1 Corps.Vr_1_f_1)
apply (simp add:subfield_def, (erule conjE)+)
apply (cut_tac field_is_ring, frule Corps.field_is_ring[of "K'"],
       frule Ring.ring_one[of "K"],
       frule rHom_one[of "K" "K'" "I\<^bsub>K\<^esub>"], assumption+, simp add:idmap_def)
done

lemma (in Corps) completion_vpr_sub:"\<lbrakk>Corps K'; valuation K v; valuation K' v';
      Completion\<^bsub>v v'\<^esub> K K'\<rbrakk> \<Longrightarrow> vp K v \<subseteq> vp K' v'"
apply (rule subsetI,
      frule completion_subset[of "K'" "v" "v'"], assumption+,
      frule Vr_ring[of "v"], frule vp_ideal[of "v"],
        frule_tac h = x in Ring.ideal_subset[of "Vr K v" "vp K v"],
        assumption+,
      frule_tac x = x in Vr_mem_f_mem[of  "v"], assumption+,
      frule_tac x = x in completion_val_eq[of "K'" "v" "v'"],
        assumption+)
apply (frule completion_subset[of "K'" "v" "v'"],
        assumption+,
       frule_tac c = x in subsetD[of "carrier K" "carrier K'"], assumption+,
       simp add:Corps.vp_mem_val_poss vp_mem_val_poss)
done

lemma (in Corps) val_v_completion:"\<lbrakk>Corps K'; valuation K v; valuation K' v'; 
      x \<in> carrier K'; x \<noteq> \<zero>\<^bsub>K'\<^esub>; Completion\<^bsub>v v'\<^esub> K K'\<rbrakk> \<Longrightarrow>
   \<exists>f. (Cauchy\<^bsub>K v\<^esub> f) \<and> (\<exists>N. (\<forall>m. N < m \<longrightarrow> v (f m) = v' x))"
apply (simp add:v_completion_def, erule conjE, (erule conjE)+)
 apply (rotate_tac -1, drule_tac x = x in bspec, assumption+,
        erule exE, erule conjE,
        subgoal_tac "\<exists>N. \<forall>m. N < m \<longrightarrow> v (f m) = v' x", blast) 
    thm Corps.limit_val
 apply (frule_tac f = f and v = v' in  Corps.limit_val[of "K'" "x"],
        assumption+,
        unfold Cauchy_seq_def, frule conjunct1, fold Cauchy_seq_def) 
apply (rule allI, drule_tac x = j in spec,
       simp add:subfield_def, erule conjE, simp add:subsetD, assumption+)
 apply (simp add:Cauchy_seq_def)
done

lemma (in Corps) v_completion_v_limit:"\<lbrakk>Corps K'; valuation K v; 
      x \<in> carrier K; subfield K K'; Complete\<^bsub>v'\<^esub> K'; \<forall>j. f j \<in> carrier K;  
      valuation K' v'; \<forall>x\<in>carrier K. v x = v' x; lim\<^bsub>K' v' \<^esub>f x\<rbrakk> \<Longrightarrow> lim\<^bsub>K v \<^esub>f x"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule Corps.field_is_ring[of K'], frule Ring.ring_is_ag[of "K'"],
       subgoal_tac "\<forall>j. f j \<in> carrier K'",
       unfold subfield_def, frule conjunct2, fold subfield_def, erule conjE)
apply (frule subsetD[of "carrier K" "carrier K'" "x"], assumption+,
       simp add:limit_diff_val[of "x" "f"],
       subgoal_tac "\<forall>n. f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> x = f n \<plusminus> -\<^sub>a x")
 apply (rule allI)
 apply (simp add:limit_def)
 apply (rotate_tac 6, drule_tac x = N in spec,
        erule exE)
 apply (subgoal_tac "\<forall>n>M. an N \<le> v'(f n \<plusminus> -\<^sub>a x)",
        subgoal_tac "\<forall>n. (v' (f n \<plusminus> -\<^sub>a x) = v (f n \<plusminus> -\<^sub>a x))", simp, blast)
 apply (rule allI)
 apply (frule_tac x = "f n \<plusminus> -\<^sub>a x" in bspec,
        rule aGroup.ag_pOp_closed, assumption+, simp,
        rule aGroup.ag_mOp_closed, assumption+) apply simp
 apply (rule allI, rule impI)
 apply (frule_tac v = v' and n = "an N" and x = "f n \<plusminus> -\<^sub>a x" in 
         Corps.n_value_x_1[of K'], assumption+, simp, simp)
 apply (frule_tac v = v' and x = "f n \<plusminus> -\<^sub>a x" in Corps.n_val_le_val[of K'],
         assumption+) 
 apply (cut_tac x = "f n" and y = "-\<^sub>a x" in aGroup.ag_pOp_closed, assumption,
        simp, rule aGroup.ag_mOp_closed, assumption+, simp add:subsetD)
 apply (subst Corps.val_pos_n_val_pos[of K' v'], assumption+)
   apply (cut_tac x = "f n" and y = "-\<^sub>a x" in aGroup.ag_pOp_closed, assumption,
        simp, rule aGroup.ag_mOp_closed, assumption+, simp add:subsetD)
apply (rule_tac i = 0 and j = "an N" and k = "n_val K' v' (f n \<plusminus> -\<^sub>a x)" in 
       ale_trans, simp+, rule allI)
 apply (subst subfield_pOp[of K'], assumption+, simp+,
        rule aGroup.ag_mOp_closed, assumption+)
 apply (simp add:subfield_mOp[of K'])
 apply (cut_tac subfield_sub[of K'], simp add:subsetD, assumption+)
done
    
lemma (in Corps) Vr_idmap_aHom:"\<lbrakk>Corps K'; valuation K v; valuation K' v'; 
      subfield K K'; \<forall>x\<in>carrier K. v x = v' x\<rbrakk> \<Longrightarrow> 
                              I\<^bsub>(Vr K v)\<^esub> \<in> aHom (Vr K v) (Vr K' v')"
apply (simp add:aHom_def)
apply (subgoal_tac "I\<^bsub>(Vr K v)\<^esub> \<in> carrier (Vr K v) \<rightarrow> carrier (Vr K' v')")
apply simp
apply (rule conjI)
 apply (simp add:idmap_def)
apply (rule ballI)+
 apply (frule Vr_ring[of "v"],
        frule Ring.ring_is_ag[of "Vr K v"],
        frule Corps.Vr_ring[of "K'" "v'"], assumption+,
        frule Ring.ring_is_ag[of "Vr K' v'"]) 
 apply (frule_tac x = a and y = b in aGroup.ag_pOp_closed[of "Vr K v"],
               assumption+,
        frule_tac x = a in funcset_mem[of "I\<^bsub>(Vr K v)\<^esub>" 
        "carrier (Vr K v)" "carrier (Vr K' v')"], assumption+,
        frule_tac x = b in funcset_mem[of "I\<^bsub>(Vr K v)\<^esub>" 
        "carrier (Vr K v)" "carrier (Vr K' v')"], assumption+,
        frule_tac x = "(I\<^bsub>(Vr K v)\<^esub>) a" and y = "(I\<^bsub>(Vr K v)\<^esub>) b" in 
        aGroup.ag_pOp_closed[of "Vr K' v'"], assumption+, 
        simp add:Vr_pOp_f_pOp)
 apply (simp add:idmap_def, simp add:subfield_def, erule conjE,
        simp add:rHom_def, frule conjunct1,
        thin_tac "I\<^bsub>K\<^esub> \<in> aHom K K' \<and>
           (\<forall>x\<in>carrier K. \<forall>y\<in>carrier K. I\<^bsub>K\<^esub> (x \<cdot>\<^sub>r y) = I\<^bsub>K\<^esub> x \<cdot>\<^sub>r\<^bsub>K'\<^esub> I\<^bsub>K\<^esub> y) \<and>
           I\<^bsub>K\<^esub> 1\<^sub>r = 1\<^sub>r\<^bsub>K'\<^esub>")
  apply (simp add:Corps.Vr_pOp_f_pOp[of K' v'])
  apply (frule_tac x = a in Vr_mem_f_mem[of v], assumption+,
         frule_tac x = b in Vr_mem_f_mem[of v], assumption+)
  apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of K],
         frule Corps.field_is_ring[of K'], frule Ring.ring_is_ag[of K']) 
  apply (frule_tac a = a and b = b in aHom_add[of K K' "I\<^bsub>K\<^esub>"], assumption+,
         frule_tac x = a and y = b in aGroup.ag_pOp_closed[of K], assumption+,
         simp add:idmap_def)
apply (rule Pi_I,
       drule_tac x = x in bspec, simp add:Vr_mem_f_mem)
apply (simp add:idmap_def)
 apply (frule_tac x1 = x in val_pos_mem_Vr[THEN sym, of v],
         simp add:Vr_mem_f_mem, simp)
 apply (subst Corps.val_pos_mem_Vr[THEN sym, of K' v'], assumption+,
        frule_tac x = x in Vr_mem_f_mem[of v], assumption+,
        frule subfield_sub[of K'], simp add:subsetD)
 apply assumption
done

lemma amult_pos_pos:"0 \<le> a \<Longrightarrow> 0 \<le> a * an N"
apply (case_tac "N = 0", simp add:an_0)
 apply (case_tac "a = \<infinity>", simp) 
 apply (frule apos_neq_minf[of a])
 apply (subst ant_tna[THEN sym, of a], simp)
 apply (subst amult_0_r, simp)
apply (case_tac "a = \<infinity>", simp add:an_def) 
 apply (frule apos_neq_minf[of a])
 apply (subst ant_tna[THEN sym, of a], simp)
 apply (case_tac "a = 0", simp)
 apply (simp add:ant_0 an_def amult_0_l)
apply (cut_tac amult_pos1[of "tna a" "an N"]) 
 apply (simp add:ant_tna)
 apply (rule_tac ale_trans[of 0 "an N" "a * an N"], simp+)
 apply (frule ale_neq_less[of 0 a], rule not_sym, assumption)
 apply (subst aless_zless[THEN sym, of 0 "tna a"], simp add:ant_tna ant_0)
 apply simp
done

lemma (in Corps) Cauchy_down:"\<lbrakk>Corps K'; valuation K v; valuation K' v'; 
  subfield K K'; \<forall>x\<in>carrier K. v x = v' x; \<forall>j. f j \<in> carrier K; Cauchy\<^bsub>K' v' \<^esub>f\<rbrakk> 
  \<Longrightarrow>  Cauchy\<^bsub>K v \<^esub>f" 
apply (simp add:Cauchy_seq_def, rule allI, erule conjE) 
apply (rotate_tac -1, drule_tac 
  x = "na (Lv K v) * N" in spec,
  erule exE,
  subgoal_tac "\<forall>n m. M < n \<and> M < m \<longrightarrow>
      f n \<plusminus> (-\<^sub>a (f m)) \<in> vp K v\<^bsup>(Vr K v) (an N)\<^esup>", blast)
 apply (simp add:amult_an_an) apply (simp add:an_na_Lv)
 apply ((rule allI)+, rule impI, erule conjE) apply (
      rotate_tac -3, drule_tac x = n in spec,
      rotate_tac -1, drule_tac x = m in spec,
      simp)
 apply (rotate_tac 7,
        frule_tac x = n in spec,
        drule_tac x = m in spec)
 apply (simp add:subfield_mOp[THEN sym],
        cut_tac field_is_ring, frule Ring.ring_is_ag[of K],
        frule_tac x = "f m" in aGroup.ag_mOp_closed[of K], assumption+)
 apply (simp add:subfield_pOp[THEN sym])
 apply (frule_tac x = "f n" and y = "-\<^sub>a f m" in aGroup.ag_pOp_closed, 
        assumption+,
        frule subfield_sub[of K'],
        frule_tac c = "f n \<plusminus> -\<^sub>a f m" in subsetD[of "carrier K" "carrier K'"], 
        assumption+)
 apply (frule Lv_pos[of v],
        frule aless_imp_le[of 0 "Lv K v"])
 apply (frule_tac N = N in amult_pos_pos[of "Lv K v"])
 apply (frule_tac n = "(Lv K v) * an N" and x = "f n \<plusminus> -\<^sub>a f m" in 
        Corps.n_value_x_1[of K' v'], assumption+)
 apply (frule_tac x = "f n \<plusminus> -\<^sub>a f m" in Corps.n_val_le_val[of K' v'],
        assumption+,
        frule_tac j = "Lv K v * an N" and k = "n_val K' v' (f n \<plusminus> -\<^sub>a f m)" in
         ale_trans[of 0], assumption+, simp add:Corps.val_pos_n_val_pos)
 apply (frule_tac i = "Lv K v * an N" and j = "n_val K' v' (f n \<plusminus> -\<^sub>a f m)" 
        and k = "v' (f n \<plusminus> -\<^sub>a f m)" in ale_trans, assumption+,
        thin_tac "n_val K' v' (f n \<plusminus> -\<^sub>a f m) \<le> v' (f n \<plusminus> -\<^sub>a f m)",
        thin_tac "Lv K v * an N \<le> n_val K' v' (f n \<plusminus> -\<^sub>a f m)")
 apply (rotate_tac 1,
        drule_tac x = "f n \<plusminus> -\<^sub>a f m" in bspec, assumption,
        rotate_tac -1, drule sym, simp)
 apply (frule_tac v1 = v and x1 = "f n \<plusminus> -\<^sub>a f m" in n_val[THEN sym],
        assumption)
 apply simp
 apply (simp only:amult_commute[of _ "Lv K v"])
apply (frule Lv_z[of v], erule exE)
 
apply (cut_tac w = z and x = "an N" and y = "n_val K v (f n \<plusminus> -\<^sub>a f m)" in
       amult_pos_mono_l,
       cut_tac m = 0 and n = z in aless_zless, simp add:ant_0)
 apply simp
 apply (rule_tac x="f n \<plusminus> -\<^sub>a (f m)" and n = "an N" in n_value_x_2[of v], 
        assumption+) 
 apply (subst val_pos_mem_Vr[THEN sym, of v], assumption+)
 apply (subst val_pos_n_val_pos[of v], assumption+)
 apply (rule_tac j = "an N" and k = "n_val K v (f n \<plusminus> -\<^sub>a f m)" in 
        ale_trans[of 0], simp, assumption+)
 apply simp
done

lemma (in Corps) Cauchy_up:"\<lbrakk>Corps K'; valuation K v; valuation K' v'; 
      Completion\<^bsub>v v'\<^esub> K K'; Cauchy\<^bsub> K v \<^esub>f\<rbrakk> \<Longrightarrow> Cauchy\<^bsub> K' v' \<^esub>f" 
apply (simp add:Cauchy_seq_def,
       erule conjE,
       rule conjI, unfold v_completion_def, frule conjunct1,
       fold v_completion_def, rule allI, frule subfield_sub[of K'])
apply (simp add:subsetD) 

apply (rule allI)
apply (rotate_tac -1, drule_tac x = "na (Lv K' v') * N" 
      in spec, erule exE) 
apply (subgoal_tac "\<forall>n m. M < n \<and> M < m \<longrightarrow>
         f n \<plusminus>\<^bsub>K'\<^esub> (-\<^sub>a\<^bsub>K'\<^esub> (f m)) \<in> vp K' v'\<^bsup>(Vr K' v') (an N)\<^esup>", blast,
       (rule allI)+, rule impI, erule conjE)
apply (rotate_tac -3, drule_tac x = n in spec,
       rotate_tac -1, 
       drule_tac x = m in spec, simp,
       frule_tac x = n in spec,
       drule_tac x = m in spec)
 apply(unfold v_completion_def, frule conjunct1, fold v_completion_def,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule_tac x = "f m" in aGroup.ag_mOp_closed[of "K"], assumption+,
       frule_tac x = "f n" and y = "-\<^sub>a (f m)" in aGroup.ag_pOp_closed[of "K"],
       assumption+)
 apply (simp add:amult_an_an) apply (simp add:Corps.an_na_Lv)
apply (simp add:subfield_mOp, simp add:subfield_pOp) apply (
       frule_tac x = "f n  \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> f m" and n = "(Lv K' v') * (an N)"
       in n_value_x_1[of v]) (*apply (
  thin_tac "f n \<plusminus>' (-\<^sub>a' (f m)) \<in> vp K v\<^bsup>(Vr K v) ( (Lv K' v') * (an N))\<^esup>",
   simp add:v_completion_def, (erule conjE)+) *) 
apply (frule Corps.Lv_pos[of "K'" "v'"], assumption+, 
       frule Corps.Lv_z[of "K'" "v'"],
       assumption, erule exE, simp, 
       cut_tac n = N in an_nat_pos,
       frule_tac w1 = z and x1 = 0 and y1 = "an N" in 
             amult_pos_mono_l[THEN sym], simp, simp add:amult_0_r)
apply assumption
apply (frule_tac x = "f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> f m " in n_val_le_val[of v],
        assumption+)
apply (subst n_val[THEN sym, of "v"], assumption+)
apply (frule Lv_pos[of "v"], frule Lv_z[of v], erule exE, simp)
apply (frule Corps.Lv_pos[of "K'" "v'"], assumption+, 
       frule Corps.Lv_z[of "K'" "v'"],   assumption, erule exE, simp, 
       cut_tac n = N in an_nat_pos,
       frule_tac w1 = za and x1 = 0 and y1 = "an N" in 
             amult_pos_mono_l[THEN sym], simp, simp add:amult_0_r)
apply (frule_tac j = "ant za * an N" and k = "n_val K v (f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> (f m))"
       in ale_trans[of "0"], assumption+)
apply (frule_tac w1 = z and x1 = 0 and y1 = "n_val K v ( f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> (f m))"
       in amult_pos_mono_r[THEN sym], simp, simp add:amult_0_l)
apply (frule_tac i = "Lv K' v' * an N" and j ="n_val K v ( f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> (f m))"
       and k = "v ( f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> (f m))" in ale_trans, assumption+)
apply (thin_tac "f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> (f m) \<in> vp K v\<^bsup> (Vr K v) (Lv K' v') * (an N)\<^esup>",
       thin_tac "Lv K' v' * an N \<le> n_val K v ( f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> (f m))",
       thin_tac "n_val K v ( f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> (f m)) \<le> v ( f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> (f m))")

apply (simp add:v_completion_def, (erule conjE)+)
 apply (thin_tac "\<forall>x\<in>carrier K. v x = v' x",
        thin_tac "\<forall>x\<in>carrier K'. \<exists>f. Cauchy\<^bsub> K v \<^esub>f \<and> lim\<^bsub> K' v' \<^esub>f x")
 apply (frule subfield_sub[of K'],
        frule_tac c = "f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> (f m)" in 
                  subsetD[of "carrier K" "carrier K'"], assumption+)
apply (simp add:Corps.n_val[THEN sym, of "K'" "v'"])
apply (simp add:amult_commute[of _ "Lv K' v'"])
apply (frule Corps.Lv_pos[of "K'" "v'"], assumption, 
       frule Corps.Lv_z[of "K'" "v'"], assumption+, erule exE, simp)
apply (simp add:amult_pos_mono_l)

apply (rule_tac x = "f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> (f m)" and n = "an N" in 
       Corps.n_value_x_2[of "K'" "v'"], assumption+)
apply (cut_tac n = N in an_nat_pos)
 apply (frule_tac j = "an N" and k = "n_val K' v' (f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> (f m))" in 
        ale_trans[of "0"], assumption+)
 apply (simp add:Corps.val_pos_n_val_pos[THEN sym, of "K'" "v'"])
 apply (simp add:Corps.val_pos_mem_Vr) apply assumption apply simp
done

lemma max_gtTr:"(n::nat) < max (Suc n) (Suc m) \<and> m < max (Suc n) (Suc m)"
by (simp add:max_def)

lemma (in Corps) completion_approx:"\<lbrakk>Corps K'; valuation K v; valuation K' v'; 
      Completion\<^bsub>v v'\<^esub> K K'; x \<in> carrier (Vr K' v')\<rbrakk> \<Longrightarrow> 
               \<exists>y\<in>carrier (Vr K v). (y \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> x) \<in> (vp K' v')"
(** show an element y near by x is included in (Vr K v) **) 
apply (frule Corps.Vr_mem_f_mem [of "K'" "v'" "x"], assumption+,
       frule Corps.val_pos_mem_Vr[THEN sym, of "K'" "v'" "x"], assumption+,
       simp add:v_completion_def, (erule conjE)+,
       rotate_tac -1, drule_tac x = x in bspec, assumption+, 
       erule exE, erule conjE)
apply (unfold Cauchy_seq_def, frule conjunct1, fold Cauchy_seq_def)
apply (case_tac "x = \<zero>\<^bsub>K'\<^esub>", 
       simp, frule Corps.field_is_ring[of "K'"], 
       frule Ring.ring_is_ag[of "K'"],
       subgoal_tac " \<zero>\<^bsub>K'\<^esub> \<in> carrier (Vr K v)",
       subgoal_tac " (\<zero>\<^bsub>K'\<^esub> \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> \<zero>\<^bsub>K'\<^esub>)\<in> vp K' v'", blast,
       frule aGroup.ag_inc_zero[of "K'"], simp add:aGroup.ag_r_inv1,
       simp add:Corps.Vr_0_f_0[THEN sym, of "K'" "v'"],
       frule Corps.Vr_ring[of "K'" "v'"], assumption+,
       frule Corps.vp_ideal[of "K'" "v'"], assumption+,
       simp add:Ring.ideal_zero,
       simp add:subfield_zero[THEN sym, of  "K'"],
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule aGroup.ag_inc_zero[of "K"],
       simp add:Vr_0_f_0[THEN sym, of "v"],
       frule Vr_ring[of "v"],simp add:Ring.ring_zero)
      apply (frule_tac f = f in Corps.limit_val[of "K'" "x" _ "v'"], 
                         assumption+)
      apply (rule allI, rotate_tac -2, frule_tac x = j in spec,
             frule subfield_sub[of K'], simp add:subsetD, assumption+)
apply (erule exE)
 apply (simp add:limit_def,
        frule Corps.Vr_ring[of K' v'], assumption+,
        rotate_tac 10,
              drule_tac x = "Suc 0" in spec, erule exE,
       rotate_tac 1,
              frule_tac x = N and y = M in two_inequalities, assumption+,
              thin_tac "\<forall>n>N. v' (f n) = v' x",
              thin_tac "\<forall>n>M. f n \<plusminus>\<^bsub>K'\<^esub> -\<^sub>a\<^bsub>K'\<^esub> x \<in> vp K' v'\<^bsup> (Vr K' v') (an (Suc 0))\<^esup>")
       apply (frule Corps.vp_ideal[of K' v'], assumption+,
              simp add:Ring.r_apow_Suc[of "Vr K' v'" "vp K' v'"])
       apply (drule_tac x = "N + M + 1" in spec, simp,
              drule_tac x = "N + M + 1" in spec, simp,
              erule conjE)
 apply (drule_tac x = "f (Suc (N + M))" in bspec, assumption+)
 apply simp 
 apply (cut_tac x = "f (Suc (N + M))" in val_pos_mem_Vr[of v], assumption+)
 apply simp apply blast
done

lemma (in Corps) res_v_completion_surj:"\<lbrakk> Corps K'; valuation K v; 
      valuation K' v'; Completion\<^bsub>v v'\<^esub> K K'\<rbrakk> \<Longrightarrow> 
      surjec\<^bsub>(Vr K v),(qring (Vr K' v') (vp K' v'))\<^esub> 
            (compos (Vr K v) (pj (Vr K' v') (vp K' v')) (I\<^bsub>(Vr K v)\<^esub>))"
apply (frule Vr_ring[of "v"], 
       frule Ring.ring_is_ag[of "Vr K v"],
       frule Corps.Vr_ring[of "K'" "v'"], assumption+,
       frule Ring.ring_is_ag[of "Vr K' v'"],
       frule Ring.ring_is_ag[of "Vr K v"])
apply (frule Corps.vp_ideal[of "K'" "v'"], assumption+, 
       frule Ring.qring_ring[of "Vr K' v'" "vp K' v'"], assumption+)
apply (simp add:surjec_def)
apply (frule aHom_compos[of "Vr K v" "Vr K' v'" 
      "qring (Vr K' v') (vp K' v')" "I\<^bsub>(Vr K v)\<^esub>" 
      "pj (Vr K' v') (vp K' v')"], assumption+, simp add:Ring.ring_is_ag)
apply (rule Vr_idmap_aHom, assumption+) apply (simp add:completion_subfield,
      simp add:v_completion_def) apply (
      frule pj_Hom[of "Vr K' v'" "vp K' v'"], assumption+) apply ( 
      simp add:rHom_def, simp)
apply (rule surj_to_test)
 apply (simp add:aHom_def)
apply (rule ballI) 
 apply (thin_tac "Ring (Vr K' v' /\<^sub>r vp K' v')",
  thin_tac "compos (Vr K v) (pj (Vr K' v') (vp K' v')) (I\<^bsub>(Vr K v)\<^esub>) \<in> 
               aHom (Vr K v) (Vr K' v' /\<^sub>r vp K' v')")
 apply (simp add:Ring.qring_carrier)
 apply (erule bexE)
 apply (frule_tac x = a in completion_approx[of "K'" "v" "v'"], 
       assumption+, erule bexE)
 apply (subgoal_tac "compos (Vr K v) (pj (Vr K' v') 
                     (vp K' v')) ((I\<^bsub>(Vr K v)\<^esub>)) y = b", blast)
 apply (simp add:compos_def compose_def idmap_def)
 apply (frule completion_Vring_sub[of "K'" "v" "v'"], assumption+)
 apply (frule_tac c = y in subsetD[of "carrier (Vr K v)" "carrier (Vr K' v')"],
         assumption+)
 apply (frule_tac x = y in pj_mem[of "Vr K' v'" "vp K' v'"], assumption+, simp,
        thin_tac "pj (Vr K' v') (vp K' v') y = y \<uplus>\<^bsub>(Vr K' v')\<^esub> (vp K' v')")
 apply (rotate_tac -5, frule sym, thin_tac "a \<uplus>\<^bsub>(Vr K' v')\<^esub> (vp K' v') = b", 
       simp)
 apply (rule_tac b1 = y and a1 = a in Ring.ar_coset_same1[THEN sym, 
        of "Vr K' v'" "vp K' v'"], assumption+)
 apply (frule Ring.ring_is_ag[of "Vr K' v'"], 
        frule_tac x = a in aGroup.ag_mOp_closed[of "Vr K' v'"],
        assumption+)
 apply (simp add:Corps.Vr_mOp_f_mOp, simp add:Corps.Vr_pOp_f_pOp)
done

lemma (in Corps) res_v_completion_ker:"\<lbrakk>Corps K'; valuation K v; 
      valuation K' v'; Completion\<^bsub>v v'\<^esub> K K'\<rbrakk> \<Longrightarrow> 
  ker\<^bsub>(Vr K v), (qring (Vr K' v') (vp K' v'))\<^esub> 
  (compos (Vr K v) (pj (Vr K' v') (vp K' v')) (I\<^bsub>(Vr K v)\<^esub>)) = vp K v"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:ker_def, (erule conjE)+)
 apply (frule Corps.Vr_ring[of "K'" "v'"], assumption+,
        frule Corps.vp_ideal[of "K'" "v'"], assumption+,
        frule Ring.qring_ring[of "Vr K' v'" "vp K' v'"], assumption+,
        simp add:Ring.qring_zero)
 apply (simp add:compos_def, simp add:compose_def, simp add:idmap_def)
 apply (frule completion_Vring_sub[of "K'" "v" "v'"], assumption+)
 apply (frule_tac c = x in subsetD[of "carrier (Vr K v)" "carrier (Vr K' v')"],
        assumption+)
 apply (simp add:pj_mem)
 apply (frule_tac a = x in Ring.qring_zero_1[of "Vr K' v'" _  "vp K' v'"], 
        assumption+)
 apply (subst vp_mem_val_poss[of v], assumption+) 
 apply (simp add:Vr_mem_f_mem)
 apply (frule_tac x = x in Corps.vp_mem_val_poss[of "K'" "v'"],
        assumption+, simp add:Corps.Vr_mem_f_mem, simp)
apply (frule_tac x = x in Vr_mem_f_mem[of v], assumption+)
 apply (frule_tac x = x in completion_val_eq[of "K'" "v" "v'"],
         assumption+, simp)
apply (rule subsetI)
 apply (simp add:ker_def)
 apply (frule Vr_ring[of  "v"])
 apply (frule vp_ideal[of "v"])
 apply (frule_tac h = x in Ring.ideal_subset[of "Vr K v" "vp K v"],
         assumption+, simp)
 apply (frule Corps.Vr_ring[of "K'" "v'"], assumption+,
        frule Corps.vp_ideal[of "K'" "v'"], assumption+, 
        simp add:Ring.qring_zero)
 apply (simp add:compos_def compose_def idmap_def)
 apply (frule completion_Vring_sub[of "K'" "v" "v'"],
        assumption+, frule_tac c = x in subsetD[of "carrier (Vr K v)"
        "carrier (Vr K' v')"], assumption+)
 apply (simp add:pj_mem)
 apply (frule completion_vpr_sub[of "K'" "v" "v'"], assumption+,
        frule_tac c = x in subsetD[of "vp K v" "vp K' v'"], assumption+)
 apply (simp add:Ring.ar_coset_same4[of "Vr K' v'" "vp K' v'"])
done 

lemma (in Corps) completion_res_qring_isom:"\<lbrakk>Corps K'; valuation K v; 
  valuation K' v'; Completion\<^bsub>v v'\<^esub> K K'\<rbrakk>  \<Longrightarrow> 
   r_isom ((Vr K v) /\<^sub>r (vp K v)) ((Vr K' v') /\<^sub>r (vp K' v'))"
apply (subst r_isom_def)
apply (frule res_v_completion_surj[of "K'" "v" "v'"], assumption+)
apply (frule Vr_ring[of "v"],
       frule Corps.Vr_ring[of "K'" "v'"], assumption+,
       frule Corps.vp_ideal[of "K'" "v'"], assumption+,
       frule Ring.qring_ring[of "Vr K' v'" "vp K' v'"], assumption+)
apply (frule rHom_compos[of "Vr K v" "Vr K' v'" "(Vr K' v' /\<^sub>r vp K' v')" 
       "(I\<^bsub>(Vr K v)\<^esub>)" "pj (Vr K' v') (vp K' v')"], assumption+)
apply (simp add:completion_idmap_rHom)
apply (simp add:pj_Hom) 
apply (frule surjec_ind_bijec [of "Vr K v" "(Vr K' v' /\<^sub>r vp K' v')" 
      "compos (Vr K v) (pj (Vr K' v') (vp K' v')) (I\<^bsub>(Vr K v)\<^esub>)"], assumption+)
apply (frule ind_hom_rhom[of "Vr K v" "(Vr K' v' /\<^sub>r vp K' v')" 
       "compos (Vr K v) (pj (Vr K' v') (vp K' v')) (I\<^bsub>(Vr K v)\<^esub>)"], assumption+)
apply (simp add:res_v_completion_ker) apply blast
done

text\<open>expansion of x in a complete field K, with normal valuation v. Here
we suppose t is an element of K satisfying the equation \<open>v t = 1\<close>.\<close>

definition
  Kxa :: "[_, 'b \<Rightarrow> ant, 'b] \<Rightarrow> 'b set" where
  "Kxa K v x = {y. \<exists>k\<in>carrier (Vr K v). y = x \<cdot>\<^sub>r\<^bsub>K\<^esub> k}"
    (**  x *\<^sub>r carrier (Vr K v) **)

primrec 
  partial_sum :: "[('b, 'm) Ring_scheme, 'b, 'b \<Rightarrow> ant, 'b] 
                                   \<Rightarrow> nat \<Rightarrow> 'b"
        ("(5psum\<^bsub> _ _ _ _\<^esub> _)" [96,96,96,96,97]96)
where
  psum_0: "psum\<^bsub> K x v t\<^esub> 0 = (csrp_fn (Vr K v) (vp K v) 
     (pj (Vr K v) (vp K v) (x \<cdot>\<^sub>r\<^bsub>K\<^esub> t\<^bsub>K\<^esub>\<^bsup>-(tna (v x))\<^esup>))) \<cdot>\<^sub>r\<^bsub>K\<^esub> (t\<^bsub>K\<^esub>\<^bsup>(tna (v x))\<^esup>)"
| psum_Suc: "psum\<^bsub> K x v t\<^esub> (Suc n) = (psum\<^bsub> K x v t\<^esub> n) \<plusminus>\<^bsub>K\<^esub> 
  ((csrp_fn (Vr K v) (vp K v) (pj (Vr K v) (vp K v)  
   ((x \<plusminus>\<^bsub>K\<^esub> -\<^sub>a\<^bsub>K\<^esub> (psum\<^bsub> K x v t\<^esub> n)) \<cdot>\<^sub>r\<^bsub>K\<^esub> (t\<^bsub>K\<^esub>\<^bsup>- (tna (v x) + int (Suc n))\<^esup>)))) \<cdot>\<^sub>r\<^bsub>K\<^esub> 
         (t\<^bsub>K\<^esub>\<^bsup>(tna (v x) + int (Suc n))\<^esup>))" 

definition
  expand_coeff :: "[_ , 'b \<Rightarrow> ant, 'b, 'b] 
                      \<Rightarrow> nat \<Rightarrow> 'b"
                   ("(5ecf\<^bsub>_ _ _ _\<^esub> _)" [96,96,96,96,97]96) where
  "ecf\<^bsub>K v t x\<^esub> n = (if n = 0 then  csrp_fn (Vr K v) (vp K v) 
     (pj (Vr K v) (vp K v) (x \<cdot>\<^sub>r\<^bsub>K\<^esub> t\<^bsub>K\<^esub>\<^bsup>(-(tna (v x)))\<^esup>))
     else csrp_fn (Vr K v) (vp K v) (pj (Vr K v) 
  (vp K v) ((x \<plusminus>\<^bsub>K\<^esub> -\<^sub>a\<^bsub>K\<^esub> (psum\<^bsub> K x v t\<^esub> (n - 1))) \<cdot>\<^sub>r\<^bsub>K\<^esub> (t\<^bsub>K\<^esub>\<^bsup>(- (tna (v x) + int n))\<^esup>))))" 

definition
  expand_term :: "[_, 'b \<Rightarrow> ant, 'b, 'b] 
                      \<Rightarrow> nat \<Rightarrow> 'b"
                   ("(5etm\<^bsub> _ _ _ _\<^esub> _)" [96,96,96,96,97]96) where
        
  "etm\<^bsub>K v t x\<^esub> n = (ecf\<^bsub>K v t x\<^esub> n)\<cdot>\<^sub>r\<^bsub>K\<^esub> (t\<^bsub>K\<^esub>\<^bsup>(tna (v x) + int n)\<^esup>)"



(*** Let O be the valuation ring with respect to the valuation v and let P
be the maximal ideal of O. Let j be the value of x (\<in> O), and  a\<^sub>0 be an 
element of the complete set of representatives such that a\<^sub>0 = x t\<^sup>-\<^sup>j mod P.
 We see that (a\<^sub>0 - x t\<^sup>-\<^sup>j)/t is an element of O, and then we choose a\<^sub>1 an 
element of the complete set of representatives which is equal to (a\<^sub>0 - x t\<^sup>-\<^sup>j)/tmodulo P. We see x - (a\<^sub>0t\<^sup>j + a\<^sub>1t\<^bsup>(j+1)\<^esup> + \<dots> + a\<^sub>st\<^bsup>(j+s)\<^esup>) \<in> (t\<^bsup>(j+s+1)\<^esup>). 
"psum G a i K v t x s" is the partial sum a\<^sub>0t\<^sup>j + a\<^sub>1t\<^bsup>(j+1)\<^esup> + \<dots> + a\<^sub>st\<^bsup>(j+s)\<^esup> ***)  

lemma (in Corps) Kxa_val_ge:"\<lbrakk>valuation K v; t \<in> carrier K; v t = 1\<rbrakk> 
 \<Longrightarrow>  Kxa K v (t\<^bsub>K\<^esub>\<^bsup>j\<^esup>) = {x. x \<in> carrier K \<and> (ant j) \<le> (v x)}"
apply (frule val1_neq_0[of v t], assumption+)
apply (cut_tac field_is_ring) 
apply (rule equalityI)
 apply (rule subsetI,
        simp add:Kxa_def, erule bexE,
        frule_tac x = k in Vr_mem_f_mem[of "v"], assumption+,
        frule npowf_mem[of "t" "j"], simp, 
        simp add:Ring.ring_tOp_closed)
 apply (simp add:val_t2p) apply (simp add:val_exp[THEN sym]) 
 apply (simp add:val_pos_mem_Vr[THEN sym, of "v"])
 apply (frule_tac x = 0 and y = "v k" in aadd_le_mono[of _ _ "ant j"])
 apply (simp add:aadd_0_l aadd_commute)
apply (rule subsetI, simp, erule conjE)
 apply (simp add:Kxa_def)
 apply (case_tac "x = \<zero>\<^bsub>K\<^esub>")
 apply (frule Vr_ring[of "v"], 
        frule Ring.ring_zero[of "Vr K v"],
        simp add:Vr_0_f_0,
        frule_tac x1 = "t\<^bsub>K\<^esub>\<^bsup>j\<^esup>" in Ring.ring_times_x_0[THEN sym, of "K"],
        simp add:npowf_mem, blast)
 apply (frule val_exp[of "v" "t" "j"], assumption+, simp) 
 apply (frule field_potent_nonzero1[of "t" "j"], 
        frule npowf_mem[of "t" "j"], assumption+)
 apply (frule_tac y = "v x" in ale_diff_pos[of "v (t\<^bsub>K\<^esub>\<^bsup>j\<^esup>)"], 
        simp add:diff_ant_def)
apply (cut_tac npowf_mem[of t j]) 
 defer 
 apply assumption apply simp
apply (frule value_of_inv[THEN sym, of "v" "t\<^bsub>K\<^esub>\<^bsup>j\<^esup>"], assumption+) 
 
 apply (cut_tac invf_closed1[of "t\<^bsub>K\<^esub>\<^bsup>j\<^esup>"], simp, erule conjE)
 apply (frule_tac x1 = x in val_t2p[THEN sym, of "v" _ "(t\<^bsub>K\<^esub>\<^bsup>j\<^esup>)\<^bsup>\<hyphen>K\<^esup>"], 
        assumption+, simp)
 apply (frule_tac x = "(t\<^bsub>K\<^esub>\<^bsup>j\<^esup>)\<^bsup>\<hyphen>K\<^esup>" and y = x in Ring.ring_tOp_closed[of "K"], 
          assumption+)
 apply (simp add:Ring.ring_tOp_commute[of "K" _ "(t\<^bsub>K\<^esub>\<^bsup>j\<^esup>)\<^bsup>\<hyphen>K\<^esup>"])
 apply (frule_tac x = "((t\<^bsub>K\<^esub>\<^bsup>j\<^esup>)\<^bsup>\<hyphen>K\<^esup>) \<cdot>\<^sub>r x" in val_pos_mem_Vr[of v], assumption+, 
        simp)
 apply (frule_tac z = x in Ring.ring_tOp_assoc[of "K" "t\<^bsub>K\<^esub>\<^bsup>j\<^esup>" "(t\<^bsub>K\<^esub>\<^bsup>j\<^esup>)\<^bsup>\<hyphen>K\<^esup>"], 
         assumption+) 
 apply (simp add:Ring.ring_tOp_commute[of K "t\<^bsub>K\<^esub>\<^bsup>j\<^esup>" "(t\<^bsub>K\<^esub>\<^bsup>j\<^esup>)\<^bsup>\<hyphen> K\<^esup>"] linvf,
        simp add:Ring.ring_l_one, blast) 
 apply simp
done

lemma (in Corps) Kxa_pow_vpr:"\<lbrakk> valuation K v; t \<in> carrier K; v t = 1;
    (0::int) \<le> j\<rbrakk> \<Longrightarrow> Kxa K v (t\<^bsub>K\<^esub>\<^bsup>j\<^esup>) = (vp K v)\<^bsup>(Vr K v) (ant j)\<^esup>"
apply (frule val_surj_n_val[of v], blast) 
apply (simp add:Kxa_val_ge) 
apply (rule equalityI)
 apply (rule subsetI, simp, erule conjE)
 apply (rule_tac x = x in n_value_x_2[of "v" _ "(ant j)"],
            assumption+)
 apply (cut_tac ale_zle[THEN sym, of "0" "j"]) 
 apply (frule_tac a = "0 \<le> j" and b = "ant 0 \<le> ant j" in a_b_exchange,
         assumption+) 
 apply (thin_tac "(0 \<le> j) = (ant 0 \<le> ant j)", simp add:ant_0)
 apply (frule_tac k = "v x" in ale_trans[of "0" "ant j"], assumption+)
 apply (simp add:val_pos_mem_Vr) apply simp
 apply (simp only:ale_zle[THEN sym, of "0" "j"], simp add:ant_0)
apply (rule subsetI)
 apply simp 
 apply (frule_tac x = x in mem_vp_apow_mem_Vr[of "v" "ant j"]) 
 apply (simp only:ale_zle[THEN sym, of "0" "j"], simp add:ant_0) 
 apply assumption
apply (simp add:Vr_mem_f_mem[of "v"])
apply (frule_tac x = x in n_value_x_1[of "v" "ant j" _ ])
 apply (simp only:ale_zle[THEN sym, of "0" "j"], simp add:ant_0) 
 apply assumption apply simp
done  

lemma (in Corps) field_distribTr:"\<lbrakk>a \<in> carrier K; b \<in> carrier K; 
      x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow> a \<plusminus> (-\<^sub>a (b \<cdot>\<^sub>r x)) = (a \<cdot>\<^sub>r (x\<^bsup>\<hyphen>K\<^esup>) \<plusminus> (-\<^sub>a b)) \<cdot>\<^sub>r x"
apply (cut_tac field_is_ring,
       cut_tac invf_closed1[of x], simp, erule conjE) apply (
       simp add:Ring.ring_inv1_1[of "K" "b" "x"],
       frule Ring.ring_is_ag[of "K"],
       frule aGroup.ag_mOp_closed[of "K" "b"], assumption+)
apply (frule Ring.ring_tOp_closed[of "K" "a" "x\<^bsup>\<hyphen>K\<^esup>"], assumption+,
       simp add:Ring.ring_distrib2, simp add:Ring.ring_tOp_assoc, 
       simp add:linvf,
       simp add:Ring.ring_r_one)
apply simp
done

lemma a0_le_1[simp]:"(0::ant) \<le> 1"
by (cut_tac a0_less_1, simp add:aless_imp_le)

lemma (in Corps) vp_mem_times_t:"\<lbrakk>valuation K v; t \<in> carrier K; t \<noteq> \<zero>; 
       v t = 1; x \<in> vp K v\<rbrakk> \<Longrightarrow> \<exists>a\<in>carrier (Vr K v). x = a \<cdot>\<^sub>r t" 
apply (frule Vr_ring[of v],
       frule vp_ideal[of v]) 
 apply (frule val_surj_n_val[of v], blast)
 apply (frule vp_mem_val_poss[of v x],
        frule_tac h = x in Ring.ideal_subset[of "Vr K v" "vp K v"], 
        assumption+, simp add:Vr_mem_f_mem, simp) 
 apply (frule gt_a0_ge_1[of "v x"])
 apply (subgoal_tac "v t \<le> v x") 
 apply (thin_tac "1 \<le> v x")
 apply (frule val_Rxa_gt_a_1[of "v" "t" "x"])
 apply (subst val_pos_mem_Vr[THEN sym, of "v" "t"], assumption+)
 apply simp 
 apply (simp add:vp_mem_Vr_mem) apply assumption+
 apply (simp add:Rxa_def, erule bexE) 
 apply (cut_tac a0_less_1) 
 apply (subgoal_tac "0 \<le> v t")
 apply (frule val_pos_mem_Vr[of "v" "t"], assumption+)
 apply (simp, simp add:Vr_tOp_f_tOp, blast, simp+)
done

lemma (in Corps) psum_diff_mem_Kxa:"\<lbrakk>valuation K v; t \<in> carrier K; 
      v t = 1; x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow> 
     (psum\<^bsub> K x v t\<^esub> n) \<in> carrier K \<and> 
     ( x \<plusminus> (-\<^sub>a (psum\<^bsub> K x v t\<^esub> n))) \<in> Kxa K v (t\<^bsub>K\<^esub>\<^bsup>((tna (v x)) + (1 + int n))\<^esup>)"
apply (frule val1_neq_0[of v t], assumption+)
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule Vr_ring[of v], frule vp_ideal[of v])
apply (induct_tac n)
apply (subgoal_tac "x \<cdot>\<^sub>r (t\<^bsub>K\<^esub>\<^bsup>- tna (v x)\<^esup>) \<in> carrier (Vr K v)",
       rule conjI, simp, rule Ring.ring_tOp_closed[of "K"], assumption+,
       frule Ring.csrp_fn_mem[of "Vr K v" "vp K v" 
       "pj (Vr K v) (vp K v) (x \<cdot>\<^sub>r (t\<^bsub>K\<^esub>\<^bsup>- tna (v x)\<^esup>))"], 
       assumption+,
       simp add:pj_mem Ring.qring_carrier, blast,
       simp add:Vr_mem_f_mem, simp add:npowf_mem)
apply (simp, 
     frule npowf_mem[of "t" "tna (v x)"], assumption+,
     frule field_potent_nonzero1[of "t" "tna (v x)"], assumption+,
     subst field_distribTr[of "x" _ "t\<^bsub>K\<^esub>\<^bsup>(tna (v x))\<^esup>"], assumption+,
     frule Ring.csrp_fn_mem[of "Vr K v" "vp K v" 
     "pj (Vr K v) (vp K v) (x \<cdot>\<^sub>r (t\<^bsub>K\<^esub>\<^bsup>- tna (v x)\<^esup>))"], 
     assumption+,
     simp add:pj_mem Ring.qring_carrier, blast, simp add:Vr_mem_f_mem,
     simp add:npowf_mem, assumption) 
apply (frule Ring.csrp_diff_in_vpr[of "Vr K v" "vp K v" 
       "x \<cdot>\<^sub>r ((t\<^bsub>K\<^esub>\<^bsup>(tna (v x))\<^esup>)\<^bsup>\<hyphen>K\<^esup>)"], assumption+) 
      apply (simp add:npowf_minus)
 
 apply (simp add:npowf_minus)
 apply (frule pj_Hom[of "Vr K v" "vp K v"], assumption+)
 apply (frule rHom_mem[of "pj (Vr K v) (vp K v)" "Vr K v" "Vr K v /\<^sub>r vp K v" 
        "x \<cdot>\<^sub>r (t\<^bsub>K\<^esub>\<^bsup>- tna (v x)\<^esup>)"], assumption+)
 apply (frule Ring.csrp_fn_mem[of "Vr K v" "vp K v" 
         "pj (Vr K v) (vp K v) (x \<cdot>\<^sub>r (t\<^bsub>K\<^esub>\<^bsup>- tna (v x)\<^esup>))"], assumption+)
 apply (frule Ring.ring_is_ag[of "Vr K v"], 
        frule_tac x = "csrp_fn (Vr K v) (vp K v) (pj (Vr K v) (vp K v) 
       (x \<cdot>\<^sub>r (t\<^bsub>K\<^esub>\<^bsup>- tna (v x)\<^esup>)))" in aGroup.ag_mOp_closed[of "Vr K v"], assumption+)
 apply (simp add:Vr_pOp_f_pOp) apply (simp add:Vr_mOp_f_mOp)
apply (frule_tac x = "x \<cdot>\<^sub>r (t\<^bsub>K\<^esub>\<^bsup>- tna (v x)\<^esup>) \<plusminus> -\<^sub>a (csrp_fn (Vr K v) (vp K v)
      (pj (Vr K v) (vp K v) (x \<cdot>\<^sub>r (t\<^bsub>K\<^esub>\<^bsup>- tna (v x)\<^esup>))))" in 
      vp_mem_times_t[of "v" "t"], assumption+, erule bexE, simp)
apply (frule_tac x = a in Vr_mem_f_mem[of  "v"], assumption+)
apply (simp add:Ring.ring_tOp_assoc[of "K"])
 apply (simp add:npowf_exp_1_add[THEN sym, of "t" "tna (v x)"]) 
 apply (simp add:add.commute)
apply (simp add:Kxa_def) 
apply (frule npowf_mem[of "t" "1 + tna (v x)"], assumption+)
apply (simp add:Ring.ring_tOp_commute[of "K" _ "t\<^bsub>K\<^esub>\<^bsup>(1 + tna (v x))\<^esup>"])
 apply blast
 apply (frule npowf_mem[of  "t" "- tna (v x)"], assumption+)
 apply (frule Ring.ring_tOp_closed[of "K" "x" "t\<^bsub>K\<^esub>\<^bsup>- tna (v x)\<^esup>"], assumption+)
apply (subst val_pos_mem_Vr[THEN sym, of v], assumption+)
 apply (simp add:val_t2p) apply (simp add:val_exp[THEN sym, of "v" "t"])
 apply (simp add:aminus[THEN sym])
 apply (frule value_in_aug_inf[of "v" "x"], assumption+, 
        simp add:aug_inf_def)
 apply (frule val_nonzero_noninf[of "v" "x"], assumption+,
         simp add:ant_tna)
 apply (simp add:aadd_minus_r)

apply (erule conjE)
 apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
 apply (rule conjI)
 apply simp
 apply (rule aGroup.ag_pOp_closed, assumption+)
 apply (rule Ring.ring_tOp_closed[of "K"], assumption+)
 apply (simp add:Kxa_def, erule bexE, simp)
 apply (subst Ring.ring_tOp_commute, assumption+)
 apply (rule npowf_mem, assumption+) apply (simp add:Vr_mem_f_mem)
 apply (frule_tac n = "tna (v x) + (1 + int n)" in npowf_mem[of t ], 
        assumption,
        frule_tac n = "- tna (v x) + (-1 - int n)" in npowf_mem[of t ], 
        assumption,
        frule_tac x = k in Vr_mem_f_mem[of v], assumption+)
 apply (simp add:Ring.ring_tOp_assoc npowf_exp_add[THEN sym, of t])
  apply (simp add:field_npowf_exp_zero) 
  apply (simp add:Ring.ring_r_one)

 apply (frule pj_Hom[of "Vr K v" "vp K v"], assumption+)
 apply (frule_tac a = k in rHom_mem[of "pj (Vr K v) (vp K v)" "Vr K v" 
        "Vr K v /\<^sub>r vp K v"], assumption+)
 apply (frule_tac x = "pj (Vr K v) (vp K v) k" in Ring.csrp_fn_mem[of "Vr K v" 
        "vp K v"], assumption+)
 apply (simp add:Vr_mem_f_mem)
 apply (rule npowf_mem, assumption+)

apply (simp add:Kxa_def) apply (erule bexE, simp)
apply (frule_tac x = k in Vr_mem_f_mem[of "v"], assumption+)
apply (frule_tac n = "tna (v x) + (1 + int n)" in npowf_mem[of "t"], 
       assumption+)
apply (frule_tac n = "- tna (v x) + (- 1 - int n)" in npowf_mem[of "t"], 
       assumption+)
apply (frule_tac x = "t\<^bsub>K\<^esub>\<^bsup>(tna (v x) + (1 + int n))\<^esup>" and y = k in 
      Ring.ring_tOp_commute[of "K"], assumption+) apply simp
apply (simp add:Ring.ring_tOp_assoc, simp add:npowf_exp_add[THEN sym])
   apply (simp add:field_npowf_exp_zero) 
   apply (simp add:Ring.ring_r_one)
   apply (thin_tac "(t\<^bsub>K\<^esub>\<^bsup>(tna (v x) + (1 + int n))\<^esup>) \<cdot>\<^sub>r k =
            k \<cdot>\<^sub>r (t\<^bsub>K\<^esub>\<^bsup>(tna (v x) + (1 + int n))\<^esup>)")
apply (frule pj_Hom[of "Vr K v" "vp K v"], assumption+)
apply (frule_tac a = k in rHom_mem[of "pj (Vr K v) (vp K v)" "Vr K v" 
        "Vr K v /\<^sub>r vp K v"], assumption+)
 apply (frule_tac x = "pj (Vr K v) (vp K v) k" in Ring.csrp_fn_mem[of "Vr K v" 
        "vp K v"], assumption+)
 apply (frule_tac x = "csrp_fn (Vr K v) (vp K v) (pj (Vr K v) (vp K v) k)" in 
        Vr_mem_f_mem[of v], assumption+)
 apply (frule_tac x = "csrp_fn (Vr K v) (vp K v) (pj (Vr K v) (vp K v) k)" and
 y = "t\<^bsub>K\<^esub>\<^bsup>(tna (v x) + (1 + int n))\<^esup>" in Ring.ring_tOp_closed[of "K"], assumption+)
 apply (simp add:aGroup.ag_p_inv[of "K"])
 apply (frule_tac x = "psum\<^bsub> K x v t\<^esub> n" in aGroup.ag_mOp_closed[of "K"], 
          assumption+)
 apply (frule_tac x = "(csrp_fn (Vr K v) (vp K v)(pj (Vr K v) (vp K v) k)) \<cdot>\<^sub>r
       (t\<^bsub>K\<^esub>\<^bsup>(tna (v x) + (1 + int n))\<^esup>)" in aGroup.ag_mOp_closed[of "K"], assumption+)
 apply (subst aGroup.ag_pOp_assoc[THEN sym], assumption+)
 apply simp
 apply (simp add:Ring.ring_inv1_1)
 apply (subst Ring.ring_distrib2[THEN sym, of "K"], assumption+)
 apply (rule aGroup.ag_mOp_closed, assumption+)
 apply (frule_tac x = k in  Ring.csrp_diff_in_vpr[of "Vr K v" "vp K v"]
     , assumption+)
 apply (frule Ring.ring_is_ag[of "Vr K v"])
 apply (frule_tac x = "csrp_fn (Vr K v) (vp K v) (pj (Vr K v) (vp K v) k)" in 
        aGroup.ag_mOp_closed[of "Vr K v"], assumption+)
 apply (simp add:Vr_pOp_f_pOp) apply (simp add:Vr_mOp_f_mOp)
 apply (frule_tac x = "k \<plusminus> -\<^sub>a (csrp_fn (Vr K v) (vp K v) (pj (Vr K v) (vp K v)
 k))" in vp_mem_times_t[of "v" "t"], assumption+, erule bexE, simp)
 apply (frule_tac x = a in Vr_mem_f_mem[of v], assumption+)
 apply (simp add:Ring.ring_tOp_assoc[of "K"])
 apply (simp add:npowf_exp_1_add[THEN sym, of "t"])
 apply (simp add:add.commute[of "2"])
 apply (simp add:add.assoc)
 apply (subst Ring.ring_tOp_commute, assumption+)
 apply (rule npowf_mem, assumption+) apply blast
done

lemma Suc_diff_int:"0 < n \<Longrightarrow> int (n - Suc 0) = int n - 1" 
by (cut_tac of_nat_Suc[of "n - Suc 0"], simp)

lemma (in Corps) ecf_mem:"\<lbrakk>valuation K v; t \<in> carrier K; v t = 1; 
      x \<in> carrier K; x \<noteq> \<zero> \<rbrakk> \<Longrightarrow>  ecf\<^bsub>K v t x\<^esub> n \<in> carrier K"
apply (frule val1_neq_0[of v t], assumption+)
apply (cut_tac field_is_ring,
       frule Vr_ring[of v], frule vp_ideal[of v])
apply (case_tac "n = 0")
 apply (simp add:expand_coeff_def)
 apply (rule Vr_mem_f_mem[of v], assumption+)
 apply (rule Ring.csrp_fn_mem, assumption+)
 apply (subgoal_tac "x \<cdot>\<^sub>r (t\<^bsub>K\<^esub>\<^bsup>- tna (v x)\<^esup>) \<in> carrier (Vr K v)")
 apply (simp add:pj_mem Ring.qring_carrier, blast)
apply (frule npowf_mem[of  "t" "- tna (v x)"], assumption+,
       subst val_pos_mem_Vr[THEN sym, of v "x \<cdot>\<^sub>r (t\<^bsub>K\<^esub>\<^bsup>(- tna(v x))\<^esup>)"], 
       assumption+,
       rule Ring.ring_tOp_closed, assumption+) 
apply (simp add:val_t2p,
       simp add:val_exp[THEN sym, of  "v" "t" "- tna (v x)"]) 
apply (frule value_in_aug_inf[of  "v" "x"], assumption+,
       simp add:aug_inf_def)
      apply (frule val_nonzero_noninf[of  "v" "x"], assumption+)
  apply (simp add:aminus[THEN sym], simp add:ant_tna)
  apply (simp add:aadd_minus_r)

apply (simp add:expand_coeff_def) 
apply (frule psum_diff_mem_Kxa[of  "v" "t" "x" "n - 1"],
                   assumption+, erule conjE)
apply (simp add:Kxa_def, erule bexE,
       frule_tac x = k in Vr_mem_f_mem[of v], assumption+,
     frule npowf_mem[of  "t" "tna (v x) + (1 + int (n - Suc 0))"], 
     assumption+,
   frule npowf_mem[of  "t" "-tna (v x) - int n"], assumption+)
  apply simp
  apply (thin_tac "x \<plusminus> -\<^sub>a psum\<^bsub> K x v t\<^esub> (n - Suc 0) =
          (t\<^bsub>K\<^esub>\<^bsup>(tna (v x) + (1 + int (n - Suc 0)))\<^esup>) \<cdot>\<^sub>r k")
apply(simp add:Ring.ring_tOp_commute[of "K" "t\<^bsub>K\<^esub>\<^bsup>(tna (v x) + (1 + int (n - Suc 0)))\<^esup>"])
 apply (simp add:Ring.ring_tOp_assoc, simp add:npowf_exp_add[THEN sym])
 apply (thin_tac "t\<^bsub>K\<^esub>\<^bsup>(tna (v x) + (1 + int (n - Suc 0)))\<^esup> \<in> carrier K",
        thin_tac "t\<^bsub>K\<^esub>\<^bsup>(- tna (v x) - int n)\<^esup> \<in> carrier K")
 apply (simp add:Suc_diff_int[of "n"])
 apply (simp add:npowf_def, simp add:Ring.ring_r_one)
apply (rule Vr_mem_f_mem, assumption+)
 apply (rule Ring.csrp_fn_mem, assumption+)
 apply (simp add:pj_mem Ring.qring_carrier, blast)
done

lemma (in Corps) etm_mem:"\<lbrakk>valuation K v; t \<in> carrier K; v t = 1; 
     x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow> etm\<^bsub>K v t x\<^esub> n \<in> carrier K"
apply (frule val1_neq_0[of v t], assumption+)
apply (simp add:expand_term_def)
apply (cut_tac field_is_ring,
       rule Ring.ring_tOp_closed[of "K"], assumption)
apply (simp add:ecf_mem)
apply (simp add:npowf_mem)
done

lemma (in Corps) psum_sum_etm:"\<lbrakk>valuation K v; t \<in> carrier K; v t = 1; 
      x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow> 
 psum\<^bsub>K x v t\<^esub> n = nsum K (\<lambda>j. (ecf\<^bsub>K v t x\<^esub> j)\<cdot>\<^sub>r (t\<^bsub>K\<^esub>\<^bsup>(tna (v x) + (int j))\<^esup>)) n" 
apply (frule val1_neq_0[of v t], assumption+)
apply (induct_tac "n")
 apply (simp add:expand_coeff_def)
apply (rotate_tac -1, drule sym)
apply simp
 apply (thin_tac "\<Sigma>\<^sub>e K (\<lambda>j. ecf\<^bsub>K v t x\<^esub> j \<cdot>\<^sub>r t\<^bsub>K\<^esub>\<^bsup>(tna (v x) + int j)\<^esup>) n =
         psum\<^bsub> K x v t\<^esub> n")
 apply (simp add:expand_coeff_def)
done

lemma zabs_pos:"0 \<le> (abs (z::int))"
by (simp add:zabs_def)

lemma abs_p_self_pos:"0 \<le> z + (abs (z::int))"
by (simp add:zabs_def)

lemma zadd_right_mono:"(i::int) \<le> j \<Longrightarrow> i  + k \<le> j  + k"
by simp

theorem (in Corps) expansion_thm:"\<lbrakk>valuation K v; t \<in> carrier K; 
       v t = 1; x \<in> carrier K; x \<noteq> \<zero>\<rbrakk>  \<Longrightarrow> lim\<^bsub>K v \<^esub>(partial_sum K x v t) x" 
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
apply (simp add:limit_def)
 apply (rule allI)
 apply (subgoal_tac "\<forall>n. (N + na (Abs (v x))) < n \<longrightarrow>
                     psum\<^bsub>K x v t\<^esub> n \<plusminus> -\<^sub>a x \<in> vp K v\<^bsup>(Vr K v) (an N)\<^esup>")
 apply blast
apply (rule allI, rule impI)
apply (frule_tac n = n in psum_diff_mem_Kxa[of "v" "t" "x"],
          assumption+, erule conjE) 
apply (frule_tac j = "tna (v x) + (1 + int n)" in  Kxa_val_ge[of "v" "t"], 
       assumption+)
 apply simp
 apply (thin_tac "Kxa K v (t\<^bsub>K\<^esub>\<^bsup>(tna (v x) + (1 + int n))\<^esup>) =
           {xa \<in> carrier K. ant (tna (v x) + (1 + int n)) \<le> v xa}")
 apply (erule conjE)
 apply (simp add:a_zpz[THEN sym])

apply (subgoal_tac "(an N) \<le> v (psum\<^bsub> K x v t\<^esub> n \<plusminus> -\<^sub>a x)")
 
 apply (frule value_in_aug_inf[of v x], assumption+,
       simp add:aug_inf_def)
      apply (frule val_nonzero_noninf[of v x], assumption+)
  apply (simp add:ant_tna)
 apply (frule val_surj_n_val[of v], blast)
apply (rule_tac x = "psum\<^bsub>K x v t\<^esub> n \<plusminus> -\<^sub>a x" and n = "an N" in 
                     n_value_x_2[of  "v"], assumption+) 
apply (subst val_pos_mem_Vr[THEN sym, of v], assumption+)
apply (rule aGroup.ag_pOp_closed[of "K"], assumption+)
apply (simp add:aGroup.ag_mOp_closed)

apply (cut_tac n = N in an_nat_pos)
apply (rule_tac i = 0 and j = "an N" and k = "v (psum\<^bsub> K x v t\<^esub> n \<plusminus> -\<^sub>a x)" in 
       ale_trans, assumption+)
apply simp
apply simp

apply (frule_tac x1 = "x \<plusminus> (-\<^sub>a psum\<^bsub>K x v t\<^esub> n)" in val_minus_eq[THEN sym,
      of v], assumption+, simp,
      thin_tac "v ( x \<plusminus> -\<^sub>a psum\<^bsub> K x v t\<^esub> n) = v (-\<^sub>a ( x \<plusminus> -\<^sub>a psum\<^bsub> K x v t\<^esub> n))")
 apply (frule_tac x = "psum\<^bsub> K x v t\<^esub> n" in aGroup.ag_mOp_closed[of "K"],
        assumption+, simp add:aGroup.ag_p_inv, simp add:aGroup.ag_inv_inv)
 apply (frule aGroup.ag_mOp_closed[of "K" "x"], assumption+)
 apply (simp add:aGroup.ag_pOp_commute[of "K" "-\<^sub>a x"])

apply (cut_tac Abs_pos[of "v x"])
apply (frule val_nonzero_z[of v x], assumption+, erule exE, simp) 
apply (simp add:na_def) 
apply (cut_tac aneg_less[THEN sym, of "0" "Abs (v x)"], simp)
apply (frule val_nonzero_noninf[of v x], assumption+)
apply (simp add:tna_ant)
apply (simp only:ant_1[THEN sym], simp del:ant_1 add:a_zpz)
apply (simp add:add.assoc[THEN sym])
apply (cut_tac m1 = "N + nat \<bar>z\<bar>" and n1 = n in of_nat_less_iff [where ?'a = int, THEN sym], simp)
apply (frule_tac a = "int N + abs z" and b = "int n" and c = "z + 1" in 
       add_strict_right_mono, simp only:add.commute)
apply (simp only:add.assoc[of _ "1"])
apply (simp only:add.assoc[THEN sym, of "1"])
apply (simp only:add.commute[of "1"])
apply (simp only:add.assoc[of _ "1"])
apply (cut_tac ?a1 = z and ?b1 = "abs z" and ?c1 = "1 + int N" in 
       add.assoc[THEN sym])
apply (thin_tac "\<bar>z\<bar> + int N < int n")
apply (frule_tac a = "z + (\<bar>z\<bar> + (1 + int N))" and b = "z + \<bar>z\<bar> + (1 + int N)" and c = "int n + (z + 1)" in ineq_conv1, assumption+)
apply (thin_tac "z + (\<bar>z\<bar> + (1 + int N)) < int n + (z + 1)",
       thin_tac "z + (\<bar>z\<bar> + (1 + int N)) = z + \<bar>z\<bar> + (1 + int N)",
       thin_tac "N + nat \<bar>z\<bar> < n")
apply (cut_tac z = z in abs_p_self_pos)
apply (frule_tac i = 0 and j = "z + abs z" and k = "1 + int N" in 
        zadd_right_mono) 
apply (simp only:add_0)
apply (frule_tac i = "1 + int N" and j = "z + \<bar>z\<bar> + (1 + int N)" and 
       k = "int n + (z + 1)" in zle_zless_trans, assumption+) 
apply (thin_tac "z + \<bar>z\<bar> + (1 + int N) < int n + (z + 1)",
       thin_tac "0 \<le> z + \<bar>z\<bar>",
       thin_tac "1 + int N \<le> z + \<bar>z\<bar> + (1 + int N)")
apply (cut_tac m1 = "1 + int N" and n1 = "int n + (z + 1)" in 
       aless_zless[THEN sym], simp)

apply (frule_tac x = "ant (1 + int N)" and y = "ant (int n + (z + 1))"
       and z = "v ( psum\<^bsub> K x v t\<^esub> n \<plusminus> -\<^sub>a x)" in aless_le_trans, assumption+)
apply (thin_tac "ant (1 + int N) < ant (int n + (z + 1))")

apply (simp add:a_zpz[THEN sym])
apply (frule_tac x = "1 + ant (int N)" and y = "v ( psum\<^bsub> K x v t\<^esub> n \<plusminus> -\<^sub>a x)" in 
       aless_imp_le, thin_tac "1 + ant (int N) < v ( psum\<^bsub> K x v t\<^esub> n \<plusminus> -\<^sub>a x)")
apply (cut_tac a0_less_1, frule aless_imp_le[of "0" "1"])
apply (frule_tac b = "ant (int N)" in aadd_pos_le[of "1"])
apply (subst an_def)
apply (rule_tac i = "ant (int N)" and j = "1 + ant (int N)" and 
       k = "v ( psum\<^bsub> K x v t\<^esub> n \<plusminus> -\<^sub>a x)" in ale_trans, assumption+)
done

subsection "Hensel's theorem"

definition
(*** Cauchy sequence of polynomials in (Vr K v)[X] ***)
  pol_Cauchy_seq :: "[('b, 'm) Ring_scheme, 'b, _, 'b \<Rightarrow> ant, 
         nat \<Rightarrow> 'b] \<Rightarrow> bool" ("(5PCauchy\<^bsub> _ _ _ _ \<^esub>_)" [90,90,90,90,91]90) where
  "PCauchy\<^bsub>R X K v\<^esub> F \<longleftrightarrow> (\<forall>n. (F n) \<in> carrier R) \<and> 
    (\<exists>d. (\<forall>n. deg R (Vr K v) X (F n) \<le> (an d))) \<and>
    (\<forall>N. \<exists>M. (\<forall>n m. M < n \<and> M < m \<longrightarrow>  
        P_mod R (Vr K v) X ((vp K v)\<^bsup>(Vr K v) (an N)\<^esup>) (F n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (F m))))"

definition
  pol_limit :: "[('b, 'm) Ring_scheme, 'b, _, 'b \<Rightarrow> ant, 
             nat \<Rightarrow> 'b, 'b] \<Rightarrow> bool" 
             ("(6Plimit\<^bsub> _ _ _ _ \<^esub>_ _)" [90,90,90,90,90,91]90) where
  "Plimit\<^bsub>R X K v\<^esub> F p \<longleftrightarrow> (\<forall>n. (F n) \<in> carrier R) \<and> 
    (\<forall>N. \<exists>M. (\<forall>m. M < m \<longrightarrow>  
        P_mod R (Vr K v) X ((vp K v)\<^bsup>(Vr K v) (an N)\<^esup>) ((F m) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p)))"

definition
  Pseql :: "[('b, 'm) Ring_scheme, 'b, _, 'b \<Rightarrow> ant, nat, 
             nat \<Rightarrow> 'b] \<Rightarrow> nat \<Rightarrow> 'b" 
            ("(6Pseql\<^bsub>_  _ _ _ _ \<^esub>_)" [90,90,90,90,90,91]90) where
  "Pseql\<^bsub>R X K v d\<^esub> F = (\<lambda>n. (ldeg_p R (Vr K v) X d (F n)))"

   (** deg R (Vr K v) X (F n) \<le> an (Suc d) **)

definition
  Pseqh :: "[('b, 'm) Ring_scheme, 'b, _, 'b \<Rightarrow> ant, nat, nat \<Rightarrow> 'b] \<Rightarrow>  
        nat \<Rightarrow> 'b" 
           ("(6Pseqh\<^bsub> _ _ _ _ _ \<^esub>_)" [90,90,90,90,90,91]90) where
  "Pseqh\<^bsub>R X K v d\<^esub> F = (\<lambda>n. (hdeg_p R (Vr K v) X (Suc d) (F n)))"

    (** deg R (Vr K v) X (F n) \<le> an (Suc d) **)

lemma an_neq_minf[simp]:"\<forall>n. -\<infinity> \<noteq> an n"
apply (rule allI)
apply (simp add:an_def) apply (rule not_sym) apply simp
done

lemma an_neq_minf1[simp]:"\<forall>n. an n \<noteq> -\<infinity>" 
apply (rule allI) apply (simp add:an_def)
done

lemma (in Corps) Pseql_mem:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X;
      F n \<in> carrier R; \<forall>n. deg R (Vr K v) X (F n) \<le> an (Suc d)\<rbrakk> \<Longrightarrow>
                     (Pseql\<^bsub>R X K v d\<^esub> F) n \<in> carrier R"
apply (frule PolynRg.is_Ring)
apply (simp add:Pseql_def)
apply (frule Vr_ring[of "v"], 
       rule PolynRg.ldeg_p_mem, assumption+, simp)
done

lemma (in Corps) Pseqh_mem:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X;
      F n \<in> carrier R; \<forall>n. deg R (Vr K v) X (F n) \<le> an (Suc d)\<rbrakk> \<Longrightarrow>
                     (Pseqh\<^bsub>R X K v d\<^esub> F) n \<in> carrier R"
apply (frule PolynRg.is_Ring)
apply (frule Vr_ring[of "v"]) 
apply (frule PolynRg.subring[of "R" "Vr K v" "X"])
apply (frule PolynRg.X_mem_R[of "R" "Vr K v" "X"])
apply (simp del:npow_suc add:Pseqh_def)
apply (rule PolynRg.hdeg_p_mem, assumption+, simp)
done

lemma (in Corps) PCauchy_lTr:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X;
    p \<in> carrier R; deg R (Vr K v) X p \<le> an (Suc d); 
    P_mod R (Vr K v) X (vp K v\<^bsup>(Vr K v) (an N)\<^esup>) p\<rbrakk> \<Longrightarrow>
    P_mod R (Vr K v) X (vp K v\<^bsup>(Vr K v) (an N)\<^esup>) (ldeg_p R (Vr K v) X d p)"
apply (frule PolynRg.is_Ring)
apply (simp add:ldeg_p_def)
apply (frule Vr_ring[of v])
apply (frule PolynRg.scf_d_pol[of "R" "Vr K v" "X" "p" "Suc d"], assumption+,
       (erule conjE)+)
apply (frule_tac n = "an N" in vp_apow_ideal[of v], simp)
apply (frule PolynRg.P_mod_mod[THEN sym, of R "Vr K v" X "vp K v\<^bsup> (Vr K v) (an N)\<^esup>"
       p "scf_d R (Vr K v) X p (Suc d)"], assumption+, simp)
apply (subst PolynRg.polyn_expr_short[of R "Vr K v" X 
             "scf_d R (Vr K v) X p (Suc d)" d], assumption+, simp)
apply (subst PolynRg.P_mod_mod[THEN sym, of R "Vr K v" X "vp K v\<^bsup> (Vr K v) (an N)\<^esup>"
       "polyn_expr R X d (d, snd (scf_d R (Vr K v) X p (Suc d)))" 
       "(d, snd (scf_d R (Vr K v) X p (Suc d)))"], assumption+)
apply (subst PolynRg.polyn_expr_short[THEN sym], simp+,
       simp add:PolynRg.polyn_mem)
apply (subst pol_coeff_def, rule allI, rule impI, 
       simp add:PolynRg.pol_coeff_mem)
apply simp+
done

lemma (in Corps) PCauchy_hTr:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X;
      p \<in> carrier R; deg R (Vr K v) X p \<le> an (Suc d); 
      P_mod R (Vr K v) X (vp K v\<^bsup>(Vr K v) (an N)\<^esup>) p\<rbrakk>
  \<Longrightarrow> P_mod R (Vr K v) X (vp K v\<^bsup>(Vr K v) (an N)\<^esup>) (hdeg_p R (Vr K v) X (Suc d) p)"
apply (frule PolynRg.is_Ring)
apply (cut_tac Vr_ring[of v])
apply (frule PolynRg.scf_d_pol[of R "Vr K v" X p "Suc d"], assumption+)
apply (frule_tac n = "an N" in vp_apow_ideal[of v], simp)
apply (frule PolynRg.P_mod_mod[THEN sym, of "R" "Vr K v" "X" 
       "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" p "scf_d R (Vr K v) X p (Suc d)"], assumption+,
       simp+)
apply (subst hdeg_p_def) 
apply (subst PolynRg.monomial_P_mod_mod[THEN sym, of "R" "Vr K v" "X" 
       "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" "snd (scf_d R (Vr K v) X p (Suc d)) (Suc d)" 
       "(snd (scf_d R (Vr K v) X p (Suc d)) (Suc d)) \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R (Suc d)\<^esup>)" 
       "Suc d"], 
       assumption+)
apply (rule PolynRg.pol_coeff_mem[of R "Vr K v" X 
       "scf_d R (Vr K v) X p (Suc d)" "Suc d"], assumption+, simp+)
done
 
lemma (in Corps) v_ldeg_p_pOp:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X; 
      p \<in> carrier R; q \<in> carrier R; deg R (Vr K v) X p \<le> an (Suc d); 
      deg R (Vr K v) X q \<le> an (Suc d)\<rbrakk> \<Longrightarrow>
      (ldeg_p R (Vr K v) X d p) \<plusminus>\<^bsub>R\<^esub> (ldeg_p R (Vr K v) X d q) =
                              ldeg_p R (Vr K v) X d (p \<plusminus>\<^bsub>R\<^esub> q)"
by (simp add:PolynRg.ldeg_p_pOp[of R "Vr K v" X p q d]) 

lemma (in Corps) v_hdeg_p_pOp:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X; 
      p \<in> carrier R; q \<in> carrier R; deg R (Vr K v) X p \<le> an (Suc d); 
      deg R (Vr K v) X q \<le> an (Suc d)\<rbrakk> \<Longrightarrow> (hdeg_p R (Vr K v) X (Suc d) p) \<plusminus>\<^bsub>R\<^esub> 
      (hdeg_p R (Vr K v) X (Suc d) q) = hdeg_p R (Vr K v) X (Suc d) (p \<plusminus>\<^bsub>R\<^esub> q)"
by (simp add:PolynRg.hdeg_p_pOp[of R "Vr K v" X p q d])

lemma (in Corps) v_ldeg_p_mOp:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X; 
       p \<in> carrier R;deg R (Vr K v) X p \<le> an (Suc d)\<rbrakk> \<Longrightarrow> 
       -\<^sub>a\<^bsub>R\<^esub> (ldeg_p R (Vr K v) X d p) = ldeg_p R (Vr K v) X d (-\<^sub>a\<^bsub>R\<^esub> p)"
by (simp add:PolynRg.ldeg_p_mOp)


lemma (in Corps) v_hdeg_p_mOp:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X; 
    p \<in> carrier R;deg R (Vr K v) X p \<le> an (Suc d)\<rbrakk> \<Longrightarrow>
   -\<^sub>a\<^bsub>R\<^esub> (hdeg_p R (Vr K v) X (Suc d) p) = hdeg_p R (Vr K v) X (Suc d) (-\<^sub>a\<^bsub>R\<^esub> p)"
by (simp add:PolynRg.hdeg_p_mOp)

lemma (in Corps) PCauchy_lPCauchy:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X; 
      \<forall>n. F n \<in> carrier R;  \<forall>n. deg R (Vr K v) X (F n) \<le> an (Suc d); 
      P_mod R (Vr K v) X (vp K v\<^bsup>(Vr K v) (an N)\<^esup>) (F n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (F m))\<rbrakk>
      \<Longrightarrow> P_mod R (Vr K v) X (vp K v\<^bsup>(Vr K v) (an N)\<^esup>)
                     (((Pseql\<^bsub>R X K v d\<^esub> F) n) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> ((Pseql\<^bsub>R X K v d\<^esub> F) m))"
apply (frule PolynRg.is_Ring)
apply (cut_tac Vr_ring[of v],
       frule Ring.ring_is_ag[of "R"],
       frule PolynRg.subring[of "R" "Vr K v" "X"])
apply (simp add:Pseql_def)
apply (subst v_ldeg_p_mOp[of "v" "R" "X" _ "d"], assumption+,
       simp, simp)
apply (subst v_ldeg_p_pOp[of v R X "F n" "-\<^sub>a\<^bsub>R\<^esub> (F m)"], assumption+,
       simp, rule aGroup.ag_mOp_closed, assumption, simp, simp,
       simp add:PolynRg.deg_minus_eq1)
apply (rule PCauchy_lTr[of v R X "F n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (F m)" "d" "N"],
       assumption+,
       rule aGroup.ag_pOp_closed[of "R" "F n" "-\<^sub>a\<^bsub>R\<^esub> (F m)"], assumption+,
       simp, rule aGroup.ag_mOp_closed, assumption+, simp)
apply (frule PolynRg.deg_minus_eq1 [of "R" "Vr K v" "X" "F m"], simp)
apply (rule PolynRg.polyn_deg_add4[of "R" "Vr K v" "X" "F n" 
       "-\<^sub>a\<^bsub>R\<^esub> (F m)" "Suc d"], assumption+, simp,
       rule aGroup.ag_mOp_closed, assumption, simp+)
done

lemma (in Corps) PCauchy_hPCauchy:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X;
      \<forall>n. F n \<in> carrier R; \<forall>n. deg R (Vr K v) X (F n) \<le> an (Suc d); 
      P_mod R (Vr K v) X (vp K v\<^bsup>(Vr K v) (an N)\<^esup>) (F n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (F m))\<rbrakk>
      \<Longrightarrow> P_mod R (Vr K v) X (vp K v\<^bsup>(Vr K v) (an N)\<^esup>)
                     (((Pseqh\<^bsub>R X K v d\<^esub> F) n) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> ((Pseqh\<^bsub>R X K v d\<^esub> F) m))"
apply (frule PolynRg.is_Ring)
apply (frule Vr_ring[of v], frule Ring.ring_is_ag[of "R"],
       frule PolynRg.subring[of "R" "Vr K v" "X"], 
       frule vp_apow_ideal[of v "an N"], simp) 

apply (simp add:Pseqh_def,
       subst v_hdeg_p_mOp[of v R X "F m" "d"], assumption+,
       simp+)

apply (subst v_hdeg_p_pOp[of v R X "F n" "-\<^sub>a\<^bsub>R\<^esub> (F m)"], assumption+,
       simp, rule aGroup.ag_mOp_closed, assumption, simp, simp,
       frule PolynRg.deg_minus_eq1 [of "R" "Vr K v" "X" "F m"],
       simp+ )
apply (frule PCauchy_hTr[of "v" "R" "X" "F n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (F m)" "d" "N"],
    assumption+,
    rule aGroup.ag_pOp_closed[of "R" "F n" "-\<^sub>a\<^bsub>R\<^esub> (F m)"], assumption+,
    simp, rule aGroup.ag_mOp_closed, assumption+, simp)
apply (frule PolynRg.deg_minus_eq1 [of "R" "Vr K v" "X" "F m"], simp+)
apply (rule PolynRg.polyn_deg_add4[of "R" "Vr K v" "X" "F n" "-\<^sub>a\<^bsub>R\<^esub> (F m)" 
       "Suc d"], assumption+,
       simp, rule aGroup.ag_mOp_closed, assumption, simp+)
done

(** Don't forget  t_vp_apow  ***)
 
lemma (in Corps) Pseq_decompos:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X;
      F n \<in> carrier R; deg R (Vr K v) X (F n) \<le> an (Suc d)\<rbrakk>
      \<Longrightarrow> F n = ((Pseql\<^bsub>R X K v d\<^esub> F) n) \<plusminus>\<^bsub>R\<^esub> ((Pseqh\<^bsub>R X K v d\<^esub> F) n)"
apply (frule PolynRg.is_Ring)
apply (simp del:npow_suc add:Pseql_def Pseqh_def)
apply (frule Vr_ring[of v])
apply (frule PolynRg.subring[of "R" "Vr K v" "X"])
apply (rule PolynRg.decompos_p[of "R" "Vr K v" "X" "F n" "d"], assumption+)
done

lemma (in Corps) deg_0_const:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X;
      p \<in> carrier R; deg R (Vr K v) X p \<le> 0\<rbrakk> \<Longrightarrow> p \<in> carrier (Vr K v)"
apply (frule Vr_ring[of v])
apply (frule PolynRg.subring)
apply (frule PolynRg.is_Ring)
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp,
       simp add:Ring.Subring_zero_ring_zero[THEN sym],
       simp add:Ring.ring_zero)
apply (subst PolynRg.pol_of_deg0[THEN sym, of "R" "Vr K v" "X" "p"], 
        assumption+)
apply (simp add:PolynRg.deg_an, simp only:an_0[THEN sym])
apply (simp only:ale_nat_le[of "deg_n R (Vr K v) X p" "0"])
done

lemma (in Corps) monomial_P_limt:"\<lbrakk>valuation K v; Complete\<^bsub>v\<^esub> K; 
     PolynRg R (Vr K v) X; \<forall>n. f n \<in> carrier (Vr K v);
     \<forall>n. F n = (f n) \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>);  \<forall>N. \<exists>M. \<forall>n m. M < n \<and> M < m \<longrightarrow>
     P_mod R (Vr K v) X (vp K v\<^bsup>(Vr K v) (an N)\<^esup>) (F n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (F m))\<rbrakk> \<Longrightarrow> 
        \<exists>b\<in>carrier (Vr K v). Plimit\<^bsub> R X K v \<^esub>F (b \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>))"
apply (frule PolynRg.is_Ring)
apply (frule Vr_ring[of v])
apply (frule PolynRg.subring[of "R" "Vr K v" "X"])
apply simp

apply (subgoal_tac "Cauchy\<^bsub> K v \<^esub>f")
 apply (simp add:v_complete_def)
 apply (drule_tac a = f in forall_spec)
 apply (thin_tac "\<forall>N. \<exists>M. \<forall>n m. M < n \<and> M < m \<longrightarrow>
        P_mod R (Vr K v) X (vp K v\<^bsup>(Vr K v) (an N)\<^esup>)
        ((f n) \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (f m) \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>))", assumption)
 apply (erule exE, erule conjE)
 apply (subgoal_tac "b \<in> carrier (Vr K v)")
 apply (subgoal_tac "Plimit\<^bsub> R X K v \<^esub>F (b \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>))", blast)
 
(******* b \<in> carrier (Vr K v) ***********)
apply (simp add:pol_limit_def)
apply (rule conjI)
 apply (rule allI)
 apply (rule Ring.ring_tOp_closed[of "R"], assumption)
 apply (frule PolynRg.subring[of "R" "Vr K v" "X"])
 apply (rule Ring.mem_subring_mem_ring[of "R" "Vr K v"], assumption+) 
 apply simp
 
 apply (frule PolynRg.X_mem_R[of "R" "Vr K v" "X"])
 apply (simp add:Ring.npClose)
apply (thin_tac "\<forall>n. F n = f n \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R d\<^esup>") 
apply (simp add:limit_def)
 apply (rule allI)
(* apply (simp add:t_vp_apow[of "K" "v" "t"]) *) 
 apply (rotate_tac -2, drule_tac x = N in spec) 
 apply (erule exE)
 apply (subgoal_tac "\<forall>n> M. P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
                   ((f n)\<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (b \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>)))", blast) 
 apply (rule allI, rule impI)
 apply (rotate_tac -2, drule_tac x = n in spec, simp)
 apply (drule_tac x = n in spec)

apply (frule_tac x = "f n" in Ring.mem_subring_mem_ring[of "R" "Vr K v"], 
       assumption+,
       frule_tac x = b in Ring.mem_subring_mem_ring[of "R" "Vr K v"], 
       assumption+)
apply (frule PolynRg.X_mem_R[of "R" "Vr K v" "X"])
 apply (frule Ring.npClose[of "R" "X" "d"], assumption+)
 apply (simp add:Ring.ring_inv1_1)
 apply (frule Ring.ring_is_ag[of "R"],
        frule_tac x = b in aGroup.ag_mOp_closed[of "R"], assumption+)
 apply (subst Ring.ring_distrib2[THEN sym, of "R" "X^\<^bsup>R d\<^esup>"], assumption+)

 apply (frule_tac n = "an N" in vp_apow_ideal[of v], simp) 
 apply (frule_tac I = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and c = "f n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> b" and 
        p = "(f n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> b) \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>)" in  
        PolynRg.monomial_P_mod_mod[of "R" "Vr K v" "X" _ _ _ "d"], assumption+)
 apply (simp add:Ring.Subring_minus_ring_minus[THEN sym])
 apply (frule Ring.ring_is_ag[of "Vr K v"])
 apply (frule_tac x = b in aGroup.ag_mOp_closed[of "Vr K v"], assumption+)
 apply (simp only:Ring.Subring_pOp_ring_pOp[THEN sym])
 apply (rule aGroup.ag_pOp_closed, assumption+) apply simp
 apply (frule_tac I1 = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and c1 = "f n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> b" and 
     p1 = "(f n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> b) \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>)" in PolynRg.monomial_P_mod_mod[THEN sym, 
     of "R" "Vr K v" "X" _ _ _ "d"], assumption+)
 apply (frule Ring.ring_is_ag[of "Vr K v"])
 apply (frule_tac x = b in aGroup.ag_mOp_closed[of "Vr K v"], assumption+)
 apply (simp only:Ring.Subring_minus_ring_minus[THEN sym])
 apply (simp only:Ring.Subring_pOp_ring_pOp[THEN sym])
 apply (rule aGroup.ag_pOp_closed, assumption+) apply simp apply simp
 apply (simp only:Vr_mOp_f_mOp[THEN sym])
 apply (frule Ring.ring_is_ag[of "Vr K v"])
 apply (frule_tac x = b in aGroup.ag_mOp_closed[of "Vr K v"], assumption+)
 apply (simp add:Vr_pOp_f_pOp[THEN sym])
 apply (simp add:Ring.Subring_pOp_ring_pOp)
 apply (simp add:Ring.Subring_minus_ring_minus)

 apply (case_tac "b = \<zero>\<^bsub>K\<^esub>", simp add:Vr_0_f_0[THEN sym], 
        simp add:Ring.ring_zero)
 apply (frule_tac b = b in limit_val[of  _ "f" "v"], assumption+,
        rule allI,
        frule_tac x = j in spec, simp add:Vr_mem_f_mem,
        assumption+, erule exE)
 apply (thin_tac "\<forall>n. F n = f n \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R d\<^esup>",
        thin_tac "\<forall>N. \<exists>M. \<forall>n m. M < n \<and> M < m \<longrightarrow>
                         P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
                          (f n \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R d\<^esup> \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> f m \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R d\<^esup>)")  
 apply (rotate_tac -1, drule_tac x = "Suc N" in spec, simp)
 apply (drule_tac x = "Suc N" in spec)
 apply (frule_tac x1 = "f (Suc N)" in val_pos_mem_Vr[THEN sym, of v],
        simp add:Vr_mem_f_mem, simp, simp add:val_pos_mem_Vr[of v]) 

apply (simp add:Cauchy_seq_def)
 apply (simp add:Vr_mem_f_mem)
 apply (rule allI)
 apply (rotate_tac -3, frule_tac x = N in spec)

 apply (thin_tac "\<forall>n. F n = f n \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R d\<^esup>")
 (*apply (simp add:t_vp_apow[of "K" "v" "t"]) *) 
 apply (frule_tac n = "an N" in vp_apow_ideal[of "v"], simp)
 apply (drule_tac x = N in spec, erule exE) 
 apply (subgoal_tac "\<forall>n m. M < n \<and> M < m \<longrightarrow>
                      f n \<plusminus> -\<^sub>a (f m) \<in> vp K v\<^bsup> (Vr K v) (an N)\<^esup>", blast)
 apply (rule allI)+
 apply (rule impI, erule conjE)
 apply (frule_tac I = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and c = "f n \<plusminus> -\<^sub>a (f m)" and 
   p = "(f n \<plusminus> -\<^sub>a (f m)) \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>)" in
   PolynRg.monomial_P_mod_mod[of "R" "Vr K v" "X" _ _ _ "d"], assumption+)
 
 apply (frule_tac x = n in spec,
        drule_tac x = m in spec)
 apply (frule Ring.ring_is_ag[of "Vr K v"],
        simp add:Vr_mOp_f_mOp[THEN sym],
        frule_tac x = "f m" in aGroup.ag_mOp_closed[of "Vr K v"], assumption+,
        simp add:Vr_pOp_f_pOp[THEN sym])
 apply (rule aGroup.ag_pOp_closed, assumption+, simp)
 apply simp 
 apply (thin_tac "(f n \<plusminus> -\<^sub>a f m \<in> vp K v\<^bsup> (Vr K v) (an N)\<^esup>) =
        P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>) ((f n \<plusminus> -\<^sub>a f m) \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R d\<^esup>)")
 apply (rotate_tac -3, drule_tac x = n in spec,
        rotate_tac -1, drule_tac x = m in spec, simp)
 apply (frule_tac x = n in spec,
        drule_tac x = m in spec)
 apply (frule_tac x = "f n" in Ring.mem_subring_mem_ring[of R "Vr K v"],
         assumption+,
        frule_tac x = "f m" in Ring.mem_subring_mem_ring[of R "Vr K v"],
         assumption+,
        frule Ring.ring_is_ag[of R],
        frule_tac x = "f m" in aGroup.ag_mOp_closed[of R], assumption+,
        frule PolynRg.X_mem_R[of R "Vr K v" X],
        frule Ring.npClose[of R X d], assumption)
 apply (simp add:Ring.ring_inv1_1[of R],
        frule_tac y1 = "f n" and z1 = "-\<^sub>a\<^bsub>R\<^esub> f m" in Ring.ring_distrib2[
        THEN sym, of R "X^\<^bsup>R d\<^esup>"], assumption+, simp,
        thin_tac "f n \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R d\<^esup> \<plusminus>\<^bsub>R\<^esub> (-\<^sub>a\<^bsub>R\<^esub> f m) \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R d\<^esup> =
                                           (f n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> f m) \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R d\<^esup>")
 apply (simp only:Ring.Subring_minus_ring_minus[THEN sym,of R "Vr K v"])
 apply (frule Ring.subring_Ring[of R "Vr K v"], assumption,
        frule Ring.ring_is_ag[of "Vr K v"],
        frule_tac x = "f m" in aGroup.ag_mOp_closed[of "Vr K v"], assumption+)
 apply (simp add:Ring.Subring_pOp_ring_pOp[THEN sym, of R "Vr K v"],
        simp add:Vr_pOp_f_pOp, simp add:Vr_mOp_f_mOp)
done

lemma (in Corps) mPlimit_uniqueTr:"\<lbrakk>valuation K v; 
     PolynRg R (Vr K v) X; \<forall>n. f n \<in> carrier (Vr K v);
     \<forall>n. F n = (f n) \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>); c \<in> carrier (Vr K v);
     Plimit\<^bsub> R X K v \<^esub>F (c \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>))\<rbrakk>  \<Longrightarrow> lim\<^bsub> K v \<^esub>f c" 
apply (frule PolynRg.is_Ring,
       simp add:pol_limit_def limit_def,
       rule allI,
       erule conjE,
       rotate_tac -1, drule_tac x = N in spec,
       erule exE)
apply (subgoal_tac "\<forall>n. M < n \<longrightarrow> f n \<plusminus> -\<^sub>a c \<in> vp K v\<^bsup> (Vr K v) (an N)\<^esup>", blast)
apply (rule allI, rule impI,
       rotate_tac -2, drule_tac x = n in spec, simp,
       drule_tac x = n in spec,
       drule_tac x = n in spec,
       thin_tac "\<forall>n. f n \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R d\<^esup> \<in> carrier R")
apply (frule Vr_ring[of v],
       frule PolynRg.X_mem_R[of "R" "Vr K v" "X"],
       frule Ring.npClose[of "R" "X" "d"], assumption+,
       frule PolynRg.subring[of "R" "Vr K v" "X"])
apply (frule_tac x = c in Ring.mem_subring_mem_ring[of "R" "Vr K v"], 
       assumption+,
      frule_tac x = "f n" in Ring.mem_subring_mem_ring[of "R" "Vr K v"], 
       assumption+)
apply (simp add:Ring.ring_inv1_1,
       frule Ring.ring_is_ag[of "R"], 
       frule aGroup.ag_mOp_closed[of "R" "c"], assumption+)
apply (simp add:Ring.ring_distrib2[THEN sym, of "R" "X^\<^bsup>R d\<^esup>" _ "-\<^sub>a\<^bsub>R\<^esub> c"],
       simp add:Ring.Subring_minus_ring_minus[THEN sym],
       frule Ring.ring_is_ag[of "Vr K v"],
       frule aGroup.ag_mOp_closed[of "Vr K v" "c"], assumption+)
apply (simp add:Ring.Subring_pOp_ring_pOp[THEN sym],
       frule_tac x = "f n" in aGroup.ag_pOp_closed[of "Vr K v" _ 
        "-\<^sub>a\<^bsub>(Vr K v)\<^esub> c"], assumption+,
       frule_tac n = "an N" in vp_apow_ideal[of "v"], simp,
       frule_tac I1 = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and 
        c1 = "f n \<plusminus>\<^bsub>(Vr K v)\<^esub> -\<^sub>a\<^bsub>(Vr K v)\<^esub> c" and p1 = "(f n \<plusminus>\<^bsub>(Vr K v)\<^esub> -\<^sub>a\<^bsub>(Vr K v)\<^esub> c)
       \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>)" in PolynRg.monomial_P_mod_mod[THEN sym, of R "Vr K v" 
        X _ _ _ d], assumption+, simp, simp)
 apply (simp add:Vr_pOp_f_pOp, simp add:Vr_mOp_f_mOp)
done

lemma (in Corps) mono_P_limt_unique:"\<lbrakk>valuation K v; 
  PolynRg R (Vr K v) X; \<forall>n. f n \<in> carrier (Vr K v); 
  \<forall>n. F n = (f n) \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>); b \<in> carrier (Vr K v); c \<in> carrier (Vr K v);
  Plimit\<^bsub> R X K v \<^esub>F (b \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>)); Plimit\<^bsub> R X K v \<^esub>F (c \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>))\<rbrakk> \<Longrightarrow> 
        b  \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>) = c \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R d\<^esup>)" 
apply (frule PolynRg.is_Ring)
apply (frule_tac mPlimit_uniqueTr[of v R X f F d b], assumption+,
       frule_tac mPlimit_uniqueTr[of v R X f F d c], assumption+)
apply (frule Vr_ring[of v],
       frule PolynRg.subring[of "R" "Vr K v" "X"],
       frule Vr_mem_f_mem[of v b], assumption+,
       frule Vr_mem_f_mem[of v c], assumption+,
       frule limit_unique[of b f v c])
apply (rule allI, simp add:Vr_mem_f_mem, assumption+, simp)
done 

lemma (in Corps) Plimit_deg:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X; 
  \<forall>n. F n \<in> carrier R; \<forall>n. deg R (Vr K v) X (F n) \<le> (an d); 
  p \<in> carrier R; Plimit\<^bsub> R X K v \<^esub>F p\<rbrakk> \<Longrightarrow>  deg R (Vr K v) X p \<le> (an d)"
apply (frule PolynRg.is_Ring, frule Vr_ring[of v])
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp add:deg_def)
apply (rule contrapos_pp, simp+,
       simp add:aneg_le,
       frule PolynRg.s_cf_expr[of R "Vr K v" X p], assumption+, (erule conjE)+,
       frule PolynRg.s_cf_deg[of R "Vr K v" X p], assumption+,
       frule PolynRg.pol_coeff_mem[of R "Vr K v" X "s_cf R (Vr K v) X p" 
        "fst (s_cf R (Vr K v) X p)"], assumption+, simp,
       frule Vr_mem_f_mem[of v "snd (s_cf R (Vr K v) X p) 
            (fst (s_cf R (Vr K v) X p))"], assumption+)
(* show the value of the leading coefficient is noninf *)
apply (frule val_nonzero_noninf[of "v" 
       "snd (s_cf R (Vr K v) X p) (fst (s_cf R (Vr K v) X p))"], assumption,
       simp add:Vr_0_f_0,
       frule val_pos_mem_Vr[THEN sym, of v "snd (s_cf R (Vr K v) X p) 
         (fst (s_cf R (Vr K v) X p))"], assumption+, simp,
       frule value_in_aug_inf[of "v" "snd (s_cf R (Vr K v) X p) 
          (fst (s_cf R (Vr K v) X p))"], assumption+,
       cut_tac mem_ant[of "v (snd (s_cf R (Vr K v) X p) 
       (fst (s_cf R (Vr K v) X p)))"], simp add:aug_inf_def,
       erule exE, simp, simp only:ant_0[THEN sym], simp only:ale_zle,
       frule_tac z = z in zpos_nat, erule exE, simp,
       thin_tac "z = int n")

(* show that the leading coefficient of p shoule be 0. contradiction *)
apply (simp add:pol_limit_def)
apply (rotate_tac 5, drule_tac x = "Suc n" in spec) 
apply (erule exE)
apply (rotate_tac -1, 
       drule_tac x = "Suc M" in spec, simp del:npow_suc,
       drule_tac x = "Suc M" in spec, 
       drule_tac x = "Suc M" in spec)

  (**** Only formula manipulation to obtain
        P_mod R (Vr K v) X (vp K v\<^bsup> Vr K v an (Suc n)\<^esup>)
         (polyn_expr R X (fst (s_cf R (Vr K v) X p))
           (add_cf (Vr K v) f
             (fst (s_cf R (Vr K v) X p),
              \<lambda>j. -\<^sub>a\<^bsub>Vr K v\<^esub> snd (s_cf R (Vr K v) X p) j))) *****)
apply (frule PolynRg.polyn_minus[of R "Vr K v" X "s_cf R (Vr K v) X p" 
       "fst (s_cf R (Vr K v) X p)"], assumption+, simp,
   frule PolynRg.minus_pol_coeff[of R "Vr K v" X "s_cf R (Vr K v) X p"],
        assumption+, drule sym,
   frule_tac x = "deg R (Vr K v) X (F (Suc M))" in ale_less_trans[of _ 
       "an d" "deg R (Vr K v) X p"], assumption+,
   frule_tac p = "F (Suc M)" and d = "deg_n R (Vr K v) X p" in 
            PolynRg.pol_expr_edeg[of "R" "Vr K v" "X"], assumption+,
   frule_tac x = "deg R (Vr K v) X (F (Suc M))" and 
         y = "deg R (Vr K v) X p" in aless_imp_le,
      subst PolynRg.deg_an[THEN sym, of "R" "Vr K v" "X" "p"], assumption+,
      erule exE, (erule conjE)+,
   frule_tac c = f in PolynRg.polyn_add1[of "R" "Vr K v" "X" _ 
    "(fst (s_cf R (Vr K v) X p), \<lambda>j. -\<^sub>a\<^bsub>Vr K v\<^esub> snd (s_cf R (Vr K v) X p) j)"],
    assumption+, simp,
   thin_tac "-\<^sub>a\<^bsub>R\<^esub> p = polyn_expr R X (fst (s_cf R (Vr K v) X p))
    (fst (s_cf R (Vr K v) X p), \<lambda>j. -\<^sub>a\<^bsub>Vr K v\<^esub> snd (s_cf R (Vr K v) X p) j)",
   thin_tac "polyn_expr R X (fst (s_cf R (Vr K v) X p))
             (s_cf R (Vr K v) X p) = p",
   thin_tac "F (Suc M) = polyn_expr R X (fst (s_cf R (Vr K v) X p)) f",
   thin_tac "polyn_expr R X (fst (s_cf R (Vr K v) X p)) f \<plusminus>\<^bsub>R\<^esub>
       polyn_expr R X (fst (s_cf R (Vr K v) X p))
        (fst (s_cf R (Vr K v) X p), \<lambda>j. -\<^sub>a\<^bsub>Vr K v\<^esub> snd (s_cf R (Vr K v) X p) j) =
       polyn_expr R X (fst (s_cf R (Vr K v) X p)) (add_cf (Vr K v) f
       (fst (s_cf R (Vr K v) X p), \<lambda>j. -\<^sub>a\<^bsub>Vr K v\<^esub> snd (s_cf R (Vr K v) X p) j))")

(** apply P_mod_mod to obtain a condition of coefficients **) 
 apply (frule_tac n = "an (Suc n)" in vp_apow_ideal[of "v"], simp,
   frule_tac p1 = "polyn_expr R X (fst (s_cf R (Vr K v) X p))(add_cf (Vr K v) f
   (fst (s_cf R (Vr K v) X p), \<lambda>j. -\<^sub>a\<^bsub>Vr K v\<^esub> snd (s_cf R (Vr K v) X p) j))" and
  I1= "vp K v\<^bsup> (Vr K v) (an (Suc n))\<^esup>" and c1 = "add_cf (Vr K v) f (fst 
   (s_cf R (Vr K v) X p), \<lambda>j. -\<^sub>a\<^bsub>Vr K v\<^esub> snd (s_cf R (Vr K v) X p) j)" in 
  PolynRg.P_mod_mod[THEN sym, of R "Vr K v" X], assumption+,
  rule PolynRg.polyn_mem[of R "Vr K v" X], assumption+,
  rule PolynRg.add_cf_pol_coeff[of R "Vr K v" X], assumption+,
  simp add:PolynRg.add_cf_len,
  rule PolynRg.add_cf_pol_coeff[of R "Vr K v" X], assumption+,
  simp add:PolynRg.add_cf_len,
  simp add:PolynRg.add_cf_len)
 apply (drule_tac x = "fst (s_cf R (Vr K v) X p)" in spec, simp,
        thin_tac "P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an (Suc n))\<^esup>)
         (polyn_expr R X (fst (s_cf R (Vr K v) X p)) (add_cf (Vr K v) f
      (fst (s_cf R (Vr K v) X p), \<lambda>j. -\<^sub>a\<^bsub>Vr K v\<^esub> snd (s_cf R (Vr K v) X p) j)))",
      simp add:add_cf_def)
 (**** we obtained snd (add_cf (Vr K v) f (fst (s_cf R (Vr K v) X p),
     \<lambda>j. -\<^sub>a\<^bsub>Vr K v\<^esub> snd (s_cf R (Vr K v) X p) j)) (fst (s_cf R (Vr K v) X p))
           \<in> vp K v\<^bsup> Vr K v an (Suc n)\<^esup>   ***)
 apply (frule_tac p = "polyn_expr R X (fst (s_cf R (Vr K v) X p)) f" and 
       c = f and j = "fst f" in PolynRg.pol_len_gt_deg[of R "Vr K v" X],
       assumption+, simp, drule sym, simp add:PolynRg.deg_an) apply simp
 apply (rotate_tac -4, drule sym, simp)
 apply (frule Ring.ring_is_ag[of "Vr K v"],
        frule_tac x = "snd (s_cf R (Vr K v) X p) (fst f)" in 
        aGroup.ag_mOp_closed[of "Vr K v"], assumption+,
        simp add:aGroup.ag_l_zero) 
 apply (frule_tac I = "vp K v\<^bsup> (Vr K v) (an (Suc n))\<^esup>" and 
        x = "-\<^sub>a\<^bsub>Vr K v\<^esub> snd (s_cf R (Vr K v) X p) (fst f)" in 
        Ring.ideal_inv1_closed[of "Vr K v"], assumption+)
 apply (simp add:aGroup.ag_inv_inv)
 apply (frule_tac n = "an (Suc n)" and x = "snd (s_cf R (Vr K v) X p) (fst f)"
         in n_value_x_1[of v], simp+)    
 apply (frule_tac x = "snd (s_cf R (Vr K v) X p) (fst f)" in 
         n_val_le_val[of v], assumption+, simp add:ant_int) 
 apply (drule_tac i = "an (Suc n)" and 
        j = "n_val K v (snd (s_cf R (Vr K v) X p) (fst f))" and
        k = "v (snd (s_cf R (Vr K v) X p) (fst f))" in ale_trans,
        assumption+)
 apply (simp add:ant_int ale_natle)
done

lemma (in Corps) Plimit_deg1:"\<lbrakk>valuation K v; Ring R; PolynRg R (Vr K v) X; 
  \<forall>n. F n \<in> carrier R; \<forall>n. deg R (Vr K v) X (F n) \<le> ad; 
  p \<in> carrier R; Plimit\<^bsub> R X K v \<^esub>F p\<rbrakk> \<Longrightarrow>  deg R (Vr K v) X p \<le> ad"
apply (frule Vr_ring[of v])
apply (case_tac "\<forall>n. F n = \<zero>\<^bsub>R\<^esub>")
apply (frule Plimit_deg[of v R X F 0 p], assumption+,
       rule allI, simp add:deg_def, assumption+)
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp add:deg_def,
       frule PolynRg.nonzero_deg_pos[of R "Vr K v" X p], assumption+,
       simp,
       frule PolynRg.pols_const[of "R" "Vr K v" "X" "p"], assumption+,
       simp,
       frule PolynRg.pols_const[of "R" "Vr K v" "X" "p"], assumption+,
       simp add:ale_refl)
 apply (subgoal_tac "p = \<zero>\<^bsub>R\<^esub>", simp)
 apply (thin_tac "p \<noteq> \<zero>\<^bsub>R\<^esub>")
 apply (rule contrapos_pp, simp+)

apply (frule n_val_valuation[of v])
apply (frule val_nonzero_z[of "n_val K v" "p"])
 apply (simp add:Vr_mem_f_mem)
 apply (frule PolynRg.subring[of "R" "Vr K v" "X"])
 apply (simp only:Ring.Subring_zero_ring_zero[THEN sym, of "R" "Vr K v"])
 apply (simp add:Vr_0_f_0, erule exE)
 apply (frule val_pos_mem_Vr[THEN sym, of "v" "p"])
 apply (simp add:Vr_mem_f_mem, simp)
 apply (frule val_pos_n_val_pos[of "v" "p"])
 apply (simp add:Vr_mem_f_mem, simp)
 apply (simp add:ant_0[THEN sym])
apply (frule_tac z = z in zpos_nat, erule exE)
apply (unfold pol_limit_def, erule conjE)
 apply (rotate_tac -1, drule_tac x = "Suc n" in spec)
 apply (subgoal_tac "\<not> (\<exists>M. \<forall>m. M < m \<longrightarrow>
             P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an (Suc n))\<^esup>) ( F m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p))")
 apply blast
 apply (thin_tac "\<exists>M. \<forall>m. M < m \<longrightarrow>
           P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an (Suc n))\<^esup>) (F m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p)")
 apply simp
 apply (subgoal_tac "M < (Suc M) \<and>
       \<not> P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an (Suc n))\<^esup>) (\<zero>\<^bsub>R\<^esub> \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p)")
 apply blast
 apply simp
 apply (frule Ring.ring_is_ag[of "R"])
 apply (frule aGroup.ag_mOp_closed[of "R" "p"], assumption) 
 apply (simp add:aGroup.ag_l_zero)
 apply (frule Ring.ring_is_ag[of "Vr K v"])
 apply (frule aGroup.ag_mOp_closed[of "Vr K v" "p"], assumption) 
 apply (frule_tac n = "an (Suc n)" in vp_apow_ideal[of v], simp)
 apply (frule PolynRg.subring[of "R" "Vr K v" "X"])
 apply (simp add:Ring.Subring_minus_ring_minus[THEN sym, of "R" "Vr K v"])
 apply (simp add:PolynRg.P_mod_coeffTr[of "R" "Vr K v" "X" _ "-\<^sub>a\<^bsub>(Vr K v)\<^esub> p"])
 apply (rule contrapos_pp, simp+)

 apply (frule_tac I = "vp K v\<^bsup> (Vr K v) (an (Suc n))\<^esup>" in 
        Ring.ideal_inv1_closed[of "Vr K v" _ "-\<^sub>a\<^bsub>(Vr K v)\<^esub> p"], assumption+)
 apply (simp add:aGroup.ag_inv_inv)
 apply (frule_tac n = "an (Suc n)" in n_value_x_1[of "v" _ "p"], simp)   
 apply assumption
 apply simp
 apply (simp add:ant_int, simp add:ale_natle)

apply (fold pol_limit_def) 
apply (case_tac "ad = \<infinity>", simp)
apply simp apply (erule exE)
apply (subgoal_tac "0 \<le> ad")
apply (frule Plimit_deg[of "v" "R" "X" "F" "na ad" "p"], assumption+)
 apply (simp add:an_na)+
apply (drule_tac x = n in spec,
       drule_tac x = n in spec)

apply (frule_tac p = "F n" in PolynRg.nonzero_deg_pos[of "R" "Vr K v" "X"],
           assumption+)
apply (rule_tac j = "deg R (Vr K v) X (F n)" in ale_trans[of "0" _ "ad"],
           assumption+)
done

lemma (in Corps) Plimit_ldeg:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X;
     \<forall>n. F n \<in> carrier R; p \<in> carrier R; 
     \<forall>n. deg R (Vr K v) X (F n) \<le> an (Suc d); 
      Plimit\<^bsub> R X K v \<^esub>F p\<rbrakk>  \<Longrightarrow>  Plimit\<^bsub> R X K v \<^esub>(Pseql\<^bsub> R X K v d \<^esub>F) 
                                             (ldeg_p R (Vr K v) X d p)"
apply (frule Vr_ring[of v], frule PolynRg.is_Ring,
       frule Ring.ring_is_ag[of "R"])
apply (frule Plimit_deg[of v R X F "Suc d" p], assumption+)
apply (simp add:Pseql_def, simp add:pol_limit_def)
apply (rule conjI, rule allI)
 apply (rule PolynRg.ldeg_p_mem, assumption+, simp+)
 apply (rule allI)
 apply (rotate_tac -5, drule_tac x = N in spec, erule exE)
 apply (subgoal_tac "\<forall>m > M. P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
              (ldeg_p R (Vr K v) X d (F m) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (ldeg_p R (Vr K v) X d p))",
        blast)
 apply (rule allI, rule impI)
 apply (rotate_tac -2, 
        frule_tac x = m in spec,
        thin_tac "\<forall>m. M < m \<longrightarrow>
            P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>) ( F m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p)",
        simp)
 apply (subst v_ldeg_p_mOp[of v R X _ d], assumption+)
 apply (subst v_ldeg_p_pOp[of v R X _ "-\<^sub>a\<^bsub>R\<^esub> p"], assumption+)
 apply (simp, rule aGroup.ag_mOp_closed, assumption, simp, simp)
 apply (frule PolynRg.deg_minus_eq1 [THEN sym, of "R" "Vr K v" "X" "p"], 
        assumption+)
 apply simp 
apply (rule_tac p = "F m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p" and N = N in PCauchy_lTr[of  "v"  
       "R" "X" _ "d" ], assumption+)
 apply (rule_tac x = "F m" in aGroup.ag_pOp_closed[of "R" _ "-\<^sub>a\<^bsub>R\<^esub> p"], 
       assumption+)
 apply (simp, rule aGroup.ag_mOp_closed, assumption+)
apply (frule PolynRg.deg_minus_eq1 [of "R" "Vr K v" "X" "p"], assumption+)
apply (rule PolynRg.polyn_deg_add4[of "R" "Vr K v" "X" _ "-\<^sub>a\<^bsub>R\<^esub> p" "Suc d"],
         assumption+)
  apply (simp, rule aGroup.ag_mOp_closed, assumption, simp+)
done

lemma (in Corps) Plimit_hdeg:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X;
     \<forall>n. F n \<in> carrier R; \<forall>n. deg R (Vr K v) X (F n) \<le> an (Suc d); 
      p \<in> carrier R; Plimit\<^bsub> R X K v  \<^esub>F p\<rbrakk>  \<Longrightarrow>  
      Plimit\<^bsub> R X K v  \<^esub>(Pseqh\<^bsub> R X K v d \<^esub>F) (hdeg_p R (Vr K v) X (Suc d) p)"
apply (frule Vr_ring[of "v"], frule PolynRg.is_Ring,
       frule Ring.ring_is_ag[of "R"])
apply (frule Plimit_deg[of v R X F "Suc d" p], assumption+)
apply (simp add:Pseqh_def, simp add:pol_limit_def)
apply (rule conjI, rule allI)
 apply (rule PolynRg.hdeg_p_mem, assumption+, simp+)
 apply (rule allI)
 apply (rotate_tac -5, drule_tac x = N in spec)
 apply (erule exE) 
 apply (subgoal_tac "\<forall>m>M. P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
  (hdeg_p R (Vr K v) X (Suc d) (F m) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (hdeg_p R (Vr K v) X (Suc d) p))",
    blast)
 apply (rule allI, rule impI)
 apply (rotate_tac -2, 
        drule_tac x = m in spec, simp)
 apply (subst v_hdeg_p_mOp[of v R X _ d], assumption+)
 apply (subst v_hdeg_p_pOp[of v R X _ "-\<^sub>a\<^bsub>R\<^esub> p"], assumption+)
 apply (simp, rule aGroup.ag_mOp_closed, assumption, simp, simp)
 apply (frule PolynRg.deg_minus_eq1 [THEN sym, of R "Vr K v" X p], assumption+)
 apply simp 
apply (rule_tac p = "F m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p" and N = N in PCauchy_hTr[of v R X _ d ], 
       assumption+)
 apply (rule_tac x = "F m" in aGroup.ag_pOp_closed[of R _ "-\<^sub>a\<^bsub>R\<^esub> p"], 
        assumption+)
 apply (simp, rule aGroup.ag_mOp_closed, assumption+)
apply (frule PolynRg.deg_minus_eq1 [of "R" "Vr K v" "X" "p"], assumption+)
apply (rule PolynRg.polyn_deg_add4[of "R" "Vr K v" "X" _ "-\<^sub>a\<^bsub>R\<^esub> p" "Suc d"],
         assumption+)
  apply (simp, rule aGroup.ag_mOp_closed, assumption, simp+)
done 

lemma (in Corps) P_limit_uniqueTr:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X\<rbrakk> \<Longrightarrow> 
 \<forall>F. ((\<forall>n. F n \<in> carrier R) \<and> (\<forall>n. deg R (Vr K v) X (F n) \<le> (an d)) \<longrightarrow>
      (\<forall>p1 p2. p1 \<in> carrier R \<and> p2 \<in> carrier R \<and> Plimit\<^bsub> R X K v \<^esub>F p1 \<and> 
           Plimit\<^bsub> R X K v \<^esub>F p2 \<longrightarrow> p1 = p2))"
apply (frule PolynRg.is_Ring)
apply (induct_tac d)
apply (rule allI, rule impI, (rule allI)+, rule impI)
apply (erule conjE)+
apply (subgoal_tac "\<forall>n. F n \<in> carrier (Vr K v)")
apply (frule Vr_ring[of "v"])
apply (frule PolynRg.X_mem_R[of "R" "Vr K v" "X"])
apply (frule_tac f = F and F = F and d = 0 and b = p1 and c = p2 in 
        mono_P_limt_unique[of v R X], assumption+)
apply (rule allI, drule_tac x = n in spec, 
       simp add:Ring.ring_r_one)
apply (frule_tac F = F and p = p1 in Plimit_deg[of v R X _ 0],
       assumption+, simp add:deg_0_const,
       frule_tac F = F and p = p2 in Plimit_deg[of v R X _ 0],
       assumption+, simp add:deg_0_const)
apply (simp add:Ring.ring_r_one)+ 
apply (simp add:deg_0_const)

(******** case Suc d **********)
apply (rename_tac d)
apply (rule allI, rule impI)
apply (erule conjE)
apply ((rule allI)+, rule impI, (erule conjE)+) 
apply (frule_tac F = F and p = p1 and d = d in Plimit_ldeg[of v R X],  
                 assumption+,
       frule_tac F = F and p = p2 and d = d in Plimit_ldeg[of v R X],  
                 assumption+,
       frule_tac F = F and p = p1 and d = d in Plimit_hdeg[of v R X],  
                 assumption+,
       frule_tac F = F and p = p2 and d = d in Plimit_hdeg[of v R X],  
                 assumption+)
apply (frule_tac a = "Pseql\<^bsub> R X K v d \<^esub>F" in forall_spec) 
 apply (rule conjI)
 apply (rule allI)
 apply (rule Pseql_mem, assumption+, simp)
 apply (rule allI, simp)
 apply (rule allI)
apply (subst Pseql_def)
 apply (rule_tac p = "F n" and d = d in PolynRg.deg_ldeg_p[of R "Vr K v" X],
                      assumption+) apply (simp add:Vr_ring)
 apply simp 
 apply (thin_tac "\<forall>F. (\<forall>n. F n \<in> carrier R) \<and> 
       (\<forall>n. deg R (Vr K v) X (F n) \<le> an d) \<longrightarrow>
         (\<forall>p1 p2. 
                p1 \<in> carrier R \<and>
                p2 \<in> carrier R \<and>
                Plimit\<^bsub> R X K v \<^esub>F p1 \<and> Plimit\<^bsub> R X K v \<^esub>F p2 \<longrightarrow>
                p1 = p2)")
apply (frule Vr_ring[of v])
apply (frule_tac F = F and d = "Suc d" and p = p1 in 
                           Plimit_deg[of v R X], assumption+,
       frule_tac F = F and d = "Suc d" and p = p2 in 
                           Plimit_deg[of v R X], assumption+)
apply (subgoal_tac "(ldeg_p R (Vr K v) X d p1) = (ldeg_p R (Vr K v) X d p2)")
apply (subgoal_tac "hdeg_p R (Vr K v) X (Suc d) p1 = 
                                        hdeg_p R (Vr K v) X (Suc d) p2")

apply (frule_tac p = p1 and d = d in PolynRg.decompos_p[of "R" "Vr K v" "X"],
                        assumption+,
       frule_tac p = p2 and d = d in PolynRg.decompos_p[of "R" "Vr K v" "X"],
                        assumption+)
 apply simp
 apply (thin_tac "Plimit\<^bsub> R X K v \<^esub>Pseql\<^bsub> R X K v d \<^esub>F (ldeg_p R (Vr K v) X d p1)",
        thin_tac "Plimit\<^bsub> R X K v \<^esub>Pseql\<^bsub> R X K v d \<^esub>F (ldeg_p R (Vr K v) X d p2)",
        thin_tac "\<forall>p1 p2. p1 \<in> carrier R \<and> p2 \<in> carrier R \<and> 
           Plimit\<^bsub> R X K v \<^esub>Pseql\<^bsub> R X K v d \<^esub>F p1 \<and>
           Plimit\<^bsub> R X K v \<^esub>Pseql\<^bsub> R X K v d \<^esub>F p2 \<longrightarrow> p1 = p2")
 apply (simp only:hdeg_p_def)
 apply (rule_tac f = "\<lambda>j. snd (scf_d R (Vr K v) X (F j) (Suc d)) (Suc d)" 
    and F = "Pseqh\<^bsub> R X K v d \<^esub>F" 
    and b = "(snd (scf_d R (Vr K v) X p1 (Suc d))) (Suc d)"
    and d = "Suc d" and c = "snd (scf_d R (Vr K v) X p2 (Suc d)) (Suc d)" in 
        mono_P_limt_unique[of v R X], assumption+)
 apply (rule allI) 
apply (frule_tac p = "F n" and d = "Suc d" in 
                 PolynRg.scf_d_pol[of "R" "Vr K v" "X"])
 apply (simp del:npow_suc)+
 apply (frule_tac c = "scf_d R (Vr K v) X (F n) (Suc d)" and
        j = "Suc d" in PolynRg.pol_coeff_mem[of R "Vr K v" X])
 apply simp apply (simp del:npow_suc)+
 apply (rule allI)
apply (frule_tac c = "scf_d R (Vr K v) X (F n) (Suc d)" and
        j = "Suc d" in PolynRg.pol_coeff_mem[of R "Vr K v" X])
 apply (frule_tac p = "F n" and d = "Suc d" in PolynRg.scf_d_pol[of R 
           "Vr K v" X], (simp del:npow_suc)+)
 apply (cut_tac p = "F n" and d = "Suc d" in PolynRg.scf_d_pol[of R 
           "Vr K v" X], (simp del:npow_suc)+)
          
 apply (subst Pseqh_def) apply (simp only:hdeg_p_def)
apply (frule_tac p = p1 and d = "Suc d" in PolynRg.scf_d_pol[of R "Vr K v" X],
       assumption+)
 apply (rule_tac c = "scf_d R (Vr K v) X p1 (Suc d)" and
        j = "Suc d" in PolynRg.pol_coeff_mem[of R "Vr K v" X], assumption+,
   simp, simp)
apply (frule_tac p = p2 and d = "Suc d" in PolynRg.scf_d_pol[of R "Vr K v" X],
       assumption+)
 apply (rule_tac c = "scf_d R (Vr K v) X p2 (Suc d)" and
        j = "Suc d" in PolynRg.pol_coeff_mem[of R "Vr K v" X], assumption+,
   simp, simp) apply simp apply simp 
 apply (rotate_tac -4,
        drule_tac x = "ldeg_p R (Vr K v) X d p1" in spec,
        rotate_tac -1,
        drule_tac x = "ldeg_p R (Vr K v) X d p2" in spec) 
 apply (simp add:PolynRg.ldeg_p_mem)
done

lemma (in Corps) P_limit_unique:"\<lbrakk>valuation K v; Complete\<^bsub>v\<^esub> K;
  PolynRg R (Vr K v) X; \<forall>n. F n \<in> carrier R; 
  \<forall>n. deg R (Vr K v) X (F n) \<le> (an d); p1 \<in> carrier R; p2 \<in> carrier R; 
  Plimit\<^bsub> R X K v \<^esub>F p1; Plimit\<^bsub> R X K v \<^esub>F p2\<rbrakk> \<Longrightarrow>  p1 = p2"
apply (frule P_limit_uniqueTr[of "v" "R" "X" "d"], assumption+)
apply blast
done 

lemma (in Corps) P_limitTr:"\<lbrakk>valuation K v; Complete\<^bsub>v\<^esub> K; PolynRg R (Vr K v) X\<rbrakk>
 \<Longrightarrow> \<forall>F. ((\<forall>n. F n \<in> carrier R) \<and> (\<forall>n. deg R (Vr K v) X (F n) \<le> (an d)) \<and>
        (\<forall>N. \<exists>M. \<forall>n m. M < n \<and> M < m \<longrightarrow> 
        P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>) (F n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (F m))) \<longrightarrow>
        (\<exists>p\<in>carrier R. Plimit\<^bsub> R X K v \<^esub>F p))"
apply (frule PolynRg.is_Ring)
apply (frule Vr_ring[of v])
 apply (induct_tac d)

 apply simp
 apply (rule allI, rule impI, (erule conjE)+)
 apply (frule_tac F = F and f = F in monomial_P_limt[of v R X  _ _ 0], 
        assumption+)
 apply (rule allI)
 apply (rotate_tac 5, drule_tac x = n in spec) 
 apply (simp add:deg_0_const)
 apply (rule allI)
  apply (drule_tac x = n in spec,
         thin_tac "\<forall>n. deg R (Vr K v) X (F n) \<le> 0")
  apply (frule PolynRg.X_mem_R[of "R" "Vr K v" "X"],
         frule PolynRg.is_Ring,
         simp add:Ring.ring_r_one, assumption)

 apply (erule bexE)
 apply (frule PolynRg.subring[of "R" "Vr K v" "X"]) 
 apply (cut_tac x = b in Ring.mem_subring_mem_ring[of "R" "Vr K v"])
  apply (frule PolynRg.X_mem_R[of "R" "Vr K v" "X"], assumption+)
  apply (simp add:Ring.ring_r_one, blast)

(*********** case n ***************)
apply (rule allI, rule impI) apply (rename_tac d F)
apply (erule conjE)+
 apply (subgoal_tac "(\<forall>n.(Pseql\<^bsub> R X K v d \<^esub>F) n \<in> carrier R) \<and>
    (\<forall>n. deg R (Vr K v) X ((Pseql\<^bsub> R X K v d \<^esub>F) n) \<le> an d) \<and>
    (\<forall>N. \<exists>M. \<forall>n m. M < n \<and> M < m \<longrightarrow>
     P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
        ((Pseql\<^bsub> R X K v d \<^esub>F) n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> ((Pseql\<^bsub> R X K v d \<^esub>F) m)))")
 apply (frule_tac a = "Pseql\<^bsub> R X K v d \<^esub>F" in forall_spec, assumption)
 apply (erule bexE)
 apply (thin_tac "\<forall>F. (\<forall>n. F n \<in> carrier R) \<and>
     (\<forall>n. deg R (Vr K v) X (F n) \<le> an d) \<and>
     (\<forall>N. \<exists>M. \<forall>n m. M < n \<and> M < m \<longrightarrow>
        P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>) (F n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (F m))) \<longrightarrow>
        (\<exists>p\<in>carrier R. Plimit\<^bsub> R X K v \<^esub>F p)",
     thin_tac "(\<forall>n. (Pseql\<^bsub> R X K v d \<^esub>F) n \<in> carrier R) \<and>
     (\<forall>n. deg R (Vr K v) X ((Pseql\<^bsub> R X K v d \<^esub>F) n) \<le> an d) \<and>
    (\<forall>N. \<exists>M. \<forall>n m. M < n \<and> M < m \<longrightarrow> P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
    ((Pseql\<^bsub> R X K v d \<^esub>F) n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> ((Pseql\<^bsub> R X K v d \<^esub>F) m)))")
 apply (subgoal_tac "\<forall>N. \<exists>M. \<forall>n m. M < n \<and> M < m \<longrightarrow>
                      P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
                       ((Pseqh\<^bsub>R X K v d\<^esub> F) n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> ((Pseqh\<^bsub>R X K v d\<^esub> F) m))")
 apply (frule_tac f = "\<lambda>j. snd (scf_d R (Vr K v) X (F j) (Suc d)) (Suc d)" 
  and  F = "Pseqh\<^bsub> R X K v d \<^esub>F" and d = "Suc d" in monomial_P_limt[of v R X], 
       assumption+)
 apply (rule allI)
 apply (drule_tac x = n in spec,
        drule_tac x = n in spec,
        frule_tac p = "F n" and d = "Suc d" in PolynRg.scf_d_pol[of R "Vr K v" 
       "X"], assumption+, (erule conjE)+)
 apply (rule_tac c = "scf_d R (Vr K v) X (F n) (Suc d)" and j = "Suc d" in 
        PolynRg.pol_coeff_mem[of R "Vr K v" X], assumption+) 
 apply simp
 apply (rule allI)
  apply (thin_tac "\<forall>N. \<exists>M. \<forall>n m. M < n \<and> M < m \<longrightarrow>
         P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
                       ( (Pseqh\<^bsub> R X K v d \<^esub>F) n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> ((Pseqh\<^bsub> R X K v d \<^esub>F) m))")
  apply (simp only:Pseqh_def hdeg_p_def, assumption, erule bexE)

apply (thin_tac "\<forall>N. \<exists>M. \<forall>n m. M < n \<and> M < m \<longrightarrow>
       P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>) (F n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (F m))",
       thin_tac "\<forall>N. \<exists>M. \<forall>n m. M < n \<and> M < m \<longrightarrow>
               P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
               ((Pseqh\<^bsub> R X K v d \<^esub>F) n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> ((Pseqh\<^bsub> R X K v d \<^esub>F) m))")

apply (subgoal_tac "Plimit\<^bsub> R X K v \<^esub>F (p \<plusminus>\<^bsub>R\<^esub> b \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R (Suc d)\<^esup>))",
       subgoal_tac "p \<plusminus>\<^bsub>R\<^esub> b \<cdot>\<^sub>r\<^bsub>R\<^esub>(X^\<^bsup>R (Suc d)\<^esup>) \<in> carrier R", blast)

apply (frule PolynRg.X_mem_R[of "R" "Vr K v" "X"],
       frule_tac n = "Suc d" in Ring.npClose[of "R" "X"], assumption+,
       frule Ring.ring_is_ag[of "R"],
       rule aGroup.ag_pOp_closed[of "R"], assumption+,
       rule Ring.ring_tOp_closed, assumption+)
 apply (frule PolynRg.subring[of "R" "Vr K v" "X"],
        simp add:Ring.mem_subring_mem_ring, assumption) 

apply (simp del:npow_suc add:pol_limit_def,
       rule allI,
       subgoal_tac "\<forall>n. F n = (Pseql\<^bsub> R X K v d \<^esub>F) n \<plusminus>\<^bsub>R\<^esub> ((Pseqh\<^bsub> R X K v d \<^esub>F) n)",
       simp del:npow_suc,
       subgoal_tac "\<forall>m. (Pseql\<^bsub> R X K v d \<^esub>F) m \<plusminus>\<^bsub>R\<^esub> ((Pseqh\<^bsub> R X K v d \<^esub>F) m) \<plusminus>\<^bsub>R\<^esub>
        -\<^sub>a\<^bsub>R\<^esub> (p \<plusminus>\<^bsub>R\<^esub> (b \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R (Suc d)\<^esup>))) = (Pseql\<^bsub> R X K v d \<^esub>F) m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p \<plusminus>\<^bsub>R\<^esub> 
         ((Pseqh\<^bsub> R X K v d \<^esub>F) m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (b \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R (Suc d)\<^esup>)))",
       simp del:npow_suc)
 
apply (thin_tac "\<forall>m. (Pseql\<^bsub>R  X K v d \<^esub>F) m \<plusminus>\<^bsub>R\<^esub> (Pseqh\<^bsub> R X K v d \<^esub>F) m \<plusminus>\<^bsub>R\<^esub>
    -\<^sub>a\<^bsub>R\<^esub> (p \<plusminus>\<^bsub>R\<^esub> b \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R (Suc d)\<^esup>) = (Pseql\<^bsub>R  X K v d \<^esub>F) m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p \<plusminus>\<^bsub>R\<^esub>
     ((Pseqh\<^bsub> R X K v d \<^esub>F) m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> b \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R (Suc d)\<^esup>)")
apply (erule conjE)+
apply (rotate_tac -3, 
       drule_tac x = N in spec, erule exE)
apply (rotate_tac 1, 
       drule_tac x = N in spec, erule exE)
apply (rename_tac d F p b N M1 M2)
apply (subgoal_tac "\<forall>m. (max M1 M2) < m \<longrightarrow>
           P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
           ((Pseql\<^bsub> R X K v d \<^esub>F) m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p \<plusminus>\<^bsub>R\<^esub>
            ((Pseqh\<^bsub> R X K v d \<^esub>F) m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (b \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R (Suc d)\<^esup>))))", blast)
apply (rule allI, rule impI)
apply (rotate_tac -2, 
       drule_tac x = m in spec, simp del:npow_suc)
apply (erule conjE)
apply (rotate_tac -5,
       drule_tac x = m in spec, simp del:npow_suc)
 apply (frule_tac n = "an N" in vp_apow_ideal[of v], simp del:npow_suc)
 apply (frule Ring.ring_is_ag[of "R"])
 apply (rule_tac I = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and 
        p = "(Pseql\<^bsub> R X K v d \<^esub>F) m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p" and 
        q = "(Pseqh\<^bsub> R X K v d \<^esub>F) m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (b \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R (Suc d)\<^esup>))" in 
        PolynRg.P_mod_add[of R "Vr K v" X], assumption+)

apply (rule aGroup.ag_pOp_closed, assumption+) 
 apply (simp add:Pseql_mem, rule aGroup.ag_mOp_closed, assumption+)

 apply (rule aGroup.ag_pOp_closed[of "R"], assumption)
 apply (simp add:Pseqh_mem, rule aGroup.ag_mOp_closed, assumption)
 apply (rule Ring.ring_tOp_closed, assumption)
 apply (frule PolynRg.subring[of "R" "Vr K v" "X"])
 apply (simp add:Ring.mem_subring_mem_ring)
 apply (frule PolynRg.X_mem_R[of "R" "Vr K v" "X"])
 apply (rule Ring.npClose, assumption+)

apply (rule allI)
 apply (thin_tac "\<forall>n.(Pseql\<^bsub> R X K v d \<^esub>F) n \<plusminus>\<^bsub>R\<^esub>((Pseqh\<^bsub> R X K v d \<^esub>F) n) \<in> carrier R")
 apply (erule conjE)+
 apply (thin_tac "\<forall>n. deg R (Vr K v) X
             ((Pseql\<^bsub>R  X K v d \<^esub>F) n \<plusminus>\<^bsub>R\<^esub> (Pseqh\<^bsub> R X K v d \<^esub>F) n) \<le> an (Suc d)")
 apply (thin_tac "\<forall>N. \<exists>M. \<forall>m>M. P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
                       ((Pseql\<^bsub>R  X K v d \<^esub>F) m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p)",
        thin_tac "\<forall>N. \<exists>M. \<forall>m>M. P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
                       ((Pseqh\<^bsub> R X K v d \<^esub>F) m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> b \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R (Suc d)\<^esup>)",
        thin_tac "\<forall>n. F n = (Pseql\<^bsub> R X K v d \<^esub>F) n \<plusminus>\<^bsub>R\<^esub> ((Pseqh\<^bsub> R X K v d \<^esub>F) n)") 
 apply (drule_tac x = m in spec,
        drule_tac x = m in spec)
 apply (subgoal_tac "b \<cdot>\<^sub>r\<^bsub>R\<^esub> X^\<^bsup>R (Suc d)\<^esup> \<in> carrier R")
 apply (frule Ring.ring_is_ag[of "R"])
 apply (frule_tac x = p in aGroup.ag_mOp_closed[of "R"], assumption+)
 apply (subst aGroup.ag_pOp_assoc[of "R"], assumption+)
 apply (rule aGroup.ag_mOp_closed, assumption+)
 apply (rule aGroup.ag_pOp_closed, assumption+)
 apply (frule_tac x1 = "-\<^sub>a\<^bsub>R\<^esub> p" and y1 = "(Pseqh\<^bsub> R X K v d \<^esub>F) m" and z1 = 
  "-\<^sub>a\<^bsub>R\<^esub> (b \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R (Suc d)\<^esup>))" in aGroup.ag_pOp_assoc[THEN sym, of "R"], 
  assumption+)
 apply (rule aGroup.ag_mOp_closed, assumption+, simp del:npow_suc)
 apply (subst aGroup.ag_pOp_assoc[THEN sym], assumption+)
 apply (rule aGroup.ag_mOp_closed, assumption+,
        rule aGroup.ag_pOp_closed, assumption+)
 apply (subst aGroup.ag_add4_rel[of R], assumption+)
 apply (rule aGroup.ag_mOp_closed, assumption+)
 apply (subst aGroup.ag_p_inv[THEN sym, of R], assumption+, simp del:npow_suc)

 apply (rule Ring.ring_tOp_closed, assumption+,
        frule PolynRg.subring[of R "Vr K v" X],
        simp add:Ring.mem_subring_mem_ring,
        rule Ring.npClose, assumption+, simp add:PolynRg.X_mem_R)
apply (rule allI)
apply (rule_tac F = F and n = n and d = d in Pseq_decompos[of "v" "R" "X"],
       assumption+, simp, simp)
apply (rule allI)
apply (rotate_tac -3, drule_tac x = N in spec)
apply (erule exE)
 apply (subgoal_tac "\<forall>n m. M < n \<and> M < m \<longrightarrow>
                    P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
                     ((Pseqh\<^bsub> R X K v d \<^esub>F) n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> ((Pseqh\<^bsub> R X K v d \<^esub>F) m))")
 apply blast
 apply ((rule allI)+, rule impI)
 apply (rotate_tac -2,
        drule_tac x = n in spec, 
        rotate_tac -1,
        drule_tac x = m in spec,
        simp) 
 
apply (simp only: Pseqh_def)
apply (subst v_hdeg_p_mOp[of "v" "R" "X"], assumption+)
 apply simp+

apply (frule Ring.ring_is_ag[of "R"])
apply (subst v_hdeg_p_pOp[of "v" "R" "X"], assumption+)
apply (simp, rule aGroup.ag_mOp_closed, assumption, simp, simp,
       frule_tac p1 = "F m" in PolynRg.deg_minus_eq1 [THEN sym, of R "Vr K v" 
       X])
apply simp 
apply (rotate_tac -1, frule sym, 
       thin_tac "deg R (Vr K v) X (F m) = deg R (Vr K v) X (-\<^sub>a\<^bsub>R\<^esub> (F m))", simp)
apply (rule PCauchy_hTr[of v R X], assumption+)
apply (rule_tac x = "F n" and y = "-\<^sub>a\<^bsub>R\<^esub> (F m)" in aGroup.ag_pOp_closed[of "R"], 
       assumption+,
       simp, rule aGroup.ag_mOp_closed, assumption+, simp)
apply (frule_tac p = "F m" in PolynRg.deg_minus_eq1 [of R "Vr K v" X],
       simp, 
       rule_tac p = "F n" and q = "-\<^sub>a\<^bsub>R\<^esub> (F m)" and n = "Suc d" in 
       PolynRg.polyn_deg_add4[of "R" "Vr K v" "X"], assumption+,
       simp, rule aGroup.ag_mOp_closed, assumption, simp+)

apply (rule conjI, rule allI, rule Pseql_mem, assumption+, simp)
 apply (rule allI, simp) 

apply (thin_tac "\<forall>F. (\<forall>n. F n \<in> carrier R) \<and>
      (\<forall>n. deg R (Vr K v) X (F n) \<le> an d) \<and>
       (\<forall>N. \<exists>M. \<forall>n m. M < n \<and> M < m \<longrightarrow>
          P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>) (F n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (F m))) \<longrightarrow>
               (\<exists>p\<in>carrier R. Plimit\<^bsub> R X K v \<^esub>F p)")

apply (rule conjI, rule allI)
 apply (subst Pseql_def)
 apply (rule_tac p = "F n" and d = d in PolynRg.deg_ldeg_p[of R "Vr K v" X],
        assumption+)
 apply simp+

apply (simp only: Pseql_def)
 apply (rule allI)
 apply (rotate_tac -1, drule_tac x = N in spec)
 apply (erule exE)
 apply (subgoal_tac "\<forall>n m. M < n \<and> M < m \<longrightarrow>
        P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>) 
          (ldeg_p R (Vr K v) X d (F n) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (ldeg_p R (Vr K v) X d (F m)))")
 apply blast
 apply ((rule allI)+, rule impI, erule conjE)
 apply (rotate_tac -3, drule_tac x = n in spec,
        rotate_tac -1, drule_tac x = m in spec, simp) 

apply (subst v_ldeg_p_mOp[of v R X], assumption+, simp+)

apply (frule Ring.ring_is_ag[of "R"])
apply (subst v_ldeg_p_pOp[of v R X], assumption+, simp,
       rule aGroup.ag_mOp_closed, assumption, simp, simp,
       frule_tac p = "F m" in PolynRg.deg_minus_eq1[of R "Vr K v" X], simp)
apply simp 
apply (rule PCauchy_lTr[of v R X], assumption+)
apply (rule_tac x = "F n" and y = "-\<^sub>a\<^bsub>R\<^esub> (F m)" in aGroup.ag_pOp_closed[of R], 
       assumption+,
       simp, rule aGroup.ag_mOp_closed, assumption+, simp)

apply (frule_tac p = "F m" in PolynRg.deg_minus_eq1[of R "Vr K v" X], simp,
       rule_tac p = "F n" and q = "-\<^sub>a\<^bsub>R\<^esub> (F m)" and n = "Suc d" in 
       PolynRg.polyn_deg_add4[of "R" "Vr K v" "X"], assumption+,
       simp, rule aGroup.ag_mOp_closed, assumption, simp+)
done

lemma (in Corps) PCauchy_Plimit:"\<lbrakk>valuation K v; Complete\<^bsub>v\<^esub> K;
      PolynRg R (Vr K v) X; PCauchy\<^bsub>R X K v\<^esub> F\<rbrakk> \<Longrightarrow>
        \<exists>p\<in>carrier R. Plimit\<^bsub>R X K v\<^esub> F p"
apply (simp add:pol_Cauchy_seq_def)
apply ((erule conjE)+, erule exE)
apply (frule_tac d = d in P_limitTr[of  "v" "R" "X"], assumption+)
apply (drule_tac a = F in forall_spec, simp)
apply assumption
done

lemma (in Corps) P_limit_mult:"\<lbrakk>valuation K v; PolynRg R (Vr K v) X; 
  \<forall>n. F n \<in> carrier R; \<forall>n. G n \<in> carrier R; p1 \<in> carrier R; p2 \<in> carrier R; 
  Plimit\<^bsub> R X K v \<^esub>F p1; Plimit\<^bsub> R X K v \<^esub>G p2\<rbrakk> \<Longrightarrow>  
                  Plimit\<^bsub> R X K v\<^esub> (\<lambda>n. (F n) \<cdot>\<^sub>r\<^bsub>R\<^esub> (G n)) (p1 \<cdot>\<^sub>r\<^bsub>R\<^esub> p2)"
apply (frule Vr_ring[of v],
       frule PolynRg.is_Ring,
       frule Ring.ring_is_ag[of "R"])
apply (simp add:pol_limit_def)
apply (rule conjI)
apply (rule allI)
 apply (drule_tac x = n in spec,
        drule_tac x = n in spec)

 apply (simp add:Ring.ring_tOp_closed[of "R"])

apply (rule allI)
 apply (rotate_tac 6,
        drule_tac x = N in spec,
        drule_tac x = N in spec)
 apply (erule exE, erule exE, rename_tac N M1 M2) 
 apply (subgoal_tac "\<forall>m. (max M1 M2) < m \<longrightarrow>
          P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
                     ((F m) \<cdot>\<^sub>r\<^bsub>R\<^esub> (G m) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (p1 \<cdot>\<^sub>r\<^bsub>R\<^esub>  p2))")
 apply blast 
 
apply (rule allI, rule impI, simp, erule conjE)
 apply (rotate_tac -4, 
        drule_tac x = m in spec,
        drule_tac x = m in spec, simp)
 apply (subgoal_tac "(F m) \<cdot>\<^sub>r\<^bsub>R\<^esub> (G m) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p1 \<cdot>\<^sub>r\<^bsub>R\<^esub> p2 =
             ((F m) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p1) \<cdot>\<^sub>r\<^bsub>R\<^esub> (G m) \<plusminus>\<^bsub>R\<^esub>  p1 \<cdot>\<^sub>r\<^bsub>R\<^esub> ((G m) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p2)", simp) 
 apply (frule_tac n = "an N" in vp_apow_ideal[of v])
 apply simp
 apply (rule_tac I = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and 
        p = "((F m) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p1) \<cdot>\<^sub>r\<^bsub>R\<^esub> (G m)" and  q = "p1 \<cdot>\<^sub>r\<^bsub>R\<^esub> ((G m) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p2)"
        in PolynRg.P_mod_add[of R "Vr K v" "X"],
         assumption+)
 apply (rule Ring.ring_tOp_closed[of "R"], assumption+)
 apply (rule aGroup.ag_pOp_closed, assumption) apply simp 
 apply (rule aGroup.ag_mOp_closed, assumption+) apply simp
 apply (rule Ring.ring_tOp_closed[of "R"], assumption+)
 apply (rule aGroup.ag_pOp_closed, assumption) apply simp
  apply (rule aGroup.ag_mOp_closed, assumption+) 
apply (frule Ring.whole_ideal[of "Vr K v"])
apply (frule_tac I = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and J = "carrier (Vr K v)" and 
   p = "F m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p1" and q = "G m" in PolynRg.P_mod_mult1[of R "Vr K v" X],
   assumption+,
   rule aGroup.ag_pOp_closed, assumption+, simp, rule aGroup.ag_mOp_closed,
      assumption+) apply simp apply assumption
apply (rotate_tac 8,
       drule_tac x = m in spec)
apply (case_tac "G m = \<zero>\<^bsub>R\<^esub>", simp add:P_mod_def)
apply (frule_tac p = "G m" in PolynRg.s_cf_expr[of R "Vr K v" X], assumption+,
       (erule conjE)+)
thm PolynRg.P_mod_mod
apply (frule_tac I1 = "carrier (Vr K v)" and p1 = "G m" and 
       c1 = "s_cf R (Vr K v) X (G m)" in PolynRg.P_mod_mod[THEN sym, 
       of R "Vr K v" X], assumption+)
apply (simp,
      thin_tac "P_mod R (Vr K v) X (carrier (Vr K v)) (G m) =
        (\<forall>j\<le>fst (s_cf R (Vr K v) X (G m)).
            snd (s_cf R (Vr K v) X (G m)) j \<in> carrier (Vr K v))")
apply (rule allI, rule impI)
 apply (simp add:PolynRg.pol_coeff_mem)
apply (simp add:Ring.idealprod_whole_r[of "Vr K v"]) 

apply (cut_tac I = "carrier (Vr K v)" and J = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and 
      p = p1 and q = "G m \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> p2" in PolynRg.P_mod_mult1[of R "Vr K v" X],
      assumption+) 
apply (simp only: Ring.whole_ideal, assumption+) 
apply (rule aGroup.ag_pOp_closed, assumption+, simp, rule aGroup.ag_mOp_closed,
      assumption+)
apply (frule PolynRg.s_cf_expr0[of R "Vr K v" X p1], assumption+)
  thm PolynRg.P_mod_mod
apply (cut_tac I1 = "carrier (Vr K v)" and p1 = p1 and 
       c1 = "s_cf R (Vr K v) X p1" in PolynRg.P_mod_mod[THEN sym,
        of R "Vr K v" X], assumption+)
apply (simp add:Ring.whole_ideal, assumption+)
apply (simp, simp, simp, (erule conjE)+,
       thin_tac "P_mod R (Vr K v) X (carrier (Vr K v)) p1 =
        (\<forall>j\<le>fst (s_cf R (Vr K v) X p1).
            snd (s_cf R (Vr K v) X p1) j \<in> carrier (Vr K v))")     
 apply (rule allI, rule impI)
 apply (simp add:PolynRg.pol_coeff_mem, assumption)  
apply (simp add:Ring.idealprod_whole_l[of "Vr K v"]) 
apply (drule_tac x = m in spec,
       drule_tac x = m in spec)
apply (frule aGroup.ag_mOp_closed[of R p1], assumption,
       frule aGroup.ag_mOp_closed[of R p2], assumption )
apply (simp add:Ring.ring_distrib1 Ring.ring_distrib2)
 apply (subst aGroup.pOp_assocTr43[of R], assumption+,
        (rule Ring.ring_tOp_closed, assumption+)+)
 apply (simp add:Ring.ring_inv1_1[THEN sym],
        simp add:Ring.ring_inv1_2[THEN sym])
apply (frule_tac x = p1 and y = "G m" in Ring.ring_tOp_closed, assumption+,
       frule_tac x = "F m" and y = "G m" in Ring.ring_tOp_closed, assumption+,
       simp add:aGroup.ag_l_inv1 aGroup.ag_r_zero)
done
       (** Hfst K v R X t S Y f g h m**)
definition
  Hfst :: "[_, 'b \<Rightarrow> ant, ('b, 'm1) Ring_scheme, 'b,'b, ('b set, 'm2) Ring_scheme, 'b set, 'b, 'b, 'b, nat] \<Rightarrow> 'b" 
        ("(11Hfst\<^bsub> _ _ _ _ _ _ _ _ _ _\<^esub> _)" [67,67,67,67,67,67,67,67,67,67,68]67) where
  "Hfst\<^bsub>K v R X t S Y f g h\<^esub> m = fst (Hpr\<^bsub>R (Vr K v) X t S Y f g h\<^esub> m)"

definition
  Hsnd :: "[_, 'b \<Rightarrow> ant, ('b, 'm1) Ring_scheme, 'b,'b, ('b set, 'm2) Ring_scheme, 'b set, 'b, 'b, 'b, nat] \<Rightarrow> 'b" 
        ("(11Hsnd\<^bsub> _ _ _ _ _ _ _ _ _ _\<^esub> _)" [67,67,67,67,67,67,67,67,67,67,68]67) where
 
  "Hsnd\<^bsub>K v R X t S Y f g h\<^esub> m = snd (Hpr\<^bsub>R (Vr K v) X t S Y f g h\<^esub> m)"

lemma (in Corps) Hensel_starter:"\<lbrakk>valuation K v; Complete\<^bsub>v\<^esub> K; 
    PolynRg R (Vr K v) X; PolynRg S ((Vr K v) /\<^sub>r (vp K v)) Y;
    t \<in> carrier (Vr K v); vp K v = (Vr K v) \<diamondsuit>\<^sub>p t;
    f \<in> carrier R; f \<noteq> \<zero>\<^bsub>R\<^esub>; g' \<in> carrier S; h' \<in> carrier S;
    0 < deg S ((Vr K v) /\<^sub>r (vp K v)) Y g';
    0 < deg S ((Vr K v) /\<^sub>r (vp K v)) Y h';
    ((erH R (Vr K v) X S ((Vr K v) /\<^sub>r (vp K v)) Y 
             (pj  (Vr K v) (vp K v))) f) =  g' \<cdot>\<^sub>r\<^bsub>S\<^esub> h';
    rel_prime_pols S ((Vr K v) /\<^sub>r (vp K v)) Y g' h'\<rbrakk> \<Longrightarrow> 
 \<exists>g h. g \<noteq> \<zero>\<^bsub>R\<^esub> \<and> h \<noteq> \<zero>\<^bsub>R\<^esub> \<and> g \<in> carrier R \<and> h \<in> carrier R \<and>
  deg R (Vr K v) X g \<le> deg S ((Vr K v) /\<^sub>r ((Vr K v) \<diamondsuit>\<^sub>p t)) Y
   (erH R (Vr K v) X S ((Vr K v) /\<^sub>r ((Vr K v) \<diamondsuit>\<^sub>p t)) Y 
   (pj (Vr K v) ((Vr K v) \<diamondsuit>\<^sub>p t)) g) \<and> (deg R (Vr K v) X h + 
    deg S ((Vr K v) /\<^sub>r ((Vr K v) \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S 
     ((Vr K v) /\<^sub>r ((Vr K v) \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) ((Vr K v) \<diamondsuit>\<^sub>p t)) g) 
    \<le> deg R (Vr K v) X f) \<and> 
   (erH R (Vr K v) X S ((Vr K v) /\<^sub>r (vp K v)) Y 
                            (pj  (Vr K v) (vp K v))) g = g' \<and>
    (erH R (Vr K v) X S ((Vr K v) /\<^sub>r (vp K v)) Y 
                            (pj  (Vr K v) (vp K v))) h = h' \<and>
  0 < deg S ((Vr K v) /\<^sub>r ((Vr K v) \<diamondsuit>\<^sub>p t)) Y
   (erH R (Vr K v) X S ((Vr K v) /\<^sub>r ((Vr K v) \<diamondsuit>\<^sub>p t)) Y 
   (pj (Vr K v) ((Vr K v) \<diamondsuit>\<^sub>p t)) g) \<and>
  0 < deg S ((Vr K v) /\<^sub>r ((Vr K v) \<diamondsuit>\<^sub>p t)) Y
    (erH R (Vr K v) X S ((Vr K v) /\<^sub>r ((Vr K v) \<diamondsuit>\<^sub>p t)) Y 
   (pj (Vr K v) ((Vr K v) \<diamondsuit>\<^sub>p t)) h) \<and>
  rel_prime_pols S ((Vr K v) /\<^sub>r ((Vr K v) \<diamondsuit>\<^sub>p t)) Y 
    (erH R (Vr K v) X S ((Vr K v) /\<^sub>r ((Vr K v) \<diamondsuit>\<^sub>p t)) Y 
    (pj (Vr K v) ((Vr K v) \<diamondsuit>\<^sub>p t)) g) 
    (erH R (Vr K v) X S ((Vr K v) /\<^sub>r ((Vr K v) \<diamondsuit>\<^sub>p t)) Y 
    (pj (Vr K v) ((Vr K v) \<diamondsuit>\<^sub>p t)) h) \<and>
 P_mod R (Vr K v) X ((Vr K v) \<diamondsuit>\<^sub>p t) (f \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (g \<cdot>\<^sub>r\<^bsub>R\<^esub> h))" 
apply (frule Vr_ring[of v],
       frule PolynRg.subring[of R "Vr K v" X],
       frule vp_maximal [of v], frule PolynRg.is_Ring,
       frule Ring.subring_Ring[of R "Vr K v"], assumption+,
       frule Ring.residue_field_cd[of "Vr K v" "vp K v"], assumption+,
       frule Corps.field_is_ring[of "Vr K v /\<^sub>r vp K v"],
       frule pj_Hom[of "Vr K v" "vp K v"], frule vp_ideal[of "v"],
       simp add:Ring.maximal_ideal_ideal) 
apply (frule Corps.field_is_idom[of "(Vr K v) /\<^sub>r (vp K v)"],
       frule Vr_integral[of v], simp,
       frule Vr_mem_f_mem[of v t], assumption+) 
apply (frule PolynRg.erH_inv[of R "Vr K v" X "Vr K v \<diamondsuit>\<^sub>p t" S Y "g'"],
       assumption+, simp add:Ring.maximal_ideal_ideal,
       simp add:PolynRg.is_Ring, assumption+, erule bexE, erule conjE)
apply (frule PolynRg.erH_inv[of R "Vr K v" X "Vr K v \<diamondsuit>\<^sub>p t" S Y "h'"],
       assumption+, simp add:Ring.maximal_ideal_ideal,
       simp add:PolynRg.is_Ring, assumption+, erule bexE, erule conjE)
apply (rename_tac g0 h0) 
apply (subgoal_tac " g0 \<noteq> \<zero>\<^bsub>R\<^esub> \<and> h0 \<noteq> \<zero>\<^bsub>R\<^esub> \<and>
  deg R (Vr K v) X g0 \<le> 
  deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S
      (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0) \<and>
  deg R (Vr K v) X h0 + deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
      (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0) \<le> deg R (Vr K v) X f \<and>
    0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S
      (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0) \<and>
   0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S
       (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0) \<and>
   rel_prime_pols S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
      (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
             (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)
      (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
             (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0) \<and>
   P_mod R (Vr K v) X (Vr K v \<diamondsuit>\<^sub>p t) (f \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> g0 \<cdot>\<^sub>r\<^bsub>R\<^esub> h0)")
 apply (thin_tac "g' \<in> carrier S",
        thin_tac "h' \<in> carrier S",
        thin_tac "0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y g'",
        thin_tac "0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y h'",
        thin_tac "erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) f = g' \<cdot>\<^sub>r\<^bsub>S\<^esub> h'",
        thin_tac "rel_prime_pols S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y g' h'",
        thin_tac "Corps (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t))",
        thin_tac "Ring  (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t))",
        thin_tac "vp K v = Vr K v \<diamondsuit>\<^sub>p t")
apply blast 
apply (rule conjI)
 apply (thin_tac "0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y h'",
    thin_tac "erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) f = g' \<cdot>\<^sub>r\<^bsub>S\<^esub> h'",
    thin_tac "rel_prime_pols S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y g' h'",
    thin_tac "erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0 = h'",
   thin_tac "deg R (Vr K v) X h0 \<le> deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y h'")
 apply (rule contrapos_pp, simp+)
 apply (simp add:PolynRg.erH_rHom_0[of R "Vr K v" X S 
      "Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)" Y "pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)"])
 apply (rotate_tac -3, drule sym, simp add:deg_def)
  apply (drule aless_imp_le[of "0" "-\<infinity>"],
        cut_tac minf_le_any[of "0"],
        frule ale_antisym[of "0" "-\<infinity>"], simp only:ant_0[THEN sym], simp)

apply (rule conjI)
 apply (thin_tac "0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y g'",
    thin_tac "erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) f = g' \<cdot>\<^sub>r\<^bsub>S\<^esub> h'",
    thin_tac "rel_prime_pols S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y g' h'",
    thin_tac "erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0 = g'",
   thin_tac "deg R (Vr K v) X h0 \<le> deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y h'")
 apply (rule contrapos_pp, simp+, 
        simp add:PolynRg.erH_rHom_0[of R "Vr K v" X S 
      "Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)" Y "pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)"])
 apply (rotate_tac -2, drule sym, simp add:deg_def)
 apply (frule aless_imp_le[of "0" "-\<infinity>"], thin_tac "0 < - \<infinity>",
        cut_tac minf_le_any[of "0"],
        frule ale_antisym[of "0" "-\<infinity>"], simp only:ant_0[THEN sym], simp)     

apply (frule_tac x = "deg R (Vr K v) X h0" and 
       y = "deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y h'" and 
       z = "deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y g'" in aadd_le_mono)
apply (simp add:PolynRg.deg_mult_pols1[THEN sym, of S 
 "Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)" Y "h'" "g'"]) 
 apply (frule PolynRg.is_Ring[of S "Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)" Y],
        simp add:Ring.ring_tOp_commute[of S "h'" "g'"])
 apply (rotate_tac 11, drule sym)
 apply simp
apply (frule PolynRg.erH_rHom[of R "Vr K v" X S 
      "(Vr K v) /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)" Y "pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)"], 
      assumption+)
apply (frule PolynRg.pHom_dec_deg[of R "Vr K v" X S "(Vr K v) /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)" Y "erH R (Vr K v) X S ((Vr K v) /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t))
 Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t))" "f"], assumption+) 
apply (frule_tac i = "deg R (Vr K v) X h0 +
        deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y g'" in ale_trans[of _ 
        "deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
             (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) f)" "deg R (Vr K v) X f"],
       assumption+) apply simp 
apply (thin_tac "deg R (Vr K v) X h0 +
        deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y g'  \<le> deg R (Vr K v) X f",
       thin_tac "deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) f)  \<le> deg R (Vr K v) X f",
       thin_tac "0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y g'",
       thin_tac "0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y h'",
      thin_tac "deg R (Vr K v) X h0 + deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y g'
       \<le> deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
             (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) f)",
     thin_tac "rel_prime_pols S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y g' h'")
 apply (rotate_tac 12, drule sym)
 apply (drule sym) 
 apply simp
apply (frule_tac x = g0 and y = h0 in Ring.ring_tOp_closed[of "R"], 
       assumption+)
 apply (thin_tac "deg R (Vr K v) X h0 \<le> deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
  (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
             (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0)",
       thin_tac "h' = erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0",
       thin_tac "g' = erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0",
       thin_tac "deg R (Vr K v) X g0 \<le> deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
             (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)")
apply (subst PolynRg.P_mod_diff[THEN sym, of R "Vr K v" X "Vr K v \<diamondsuit>\<^sub>p t" 
       S Y f], assumption+) apply (simp add:Ring.maximal_ideal_ideal, assumption+)
apply (rotate_tac 12, drule sym)
apply (subst PolynRg.erH_mult[of R "Vr K v" X S "Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)"
        Y], assumption+)
done

lemma aadd_plus_le_plus:"\<lbrakk> a \<le> (a'::ant); b \<le> b'\<rbrakk> \<Longrightarrow> a + b \<le> a' + b'"
apply (frule aadd_le_mono[of "a" "a'" "b"])
apply (frule aadd_le_mono[of "b" "b'" "a'"])
apply (simp add:aadd_commute[of _ "a'"])
done

lemma (in Corps) Hfst_PCauchy:"\<lbrakk>valuation K v; Complete\<^bsub>v\<^esub> K; 
  PolynRg R (Vr K v) X; PolynRg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y; g0 \<in> carrier R;
  h0 \<in> carrier R; f \<in> carrier R; f \<noteq> \<zero>\<^bsub>R\<^esub>; g0 \<noteq> \<zero>\<^bsub>R\<^esub>; h0 \<noteq> \<zero>\<^bsub>R\<^esub>; 
  t \<in> carrier (Vr K v);  vp K v = Vr K v \<diamondsuit>\<^sub>p t; 
  deg R (Vr K v) X g0 \<le> deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S
       (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0);
  deg R (Vr K v) X h0 + deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S
       (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)
        \<le> deg R (Vr K v) X f;
  0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S 
       (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0);
  0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S 
       (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0);
  rel_prime_pols S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S 
         (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)
    (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y 
                                    (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0);

   erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
      (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) f =
        erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
                        (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0 \<cdot>\<^sub>r\<^bsub>S\<^esub>
        erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
                               (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0\<rbrakk> \<Longrightarrow>
      PCauchy\<^bsub> R X K v \<^esub>Hfst K v R X t S Y f g0 h0" 
(*  P_mod begin*)
apply(frule Vr_integral[of v], frule vp_ideal[of v],
       frule Vr_ring, frule pj_Hom[of "Vr K v" "vp K v"], assumption+,
       simp add:PolynRg.erH_mult[THEN sym, of R "Vr K v" X S 
          "Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)" Y "pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)" g0 h0],
       frule PolynRg.P_mod_diff[THEN sym, of R "Vr K v" X "Vr K v \<diamondsuit>\<^sub>p t" S Y
        f "g0 \<cdot>\<^sub>r\<^bsub>R\<^esub> h0"], assumption+, 
       frule PolynRg.is_Ring[of R], rule Ring.ring_tOp_closed,
       assumption+) (** P_mod done **) 
apply (simp add:pol_Cauchy_seq_def, rule conjI)
 apply (rule allI)

apply (frule_tac t = t and g = g0 and h = h0 and m = n in 
       PolynRg.P_mod_diffxxx5_2[of R "Vr K v" X _ S Y f],
       rule Vr_integral[of v], assumption+, simp add:vp_gen_nonzero,
       drule sym, simp add:vp_maximal, assumption+)

apply (subst Hfst_def)
apply (rule cart_prod_fst, assumption)
apply (rule conjI)
apply (subgoal_tac "\<forall>n. deg R (Vr K v) X (Hfst\<^bsub> K v R X t S Y f g0 h0\<^esub> n) \<le> 
                     an (deg_n R (Vr K v) X f)")
apply blast
apply (rule allI)
apply (frule Vr_integral[of v],
       frule_tac t = t and g = g0 and h = h0 and m = n in 
       PolynRg.P_mod_diffxxx5_4[of R "Vr K v" X _ S Y f], assumption+,
       simp add:vp_gen_nonzero,
       drule sym, simp add:vp_maximal, assumption+)
apply (subst PolynRg.deg_an[THEN sym], (erule conjE)+, assumption+)
apply (simp add:Hfst_def, (erule conjE)+)
apply (frule_tac i = "deg R (Vr K v) X (fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n))" and
      j = "deg R (Vr K v) X g0" and k = "deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
            (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
              (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)" in ale_trans, assumption+,
       frule PolynRg.nonzero_deg_pos[of R "Vr K v" X h0], assumption+,
       frule_tac x = 0 and y = "deg R (Vr K v) X h0" and z = "deg S 
  (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
      (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)" in aadd_le_mono, simp add:aadd_0_l) 
apply (rule allI)
apply (subgoal_tac "\<forall>n m. N < n \<and> N < m \<longrightarrow>
  P_mod R (Vr K v) X (Vr K v \<diamondsuit>\<^sub>p t\<^bsup> (Vr K v) (an N)\<^esup>)
     ( Hfst\<^bsub> K v R X t S Y f g0 h0\<^esub> n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (Hfst\<^bsub> K v R X t S Y f g0 h0\<^esub> m))")
apply blast
apply ((rule allI)+, rule impI, (erule conjE)+,
       frule Vr_integral[of v], frule vp_gen_nonzero[of v t], assumption+,
       frule vp_maximal[of v])
apply (frule_tac t = t and g = g0 and h = h0 and m = n in 
      PolynRg.P_mod_diffxxx5_2[of R "Vr K v" X _ S Y f], assumption+, simp,
      assumption+,
      frule_tac t = t and g = g0 and h = h0 and m = m in 
       PolynRg.P_mod_diffxxx5_2[of R "Vr K v" X _ S Y f], assumption+, simp,
       assumption+,
      frule_tac t = t and g = g0 and h = h0 and m = N in 
       PolynRg.P_mod_diffxxx5_2[of R "Vr K v" X _ S Y f], assumption+, simp,
       assumption+, 
      frule_tac x = "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m" in cart_prod_fst[of _ 
       "carrier R" "carrier R"],
       frule_tac x = "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N" in cart_prod_fst[of _ 
       "carrier R" "carrier R"],
      frule_tac x = "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n" in cart_prod_fst[of _ 
       "carrier R" "carrier R"],
       thin_tac "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n \<in> carrier R \<times> carrier R",
       thin_tac "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m \<in> carrier R \<times> carrier R")
apply (frule PolynRg.is_Ring)
apply (case_tac "N = 0", simp add:r_apow_def)
apply (rule_tac p = "Hfst\<^bsub> K v R X t S Y f g0 h0\<^esub> n \<plusminus>\<^bsub>R\<^esub>
               -\<^sub>a\<^bsub>R\<^esub> (Hfst\<^bsub> K v R X t S Y f g0 h0\<^esub> m)" in 
       PolynRg.P_mod_whole[of "R" "Vr K v" "X"], assumption+,
       frule Ring.ring_is_ag[of "R"], simp add:Hfst_def,
       rule aGroup.ag_pOp_closed, assumption+, rule aGroup.ag_mOp_closed, 
       assumption+)

apply (frule_tac t = t and g = g0 and h = h0 and m = N and n = "n - N" in 
       PolynRg.P_mod_diffxxx5_3[of R "Vr K v" X _ S Y f], assumption+,
       simp+, (erule conjE)+,
       frule_tac t = t and g = g0 and h = h0 and m = N and n = "m - N" in 
       PolynRg.P_mod_diffxxx5_3[of R "Vr K v" X _ S Y f], assumption+,
       simp, (erule conjE)+,
       thin_tac "P_mod R (Vr K v) X (Vr K v \<diamondsuit>\<^sub>p (t^\<^bsup>(Vr K v) N\<^esup>)) (snd 
     (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n)))",
      thin_tac "P_mod R (Vr K v) X (Vr K v \<diamondsuit>\<^sub>p (t^\<^bsup>(Vr K v) N\<^esup>)) (snd
    (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)))")
apply (frule Vr_ring[of v],
       simp only:Ring.principal_ideal_n_pow1[THEN sym],
       drule sym, simp, frule vp_ideal[of v],
       simp add:Ring.ring_pow_apow,
       frule_tac n = "an N" in vp_apow_ideal[of v], simp,
       frule Ring.ring_is_ag[of R],
       frule_tac x = "fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n)" in 
        aGroup.ag_mOp_closed[of R], assumption)
apply (frule_tac I = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and 
      p = "(fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N)) \<plusminus>\<^bsub>R\<^esub>
      -\<^sub>a\<^bsub>R\<^esub> (fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n))" in PolynRg.P_mod_minus[of R 
     "Vr K v" X], assumption+)

apply (rule aGroup.ag_pOp_closed, assumption+,
       simp add:aGroup.ag_p_inv aGroup.ag_inv_inv) 
 apply (frule Ring.ring_is_ag,
       frule_tac x = "-\<^sub>a\<^bsub>R\<^esub> fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N)" and 
       y = "fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n)" in aGroup.ag_pOp_commute) 
 apply(rule aGroup.ag_mOp_closed, assumption+, simp,
       thin_tac "-\<^sub>a\<^bsub>R\<^esub> fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N) \<plusminus>\<^bsub>R\<^esub>
       fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n) = fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n) \<plusminus>\<^bsub>R\<^esub>
       -\<^sub>a\<^bsub>R\<^esub> fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N)")
apply (frule_tac I = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and 
       p = "fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n) \<plusminus>\<^bsub>R\<^esub>
          -\<^sub>a\<^bsub>R\<^esub> fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N)" and 
       q = "fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N) \<plusminus>\<^bsub>R\<^esub>
          -\<^sub>a\<^bsub>R\<^esub> fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)" in PolynRg.P_mod_add[of 
          R "Vr K v" X], assumption+)
apply (rule aGroup.ag_pOp_closed, assumption+,
       rule aGroup.ag_mOp_closed, assumption+)
apply (rule aGroup.ag_pOp_closed, assumption+,
       rule aGroup.ag_mOp_closed, assumption+)
apply (frule_tac x = "fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N)" in 
       aGroup.ag_mOp_closed, assumption+,
       frule_tac x = "fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)" in
       aGroup.ag_mOp_closed, assumption+,
       simp add:aGroup.pOp_assocTr43[of R] aGroup.ag_l_inv1 aGroup.ag_r_zero)
apply (simp add:Hfst_def)
done

lemma (in Corps) Hsnd_PCauchy:"\<lbrakk>valuation K v; Complete\<^bsub>v\<^esub> K; 
  PolynRg R (Vr K v) X; PolynRg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y; g0 \<in> carrier R;
  h0 \<in> carrier R; f \<in> carrier R; f \<noteq> \<zero>\<^bsub>R\<^esub>; g0 \<noteq> \<zero>\<^bsub>R\<^esub>; h0 \<noteq> \<zero>\<^bsub>R\<^esub>; 
  t \<in> carrier (Vr K v);  vp K v = Vr K v \<diamondsuit>\<^sub>p t; 
  deg R (Vr K v) X g0 \<le> deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S
       (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0);
  deg R (Vr K v) X h0 + deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S
       (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)
        \<le> deg R (Vr K v) X f;
  0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S 
       (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0);
  0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S 
       (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0);
  rel_prime_pols S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S 
         (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)
    (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y 
                                    (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0);
   erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
      (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) f =
        erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
                        (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0 \<cdot>\<^sub>r\<^bsub>S\<^esub>
        erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
                               (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0\<rbrakk> \<Longrightarrow>
      PCauchy\<^bsub> R X K v \<^esub>Hsnd K v R X t S Y f g0 h0"
(*  P_mod begin*)
apply(frule Vr_integral[of v], frule vp_ideal[of v],
       frule Vr_ring, frule pj_Hom[of "Vr K v" "vp K v"], assumption+,
       simp add:PolynRg.erH_mult[THEN sym, of R "Vr K v" X S 
          "Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)" Y "pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)" g0 h0],
       frule PolynRg.P_mod_diff[THEN sym, of R "Vr K v" X "Vr K v \<diamondsuit>\<^sub>p t" S Y
        f "g0 \<cdot>\<^sub>r\<^bsub>R\<^esub> h0"], assumption+, 
       frule PolynRg.is_Ring[of R], rule Ring.ring_tOp_closed,
       assumption+) (** P_mod done **) 
apply (simp add:pol_Cauchy_seq_def, rule conjI)
 apply (rule allI)

apply (frule_tac t = t and g = g0 and h = h0 and m = n in 
       PolynRg.P_mod_diffxxx5_2[of R "Vr K v" X _ S Y f],
       rule Vr_integral[of v], assumption+, simp add:vp_gen_nonzero,
       drule sym, simp add:vp_maximal, assumption+) 

apply (subst Hsnd_def)
apply (rule cart_prod_snd, assumption)
apply (rule conjI)
apply (subgoal_tac "\<forall>n. deg R (Vr K v) X (Hsnd\<^bsub> K v R X t S Y f g0 h0\<^esub> n) \<le> 
                     an (deg_n R (Vr K v) X f)")
apply blast
apply (rule allI)
apply (frule Vr_integral[of v],
       frule_tac t = t and g = g0 and h = h0 and m = n in 
       PolynRg.P_mod_diffxxx5_4[of R "Vr K v" X _ S Y f], assumption+,
       simp add:vp_gen_nonzero,
       drule sym, simp add:vp_maximal, assumption+)
apply (subst PolynRg.deg_an[THEN sym], (erule conjE)+, assumption+)

apply (simp add:Hsnd_def)
apply (rule allI)
apply (subgoal_tac "\<forall>n m. N < n \<and> N < m \<longrightarrow>
  P_mod R (Vr K v) X (Vr K v \<diamondsuit>\<^sub>p t\<^bsup> (Vr K v) (an N)\<^esup>)
     ( Hsnd\<^bsub> K v R X t S Y f g0 h0\<^esub> n \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (Hsnd\<^bsub> K v R X t S Y f g0 h0\<^esub> m))")
apply blast
apply ((rule allI)+, rule impI, (erule conjE)+)
apply (frule Vr_integral[of v], frule vp_gen_nonzero[of v t], assumption+)
apply (frule vp_maximal[of v])
apply (frule_tac t = t and g = g0 and h = h0 and m = n in 
      PolynRg.P_mod_diffxxx5_2[of R "Vr K v" X _ S Y f], assumption+, simp,
      assumption+) 
apply (frule_tac t = t and g = g0 and h = h0 and m = m in 
       PolynRg.P_mod_diffxxx5_2[of R "Vr K v" X _ S Y f], assumption+, simp,
       assumption+,
      frule_tac t = t and g = g0 and h = h0 and m = N in 
       PolynRg.P_mod_diffxxx5_2[of R "Vr K v" X _ S Y f], assumption+, simp,
       assumption+, 
      frule_tac x = "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m" in cart_prod_snd[of _ 
       "carrier R" "carrier R"],
       frule_tac x = "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N" in cart_prod_snd[of _ 
       "carrier R" "carrier R"],
      frule_tac x = "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n" in cart_prod_snd[of _ 
       "carrier R" "carrier R"],
       thin_tac "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n \<in> carrier R \<times> carrier R",
       thin_tac "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m \<in> carrier R \<times> carrier R")
apply (frule PolynRg.is_Ring)
apply (case_tac "N = 0", simp add:r_apow_def)
apply (rule_tac p = "Hsnd\<^bsub> K v R X t S Y f g0 h0\<^esub> n \<plusminus>\<^bsub>R\<^esub>
               -\<^sub>a\<^bsub>R\<^esub> (Hsnd\<^bsub> K v R X t S Y f g0 h0\<^esub> m)" in 
       PolynRg.P_mod_whole[of "R" "Vr K v" "X"], assumption+,
       frule Ring.ring_is_ag[of "R"], simp add:Hsnd_def,
       rule aGroup.ag_pOp_closed, assumption+, rule aGroup.ag_mOp_closed, 
       assumption+)

apply (frule_tac t = t and g = g0 and h = h0 and m = N and n = "n - N" in 
       PolynRg.P_mod_diffxxx5_3[of R "Vr K v" X _ S Y f], assumption+)
apply simp+
apply (erule conjE)+
apply (frule_tac t = t and g = g0 and h = h0 and m = N and n = "m - N" in 
       PolynRg.P_mod_diffxxx5_3[of R "Vr K v" X _ S Y f], assumption+)
apply simp apply (erule conjE)+
apply (thin_tac "P_mod R (Vr K v) X (Vr K v \<diamondsuit>\<^sub>p (t^\<^bsup>(Vr K v) N\<^esup>)) (fst 
    (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n)))",
      thin_tac "P_mod R (Vr K v) X (Vr K v \<diamondsuit>\<^sub>p (t^\<^bsup>(Vr K v) N\<^esup>)) (fst 
    (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)))")
apply (frule Vr_ring[of v])
apply (simp only:Ring.principal_ideal_n_pow1[THEN sym])
apply (drule sym, simp, frule vp_ideal[of v])
apply (simp add:Ring.ring_pow_apow,
      frule_tac n = "an N" in vp_apow_ideal[of v], simp,
      frule Ring.ring_is_ag[of R],
      frule_tac x = "snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n)" in 
        aGroup.ag_mOp_closed[of R], assumption)
apply (frule_tac I = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and 
      p = "(snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N)) \<plusminus>\<^bsub>R\<^esub>
      -\<^sub>a\<^bsub>R\<^esub> (snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n))" in PolynRg.P_mod_minus[of R 
     "Vr K v" X], assumption+)

apply (rule aGroup.ag_pOp_closed, assumption+,
       simp add:aGroup.ag_p_inv aGroup.ag_inv_inv) 
 apply (frule Ring.ring_is_ag,
       frule_tac x = "-\<^sub>a\<^bsub>R\<^esub> snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N)" and 
       y = "snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n)" in aGroup.ag_pOp_commute) 
 apply(rule aGroup.ag_mOp_closed, assumption+, simp,
       thin_tac "-\<^sub>a\<^bsub>R\<^esub> snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N) \<plusminus>\<^bsub>R\<^esub>
       snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n) = snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n) \<plusminus>\<^bsub>R\<^esub>
       -\<^sub>a\<^bsub>R\<^esub> snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N)")
apply (frule_tac I = "vp K v\<^bsup> (Vr K v) (an N)\<^esup>" and 
       p = "snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n) \<plusminus>\<^bsub>R\<^esub>
          -\<^sub>a\<^bsub>R\<^esub> snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N)" and 
       q = "snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N) \<plusminus>\<^bsub>R\<^esub>
          -\<^sub>a\<^bsub>R\<^esub> snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)" in PolynRg.P_mod_add[of 
          R "Vr K v" X], assumption+)
apply (rule aGroup.ag_pOp_closed, assumption+,
       rule aGroup.ag_mOp_closed, assumption+)
apply (rule aGroup.ag_pOp_closed, assumption+,
       rule aGroup.ag_mOp_closed, assumption+)
apply (frule_tac x = "snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> N)" in 
       aGroup.ag_mOp_closed, assumption+,
       frule_tac x = "snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)" in
       aGroup.ag_mOp_closed, assumption+,
       simp add:aGroup.pOp_assocTr43[of R] aGroup.ag_l_inv1 aGroup.ag_r_zero)
apply (simp add:Hsnd_def)
done

lemma (in Corps) H_Plimit_f:"\<lbrakk>valuation K v; Complete\<^bsub>v\<^esub> K;
     t \<in> carrier (Vr K v); vp K v = Vr K v \<diamondsuit>\<^sub>p t;
     PolynRg R (Vr K v) X; PolynRg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y;
     f \<in> carrier R; f \<noteq> \<zero>\<^bsub>R\<^esub>; g0 \<in> carrier R; h0 \<in> carrier R; g0 \<noteq> \<zero>\<^bsub>R\<^esub>; 
     h0 \<noteq> \<zero>\<^bsub>R\<^esub>; 
     0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
             (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
               (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0);
     0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
             (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
               (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0);
     deg R (Vr K v) X h0 +
        deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)  \<le> deg R (Vr K v) X f;
       
     rel_prime_pols S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
                      (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)
         (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
                       (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0);
      
     erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) f =
      erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0 \<cdot>\<^sub>r\<^bsub>S\<^esub>
        erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0;
      
        deg R (Vr K v) X g0
        \<le> deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
             (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0);
      
      g \<in> carrier R; h \<in> carrier R;
        Plimit\<^bsub> R X K v \<^esub>(Hfst K v R X t S Y f g0 h0) g; 
        Plimit\<^bsub> R X K v \<^esub>(Hsnd K v R X t S Y f g0 h0) h;
        Plimit\<^bsub> R X K v \<^esub>(\<lambda>n. (Hfst\<^bsub> K v R X t S Y f g0 h0\<^esub> n) \<cdot>\<^sub>r\<^bsub>R\<^esub>
                            (Hsnd\<^bsub> K v R X t S Y f g0 h0\<^esub> n)) (g \<cdot>\<^sub>r\<^bsub>R\<^esub> h)\<rbrakk>
       \<Longrightarrow> Plimit\<^bsub> R X K v \<^esub>(\<lambda>n. (Hfst\<^bsub> K v R X t S Y f g0 h0\<^esub> n) \<cdot>\<^sub>r\<^bsub>R\<^esub>
                              (Hsnd\<^bsub> K v R X t S Y f g0 h0\<^esub> n)) f"
apply(frule Vr_integral[of v], frule vp_ideal[of v],
       frule Vr_ring, frule pj_Hom[of "Vr K v" "vp K v"], assumption+,
       simp add:PolynRg.erH_mult[THEN sym, of R "Vr K v" X S 
          "Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)" Y "pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)" g0 h0])
apply(frule PolynRg.P_mod_diff[of R "Vr K v" X "Vr K v \<diamondsuit>\<^sub>p t" S Y
        f "g0 \<cdot>\<^sub>r\<^bsub>R\<^esub> h0"], assumption+, 
       frule PolynRg.is_Ring[of R], rule Ring.ring_tOp_closed,
       assumption+, simp) (** P_mod done **)
apply (simp add:PolynRg.erH_mult[of R "Vr K v" X S 
          "Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)" Y "pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)" g0 h0])
apply (frule PolynRg.is_Ring[of R]) 
apply (frule Hfst_PCauchy[of v R X S t Y g0 h0 f], assumption+, 
       frule Hsnd_PCauchy[of v R X S t Y g0 h0 f], assumption+) 
apply (subst pol_limit_def)
apply (rule conjI)
 apply (rule allI) 
 apply (rule Ring.ring_tOp_closed, assumption)
 apply (simp add:pol_Cauchy_seq_def, simp add:pol_Cauchy_seq_def) 
 apply (rule allI)
 apply (subgoal_tac "\<forall>m>N. P_mod R (Vr K v) X (vp K v\<^bsup> (Vr K v) (an N)\<^esup>)
                   ((Hfst\<^bsub> K v R X t S Y f g0 h0\<^esub> m) \<cdot>\<^sub>r\<^bsub>R\<^esub> (Hsnd\<^bsub> K v R X t S Y f g0 h0\<^esub> m)
                       \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> f)")
apply blast

apply (rule allI, rule impI, frule Vr_integral[of v])
apply (frule_tac t = t and g = g0 and h = h0 and m = "m - Suc 0" in 
       PolynRg.P_mod_diffxxx5_1[of R "Vr K v" X _ S Y], assumption+,
       simp add:vp_gen_nonzero[of v],
       frule vp_maximal[of v], simp, assumption+)
apply ((erule conjE)+, simp del:npow_suc Hpr_Suc)
apply (frule Ring.ring_is_ag[of "R"])
apply (thin_tac "0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
       (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
               (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)",
       thin_tac "0 < deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
             (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
               (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0)",
       thin_tac "rel_prime_pols S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)
         (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0)",
       thin_tac "P_mod R (Vr K v) X (Vr K v \<diamondsuit>\<^sub>p t) ( f \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> g0 \<cdot>\<^sub>r\<^bsub>R\<^esub> h0)",
       thin_tac "erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) f = 
         (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0) \<cdot>\<^sub>r\<^bsub>S\<^esub>
         (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0)",
       thin_tac "deg R (Vr K v) X g0  \<le> deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
             (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)",
       thin_tac "deg R (Vr K v) X h0 +  deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)  \<le> deg R (Vr K v) X f",
        thin_tac "erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) (fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)) =
        erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0",
       thin_tac "erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) (snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)) =
        erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0",
       thin_tac "deg R (Vr K v) X (fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m))
        \<le> deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
             (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)",
       thin_tac "P_mod R (Vr K v) X (Vr K v \<diamondsuit>\<^sub>p (t^\<^bsup>(Vr K v) m\<^esup>))
        ( fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> (m - Suc 0)) \<plusminus>\<^bsub>R\<^esub>
             -\<^sub>a\<^bsub>R\<^esub> (fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)))",
       thin_tac "deg R (Vr K v) X (snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)) +
        deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
           (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0) \<le> deg R (Vr K v) X f",
       thin_tac "P_mod R (Vr K v) X (Vr K v \<diamondsuit>\<^sub>p (t^\<^bsup>(Vr K v) m\<^esup>))
         (snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> (m - Suc 0)) \<plusminus>\<^bsub>R\<^esub>
             -\<^sub>a\<^bsub>R\<^esub> (snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)))")
apply (case_tac "N = 0", simp add:r_apow_def)
apply (rule_tac p = "(Hfst\<^bsub> K v R X t S Y f g0 h0\<^esub> m) \<cdot>\<^sub>r\<^bsub>R\<^esub> (Hsnd\<^bsub> K v R X t S Y f g0 h0\<^esub> m)
               \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> f" in PolynRg.P_mod_whole[of R "Vr K v" X], assumption+)
apply (simp add:Hfst_def Hsnd_def)
apply (frule_tac x = "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m" in cart_prod_fst[of _ "carrier R" "carrier R"]) 
apply (frule_tac x = "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m" in cart_prod_snd[of _ 
       "carrier R" "carrier R"])
apply (frule Ring.ring_is_ag[of R],
       rule aGroup.ag_pOp_closed, assumption)
 apply (rule Ring.ring_tOp_closed, assumption+) 
 apply (rule aGroup.ag_mOp_closed, assumption+)

apply (frule_tac g = "f \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)) \<cdot>\<^sub>r\<^bsub>R\<^esub>
       (snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m))" and m = "N - Suc 0" and n = m in
       PolynRg.P_mod_n_m[of "R" "Vr K v" "X"], assumption+)
apply (frule_tac x = "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m" in cart_prod_fst[of _ "carrier R" "carrier R"],
       frule_tac x = "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m" in cart_prod_snd[of _ "carrier R" "carrier R"]) 

apply (rule aGroup.ag_pOp_closed, assumption+, rule aGroup.ag_mOp_closed, 
       assumption)
apply (rule Ring.ring_tOp_closed, assumption+)
apply (subst Suc_le_mono[THEN sym], simp)
apply assumption
apply (simp del:npow_suc)
apply (simp only:Ring.principal_ideal_n_pow1[THEN sym, of "Vr K v"])
apply (cut_tac n = N in an_neq_inf)
apply (subgoal_tac "an N \<noteq> 0") 
apply (subst r_apow_def, simp) apply (simp add:na_an)
apply (frule Ring.principal_ideal[of "Vr K v" t], assumption)
apply (frule_tac I = "Vr K v \<diamondsuit>\<^sub>p t" and n = N in Ring.ideal_pow_ideal[of "Vr K v"], assumption+)
apply (frule_tac x = "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m" in cart_prod_fst[of _ "carrier R" "carrier R"],
       frule_tac x = "Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m" in cart_prod_snd[of _ "carrier R" "carrier R"])

apply (thin_tac "PCauchy\<^bsub> R X K v \<^esub>Hfst K v R X t S Y f g0 h0",
       thin_tac "PCauchy\<^bsub> R X K v \<^esub>Hsnd K v R X t S Y f g0 h0")
apply (simp add:Hfst_def Hsnd_def)
apply (frule_tac x = "fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)" and y = "snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)" in Ring.ring_tOp_closed[of "R"],  assumption+)

apply (frule_tac  x = "(fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)) \<cdot>\<^sub>r\<^bsub>R\<^esub> (snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m))" in aGroup.ag_mOp_closed[of "R"], assumption+)
apply (frule_tac I = "Vr K v \<diamondsuit>\<^sub>p t \<^bsup>\<diamondsuit>(Vr K v) N\<^esup>" and 
       p = "f \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m)) \<cdot>\<^sub>r\<^bsub>R\<^esub> 
        (snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> m))" in 
       PolynRg.P_mod_minus[of R "Vr K v" X], assumption+)
apply (frule Ring.ring_is_ag[of "R"])
apply (rule aGroup.ag_pOp_closed, assumption+)
apply (simp add:aGroup.ag_p_inv, simp add:aGroup.ag_inv_inv,
       frule aGroup.ag_mOp_closed[of "R" "f"], assumption+)
apply (simp add:aGroup.ag_pOp_commute[of "R" "-\<^sub>a\<^bsub>R\<^esub> f"])
apply (subst an_0[THEN sym])
apply (subst aneq_natneq[of _ "0"], thin_tac "an N \<noteq> \<infinity>", simp) 
done

theorem (in Corps) Hensel:"\<lbrakk>valuation K v; Complete\<^bsub>v\<^esub> K; 
    PolynRg R (Vr K v) X; PolynRg S ((Vr K v) /\<^sub>r (vp K v)) Y;
    f \<in> carrier R; f \<noteq> \<zero>\<^bsub>R\<^esub>; g' \<in> carrier S; h' \<in> carrier S;  
    0 < deg S ((Vr K v) /\<^sub>r (vp K v)) Y g';
    0 < deg S ((Vr K v) /\<^sub>r (vp K v)) Y h';
    ((erH R (Vr K v) X S ((Vr K v) /\<^sub>r (vp K v)) Y 
             (pj  (Vr K v) (vp K v))) f) =  g' \<cdot>\<^sub>r\<^bsub>S\<^esub> h';
    rel_prime_pols S ((Vr K v) /\<^sub>r (vp K v)) Y g' h'\<rbrakk> \<Longrightarrow>
  \<exists>g h. g \<in> carrier R \<and> h \<in> carrier R \<and> 
        deg R (Vr K v) X g \<le> deg S ((Vr K v) /\<^sub>r (vp K v)) Y g' \<and>
                  f = g \<cdot>\<^sub>r\<^bsub>R\<^esub> h"
apply (frule PolynRg.is_Ring[of R "Vr K v" X],
       frule PolynRg.is_Ring[of S "Vr K v /\<^sub>r vp K v" Y],
       frule vp_gen_t[of v], erule bexE,
       frule_tac t = t in vp_gen_nonzero[of v], assumption)
apply (frule_tac t = t in Hensel_starter[of v R X S Y _ f g' h'], assumption+) 
apply ((erule exE)+, (erule conjE)+, rename_tac  g0 h0)
apply (frule Vr_ring[of v], frule Vr_integral[of v])
apply (rotate_tac 22, drule sym, drule sym, simp)
apply (frule vp_maximal[of v], simp)
apply (frule_tac mx = "Vr K v \<diamondsuit>\<^sub>p t" in Ring.residue_field_cd[of "Vr K v"],
                 assumption)
apply (frule_tac mx = "Vr K v \<diamondsuit>\<^sub>p t" in  Ring.maximal_ideal_ideal[of "Vr K v"],
          assumption)
apply (frule_tac I = "Vr K v \<diamondsuit>\<^sub>p t" in Ring.qring_ring[of "Vr K v"], 
       assumption+)
apply (frule_tac B = "Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)" and h = "pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)" in PolynRg.erH_rHom[of R "Vr K v" X S _ Y], assumption+)
 apply (simp add:pj_Hom) 
apply (frule_tac ?g0.0 = g0 and ?h0.0 = h0 in Hfst_PCauchy[of v R X S _ Y _ _ 
       f], assumption+)
apply (frule_tac ?g0.0 = g0 and ?h0.0 = h0 in Hsnd_PCauchy[of v R X S _ Y _ _ 
       f], assumption+)
apply (frule_tac F = "\<lambda>j. Hfst\<^bsub>K v R X t S Y f g0 h0\<^esub> j" in PCauchy_Plimit[of v R X]
      , assumption+)
apply (frule_tac F = "\<lambda>j. Hsnd\<^bsub>K v R X t S Y f g0 h0\<^esub> j" in PCauchy_Plimit[of v R X]
, assumption+)
apply ((erule bexE)+, rename_tac g0 h0 g h) 

apply (frule_tac F = "\<lambda>j. Hfst\<^bsub>K v R X t S Y f g0 h0\<^esub> j" and 
        G = "\<lambda>j. Hsnd\<^bsub>K v R X t S Y f g0 h0\<^esub> j" and ?p1.0 = g and ?p2.0 = h 
       in P_limit_mult[of v R X], assumption+, rule allI)

apply (simp add:pol_Cauchy_seq_def) 
apply (simp add:pol_Cauchy_seq_def, assumption+)
apply (frule_tac t = t and ?g0.0 = g0 and ?h0.0 = h0 and g = g and h = h in 
       H_Plimit_f[of v _ R X S Y f], assumption+) 
apply (frule_tac F = "\<lambda>n. (Hfst\<^bsub> K v R X t S Y f g0 h0\<^esub> n) \<cdot>\<^sub>r\<^bsub>R\<^esub> (Hsnd\<^bsub> K v R X t S Y f g0 h0\<^esub> n)" and ?p1.0 = "g \<cdot>\<^sub>r\<^bsub>R\<^esub> h" and d = "na (deg R (Vr K v) X g0 + deg R (Vr K v) X f)" in  P_limit_unique[of v R X _ _  _ f], assumption+)
apply (rule allI)
 apply (frule PolynRg.is_Ring[of R],
        rule Ring.ring_tOp_closed, assumption)
 apply (simp add:pol_Cauchy_seq_def)
 apply (simp add:pol_Cauchy_seq_def)
 apply (rule allI)
apply (thin_tac "Plimit\<^bsub> R X K v \<^esub>(Hfst K v R X t S Y f g0 h0) g",
       thin_tac "Plimit\<^bsub> R X K v \<^esub>(Hsnd K v R X t S Y f g0 h0) h",
       thin_tac "Plimit\<^bsub> R X K v \<^esub>(\<lambda>n. (Hfst\<^bsub> K v R X t S Y f g0 h0\<^esub> n) \<cdot>\<^sub>r\<^bsub>R\<^esub>
                             (Hsnd\<^bsub> K v R X t S Y f g0 h0\<^esub> n)) (g \<cdot>\<^sub>r\<^bsub>R\<^esub> h)",
       thin_tac "Plimit\<^bsub> R X K v \<^esub>(\<lambda>n. (Hfst\<^bsub> K v R X t S Y f g0 h0\<^esub> n) \<cdot>\<^sub>r\<^bsub>R\<^esub>
                             (Hsnd\<^bsub> K v R X t S Y f g0 h0\<^esub> n)) f")
apply (subst PolynRg.deg_mult_pols1[of R "Vr K v" X], assumption+)

 apply (simp add:pol_Cauchy_seq_def, simp add:pol_Cauchy_seq_def,
        thin_tac "g' = erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0",
        thin_tac "h' = erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
         (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) h0")
apply (subst PolynRg.deg_mult_pols1[THEN sym, of R "Vr K v" X], assumption+)
apply (simp add:pol_Cauchy_seq_def, simp add:pol_Cauchy_seq_def)

apply (frule_tac p1 = g0 in PolynRg.deg_mult_pols1[THEN sym, of R "Vr K v" X _         f], assumption+, simp)
apply (frule_tac x = g0 in Ring.ring_tOp_closed[of R _ f], assumption+)
apply (frule_tac p = "g0 \<cdot>\<^sub>r\<^bsub>R\<^esub> f" in PolynRg.nonzero_deg_pos[of R "Vr K v" X],
          assumption+)
apply (frule_tac p = "g0 \<cdot>\<^sub>r\<^bsub>R\<^esub> f" in PolynRg.deg_in_aug_minf[of R "Vr K v" X], 
       assumption+, simp add:aug_minf_def,
       simp add:PolynRg.polyn_ring_integral[of R "Vr K v" X],
       simp add:Idomain.idom_tOp_nonzeros[of R _ f],
       frule_tac p = "g0 \<cdot>\<^sub>r\<^bsub>R\<^esub> f" in PolynRg.deg_noninf[of R "Vr K v" X],
       assumption+)       
apply (simp add:an_na)
apply (subst PolynRg.deg_mult_pols1[of "R" "Vr K v" "X"], assumption+,
       simp add:pol_Cauchy_seq_def, simp add:pol_Cauchy_seq_def)
apply (frule_tac  t = t and g = g0 and h = h0 and m = n in 
       PolynRg.P_mod_diffxxx5_4[of R "Vr K v" X _ S Y f], assumption+)
apply (erule conjE)

apply (frule_tac a = "deg R (Vr K v) X (fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n))" and a' = "deg R (Vr K v) X g0" and b = "deg R (Vr K v) X (snd (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n))" and b' = "deg R (Vr K v) X f" in aadd_plus_le_plus, assumption+)
 apply simp
apply (simp add:Hfst_def Hsnd_def)

apply (rule Ring.ring_tOp_closed, assumption+)
 apply (rotate_tac -1, drule sym)
apply (frule_tac F = "\<lambda>j. Hfst\<^bsub>K v R X t S Y f g0 h0\<^esub> j" and p = g and ad = "deg S
 (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y 
  (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)" in Plimit_deg1[of v R X], assumption+,
  simp add:pol_Cauchy_seq_def) 
apply (rule allI)
apply (frule_tac  t = t and g = g0 and h = h0 and m = n in 
      PolynRg.P_mod_diffxxx5_4[of R "Vr K v" X _ S Y f], assumption+,
      erule conjE)
apply (frule_tac i = "deg R (Vr K v) X (fst (Hpr\<^bsub> R (Vr K v) X t S Y f g0 h0\<^esub> n))" and
 j = "deg R (Vr K v) X g0" and k = "deg S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
      (erH R (Vr K v) X S (Vr K v /\<^sub>r (Vr K v \<diamondsuit>\<^sub>p t)) Y
               (pj (Vr K v) (Vr K v \<diamondsuit>\<^sub>p t)) g0)" in ale_trans, assumption+)
 apply (subst Hfst_def, assumption+, blast)
done

end
