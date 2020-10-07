(**       Algebra5  
                            author Hidetsune Kobayashi
                            Group You Santo
                            Department of Mathematics
                            Nihon University
                            h_coba@math.cst.nihon-u.ac.jp
                            May 3, 2004.
                            April 6, 2007 (revised).

  chapter 4.  Ring theory (continued)
    section 6.   operation of ideals
    section 7.   direct product1, general case
    section 8.   Chinese remainder theorem
    section 9.   addition of finite elements of a ring and ideal_multiplication
    section 10.  extension and contraction
    section 11.  complete system of representatives
    section 12.  Polynomial ring 
    section 13.  addition and multiplication of polyn_exprs
    section 14.  the degree of a polynomial
   **)

theory Algebra5 imports Algebra4 begin

section "Operation of ideals"

lemma (in Ring) ideal_sumTr1:"\<lbrakk>ideal R A; ideal R B\<rbrakk> \<Longrightarrow> 
          A \<minusplus> B = \<Inter> {J. ideal R J \<and> (A \<union> B) \<subseteq> J}"
apply (frule sum_ideals[of "A" "B"], assumption,
       frule sum_ideals_la1[of "A" "B"], assumption,
       frule sum_ideals_la2[of "A" "B"], assumption)
apply (rule equalityI)
  (* A \<minusplus>\<^sub>R B \<subseteq> \<Inter>{J. ideal R J \<and> A \<union> B \<subseteq> J} *)

apply (rule_tac A = "{J. ideal R J \<and> (A \<union> B) \<subseteq> J}" and C = "A \<minusplus> B" in
                Inter_greatest)
 apply (simp, (erule conjE)+)
 apply (rule_tac A = A and B = B and I = X in sum_ideals_cont,
        simp add:ideal_subset1, simp add:ideal_subset1, assumption+)
apply (rule_tac B = "A \<minusplus> B" and A = "{J. ideal R J \<and> (A \<union> B) \<subseteq> J}" in
         Inter_lower)
 apply simp
done

lemma (in Ring) sum_ideals_commute:"\<lbrakk>ideal R A; ideal R B\<rbrakk> \<Longrightarrow>   
                       A \<minusplus> B = B \<minusplus> A"
apply (frule ideal_sumTr1 [of "B"], assumption+,
       frule ideal_sumTr1 [of "A" "B"], assumption+)
apply (simp add:Un_commute[of "B" "A"])
done

lemma (in Ring) ideal_prod_mono1:"\<lbrakk>ideal R A; ideal R B; ideal R C;
                A \<subseteq> B \<rbrakk> \<Longrightarrow> A \<diamondsuit>\<^sub>r C \<subseteq> B \<diamondsuit>\<^sub>r C"
apply (frule ideal_prod_ideal[of "B" "C"], assumption+)
apply (rule ideal_prod_subTr[of "A" "C" "B \<diamondsuit>\<^sub>r C"], assumption+)
 apply (rule ballI)+
 apply (frule_tac c = i in subsetD[of "A" "B"], assumption+)
 apply (rule_tac i = i and j = j in prod_mem_prod_ideals[of "B" "C"],
                 assumption+)
done

lemma (in Ring) ideal_prod_mono2:"\<lbrakk>ideal R A; ideal R B; ideal R C;
                A \<subseteq> B \<rbrakk> \<Longrightarrow> C \<diamondsuit>\<^sub>r A \<subseteq> C \<diamondsuit>\<^sub>r B"
apply (frule ideal_prod_mono1[of "A" "B" "C"], assumption+)
apply (simp add:ideal_prod_commute)
done

lemma (in Ring) cont_ideal_prod:"\<lbrakk>ideal R A; ideal R B; ideal R C;
        A \<subseteq> C; B \<subseteq> C \<rbrakk> \<Longrightarrow> A \<diamondsuit>\<^sub>r B \<subseteq> C"
apply (simp add:ideal_prod_def)
apply (rule subsetI, simp)
 apply (frule ideal_prod_ideal[of "A" "B"], assumption,
        frule_tac a = "A \<diamondsuit>\<^sub>r B" in forall_spec,
   thin_tac "\<forall>xa. ideal R xa \<and> {x. \<exists>i\<in>A. \<exists>j\<in>B. x = i \<cdot>\<^sub>r j} \<subseteq> xa \<longrightarrow> x \<in> xa",
   simp)
 apply (rule subsetI, simp, (erule bexE)+, simp add:prod_mem_prod_ideals)
 apply (frule ideal_prod_la1[of "A" "B"], assumption,
        frule_tac c = x in subsetD[of "A \<diamondsuit>\<^sub>r B" "A"], assumption+,
        simp add:subsetD)
done

lemma (in Ring) ideal_distrib:"\<lbrakk>ideal R A; ideal R B; ideal R C\<rbrakk> \<Longrightarrow>
             A \<diamondsuit>\<^sub>r (B \<minusplus> C) =  A \<diamondsuit>\<^sub>r B \<minusplus>  A \<diamondsuit>\<^sub>r C"
apply (frule sum_ideals[of "B" "C"], assumption,
       frule ideal_prod_ideal[of "A" "B \<minusplus> C"], assumption+,
       frule ideal_prod_ideal[of "A" "B"], assumption+,
       frule ideal_prod_ideal[of "A" "C"], assumption+,
       frule sum_ideals[of "A \<diamondsuit>\<^sub>r B" "A \<diamondsuit>\<^sub>r C"], assumption)
apply (rule equalityI)
 apply (rule ideal_prod_subTr[of "A" "B \<minusplus> C" "A \<diamondsuit>\<^sub>r B \<minusplus> A \<diamondsuit>\<^sub>r C"], assumption+)
 apply (rule ballI)+
 apply (frule_tac x = j in ideals_set_sum[of B C], assumption+,
        (erule bexE)+, simp) apply (
        thin_tac "j = h \<plusminus> k",
        frule_tac h = i in ideal_subset[of "A"], assumption+,
        frule_tac h = h in ideal_subset[of "B"], assumption+,
        frule_tac h = k in ideal_subset[of "C"], assumption+)
 apply (simp add:ring_distrib1)
 apply (frule_tac i = i and j = h in prod_mem_prod_ideals[of "A" "B"],
         assumption+,
        frule_tac i = i and j = k in prod_mem_prod_ideals[of "A" "C"],
         assumption+)
 apply (frule sum_ideals_la1[of "A \<diamondsuit>\<^sub>r B" "A \<diamondsuit>\<^sub>r C"], assumption+,
        frule sum_ideals_la2[of "A \<diamondsuit>\<^sub>r B" "A \<diamondsuit>\<^sub>r C"], assumption+)
 apply (frule_tac c = "i \<cdot>\<^sub>r h" in subsetD[of "A \<diamondsuit>\<^sub>r B" "A \<diamondsuit>\<^sub>r B \<minusplus> A \<diamondsuit>\<^sub>r C"], 
                                assumption+,
        frule_tac c = "i \<cdot>\<^sub>r k" in subsetD[of "A \<diamondsuit>\<^sub>r C" "A \<diamondsuit>\<^sub>r B \<minusplus> A \<diamondsuit>\<^sub>r C"], 
                                assumption+)
 apply (simp add:ideal_pOp_closed) 
 apply (rule sum_ideals_cont[of "A \<diamondsuit>\<^sub>r (B \<minusplus> C)" "A \<diamondsuit>\<^sub>r B" "A \<diamondsuit>\<^sub>r C" ],
          assumption+) 
 apply (rule ideal_prod_subTr[of "A" "B" "A \<diamondsuit>\<^sub>r (B \<minusplus> C)"], assumption+)
  apply (rule ballI)+
  apply (frule sum_ideals_la1[of "B" "C"], assumption+,
         frule_tac c = j in subsetD[of "B" "B \<minusplus> C"], assumption+,
         rule_tac i = i and j = j in prod_mem_prod_ideals[of "A" "B \<minusplus> C"],
         assumption+)

  apply (rule ideal_prod_subTr[of "A" "C" "A \<diamondsuit>\<^sub>r (B \<minusplus> C)"], assumption+)
  apply (rule ballI)+
  apply (frule sum_ideals_la2[of "B" "C"], assumption+,
         frule_tac c = j in subsetD[of "C" "B \<minusplus> C"], assumption+,
         rule_tac i = i and j = j in prod_mem_prod_ideals[of "A" "B \<minusplus> C"],
         assumption+)
done

definition
  coprime_ideals::"[_, 'a set, 'a set] \<Rightarrow> bool" where
  "coprime_ideals R A B \<longleftrightarrow> A \<minusplus>\<^bsub>R\<^esub> B = carrier R"

lemma (in Ring) coprimeTr:"\<lbrakk>ideal R A; ideal R B\<rbrakk> \<Longrightarrow>
                coprime_ideals R A B = (\<exists>a \<in> A. \<exists>b \<in> B. a \<plusminus> b = 1\<^sub>r)"
apply (rule iffI)
 apply (simp add:coprime_ideals_def) 
 apply (cut_tac ring_one, frule sym, thin_tac "A \<minusplus> B = carrier R", simp,
        thin_tac "carrier R = A \<minusplus> B", frule ideals_set_sum[of A B],
        assumption+, (erule bexE)+, frule sym, blast)

apply (erule bexE)+
 apply (frule ideal_subset1[of A], frule ideal_subset1[of B]) 
 apply (frule_tac a = a and b = b in set_sum_mem[of _ A _ B], assumption+)
 apply (simp add:coprime_ideals_def)
 apply (frule sum_ideals[of "A" "B"], assumption+,
        frule ideal_inc_one[of "A \<minusplus> B"], assumption)
 apply (simp add:coprime_ideals_def)
done

lemma (in Ring) coprime_int_prod:"\<lbrakk>ideal R A; ideal R B; coprime_ideals R A B\<rbrakk>
       \<Longrightarrow>   A \<inter> B = A \<diamondsuit>\<^sub>r B"
apply (frule ideal_prod_la1[of "A" "B"], assumption+,
       frule ideal_prod_la2[of "A" "B"], assumption+) 
apply (rule equalityI) 
defer
 (**  A \<diamondsuit>\<^bsub>R\<^esub> B \<subseteq> A \<inter> B **)
 apply simp
 apply (simp add:coprime_ideals_def)
 apply (frule int_ideal[of "A" "B"], assumption)
 apply (frule idealprod_whole_r[of "A \<inter> B"])
 apply (frule sym, thin_tac "A \<minusplus> B = carrier R", simp)
 apply (simp add:ideal_distrib)
 apply (simp add:ideal_prod_commute[of "A \<inter> B" "A"])
 apply (cut_tac Int_lower1[of "A" "B"], cut_tac Int_lower2[of "A" "B"])
 apply (frule ideal_prod_mono2[of "A \<inter> B" "B" "A"], assumption+,  
        frule ideal_prod_mono1[of "A \<inter> B" "A" "B"], assumption+)
 apply (frule ideal_prod_ideal[of "A \<inter> B" "B"], assumption+,
        frule ideal_prod_ideal[of "A" "A \<inter> B"], assumption+,
        frule ideal_subset1[of "A \<diamondsuit>\<^sub>r (A \<inter> B)"],
        frule ideal_subset1[of "(A \<inter> B) \<diamondsuit>\<^sub>r B"])
 apply (frule ideal_prod_ideal[of A B], assumption+,
        frule sum_ideals_cont[of "A \<diamondsuit>\<^sub>r B" "A \<diamondsuit>\<^sub>r (A \<inter> B)" "(A \<inter> B) \<diamondsuit>\<^sub>r B"],
        assumption+) 
 apply simp
done

lemma (in Ring) coprime_elems:"\<lbrakk>ideal R A; ideal R B; coprime_ideals R A B\<rbrakk> \<Longrightarrow>
                    \<exists>a\<in>A. \<exists>b\<in>B. a \<plusminus> b = 1\<^sub>r"
by (simp add:coprimeTr)

lemma (in Ring) coprime_elemsTr:"\<lbrakk>ideal R A; ideal R B; a\<in>A; b\<in>B; a \<plusminus> b = 1\<^sub>r\<rbrakk> 
               \<Longrightarrow> pj R A b = 1\<^sub>r\<^bsub>(qring R A)\<^esub> \<and> pj R B a = 1\<^sub>r\<^bsub>(qring R B)\<^esub>"
apply (frule pj_Hom [OF Ring, of "A"],
       frule pj_Hom [OF Ring, of "B"])
 apply (frule qring_ring[of "A"], frule qring_ring[of "B"])
 apply (cut_tac ring_is_ag,
        frule Ring.ring_is_ag[of "R /\<^sub>r A"],
         frule Ring.ring_is_ag[of "R /\<^sub>r B"])
 apply (frule_tac a = a and b = b in aHom_add[of "R" "R /\<^sub>r A" "pj R A"],
         assumption+,
       simp add:rHom_def, simp add:ideal_subset,
       simp add:ideal_subset, simp)
 apply (frule ideal_subset[of "A" "a"], assumption,
        frule ideal_subset[of "B" "b"], assumption+)
 apply (simp only:pj_zero[OF Ring, THEN sym, of "A" "a"],
        frule rHom_mem[of "pj R A" "R" "qring R A" "b"], assumption+,
        simp add:aGroup.l_zero[of "R /\<^sub>r A"])
  apply (simp add:rHom_one[OF Ring, of "qring R A"])
  
  apply (frule_tac a = a and b = b in aHom_add[of "R" "R /\<^sub>r B" "pj R B"],
         assumption+,
       simp add:rHom_def, simp add:ideal_subset,
       simp add:ideal_subset, simp)
  apply (simp only:pj_zero[OF Ring, THEN sym, of "B" "b"],
        frule rHom_mem[of "pj R B" "R" "qring R B" "a"], assumption+,
        simp add:aGroup.ag_r_zero[of "R /\<^sub>r B"])
  apply (simp add:rHom_one[OF Ring, of "qring R B"])
done

lemma (in Ring) partition_of_unity:"\<lbrakk>ideal R A; a \<in> A; b \<in> carrier R; 
       a \<plusminus> b = 1\<^sub>r; u \<in> carrier R; v \<in> carrier R\<rbrakk> \<Longrightarrow> 
                                 pj R A (a \<cdot>\<^sub>r v \<plusminus> b \<cdot>\<^sub>r u ) = pj R A u"
apply (frule pj_Hom [OF Ring, of "A"],
       frule ideal_subset [of "A" "a"], assumption+,
       frule ring_tOp_closed[of "a" "v"], assumption+,
       frule ring_tOp_closed[of "b" "u"], assumption+,
       frule qring_ring[of "A"])
 apply (simp add:ringhom1[OF Ring, of "qring R A" "a \<cdot>\<^sub>r v" "b \<cdot>\<^sub>r u" "pj R A"])
 apply (frule ideal_ring_multiple1[of "A" "a" "v"], assumption+,
        simp add:pj_zero[OF Ring, THEN sym, of "A" "a \<cdot>\<^sub>r v"],
        frule rHom_mem[of "pj R A" "R" "qring R A" "b \<cdot>\<^sub>r u"], assumption+,
        simp add:Ring.l_zero, simp add:rHom_tOp[OF Ring])
 apply (frule ringhom1[OF Ring, of "qring R A" "a" "b" "pj R A"], assumption+,
        simp,
        simp add:pj_zero[OF Ring, THEN sym, of "A" "a"],
        frule rHom_mem[of "pj R A" "R" "qring R A" "b"], assumption+,
        simp add:Ring.l_zero)
   apply (simp add:rHom_one[OF Ring, of "qring R A" "pj R A"],
          rotate_tac -2, frule sym, thin_tac "1\<^sub>r\<^bsub>R /\<^sub>r A\<^esub> = pj R A b",
          simp,
          rule Ring.ring_l_one[of "qring R A" "pj R A u"], assumption)
  apply (simp add:rHom_mem)
done

lemma (in Ring) coprimes_commute:"\<lbrakk>ideal R A; ideal R B; coprime_ideals R A B \<rbrakk>
 \<Longrightarrow> coprime_ideals R B A"
apply (simp add:coprime_ideals_def)
apply (simp add:sum_ideals_commute)
done

lemma (in Ring) coprime_surjTr:"\<lbrakk>ideal R A; ideal R B; coprime_ideals R A B; 
                 X \<in> carrier (qring R A); Y \<in> carrier (qring R B) \<rbrakk> \<Longrightarrow> 
                         \<exists>r\<in>carrier R. pj R A r = X \<and> pj R B r = Y"
apply (frule qring_ring [of "A"], 
       frule qring_ring [of "B"], 
       frule coprime_elems [of "A" "B"], assumption+,
       frule pj_Hom [OF Ring, of "A"],
       frule pj_Hom [OF Ring, of "B"])
apply (erule bexE)+
 apply (simp add:qring_carrier[of "A"],
        simp add:qring_carrier[of "B"], (erule bexE)+,
        rename_tac a b u v)
 apply (rotate_tac -1, frule sym, thin_tac "v \<uplus>\<^bsub>R\<^esub> B = Y",
        rotate_tac -3, frule sym, thin_tac "u \<uplus>\<^bsub>R\<^esub> A = X", simp)
 apply (frule_tac h = a in ideal_subset[of "A"], assumption+,
       frule_tac h = b in ideal_subset[of "B"], assumption+,
       frule_tac x = a and y = v in ring_tOp_closed, assumption+,
       frule_tac x = b and y = u in ring_tOp_closed, assumption+,
       cut_tac ring_is_ag,
       frule_tac x = "a \<cdot>\<^sub>r v" and y = "b \<cdot>\<^sub>r u" in aGroup.ag_pOp_closed[of "R"], 
       assumption+) 
 apply (frule_tac a = a and b = b and u = u and v = v in 
                  partition_of_unity[of "A"], assumption+,
        simp add:pj_mem[OF Ring, of "A"])
 apply (frule_tac a = b and b = a and u = v and v = u in 
           partition_of_unity[of "B"], assumption+,
        subst aGroup.ag_pOp_commute[of "R"], assumption+,
        simp add:pj_mem[OF Ring, of "B"])      
 apply (frule_tac x = "b \<cdot>\<^sub>r u" and y = "a \<cdot>\<^sub>r v" in 
             aGroup.ag_pOp_commute[of "R"], assumption+, simp)
 apply (simp add:pj_mem[OF Ring], blast)
done

lemma (in Ring) coprime_n_idealsTr0:"\<lbrakk>ideal R A; ideal R B; ideal R C; 
         coprime_ideals R A C; coprime_ideals R B C \<rbrakk> \<Longrightarrow> 
             coprime_ideals R (A \<diamondsuit>\<^sub>r B) C" 
apply (simp add:coprimeTr[of "A" "C"],
       simp add:coprimeTr[of "B" "C"], (erule bexE)+)
apply (cut_tac ring_is_ag,
       frule_tac h = a in ideal_subset[of "A"], assumption+,
       frule_tac h = aa in ideal_subset[of "B"], assumption+,
       frule_tac h = b in ideal_subset[of "C"], assumption+,
       frule_tac h = ba in ideal_subset[of "C"], assumption+,
       frule_tac x = a and y = b in aGroup.ag_pOp_closed, assumption+)
apply (frule_tac x = "a \<plusminus> b" and y = aa and z = ba in ring_distrib1,
        assumption+) apply (
       rotate_tac 6, frule sym, thin_tac "a \<plusminus> b = 1\<^sub>r",
       frule sym, thin_tac "aa \<plusminus> ba = 1\<^sub>r")
      apply (simp only:ring_distrib2)
apply (rotate_tac -1, frule sym, thin_tac "1\<^sub>r = a \<plusminus> b", simp,
       thin_tac "aa \<plusminus> ba = 1\<^sub>r")
       apply (simp add:ring_r_one,
       thin_tac "a \<cdot>\<^sub>r aa \<plusminus> b \<cdot>\<^sub>r aa \<plusminus> (a \<cdot>\<^sub>r ba \<plusminus> b \<cdot>\<^sub>r ba) \<in> carrier R",
       thin_tac "a \<plusminus> b = a \<cdot>\<^sub>r aa \<plusminus> b \<cdot>\<^sub>r aa \<plusminus> (a \<cdot>\<^sub>r ba \<plusminus> b \<cdot>\<^sub>r ba)")
 apply (frule_tac x = a and y = aa in ring_tOp_closed, assumption+,
        frule_tac x = b and y = aa in ring_tOp_closed, assumption+,
        frule_tac x = a and y = ba in ring_tOp_closed, assumption+,
        frule_tac x = b and y = ba in ring_tOp_closed, assumption+, 
        frule_tac x = "a \<cdot>\<^sub>r ba" and y = "b \<cdot>\<^sub>r ba" in aGroup.ag_pOp_closed, 
        assumption+)
  apply (simp add:aGroup.ag_pOp_assoc,
         frule sym, thin_tac "1\<^sub>r = a \<cdot>\<^sub>r aa \<plusminus> (b \<cdot>\<^sub>r aa \<plusminus> (a \<cdot>\<^sub>r ba \<plusminus> b \<cdot>\<^sub>r ba))")
  apply (frule_tac i = a and j = aa in prod_mem_prod_ideals[of "A" "B"],
           assumption+)
  apply (frule_tac x = ba and r = a in ideal_ring_multiple[of "C"],
           assumption+,
         frule_tac x = ba and r = b in ideal_ring_multiple[of "C"],
           assumption+,
         frule_tac x = b and r = aa in ideal_ring_multiple1[of "C"],
           assumption+)
  apply (frule_tac I = C and x = "a \<cdot>\<^sub>r ba" and y = "b \<cdot>\<^sub>r ba" in 
         ideal_pOp_closed, assumption+,
         frule_tac I = C and x = "b \<cdot>\<^sub>r aa" and y = "a \<cdot>\<^sub>r ba \<plusminus> b \<cdot>\<^sub>r ba" in 
         ideal_pOp_closed, assumption+)
  apply (frule ideal_prod_ideal[of "A" "B"], assumption)
  apply (subst coprimeTr, assumption+, blast)
done

lemma (in Ring) coprime_n_idealsTr1:"ideal R C \<Longrightarrow>
    (\<forall>k \<le> n. ideal R (J k)) \<and> (\<forall>i \<le> n.  coprime_ideals R (J i) C) \<longrightarrow> 
    coprime_ideals R (i\<Pi>\<^bsub>R,n\<^esub> J) C"
apply (induct_tac n)
apply (rule impI)
apply (erule conjE)
 apply simp 

apply (rule impI)
apply (erule conjE)
apply (cut_tac n = "Suc n" in n_in_Nsetn)
apply (cut_tac n = n in Nset_Suc) apply simp
 apply (cut_tac n = n and J = J in n_prod_ideal,
        rule allI, simp)
 apply (rule_tac A = "i\<Pi>\<^bsub>R,n\<^esub> J" and B = "J (Suc n)" in 
                coprime_n_idealsTr0[of _ _ "C"], simp+)
done

lemma (in Ring) coprime_n_idealsTr2:"\<lbrakk>ideal R C; (\<forall>k \<le> n. ideal R (J k)); 
       (\<forall>i \<le> n. coprime_ideals R (J i) C) \<rbrakk> \<Longrightarrow> 
                                     coprime_ideals R (i\<Pi>\<^bsub>R,n\<^esub> J) C"
by (simp add:coprime_n_idealsTr1)

lemma (in Ring) coprime_n_idealsTr3:"(\<forall>k \<le> (Suc n). ideal R (J k)) \<and> 
    (\<forall>i \<le> (Suc n). \<forall>j \<le> (Suc n). i \<noteq> j \<longrightarrow> 
    coprime_ideals R (J i) (J j)) \<longrightarrow>  coprime_ideals R (i\<Pi>\<^bsub>R,n\<^esub> J) (J (Suc n))"
apply (rule impI, erule conjE)
apply (case_tac "n = 0", simp)
 apply (simp add:Nset_1)
 apply (cut_tac nat_eq_le[of "Suc n" "Suc n"],
        frule_tac a = "Suc n" in forall_spec, assumption) 
 apply (rotate_tac 1, frule_tac a = "Suc n" in forall_spec, assumption,
        thin_tac "\<forall>j\<le>Suc n. Suc n \<noteq> j \<longrightarrow> coprime_ideals R (J (Suc n)) (J j)")
 apply (rule_tac C = "J (Suc n)" and n = n and J = J in coprime_n_idealsTr2,
        assumption, rule allI, simp)
 apply (rule allI, rule impI)
 apply (frule_tac a = i in forall_spec, simp,
       thin_tac "\<forall>i\<le>Suc n. \<forall>j\<le>Suc n. i \<noteq> j \<longrightarrow> coprime_ideals R (J i) (J j)",
       rotate_tac -1,
       frule_tac a = "Suc n" in forall_spec, assumption+)
 apply simp+
done

lemma (in Ring) coprime_n_idealsTr4:"\<lbrakk>(\<forall>k \<le> (Suc n). ideal R (J k)) \<and> 
   (\<forall>i \<le> (Suc n). \<forall>j \<le> (Suc n). i \<noteq> j \<longrightarrow> 
    coprime_ideals R (J i) (J j))\<rbrakk> \<Longrightarrow> coprime_ideals R (i\<Pi>\<^bsub>R,n\<^esub> J) (J (Suc n))"
apply (simp add:coprime_n_idealsTr3)
done

section "Direct product1, general case"

definition
  prod_tOp :: "['i set,  'i \<Rightarrow> ('a, 'm) Ring_scheme] \<Rightarrow> 
    ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow>  ('i \<Rightarrow> 'a)" where
  "prod_tOp I A = (\<lambda>f\<in>carr_prodag I A. \<lambda>g\<in>carr_prodag I A.
                           \<lambda>x\<in>I. (f x) \<cdot>\<^sub>r\<^bsub>(A x)\<^esub> (g x))"
  (** Let x \<in> I, then A x is a ring, {A x | x \<in> I} is a set of rings. **)

definition
  prod_one::"['i set,  'i  \<Rightarrow> ('a, 'm) Ring_scheme] \<Rightarrow> ('i \<Rightarrow> 'a)" where
  "prod_one I A == \<lambda>x\<in>I. 1\<^sub>r\<^bsub>(A x)\<^esub>"
  (** 1\<^sub>(A x) is the unit of a ring A x. **)

definition
  prodrg :: "['i set, 'i \<Rightarrow> ('a, 'more) Ring_scheme] \<Rightarrow> ('i \<Rightarrow> 'a) Ring" where
  "prodrg I A = \<lparr>carrier = carr_prodag I A, pop = prod_pOp I A, mop = 
    prod_mOp I A, zero = prod_zero I A, tp = prod_tOp I A, 
    un = prod_one I A \<rparr>"
 (** I is the index set **)

abbreviation
  PRODRING  ("(r\<Pi>\<^bsub>_\<^esub>/ _)" [72,73]72) where
  "r\<Pi>\<^bsub>I\<^esub> A == prodrg I A"

definition
  augm_func :: "[nat, nat \<Rightarrow> 'a,'a set, nat, nat \<Rightarrow> 'a, 'a set] \<Rightarrow> nat \<Rightarrow> 'a" where
  "augm_func n f A m g B = (\<lambda>i\<in>{j. j \<le> (n + m)}. if i \<le> n then f i else
    if (Suc n) \<le> i \<and> i \<le> n + m then g ((sliden (Suc n)) i) else undefined)"
 (* Remark. g is a function of Nset (m - 1) \<rightarrow> B *)  

definition    
  ag_setfunc :: "[nat, nat \<Rightarrow> ('a, 'more) Ring_scheme, nat, 
nat \<Rightarrow> ('a, 'more)  Ring_scheme] \<Rightarrow> (nat \<Rightarrow> 'a) set \<Rightarrow> (nat \<Rightarrow> 'a) set
 \<Rightarrow> (nat  \<Rightarrow> 'a) set" where
  "ag_setfunc n B1 m B2 X Y =
    {f. \<exists>g. \<exists>h. (g\<in>X) \<and>(h\<in>Y) \<and>(f = (augm_func n g (Un_carrier {j. j \<le> n} B1) 
      m h (Un_carrier {j. j \<le> (m - 1)} B2)))}"
 (* Later we consider X = ac_Prod_Rg (Nset n) B1 and Y = ac_Prod_Rg (Nset (m - 1)) B2 *)  
 
primrec
  ac_fProd_Rg :: "[nat, nat \<Rightarrow> ('a, 'more) Ring_scheme] \<Rightarrow>
                 (nat \<Rightarrow> 'a) set"
where
  fprod_0: "ac_fProd_Rg 0 B = carr_prodag {0::nat} B"
| frpod_n: "ac_fProd_Rg (Suc n) B = ag_setfunc n B (Suc 0) (compose {0::nat} 
 B (slide (Suc n))) (carr_prodag {j. j \<le> n} B) (carr_prodag {0} (compose {0} B (slide (Suc n))))"

definition
  prodB1 :: "[('a, 'm) Ring_scheme, ('a, 'm) Ring_scheme] \<Rightarrow>
                 (nat \<Rightarrow> ('a, 'm) Ring_scheme)" where
  "prodB1 R S = (\<lambda>k. if k=0 then R else if k=Suc 0 then S else
                 undefined)"

definition
  Prod2Rg :: "[('a, 'm) Ring_scheme, ('a, 'm) Ring_scheme]
              \<Rightarrow> (nat \<Rightarrow> 'a) Ring" (infixl "\<Oplus>\<^sub>r" 80) where
  "A1 \<Oplus>\<^sub>r A2 = prodrg {0, Suc 0} (prodB1 A1 A2)"

text \<open>Don't try \<open>(Prod_ring (Nset n) B) \<Oplus>\<^sub>r (B (Suc n))\<close>\<close>

lemma carr_prodrg_mem_eq:"\<lbrakk>f \<in> carrier (r\<Pi>\<^bsub>I\<^esub> A); g \<in> carrier (r\<Pi>\<^bsub>I\<^esub> A);
       \<forall>i\<in>I. f i = g i \<rbrakk> \<Longrightarrow> f = g" 
by (simp add:prodrg_def carr_prodag_def, (erule conjE)+,
    rule funcset_eq[of _ I], assumption+)

lemma prod_tOp_mem:"\<lbrakk>\<forall>k\<in>I. Ring (A k); X \<in> carr_prodag I A;
 Y \<in> carr_prodag I A\<rbrakk> \<Longrightarrow> prod_tOp I A X Y \<in> carr_prodag I A"
apply (subst carr_prodag_def, simp)
apply (rule conjI)
 apply (simp add:prod_tOp_def restrict_def extensional_def)
apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:Un_carrier_def prod_tOp_def)
 apply (simp add:carr_prodag_def, (erule conjE)+)
 apply (blast dest: Ring.ring_tOp_closed del:PiE)
 
 apply (rule ballI)
 apply (simp add:prod_tOp_def)
 apply (simp add:carr_prodag_def, (erule conjE)+)
 apply (simp add:Ring.ring_tOp_closed)
done
 
 
lemma prod_tOp_func:"\<forall>k\<in>I. Ring (A k) \<Longrightarrow>
    prod_tOp I A \<in> carr_prodag I A \<rightarrow> carr_prodag I A \<rightarrow> carr_prodag I A"
by (simp add:prod_tOp_mem)

lemma prod_one_func:"\<forall>k\<in>I. Ring (A k) \<Longrightarrow>
                           prod_one I A \<in> carr_prodag I A"
apply (simp add:prod_one_def carr_prodag_def)
apply (rule conjI)
apply (rule Pi_I)
 apply (simp add:Un_carrier_def)
 apply (blast dest: Ring.ring_one)
 apply (simp add: Ring.ring_one)
done

lemma prodrg_carrier:"\<forall>k\<in>I. Ring (A k) \<Longrightarrow>
                  carrier (prodrg I A) = carrier (prodag I A)"
by (simp add:prodrg_def prodag_def)

lemma prodrg_ring:"\<forall>k\<in>I. Ring (A k) \<Longrightarrow> Ring (prodrg I A)"
apply (rule Ring.intro)
 apply (simp add:prodrg_def)
 apply (rule prod_pOp_func,
        rule ballI, simp add:Ring.ring_is_ag)
 
 apply (simp add:prodrg_def, rule prod_pOp_assoc,
        simp add:Ring.ring_is_ag, assumption+)
 
 apply (simp add:prodrg_def, rule prod_pOp_commute,
          simp add:Ring.ring_is_ag, assumption+)

 apply (simp add:prodrg_def, rule prod_mOp_func,
           simp add:Ring.ring_is_ag) 
 
 apply (simp add:prodrg_def)
 apply (cut_tac X = a in prod_mOp_mem[of "I" "A"])
        apply (simp add:Ring.ring_is_ag, assumption)
 apply (cut_tac X = "prod_mOp I A a" and Y = a in prod_pOp_mem[of "I" "A"],
        simp add:Ring.ring_is_ag, assumption+,
        cut_tac prod_zero_func[of "I" "A"])
 apply (rule carr_prodag_mem_eq[of "I" "A"],
        simp add:Ring.ring_is_ag, assumption+,
        rule ballI, simp add:prod_pOp_def,
        subst prod_mOp_mem_i, simp add:Ring.ring_is_ag, assumption+,
        subst prod_zero_i, simp add:Ring.ring_is_ag, assumption+,
        rule aGroup.l_m, simp add:Ring.ring_is_ag,
        simp add:prodag_comp_i, simp add:Ring.ring_is_ag)
 apply (simp add:prodrg_def,
        rule prod_zero_func, simp add:Ring.ring_is_ag)
 apply (simp add:prodrg_def,
        cut_tac prod_zero_func[of "I" "A"],
        cut_tac X = "prod_zero I A" and Y = a in prod_pOp_mem[of "I" "A"],
        simp add:Ring.ring_is_ag, assumption+,
        rule carr_prodag_mem_eq[of "I" "A"],
        simp add:Ring.ring_is_ag, assumption+)
        apply (rule ballI)
      apply (simp add:prod_pOp_def prod_zero_def)
      apply (rule aGroup.ag_l_zero, simp add:Ring.ring_is_ag)
      apply (simp add:prodag_comp_i, simp add:Ring.ring_is_ag)
 apply (simp add:prodrg_def,
        rule prod_tOp_func, simp add:Ring.ring_is_ag)
 apply (simp add:prodrg_def)
  apply (frule_tac X = a and Y = b in prod_tOp_mem[of "I" "A"], assumption+,
         frule_tac X = "prod_tOp I A a b" and Y = c in 
                                      prod_tOp_mem[of "I" "A"], assumption+,
         frule_tac X = b and Y = c in prod_tOp_mem[of "I" "A"], assumption+,
         frule_tac X = a and Y = "prod_tOp I A b c" in 
                                      prod_tOp_mem[of "I" "A"], assumption+)
  apply (rule carr_prodag_mem_eq[of "I" "A"],
         simp add:Ring.ring_is_ag, assumption+, rule ballI)
  apply (simp add:prod_tOp_def)
  apply (rule Ring.ring_tOp_assoc, simp, (simp add:prodag_comp_i)+)
 apply (simp add:prodrg_def)
  apply (frule_tac X = a and Y = b in prod_tOp_mem[of "I" "A"], assumption+,
         frule_tac X = b and Y = a in prod_tOp_mem[of "I" "A"], assumption+,
         rule carr_prodag_mem_eq[of "I" "A"],
         simp add:Ring.ring_is_ag, assumption+)
  apply (rule ballI, simp add:prod_tOp_def)
  apply (rule Ring.ring_tOp_commute, (simp add:prodag_comp_i)+)
 apply (simp add:prodrg_def, rule prod_one_func, assumption)

 apply (simp add:prodrg_def)
  apply (cut_tac X = b and Y = c in prod_pOp_mem[of "I" "A"],
         simp add:Ring.ring_is_ag, assumption+,
         cut_tac X = a and Y = b in prod_tOp_mem[of "I" "A"], assumption+,
         cut_tac X = a and Y = c in prod_tOp_mem[of "I" "A"], assumption+,
         cut_tac X = "prod_tOp I A a b" and Y = "prod_tOp I A a c" in 
         prod_pOp_mem[of "I" "A"], simp add:Ring.ring_is_ag, assumption+)
  apply (rule carr_prodag_mem_eq[of "I" "A"],
         simp add:Ring.ring_is_ag, rule prod_tOp_mem[of "I" "A"], assumption+)
  apply (rule ballI, simp add:prod_tOp_def prod_pOp_def)
  apply (rule Ring.ring_distrib1, (simp add:prodag_comp_i)+)

 apply (simp add:prodrg_def,
        cut_tac prod_one_func[of "I" "A"],
        cut_tac X = "prod_one I A" and Y = a in prod_tOp_mem[of "I" "A"], 
        assumption+) 
 apply (rule carr_prodag_mem_eq[of "I" "A"],
        simp add:Ring.ring_is_ag, assumption+,
        rule ballI, simp add:prod_tOp_def prod_one_def,
        rule Ring.ring_l_one, simp, simp add:prodag_comp_i)
 apply simp
done

lemma prodrg_elem_extensional:"\<lbrakk>\<forall>k\<in>I. Ring (A k); f \<in> carrier (prodrg I A)\<rbrakk>
      \<Longrightarrow>  f \<in> extensional I"
apply (simp add:prodrg_carrier)
apply (simp add:prodag_def carr_prodag_def)
done

lemma prodrg_pOp:"\<forall>k\<in>I. Ring (A k) \<Longrightarrow> 
                  pop (prodrg I A) = prod_pOp I A"
apply (simp add:prodrg_def)
done

lemma prodrg_mOp:"\<forall>k\<in>I. Ring (A k) \<Longrightarrow> 
                  mop (prodrg I A) = prod_mOp I A"
apply (simp add:prodrg_def)
done 

lemma prodrg_zero:"\<forall>k\<in>I. Ring (A k) \<Longrightarrow> 
                  zero (prodrg I A) = prod_zero I A"
apply (simp add:prodrg_def)
done

lemma prodrg_tOp:"\<forall>k\<in>I. Ring (A k) \<Longrightarrow> 
                  tp (prodrg I A) = prod_tOp I A"
apply (simp add:prodrg_def)
done

lemma prodrg_one:"\<forall>k\<in>I. Ring (A k) \<Longrightarrow> 
                  un (prodrg I A) = prod_one I A"
apply (simp add:prodrg_def)
done

lemma prodrg_sameTr5:"\<lbrakk>\<forall>k\<in>I. Ring (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prod_tOp I A = prod_tOp I B"
apply (frule prod_tOp_func)
apply (subgoal_tac "carr_prodag I A = carr_prodag I B", simp)
apply (frule prod_tOp_func [of "I" "B"])
 apply (rule funcset_eq [of _ "carr_prodag I B" _])
 apply (simp add:prod_tOp_def extensional_def) 
 apply (simp add:prod_tOp_def extensional_def) 
apply (rule ballI)
 apply (frule_tac x = x in funcset_mem [of "prod_tOp I A" "carr_prodag I B"
 "carr_prodag I B \<rightarrow> carr_prodag I B"], assumption+)
 apply (frule_tac x = x in funcset_mem [of "prod_tOp I B" "carr_prodag I B"
 "carr_prodag I B \<rightarrow> carr_prodag I B"], assumption+)
 apply (thin_tac " prod_tOp I A
           \<in> carr_prodag I B \<rightarrow> carr_prodag I B \<rightarrow> carr_prodag I B")
 apply (thin_tac "prod_tOp I B
           \<in> carr_prodag I B \<rightarrow> carr_prodag I B \<rightarrow> carr_prodag I B")
 apply (rule funcset_eq [of _ "carr_prodag I B"])
 apply (simp add:prod_tOp_def extensional_def) 
 apply (simp add:prod_tOp_def extensional_def) 
apply (rule ballI)
 apply (frule_tac f = "prod_tOp I A x" and A = "carr_prodag I B" and
         x = xa in funcset_mem, assumption+)
 apply (frule_tac f = "prod_tOp I B x" and A = "carr_prodag I B" and
         x = xa in funcset_mem, assumption+)
 apply (subgoal_tac "\<forall>k\<in>I. aGroup (B k)") 
 apply (rule carr_prodag_mem_eq, assumption+)
 apply (rule ballI, simp add:prod_tOp_def) 
 apply (rule ballI, rule Ring.ring_is_ag, simp)
apply (subgoal_tac "\<forall>k\<in>I. aGroup (A k)")
 apply (simp add:prodag_sameTr1)
 apply (rule ballI, rule Ring.ring_is_ag, simp)
done

lemma prodrg_sameTr6:"\<lbrakk>\<forall>k\<in>I. Ring (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prod_one I A = prod_one I B"
apply (frule prod_one_func [of "I" "A"])
apply (cut_tac prodag_sameTr1[of "I" "A" "B"])
apply (rule carr_prodag_mem_eq[of I A "prod_one I A" "prod_one I B"])
apply (simp add:Ring.ring_is_ag, assumption)
 apply (cut_tac prod_one_func [of "I" "B"], simp)
 apply simp
 apply (rule ballI, simp add:prod_one_def)
 apply (simp add:Ring.ring_is_ag, simp)
done

lemma prodrg_same:"\<lbrakk>\<forall>k\<in>I. Ring (A k); \<forall>k\<in>I. A k = B k\<rbrakk>
                               \<Longrightarrow> prodrg I A = prodrg I B"
apply (subgoal_tac "\<forall>k\<in>I. aGroup (A k)")
apply (frule prodag_sameTr1, assumption+) 
apply (frule prodag_sameTr2, assumption+) 
apply (frule prodag_sameTr3, assumption+)
apply (frule prodag_sameTr4, assumption+)
apply (frule prodrg_sameTr5, assumption+)
apply (frule prodrg_sameTr6, assumption+)
apply (simp add:prodrg_def)
apply (rule ballI, rule Ring.ring_is_ag, simp)
done

lemma prodrg_component:"\<lbrakk>f \<in> carrier (prodrg I A); i \<in> I\<rbrakk> \<Longrightarrow>
                                 f i \<in> carrier (A i)"
by (simp add:prodrg_def carr_prodag_def)

lemma project_rhom:"\<lbrakk>\<forall>k\<in>I. Ring (A k); j \<in> I\<rbrakk> \<Longrightarrow>
                         PRoject I A j \<in> rHom ( prodrg I A) (A j)"
apply (simp add:rHom_def)
apply (rule conjI)
 apply (simp add:aHom_def)
 apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:prodrg_carrier)
 apply (cut_tac prodag_carrier[of I A], simp)

 apply (simp add:PRoject_def)
 apply (cut_tac prodag_carrier[of I A], simp,
        thin_tac "carrier (a\<Pi>\<^bsub>I\<^esub> A) = carr_prodag I A")
 apply (simp add:prodag_comp_i) 
 apply (simp add:Ring.ring_is_ag)
 apply (simp add:Ring.ring_is_ag)

 apply (subgoal_tac "\<forall>k\<in>I. aGroup (A k)") 
 apply (frule project_aHom [of "I" "A" "j"], assumption+) 
 apply (rule conjI)
 apply (simp add:prodrg_carrier aHom_def)
 apply (simp add:prodrg_carrier)
 apply (simp add:prodrg_pOp)
 apply (simp add:prodag_pOp[THEN sym])
 apply (simp add:aHom_def)

 apply (rule ballI, simp add:Ring.ring_is_ag)

 apply (rule conjI)
 apply (rule ballI)+
 apply (simp add:prodrg_carrier)
 apply (cut_tac prodag_carrier[of I A], simp) 
 apply (frule_tac X = x and Y = y in prod_tOp_mem[of I A], assumption+)
 apply (simp add:prodrg_tOp)
 apply (simp add:PRoject_def)
 apply (simp add:prod_tOp_def)
 
 apply (rule ballI)
 apply (simp add:Ring.ring_is_ag)

apply (frule prodrg_ring [of "I" "A"])
apply (frule Ring.ring_one[of "r\<Pi>\<^bsub>I\<^esub> A"])
 apply (simp add:prodrg_carrier)
 apply (cut_tac prodag_carrier[of I A], simp)
 apply (simp add:PRoject_def) apply (simp add:prodrg_def)
 apply (fold prodrg_def) apply (simp add:prod_one_def) 

apply (rule ballI)
 apply (simp add:Ring.ring_is_ag) 
done

lemma augm_funcTr:"\<lbrakk>\<forall>k \<le>(Suc n). Ring (B k); 
                       f \<in> carr_prodag {i. i \<le> (Suc n)} B\<rbrakk> \<Longrightarrow> 
 f = augm_func n (restrict f {i. i \<le> n}) (Un_carrier {i. i \<le> n} B) (Suc 0)  
     (\<lambda>x\<in>{0::nat}. f (x + Suc n)) 
             (Un_carrier {0} (compose {0} B (slide (Suc n))))"
apply (rule carr_prodag_mem_eq [of "{i. i \<le> (Suc n)}" "B" "f"
 "augm_func n (restrict f {i. i \<le> n}) (Un_carrier {i. i \<le> n} B) (Suc 0)
 (\<lambda>x\<in>{0}. f (x + Suc n)) (Un_carrier {0} (compose {0} B (slide (Suc n))))"])
 apply (rule ballI, simp add:Ring.ring_is_ag)
 apply (simp add:augm_func_def)
 apply (simp add:carr_prodag_def)
 apply (rule conjI)
 apply (simp add:augm_func_def)
 apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:augm_func_def sliden_def) 
 apply (erule conjE)+
 apply (frule_tac x = x in funcset_mem[of f "{i. i \<le> Suc n}" 
                           "Un_carrier {i. i \<le> Suc n} B"]) apply simp
 apply simp 
 apply (rule impI)
  apply (rule_tac x = "Suc n" in funcset_mem[of f "{i. i \<le> Suc n}" 
                  "Un_carrier {i. i \<le> Suc n} B"], assumption) apply simp
 apply (rule allI, (erule conjE)+) 
 apply (simp add:augm_func_def)
 apply (case_tac "i \<le> n", simp add:sliden_def)
 apply (simp add:sliden_def, rule impI) 
 apply (simp add:nat_not_le_less,
        frule_tac m = n and n = i in Suc_leI,
        frule_tac m = i and n = "Suc n" in Nat.le_antisym, assumption+,
        simp)
 
 apply (rule ballI, simp) 
 apply (simp add:augm_func_def sliden_def)
 apply (rule impI, simp add:nat_not_le_less)
  apply (frule_tac n = l in Suc_leI[of n _])
  apply (frule_tac m = l and n = "Suc n" in Nat.le_antisym, assumption+,
         simp)
done

lemma A_to_prodag_mem:"\<lbrakk>Ring A; \<forall>k\<in>I. Ring (B k);  \<forall>k\<in>I. (S k) \<in> 
 rHom A (B k); x \<in> carrier A \<rbrakk> \<Longrightarrow> A_to_prodag A I S B x \<in> carr_prodag I B"
apply (simp add:carr_prodag_def)
apply (rule conjI)
apply (simp add:A_to_prodag_def extensional_def) 
apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add: A_to_prodag_def)
 apply (subgoal_tac "(S xa) \<in> rHom A (B xa)") prefer 2 apply simp
 apply (thin_tac "\<forall>k\<in>I. S k \<in> rHom A (B k)") 
 apply (frule_tac f = "S xa" and A = A and R = "B xa" in rHom_mem, assumption+)
 apply (simp add:Un_carrier_def) apply blast
apply (rule ballI)

apply (simp add:A_to_prodag_def)
 apply (rule_tac f = "S i" and A = A and R = "B i" and a = x in rHom_mem)
   apply simp 
   apply assumption
done

lemma A_to_prodag_rHom:"\<lbrakk>Ring A; \<forall>k\<in>I. Ring (B k); \<forall>k\<in>I. (S k) \<in> 
      rHom A (B k) \<rbrakk>  \<Longrightarrow> A_to_prodag A I S B \<in> rHom A (r\<Pi>\<^bsub>I\<^esub> B)"
apply (simp add:rHom_def [of "A" "r\<Pi>\<^bsub>I\<^esub> B"])
apply (rule conjI)
 apply (cut_tac A_to_prodag_aHom[of A I B S])
 apply (subst aHom_def, simp)
 apply (simp add:prodrg_carrier)
 apply (simp add:aHom_def)
 apply (simp add:prodrg_def)
 apply (cut_tac prodag_pOp[of I B], simp)

 apply (rule ballI, simp add:Ring.ring_is_ag,
        simp add:Ring.ring_is_ag,
        rule ballI, simp add:Ring.ring_is_ag)

 apply (rule ballI) 
 apply (simp add:rHom_def)

apply (rule conjI)
 apply (rule ballI)+
 apply (frule_tac x = x and y = y in Ring.ring_tOp_closed[of A], assumption+)
 apply (frule_tac x = "x \<cdot>\<^sub>r\<^bsub>A\<^esub> y" in A_to_prodag_mem[of A I B S], assumption+,
        frule_tac x = x in A_to_prodag_mem[of A I B S], assumption+,
        frule_tac x = y in A_to_prodag_mem[of A I B S], assumption+)
 apply (simp add:prodrg_tOp[of I B])
 apply (frule_tac X = "A_to_prodag A I S B x " and Y = "A_to_prodag A I S B y"         in prod_tOp_mem[of I B], assumption+)
apply (cut_tac X = "A_to_prodag A I S B (x \<cdot>\<^sub>r\<^bsub>A\<^esub> y)" and Y = "prod_tOp I B (A_to_prodag A I S B x) (A_to_prodag A I S B y)" in carr_prodag_mem_eq[of I B])
 apply (rule ballI, simp add:Ring.ring_is_ag) apply assumption+
 apply (rule ballI, simp add:prod_tOp_def A_to_prodag_def)
 apply (frule_tac x = l in bspec, assumption,
        thin_tac "\<forall>k\<in>I. Ring (B k)",
        frule_tac x = l in bspec, assumption,
        thin_tac "\<forall>k\<in>I. S k \<in> rHom A (B k)")
 apply (simp add:rHom_tOp) apply simp

 apply (simp add:prodrg_one[of I B])
 apply (frule prod_one_func[of I B])
 apply (frule Ring.ring_one[of A],
        frule_tac x = "1\<^sub>r\<^bsub>A\<^esub>" in A_to_prodag_mem[of A I B S], assumption+)
 apply (cut_tac X = "A_to_prodag A I S B 1\<^sub>r\<^bsub>A\<^esub>" and Y = "prod_one I B" in 
        carr_prodag_mem_eq[of I B])
 apply (rule ballI, simp add:Ring.ring_is_ag)
 apply assumption+
 apply (rule ballI)
 apply (subst A_to_prodag_def, simp add:prod_one_def)
 apply (frule_tac x = l in bspec, assumption,
        thin_tac "\<forall>k\<in>I. Ring (B k)",
        frule_tac x = l in bspec, assumption,
        thin_tac "\<forall>k\<in>I. S k \<in> rHom A (B k)")
 apply (simp add:rHom_one)
 apply assumption
done 

lemma ac_fProd_ProdTr1:"\<forall>k \<le> (Suc n). Ring (B k) \<Longrightarrow> 
 ag_setfunc n B (Suc 0) (compose {0::nat} B (slide (Suc n))) 
   (carr_prodag {i. i \<le> n} B) (carr_prodag {0} 
     (compose {0} B (slide (Suc n)))) \<subseteq>  carr_prodag {i. i \<le> (Suc n)} B" 
apply (rule subsetI)
apply (simp add:ag_setfunc_def) 
apply (erule exE, erule conjE, erule exE, erule conjE)
apply (simp,
       thin_tac "x =
        augm_func n g (Un_carrier {j. j \<le> n} B) (Suc 0) h
         (Un_carrier {0} (compose {0} B (slide (Suc n))))")
apply (simp add:carr_prodag_def [of "{j. j \<le> (Suc n)}" "B"])
apply (rule conjI)
 apply (simp add:augm_func_def)
apply (rule conjI) 
 apply (simp add:Pi_def) apply (rule allI) apply (rule impI)
 apply (simp add:augm_func_def)
 apply (case_tac "x \<le> n")
 apply simp apply (simp add:carr_prodag_def)
 apply (erule conjE)+ apply (frule_tac x = x in mem_of_Nset [of _ "n"])
 apply (frule_tac f = g and x = x in funcset_mem[of _ "{j. j \<le> n}" 
                      "Un_carrier {j. j \<le> n} B"], assumption+)
 apply (simp add:Un_carrier_def,
        erule exE, erule conjE, erule exE, simp, erule conjE,
        frule_tac x = i and y = n and z = "Suc n" in le_less_trans,
        simp, 
        frule_tac x = i and y = "Suc n" in less_imp_le, blast)
 apply (simp add:sliden_def)
 apply (simp add:carr_prodag_def Un_carrier_def, (erule conjE)+)
 apply (simp add:compose_def slide_def)
 apply (cut_tac n_in_Nsetn[of "Suc n"], blast)
 apply (rule allI, rule impI)
 apply (simp add:augm_func_def) 
 apply (case_tac "i \<le> n", simp)
 apply (simp add:carr_prodag_def [of "{i. i \<le> n}" _])
 apply simp apply (thin_tac "g \<in> carr_prodag {i. i \<le> n} B")
 apply (simp add: not_less [symmetric, of _ n],
        frule_tac n = i in Suc_leI[of n],
        frule_tac m = i and n = "Suc n" in le_antisym, assumption+, simp)
 apply (simp add:carr_prodag_def compose_def slide_def sliden_def)
done

lemma ac_fProd_Prod:"\<forall>k \<le> n. Ring (B k) \<Longrightarrow> 
                      ac_fProd_Rg n B = carr_prodag {j. j \<le> n} B"
apply (case_tac "n = 0") 
 apply simp
 apply (subgoal_tac "\<exists>m. n = Suc m")
 apply (subgoal_tac "\<forall>m. n = Suc m \<longrightarrow> 
                     ac_fProd_Rg n B = carr_prodag {j. j \<le> n} B")
 apply blast apply (thin_tac "\<exists>m. n = Suc m")
 apply (rule allI, rule impI) apply (simp, thin_tac "n = Suc m")
 apply (rule equalityI)
 apply (simp add:ac_fProd_ProdTr1)
 apply (rule subsetI)
 apply (rename_tac m f)  
apply (frule augm_funcTr, assumption+)
 apply (simp add:ag_setfunc_def)
 apply (subgoal_tac "(restrict f {j. j \<le> m}) \<in> carr_prodag {j. j \<le> m} B")
 apply (subgoal_tac "(\<lambda>x\<in>{0::nat}. f (Suc (x + m))) \<in>  carr_prodag {0}
                           (compose {0} B (slide (Suc m)))")
 
 apply blast
 apply (thin_tac "f =
           augm_func m (restrict f {i. i \<le> m}) (Un_carrier {i. i \<le> m} B)
            (Suc 0) (\<lambda>x\<in>{0}. f (Suc (x + m)))
            (Un_carrier {0} (compose {0} B (slide (Suc m))))")
 apply (simp add:carr_prodag_def)
 apply (rule conjI)
 apply (simp add:Pi_def restrict_def)
 apply (simp add:Un_carrier_def compose_def slide_def)
 apply (simp add:compose_def slide_def)

 apply (thin_tac "f =
           augm_func m (restrict f {i. i \<le> m}) (Un_carrier {i. i \<le> m} B)
            (Suc 0) (\<lambda>x\<in>{0}. f (Suc (x + m)))
            (Un_carrier {0} (compose {0} B (slide (Suc m))))")
 apply (simp add:carr_prodag_def)
 apply (simp add:Un_carrier_def)
 apply (simp add:Pi_def)
 apply (rule allI) apply (rule impI)
apply (erule conjE)+
 apply (rotate_tac 1) 
 apply (frule_tac a = x in forall_spec, simp)
 apply (erule exE,
        thin_tac "\<forall>x\<le>Suc m. \<exists>xa. (\<exists>i\<le>Suc m. xa = carrier (B i)) \<and> f x \<in> xa")
 apply (frule_tac a = x in forall_spec, simp)
apply blast
apply (cut_tac t = n in Suc_pred[THEN sym], simp)
apply blast
done

text\<open>A direct product of a finite number of rings defined with
 \<open>ac_fProd_Rg\<close> is equal to that defined by using \<open>carr_prodag\<close>.\<close>

definition
 fprodrg :: "[nat, nat \<Rightarrow> ('a, 'more) Ring_scheme] \<Rightarrow> 
  \<lparr>carrier:: (nat \<Rightarrow> 'a) set, pop::[(nat \<Rightarrow> 'a), (nat \<Rightarrow> 'a)]
   \<Rightarrow> (nat \<Rightarrow> 'a), mop:: (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a), zero::(nat \<Rightarrow> 'a), 
   tp :: [(nat \<Rightarrow> 'a), (nat \<Rightarrow> 'a)] \<Rightarrow> (nat \<Rightarrow> 'a), un :: (nat \<Rightarrow> 'a) \<rparr>" where
  
  "fprodrg n B = \<lparr> carrier = ac_fProd_Rg n B,
     pop = \<lambda>f. \<lambda>g. prod_pOp {i. i \<le> n} B f g, mop = \<lambda>f. prod_mOp {i. i \<le> n} B f,
     zero = prod_zero {i. i \<le> n} B, tp =  \<lambda>f. \<lambda>g. prod_tOp {i. i \<le> n} B f g, 
     un = prod_one {i. i \<le> n} B \<rparr>"  

definition
  fPRoject ::"[nat, nat \<Rightarrow> ('a, 'more) Ring_scheme, nat]
                   \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "fPRoject n B x = (\<lambda>f\<in>ac_fProd_Rg n B. f x)"

lemma fprodrg_ring:"\<forall>k \<le> n. Ring (B k) \<Longrightarrow> Ring (fprodrg n B)"
apply (simp add:fprodrg_def)
apply (frule ac_fProd_Prod)
apply simp 
 apply (fold prodrg_def)
apply (simp add:prodrg_ring)
done


section "Chinese remainder theorem"

lemma Chinese_remTr1:"\<lbrakk>Ring A; \<forall>k \<le> (n::nat). ideal A (J k); 
 \<forall>k \<le> n. B k = qring A (J k); \<forall>k \<le> n. S k = pj A (J k) \<rbrakk> \<Longrightarrow>
   ker\<^bsub>A,(r\<Pi>\<^bsub>{j. j \<le> n}\<^esub> B)\<^esub> (A_to_prodag A {j. j \<le> n} S B) = 
                                        \<Inter> {I. \<exists>k\<in>{j. j \<le> n}. I = (J k)}" 
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:ker_def)
 apply (rule allI, rule impI)
 apply (rename_tac a K, erule conjE)
 apply (simp add:prodrg_def, simp add:A_to_prodag_def prod_one_def)
 apply (erule exE, erule conjE) 
 
 apply (subgoal_tac "(\<lambda>k\<in>{j. j \<le> n}. S k a) k = (\<lambda>x\<in>{j. j \<le> n}. \<zero>\<^bsub>B x\<^esub>) k")
 apply (thin_tac "(\<lambda>k\<in>{j. j \<le> n}. S k a) = prod_zero {j. j \<le> n} B")
 apply simp  apply (frule_tac I = "J k" in Ring.qring_zero [of "A"])
 apply simp
 apply (frule_tac I = "J k" and x = a in pj_mem [of "A"]) apply simp
 apply assumption apply simp
 apply (frule_tac I = "J k" and a = a in Ring.a_in_ar_coset [of "A"])
 apply simp apply assumption apply simp
 apply (simp add:prod_zero_def)
apply (rule subsetI)
 apply (simp add:CollectI ker_def)

 apply (cut_tac Nset_inc_0[of n]) 
 apply (frule_tac a = "J 0" in forall_spec, blast)
 apply (frule_tac x = 0 in spec, simp)
 apply (frule_tac h = x in Ring.ideal_subset [of "A" "J 0"], simp+)
 apply (thin_tac "x \<in> J 0")
 apply (simp add:A_to_prodag_def prodrg_def)
 apply (simp add:prod_zero_def)
 apply (rule funcset_eq [of _ "{j. j \<le> n}"])
 apply (simp add:extensional_def restrict_def)+
 apply (rule allI, rule impI) 
 apply (simp add:Ring.qring_zero)
 apply (frule_tac a = xa in forall_spec, assumption,
        thin_tac "\<forall>k \<le> n. ideal A (J k)")
 apply (subst pj_mem [of "A"], assumption+)
 apply (frule_tac I = "J xa" and a = x in Ring.a_in_ar_coset [of "A"], 
        assumption+) 
 apply (rule_tac a = x and I = "J xa" in Ring.Qring_fix1 [of "A"], assumption+)
 apply blast 
done

lemma (in Ring) coprime_prod_int2Tr:
"((\<forall>k \<le> (Suc n). ideal R (J k)) \<and> 
 (\<forall>i \<le> (Suc n). \<forall>j \<le> (Suc n). (i \<noteq>j \<longrightarrow> coprime_ideals R (J i) (J j))))
  \<longrightarrow> (\<Inter> {I. \<exists>k \<le> (Suc n). I = (J k)} = ideal_n_prod R (Suc n) J)"
apply (induct_tac n)
apply (rule impI)
 apply (erule conjE) 
 apply (simp add:Nset_1) 
 apply (subst coprime_int_prod [THEN sym, of "J 0" "J (Suc 0)"], simp+)
 apply (rule equalityI, rule subsetI)
 apply (simp, blast)
 apply (rule subsetI, simp, rule allI, rule impI, erule exE, (erule conjE)+)
 apply simp
 apply (simp add:Nset_1_1, erule disjE, (simp del:ideal_n_prodSn)+)

(** n **)
apply (rule impI)
 apply (subgoal_tac "\<Inter>{I. \<exists>k \<le> (Suc (Suc n)). I = J k} =
              (\<Inter>{I. \<exists>k \<le> (Suc n). I = J k}) \<inter> (J (Suc (Suc n)))")
 apply (subgoal_tac "\<Inter>{I. \<exists>k \<le> (Suc n). I = J k} = (i\<Pi>\<^bsub>R,(Suc n)\<^esub> J)")
(* apply (simp del:ideal_n_prodSn)*) 
 apply (frule_tac n = "Suc n" and J = J in coprime_n_idealsTr4)
  apply (simp del:ideal_n_prodSn)
 apply (subst coprime_int_prod)
 apply (rule n_prod_ideal)
 apply (rule allI, simp, simp, assumption) 
 apply simp apply (cut_tac n = "Suc n" in Nsetn_sub_mem1)
 apply simp
 apply (thin_tac "(\<forall>k\<le>Suc n. ideal R (J k)) \<and>
         (\<forall>i\<le>Suc n. \<forall>j\<le>Suc n. i \<noteq> j \<longrightarrow> coprime_ideals R (J i) (J j)) \<longrightarrow>
         \<Inter>{I. \<exists>k\<le>Suc n. I = J k} = i\<Pi>\<^bsub>R,Suc n\<^esub> J",
        thin_tac "(\<forall>k\<le>Suc (Suc n). ideal R (J k)) \<and>
         (\<forall>i\<le>Suc (Suc n).
             \<forall>j\<le>Suc (Suc n). i \<noteq> j \<longrightarrow> coprime_ideals R (J i) (J j))")
 apply (rule equalityI, rule subsetI, simp)
 apply (rule conjI,
        rule allI, rule impI, erule exE, erule conjE, simp,
        frule_tac a = xa in forall_spec,
        frule_tac x = k and y = "Suc n" and z = "Suc (Suc n)" in 
        le_less_trans, simp,
        frule_tac x = k and y = "Suc (Suc n)" in less_imp_le, blast)
 apply simp 
 apply (frule_tac a = "J (Suc (Suc n))" in forall_spec,
        cut_tac n = "Suc (Suc n)" in le_refl, blast, simp)
 
 apply (rule subsetI, simp, rule allI, rule impI)
 apply (erule exE, erule conjE)
 apply (erule conjE, 
        case_tac "k = Suc (Suc n)", simp)
 apply (frule_tac m = k and n = "Suc (Suc n)" in noteq_le_less, assumption,
        thin_tac "k \<le> Suc (Suc n)")
 apply (frule_tac x = k and n = "Suc n" in Suc_less_le)
 apply (frule_tac a = xa in forall_spec, 
        blast,
        thin_tac "\<forall>xa. (\<exists>k\<le>Suc n. xa = J k) \<longrightarrow> x \<in> xa",
        simp)
done

lemma (in Ring) coprime_prod_int2:"\<lbrakk> \<forall>k \<le> (Suc n). ideal R (J k); 
 \<forall>i \<le> (Suc n). \<forall>j \<le> (Suc n). (i \<noteq>j \<longrightarrow> coprime_ideals R (J i) (J j))\<rbrakk>
 \<Longrightarrow> (\<Inter> {I. \<exists>k \<le> (Suc n). I = (J k)} = ideal_n_prod R (Suc n) J)"
apply (simp add:coprime_prod_int2Tr)
done

lemma (in Ring) coprime_2_n:"\<lbrakk>ideal R A; ideal R B\<rbrakk> \<Longrightarrow>
 (qring R A) \<Oplus>\<^sub>r (qring R B) = r\<Pi>\<^bsub>{j. j \<le> (Suc 0)}\<^esub> (prodB1 (qring R A) (qring R B))"
apply (simp add:Prod2Rg_def Nset_1)
done

text\<open>In this and following lemmata, ideals A and B are of type 
       \<open>('a, 'more) RingType_scheme\<close>. Don't try 
       \<open>(r\<Pi>\<^sub>(Nset n) B) \<Oplus>\<^sub>r B (Suc n)\<close>\<close>

lemma (in Ring) A_to_prodag2_hom:"\<lbrakk>ideal R A; ideal R B; S 0 = pj R A; 
      S (Suc 0) = pj R B\<rbrakk>  \<Longrightarrow> 
      A_to_prodag R {j. j \<le> (Suc 0)} S (prodB1 (qring R A) (qring R B)) \<in> 
      rHom R (qring R A \<Oplus>\<^sub>r qring R B)"
apply (subst coprime_2_n [of "A" "B"], assumption+)
apply (rule A_to_prodag_rHom, rule Ring_axioms)
apply (rule ballI)
apply (case_tac "k = 0")
apply (simp add:prodB1_def)
apply (simp add:qring_ring)
apply (simp)
 apply (frule_tac n = k in Suc_leI[of 0], thin_tac "0 < k")
 apply (frule_tac m = k and n = "Suc 0" in le_antisym, assumption)
 apply (simp, simp add:prodB1_def, simp add:qring_ring)

apply (rule ballI)
 apply (simp add:Nset_1)
 apply (erule disjE) 
 apply (simp add:prodB1_def, rule pj_Hom, rule Ring_axioms, assumption)
 apply (simp, simp add:prodB1_def)
 apply (rule pj_Hom, rule Ring_axioms, assumption+)
done

lemma (in Ring) A2coprime_rsurjecTr:"\<lbrakk>ideal R A; ideal R B; S 0 = pj R A; 
      S (Suc 0) = pj R B\<rbrakk> \<Longrightarrow> 
      (carrier (qring R A \<Oplus>\<^sub>r qring R B)) = 
        carr_prodag {j. j \<le> (Suc 0)} (prodB1 (qring R A) (qring R B))"
apply (simp add:Prod2Rg_def prodrg_def Nset_1)
done

lemma (in Ring) A2coprime_rsurjec:"\<lbrakk>ideal R A; ideal R B; S 0 = pj R A; 
      S (Suc 0) = pj R B; coprime_ideals R A B\<rbrakk> \<Longrightarrow> 
      surjec\<^bsub>R,((qring R A) \<Oplus>\<^sub>r (qring R B))\<^esub> 
           (A_to_prodag R {j. j\<le>(Suc 0)} S (prodB1 (qring R A) (qring R B)))"
apply (frule A_to_prodag2_hom [of "A" "B" "S"], assumption+)
apply (simp add:surjec_def)
apply (rule conjI, 
       simp add:rHom_def)
apply (rule surj_to_test[of "A_to_prodag R {j. j \<le> (Suc 0)} S 
       (prodB1 (qring R A) (qring R B))" "carrier R" 
        "carrier (qring R A \<Oplus>\<^sub>r qring R B)"])
 apply (simp add:rHom_def aHom_def)

 apply (rule ballI)
 apply (frule rHom_func[of "A_to_prodag R {j. j \<le> (Suc 0)} S 
                                   (prodB1 (R /\<^sub>r A) (R /\<^sub>r B))" R],
        thin_tac "A_to_prodag R {j. j \<le> (Suc 0)} S (prodB1 (R /\<^sub>r A) (R /\<^sub>r B))
         \<in> rHom R (R /\<^sub>r A \<Oplus>\<^sub>r R /\<^sub>r B)")
 apply (simp add:A2coprime_rsurjecTr[of A B S])
 apply (simp add:Nset_1)
 apply (frule_tac X = "b 0" and Y = "b (Suc 0)" in 
                  coprime_surjTr[of A B], assumption+)
 apply (simp add:carr_prodag_def prodB1_def,
        simp add:carr_prodag_def prodB1_def) 

 apply (erule bexE)
 apply (frule_tac x = r in funcset_mem[of "A_to_prodag R {0, Suc 0} S 
        (prodB1 (R /\<^sub>r A) (R /\<^sub>r B))"
         "carrier R" "carr_prodag {0, Suc 0} (prodB1 (R /\<^sub>r A) (R /\<^sub>r B))"],
         assumption+)
 apply (cut_tac X = "A_to_prodag R {0, Suc 0} S (prodB1 (R /\<^sub>r A) (R /\<^sub>r B)) r" 
        and Y = b in 
        carr_prodag_mem_eq[of "{0, Suc 0}" "prodB1 (R /\<^sub>r A) (R /\<^sub>r B)"])
  apply (rule ballI)
  apply (simp, erule disjE)
  apply (simp add:prodB1_def, fold prodB1_def, 
                                simp add:qring_ring Ring.ring_is_ag)
  apply (simp add:prodB1_def, fold prodB1_def, 
                               simp add:qring_ring Ring.ring_is_ag)
  apply assumption+
  apply (rule ballI, simp, erule disjE, simp)
  apply (subst A_to_prodag_def, simp)
  apply (subst A_to_prodag_def, simp)
 apply blast
done

lemma (in Ring) prod2_n_Tr1:"\<lbrakk>\<forall>k \<le> (Suc 0). ideal R (J k); 
      \<forall>k \<le> (Suc 0). B k = qring R (J k); 
      \<forall>k \<le> (Suc 0). S k = pj R (J k) \<rbrakk>  \<Longrightarrow> 
    A_to_prodag R {j. j \<le> (Suc 0)} S 
            (prodB1 (qring R (J 0)) (qring R (J (Suc 0)))) = 
                               A_to_prodag R {j. j \<le> (Suc 0)} S B"
apply (subgoal_tac "\<forall>k \<le> (Suc 0). (prodB1 (qring R (J 0)) (qring R (J (Suc 0)))) k = B k") 
apply (simp add:A_to_prodag_def)
apply (rule allI, rule impI)
 apply (case_tac "k = 0", simp add:Nset_1_1)
 apply (simp add:prodB1_def)
 apply (simp add:Nset_1_1)
 apply (simp add:prodB1_def)
done  

lemma (in aGroup) restrict_prod_Suc:"\<lbrakk>\<forall>k \<le> (Suc (Suc n)). ideal R (J k);
        \<forall>k \<le> (Suc (Suc n)). B k = R /\<^sub>r J k;
        \<forall>k \<le> (Suc (Suc n)). S k = pj R (J k);
        f \<in> carrier (r\<Pi>\<^bsub>{j. j \<le> (Suc (Suc n))}\<^esub> B)\<rbrakk> \<Longrightarrow> 
        restrict f {j. j \<le> (Suc n)} \<in> carrier (r\<Pi>\<^bsub>{j. j \<le> (Suc n)}\<^esub> B)"
apply (cut_tac Nsetn_sub_mem1[of "Suc n"])
 apply (simp add:prodrg_def) 
 apply (simp add:carr_prodag_def, (erule conjE)+)
 apply (simp add:Un_carrier_def)
 apply (rule Pi_I)
 apply simp
 apply (frule_tac x = x in funcset_mem[of f "{j. j \<le> (Suc (Suc n))}"
        "\<Union>{X. \<exists>i \<le> (Suc (Suc n)). X = carrier (R /\<^sub>r J i)}"],
        simp)
 apply simp
 apply (erule exE, erule conjE, erule exE, erule conjE, simp)
 
 apply (rotate_tac -5) 
 apply (frule_tac a = x in forall_spec) apply simp
 apply blast
done

lemma (in Ring) Chinese_remTr2:"(\<forall>k \<le> (Suc n). ideal R (J k)) \<and> 
     (\<forall>k\<le>(Suc n). B k = qring R (J k)) \<and> 
     (\<forall>k\<le>(Suc n). S k = pj R (J k)) \<and> 
     (\<forall>i\<le>(Suc n). \<forall>j\<le> (Suc n). (i \<noteq>j \<longrightarrow> 
     coprime_ideals R (J i) (J j))) \<longrightarrow> 
     surjec\<^bsub>R,(r\<Pi>\<^bsub>{j. j\<le> (Suc n)}\<^esub> B)\<^esub> 
                   (A_to_prodag R {j. j\<le>(Suc n)} S B)"
apply (cut_tac Ring)
apply (induct_tac n)
(* case n = 0, i.e. two coprime_ideals *)  (** use coprime_surjTr **)
apply (rule impI) apply (erule conjE)+
 apply (frule  A_to_prodag_rHom [of R "{j. j \<le> Suc 0}" "B" "S"])
 apply (rule ballI, simp add:Ring.qring_ring)
 apply (rule ballI, simp add:pj_Hom) 
 apply (frule rHom_func[of "A_to_prodag R {j. j \<le> (Suc 0)} S B" R 
                           "r\<Pi>\<^bsub>{j. j \<le> (Suc 0)}\<^esub> B"])
 apply (simp add:surjec_def)  
  apply (rule conjI)
  apply (simp add:rHom_def)
 apply (rule surj_to_test, assumption+)
 apply (rule ballI) apply (simp add:Nset_1) 
 apply (cut_tac coprime_elems [of "J 0" "J (Suc 0)"])
 apply (rename_tac f)
 apply (erule bexE, erule bexE)
 apply (simp add:prodrg_def) apply (fold prodrg_def)
 apply (cut_tac X = "f 0" and Y = "f (Suc 0)" in 
                  coprime_surjTr[of "J 0" "J (Suc 0)"], simp+)
 apply (simp add:carr_prodag_def, simp add:carr_prodag_def)
 apply (erule bexE, (erule conjE)+)
 apply (frule_tac x = r in funcset_mem[of "A_to_prodag R {0, Suc 0} S B"
        "carrier R" "carr_prodag {0, Suc 0} B"], assumption+)
 apply (cut_tac X = "A_to_prodag R {0, Suc 0} S B r" and Y = f in 
         carr_prodag_mem_eq[of "{0, Suc 0}" B])
  apply (rule ballI, simp, erule disjE, simp add:qring_ring 
                           Ring.ring_is_ag,
         simp add:Ring.qring_ring Ring.ring_is_ag)
  apply assumption+
  apply (rule ballI, simp, erule disjE, simp)
  apply (simp add:A_to_prodag_def, simp add:A_to_prodag_def)
  apply blast apply simp+
 
 apply (rule impI, (erule conjE)+)
 
(**** n ****)
 apply (cut_tac n = "Suc n" in Nsetn_sub_mem1)
apply (subgoal_tac "\<forall>k\<in>{i. i \<le> Suc (Suc n)}. Ring (B k)")
apply (frule_tac I = "{i. i \<le> Suc (Suc n)}"  in A_to_prodag_rHom [of "R" _ "B" "S"])
 apply assumption 
 apply (rule ballI)
 apply (simp add:pj_Hom)
 apply simp
 apply (subst surjec_def, rule conjI,
        simp add:rHom_def)
 apply (cut_tac n = "Suc n" in coprime_n_idealsTr4[of  _ J])
 apply blast
 apply (frule_tac f = "A_to_prodag R {j. j \<le> (Suc (Suc n))} S B" and 
        A = R in rHom_func)
 apply (rule_tac f = "A_to_prodag R {j. j \<le> (Suc (Suc n))} S B" and
        A = "carrier R" and B = "carrier (r\<Pi>\<^bsub>{j. j \<le> (Suc (Suc n))}\<^esub> B)" in
        surj_to_test, assumption+)
 apply (rule ballI)
 apply (cut_tac n = "Suc n" in n_prod_ideal[of  _ J])
 apply (rule allI, simp)
 apply (frule_tac A = "i\<Pi>\<^bsub>R,(Suc n)\<^esub> J" and B = "J (Suc (Suc n))" in 
        coprime_elems,
        cut_tac n = "Suc (Suc n)" in n_in_Nsetn,
        blast, assumption)
 apply (erule bexE, erule bexE) apply (rename_tac n f a b)
 apply (thin_tac " coprime_ideals R (i\<Pi>\<^bsub>R,(Suc n)\<^esub> J) (J (Suc (Suc n)))")
 apply (cut_tac n = "Suc n" and a = a and J = J in ele_n_prod,
        rule allI, simp, assumption)

 apply (cut_tac ring_is_ag)
 apply (frule_tac n = n and f = f in aGroup.restrict_prod_Suc[of R _ R J B S],
          assumption+)
 apply (frule_tac S = "r\<Pi>\<^bsub>{j. j \<le> (Suc n)}\<^esub> B" and 
        f = "A_to_prodag R {j. j \<le> (Suc n)} S B" in surjec_surj_to[of R]) 
 apply (frule_tac f = "A_to_prodag R {j. j \<le> (Suc n)} S B" and A = "carrier R"
        and B = "carrier (r\<Pi>\<^bsub>{j. j \<le>  (Suc n)}\<^esub> B)" and 
        b = "restrict f {j. j \<le> (Suc n)}" in surj_to_el2, assumption)
 apply (erule bexE, rename_tac n f a b u)
 apply (cut_tac n = "Suc (Suc n)" in n_in_Nsetn,
        frule_tac f = f and I = "{j. j \<le> (Suc (Suc n))}" and A = B and 
         i = "Suc (Suc n)" in prodrg_component, assumption)  
 apply simp
 apply (frule_tac J = "J (Suc (Suc n))" and X = "f (Suc (Suc n))" in 
                pj_surj_to[of R], simp, assumption)
 apply (erule bexE, rename_tac n f a b u v)
 apply (frule_tac a = "Suc (Suc n)" in forall_spec, simp,
        frule_tac I = "J (Suc (Suc n))" and h = b in Ring.ideal_subset[of R],
        assumption+,
        cut_tac I = "i\<Pi>\<^bsub>R,n\<^esub> J \<diamondsuit>\<^sub>r\<^bsub>R\<^esub> J (Suc n)" and h = a in 
                       Ring.ideal_subset[of R], assumption+)
 apply (frule_tac x = b and y = u in  Ring.ring_tOp_closed[of R], assumption+,
        frule_tac x = a and y = v in  Ring.ring_tOp_closed[of R], assumption+,
       frule Ring.ring_is_ag[of R],
       frule_tac x = "b \<cdot>\<^sub>r\<^bsub>R\<^esub> u" and y = "a \<cdot>\<^sub>r\<^bsub>R\<^esub> v" in aGroup.ag_pOp_closed[of R],
       assumption+)
 apply (frule_tac f = "A_to_prodag R {j. j \<le> (Suc (Suc n))} S B" and 
        A = "carrier R" and B = "carrier (r\<Pi>\<^bsub>{j. j \<le> (Suc (Suc n))}\<^esub> B)" and
        x = "b \<cdot>\<^sub>r\<^bsub>R\<^esub> u \<plusminus>\<^bsub>R\<^esub> a \<cdot>\<^sub>r\<^bsub>R\<^esub> v" in funcset_mem, assumption+)
apply (frule_tac f = "A_to_prodag R {j. j \<le> (Suc (Suc n))} S B 
                       (b \<cdot>\<^sub>r\<^bsub>R\<^esub> u \<plusminus>\<^bsub>R\<^esub> a \<cdot>\<^sub>r\<^bsub>R\<^esub> v)" and I = "{j. j \<le> (Suc (Suc n))}"
           and  g = f in carr_prodrg_mem_eq, simp)    
 apply (rule ballI)
 apply (subst A_to_prodag_def, simp)
 apply (frule_tac I = "J i" in pj_Hom[of R], simp)
 apply (simp add: rHom_add)
 apply (frule_tac a = i in forall_spec, assumption,
        thin_tac "\<forall>k \<le> (Suc (Suc n)). ideal R (J k)",
        frule_tac I = "J i" in Ring.qring_ring[of R], assumption,
        thin_tac "\<forall>k \<le> (Suc (Suc n)). Ring (R /\<^sub>r J k)",
        frule_tac R = "R /\<^sub>r (J i)" and x = b and y = u and f = "pj R (J i)" in
         rHom_tOp[of R], assumption+, simp,
     thin_tac "pj R (J i) (b \<cdot>\<^sub>r\<^bsub>R\<^esub> u) = pj R (J i) b \<cdot>\<^sub>r\<^bsub>R /\<^sub>r J i\<^esub> pj R (J i) u",
     frule_tac R = "R /\<^sub>r (J i)" and x = a and y = v and f = "pj R (J i)" in
     rHom_tOp[of R], simp add:Ring.qring_ring, assumption+)
  apply (frule_tac f = "pj R (J i)" and R = "R /\<^sub>r J i" and a = v in
                    rHom_mem[of _ R], assumption+,
         frule_tac f = "pj R (J i)" and R = "R /\<^sub>r J i" and a = u in
                    rHom_mem[of _ R], assumption+,
         frule_tac f = "pj R (J i)" and R = "R /\<^sub>r J i" and a = b in
                    rHom_mem[of _ R], assumption+,
         frule_tac f = "pj R (J i)" and R = "R /\<^sub>r J i" and a = a in
                    rHom_mem[of _ R], assumption+)
      apply (frule_tac R = "R /\<^sub>r J i" in Ring.ring_is_ag)
  apply (case_tac "i \<le> (Suc n)")
  apply (frule_tac I1 = "J i" and x1 = a in pj_zero[THEN sym, of R ],
            assumption+, simp,
    thin_tac "pj R (J i) (a \<cdot>\<^sub>r\<^bsub>R\<^esub> v) = \<zero>\<^bsub>R /\<^sub>r J i\<^esub> \<cdot>\<^sub>r\<^bsub>R /\<^sub>r J i\<^esub> pj R (J i) v")
         apply (simp add:Ring.ring_times_0_x) 
  apply (frule_tac f = "pj R (J i)" and A = R and R = "R /\<^sub>r J i" and
                 x = a and y = b in rHom_add, assumption+, simp,
         thin_tac "A_to_prodag R {j. j \<le> Suc (Suc n)} S B
         (b \<cdot>\<^sub>r u) \<plusminus>\<^bsub>r\<Pi>\<^bsub>{i. i \<le> Suc (Suc n)}\<^esub> B\<^esub>
        A_to_prodag R {j. j \<le> Suc (Suc n)} S B (a \<cdot>\<^sub>r v)
        \<in> carrier (r\<Pi>\<^bsub>{j. j \<le> Suc (Suc n)}\<^esub> B)")

  apply (simp add:aGroup.ag_l_zero)
  apply (rotate_tac -1, frule sym, thin_tac " pj R (J i) 1\<^sub>r\<^bsub>R\<^esub> = pj R (J i) b",
         simp add:rHom_one) apply (simp add:Ring.ring_l_one)
         apply (simp add:aGroup.ag_r_zero)
  apply (frule_tac f = "A_to_prodag R {j. j \<le> (Suc n)} S B u" and 
          g = "restrict f {j. j \<le> (Suc n)}" and x = i in eq_fun_eq_val,
    thin_tac "A_to_prodag R {j. j\<le>(Suc n)} S B u = restrict f {j. j\<le>(Suc n)}")
  apply (simp add:A_to_prodag_def) 
  apply simp
  apply (frule_tac y = i and x = "Suc n" in not_le_imp_less, 
         frule_tac m = "Suc n" and n = i in Suc_leI,
         frule_tac m = i and n = "Suc (Suc n)" in Nat.le_antisym, assumption+,
         simp)
  apply (frule_tac I1 = "J (Suc (Suc n))" and x1 = b in pj_zero[THEN sym, of
          R ],  assumption+, simp add:Ring.ring_times_0_x) 
   apply (frule_tac f = "pj R (J (Suc (Suc n)))" and A = R and 
          R = "R /\<^sub>r J (Suc (Suc n))" and
                 x = a and y = b in rHom_add, assumption+, simp)      
   apply (simp add:aGroup.ag_r_zero)
   apply (rotate_tac -1, frule sym, 
          thin_tac "pj R (J (Suc (Suc n))) 1\<^sub>r\<^bsub>R\<^esub> = pj R (J (Suc (Suc n))) a",
          simp add:rHom_one,
          simp add:Ring.ring_l_one)
   apply (simp add:aGroup.ag_l_zero)

   apply blast
   apply (rule ballI, simp add:Ring.qring_ring)
done

lemma (in Ring) Chinese_remTr3:"\<lbrakk>\<forall>k \<le> (Suc n). ideal R (J k); 
      \<forall>k \<le> (Suc n). B k = qring R (J k); \<forall>k\<le> (Suc n). S k = pj R (J k); 
  \<forall>i \<le> (Suc n). \<forall>j \<le> (Suc n). (i \<noteq>j \<longrightarrow> coprime_ideals R (J i) (J j))\<rbrakk> \<Longrightarrow>
    surjec\<^bsub>R,(r\<Pi>\<^bsub>{j. j \<le> (Suc n)}\<^esub> B)\<^esub> 
                   (A_to_prodag R {j. j \<le> (Suc n)} S B)"
apply (simp add:Chinese_remTr2 [of  "n" "J" "B" "S"])
done

lemma (in Ring) imset:"\<lbrakk>\<forall>k\<le> (Suc n). ideal R (J k)\<rbrakk>
\<Longrightarrow> {I. \<exists>k\<le> (Suc n). I = J k} = {J k| k. k \<in> {j. j \<le> (Suc n)}}"
apply blast
done

theorem (in Ring) Chinese_remThm:"\<lbrakk>(\<forall>k \<le> (Suc n). ideal R (J k)); 
 \<forall>k\<le>(Suc n). B k = qring R (J k); \<forall>k \<le> (Suc n). S k = pj R (J k); 
 \<forall>i \<le> (Suc n). \<forall>j \<le> (Suc n). (i \<noteq>j \<longrightarrow> coprime_ideals R (J i) (J j))\<rbrakk> 
\<Longrightarrow> bijec\<^bsub>(qring R (\<Inter> {J k | k. k\<in>{j. j \<le> (Suc n)}})),(r\<Pi>\<^bsub>{j. j \<le> (Suc n)}\<^esub> B)\<^esub> 
     ((A_to_prodag R {j. j \<le> (Suc n)} S B)\<degree>\<^bsub>R,(prodrg {j. j \<le> (Suc n)} B)\<^esub>)"
apply (frule Chinese_remTr3, assumption+)
apply (cut_tac I = "{j. j \<le> (Suc n)}" and A = B in prodrg_ring)
  apply (rule ballI, simp add:qring_ring)
apply (cut_tac surjec_ind_bijec [of "R" "r\<Pi>\<^bsub>{j. j \<le> (Suc n)}\<^esub> B" 
                   "A_to_prodag R {j. j \<le> (Suc n)} S B"])
apply (cut_tac Ring,
       simp add:Chinese_remTr1 [of "R" "Suc n" "J" "B" "S"])
apply (simp add:imset, rule Ring_axioms, assumption+)
apply (rule A_to_prodag_rHom, rule Ring_axioms)
 apply (rule ballI)
 apply (simp add:qring_ring)
 apply (rule ballI, simp, rule pj_Hom, rule Ring_axioms, simp)
 apply assumption
done

lemma (in Ring) prod_prime:"\<lbrakk>ideal R A; \<forall>k\<le>(Suc n). prime_ideal R (P k);
      \<forall>l\<le>(Suc n). \<not> (A \<subseteq> P l); 
      \<forall>k\<le> (Suc n). \<forall>l\<le> (Suc n). k = l \<or> \<not> (P k) \<subseteq> (P l)\<rbrakk> \<Longrightarrow> 
     \<forall>i \<le> (Suc n). (nprod R (ppa R P A i) n \<in> A \<and> 
        (\<forall>l \<in> {j. j\<le>(Suc n)} - {i}. nprod R (ppa R P A i) n \<in> P l) \<and> 
        (nprod R (ppa R P A i) n \<notin> P i))"
apply (rule allI, rule impI)
apply (rule conjI)
apply (frule_tac i = i in prod_primeTr1[of n P A], assumption+)
apply (frule_tac n = n and f = "ppa R P A i" in ideal_nprod_inc[of  A])
  apply (rule allI, rule impI)
  apply (rotate_tac -2, 
         frule_tac a = ia in forall_spec, assumption,
         thin_tac "\<forall>l \<le> n.
           ppa R P A i l \<in> A \<and>
           ppa R P A i l \<in> P (skip i l) \<and> ppa R P A i l \<notin> P i",
         simp add:ideal_subset)
  apply (rotate_tac -1, 
         frule_tac a = n in forall_spec, simp,
         thin_tac "\<forall>l\<le> n.
            ppa R P A i l \<in> A \<and>
            ppa R P A i l \<in> P (skip i l) \<and> ppa R P A i l \<notin> P i",
         (erule conjE)+, 
         blast, assumption)
apply (frule_tac i = i in prod_primeTr1[of n P A], assumption+)
apply (rule conjI)
 apply (rule ballI)
 apply (frule_tac a = l in forall_spec, simp,
        frule_tac I = "P l" in prime_ideal_ideal) 
apply (frule_tac n = n and f = "ppa R P A i" and A = "P l" in ideal_nprod_inc)
 apply (rule allI) apply (simp add:ppa_mem, simp)
 apply (case_tac "l < i",
        thin_tac "\<forall>l\<le> (Suc n). \<not> A \<subseteq> P l",
        thin_tac "\<forall>k\<le> (Suc n). \<forall>l \<le> (Suc n). k = l \<or> \<not> P k \<subseteq> P l")
  apply (erule conjE,
         frule_tac x = l and y = i and z = "Suc n" in less_le_trans,
         assumption,
         frule_tac x = l and n = n in Suc_less_le)
  apply (rotate_tac 2, 
         frule_tac a = l in forall_spec, assumption,
         thin_tac "\<forall>l\<le>n. ppa R P A i l \<in> A \<and>
                 ppa R P A i l \<in> P (skip i l) \<and> ppa R P A i l \<notin> P i",
         thin_tac "l < Suc n")
  apply (simp only:skip_im_Tr1_2, blast)
  apply (frule_tac x = l and y = i in leI,
         thin_tac "\<not> l < i",
         cut_tac x = l and A = "{j. j \<le> (Suc n)}" and a = i in in_diff1)
         apply simp  
         apply (erule conjE,
         frule not_sym, thin_tac "l \<noteq> i",
         frule_tac x = i and y = l in le_imp_less_or_eq,
         erule disjE, thin_tac "i \<le> l",
         frule_tac x = i and n = l in less_le_diff) 
  apply (cut_tac i = i and n = n and x = "l - Suc 0" in skip_im_Tr2_1,
         simp, assumption+, simp,
         frule_tac x = l and n = n in le_Suc_diff_le) 
  apply (rotate_tac -7,
         frule_tac a = "l - Suc 0" in forall_spec, assumption,
         thin_tac "\<forall>l\<le>n. ppa R P A i l \<in> A \<and>
                 ppa R P A i l \<in> P (skip i l) \<and> ppa R P A i l \<notin> P i",
         simp, (erule conjE)+)
  apply blast
  apply simp
  apply assumption
    apply (frule_tac a = i in forall_spec, assumption,
           thin_tac "\<forall>k\<le> (Suc n). prime_ideal R (P k)") 
    apply (rule_tac P = "P i" and n = n and f = "ppa R P A i" in
             prime_nprod_exc, assumption+)
    apply (rule allI, rule impI)
    apply (rotate_tac -3, 
           frule_tac a = ia in forall_spec, assumption,
           thin_tac "\<forall>l \<le> n.
           ppa R P A i l \<in> A \<and>
           ppa R P A i l \<in> P (skip i l) \<and> ppa R P A i l \<notin> P i",
           simp add:ideal_subset)
    apply (rule allI, rule impI) apply (
           rotate_tac 4,
           frule_tac a = l in forall_spec, assumption,
           thin_tac "\<forall>l\<le> n.
            ppa R P A i l \<in> A \<and>
            ppa R P A i l \<in> P (skip i l) \<and> ppa R P A i l \<notin> P i",
           simp)
done

lemma skip_im1:"\<lbrakk>i \<le> (Suc n); P \<in> {j. j \<le> (Suc n)} \<rightarrow> Collect (prime_ideal R)\<rbrakk>
    \<Longrightarrow>
   compose {j. j \<le> n} P (skip i) ` {j. j \<le> n} = P ` ({j. j \<le> (Suc n)} - {i})"
apply (cut_tac skip_fun[of i n])
apply (subst setim_cmpfn[of _ _ _ _ "{X. prime_ideal R X}"], assumption+)
apply  simp
apply (simp add:skip_fun_im)
done

lemma (in Ring) mutch_aux1:"\<lbrakk>ideal R A; i \<le> (Suc n);
        P \<in> {j. j \<le> (Suc n)} \<rightarrow> Collect (prime_ideal R)\<rbrakk> \<Longrightarrow> 
        compose {j. j \<le> n} P (skip i) \<in> {j. j \<le> n} \<rightarrow> Collect (prime_ideal R)"
apply (cut_tac skip_fun[of i n])
apply (simp add:composition[of "skip i" "{j. j \<le> n}" "{j. j \<le> (Suc n)}" P 
            "Collect (prime_ideal R)"])
done

lemma (in Ring) prime_ideal_cont1Tr:"ideal R A  \<Longrightarrow> 
      \<forall>P. ((P \<in> {j. j \<le> (n::nat)} \<rightarrow> {X. prime_ideal R X}) \<and> 
                   (A \<subseteq> \<Union> (P ` {j. j \<le> n}))) \<longrightarrow> (\<exists>i\<le> n. A \<subseteq> (P i))"
apply (induct_tac n)
 apply (rule allI, rule impI)
 apply (erule conjE)
 apply simp 
(** n **)
apply (rule allI, rule impI)
 apply (erule conjE)+ 
 apply (case_tac "\<exists>i \<le> (Suc n). \<exists>j\<le> (Suc n). (i \<noteq> j \<and> P i \<subseteq> P j)")
 apply ((erule exE, erule conjE)+, erule conjE)
 apply (frule_tac f = P and n = n and X = "{X. prime_ideal R X}" and
         A = A and i = i and j = j in Un_less_Un, assumption+, simp+)
 apply (frule mutch_aux1, assumption+)
 apply (frule_tac a = "compose {j. j \<le> n} P (skip i)" in forall_spec,
        simp, erule exE)
 apply (cut_tac i = i and n = n and x = ia in skip_fun_im1,
               simp+, erule conjE, simp add:compose_def,blast)
 (** last_step induction assumption is of no use **)
apply (thin_tac "\<forall>P. P \<in> {j. j \<le> n} \<rightarrow> {X. prime_ideal R X} \<and>
               A \<subseteq> \<Union>(P ` {j. j \<le> n}) \<longrightarrow>
               (\<exists>i\<le>n. A \<subseteq> P i)",
       rule contrapos_pp, simp+)
 apply (cut_tac n = n and P = P in prod_prime [of A], assumption)
 apply (rule allI, rule impI,
     frule_tac f = P and A = "{j. j \<le> (Suc n)}" and B = "{X. prime_ideal R X}"
     and x = k in funcset_mem, simp, simp, assumption+) 
 apply (frule_tac n = "Suc n" and 
        f = "\<lambda>i\<in>{j. j \<le> (Suc n)}. (nprod R (ppa R P A i) n)" in 
        nsum_ideal_inc[of A], rule allI, rule impI, simp)
 apply (subgoal_tac "(nsum R (\<lambda>i\<in>{j. j \<le> (Suc n)}. nprod R (ppa R P A i) n) 
        (Suc n)) \<notin> (\<Union>x\<in>{j. j \<le> (Suc n)}. P x)")
 apply blast
 apply (simp del:nsum_suc)
 apply (rule allI, rule impI) apply (rename_tac n P l)
  apply (frule_tac f = P and A = "{j. j \<le> (Suc n)}" and 
         B = "{X. prime_ideal R X}"
         and x = l in funcset_mem, simp, simp del:nsum_suc,
         frule_tac I = "P l" in prime_ideal_ideal)
  apply (rule_tac A = "P l" and n = "Suc n" and 
         f = "\<lambda>i\<in>{j. j \<le> (Suc n)}. (nprod R (ppa R P A i) n)" in 
         nsum_ideal_exc, simp+, rule allI, simp add:ideal_subset)
  apply (rule contrapos_pp, simp+)
  apply (rotate_tac -1,
         frule_tac a = l in forall_spec, simp,
         thin_tac "\<forall>j\<le>Suc n.
           (\<exists>la\<in>{i. i \<le> Suc n} - {j}. e\<Pi>\<^bsub>R,n\<^esub> ppa R P A la \<notin> P l) \<or>
           e\<Pi>\<^bsub>R,n\<^esub> ppa R P A j \<in> P l",
         thin_tac "\<forall>i\<le>Suc n. \<forall>j\<le>Suc n. i = j \<or> \<not> P i \<subseteq> P j",
         thin_tac "\<forall>i\<le>Suc n. \<not> A \<subseteq> P i")
  apply (erule disjE, erule bexE) 
  apply (frule_tac a = la in forall_spec, simp,
         thin_tac "\<forall>i\<le>Suc n.
           e\<Pi>\<^bsub>R,n\<^esub> ppa R P A i \<in> A \<and>
           (\<forall>l\<in>{j. j \<le> Suc n} - {i}. e\<Pi>\<^bsub>R,n\<^esub> ppa R P A i \<in> P l) \<and>
           e\<Pi>\<^bsub>R,n\<^esub> ppa R P A i \<notin> P i",
           (erule conjE)+)
  apply blast
  apply blast
done
 
lemma (in Ring) prime_ideal_cont1:"\<lbrakk>ideal R A; \<forall>i \<le> (n::nat). 
     prime_ideal R (P i); A \<subseteq> \<Union> {X. (\<exists>i \<le> n. X = (P i))} \<rbrakk> \<Longrightarrow> 
     \<exists>i\<le> n. A\<subseteq>(P i)"
apply (frule prime_ideal_cont1Tr[of A n])
apply (frule_tac a = P in forall_spec,
       thin_tac "\<forall>P. P \<in> {j. j \<le> n} \<rightarrow> {X. prime_ideal R X} \<and> 
       A \<subseteq> \<Union>(P ` {j. j \<le> n}) \<longrightarrow> (\<exists>i\<le>n. A \<subseteq> P i)")
apply (rule conjI, simp,
       rule subsetI, simp,
       frule_tac c = x in subsetD[of A "\<Union>{X. \<exists>i\<le>n. X = P i}"], assumption+,
       simp, blast)
apply assumption
done

lemma (in Ring) prod_n_ideal_contTr0:"(\<forall>l\<le> n. ideal R (J l)) \<longrightarrow>
                               i\<Pi>\<^bsub>R,n\<^esub> J  \<subseteq>  \<Inter>{X. (\<exists>k\<le>n. X = (J k))}"
apply (induct_tac n)
 apply simp 

 apply (rule impI)
 apply (cut_tac n = n in Nsetn_sub_mem1,
         simp)
 apply (cut_tac n = n in n_prod_ideal[of _ J], simp)
 apply (cut_tac I = "i\<Pi>\<^bsub>R,n\<^esub> J" and J = "J (Suc n)" in 
             ideal_prod_sub_Int) apply assumption apply simp
 apply (frule_tac A = "i\<Pi>\<^bsub>R,n\<^esub> J \<diamondsuit>\<^sub>r\<^bsub>R\<^esub> J (Suc n)" and 
        B = "i\<Pi>\<^bsub>R,n\<^esub> J \<inter> J (Suc n)" and
        C = "\<Inter>{X. \<exists>k\<le> n. X = J k} \<inter> J (Suc n)" in subset_trans)
 apply (rule_tac A = "i\<Pi>\<^bsub>R,n\<^esub> J" and B = "\<Inter>{X. \<exists>k\<le>n. X = J k}" and 
        C = "J (Suc n)" in inter_mono, assumption)
 apply (rule_tac A = "i\<Pi>\<^bsub>R,n\<^esub> J \<diamondsuit>\<^sub>r J (Suc n)" and
                 B = "\<Inter>{X. \<exists>k\<le> n. X = J k} \<inter> J (Suc n)" and
                 C = "\<Inter>{X. \<exists>k\<le> (Suc n). X = J k}" in subset_trans,
         assumption)
 apply (rule subsetI)
  apply simp 
  apply (rule allI, rule impI) 
  apply (erule exE, (erule conjE)+)
  apply (case_tac "k = Suc n", simp)
  apply (frule_tac m = k and n = "Suc n" in noteq_le_less, assumption)
  apply (thin_tac " k \<le> Suc n")
  apply (frule_tac x = k and n = "Suc n" in less_le_diff,
         thin_tac "k < Suc n", simp, thin_tac "\<forall>l\<le>Suc n. ideal R (J l)")
  apply (frule_tac a = xa in forall_spec, blast,
         thin_tac "\<forall>xa. (\<exists>k\<le>n. xa = J k) \<longrightarrow> x \<in> xa",
         simp)
done

lemma (in Ring) prod_n_ideal_contTr:"\<lbrakk>\<forall>l\<le> n. ideal R (J l)\<rbrakk> \<Longrightarrow>
             i\<Pi>\<^bsub>R,n\<^esub> J  \<subseteq>  \<Inter>{X. (\<exists>k \<le> n. X = (J k))}"
apply (simp add:prod_n_ideal_contTr0)
done

lemma (in Ring) prod_n_ideal_cont2:"\<lbrakk>\<forall>l\<le> (n::nat). ideal R (J l); 
     prime_ideal R P; \<Inter>{X. (\<exists>k\<le> n. X = (J k))} \<subseteq> P\<rbrakk> \<Longrightarrow> 
     \<exists>l\<le> n. (J l) \<subseteq> P"
apply (frule prod_n_ideal_contTr[of n J])
apply (frule_tac A = "i\<Pi>\<^bsub>R,n\<^esub> J" and B = "\<Inter>{X. \<exists>k\<le> n. X = J k}" and C = P 
       in subset_trans, assumption+)
apply (thin_tac "\<Inter>{X. \<exists>k\<le> n. X = J k} \<subseteq> P",
       thin_tac "i\<Pi>\<^bsub>R,n\<^esub> J \<subseteq> \<Inter>{X. \<exists>k\<le> n. X = J k}")
 apply (simp add:ideal_n_prod_prime)
done

lemma (in Ring) prod_n_ideal_cont3:"\<lbrakk>\<forall>l\<le> (n::nat). ideal R (J l); 
      prime_ideal R P; \<Inter>{X. (\<exists>k\<le> n. X = (J k))} = P\<rbrakk> \<Longrightarrow> 
      \<exists>l\<le> n. (J l) = P"
apply (frule prod_n_ideal_cont2[of n J P], assumption+)
 apply simp
 apply (erule exE)
 apply (subgoal_tac "J l = P")
 apply blast
apply (rule equalityI, simp)
 apply (rule subsetI)
 apply (rotate_tac -4, frule sym, thin_tac "\<Inter>{X. \<exists>k\<le> n. X = J k} = P") 
 apply simp
 apply blast
done

definition
  ideal_quotient :: "[_ , 'a set, 'a set] \<Rightarrow> 'a set" where
  "ideal_quotient R A B = {x| x. x \<in> carrier R \<and> (\<forall>b\<in>B. x \<cdot>\<^sub>r\<^bsub>R\<^esub> b \<in> A)}"

abbreviation
  IDEALQT  ("(3_/ \<dagger>\<^sub>_/ _)" [82,82,83]82) where
  "A \<dagger>\<^sub>R B == ideal_quotient R A B"


lemma (in Ring) ideal_quotient_is_ideal:
  "\<lbrakk>ideal R A; ideal R B\<rbrakk> \<Longrightarrow> ideal R (ideal_quotient R A B)"
apply (rule ideal_condition)
 apply (rule subsetI) 
 apply (simp add:ideal_quotient_def CollectI)
 apply (simp add:ideal_quotient_def)
 apply (cut_tac ring_zero)
 apply (subgoal_tac "\<forall>b\<in>B. \<zero> \<cdot>\<^sub>r b \<in> A")
 apply blast
 apply (rule ballI)
 apply (frule_tac h = b in ideal_subset[of B], assumption)
 apply (frule_tac x = b in ring_times_0_x )
 apply (simp add:ideal_zero)
apply (rule ballI)+
 apply (simp add:ideal_quotient_def, (erule conjE)+,
        rule conjI)
 apply (rule ideal_pOp_closed)
 apply (simp add:whole_ideal, assumption+)
 apply (cut_tac ring_is_ag)
 apply (simp add:aGroup.ag_mOp_closed)
apply (rule ballI)
apply (subst ring_distrib2) 
 apply (simp add:ideal_subset, assumption)
 apply (cut_tac ring_is_ag, simp add: aGroup.ag_mOp_closed)
 apply (frule_tac a1 = y and b1 = b in ring_inv1_1 [THEN sym])
 apply (simp add:ideal_subset, simp)
 apply (rule ideal_pOp_closed, assumption+, simp)
 apply (rule ideal_inv1_closed, assumption+, simp) 
apply (rule ballI)+
 apply (simp add:ideal_quotient_def)
 apply (rule conjI) 
  apply (erule conjE) 
  apply (simp add:ring_tOp_closed)
 apply (erule conjE)
apply (rule ballI)
 apply (subst ring_tOp_assoc, assumption+, simp add:ideal_subset)
 apply (simp add:ideal_ring_multiple [of "A"])
done

section \<open>Addition of finite elements of a ring and \<open>ideal_multiplication\<close>\<close>
text\<open>We consider sum in an abelian group\<close>

lemma (in aGroup) nsum_mem1Tr:" A +> J  \<Longrightarrow>  
                     (\<forall>j \<le> n. f j \<in> J)  \<longrightarrow> nsum A f n \<in> J"
apply (induct_tac n)
 apply (rule impI) 
 apply simp
apply (rule impI) 
 apply simp
 apply (rule asubg_pOp_closed, assumption+)
 apply simp
done

lemma (in aGroup) fSum_mem:"\<lbrakk>\<forall>j \<in> nset (Suc n) m. f j \<in> carrier A; n < m\<rbrakk> \<Longrightarrow>
                   fSum A f (Suc n) m \<in> carrier A" 
apply (simp add:fSum_def)
apply (rule nsum_mem)
apply (rule allI, simp add:cmp_def slide_def)
apply (rule impI)
apply (frule_tac x = "Suc (n + j)" in bspec)
 apply (simp add:nset_def, arith)
done

lemma (in aGroup) nsum_mem1:"\<lbrakk>A +> J; \<forall>j \<le> n. f j \<in> J\<rbrakk> \<Longrightarrow> nsum A f n \<in> J"
apply (simp add:nsum_mem1Tr)
done 
   
lemma (in aGroup) nsum_eq_i:"\<lbrakk>\<forall>j\<le>n. f j \<in> carrier A; \<forall>j\<le>n. g j \<in> carrier A;
 i \<le> n; \<forall>l \<le> i. f l = g l\<rbrakk> \<Longrightarrow> nsum A f i = nsum A g i"
apply (rule nsum_eq)
apply (rule allI, rule impI, simp)+
done

lemma (in aGroup) nsum_cmp_eq:"\<lbrakk>f \<in> {j. j\<le>(n::nat)} \<rightarrow> carrier A; 
 h1 \<in> {j. j \<le> n} \<rightarrow> {j. j \<le> n};  h2 \<in> {j. j \<le> n} \<rightarrow> {j. j \<le> n}; i \<le> n\<rbrakk> \<Longrightarrow>
 nsum A (cmp f (cmp h2 h1)) i = nsum A (cmp (cmp f h2) h1) i"
apply (rule nsum_eq_i [of n "cmp f (cmp h2 h1)" "cmp (cmp f h2) h1" i])
apply (rule allI, rule impI, simp add:cmp_def)
apply ((rule funcset_mem, assumption)+, simp) 
apply (rule allI, rule impI, simp add:cmp_def,
        (rule funcset_mem, assumption)+, simp+)
apply (rule allI, rule impI, simp add:cmp_def)
done

lemma (in aGroup) nsum_cmp_eq_transpos:"\<lbrakk> \<forall>j\<le>(Suc n). f j \<in> carrier A; 
       i \<le> n;i \<noteq> n \<rbrakk> \<Longrightarrow>
 nsum A (cmp f (cmp (transpos i n) (cmp (transpos n (Suc n)) (transpos i n))))
 (Suc n) = nsum A (cmp f (transpos i (Suc n))) (Suc n)" 
apply (rule nsum_eq [of "Suc n" "cmp f (cmp (transpos i n) 
                            (cmp (transpos n (Suc n)) (transpos i n)))" 
       "cmp f (transpos i (Suc n))"])
apply (rule allI, rule impI)
apply (simp add:cmp_def)
apply (cut_tac i = i and n = "Suc n" and j = n and l = j in transpos_mem,
       simp+) 
apply (cut_tac i = n and n = "Suc n" and j = "Suc n" and l = "transpos i n j"
        in transpos_mem, simp+)
apply (cut_tac i = i and n = "Suc n" and j = n and
        l = "transpos n (Suc n) (transpos i n j)" in transpos_mem,
       simp+) 
apply (rule allI, rule impI, simp add:cmp_def)
apply (cut_tac i = i and n = "Suc n" and j = "Suc n" and l = j in transpos_mem,
       simp+)
apply (rule allI, rule impI)
 apply (simp add:cmp_def)
 apply (thin_tac "\<forall>j\<le>Suc n. f j \<in> carrier A",
        rule eq_elems_eq_val[of _ _ f])
 apply (simp add:transpos_def)
done

lemma transpos_Tr_n1:"Suc (Suc 0) \<le> n \<Longrightarrow> 
                           transpos (n - Suc 0) n n = n - Suc 0"
apply (simp add:transpos_def)
done

lemma transpos_Tr_n2:"Suc (Suc 0) \<le> n \<Longrightarrow> 
               transpos (n - (Suc 0)) n (n - (Suc 0)) = n"
apply (simp add:transpos_def) 
done

lemma (in aGroup) additionTr0:"\<lbrakk>0 < n; \<forall>j \<le> n. f j \<in> carrier A\<rbrakk>
 \<Longrightarrow> nsum A (cmp f (transpos (n - 1) n)) n = nsum A f n" 
apply (case_tac "n \<le> 1")
 apply simp
 apply (frule Suc_leI [of "0" "n"])
 apply (frule le_antisym [of "n" "Suc 0"], assumption+, simp)
 apply (simp add:cmp_def)
 apply (subst transpos_ij_1[of 0 "Suc 0"], simp+)
 apply (subst transpos_ij_2[of 0 "Suc 0"], simp+)
 apply (rule ag_pOp_commute, simp+)
 apply (frule not_le_imp_less[of n "Suc 0"])
apply (frule_tac Suc_leI [of "Suc 0" "n"],
       thin_tac "\<not> n \<le> Suc 0")
 apply (cut_tac nsum_suc[of A f "n - Suc 0"], simp)
 apply (cut_tac nsum_suc[of A "cmp f (transpos (n - Suc 0) n)" "n - Suc 0"], 
        simp,
        thin_tac "\<Sigma>\<^sub>e A f n = \<Sigma>\<^sub>e A f (n - Suc 0) \<plusminus> f n",
        thin_tac "\<Sigma>\<^sub>e A (cmp f (transpos (n - Suc 0) n)) n =
     \<Sigma>\<^sub>e A (cmp f (transpos (n - Suc 0) n)) (n - Suc 0) \<plusminus>
     (cmp f (transpos (n - Suc 0) n) n)")
apply (case_tac "n = Suc (Suc 0)", simp)
 apply (cut_tac transpos_id_1[of "Suc 0" "Suc (Suc 0)" "Suc (Suc 0)" 0],
        cut_tac transpos_ij_1[of "Suc 0" "Suc (Suc 0)" "Suc (Suc 0)"],
        cut_tac transpos_ij_2[of "Suc 0" "Suc (Suc 0)" "Suc (Suc 0)"],
        simp add:cmp_def,
        thin_tac "n = Suc (Suc 0)",
        thin_tac "transpos (Suc 0) (Suc (Suc 0)) 0 = 0",
        thin_tac "transpos (Suc 0) (Suc (Suc 0)) (Suc 0) = Suc (Suc 0)",
        thin_tac "transpos (Suc 0) (Suc (Suc 0)) (Suc (Suc 0)) = Suc 0")
 apply (subst ag_pOp_assoc, simp+)
 apply (subst ag_pOp_commute[of "f (Suc (Suc 0))" "f (Suc 0)"], simp+)
  apply (subst ag_pOp_assoc[THEN sym], simp+)

 apply (frule not_sym)
 apply (frule noteq_le_less[of "Suc (Suc 0)" n], assumption,
        thin_tac "Suc (Suc 0) \<le> n")
 apply (cut_tac nsum_suc[of A f "n - Suc 0 - Suc 0"])
 apply (cut_tac Suc_pred[of "n - Suc 0"], simp del:nsum_suc)
 apply (cut_tac nsum_suc[of A "cmp f (transpos (n - Suc 0) n)"  
                "n - Suc (Suc 0)"], simp del:nsum_suc,
     thin_tac "\<Sigma>\<^sub>e A f (n - Suc 0) = \<Sigma>\<^sub>e A f (n - Suc (Suc 0)) \<plusminus> f (n - Suc 0)",
     thin_tac "Suc (n - Suc (Suc 0)) = n - Suc 0",
     thin_tac "\<Sigma>\<^sub>e A (cmp f (transpos (n - Suc 0) n)) (n - Suc 0) =
     \<Sigma>\<^sub>e A (cmp f (transpos (n - Suc 0) n)) (n - Suc (Suc 0)) \<plusminus>
     (cmp f (transpos (n - Suc 0) n)) (n - Suc 0)")
 apply (cut_tac nsum_eq_i[of n "cmp f (transpos (n - Suc 0) n)" f 
                 "n - Suc (Suc 0)"], simp,   
        thin_tac "\<Sigma>\<^sub>e A (cmp f (transpos (n - Suc 0) n)) (n - Suc (Suc 0)) =
     \<Sigma>\<^sub>e A f (n - Suc (Suc 0))")
 apply (simp add:cmp_def)
 apply (cut_tac transpos_ij_1[of "n - Suc 0" n n], simp)
 apply (cut_tac transpos_ij_2[of "n - Suc 0" n n], simp) 
 apply (subst ag_pOp_assoc,
        rule nsum_mem, rule allI, rule impI)
 apply (frule_tac x = j and y = "n - Suc (Suc 0)" and z = n in 
        le_less_trans, simp, frule_tac x = j and y = n in less_imp_le)
        apply simp+
 apply (subst ag_pOp_commute[of "f n"], simp, simp)
 apply (subst ag_pOp_assoc[THEN sym],
         rule nsum_mem, rule allI, rule impI,
         frule_tac x = j and y = "n - Suc (Suc 0)" and z = n in 
         le_less_trans, simp, frule_tac x = j and y = n in less_imp_le)
        apply simp+ 

 apply (rule allI, rule impI, simp add:cmp_def)
 apply (cut_tac i = "n - Suc 0" and n = n and j = n and l = j in transpos_mem,
        simp+) 
 
 apply (rule allI, rule impI)
 apply (simp add:cmp_def)
 apply (cut_tac i = "n - Suc 0" and n = n and j = n and x = l in transpos_id,
        simp+) 

 apply (cut_tac x = l and y = "n - Suc (Suc 0)" and z = n in le_less_trans,
        assumption) apply simp
 apply arith
 apply simp
 apply arith
done

lemma (in aGroup) additionTr1:"\<lbrakk> \<forall>f. \<forall>h. f \<in> {j. j\<le>(Suc n)} \<rightarrow> carrier A \<and>
       h \<in> {j. j\<le>(Suc n)} \<rightarrow> {j. j\<le>(Suc n)} \<and> inj_on h {j. j\<le>(Suc n)} \<longrightarrow>
       nsum A (cmp f h) (Suc n) = nsum A f (Suc n); 
       f \<in> {j. j\<le>(Suc (Suc n))} \<rightarrow> carrier A; 
       h \<in> {j. j\<le>(Suc (Suc n))} \<rightarrow> {j. j\<le>(Suc (Suc n))}; 
       inj_on h {j. j\<le>(Suc (Suc n))}; h (Suc (Suc n)) = Suc (Suc n)\<rbrakk>
        \<Longrightarrow> nsum A (cmp f h) (Suc (Suc n)) = nsum A f (Suc (Suc n))"
apply (subgoal_tac "f \<in> {j. j\<le>(Suc n)} \<rightarrow> carrier A")
apply (subgoal_tac "h \<in> {j. j\<le>(Suc n)} \<rightarrow> {j. j\<le>(Suc n)}")
apply (subgoal_tac "inj_on h {j. j\<le>(Suc n)}")
apply (subgoal_tac "nsum A (cmp f h) (Suc n) = nsum A f (Suc n)")
apply (thin_tac "\<forall>f. \<forall>h. f \<in> {j. j\<le>(Suc n)} \<rightarrow> carrier A \<and>
       h \<in> {j. j\<le>(Suc n)} \<rightarrow> {j. j\<le>(Suc n)} \<and> inj_on h {j. j\<le>(Suc n)} \<longrightarrow>
       nsum A (cmp f h) (Suc n) = nsum A f (Suc n)")
prefer 2 apply simp
apply simp
 apply (thin_tac "nsum A (cmp f h) n \<plusminus> (cmp f h (Suc n)) =  nsum A f n \<plusminus> (f (Suc n))")
 apply (simp add:cmp_def)
 apply (thin_tac "\<forall>f h. (f \<in> {j. j \<le> Suc n} \<rightarrow> carrier A) \<and>
           (h \<in> {j. j\<le>Suc n} \<rightarrow> {j. j\<le>Suc n}) \<and> (inj_on h {j. j\<le>Suc n}) \<longrightarrow>
           \<Sigma>\<^sub>e A (cmp f h) (Suc n) = \<Sigma>\<^sub>e A f (Suc n)")
 apply (frule Nset_injTr0 [of "h" "Suc n"], assumption+, simp) 
 apply (frule Nset_injTr0 [of "h" "Suc n"], assumption+, simp)
apply (simp add:Pi_def)
done

lemma (in aGroup) additionTr1_1:"\<lbrakk>\<forall>f. \<forall>h. f \<in> {j. j\<le>Suc n} \<rightarrow> carrier A \<and>
      h \<in> {j. j\<le>Suc n} \<rightarrow> {j. j\<le>Suc n} \<and> inj_on h {j. j\<le>Suc n} \<longrightarrow>
      nsum A (cmp f h) (Suc n) = nsum A f (Suc n); 
      f \<in> {j. j\<le>Suc (Suc n)} \<rightarrow> carrier A; i \<le> n\<rbrakk> \<Longrightarrow> 
    nsum A (cmp f (transpos i (Suc n))) (Suc (Suc n)) = nsum A f (Suc (Suc n))"
apply (rule additionTr1 [of "n" "f" "transpos i (Suc n)"], assumption+)
apply (rule transpos_hom [of "i" "Suc (Suc n)" "Suc n"])
 apply simp+
 apply (rule transpos_inj [of "i" "Suc (Suc n)" "Suc n"])
  apply simp+ 
  apply (subst transpos_id[of i "Suc (Suc n)" "Suc n" "Suc (Suc n)"])
  apply simp+
done

lemma (in aGroup) additionTr1_2:"\<lbrakk>\<forall>f. \<forall>h. f \<in> {j. j\<le>Suc n} \<rightarrow> carrier A \<and>
          h \<in> {j. j\<le>Suc n} \<rightarrow> {j. j\<le>Suc n} \<and> 
          inj_on h {j. j\<le>Suc n} \<longrightarrow>
          nsum A (cmp f h) (Suc n) = nsum A f (Suc n); 
         f \<in> {j. j\<le> Suc (Suc n)} \<rightarrow> carrier A; i \<le> (Suc n)\<rbrakk> \<Longrightarrow> 
       nsum A (cmp f (transpos i (Suc (Suc n)))) (Suc (Suc n)) = 
                                             nsum A f (Suc (Suc n))"
apply (case_tac "i = Suc n")
 apply (simp del:nsum_suc) 
 apply (cut_tac additionTr0 [of "Suc (Suc n)" "f"], simp, simp,
         rule allI, rule impI, rule funcset_mem[of f "{j. j \<le> Suc (Suc n)}"
         "carrier A"], (simp del:nsum_suc)+)
 apply (subst nsum_cmp_eq_transpos [THEN sym, of "Suc n" f i],
        rule allI, rule impI, rule funcset_mem[of f "{j. j \<le> Suc (Suc n)}" 
        "carrier A"], assumption+,
        simp, assumption+)
 apply (subst nsum_cmp_eq [of "f" "Suc (Suc n)"  
        "cmp (transpos (Suc n) (Suc(Suc n))) (transpos i (Suc n))" 
        "transpos i (Suc n)" "Suc (Suc n)"], assumption+,
        rule Pi_I, simp add:cmp_def,
        rule transpos_mem, (simp del:nsum_suc)+,
        rule transpos_mem, (simp del:nsum_suc)+,
        rule Pi_I, simp,
        rule transpos_mem, (simp del:nsum_suc)+)
apply (subst nsum_cmp_eq [of "cmp f (transpos i (Suc n))" "Suc (Suc n)"  
       "(transpos i (Suc n))" "transpos (Suc n) (Suc (Suc n))" "Suc (Suc n)"],
       rule Pi_I, simp add:cmp_def,
       rule funcset_mem[of f "{j. j \<le> Suc (Suc n)}" "carrier A"], assumption,
       simp,
       rule transpos_mem, (simp del:nsum_suc)+,
       (rule Pi_I, simp,
        rule transpos_mem, (simp del:nsum_suc)+)+)

apply (subst additionTr1_1 [of "n" "cmp (cmp f (transpos i (Suc n)))
               (transpos (Suc n) (Suc (Suc n)))" "i"], assumption+,
       rule  cmp_fun [of _ "{j. j \<le> (Suc (Suc n))}" 
                       "{j. j \<le> (Suc (Suc n))}" _ "carrier A"],
       rule transpos_hom, simp, simp, simp,
       rule cmp_fun [of _ "{j. j \<le> (Suc (Suc n))}" 
                       "{j. j \<le> (Suc (Suc n))}" "f" "carrier A"],
       rule transpos_hom, simp, simp, assumption+, arith)
apply (cut_tac additionTr0 [of  "Suc (Suc n)" "cmp f (transpos i (Suc n))"],
       simp del:nsum_suc,
       thin_tac "nsum A (cmp 
  (cmp f (transpos i (Suc n))) (transpos (Suc n) (Suc (Suc n)))) (Suc (Suc n))
  = nsum A (cmp f (transpos i (Suc n))) (Suc (Suc n))")
apply (rule additionTr1_1, assumption+, arith, simp,
       rule allI, rule impI, simp add:cmp_def,
       rule funcset_mem[of f "{j. j \<le> Suc (Suc n)}" "carrier A"],
       assumption)
apply (simp add:transpos_mem)
done

lemma (in aGroup) additionTr2:" \<forall>f. \<forall>h. f \<in> {j. j \<le> (Suc n)} \<rightarrow> carrier A \<and> 
        h \<in> {j. j \<le> (Suc n)} \<rightarrow> {j. j \<le> (Suc n)} \<and> 
        inj_on h {j. j \<le> (Suc n)} \<longrightarrow> 
          nsum A (cmp f h) (Suc n) = nsum A f (Suc n)" 
apply (induct_tac n) 
 apply (rule allI)+
 apply (rule impI, (erule conjE)+)
 apply (simp add:cmp_def)
 apply (case_tac "h 0 = 0")
  apply (simp add:Nset_1)
  apply (simp add:Nset_1 ag_pOp_commute)

(************* n *****************)
apply (rule allI)+
apply (rule impI, (erule conjE)+)
apply (case_tac "h (Suc (Suc n)) = Suc (Suc n)") 
apply (rule additionTr1, assumption+)
apply (frule_tac f = h and n = "Suc (Suc n)" in inj_surj, assumption+)
 apply (frule sym, thin_tac "h ` {i. i \<le> Suc (Suc n)} = {i. i \<le> Suc (Suc n)}")
 apply (cut_tac n = "Suc (Suc n)" in n_in_Nsetn)
 apply (frule_tac a = "Suc (Suc n)" and A = "{i. i \<le> Suc (Suc n)}" and 
        B = "h ` {i. i \<le> Suc (Suc n)}" in eq_set_inc, assumption+)
 apply (thin_tac "{i. i \<le> Suc (Suc n)} = h ` {i. i \<le> Suc (Suc n)}")
 apply (simp del:nsum_suc add:image_def) 
 apply (erule exE, erule conjE)
 apply (frule sym, thin_tac "Suc (Suc n) = h x")
 apply (frule_tac i = x and n = "Suc (Suc n)" and j = "Suc (Suc n)" in 
                  transpos_ij_2, simp del:nsum_suc add:n_in_Nsetn)
        apply (rule contrapos_pp, (simp del:nsum_suc)+)
 apply (frule_tac x = "transpos x (Suc (Suc n)) (Suc (Suc n))" and y = x and 
        f = h in eq_elems_eq_val,
        thin_tac "transpos x (Suc (Suc n)) (Suc (Suc n)) = x",           
        simp del:nsum_suc)
 apply (frule_tac f = h and A = "{i. i \<le> Suc (Suc n)}" and x = x and 
                  y = "Suc (Suc n)" in inj_onTr2, simp, simp,
        frule not_sym, simp)
 apply (cut_tac f1 = "cmp f h" and n1 = n and i1 = x in 
        additionTr1_2[THEN sym], assumption)
 apply (rule cmp_fun, simp, assumption, arith)
 apply (simp del:nsum_suc,
        thin_tac "\<Sigma>\<^sub>e A (cmp f h) (Suc (Suc n)) =
        \<Sigma>\<^sub>e A (cmp (cmp f h) (transpos x (Suc (Suc n)))) (Suc (Suc n))")
 apply (frule_tac f = f and n = "Suc n" and A = "carrier A" in func_pre)
 apply (cut_tac f = "cmp h (transpos x (Suc (Suc n)))" and A = "{j. j \<le> (Suc (        Suc n))}" and ?A1.0 = "{j. j \<le> (Suc n)}" in restrict_inj)
 apply (rule_tac f = "transpos x (Suc (Suc n))" and A = "{j. j \<le> Suc (Suc n)}"
 and B = "{j. j \<le> Suc (Suc n)}" and g = h and C = "{j. j \<le> Suc (Suc n)}" in
  cmp_inj, simp,
  rule transpos_hom, simp, simp, assumption+,
  rule transpos_inj, simp, simp, assumption+,
  rule subsetI, simp)
apply (subst nsum_cmp_assoc,
       rule allI, rule impI, simp add:Pi_def,
       rule transpos_hom, assumption, simp, assumption+)
 apply (cut_tac f = "cmp f (cmp h (transpos x (Suc (Suc n))))" and n = "Suc n"
        in nsum_suc[of A ], simp del:nsum_suc,
   thin_tac "\<Sigma>\<^sub>e A (cmp f (cmp h (transpos x (Suc (Suc n))))) (Suc (Suc n)) =
        \<Sigma>\<^sub>e A (cmp f (cmp h (transpos x (Suc (Suc n))))) (Suc n) \<plusminus>
        cmp f (cmp h (transpos x (Suc (Suc n)))) (Suc (Suc n))")
 apply (frule_tac x = f in spec,
        thin_tac "\<forall>f h. f \<in> {j. j \<le> Suc n} \<rightarrow> carrier A \<and>
              h \<in> {j. j \<le> Suc n} \<rightarrow> {j. j \<le> Suc n} \<and>
              inj_on h {j. j \<le> Suc n} \<longrightarrow>
              \<Sigma>\<^sub>e A (cmp f h) (Suc n) = \<Sigma>\<^sub>e A f (Suc n)")
 apply (frule_tac a = "cmp h (transpos x (Suc (Suc n)))" in forall_spec,
        thin_tac "\<forall>h. f \<in> {j. j \<le> Suc n} \<rightarrow> carrier A \<and>
         h \<in> {j. j \<le> Suc n} \<rightarrow> {j. j \<le> Suc n} \<and> inj_on h {j. j \<le> Suc n} \<longrightarrow>
         \<Sigma>\<^sub>e A (cmp f h) (Suc n) = \<Sigma>\<^sub>e A f (Suc n)")
 apply simp
 apply (rule Pi_I)
 apply (simp add:cmp_def)
 apply (case_tac "xa = x", simp)
 apply (cut_tac i = x and n = "Suc (Suc n)" and j = "Suc (Suc n)" in 
         transpos_ij_1, simp, simp, simp, simp,
        frule_tac x = "Suc (Suc n)" and f = h and A = "{j. j \<le> Suc (Suc n)}"
         and B = "{j. j \<le> Suc (Suc n)}" in funcset_mem, simp,
        thin_tac "h \<in> {j. j \<le> Suc (Suc n)} \<rightarrow> {j. j \<le> Suc (Suc n)}")
 apply (cut_tac m = "h (Suc (Suc n))" and n = "Suc (Suc n)" in noteq_le_less,
        simp, simp,
        rule_tac x = "h (Suc (Suc n))" and n = "Suc n" in Suc_less_le,
        assumption)
 apply (subst transpos_id, simp, simp, simp, simp,
        frule_tac x = xa and f = h and A = "{j. j \<le> Suc (Suc n)}" and 
        B = "{j. j \<le> Suc (Suc n)}" in funcset_mem, simp)
 apply (frule_tac f = h and A = "{j. j \<le> Suc (Suc n)}" and x = xa and y = x 
        in injective, simp, simp, assumption)
 apply (cut_tac m = "h xa" and n = "Suc (Suc n)" in noteq_le_less, simp,
        simp)
 apply (rule Suc_less_le, assumption,
        thin_tac "\<forall>h. f \<in> {j. j \<le> Suc n} \<rightarrow> carrier A \<and>
        h \<in> {j. j \<le> Suc n} \<rightarrow> {j. j \<le> Suc n} \<and> inj_on h {j. j \<le> Suc n} \<longrightarrow>
        \<Sigma>\<^sub>e A (cmp f h) (Suc n) = \<Sigma>\<^sub>e A f (Suc n)")
 apply (simp del:nsum_suc add:cmp_def)
 apply simp
done

lemma (in aGroup) addition2:"\<lbrakk>f \<in> {j. j \<le> (Suc n)} \<rightarrow> carrier A; 
  h \<in> {j. j \<le> (Suc n)} \<rightarrow> {j. j \<le> (Suc n)}; inj_on h {j. j \<le> (Suc n)}\<rbrakk> \<Longrightarrow>
  nsum A (cmp f h) (Suc n) = nsum A f (Suc n)"
apply (simp del:nsum_suc add:additionTr2)
done

lemma (in aGroup) addition21:"\<lbrakk>f \<in> {j. j \<le> n} \<rightarrow> carrier A; 
       h \<in> {j. j \<le> n} \<rightarrow> {j. j \<le> n}; inj_on h {j. j \<le> n}\<rbrakk> \<Longrightarrow>
       nsum A (cmp f h) n = nsum A f n"
apply (case_tac "n = 0")
 apply (simp add: cmp_def)
 apply (cut_tac f = f and n = "n - Suc 0" and h = h in addition2)
 apply simp+
done

lemma (in aGroup) addition3:"\<lbrakk>\<forall>j \<le> (Suc n). f j \<in> carrier A; j \<le> (Suc n);
j \<noteq> Suc n\<rbrakk> \<Longrightarrow> nsum A f (Suc n) = nsum A (cmp f (transpos j (Suc n))) (Suc n)"
apply (rule addition2 [THEN sym,of "f" "n" "transpos j (Suc n)"])
apply (simp)
apply (rule transpos_hom, assumption+, simp, assumption)
apply (rule transpos_inj, simp+)
done

lemma (in aGroup) nsum_splitTr:"(\<forall>j \<le> (Suc (n + m)). f j \<in> carrier A) \<longrightarrow>
   nsum A f (Suc (n + m)) = nsum A f n \<plusminus> (nsum A (cmp f (slide (Suc n))) m)" 
apply (induct_tac m)
apply (rule impI) apply (simp add:slide_def cmp_def)
apply (rule impI, simp del:nsum_suc)

apply (cut_tac n = "Suc (n + na)" in nsum_suc[of A f],
       simp del:nsum_suc,
       thin_tac "\<Sigma>\<^sub>e A f (Suc (Suc (n + na))) =
       \<Sigma>\<^sub>e A f n \<plusminus> \<Sigma>\<^sub>e A (cmp f (slide (Suc n))) na \<plusminus> f (Suc (Suc (n + na)))")
apply (cut_tac f = "cmp f (slide (Suc n))" and n = na in nsum_suc[of A],
       simp del:nsum_suc)
apply (subst ag_pOp_assoc)
apply (rule nsum_mem, rule allI, simp) 
 apply (rule_tac n = na in nsum_mem, 
        thin_tac "\<Sigma>\<^sub>e A (cmp f (slide (Suc n))) (Suc na) =
          \<Sigma>\<^sub>e A (cmp f (slide (Suc n))) na \<plusminus> (cmp f (slide (Suc n)) (Suc na))")
 apply (rule allI, rule impI,
        simp add:cmp_def slide_def, simp)
 apply (simp add:cmp_def slide_def)
done

lemma (in aGroup) nsum_split:"\<forall>j \<le> (Suc (n + m)). f j \<in> carrier A \<Longrightarrow>
   nsum A f (Suc (n + m)) = nsum A f n \<plusminus> (nsum A (cmp f (slide (Suc n))) m)"  
by (simp del:nsum_suc add:nsum_splitTr)                                     

lemma (in aGroup) nsum_split1:"\<lbrakk>\<forall>j \<le> m. f j \<in> carrier A; n < m\<rbrakk> \<Longrightarrow>
                   nsum A f m = nsum A f n \<plusminus> (fSum A f (Suc n) m)"
apply (cut_tac nsum_split[of n "m - n - Suc 0" f])
apply simp
apply (simp add:fSum_def)
apply simp
done

lemma (in aGroup) nsum_minusTr:" (\<forall>j \<le> n. f j \<in> carrier A) \<longrightarrow>
                    -\<^sub>a (nsum A f n) = nsum A (\<lambda>x\<in>{j. j \<le> n}. -\<^sub>a (f x)) n"
apply (induct_tac n)
 apply (rule impI, simp)
apply (rule impI)
 apply (subst nsum_suc, subst nsum_suc)
 apply (subst ag_p_inv) 
 apply (rule_tac n = n in nsum_mem [of _ f],
        rule allI, simp, simp)
 apply (subgoal_tac "\<forall>j\<le>n. f j \<in> carrier A", simp)
 apply (rule_tac a = "\<Sigma>\<^sub>e A (\<lambda>u. if u \<le> n then  -\<^sub>a (f u) else undefined) n"
     and b = "\<Sigma>\<^sub>e A (\<lambda>x\<in>{j. j \<le> (Suc n)}. -\<^sub>a (f x)) n" and c = "-\<^sub>a (f (Suc n))"
     in ag_pOp_add_r,
     rule_tac n = n in nsum_mem,
     rule allI, rule impI, simp,
     rule ag_mOp_closed, simp)
 apply (rule_tac n = n in nsum_mem,
        rule allI, rule impI, simp,
        rule ag_mOp_closed, simp,
        rule ag_mOp_closed, simp) 
 apply (rule_tac f = "\<lambda>u. if u \<le> n then -\<^sub>a (f u) else undefined" and 
        n = n and g = "\<lambda>x\<in>{j. j \<le> (Suc n)}. -\<^sub>a (f x)" in nsum_eq,
        rule allI, rule impI,
        simp, rule ag_mOp_closed, simp,
        rule allI, simp, rule impI, rule ag_mOp_closed, simp) 
 apply (rule allI, simp)
 apply (rule allI, simp)
done

lemma (in aGroup) nsum_minus:"\<forall>j \<le> n. f j \<in> carrier A \<Longrightarrow> 
                    -\<^sub>a (nsum A f n) = nsum A (\<lambda>x\<in>{j. j \<le> n}. -\<^sub>a (f x)) n"
apply (simp add:nsum_minusTr)
done

lemma (in aGroup) ring_nsum_zeroTr:"(\<forall>j \<le> (n::nat). f j \<in> carrier A) \<and> 
                    (\<forall>j \<le> n. f j = \<zero>) \<longrightarrow> nsum A f n = \<zero>"
apply (induct_tac n)
apply (rule impI) apply (erule conjE)+ apply simp

apply (rule impI, (erule conjE)+)
 apply (cut_tac n = n in Nsetn_sub_mem1, simp)
 apply (simp add:ag_inc_zero)
 apply (cut_tac ag_inc_zero,
        simp add:ag_r_zero)
done

lemma (in aGroup) ring_nsum_zero:"\<forall>j \<le> (n::nat). f j = \<zero>  \<Longrightarrow> \<Sigma>\<^sub>e A f n = \<zero>"
apply (cut_tac ring_nsum_zeroTr[of n f])
apply (simp add:ag_inc_zero)
done

lemma (in aGroup) ag_nsum_1_nonzeroTr:
"\<forall>f. (\<forall>j \<le> n. f j \<in> carrier A) \<and> 
       (l \<le> n \<and> (\<forall>j \<in> {j. j \<le> n} - {l}. f j = \<zero>))
      \<longrightarrow> nsum A f n = f l" 
apply (induct_tac n)
      apply simp 
apply (rule allI,
       rule impI, (erule conjE)+)
 apply (case_tac "l = Suc n") 
 apply simp
 apply (subgoal_tac "{j. j \<le> Suc n} - {Suc n} = {j. j \<le> n}", simp,
        frule ring_nsum_zero, simp)
 apply (rule ag_l_zero, simp)
 apply (rule equalityI, rule subsetI, simp,
        rule subsetI, simp)
 apply (frule_tac m = l and n = "Suc n" in noteq_le_less, assumption,
        thin_tac "l \<le> Suc n",
        frule_tac x = l and n = n in Suc_less_le)
 apply (cut_tac n = n in Nsetn_sub_mem1, simp)
 apply (thin_tac "\<forall>f. (\<forall>j\<le>n. f j \<in> carrier A) \<and>
               (\<forall>j\<in>{j. j \<le> n} - {l}. f j = \<zero>) \<longrightarrow>
               \<Sigma>\<^sub>e A f n = f l",
        frule_tac a = l in forall_spec, simp)
 apply (simp add:ag_r_zero)
done
            
lemma (in aGroup) ag_nsum_1_nonzero:"\<lbrakk>\<forall>j \<le> n. f j \<in> carrier A; l \<le> n; 
       \<forall>j\<in>({j. j \<le> n} - {l}). f j = \<zero> \<rbrakk> \<Longrightarrow> nsum A f n = f l"  
apply (simp add:ag_nsum_1_nonzeroTr[of n l])
done

definition
  set_mult :: "[_ , 'a set, 'a set] \<Rightarrow> 'a set" where
  "set_mult R A B = {z. \<exists>x\<in>A. \<exists>y\<in>B.  x \<cdot>\<^sub>r\<^bsub>R\<^esub> y = z}"

definition
  sum_mult :: "[_ , 'a set, 'a set] \<Rightarrow> 'a set" where
  "sum_mult R A B = {x. \<exists>n. \<exists>f \<in> {j. j \<le> (n::nat)}
                           \<rightarrow> set_mult R A B. nsum R f n = x}"  
(*
 zero_fini::"[_ , 'a set, 'a set] \<Rightarrow> (nat \<Rightarrow> 'a)"
     "zero_fini R A B i == \<zero> \<cdot>\<^sub>r \<zero>" *)

lemma (in Ring) set_mult_sub:"\<lbrakk>A \<subseteq> carrier R; B \<subseteq> carrier R\<rbrakk> \<Longrightarrow>
                                    set_mult R A B \<subseteq> carrier R"
apply (rule subsetI, simp add:set_mult_def, (erule bexE)+,
       frule sym, thin_tac "xa \<cdot>\<^sub>r y = x", simp)
apply (rule ring_tOp_closed, (simp add:subsetD)+)
done

lemma (in Ring) set_mult_mono:"\<lbrakk>A1 \<subseteq> carrier R; A2 \<subseteq> carrier R; A1 \<subseteq> A2; 
       B \<subseteq> carrier R\<rbrakk> \<Longrightarrow> set_mult R A1 B \<subseteq> set_mult R A2 B"
apply (rule subsetI)
 apply (simp add:set_mult_def, (erule bexE)+)
 apply (frule_tac c = xa in subsetD[of A1 A2], assumption+)
 apply blast
done
 
lemma (in Ring) sum_mult_Tr1:"\<lbrakk>A \<subseteq> carrier R; B \<subseteq> carrier R\<rbrakk> \<Longrightarrow>
               (\<forall>j \<le> n. f j \<in> set_mult R A B) \<longrightarrow> nsum R f n \<in> carrier R"
apply (cut_tac ring_is_ag)
apply (induct_tac n)
 apply (rule impI, simp)
 apply (frule set_mult_sub[of A B], assumption, simp add:subsetD)
apply (rule impI)
 apply (cut_tac n = n in Nsetn_sub_mem1, simp)
 apply (frule set_mult_sub[of A B], assumption) 
 apply (frule_tac a = "Suc n" in forall_spec, simp,
        frule_tac c = "f (Suc n)" in subsetD[of "set_mult R A B" "carrier R"],
        assumption)
 apply (rule aGroup.ag_pOp_closed, assumption+)
done

lemma (in Ring) sum_mult_mem:"\<lbrakk>A \<subseteq> carrier R; B \<subseteq> carrier R; 
   \<forall>j \<le> n. f j \<in> set_mult R A B\<rbrakk>  \<Longrightarrow> nsum R f n \<in> carrier R"
apply (cut_tac ring_is_ag)
apply (simp add:sum_mult_Tr1)
done

lemma (in Ring) sum_mult_mem1:"\<lbrakk>A \<subseteq> carrier R; B \<subseteq> carrier R; 
        x \<in> sum_mult R A B\<rbrakk>  \<Longrightarrow>
        \<exists>n. \<exists>f\<in>{j. j \<le> (n::nat)} \<rightarrow> set_mult R A B. nsum R f n = x"
by (simp add:sum_mult_def)

lemma (in Ring) sum_mult_subR:"\<lbrakk>A \<subseteq> carrier R; B \<subseteq> carrier R\<rbrakk> \<Longrightarrow>
                         sum_mult R A B \<subseteq> carrier R"
apply (rule subsetI)
apply (frule_tac x = x in sum_mult_mem1[of A B], assumption+)
apply (erule exE, erule bexE, frule sym, thin_tac "\<Sigma>\<^sub>e R f n = x", simp)
apply (cut_tac ring_is_ag)
apply (rule aGroup.nsum_mem[of R], assumption) 
apply (rule allI, rule impI)
apply (frule_tac f = f and A = "{j. j \<le> n}" and B = "set_mult R A B" and
       x = j in funcset_mem, simp) 
apply (frule set_mult_sub[of A B], assumption)
apply (simp add:subsetD)
done

lemma (in Ring) times_mem_sum_mult:"\<lbrakk>A \<subseteq> carrier R; B \<subseteq> carrier R; 
       a \<in> A; b \<in> B \<rbrakk>  \<Longrightarrow>  a \<cdot>\<^sub>r b \<in> sum_mult R A B"
apply (simp add:sum_mult_def)
apply (subgoal_tac "(\<lambda>i\<in>{j. j \<le> (0::nat)}. a \<cdot>\<^sub>r b) \<in> {j. j \<le> 0} \<rightarrow> set_mult R A B") 
apply (subgoal_tac "nsum R (\<lambda>i\<in>{j. j \<le> (0::nat)}. a \<cdot>\<^sub>r b) 0 = a \<cdot>\<^sub>r b") 
apply blast
 apply simp
 apply (rule Pi_I, simp add:set_mult_def, blast)
done

lemma (in Ring) mem_minus_sum_multTr2:"\<lbrakk>A \<subseteq> carrier R; B \<subseteq> carrier R; 
       \<forall>j \<le> n. f j \<in> set_mult R A B; i \<le> n\<rbrakk> \<Longrightarrow> f i \<in> carrier R"
apply (frule_tac a = i in forall_spec, simp)
apply (frule set_mult_sub[of A B], assumption, simp add:subsetD)
done

lemma (in aGroup) nsum_jointfun:"\<lbrakk>\<forall>j \<le> n. f j \<in> carrier A; 
      \<forall>j \<le> m. g j \<in> carrier A\<rbrakk>  \<Longrightarrow> 
      \<Sigma>\<^sub>e A (jointfun n f m g) (Suc (n + m)) =  \<Sigma>\<^sub>e A f n \<plusminus> (\<Sigma>\<^sub>e A g m)"
 apply (subst nsum_split)
 apply (rule allI, rule impI)
 apply (frule_tac f = f and n = n and A = "carrier A" and g = g and m = m
        and B = "carrier A" in jointfun_mem, assumption+, simp)
 apply (subgoal_tac "nsum A (jointfun n f m g) n = nsum A f n")
 apply (subgoal_tac "nsum A (cmp (jointfun n f m g) (slide (Suc n))) m =
                               nsum A g m")
apply simp
 apply (thin_tac "nsum A (jointfun n f m g) n = nsum A f n") 
 apply (rule nsum_eq)
 apply (rule allI, rule impI,
        simp add:cmp_def jointfun_def slide_def sliden_def,
        assumption)
 apply (rule allI, simp add:cmp_def jointfun_def slide_def sliden_def)

 apply (rule nsum_eq)
 apply (rule allI, rule impI,
             simp add:jointfun_def, assumption)
 apply (rule allI, rule impI)
 apply (simp add:jointfun_def) 
done

lemma (in Ring) sum_mult_pOp_closed:"\<lbrakk>A \<subseteq> carrier R; B \<subseteq> carrier R;
       a \<in> sum_mult R A B;  b \<in> sum_mult R A B \<rbrakk> \<Longrightarrow> a \<plusminus>\<^bsub>R\<^esub> b \<in> sum_mult R A B" 
apply (cut_tac ring_is_ag)
apply (simp add:sum_mult_def)
 apply ((erule exE)+, (erule bexE)+)
 apply (rename_tac n m f g) 
 apply (frule sym, thin_tac "\<Sigma>\<^sub>e R f n = a", frule sym, 
        thin_tac "\<Sigma>\<^sub>e R g m = b", simp)
 apply (frule set_mult_sub[of A B], assumption)
 apply (subst aGroup.nsum_jointfun[THEN sym, of R], assumption)
 apply (rule allI, rule impI, 
        frule_tac f = f and A = "{j. j \<le> n}" and B = "set_mult R A B" and
        x = j in funcset_mem, simp, simp add:subsetD)
 apply (rule allI, rule impI, 
        frule_tac f = g and A = "{j. j \<le> m}" and B = "set_mult R A B" and
        x = j in funcset_mem, simp, simp add:subsetD)
  apply (frule_tac f = f and n = n and A = "set_mult R A B" and g = g and m = m
        and B = "set_mult R A B" in jointfun_hom, assumption+)
 apply (simp del:nsum_suc)
 apply blast
done

lemma (in Ring) set_mult_mOp_closed:"\<lbrakk>A \<subseteq> carrier R; ideal R B;
       x \<in> set_mult R A B\<rbrakk> \<Longrightarrow> -\<^sub>a x \<in> set_mult R A B" 
apply (cut_tac ring_is_ag,
       simp add:set_mult_def,
       (erule bexE)+, frule sym, thin_tac "xa \<cdot>\<^sub>r y = x", simp,
       frule_tac c = xa in subsetD[of A "carrier R"], assumption+,
       frule ideal_subset1[of B],
       frule_tac c = y in subsetD[of B "carrier R"], assumption+,
       simp add:ring_inv1_2,
       frule_tac I = B and x = y in ideal_inv1_closed,
           assumption+) 
apply blast
done

lemma (in Ring) set_mult_ring_times_closed:"\<lbrakk>A \<subseteq> carrier R; ideal R B;
       x \<in> set_mult R A B; r \<in> carrier R\<rbrakk> \<Longrightarrow> r \<cdot>\<^sub>r  x \<in> set_mult R A B" 
apply (cut_tac ring_is_ag,   
       simp add:set_mult_def,
       (erule bexE)+, frule sym, thin_tac "xa \<cdot>\<^sub>r y = x", simp,
       frule_tac c = xa in subsetD[of A "carrier R"], assumption+,
       frule ideal_subset1[of B],
       frule_tac c = y in subsetD[of B "carrier R"], assumption,
       frule_tac x = r and y = "xa \<cdot>\<^sub>r y" in ring_tOp_commute,
       simp add:ring_tOp_closed, simp,
       subst ring_tOp_assoc, assumption+) 
 apply (frule_tac x = y and y = r in ring_tOp_commute, assumption+,
        simp,
        frule_tac x = y and r = r in ideal_ring_multiple [of B], assumption+)
 apply blast
done
 
lemma (in Ring) set_mult_sub_sum_mult:"\<lbrakk>A \<subseteq> carrier R; ideal R B\<rbrakk> \<Longrightarrow>
                   set_mult R A B \<subseteq> sum_mult R A B" 
apply (rule subsetI)
 apply (simp add:sum_mult_def)
 apply (cut_tac f = "(\<lambda>i\<in>{j. j \<le> (0::nat)}. x)" in nsum_0[of R]) 
 apply (cut_tac n_in_Nsetn[of 0],
        simp del:nsum_0)
 apply (cut_tac f = "\<lambda>i\<in>{j. j \<le> (0::nat)}. x" and B = "%_. set_mult R A B" in 
                Pi_I[of "{j. j \<le> 0}"],
       simp)
 apply (subgoal_tac "\<Sigma>\<^sub>e R (\<lambda>i\<in>{j. j \<le> 0}. x) 0 = x")
 apply blast
 apply simp
done

lemma (in Ring) sum_mult_pOp_closedn:"\<lbrakk>A \<subseteq> carrier R; ideal R B\<rbrakk>  \<Longrightarrow> 
               (\<forall>j \<le> n. f j \<in> set_mult R A B) \<longrightarrow> \<Sigma>\<^sub>e R f n \<in> sum_mult R A B"
apply (induct_tac n)
 apply (rule impI, simp) 
 apply (frule set_mult_sub_sum_mult[of A B], assumption+, simp add:subsetD)

apply (rule impI)
 apply simp
 apply (frule_tac a = "Suc n" in forall_spec, simp)
 apply (frule set_mult_sub_sum_mult[of A B], assumption+, 
        frule_tac c= "f (Suc n)" in 
                  subsetD[of "set_mult R A B" "sum_mult R A B"], assumption+)
 apply (rule sum_mult_pOp_closed, assumption,
        simp add:ideal_subset1, assumption+)
done

lemma (in Ring) mem_minus_sum_multTr4:"\<lbrakk>A \<subseteq> carrier R; ideal R B\<rbrakk> \<Longrightarrow>
        (\<forall>j \<le> n. f j \<in> set_mult R A B) \<longrightarrow> -\<^sub>a (nsum R f n) \<in> sum_mult R A B"
apply (cut_tac ring_is_ag)
apply (induct_tac n)
 apply (rule impI)
 apply (cut_tac n_in_Nsetn[of 0])
 apply (frule_tac x = "f 0" in set_mult_mOp_closed[of A B], assumption+)
 apply simp
 apply (frule set_mult_sub_sum_mult[of A B], assumption+, 
        simp add:subsetD)
apply (rule impI)
 apply (cut_tac n = n in Nsetn_sub_mem1, simp)
 apply (frule sum_mult_subR[of A B], simp add:ideal_subset1)
 apply (frule_tac n = n and f = f in sum_mult_pOp_closedn[of A B], assumption,
        cut_tac n = n in Nsetn_sub_mem1, simp)
 apply (frule_tac c = "\<Sigma>\<^sub>e R f n" in subsetD[of "sum_mult R A B" "carrier R"],
        assumption+,
        frule_tac a = "Suc n" in forall_spec, simp,
        thin_tac "\<forall>j\<le>Suc n. f j \<in> set_mult R A B",
        frule set_mult_sub[of A B], simp add:ideal_subset1,
        frule_tac c = "f (Suc n)" in subsetD[of "set_mult R A B" "carrier R"],
        assumption+ )       
 apply (frule_tac x = "\<Sigma>\<^sub>e R f n" and y = "f (Suc n)" in aGroup.ag_p_inv[of R],
        assumption+, simp) 
 apply (rule_tac a = "-\<^sub>a (\<Sigma>\<^sub>e R f n)" and b = "-\<^sub>a (f (Suc n))" in 
        sum_mult_pOp_closed[of A B], assumption+,
        simp add:ideal_subset1, assumption)
 apply (frule_tac x = "f (Suc n)" in set_mult_mOp_closed[of A B], assumption+,
        frule set_mult_sub_sum_mult[of A B], assumption+)
 apply (simp add:subsetD)
done
 
lemma (in Ring) sum_mult_iOp_closed:"\<lbrakk>A \<subseteq> carrier R; ideal R B; 
       x \<in> sum_mult R A B \<rbrakk> \<Longrightarrow> -\<^sub>a x \<in> sum_mult R A B"
apply (frule sum_mult_mem1 [of A B x],
       simp add:ideal_subset1, assumption)
apply (erule exE, erule bexE, frule sym, thin_tac "\<Sigma>\<^sub>e R f n = x")
apply simp
apply (frule_tac n = n and f = f in mem_minus_sum_multTr4[of A B], 
        assumption+)
apply (simp add:Pi_def)
done

lemma (in Ring) sum_mult_ring_multiplicationTr:
      "\<lbrakk>A \<subseteq> carrier R; ideal R B; r \<in> carrier R\<rbrakk> \<Longrightarrow>
       (\<forall>j \<le> n. f j \<in> set_mult R A B) \<longrightarrow> r \<cdot>\<^sub>r (nsum R f n) \<in> sum_mult R A B"
apply (cut_tac ring_is_ag)
apply (induct_tac n)
 apply (rule impI, simp)
 apply (simp add:set_mult_def)
 apply ((erule bexE)+, frule sym, thin_tac "x \<cdot>\<^sub>r y = f 0", simp)
 apply (frule_tac c = x in subsetD[of A "carrier R"], assumption+) 
 apply (frule ideal_subset1[of B],
        frule_tac c = y in subsetD[of B "carrier R"], assumption,
        frule_tac x = r and y = "x \<cdot>\<^sub>r y" in ring_tOp_commute,
        simp add:ring_tOp_closed, simp,
        subst ring_tOp_assoc, assumption+) 
 apply (frule_tac x = y and y = r in ring_tOp_commute, assumption+,
        simp,
        frule_tac x = y and r = r in ideal_ring_multiple [of B], assumption+)
 apply (rule times_mem_sum_mult, assumption+)
 
apply (rule impI)
 apply (cut_tac n = n in Nsetn_sub_mem1, simp)
 apply (frule_tac f = f and n = n in aGroup.nsum_mem,
        frule set_mult_sub [of "A" "B"], simp add:ideal_subset1,
        rule allI, rule impI, cut_tac n = n in Nsetn_sub_mem1,
         simp add: subsetD,
        frule_tac a = "Suc n" in forall_spec, simp) 
 apply (frule set_mult_sub[of A B], simp add:ideal_subset1,
        frule_tac c = "f (Suc n)" in subsetD[of "set_mult R A B" "carrier R"],
        assumption)
 apply (simp add: ring_distrib1) 
 apply (rule sum_mult_pOp_closed[of A B], assumption+,
        simp add:ideal_subset1, assumption)
 apply (frule_tac x = "f (Suc n)" in set_mult_ring_times_closed [of A B _ r],
        assumption+, simp, assumption,
        frule set_mult_sub_sum_mult[of A B], assumption+,
        simp add:subsetD)
done

lemma (in Ring) sum_mult_ring_multiplication:"\<lbrakk>A \<subseteq> carrier R; ideal R B; 
 r \<in> carrier R; a \<in> sum_mult R A B\<rbrakk>  \<Longrightarrow> r \<cdot>\<^sub>r a \<in> sum_mult R A B"
apply (cut_tac ring_is_ag)
apply (frule sum_mult_mem1[of A B a],
       simp add:ideal_subset1, assumption)
apply (erule exE, erule bexE, frule sym, thin_tac "\<Sigma>\<^sub>e R f n = a", simp)
apply (subgoal_tac "\<forall>j \<le> n. f j \<in> set_mult R A B")
apply (simp add:sum_mult_ring_multiplicationTr)
apply (simp add:Pi_def)
done

lemma (in Ring) ideal_sum_mult:"\<lbrakk>A \<subseteq> carrier R; A \<noteq> {}; ideal R B\<rbrakk> \<Longrightarrow>
                ideal R (sum_mult R A B)"
apply (simp add:ideal_def [of _ "sum_mult R A B"])
apply (cut_tac ring_is_ag)
apply (rule conjI) 
apply (rule aGroup.asubg_test, assumption+)
apply (rule subsetI)
 apply (frule_tac x = x in sum_mult_mem1[of A B],
        simp add:ideal_subset1, assumption,
        erule exE, erule bexE, frule sym, thin_tac "\<Sigma>\<^sub>e R f n = x", simp)
 apply (rule_tac f = f and n = n in sum_mult_mem[of A B _ _], assumption+)
 apply (simp add:ideal_subset1)
 apply (simp add:Pi_def)
 apply (frule nonempty_ex[of A], erule exE)
 apply (frule ideal_zero[of B])
 apply (frule_tac a = x and b = \<zero> in times_mem_sum_mult[of A B],
        simp add:ideal_subset1, assumption+) apply blast

 apply (rule ballI)+
 apply (rule_tac a = a and b = "-\<^sub>a b" in sum_mult_pOp_closed[of A B],
        assumption, simp add:ideal_subset1, assumption+,
        rule_tac x = b in sum_mult_iOp_closed[of A B], assumption+)
 apply (rule ballI)+
 apply (rule sum_mult_ring_multiplication, assumption+)
done

lemma (in Ring) ideal_inc_set_multTr:"\<lbrakk>A \<subseteq> carrier R; ideal R B; ideal R C; 
       set_mult R A B \<subseteq> C \<rbrakk> \<Longrightarrow>
         \<forall>f \<in> {j. j \<le> (n::nat)} \<rightarrow> set_mult R A B. \<Sigma>\<^sub>e R f n \<in> C"
apply (induct_tac n)
 apply (simp add:subsetD)

apply (rule ballI)
  apply (
       frule_tac f = f and A = "{j. j \<le> Suc n}" and x = "Suc n" and 
                 B = "set_mult R A B"in funcset_mem, simp,
       frule_tac c = "f (Suc n)" in subsetD[of "set_mult R A B" "C"], 
       assumption+, simp)
 apply (rule ideal_pOp_closed[of C], assumption+,
        cut_tac n = n in Nsetn_sub_mem1, 
        frule_tac x = f in bspec, simp)
 apply (simp add:Pi_def, assumption+)
done

lemma (in Ring) ideal_inc_set_mult:"\<lbrakk>A \<subseteq> carrier R; ideal R B; ideal R C; 
                           set_mult R A B \<subseteq> C \<rbrakk> \<Longrightarrow> sum_mult R A B \<subseteq> C"
apply (rule subsetI)
 apply (frule_tac x = x in sum_mult_mem1[of A B],
        simp add:ideal_subset1, assumption+)
 apply (erule exE, erule bexE, frule sym, thin_tac "\<Sigma>\<^sub>e R f n = x", simp,
        thin_tac "x = \<Sigma>\<^sub>e R f n", simp add:subsetD)
apply (simp add:ideal_inc_set_multTr)
done

lemma (in Ring) AB_inc_sum_mult:"\<lbrakk>ideal R A; ideal R B\<rbrakk> \<Longrightarrow> 
                                     sum_mult R A B \<subseteq> A \<inter> B"
apply (frule ideal_subset1[of A], frule ideal_subset1[of B])
apply (frule ideal_inc_set_mult [of "A" "B" "A"], assumption+)
apply (rule subsetI, 
       simp add:set_mult_def, (erule bexE)+, frule sym, thin_tac "xa \<cdot>\<^sub>r y = x",
       simp,
       frule_tac c = xa in subsetD[of A "carrier R"], assumption+,
       frule_tac c = y in subsetD[of B "carrier R"], assumption+,
       subst ring_tOp_commute, assumption+,
       simp add:ideal_ring_multiple)
apply (frule ideal_inc_set_mult [of "A" "B" "B"], assumption+)
apply (rule subsetI, 
       simp add:set_mult_def, (erule bexE)+, frule sym, thin_tac "xa \<cdot>\<^sub>r y = x",
       simp,
       frule_tac c = xa in subsetD[of A "carrier R"], assumption+,
       simp add:ideal_ring_multiple)
apply simp
done

lemma (in Ring) sum_mult_is_ideal_prod:"\<lbrakk>ideal R A; ideal R B\<rbrakk> \<Longrightarrow>
                                  sum_mult R A B =  A \<diamondsuit>\<^sub>r B"
apply (rule equalityI)
 apply (frule ideal_prod_ideal [of "A" "B"], assumption+)
 apply (rule ideal_inc_set_mult)
  apply (simp add:ideal_subset1)+
 apply (rule subsetI)
 apply (simp add:set_mult_def ideal_prod_def)
 apply (auto del:subsetI) 
 apply (rule subsetI)
 apply (simp add:ideal_prod_def)
 apply (frule ideal_subset1[of A],
        frule ideal_sum_mult[of A B],
        frule ideal_zero[of A], blast, assumption)
 apply (frule_tac a = "sum_mult R A B" in forall_spec, simp)
 apply (rule subsetI, simp,
        thin_tac "\<forall>xa. ideal R xa \<and> {x. \<exists>i\<in>A. \<exists>j\<in>B. x = i \<cdot>\<^sub>r j} \<subseteq> xa \<longrightarrow> x \<in> xa",
        (erule bexE)+, simp)
 apply (rule times_mem_sum_mult, assumption,
        simp add:ideal_subset1, assumption+)
done

lemma (in Ring) ideal_prod_assocTr0:"\<lbrakk>ideal R A; ideal R B; ideal R C; y \<in> C; 
                 z \<in> set_mult R A B\<rbrakk> \<Longrightarrow> z \<cdot>\<^sub>r y \<in> sum_mult R A (B \<diamondsuit>\<^sub>r C)"
apply (simp add:set_mult_def, (erule bexE)+,
        frule sym, thin_tac "x \<cdot>\<^sub>r ya = z", simp)
 apply (frule_tac h = x in ideal_subset[of A], assumption,
        frule_tac h = ya in ideal_subset[of B], assumption,
        frule_tac h = y in ideal_subset[of C], assumption,
        subst ring_tOp_assoc, assumption+) 
 apply (frule ideal_subset1[of A],
        frule ideal_subset1[of B], 
        frule ideal_subset1[of C],
        frule ideal_prod_ideal[of B C], assumption,
        frule ideal_subset1[of "B \<diamondsuit>\<^sub>r C"])
  apply (rule times_mem_sum_mult[of A "B \<diamondsuit>\<^sub>r C"], assumption+,
         subst sum_mult_is_ideal_prod[of B C, THEN sym], assumption+,
         rule times_mem_sum_mult[of B C], assumption+)
done

lemma (in Ring) ideal_prod_assocTr1:"\<lbrakk>ideal R A; ideal R B; ideal R C; y \<in> C\<rbrakk>
 \<Longrightarrow> \<forall>f \<in> {j. j\<le>(n::nat)} \<rightarrow> set_mult R A B. (\<Sigma>\<^sub>e R f n) \<cdot>\<^sub>r y \<in> A \<diamondsuit>\<^sub>r (B \<diamondsuit>\<^sub>r C)"
apply (cut_tac ring_is_ag)
apply (frule ideal_prod_ideal[of "B" "C"], assumption+,
       subst sum_mult_is_ideal_prod[of A "B \<diamondsuit>\<^sub>r C", THEN sym], assumption+)     
apply (induct_tac n)
 apply simp
 apply (simp add:ideal_prod_assocTr0)
 apply (rule ballI,
       frule_tac x = f in bspec,
       thin_tac "\<forall>f\<in>{j. j \<le> n} \<rightarrow> set_mult R A B.
            \<Sigma>\<^sub>e R f n \<cdot>\<^sub>r y \<in> sum_mult R A (B \<diamondsuit>\<^sub>r C)",
       rule Pi_I, simp,
       frule_tac f = f and A = "{j. j \<le> Suc n}" and B = "set_mult R A B" and
                 x = x in funcset_mem, simp, assumption)
 apply simp

 apply (frule ideal_subset1[of A], frule ideal_subset1[of B],
        frule set_mult_sub[of A B], assumption,
        frule_tac f = f and A = "{j. j \<le> (Suc n)}" in extend_fun[of _ _ 
                 "set_mult R A B"
         "carrier R"], assumption,
        subst ring_distrib2,
        simp add:ideal_subset)
 apply (rule aGroup.nsum_mem, assumption)
 apply (simp add:Pi_def)
 apply (simp add:funcset_mem del:Pi_I',
        frule_tac f = f and A = "{j. j \<le> Suc n}" and B = "set_mult R A B" and
        x =  "Suc n" in funcset_mem, simp)
apply (frule ideal_subset1[of A],
       frule ideal_zero[of A],
       frule ideal_sum_mult[of A "B \<diamondsuit>\<^sub>r C"], blast, assumption)
apply (rule ideal_pOp_closed, assumption+)
apply (simp add:ideal_prod_assocTr0)
done

lemma (in Ring) ideal_quotient_idealTr:"\<lbrakk>ideal R A; ideal R B; ideal R C; 
       x \<in> carrier R;\<forall>c\<in>C. x \<cdot>\<^sub>r c \<in> ideal_quotient R A B\<rbrakk> \<Longrightarrow> 
       f\<in>{j. j \<le> n} \<rightarrow> set_mult R B C \<longrightarrow>  x \<cdot>\<^sub>r (nsum R f n) \<in> A"

apply (frule ideal_subset1 [of "A"],
       frule ideal_subset1 [of "B"])
apply (induct_tac n)
 apply (rule impI) 
 apply (cut_tac n_in_Nsetn[of 0])
 apply (frule funcset_mem, assumption+) 
 apply (thin_tac "f \<in> {j. j \<le> 0} \<rightarrow> set_mult R B C")
 apply (simp add:set_mult_def)
 apply (erule bexE)+
 apply (frule sym, thin_tac "xa \<cdot>\<^sub>r y = f 0", simp)
 apply (frule_tac h = xa in ideal_subset[of B], assumption,
        frule_tac h = y in ideal_subset[of C], assumption)
 apply (frule_tac x = xa and y = y in ring_tOp_commute, assumption+,
        simp)
 apply (subst ring_tOp_assoc[THEN sym], assumption+)
 apply (frule_tac x = y in bspec, assumption,
        thin_tac "\<forall>c\<in>C. x \<cdot>\<^sub>r c \<in> A \<dagger>\<^sub>R B")
 apply (simp add:ideal_quotient_def)
(****** n ********)
apply (rule impI)
 apply (frule func_pre) apply simp
 apply (cut_tac ring_is_ag) 
 apply (frule ideal_subset1[of B], frule ideal_subset1[of C],
        frule set_mult_sub[of B C], assumption+)
 apply (cut_tac  n = n in nsum_memr [of _ "f"],
        rule allI, rule impI,
        frule_tac x = i in funcset_mem, simp, simp add:subsetD) 
 apply (frule_tac a = n in forall_spec, simp) 
 apply (thin_tac "\<forall>l\<le>n. \<Sigma>\<^sub>e R f l \<in> carrier R",
        frule_tac f = f and A = "{j. j \<le> Suc n}" and B = "set_mult R B C" 
                  and x = "Suc n" in funcset_mem, simp,
        frule_tac c = "f (Suc n)" in subsetD[of "set_mult R B C" " carrier R"],
         assumption+)
 apply (subst ring_distrib1, assumption+)
 apply (rule ideal_pOp_closed[of A], assumption+)
 apply (simp add: set_mult_def, (erule bexE)+,
        fold set_mult_def,
        frule sym, thin_tac "xa \<cdot>\<^sub>r y = f (Suc n)", simp)
 apply (frule_tac c = xa in subsetD[of B "carrier R"], assumption+,
        frule_tac c = y in subsetD[of C "carrier R"], assumption+,
        frule_tac x = xa and y = y in ring_tOp_commute, assumption, simp,
        subst ring_tOp_assoc[THEN sym], assumption+)
 apply (simp add:ideal_quotient_def)
done

lemma (in Ring) ideal_quotient_ideal:"\<lbrakk>ideal R A; ideal R B; ideal R C\<rbrakk> \<Longrightarrow> 
                         A \<dagger>\<^sub>R B \<dagger>\<^sub>R C = A \<dagger>\<^sub>R B \<diamondsuit>\<^sub>r C"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:ideal_quotient_def [of _ _ "C"])
 apply (erule conjE)
 apply (simp add:ideal_quotient_def [of _ _ "B \<diamondsuit>\<^sub>r C"])
 apply (rule ballI)
apply (simp add:sum_mult_is_ideal_prod [THEN sym])
 apply (simp add:sum_mult_def)
 apply (erule exE, erule bexE)
 apply (rename_tac x c n f)
 apply (frule sym) apply simp 
apply (simp add:ideal_quotient_idealTr)
apply (rule subsetI)
 apply (simp add:sum_mult_is_ideal_prod [THEN sym])
 apply (simp add:ideal_quotient_def)
 apply (erule conjE)
 apply (rule ballI)
 apply (rename_tac x c)
 apply (frule ideal_subset [of "C"], assumption+)
 apply (simp add:ring_tOp_closed)
apply (rule ballI)
apply (rename_tac x v u)
 apply (frule ideal_subset [of "B"], assumption+)
 apply (subst ring_tOp_assoc, assumption+)
 apply (frule ideal_subset1[of B],
        frule ideal_subset1[of C],
        frule_tac a = u and b = v in times_mem_sum_mult[of B C], assumption+)
 apply (frule_tac x = u and y = v in ring_tOp_commute, assumption,
        simp)
done

lemma (in Ring) ideal_prod_assocTr:"\<lbrakk>ideal R A; ideal R B; ideal R C\<rbrakk> \<Longrightarrow>
  \<forall>f. (f \<in> {j. j \<le> (n::nat)} \<rightarrow> set_mult R (A \<diamondsuit>\<^sub>r B) C \<longrightarrow> 
                                          (\<Sigma>\<^sub>e R f n) \<in> A \<diamondsuit>\<^sub>r (B \<diamondsuit>\<^sub>r C))"
apply (subgoal_tac "\<forall>x\<in>(A \<diamondsuit>\<^sub>r B). \<forall>y\<in>C. x \<cdot>\<^sub>r y \<in> A \<diamondsuit>\<^sub>r (B \<diamondsuit>\<^sub>r C)")
apply (induct_tac n)
  apply (rule allI) apply (rule impI)
  apply (frule_tac f = f and A = "{j. j \<le> 0}" and B = "set_mult R (A \<diamondsuit>\<^sub>r B) C"
        and x = 0 in funcset_mem, simp, simp)
  apply (simp add:set_mult_def)
  apply ((erule bexE)+, frule sym, thin_tac "x \<cdot>\<^sub>r y = f 0", simp)
apply (rule allI, rule impI)
  apply (frule func_pre)
  apply (frule_tac a = f in forall_spec, simp,
         thin_tac "\<forall>f. f \<in> {j. j \<le> n} \<rightarrow> set_mult R (A \<diamondsuit>\<^sub>r B) C \<longrightarrow>
               \<Sigma>\<^sub>e R f n \<in> A \<diamondsuit>\<^sub>r (B \<diamondsuit>\<^sub>r C)",
         frule ideal_prod_ideal[of "B" "C"], assumption+,
         frule ideal_prod_ideal[of "A" "B \<diamondsuit>\<^sub>r C"], assumption+, simp)
  apply (rule ideal_pOp_closed[of "A \<diamondsuit>\<^sub>r (B \<diamondsuit>\<^sub>r C)"], assumption+)
  apply (cut_tac n = "Suc n" in n_in_Nsetn,
       frule_tac f = f and A = "{j. j \<le> Suc n}" and 
       B = "set_mult R (A \<diamondsuit>\<^sub>r B) C" and x = "Suc n" in funcset_mem, assumption) 
 apply (thin_tac "f \<in> {j. j \<le> n} \<rightarrow> set_mult R (A \<diamondsuit>\<^sub>r B) C",
        thin_tac "f \<in> {j. j \<le> Suc n} \<rightarrow> set_mult R (A \<diamondsuit>\<^sub>r B) C")
 apply (simp add:set_mult_def)
 apply ((erule bexE)+,
        frule sym, thin_tac "x \<cdot>\<^sub>r y = f (Suc n)", simp)

 apply (rule ballI)+
 apply (simp add:sum_mult_is_ideal_prod[of A B, THEN sym])
 apply (frule ideal_subset1[of A], frule ideal_subset1[of B],
        frule_tac x = x in sum_mult_mem1[of A B], assumption+)
       apply (erule exE, erule bexE, frule sym, thin_tac "\<Sigma>\<^sub>e R f n = x",
               simp)
  apply (simp add:ideal_prod_assocTr1)
done
 
lemma (in Ring) ideal_prod_assoc:"\<lbrakk>ideal R A; ideal R B; ideal R C\<rbrakk> \<Longrightarrow>
            (A \<diamondsuit>\<^sub>r B) \<diamondsuit>\<^sub>r C = A \<diamondsuit>\<^sub>r (B \<diamondsuit>\<^sub>r C)" 
apply (rule equalityI)
 apply (rule subsetI)
 apply (frule ideal_prod_ideal[of "A" "B"], assumption+)
 apply (frule sum_mult_is_ideal_prod[of "A \<diamondsuit>\<^sub>r B" "C"], assumption+)
 apply (frule sym) apply (thin_tac "sum_mult R (A \<diamondsuit>\<^sub>r B) C = (A \<diamondsuit>\<^sub>r B) \<diamondsuit>\<^sub>r C")
 apply simp apply (thin_tac "(A \<diamondsuit>\<^sub>r B) \<diamondsuit>\<^sub>r C = sum_mult R (A \<diamondsuit>\<^sub>r B) C")
 apply (thin_tac "ideal R (A \<diamondsuit>\<^sub>r B)")
 apply (frule ideal_prod_ideal[of "B" "C"], assumption+)
  apply (simp add:sum_mult_def)
  apply (erule exE, erule bexE)  
 apply (frule sym, thin_tac "\<Sigma>\<^sub>e R f n = x", simp) 
 apply (simp add:ideal_prod_assocTr) 
apply (rule subsetI)
 apply (frule ideal_prod_ideal[of "B" "C"], assumption+)
 apply (simp add:ideal_prod_commute [of "A" "B \<diamondsuit>\<^sub>r C"])
 apply (frule ideal_prod_ideal[of "A" "B"], assumption+)
 apply (simp add:ideal_prod_commute[of "A \<diamondsuit>\<^sub>r B" "C"])
 apply (simp add:ideal_prod_commute[of "A" "B"])
 apply (simp add:ideal_prod_commute[of "B" "C"])
 apply (frule ideal_prod_ideal[of "C" "B"], assumption+)
 apply (frule sum_mult_is_ideal_prod[of "C \<diamondsuit>\<^sub>r B" "A"], assumption+)
 apply (frule sym) apply (thin_tac "sum_mult R (C \<diamondsuit>\<^sub>r B) A = (C \<diamondsuit>\<^sub>r B) \<diamondsuit>\<^sub>r A")
 apply simp apply (thin_tac "(C \<diamondsuit>\<^sub>r B) \<diamondsuit>\<^sub>r A = sum_mult R (C \<diamondsuit>\<^sub>r B) A")
 apply (thin_tac "ideal R (C \<diamondsuit>\<^sub>r B)")
 apply (frule ideal_prod_ideal[of "B" "A"], assumption+)
  apply (simp add:sum_mult_def)
  apply (erule exE, erule bexE)
 apply (frule sym, thin_tac "\<Sigma>\<^sub>e R f n = x", simp) 
 apply (simp add:ideal_prod_assocTr) 
done

lemma (in Ring) prod_principal_idealTr0:"  \<lbrakk>a \<in> carrier R; b \<in> carrier R;
         z \<in> set_mult R (R \<diamondsuit>\<^sub>p a) (R \<diamondsuit>\<^sub>p b)\<rbrakk> \<Longrightarrow>  z \<in> R \<diamondsuit>\<^sub>p (a \<cdot>\<^sub>r b)"
apply (simp add:set_mult_def, (erule bexE)+,
       simp add:Rxa_def, (erule bexE)+, simp)
apply (frule_tac x = r and y = a and z = "ra \<cdot>\<^sub>r b" in ring_tOp_assoc,
           assumption+, simp add:ring_tOp_closed, simp)
apply (simp add:ring_tOp_assoc[THEN sym, of a _ b])
apply (frule_tac x = a and y = ra in ring_tOp_commute, assumption+, simp)
apply (simp add:ring_tOp_assoc[of _ a b],
       frule_tac x = a and y = b in ring_tOp_closed, assumption)
apply (simp add:ring_tOp_assoc[THEN sym, of _ _ "a \<cdot>\<^sub>r b"],
       frule sym, thin_tac "r \<cdot>\<^sub>r ra \<cdot>\<^sub>r (a \<cdot>\<^sub>r b) = z", simp,
       frule_tac x = r and y = ra in ring_tOp_closed, assumption+)
apply blast
done
 

lemma (in Ring) prod_principal_idealTr1:"  \<lbrakk>a \<in> carrier R; b \<in> carrier R\<rbrakk> \<Longrightarrow>
      \<forall>f \<in> {j. j \<le> (n::nat)} \<rightarrow> set_mult R (R \<diamondsuit>\<^sub>p a) (R \<diamondsuit>\<^sub>p b). 
                                         \<Sigma>\<^sub>e R f n \<in> R \<diamondsuit>\<^sub>p (a \<cdot>\<^sub>r b)"
apply (induct_tac n)
 apply (rule ballI, 
        frule_tac f = f in funcset_mem[of _ "{j. j \<le> 0}" 
         "set_mult R (R \<diamondsuit>\<^sub>p a) (R \<diamondsuit>\<^sub>p b)"], simp)
 apply (simp add:prod_principal_idealTr0)
apply (rule ballI,
       frule func_pre,
       frule_tac x = f in bspec, assumption,
       thin_tac "\<forall>f\<in>{j. j \<le> n} \<rightarrow> set_mult R (R \<diamondsuit>\<^sub>p a) (R \<diamondsuit>\<^sub>p b).
                                       \<Sigma>\<^sub>e R f n \<in> R \<diamondsuit>\<^sub>p (a \<cdot>\<^sub>r b)")
 apply (frule ring_tOp_closed[of a b], assumption)
 apply (frule principal_ideal[of "a \<cdot>\<^sub>r b"], simp,
        rule ideal_pOp_closed, assumption+)
 apply (cut_tac n = "Suc n" in n_in_Nsetn,
        frule_tac f = f and A = "{j. j \<le> Suc n}" and 
        B = "set_mult R (R \<diamondsuit>\<^sub>p a) (R \<diamondsuit>\<^sub>p b)" in funcset_mem, assumption)
 apply (simp add:prod_principal_idealTr0)
done

lemma (in Ring) prod_principal_ideal:"\<lbrakk>a \<in> carrier R; b \<in> carrier R\<rbrakk> \<Longrightarrow> 
                     (Rxa R a) \<diamondsuit>\<^sub>r (Rxa R b) = Rxa R (a \<cdot>\<^sub>r b)" 
apply (frule principal_ideal[of "a"], 
       frule principal_ideal[of "b"])
apply (subst sum_mult_is_ideal_prod[THEN sym, of "Rxa R a" "Rxa R b"], 
       assumption+) 
 apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:sum_mult_def)
 apply (erule exE, erule bexE)
 apply (frule sym, thin_tac "\<Sigma>\<^sub>e R f n = x", simp, thin_tac "x = \<Sigma>\<^sub>e R f n")
 apply (simp add:prod_principal_idealTr1)

apply (rule subsetI)
 apply (simp add:Rxa_def, fold Rxa_def)
 apply (erule bexE)
 apply (simp add:ring_tOp_assoc[THEN sym])
 apply (frule ideal_subset1[of "R \<diamondsuit>\<^sub>p a"],
        frule ideal_subset1[of "R \<diamondsuit>\<^sub>p b"])
 apply (rule_tac a = "r \<cdot>\<^sub>r a" and b = b in times_mem_sum_mult[of "R \<diamondsuit>\<^sub>p a" 
         "R \<diamondsuit>\<^sub>p b"], assumption+)
 apply (simp add:Rxa_def, blast)
 apply (simp add:a_in_principal)
done

lemma (in Ring) principal_ideal_n_pow1:"a \<in> carrier R \<Longrightarrow>  
                                  (Rxa R a)\<^bsup>\<diamondsuit>R n\<^esup>  = Rxa R (a^\<^bsup>R n \<^esup>)"
 apply (cut_tac ring_one)
apply (induct_tac n)
 apply simp 
 apply (cut_tac a_in_principal[of "1\<^sub>r"])
 apply (frule principal_ideal[of "1\<^sub>r"])
 apply (frule ideal_inc_one, assumption, simp)
 apply (simp add:ring_one)
 apply simp
 apply (frule_tac n = n in npClose[of a],
        subst prod_principal_ideal, assumption+)
 apply (simp add:ring_tOp_commute)
done

lemma (in Ring) principal_ideal_n_pow:"\<lbrakk>a \<in> carrier R; I = Rxa R a\<rbrakk> \<Longrightarrow>  
                                  I \<^bsup>\<diamondsuit>R n\<^esup>  = Rxa R (a^\<^bsup>R n\<^esup>)"
apply simp 
apply (rule principal_ideal_n_pow1[of "a" "n"], assumption+)
done

text\<open>more about \<open>ideal_n_prod\<close>\<close>

lemma (in Ring) nprod_eqTr:" f \<in> {j. j \<le> (n::nat)} \<rightarrow> carrier R \<and>
       g \<in> {j. j \<le> n} \<rightarrow> carrier R \<and> (\<forall>j \<le> n. f j = g j) \<longrightarrow>
       nprod R f n = nprod R g n" 
apply (induct_tac n)
  apply simp
apply (rule impI, (erule conjE)+)
  apply (frule func_pre[of f], frule func_pre[of g],
         cut_tac n = n in Nsetn_sub_mem1, simp)
done

lemma (in Ring) nprod_eq:"\<lbrakk>\<forall>j \<le> n. f j \<in> carrier R; \<forall>j \<le> n. g j \<in> carrier R;
(\<forall>j \<le> (n::nat). f j = g j)\<rbrakk> \<Longrightarrow> nprod R f n = nprod R g n"
apply (cut_tac nprod_eqTr[of f n g])
apply simp
done

definition
  mprod_expR :: "[('b, 'm) Ring_scheme, nat \<Rightarrow> nat, nat \<Rightarrow> 'b, nat] \<Rightarrow> 'b" where
  "mprod_expR R e f n = nprod R (\<lambda>j. ((f j)^\<^bsup>R (e j)\<^esup>)) n"

 (** Note that e j is a natural number for all j in Nset n **)

lemma (in Ring) mprodR_Suc:"\<lbrakk>e \<in> {j. j \<le> (Suc n)} \<rightarrow> {j. (0::nat) \<le> j};
                 f \<in> {j. j \<le> (Suc n)} \<rightarrow> carrier R\<rbrakk> \<Longrightarrow> 
       mprod_expR R e f (Suc n) = 
            (mprod_expR R e f n) \<cdot>\<^sub>r ((f (Suc n))^\<^bsup>R (e (Suc n))\<^esup>)"
apply (simp add:mprod_expR_def)
done  

lemma (in Ring) mprod_expR_memTr:"e \<in> {j. j \<le> n} \<rightarrow> {j. (0::nat) \<le> j} \<and> 
       f \<in> {j. j \<le> n} \<rightarrow> carrier R  \<longrightarrow>  mprod_expR R e f n \<in> carrier R"
apply (induct_tac n)
 apply (rule impI, (erule conjE)+)
 apply (cut_tac n_in_Nsetn[of 0], 
        simp add: mprod_expR_def)
 apply (rule npClose,
        simp add:Pi_def)

apply (rule impI, (erule conjE)+)
 apply (frule func_pre[of "e"], frule func_pre[of "f"])
 apply simp
 apply (simp add:mprodR_Suc)
 apply (rule ring_tOp_closed, assumption+)
 apply (rule npClose, cut_tac n = "Suc n" in n_in_Nsetn)
 apply (simp add:Pi_def)
done

lemma (in Ring) mprod_expR_mem:"\<lbrakk> e \<in> {j. j \<le> n} \<rightarrow> {j. (0::nat) \<le> j};
       f \<in> {j. j \<le> n} \<rightarrow> carrier R\<rbrakk>   \<Longrightarrow>  mprod_expR R e f n \<in> carrier R"
apply (simp add:mprod_expR_memTr)
done  

lemma (in Ring) prod_n_principal_idealTr:"e \<in> {j. j\<le>n} \<rightarrow> {j. (0::nat)\<le>j} \<and> 
f \<in> {j. j\<le>n} \<rightarrow> carrier R \<and> (\<forall>k \<le> n. J k = (Rxa R (f k))\<^bsup>\<diamondsuit>R (e k)\<^esup>) \<longrightarrow>
                 ideal_n_prod R n J = Rxa R (mprod_expR R e f n)"
apply (induct_tac n)
 apply (rule impI) apply (erule conjE)+
 apply (simp add:mprod_expR_def)
 apply (subgoal_tac "J 0 = R \<diamondsuit>\<^sub>p (f 0) \<^bsup>\<diamondsuit>R (e 0)\<^esup>")
 apply simp
 apply (rule principal_ideal_n_pow[of "f 0" "R \<diamondsuit>\<^sub>p (f 0)"])
 apply (cut_tac n_in_Nsetn[of 0], simp add:Pi_def) apply simp
 apply (cut_tac n_in_Nsetn[of 0], simp)

apply (rule impI, (erule conjE)+)
 apply (frule func_pre[of "e"], frule func_pre[of "f"])
 apply (cut_tac n = n in Nsetn_sub_mem1,
        simp add:mprodR_Suc)
 apply (cut_tac n = "Suc n" in n_in_Nsetn, simp)
 apply (frule_tac A = "{j. j \<le> Suc n}" and x = "Suc n" in funcset_mem[of "f" _ "carrier R"], simp)
 apply (frule_tac a = "f (Suc n)" and I = "R \<diamondsuit>\<^sub>p (f (Suc n))" and n = "e (Suc n)" in  principal_ideal_n_pow) apply simp
 apply (subst prod_principal_ideal[THEN sym])
 apply (simp add:mprod_expR_mem)
 apply (rule npClose, assumption+) apply simp 
done

(************* used in Valuation2.thy *****************)
lemma (in Ring) prod_n_principal_ideal:"\<lbrakk>e \<in> {j. j\<le>n} \<rightarrow> {j. (0::nat)\<le>j};  
f \<in> {j. j\<le>n} \<rightarrow> carrier R; \<forall>k\<le> n. J k = (Rxa R (f k))\<^bsup>\<diamondsuit>R (e k)\<^esup>\<rbrakk> \<Longrightarrow>
                 ideal_n_prod R n J = Rxa R (mprod_expR R e f n)"
apply (simp add:prod_n_principal_idealTr[of e n f J])
done  
(*******************************************************)

lemma (in Idomain) a_notin_n_pow1:"\<lbrakk>a \<in> carrier R; \<not> Unit R a; a \<noteq> \<zero>; 0 < n\<rbrakk>
  \<Longrightarrow>  a \<notin> (Rxa R a) \<^bsup>\<diamondsuit>R  (Suc n)\<^esup>" 
apply (rule contrapos_pp)
 apply (simp del:ipSuc) apply (simp del:ipSuc)
 apply (frule principal_ideal[of "a"])
 apply (frule principal_ideal_n_pow[of "a" "R \<diamondsuit>\<^sub>p a" "Suc n"]) 
 apply simp apply (simp del:ipSuc)
 apply (thin_tac "R \<diamondsuit>\<^sub>p a \<^bsup>\<diamondsuit>R (Suc n)\<^esup> = R \<diamondsuit>\<^sub>p (a^\<^bsup>R n\<^esup> \<cdot>\<^sub>r a)")
 apply (thin_tac "ideal R (R \<diamondsuit>\<^sub>p a)")
 apply (simp add:Rxa_def)
 apply (erule bexE)
apply (frule npClose[of "a" "n"])
 apply (simp add:ring_tOp_assoc[THEN sym])
 apply (frule ring_l_one[THEN sym, of "a"])
 apply (subgoal_tac "1\<^sub>r \<cdot>\<^sub>r a = r \<cdot>\<^sub>r a^\<^bsup>R n\<^esup> \<cdot>\<^sub>r a") 
 apply (cut_tac b = "r \<cdot>\<^sub>r (a^\<^bsup>R n\<^esup>)" in idom_mult_cancel_r[of "1\<^sub>r" _ "a"])
 apply (simp add:ring_one) apply (simp add:ring_tOp_closed)
 apply assumption+
 apply (thin_tac "1\<^sub>r \<cdot>\<^sub>r a = r \<cdot>\<^sub>r a^\<^bsup>R n\<^esup> \<cdot>\<^sub>r a",
        thin_tac "a = 1\<^sub>r \<cdot>\<^sub>r a",
        thin_tac "a = r \<cdot>\<^sub>r a^\<^bsup>R n\<^esup> \<cdot>\<^sub>r a")
 apply (subgoal_tac "1\<^sub>r = r \<cdot>\<^sub>r (a^\<^bsup>R (Suc (n - Suc 0))\<^esup>)") prefer 2
 apply (simp del:ipSuc) 
 apply (thin_tac "1\<^sub>r = r \<cdot>\<^sub>r a^\<^bsup>R n\<^esup>")
 apply (simp del:Suc_pred)
 apply (frule npClose[of "a" "n - Suc 0"])
 apply (simp add:ring_tOp_assoc[THEN sym])
 apply (frule_tac x = r and y = "a^\<^bsup>R (n - Suc 0)\<^esup>" in ring_tOp_closed, assumption)
 apply (simp add:ring_tOp_commute[of _ a])
 apply (simp add:Unit_def) apply blast
 apply simp
done

lemma (in Idomain) a_notin_n_pow2:"\<lbrakk>a \<in> carrier R; \<not> Unit R a; a \<noteq> \<zero>; 
 0 < n\<rbrakk> \<Longrightarrow> a^\<^bsup>R n\<^esup> \<notin> (Rxa R a) \<^bsup>\<diamondsuit>R (Suc n)\<^esup>"
apply (rule contrapos_pp)
 apply (simp del:ipSuc, simp del:ipSuc)
 apply (frule principal_ideal[of "a"])
 apply (frule principal_ideal_n_pow[of "a" "R \<diamondsuit>\<^sub>p a" "Suc n"])
 apply (simp, simp del:ipSuc)
 apply (thin_tac "R \<diamondsuit>\<^sub>p a \<^bsup>\<diamondsuit>R (Suc n)\<^esup> = R \<diamondsuit>\<^sub>p (a^\<^bsup>R n\<^esup> \<cdot>\<^sub>r a)")
 apply (thin_tac "ideal R (R \<diamondsuit>\<^sub>p a)")
apply (simp add:Rxa_def) 
 apply (erule bexE)
 apply (frule idom_potent_nonzero[of "a" "n"], assumption+)
 apply (frule npClose[of "a" "n"])
 apply (frule ring_l_one[THEN sym, of "a^\<^bsup>R n\<^esup> "])
 apply (subgoal_tac "1\<^sub>r \<cdot>\<^sub>r (a^\<^bsup>R n\<^esup>) =  r \<cdot>\<^sub>r ((a^\<^bsup>R n\<^esup>) \<cdot>\<^sub>r a)")
 prefer 2 apply simp 
 apply (thin_tac "a^\<^bsup>R n\<^esup> = 1\<^sub>r \<cdot>\<^sub>r a^\<^bsup>R n\<^esup>",
        thin_tac "a^\<^bsup>R n\<^esup> = r \<cdot>\<^sub>r (a^\<^bsup>R n\<^esup> \<cdot>\<^sub>r a)")
 apply (simp add:ring_tOp_commute[of "a^\<^bsup>R n\<^esup>" a])
 apply (simp add:ring_tOp_assoc[THEN sym])
 apply (cut_tac ring_one,
        frule_tac b = "r \<cdot>\<^sub>r a" in idom_mult_cancel_r[of "1\<^sub>r" _ "a^\<^bsup>R n\<^esup>"],
        simp add:ring_tOp_closed,
        assumption+)
 apply (simp add:ring_tOp_commute[of _ a])
 apply (simp add:Unit_def, blast)
done

lemma (in Idomain) n_pow_not_prime:"\<lbrakk>a \<in> carrier R; a \<noteq> \<zero>;  0 < n\<rbrakk>
            \<Longrightarrow>   \<not> prime_ideal R ((Rxa R a) \<^bsup>\<diamondsuit>R (Suc n)\<^esup>)"
apply (case_tac "n = 0") 
 apply simp 
apply (case_tac "Unit R a")
 apply (simp del:ipSuc add:prime_ideal_def, rule impI)
 apply (frule principal_ideal[of "a"])
 apply (frule principal_ideal_n_pow[of "a" "R \<diamondsuit>\<^sub>p a" "Suc n"]) 
 apply simp apply (simp del:npow_suc)
 apply (simp del:npow_suc add:idom_potent_unit [of "a" "Suc n"])
 apply (thin_tac "R \<diamondsuit>\<^sub>p a \<diamondsuit>\<^sub>r R \<diamondsuit>\<^sub>p a \<^bsup>\<diamondsuit>R n\<^esup> = R \<diamondsuit>\<^sub>p (a^\<^bsup>R (Suc n)\<^esup>)")
 apply (frule npClose[of "a" "Suc n"])
 apply (frule a_in_principal[of "a^\<^bsup>R (Suc n)\<^esup>"])
 apply (simp add: ideal_inc_unit)
 apply (frule a_notin_n_pow1[of "a" "n"], assumption+)
 apply (frule a_notin_n_pow2[of "a" "n"], assumption+)

 apply (frule npClose[of "a" "n"])
 apply (frule principal_ideal[of "a"])
 apply (frule principal_ideal_n_pow[of "a" "R \<diamondsuit>\<^sub>p a" "Suc n"])
 apply simp apply (simp del:ipSuc npow_suc)
 apply (thin_tac "R \<diamondsuit>\<^sub>p a \<^bsup>\<diamondsuit>R (Suc n)\<^esup> = R \<diamondsuit>\<^sub>p (a^\<^bsup>R (Suc n)\<^esup>)")
 apply (subst prime_ideal_def) 
 apply (simp del:npow_suc) apply (rule impI)
 apply (subgoal_tac "(a^\<^bsup>R n\<^esup>) \<cdot>\<^sub>r a \<in> R \<diamondsuit>\<^sub>p (a^\<^bsup>R (Suc n)\<^esup>)")
 apply blast

 apply (simp add:Rxa_def)
  apply (frule ring_tOp_closed[of "a" "a^\<^bsup>R n\<^esup>"], assumption+)
 apply (frule ring_l_one[THEN sym, of "a \<cdot>\<^sub>r (a^\<^bsup>R n\<^esup>)"])
 apply (cut_tac ring_one)
 apply (simp add:ring_tOp_commute[of _ a], blast)
done

lemma (in Idomain) principal_pow_prime_condTr:
  "\<lbrakk>a \<in> carrier R; a \<noteq> \<zero>; prime_ideal R ((Rxa R a) \<^bsup>\<diamondsuit>R (Suc n)\<^esup>)\<rbrakk> \<Longrightarrow> n = 0"
apply (rule contrapos_pp, (simp del:ipSuc)+) 
apply (frule n_pow_not_prime[of  "a" "n"], assumption+)
apply (simp del:ipSuc)
done

lemma (in Idomain) principal_pow_prime_cond:
  "\<lbrakk>a \<in> carrier R; a \<noteq> \<zero>;  prime_ideal R ((Rxa R a) \<^bsup>\<diamondsuit>R n\<^esup>)\<rbrakk> \<Longrightarrow> n = Suc 0"
apply (case_tac "n = 0")
 apply simp
 apply (simp add:prime_ideal_def) apply (erule conjE)
 apply (cut_tac ring_one, simp)
apply (subgoal_tac "prime_ideal R (R \<diamondsuit>\<^sub>p a \<^bsup>\<diamondsuit>R (Suc (n - Suc 0))\<^esup>)")
apply (frule principal_pow_prime_condTr[of "a" "n - Suc 0"], assumption+)
apply simp apply simp
done

section "Extension and contraction"


locale TwoRings = Ring +
       fixes R' (structure)
       assumes secondR: "Ring R'"


definition
  i_contract :: "['a \<Rightarrow> 'b, ('a, 'm1) Ring_scheme, ('b, 'm2) Ring_scheme,
    'b set]  \<Rightarrow> 'a set" where
  "i_contract f R R' J = invim f (carrier R) J"

definition
  i_extension :: "['a \<Rightarrow> 'b, ('a, 'm1) Ring_scheme, ('b, 'm2) Ring_scheme,
           'a set] \<Rightarrow> 'b set" where
  "i_extension f R R' I = sum_mult R' (f ` I) (carrier R')"

lemma (in TwoRings) i_contract_sub:"\<lbrakk>f \<in> rHom R R'; ideal R' J \<rbrakk> \<Longrightarrow>
                       (i_contract f R R' J) \<subseteq> carrier R"
  by (auto simp add:i_contract_def invim_def)

lemma (in TwoRings) i_contract_ideal:"\<lbrakk>f \<in> rHom R R'; ideal R' J \<rbrakk> \<Longrightarrow>
                                          ideal R (i_contract f R R' J)"
 apply (cut_tac Ring,
        cut_tac secondR)
apply (rule ideal_condition)
apply (simp add:i_contract_sub)
apply (simp add:i_contract_def invim_def)
 apply (cut_tac ring_zero)
 apply (cut_tac Ring)
 apply (frule rHom_0_0[of R R' f], assumption+,
        cut_tac Ring.ideal_zero[of R' J])
 apply (frule sym, thin_tac "f \<zero> = \<zero>\<^bsub>R'\<^esub>", simp, blast,
        assumption+)
apply (rule ballI)+
 apply (simp add:i_contract_def invim_def, (erule conjE)+)
 apply (cut_tac ring_is_ag,
        frule_tac x = y in aGroup.ag_mOp_closed[of R], assumption)
 apply (simp add:aGroup.ag_pOp_closed)
 apply (simp add:rHom_add) 
 apply (frule_tac x = y in rHom_inv_inv[of R R' _ f], assumption+, simp,
        thin_tac "f (-\<^sub>a y) = -\<^sub>a\<^bsub>R'\<^esub> (f y)",
        frule_tac x = "f y" in Ring.ideal_inv1_closed[of R' J], assumption+,
        rule Ring.ideal_pOp_closed[of R'], assumption+)
 apply ((rule ballI)+,
        simp add:i_contract_def invim_def, erule conjE,
        simp add:ring_tOp_closed,
        simp add:rHom_tOp)
 apply (frule_tac a = r in rHom_mem[of f R R'], assumption,
        simp add:Ring.ideal_ring_multiple[of R' J])
done

lemma (in TwoRings) i_contract_mono:"\<lbrakk>f \<in> rHom R R'; ideal R' J1; ideal R' J2;
 J1 \<subseteq> J2 \<rbrakk> \<Longrightarrow> i_contract f R R' J1 \<subseteq> i_contract f R R' J2"
apply (rule subsetI)
apply (simp add:i_contract_def invim_def) apply (erule conjE)
apply (rule subsetD, assumption+)
done

lemma (in TwoRings) i_contract_prime:"\<lbrakk>f \<in> rHom R R'; prime_ideal R' P\<rbrakk> \<Longrightarrow> 
                            prime_ideal R (i_contract f R R' P)"
apply (cut_tac Ring,
        cut_tac secondR)
apply (simp add:prime_ideal_def, (erule conjE)+)
 apply (simp add:i_contract_ideal)
 apply (rule conjI)
 apply (rule contrapos_pp, simp+)
 apply (simp add:i_contract_def invim_def, erule conjE)
 apply (simp add:rHom_one)
apply (rule ballI)+
 apply (frule_tac a = x in rHom_mem[of "f" "R" "R'"], assumption+,
        frule_tac a = y in rHom_mem[of "f" "R" "R'"], assumption+)
 apply (rule impI)
 apply (simp add:i_contract_def invim_def, erule conjE)
 apply (simp add:rHom_tOp)
done   

lemma (in TwoRings) i_extension_ideal:"\<lbrakk>f \<in> rHom R R'; ideal R I \<rbrakk> \<Longrightarrow>
                            ideal R' (i_extension f R R' I)"
apply (cut_tac Ring, cut_tac secondR)
apply (simp add:i_extension_def)
apply (rule Ring.ideal_sum_mult [of "R'" "f ` I" "carrier R'"], assumption+)
apply (rule subsetI)
apply (simp add:image_def)
   apply (erule bexE, frule_tac a = xa in rHom_mem[of f R R'],
          rule ideal_subset, assumption+, simp)
 apply (frule ideal_zero, simp, blast)
 apply (simp add:Ring.whole_ideal[of R'])
done

lemma (in TwoRings) i_extension_mono:"\<lbrakk>f \<in> rHom R R'; ideal R I1; ideal R I2;
 I1 \<subseteq> I2 \<rbrakk> \<Longrightarrow> (i_extension f R R' I1) \<subseteq> (i_extension f R R' I2)"
apply (rule subsetI)
 apply (simp add:i_extension_def)
 apply (simp add:sum_mult_def)
 apply (erule exE, erule bexE)
 apply (cut_tac Ring.set_mult_mono[of R' "f ` I1" "f ` I2" "carrier R'"])
 apply (frule_tac f = fa and A = "{j. j \<le> n}" in extend_fun[of _ _ 
     "set_mult R' (f ` I1) (carrier R')" "set_mult R' (f ` I2) (carrier R')"],
     assumption+) apply blast
 apply (simp add:secondR)
 apply (simp add:image_def, rule subsetI, simp, erule bexE,
       frule_tac h = xb in ideal_subset[of I1], assumption, simp add:rHom_mem) 
 apply (simp add:image_def, rule subsetI, simp, erule bexE,
       frule_tac h = xb in ideal_subset[of I2], assumption, simp add:rHom_mem)
 apply (rule subsetI,
        simp add:image_def, erule bexE,
        frule_tac c = xb in subsetD[of I1 I2], assumption+, blast)
 apply simp
done 

lemma (in TwoRings) e_c_inc_self:"\<lbrakk>f \<in> rHom R R'; ideal R I\<rbrakk> \<Longrightarrow>
              I \<subseteq> i_contract f R R' (i_extension f R R' I)"
apply (rule subsetI)
 apply (simp add:i_contract_def i_extension_def invim_def)
 apply (simp add:ideal_subset)
 apply (cut_tac secondR,
        frule Ring.ring_one [of "R'"])
 apply (frule_tac h = x in ideal_subset[of I], assumption,
        frule_tac f = f and A = R and R = R' and a = x in rHom_mem, assumption)
 apply (frule_tac t = "f x" in Ring.ring_r_one[THEN sym, of R'], assumption)
 apply (frule_tac a = "f x" and b = "1\<^sub>r\<^bsub>R'\<^esub>" in Ring.times_mem_sum_mult[of R'
                 "f ` I" "carrier R'"],
       rule subsetI,
       simp add:image_def, erule bexE,
       frule_tac h = xb in ideal_subset[of I], assumption,
       simp add:rHom_mem, simp,
       simp add:image_def, blast, assumption+)
 apply simp
done
       
lemma (in TwoRings) c_e_incd_self:"\<lbrakk>f \<in> rHom R R'; ideal R' J \<rbrakk> \<Longrightarrow>
                          i_extension f R R' (i_contract f R R' J) \<subseteq> J"
apply (rule subsetI)
 apply (simp add:i_extension_def)
 apply (simp add:sum_mult_def)
 apply (erule exE, erule bexE)
 apply (cut_tac secondR,
        frule_tac n = n and f = fa in Ring.ideal_nsum_closed[of R' J ],
        assumption)
 apply (rule allI, rule impI) apply (
        frule_tac f = fa and A = "{j. j \<le> n}" and 
        B = "set_mult R' (f ` i_contract f R R' J) (carrier R')" and x = j in
        funcset_mem, simp) apply (
  thin_tac "fa \<in> {j. j \<le> n} \<rightarrow> set_mult R' (f ` i_contract f R R' J) (carrier R')")
  apply (simp add:set_mult_def, (erule bexE)+,
         simp add:i_contract_def invim_def, erule conjE)
  apply (frule_tac x = "f xa" and r = y in Ring.ideal_ring_multiple1[of R' J],
         assumption+, simp)
       
  apply simp
done

lemma (in TwoRings) c_e_c_eq_c:"\<lbrakk>f \<in> rHom R R'; ideal R' J \<rbrakk> \<Longrightarrow>
  i_contract f R R' (i_extension f R R' (i_contract f R R' J)) 
                                          = i_contract f R R' J"
apply (frule i_contract_ideal [of "f" "J"], assumption)
apply (frule e_c_inc_self [of "f" "i_contract f R R' J"], assumption+)
apply (frule c_e_incd_self [of "f" "J"], assumption+)
apply (frule i_contract_mono [of "f" 
         "i_extension f R R' (i_contract f R R' J)" "J"])
apply (rule i_extension_ideal, assumption+)
apply (rule equalityI, assumption+)
done

lemma (in TwoRings) e_c_e_eq_e:"\<lbrakk>f \<in> rHom R R'; ideal R I \<rbrakk> \<Longrightarrow>
  i_extension f R R' (i_contract f R R' (i_extension f R R' I)) 
                                          = i_extension f R R' I"
apply (frule i_extension_ideal [of "f" "I"], assumption+)
apply (frule c_e_incd_self [of "f" "i_extension f R R' I"], assumption+)
apply (rule equalityI, assumption+)
 apply (thin_tac "i_extension f R R' (i_contract f R R' (i_extension f R R' I))
       \<subseteq> i_extension f R R' I")
apply (frule e_c_inc_self [of "f" "I"], assumption+)
apply (rule i_extension_mono [of "f" "I" 
               "i_contract f R R' (i_extension f R R' I)"], assumption+)
apply (rule i_contract_ideal, assumption+)
done

section "Complete system of representatives"

definition
  csrp_fn :: "[_, 'a set] \<Rightarrow> 'a set \<Rightarrow> 'a" where
  "csrp_fn R I = (\<lambda>x\<in>carrier (R /\<^sub>r I). (if x = I then \<zero>\<^bsub>R\<^esub> else SOME y. y \<in> x))"
 
definition
  csrp :: "[_ , 'a set] \<Rightarrow> 'a set" where
  "csrp R I == (csrp_fn R I) ` (carrier (R /\<^sub>r I))"

(** complete system of representatives having 1-1 correspondence with
    carrier  (R /\<^sub>r I) **)

lemma (in Ring) csrp_mem:"\<lbrakk>ideal R I; a \<in> carrier R\<rbrakk> \<Longrightarrow>
                           csrp_fn R I (a \<uplus>\<^bsub>R\<^esub> I) \<in> a \<uplus>\<^bsub>R\<^esub> I"
apply (simp add:csrp_fn_def qring_carrier) 
apply (case_tac "a \<uplus>\<^bsub>R\<^esub> I = I") apply simp
 apply (rule conjI, rule impI)
 apply (simp add:ideal_zero)
 apply (rule impI)
 apply (cut_tac ring_zero)
 apply (frule_tac x = \<zero>  in bspec, assumption+)
 apply (thin_tac "\<forall>a\<in>carrier R. a \<uplus>\<^bsub>R\<^esub> I \<noteq> I")
 apply (frule ideal_zero[of "I"])
 apply (frule ar_coset_same4[of "I" "\<zero>"], assumption+, simp)
apply simp
 apply (rule conjI)
 apply (rule impI, rule someI2_ex)
 apply (frule a_in_ar_coset[of "I" "a"], assumption+, blast, assumption+)
apply (rule impI)
 apply (frule_tac x = a in bspec, assumption+,
        thin_tac "\<forall>aa\<in>carrier R. aa \<uplus>\<^bsub>R\<^esub> I \<noteq> a \<uplus>\<^bsub>R\<^esub> I", simp)
done

lemma (in Ring) csrp_same:"\<lbrakk>ideal R I; a \<in> carrier R\<rbrakk> \<Longrightarrow>
                           csrp_fn R I (a \<uplus>\<^bsub>R\<^esub> I) \<uplus>\<^bsub>R\<^esub> I = a \<uplus>\<^bsub>R\<^esub> I"
apply (frule csrp_mem[of "I" "a"], assumption+)
apply (rule ar_cos_same[of "a" "I" "csrp_fn R I (a \<uplus>\<^bsub>R\<^esub> I)"], assumption+)
done

lemma (in Ring) csrp_mem1:"\<lbrakk>ideal R I; x \<in> carrier (R /\<^sub>r I)\<rbrakk> \<Longrightarrow>
                           csrp_fn R I x \<in> x"
apply (simp add:qring_carrier, erule bexE, frule sym,
       thin_tac "a \<uplus>\<^bsub>R\<^esub> I = x", simp)
apply (simp add:csrp_mem)
done

lemma (in Ring) csrp_fn_mem:"\<lbrakk>ideal R I; x \<in> carrier (R /\<^sub>r I)\<rbrakk> \<Longrightarrow>
                              (csrp_fn R I x) \<in> carrier R"
apply (simp add:qring_carrier, erule bexE, frule sym,
       thin_tac "a \<uplus>\<^bsub>R\<^esub> I = x", simp,
       frule_tac a = a in csrp_mem[of "I"], assumption+) 
apply (rule_tac a = a and x = "csrp_fn R I (a \<uplus>\<^bsub>R\<^esub> I)" in 
       ar_coset_subsetD[of  "I"], assumption+)
done

lemma (in Ring) csrp_eq_coset:"\<lbrakk>ideal R I; x \<in> carrier (R /\<^sub>r I)\<rbrakk> \<Longrightarrow>
                           (csrp_fn R I x) \<uplus>\<^bsub>R\<^esub> I = x"
apply (simp add:qring_carrier, erule bexE)
apply (frule sym, thin_tac "a \<uplus>\<^bsub>R\<^esub> I = x", simp)
 apply (frule_tac a = a in csrp_mem[of  "I"], assumption+)
apply (rule ar_cos_same, assumption+)
done 

lemma (in Ring) csrp_nz_nz:"\<lbrakk>ideal R I; x \<in> carrier (R /\<^sub>r I);
        x \<noteq> \<zero>\<^bsub>(R /\<^sub>r I)\<^esub>\<rbrakk> \<Longrightarrow> (csrp_fn R I x) \<noteq> \<zero>"
apply (rule contrapos_pp, simp+)
apply (frule csrp_eq_coset[of "I" "x"], assumption+, simp)
apply (simp add:qring_zero[of "I"])
apply (frule ideal_zero[of  "I"]) apply (
       cut_tac ring_zero)
       apply (simp add:Qring_fix1 [of "\<zero>" "I"])
done


lemma (in Ring) csrp_diff_in_vpr:"\<lbrakk>ideal R I; x \<in> carrier R\<rbrakk> \<Longrightarrow>
              x \<plusminus> (-\<^sub>a (csrp_fn R I (pj R I x))) \<in> I"
apply (frule csrp_mem[of "I" "x"], 
       frule csrp_same[of "I" "x"], 
       simp add:pj_mem, assumption,
       frule  ar_coset_subsetD[of I x "csrp_fn R I (x \<uplus>\<^bsub>R\<^esub> I)"],
       assumption+)  
apply (frule belong_ar_coset2[of I x "csrp_fn R I (x \<uplus>\<^bsub>R\<^esub> I)"], assumption+,
     frule ideal_inv1_closed[of I "csrp_fn R I (x \<uplus>\<^bsub>R\<^esub> I) \<plusminus> -\<^sub>a x"], assumption+,
     cut_tac ring_is_ag,
     frule aGroup.ag_mOp_closed[of R x], assumption,
     simp add:aGroup.ag_pOp_commute[of R "csrp_fn R I (x \<uplus>\<^bsub>R\<^esub> I)" "-\<^sub>a x"]) 
apply (simp add:aGroup.ag_p_inv[of R "-\<^sub>a x" "csrp_fn R I (x \<uplus>\<^bsub>R\<^esub> I)"],
       simp add:aGroup.ag_inv_inv,
       cut_tac Ring, simp add:pj_mem[of R I x])
done

lemma (in Ring) csrp_pj:"\<lbrakk>ideal R I; x \<in> carrier (R /\<^sub>r I)\<rbrakk> \<Longrightarrow>
                 (pj R I) (csrp_fn R I x) = x"
apply(cut_tac Ring,
      frule csrp_fn_mem[of "I" "x"], assumption+,
      simp add:pj_mem[of "R" "I" "csrp_fn R I x"],
      simp add:csrp_eq_coset)
done

section "Polynomial ring" 

text\<open>In this section, we treat a ring of polynomials over a ring S.
       Numbers are of type ant\<close>

definition
  pol_coeff :: "[('a, 'more) Ring_scheme, (nat \<times> (nat \<Rightarrow> 'a))] \<Rightarrow> bool" where
  "pol_coeff S c \<longleftrightarrow> (\<forall>j \<le> (fst c). (snd c) j \<in> carrier S)"

definition
  c_max :: "[('a, 'more) Ring_scheme, nat \<times> (nat \<Rightarrow> 'a)] \<Rightarrow> nat" where
  "c_max S c = (if {j. j \<le> (fst c) \<and> (snd c) j \<noteq> \<zero>\<^bsub>S\<^esub>} = {} then 0 else
                   n_max {j. j \<le> (fst c) \<and> (snd c) j \<noteq> \<zero>\<^bsub>S\<^esub>})"

definition
  polyn_expr :: "[('a, 'more) Ring_scheme, 'a, nat, nat \<times> (nat \<Rightarrow> 'a)]  \<Rightarrow> 'a" where
  "polyn_expr R X k c == nsum R (\<lambda>j. ((snd c) j) \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R j\<^esup>)) k"

definition
  algfree_cond :: "[('a, 'm) Ring_scheme, ('a, 'm1) Ring_scheme,
                                                'a] \<Rightarrow> bool" where
  "algfree_cond R S X \<longleftrightarrow> (\<forall>c. pol_coeff S c \<and> (\<forall>k \<le> (fst c).  
             (nsum R (\<lambda>j. ((snd c) j) \<cdot>\<^sub>r\<^bsub>R\<^esub> (X^\<^bsup>R j\<^esup>)) k = \<zero>\<^bsub>R\<^esub> \<longrightarrow> 
             (\<forall>j \<le> k. (snd c) j = \<zero>\<^bsub>S\<^esub>))))"

locale PolynRg = Ring +
       fixes S (structure)
       fixes X (structure)
       assumes X_mem_R:"X \<in> carrier R"
       and not_zeroring:"\<not> Zero_ring S"
       and subring:  "Subring R S"
       and algfree: "algfree_cond R S X"
       and S_X_generate:"x \<in> carrier R \<Longrightarrow>
           \<exists>f. pol_coeff S f \<and> x = polyn_expr R X (fst f) f"

(** a polynomial is an element of a polynomial ring **)
section \<open>Addition and multiplication of \<open>polyn_exprs\<close>\<close>

subsection \<open>Simple properties of a \<open>polyn_ring\<close>\<close>

lemma Subring_subset:"Subring R S \<Longrightarrow> carrier S \<subseteq> carrier R"
by (simp add:Subring_def)

lemma (in Ring) subring_Ring:"Subring R S \<Longrightarrow> Ring S"
by (simp add:Subring_def)

lemma (in Ring) mem_subring_mem_ring:"\<lbrakk>Subring R S; x \<in> carrier S\<rbrakk> \<Longrightarrow>
                      x \<in> carrier R"
by (simp add:Subring_def, (erule conjE)+, simp add: subsetD)

lemma (in Ring) Subring_pOp_ring_pOp:"\<lbrakk>Subring R S; a \<in> carrier S;
 b \<in> carrier S \<rbrakk> \<Longrightarrow> a \<plusminus>\<^bsub>S\<^esub> b = a \<plusminus> b"
apply (simp add:Subring_def, (erule conjE)+)
apply (frule rHom_add[of "ridmap S" S R a b], assumption+)
apply (cut_tac Ring.ring_is_ag[of S],
       frule aGroup.ag_pOp_closed[of S a b], assumption+,
       simp add:ridmap_def, assumption)
done

lemma (in Ring) Subring_tOp_ring_tOp:"\<lbrakk>Subring R S; a \<in> carrier S;
              b \<in> carrier S \<rbrakk> \<Longrightarrow> a \<cdot>\<^sub>r\<^bsub>S\<^esub> b = a \<cdot>\<^sub>r b"
apply (simp add:Subring_def, (erule conjE)+)
apply (frule rHom_tOp[of "S" "R" "a" "b" "ridmap S"], rule Ring_axioms, assumption+)
apply (frule Ring.ring_tOp_closed[of "S" "a" "b"], assumption+,
       simp add:ridmap_def)
done

lemma (in Ring) Subring_one_ring_one:"Subring R S \<Longrightarrow> 1\<^sub>r\<^bsub>S\<^esub> = 1\<^sub>r"
apply (simp add:Subring_def, (erule conjE)+)
apply (frule rHom_one[of "S" "R" "ridmap S"], rule Ring_axioms, assumption+)
apply (simp add:ridmap_def, simp add:Ring.ring_one[of S])
done

lemma (in Ring) Subring_zero_ring_zero:"Subring R S \<Longrightarrow> \<zero>\<^bsub>S\<^esub> = \<zero>"
apply (simp add:Subring_def, (erule conjE)+,
       frule rHom_0_0[of "S" "R" "ridmap S"], rule Ring_axioms, assumption+,
       simp add:ridmap_def, simp add:Ring.ring_zero[of "S"])
done

lemma (in Ring) Subring_minus_ring_minus:"\<lbrakk>Subring R S; x \<in> carrier S\<rbrakk>
      \<Longrightarrow> -\<^sub>a\<^bsub>S\<^esub> x = -\<^sub>a x"
apply (simp add:Subring_def, (erule conjE)+, simp add:rHom_def, (erule conjE)+)
apply (cut_tac ring_is_ag, frule Ring.ring_is_ag[of "S"])
apply (frule aHom_inv_inv[of "S" "R" "ridmap S" "x"], assumption+,
       frule aGroup.ag_mOp_closed[of "S" "x"], assumption+)
apply (simp add:ridmap_def)
done 

lemma (in PolynRg) Subring_pow_ring_pow:"x \<in> carrier S \<Longrightarrow>
                   x^\<^bsup>S n\<^esup> = x^\<^bsup>R n\<^esup>"
apply (cut_tac subring, frule subring_Ring)          
apply (induct_tac n)
 apply (simp, simp add:Subring_one_ring_one)
apply (frule_tac n = n in Ring.npClose[of S x], assumption+)
apply (simp add:Subring_tOp_ring_tOp)
done

lemma (in PolynRg) is_Ring: "Ring R" ..

lemma (in PolynRg) polyn_ring_nonzero:"1\<^sub>r \<noteq> \<zero>"
apply (cut_tac Ring, cut_tac subring)
apply (simp add:Subring_zero_ring_zero[THEN sym])
apply (simp add:Subring_one_ring_one[THEN sym])
apply (simp add:not_zeroring)
done

lemma (in PolynRg) polyn_ring_S_nonzero:"1\<^sub>r\<^bsub>S\<^esub> \<noteq> \<zero>\<^bsub>S\<^esub>"
apply (cut_tac subring)
apply (simp add:Subring_zero_ring_zero)
apply (simp add:Subring_one_ring_one)
apply (simp add:polyn_ring_nonzero)
done

lemma (in PolynRg) polyn_ring_X_nonzero:"X \<noteq> \<zero>"
apply (cut_tac algfree,
       cut_tac subring)
apply (simp add:algfree_cond_def)
apply (rule contrapos_pp, simp+)
apply (drule_tac x = "Suc 0" in spec)
 apply (subgoal_tac "pol_coeff S ((Suc 0), 
          (\<lambda>j\<in>{l. l \<le> (Suc 0)}. if j = 0 then \<zero>\<^bsub>S\<^esub> else 1\<^sub>r\<^bsub>S\<^esub>))")
 apply (drule_tac x = "\<lambda>j\<in>{l. l \<le> (Suc 0)}. if j = 0 then \<zero>\<^bsub>S\<^esub> else 1\<^sub>r\<^bsub>S\<^esub>" in 
        spec) 
 apply (erule conjE, simp)
 apply (simp only:Nset_1)
 apply (drule_tac a = "Suc 0" in forall_spec, simp)
 apply simp
 apply (cut_tac subring, simp add:Subring_zero_ring_zero,
        simp add:Subring_one_ring_one, cut_tac ring_zero, cut_tac ring_one,
        simp add:ring_r_one, simp add:ring_times_x_0, cut_tac ring_is_ag,
          simp add:aGroup.ag_r_zero,
        drule_tac a = "Suc 0" in forall_spec, simp, simp)
 apply (cut_tac polyn_ring_S_nonzero, simp add:Subring_zero_ring_zero)

 apply (thin_tac "\<forall>b. pol_coeff S (Suc 0, b) \<and>
         (\<forall>k\<le>Suc 0. \<Sigma>\<^sub>e R (\<lambda>j. b j \<cdot>\<^sub>r \<zero>^\<^bsup>R j\<^esup>) k = \<zero> \<longrightarrow> (\<forall>j\<le>k. b j = \<zero>\<^bsub>S\<^esub>))",
        simp add:pol_coeff_def,
        rule allI,
        simp add:Subring_def, simp add:Ring.ring_zero,
        (rule impI)+,
        simp add:Ring.ring_one)
done

subsection "Coefficients of a polynomial" 

lemma (in PolynRg) pol_coeff_split:"pol_coeff S f = pol_coeff S (fst f, snd f)"
by simp

lemma (in PolynRg) pol_coeff_cartesian:"pol_coeff S c \<Longrightarrow>
                   (fst c, snd c) = c"
by simp

lemma (in PolynRg) split_pol_coeff:"\<lbrakk>pol_coeff S c; k \<le> (fst c)\<rbrakk> \<Longrightarrow>
                                               pol_coeff S (k, snd c)"
by (simp add:pol_coeff_def)

lemma (in PolynRg) pol_coeff_pre:"pol_coeff S ((Suc n), f) \<Longrightarrow> 
                   pol_coeff S (n, f)"
apply (simp add:pol_coeff_def)
done

lemma (in PolynRg) pol_coeff_le:"\<lbrakk>pol_coeff S c; n \<le> (fst c)\<rbrakk> \<Longrightarrow>
                               pol_coeff S (n, (snd c))"
apply (simp add:pol_coeff_def) 
done

lemma (in PolynRg) pol_coeff_mem:"\<lbrakk>pol_coeff S c; j \<le> (fst c)\<rbrakk> \<Longrightarrow> 
                                                   ((snd c) j) \<in> carrier S"
by (simp add:pol_coeff_def) 

lemma (in PolynRg) pol_coeff_mem_R:"\<lbrakk>pol_coeff S c; j \<le> (fst c)\<rbrakk>
                  \<Longrightarrow>  ((snd c) j) \<in> carrier R"
apply (cut_tac subring, frule subring_Ring)
apply (frule pol_coeff_mem[of c "j"], assumption+,
       simp add:mem_subring_mem_ring)
done

lemma (in PolynRg) Slide_pol_coeff:"\<lbrakk>pol_coeff S c; n < (fst c)\<rbrakk> \<Longrightarrow>
        pol_coeff S (((fst c) - Suc n), (\<lambda>x. (snd c) (Suc (n + x))))"   
apply (simp add: pol_coeff_def)
done

subsection \<open>Addition of \<open>polyn_exprs\<close>\<close>

lemma (in PolynRg) monomial_mem:"pol_coeff S c \<Longrightarrow> 
                        \<forall>j \<le> (fst c). (snd c) j \<cdot>\<^sub>r X^\<^bsup>R j\<^esup> \<in> carrier R"
apply (rule allI, rule impI)
apply (rule ring_tOp_closed) 
apply (simp add:pol_coeff_mem_R[of c],
       cut_tac X_mem_R, simp add:npClose)
done

lemma (in PolynRg) polyn_mem:"\<lbrakk>pol_coeff S c; k \<le> (fst c)\<rbrakk> \<Longrightarrow> 
                                        polyn_expr R X k c \<in> carrier R"
apply (simp add:polyn_expr_def,
       cut_tac ring_is_ag)
apply (rule aGroup.nsum_mem[of R k "\<lambda>j. (snd c) j \<cdot>\<^sub>r X^\<^bsup>R j\<^esup>"], assumption+)
apply (simp add:monomial_mem)
done

lemma (in PolynRg) polyn_exprs_eq:"\<lbrakk>pol_coeff S c; pol_coeff S d; 
         k \<le> (min (fst c) (fst d)); \<forall>j \<le> k. (snd c) j = (snd d) j\<rbrakk> \<Longrightarrow> 
                     polyn_expr R X k c = polyn_expr R X k d" 
apply (cut_tac ring_is_ag,
       simp add:polyn_expr_def,
       cut_tac subring,
       cut_tac X_mem_R)
apply (rule aGroup.nsum_eq[of R k "\<lambda>j. (snd c) j \<cdot>\<^sub>r X^\<^bsup>R j\<^esup>"
                                   "\<lambda>j. (snd d) j \<cdot>\<^sub>r X^\<^bsup>R j\<^esup>"], assumption)
apply (simp add:monomial_mem)+
done

lemma (in PolynRg) polyn_expr_restrict:"pol_coeff S (Suc n, f) \<Longrightarrow>
              polyn_expr R X n (Suc n, f) = polyn_expr R X n (n, f)" 
apply (cut_tac subring, frule subring_Ring,
       cut_tac pol_coeff_le[of "(Suc n, f)" n]) 
apply (cut_tac polyn_exprs_eq[of "(Suc n, f)" "(n, f)" n],
       (simp add:pol_coeff_split[THEN sym])+) 
done

lemma (in PolynRg) polyn_expr_short:"\<lbrakk>pol_coeff S c; k \<le> (fst c)\<rbrakk> \<Longrightarrow>
         polyn_expr R X k c = polyn_expr R X k (k, snd c)"
apply (rule polyn_exprs_eq[of c "(k, snd c)" k], assumption+)
 apply (simp add:pol_coeff_def)
 apply (simp)
 apply simp
done

lemma (in PolynRg) polyn_expr0:"pol_coeff S c \<Longrightarrow> 
                                   polyn_expr R X 0 c = (snd c) 0"
apply (simp add:polyn_expr_def)
apply (cut_tac subring,
       cut_tac subring_Ring[of S])
apply (frule pol_coeff_mem[of c 0], simp)
 apply (frule mem_subring_mem_ring [of S "(snd c) 0"], assumption)
apply (simp add:ring_r_one, assumption)
done 

lemma (in PolynRg) polyn_expr_split:"
          polyn_expr R X k f = polyn_expr R X k (fst f, snd f)"
by simp

lemma (in PolynRg) polyn_Suc:"Suc n \<le> (fst c) \<Longrightarrow> 
       polyn_expr R X (Suc n) ((Suc n), (snd c)) = 
               polyn_expr R X n c \<plusminus> ((snd c) (Suc n)) \<cdot>\<^sub>r (X^\<^bsup>R (Suc n)\<^esup>)"
by (simp add:polyn_expr_def)

lemma (in PolynRg) polyn_Suc_split:"pol_coeff S (Suc n, f) \<Longrightarrow> 
       polyn_expr R X (Suc n) ((Suc n), f) = 
          polyn_expr R X n (n, f) \<plusminus> (f (Suc n)) \<cdot>\<^sub>r (X^\<^bsup>R (Suc n)\<^esup>)"
apply (cut_tac polyn_Suc[of n "(Suc n, f)"])
apply (simp del:npow_suc)
 apply (subst polyn_expr_short[of "(Suc n, f)" n], assumption+, simp)
 apply (simp del:npow_suc)
 apply simp
done

lemma (in PolynRg) polyn_n_m:"\<lbrakk>pol_coeff S c; n < m; m \<le> (fst c)\<rbrakk> \<Longrightarrow> 
      polyn_expr R X m (m, (snd c)) = polyn_expr R X n (n, (snd c)) \<plusminus>  
                        (fSum R (\<lambda>j. ((snd c) j) \<cdot>\<^sub>r (X^\<^bsup>R j\<^esup>)) (Suc n) m)"
apply (simp add:polyn_expr_def, cut_tac ring_is_ag)
apply (rule aGroup.nsum_split1[of "R" m "\<lambda>j. ((snd c) j) \<cdot>\<^sub>r (X^\<^bsup>R j\<^esup>)" n], 
         assumption+)
apply (rule allI, rule impI)
apply (frule_tac monomial_mem[of c],
       frule_tac i = j and j = m and k = "(fst c)" in le_trans, assumption+,
       simp+)
done

lemma (in PolynRg) polyn_n_m1:"\<lbrakk>pol_coeff S c; n < m; m \<le> (fst c)\<rbrakk> \<Longrightarrow> 
      polyn_expr R X m c = polyn_expr R X n c \<plusminus>  
                        (fSum R (\<lambda>j. ((snd c) j) \<cdot>\<^sub>r (X^\<^bsup>R j\<^esup>)) (Suc n) m)"
apply (subst polyn_expr_short[of c n], assumption)
 apply (frule_tac x = n and y = m and z = "fst c" in less_le_trans, assumption,
        simp add:less_imp_le)
 apply (subst polyn_expr_short[of c m], assumption+)
 apply (simp add:polyn_n_m)
done

lemma (in PolynRg) polyn_n_m_mem:"\<lbrakk>pol_coeff S c; n < m; m \<le> (fst c)\<rbrakk> \<Longrightarrow> 
            (fSum R (\<lambda>j. ((snd c) j) \<cdot>\<^sub>r (X^\<^bsup>R j\<^esup>)) (Suc n) m) \<in> carrier R"
apply (simp add:fSum_def)
apply (cut_tac ring_is_ag,
       rule_tac n = "m - Suc n" in aGroup.nsum_mem, assumption+)
apply (rule allI, rule impI,
        simp del:npow_suc add:cmp_def slide_def)
apply (rule ring_tOp_closed)
 apply (simp add:pol_coeff_def)
 apply (frule_tac a = "Suc (n + j)" in forall_spec, arith)
 apply (cut_tac subring)
 apply (simp add:mem_subring_mem_ring)
 apply (rule npClose)
 apply (cut_tac X_mem_R,
        simp del:npow_suc add:npClose)
done 

lemma (in PolynRg) polyn_n_ms_eq:"\<lbrakk>pol_coeff S c; pol_coeff S d;
        m \<le> min (fst c) (fst d); n < m; 
       \<forall>j\<in>nset (Suc n) m. (snd c) j = (snd d) j\<rbrakk> \<Longrightarrow> 
            (fSum R (\<lambda>j. ((snd c) j) \<cdot>\<^sub>r (X^\<^bsup>R j\<^esup>)) (Suc n) m) =
                    (fSum R (\<lambda>j. ((snd d) j) \<cdot>\<^sub>r (X^\<^bsup>R j\<^esup>)) (Suc n) m)" 
apply (cut_tac ring_is_ag)
apply (cut_tac aGroup.fSum_eq1[of R "Suc n" m "\<lambda>j. (snd c) j \<cdot>\<^sub>r X^\<^bsup>R j\<^esup>"
                                             "\<lambda>j. (snd d) j \<cdot>\<^sub>r X^\<^bsup>R j\<^esup>"],
       assumption+)
   apply (rule Suc_leI, assumption,
          simp add:nset_def, simp add:monomial_mem)
   apply (frule Suc_leI,
              rule ballI, simp add:nset_def)

   apply (simp add:monomial_mem)
 apply simp
done


lemma (in PolynRg) polyn_addTr:
 "(pol_coeff S (n, f)) \<and> (pol_coeff S (n, g)) \<longrightarrow>
    (polyn_expr R X n (n, f)) \<plusminus> (polyn_expr R X n (n, g)) =
                 nsum R (\<lambda>j. ((f j) \<plusminus>\<^bsub>S\<^esub> (g j)) \<cdot>\<^sub>r (X^\<^bsup>R j\<^esup>)) n"
apply (cut_tac subring,
        frule subring_Ring[of S])
apply (induct_tac n)
 apply (rule impI, simp, erule conjE)
 apply (simp add:polyn_expr0)
 apply (cut_tac pol_coeff_mem[of "(0, f)" 0], simp,
        cut_tac pol_coeff_mem[of "(0, g)" 0], simp,
       frule  mem_subring_mem_ring[of S "f 0"], assumption+,
       frule  mem_subring_mem_ring[of S "g 0"], assumption+,
       frule Ring.ring_is_ag[of S],
       frule aGroup.ag_pOp_closed[of S "f 0" "g 0"], assumption+,
       frule mem_subring_mem_ring[of S "f 0 \<plusminus>\<^bsub>S\<^esub> g 0"], assumption+)
apply (simp add:ring_r_one)
 apply (simp add:Subring_pOp_ring_pOp[of S "f 0" "g 0"])
 apply (simp del:npow_suc)+
apply (rule impI, erule conjE)
 apply (frule_tac n = n in  pol_coeff_pre[of _ f],
        frule_tac n = n in  pol_coeff_pre[of _ g], simp del:npow_suc)
 apply (cut_tac n = n and c = "(Suc n, f)" in polyn_Suc, simp del:npow_suc,
        simp del:npow_suc,
        thin_tac "polyn_expr R X (Suc n) (Suc n, f) =
         polyn_expr R X n (Suc n, f) \<plusminus> f (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup>")
 apply (cut_tac n = n and c = "(Suc n, g)" in polyn_Suc, simp del:npow_suc,
        simp del:npow_suc,
        thin_tac "polyn_expr R X (Suc n) (Suc n, g) =
         polyn_expr R X n (Suc n, g) \<plusminus> g (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup>")
 apply (cut_tac c = "(Suc n, f)" and k = n in polyn_mem, assumption, 
                simp del:npow_suc,
        cut_tac k = n and c = "(Suc n, g)" in polyn_mem, assumption, 
                simp del:npow_suc)
 apply (frule_tac j = "Suc n" and c = "(Suc n, f)" in pol_coeff_mem_R, simp,
        frule_tac j = "Suc n" and c = "(Suc n, g)" in pol_coeff_mem_R, simp,
        cut_tac  X_mem_R,
        frule_tac n = "Suc n" in npClose[of "X"], simp del:npow_suc)
 apply (frule_tac x = "f (Suc n)" and y = "X^\<^bsup>R (Suc n)\<^esup>" in ring_tOp_closed,
         assumption+,
        frule_tac x = "g (Suc n)" and y = "X^\<^bsup>R (Suc n)\<^esup>" in ring_tOp_closed,
         assumption+)
 apply (cut_tac ring_is_ag, 
        subst aGroup.pOp_assocTr43, assumption+)
 apply (frule_tac x = "f (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup>" and 
        y = "polyn_expr R X n (Suc n, g)" in aGroup.ag_pOp_commute[of R],
        assumption+, simp del:npow_suc,
        thin_tac "f (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup> \<plusminus> polyn_expr R X n (Suc n, g) =
         polyn_expr R X n (Suc n, g) \<plusminus> f (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup>")
 apply (subst  aGroup.pOp_assocTr43[THEN sym], assumption+,
        simp del:npow_suc add:polyn_expr_restrict) 

 apply (frule_tac c = "(Suc n, f)" and j = "Suc n" in pol_coeff_mem, simp,
        frule_tac c = "(Suc n, g)" and j = "Suc n" in pol_coeff_mem, simp)
 apply (subst ring_distrib2[THEN sym], assumption+) 
apply (frule_tac c = "(Suc n, f)" and j = "Suc n" in  pol_coeff_mem, simp,
       frule_tac c = "(Suc n, g)" and j = "Suc n" in  pol_coeff_mem, simp)
 apply (frule_tac a = "f (Suc n)" and b = "g (Suc n)" in 
                      Subring_pOp_ring_pOp[of S], simp, simp)
apply simp
done

lemma (in PolynRg) polyn_add_n:"\<lbrakk>pol_coeff S (n, f); pol_coeff S (n, g)\<rbrakk> \<Longrightarrow> 
      (polyn_expr R X n (n, f)) \<plusminus> (polyn_expr R X n (n, g)) =  
           nsum R (\<lambda>j. ((f j) \<plusminus>\<^bsub>S\<^esub> (g j)) \<cdot>\<^sub>r (X^\<^bsup>R j\<^esup>)) n"
by (simp add:polyn_addTr)

definition
  add_cf :: "[('a, 'm) Ring_scheme, nat \<times> (nat \<Rightarrow> 'a), nat \<times> (nat \<Rightarrow> 'a)] \<Rightarrow>
                     nat \<times> (nat \<Rightarrow> 'a)" where
  "add_cf S c d =
    (if (fst c) < (fst d) then ((fst d),  \<lambda>j. (if j \<le> (fst c)
                                               then (((snd c) j) \<plusminus>\<^bsub>S\<^esub> ((snd d) j)) else ((snd d) j)))
     else if (fst c) = (fst d) then ((fst c), \<lambda>j. ((snd c) j \<plusminus>\<^bsub>S\<^esub> (snd d) j))
     else ((fst c), \<lambda>j. (if j \<le> (fst d) then 
                        ((snd c) j \<plusminus>\<^bsub>S\<^esub> (snd d) j) else ((snd c) j))))" 

lemma (in PolynRg) add_cf_pol_coeff:"\<lbrakk>pol_coeff S c; pol_coeff S d\<rbrakk>
      \<Longrightarrow>  pol_coeff S (add_cf S c d)"
apply (cut_tac subring,
       frule subring_Ring[of S], frule Ring.ring_is_ag[of S])
 apply (simp add:pol_coeff_def)
 apply (rule allI, rule impI) 
 
apply (case_tac "(fst c) < (fst d)", simp add:add_cf_def)
 apply (rule impI, rule aGroup.ag_pOp_closed, assumption+, simp+)
 apply (drule leI[of "fst c" "fst d"],
              drule le_imp_less_or_eq[of "fst d" "fst c"])
apply (erule disjE)
 apply (simp add:add_cf_def, rule impI)
 apply (frule Ring.ring_is_ag[of S], rule aGroup.ag_pOp_closed, assumption,
       simp+)

apply (simp add:add_cf_def)
apply (frule Ring.ring_is_ag[of S], rule aGroup.ag_pOp_closed, assumption,
       simp+)
done  

lemma (in PolynRg) add_cf_len:"\<lbrakk>pol_coeff S c; pol_coeff S d\<rbrakk>
      \<Longrightarrow> fst (add_cf S c d) = (max (fst c) (fst d))" 
by (simp add: add_cf_def max.absorb1 max.absorb2)

lemma (in PolynRg) polyn_expr_restrict1:"\<lbrakk>pol_coeff S (n, f);
    pol_coeff S (Suc (m + n), g)\<rbrakk> \<Longrightarrow> 
    polyn_expr R X (m + n) (add_cf S (n, f) (m + n, g)) = 
    polyn_expr R X (m + n) (m + n, snd (add_cf S (n, f) (Suc (m + n), g)))"
apply (frule pol_coeff_pre[of "m+n" g])
apply (frule add_cf_pol_coeff[of "(n, f)" "(Suc (m + n), g)"], assumption+,
       frule add_cf_pol_coeff[of "(n, f)" "(m + n, g)"], assumption+)
apply (rule polyn_exprs_eq[of "add_cf S (n, f) (m + n, g)" 
       "(m + n, snd (add_cf S (n, f) (Suc (m + n), g)))" "m + n"], assumption+)
 apply (rule split_pol_coeff[of "add_cf S (n, f) (Suc (m + n), g)" "m + n"],
         assumption, simp add:add_cf_len)
 apply (simp add:add_cf_len)

apply (rule allI, rule impI)
 apply (simp add:add_cf_def)
done

lemma (in PolynRg) polyn_add_n1:"\<lbrakk>pol_coeff S (n, f); pol_coeff S (n, g)\<rbrakk> \<Longrightarrow> 
      (polyn_expr R X n (n, f)) \<plusminus> (polyn_expr R X n (n, g)) =  
                                polyn_expr R X n (add_cf S (n, f) (n, g))"
apply (subst polyn_add_n, assumption+)
 apply (simp add:polyn_expr_def add_cf_def)
done

lemma (in PolynRg) add_cf_val_hi:"(fst c) < (fst d) \<Longrightarrow>
                       snd (add_cf S c d) (fst d) = (snd d) (fst d)"
by (simp add:add_cf_def)

lemma (in PolynRg) add_cf_commute:"\<lbrakk>pol_coeff S c; pol_coeff S d\<rbrakk>
  \<Longrightarrow> \<forall>j \<le> (max (fst c) (fst d)). snd (add_cf S c d) j = 
                           snd (add_cf S d c) j"
apply (cut_tac subring, frule subring_Ring,
       frule Ring.ring_is_ag[of S])
apply (simp add: add_cf_def max.absorb1 max.absorb2)
apply (case_tac "(fst c) = (fst d)", simp add: pol_coeff_def)
 apply (rule allI, rule impI,
        rule aGroup.ag_pOp_commute[of S], simp+)

apply (case_tac "(fst d) < (fst c)", simp,
       rule allI, rule impI,
       rule aGroup.ag_pOp_commute, assumption+)
apply (frule_tac x = j and y = "fst d" and z = "fst c" in le_less_trans, 
          assumption+, frule_tac x = j and y = "fst c" in less_imp_le,
          thin_tac "j < fst c", simp add:pol_coeff_mem, simp add:pol_coeff_mem)

apply simp
apply (frule leI[of "fst d" "fst c"],
       frule noteq_le_less[of "fst c" "fst d"], assumption,
       rule allI, rule impI,
       simp)

apply (rule aGroup.ag_pOp_commute, assumption+,
       simp add:pol_coeff_mem,
       frule_tac x = j and y = "fst c" and z = "fst d" in le_less_trans, 
          assumption+, frule_tac x = j and y = "fst d" in less_imp_le,
           thin_tac "j < fst d", simp add:pol_coeff_mem)
done

lemma (in PolynRg) polyn_addTr1:"pol_coeff S (n, f) \<Longrightarrow>
  \<forall>g. pol_coeff S (n + m, g) \<longrightarrow> 
        (polyn_expr R X n (n, f) \<plusminus> (polyn_expr R X (n + m) ((n + m), g))
                   = polyn_expr R X (n + m) (add_cf S (n, f) ((n + m), g)))"
apply (cut_tac subring, frule subring_Ring)
apply (induct_tac m)
 apply (rule allI, rule impI, simp) 
 apply (simp add:polyn_add_n1)

apply (simp add:add.commute[of n])
 apply (rule allI, rule impI)
  apply (frule_tac n = "na + n" and f = g in pol_coeff_pre)
  apply (drule_tac a = g in forall_spec, assumption)
  apply (cut_tac n = "na + n" and c = "(Suc (na + n), g)" in  polyn_Suc,
         simp, simp del:npow_suc,
         thin_tac "polyn_expr R X (Suc (na + n)) (Suc (na + n), g) =
        polyn_expr R X (na + n) (Suc (na + n), g) \<plusminus>
        g (Suc (na + n)) \<cdot>\<^sub>r X^\<^bsup>R (Suc (na + n))\<^esup>")
  apply (frule_tac c = "(n, f)" and k = n in polyn_mem, simp,
         frule_tac c = "(Suc (na + n), g)" and k = "na + n" in polyn_mem, simp,
         frule_tac c = "(Suc (na + n), g)" in monomial_mem)
  apply (drule_tac a = "Suc (na + n)" in forall_spec, simp del:npow_suc,
         cut_tac ring_is_ag, 
         subst aGroup.ag_pOp_assoc[THEN sym], assumption+, simp del:npow_suc)
  apply (simp del:npow_suc add:polyn_expr_restrict) 
  apply (frule_tac c = "(n, f)" and d = "(Suc (na + n), g)" in 
         add_cf_pol_coeff, assumption+,
         frule_tac c = "(n, f)" and d = "(na + n, g)" in 
         add_cf_pol_coeff, assumption+) 
  apply (frule_tac c = "add_cf S (n, f) (Suc (na + n), g)" and 
           n = "na + n" and m = "Suc (na + n)" in polyn_n_m, simp,
         subst add_cf_len, assumption+, simp) 
  apply (cut_tac k = "Suc (na + n)" and f = "add_cf S (n, f) (Suc (na + n), g)"
          in polyn_expr_split)
  apply (frule_tac c = "(n, f)" and d = "(Suc (na + n), g)" in 
          add_cf_len, assumption+, simp del: npow_suc add: max.absorb1 max.absorb2)
  apply (thin_tac "polyn_expr R X (Suc (na + n))
         (Suc (na + n), snd (add_cf S (n, f) (Suc (na + n), g))) =
        polyn_expr R X (na + n)
         (na + n, snd (add_cf S (n, f) (Suc (na + n), g))) \<plusminus>
        \<Sigma>\<^sub>f R (\<lambda>j. snd (add_cf S (n, f) (Suc (na + n), g)) j \<cdot>\<^sub>r
                  X^\<^bsup>R j\<^esup>) (Suc (na + n)) (Suc (na + n))",
       thin_tac "polyn_expr R X (Suc (na + n)) (add_cf S (n, f) (Suc (na + n),
        g)) =
        polyn_expr R X (na + n)
         (na + n, snd (add_cf S (n, f) (Suc (na + n), g))) \<plusminus>
         \<Sigma>\<^sub>f R (\<lambda>j. snd (add_cf S (n, f) (Suc (na + n), g)) j \<cdot>\<^sub>r
                  X^\<^bsup>R j\<^esup>) (Suc (na + n)) (Suc (na + n))")
  apply (simp del:npow_suc add:fSum_def cmp_def slide_def) 
  apply (cut_tac d = "(Suc (na + n), g)" in add_cf_val_hi[of "(n, f)"],
         simp, simp del:npow_suc,
         thin_tac "snd (add_cf S (n, f) (Suc (na + n), g)) (Suc (na + n)) =
        g (Suc (na + n))")
  apply (frule_tac c = "add_cf S (n, f) (Suc (na + n), g)" and k = "na + n" in
         polyn_mem, simp,
         frule_tac c = "add_cf S (n, f) (na + n, g)" and k = "na + n" in
         polyn_mem, simp )
  apply (subst add_cf_len, assumption+, simp del:npow_suc)
 apply (frule_tac a = "polyn_expr R X (na + n) (add_cf S (n, f) (na + n, g))" 
        and b = "polyn_expr R X (na + n) (add_cf S (n, f) (Suc (na + n), g))"
        and c = "g (Suc (na + n)) \<cdot>\<^sub>r  X^\<^bsup>R (Suc (na + n))\<^esup>" in 
        aGroup.ag_pOp_add_r[of R], assumption+) 
 apply (rule_tac c = "add_cf S (n, f) (na + n, g)" and 
        d = "add_cf S (n, f) (Suc (na + n), g)" and k = "na + n" in 
        polyn_exprs_eq, assumption+, simp,
        subst add_cf_len, assumption+) 
  apply (simp)

apply (rule allI, rule impI,
        (subst add_cf_def)+, simp,
        frule_tac m = na and g = g in polyn_expr_restrict1[of n f], assumption,
        simp del:npow_suc)
done

lemma (in PolynRg) polyn_add:"\<lbrakk>pol_coeff S (n, f); pol_coeff S (m, g)\<rbrakk>
       \<Longrightarrow> polyn_expr R X n (n, f) \<plusminus> (polyn_expr R X m (m, g))
                   = polyn_expr R X (max n m) (add_cf S (n, f) (m, g))"  
apply (cut_tac less_linear[of n m])
 apply (erule disjE,
        frule polyn_addTr1[of n f "m - n"],
        drule_tac a = g in forall_spec, simp, simp add: max.absorb1 max.absorb2)

 apply (erule disjE,
        simp add:polyn_add_n1) 
apply (frule polyn_mem[of "(n, f)" n], simp,
       frule polyn_mem[of "(m, g)" m], simp)
 apply (cut_tac ring_is_ag, simp add:aGroup.ag_pOp_commute)

 apply (frule polyn_addTr1[of m g "n - m"],
        drule_tac a = f in forall_spec, simp, simp,
        frule add_cf_commute[of "(m, g)" "(n, f)"], assumption+, 
        simp add:max_def,
        frule add_cf_pol_coeff[of "(n, f)" "(m, g)"], assumption+,
        frule add_cf_pol_coeff[of "(m, g)" "(n, f)"], assumption+)
 apply (rule polyn_exprs_eq[of "add_cf S (m, g) (n, f)" 
                 "add_cf S (n, f) (m, g)" n], assumption+)
  apply (simp add:add_cf_len, simp)
done

lemma (in PolynRg) polyn_add1:"\<lbrakk>pol_coeff S c; pol_coeff S d\<rbrakk>
       \<Longrightarrow> polyn_expr R X (fst c) c \<plusminus> (polyn_expr R X (fst d) d)
                   = polyn_expr R X (max (fst c) (fst d)) (add_cf S c d)"
apply (cases c)
apply (cases d)
apply (simp add: polyn_add)
done

lemma (in PolynRg) polyn_minus_nsum:"\<lbrakk>pol_coeff S c; k \<le> (fst c)\<rbrakk> \<Longrightarrow> 
       -\<^sub>a (polyn_expr R X k c) = nsum R (\<lambda>j. ((-\<^sub>a\<^bsub>S\<^esub> ((snd c) j)) \<cdot>\<^sub>r (X^\<^bsup>R j\<^esup>))) k"
apply (cut_tac subring,
       frule subring_Ring[of S],
       frule Ring.ring_is_ag[of S],
       cut_tac ring_is_ag,
       cut_tac X_mem_R)
apply (simp add:polyn_expr_def,
       subst aGroup.nsum_minus[of R], assumption)
 apply (frule monomial_mem[of c], rule allI, rule impI,
        frule_tac i = j and j = k and k = "fst c" in le_trans, assumption+,
        simp)
apply (rule aGroup.nsum_eq, assumption,
       rule allI, rule impI, simp,
       rule aGroup.ag_mOp_closed, assumption) 
 apply (frule monomial_mem[of c],
        frule_tac i = j and j = k and k = "fst c" in le_trans, assumption+,
        simp)
apply (rule allI, rule impI,
       rule ring_tOp_closed)
apply (frule_tac j = j  in pol_coeff_mem[of c]) 
apply (frule_tac i = j and j = k and k = "fst c" in le_trans, assumption+,
       simp add:Subring_minus_ring_minus,
       frule_tac x = "(snd c) j" in mem_subring_mem_ring[of S], assumption,
       simp add:aGroup.ag_mOp_closed,
       simp add:npClose)
apply (rule allI, rule impI, simp,
       cut_tac j = j in pol_coeff_mem[of c], assumption,
       rule_tac i = j and j = k and k = "fst c" in le_trans, assumption+) 
apply (simp add:Subring_minus_ring_minus,
       frule_tac x = "(snd c) j" in mem_subring_mem_ring[of S], assumption)
apply (subst ring_inv1_1, assumption+)
apply (simp add:npClose, simp) 
done

lemma (in PolynRg) minus_pol_coeff:"pol_coeff S c \<Longrightarrow> 
                         pol_coeff S ((fst c), (\<lambda>j. (-\<^sub>a\<^bsub>S\<^esub> ((snd c) j))))"
apply (simp add:pol_coeff_def)
apply (rule allI, rule impI)
apply (cut_tac subring, frule subring_Ring)
apply (frule Ring.ring_is_ag[of "S"])
apply (rule aGroup.ag_mOp_closed, assumption)
apply simp 
done

lemma (in PolynRg) polyn_minus:"\<lbrakk>pol_coeff S c; k \<le> (fst c)\<rbrakk> \<Longrightarrow> 
       -\<^sub>a (polyn_expr R X k c) = 
                    polyn_expr R X k (fst c, (\<lambda>j. (-\<^sub>a\<^bsub>S\<^esub> ((snd c) j))))"
apply (cases c)
apply (subst polyn_minus_nsum)
apply (simp_all add: polyn_expr_def)
done

definition
  m_cf :: "[('a, 'm) Ring_scheme, nat \<times> (nat \<Rightarrow> 'a)] \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a)" where
  "m_cf S c = (fst c, (\<lambda>j. (-\<^sub>a\<^bsub>S\<^esub> ((snd c) j))))"  

lemma (in PolynRg) m_cf_pol_coeff:"pol_coeff S c \<Longrightarrow>
                              pol_coeff S (m_cf S c)"
by (simp add:m_cf_def, simp add:minus_pol_coeff)

lemma (in PolynRg) m_cf_len:"pol_coeff S c \<Longrightarrow>
                                         fst (m_cf S c) = fst c"
by (simp add:m_cf_def)

lemma (in PolynRg) polyn_minus_m_cf:"\<lbrakk>pol_coeff S c; k \<le> (fst c)\<rbrakk> \<Longrightarrow> 
        -\<^sub>a (polyn_expr R X k c) =  
                     polyn_expr R X k (m_cf S c)"
by (simp add:m_cf_def polyn_minus) 

lemma (in PolynRg) polyn_zero_minus_zero:"\<lbrakk>pol_coeff S c; k \<le> (fst c)\<rbrakk> \<Longrightarrow> 
       (polyn_expr R X k c = \<zero>) = (polyn_expr R X k (m_cf S c) = \<zero>)"
apply (cut_tac ring_is_ag)
apply (simp add:polyn_minus_m_cf[THEN sym])
apply (rule iffI, simp)
apply (simp add:aGroup.ag_inv_zero)
apply (frule polyn_mem[of c k], assumption)
apply (frule aGroup.ag_inv_inv[of "R" "polyn_expr R X k c"], assumption)
apply (simp add:aGroup.ag_inv_zero)
done

lemma (in PolynRg) coeff_0_pol_0:"\<lbrakk>pol_coeff S c; k \<le> fst c\<rbrakk> \<Longrightarrow>
       (\<forall>j\<le> k. (snd c) j = \<zero>\<^bsub>S\<^esub>) = (polyn_expr R X k c = \<zero>)"
apply (rule iffI)
apply (cut_tac ring_is_ag, cut_tac subring,
       frule subring_Ring)
apply (simp add:Subring_zero_ring_zero)
apply (simp add:polyn_expr_def,
       rule aGroup.nsum_zeroA[of R], assumption)
apply (rule allI, rule impI,
       cut_tac X_mem_R)
 apply (drule_tac a = j in forall_spec, simp,
        frule_tac n = j in npClose[of X], simp)
 apply (simp add:ring_times_0_x)
apply (cases c)
using algfree [simplified algfree_cond_def] by (auto simp add: polyn_expr_def)

subsection \<open>Multiplication of \<open>pol_exprs\<close>\<close>

subsection "Multiplication"

definition
  ext_cf :: "[('a, 'm) Ring_scheme, nat, nat \<times> (nat \<Rightarrow> 'a)] \<Rightarrow> 
                                                  nat \<times> (nat \<Rightarrow> 'a)" where
  "ext_cf S n c = (n + fst c, \<lambda>i. if n \<le> i then (snd c) (sliden n i) else \<zero>\<^bsub>S\<^esub>)"

  (* 0         0 g(0)         g(m) 
     0            n           m+n  , where (m, g) is a pol_coeff  **)

definition
  sp_cf :: "[('a, 'm) Ring_scheme, 'a, nat \<times> (nat \<Rightarrow> 'a)] \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a)" where
  "sp_cf S a c = (fst c, \<lambda>j. a \<cdot>\<^sub>r\<^bsub>S\<^esub> ((snd c) j))" (* scalar times cf *)

definition
  special_cf :: "('a, 'm) Ring_scheme \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a)" ("C\<^sub>0") where
  "C\<^sub>0 S = (0, \<lambda>j. 1\<^sub>r\<^bsub>S\<^esub>)"

lemma (in PolynRg) special_cf_pol_coeff:"pol_coeff S (C\<^sub>0 S)"  
apply (cut_tac subring, frule subring_Ring)
apply (simp add:pol_coeff_def special_cf_def)
apply (simp add:Ring.ring_one)
done

lemma (in PolynRg) special_cf_len:"fst (C\<^sub>0 S) = 0"
apply (simp add:special_cf_def)
done

lemma (in PolynRg) ext_cf_pol_coeff:"pol_coeff S c \<Longrightarrow> 
                           pol_coeff S (ext_cf S n c)"
apply (simp add: pol_coeff_def ext_cf_def sliden_def)
apply (rule impI)
apply (rule Ring.ring_zero)
apply (rule subring_Ring)
apply (rule subring)
done

lemma (in PolynRg) ext_cf_len:"pol_coeff S c \<Longrightarrow>
                   fst (ext_cf S m c) = m + fst c"
by (simp add:ext_cf_def)

lemma (in PolynRg) ext_special_cf_len:"fst (ext_cf S m (C\<^sub>0 S)) = m"
apply (cut_tac special_cf_pol_coeff)
apply (simp add:ext_cf_len special_cf_def)
done

lemma (in PolynRg) ext_cf_self:"pol_coeff S c \<Longrightarrow> 
                   \<forall>j \<le> (fst c). snd (ext_cf S 0 c) j = (snd c) j" 
apply (rule allI, rule impI, simp add:ext_cf_def sliden_def)
done

lemma (in PolynRg) ext_cf_hi:"pol_coeff S c \<Longrightarrow> 
                   (snd c) (fst c)  =
                      snd (ext_cf S n c) (n + (fst c))"
apply (subst ext_cf_def)
apply (simp add:sliden_def)
done

lemma (in PolynRg) ext_special_cf_hi:"snd (ext_cf S n (C\<^sub>0 S)) n = 1\<^sub>r\<^bsub>S\<^esub>"
apply (cut_tac special_cf_pol_coeff)
apply (cut_tac ext_cf_hi[of "C\<^sub>0 S" n, THEN sym])
apply (simp add:special_cf_def, assumption)
done
 

lemma (in PolynRg) ext_cf_lo_zero:"\<lbrakk>pol_coeff S c; 0 < n; x \<le> (n - Suc 0)\<rbrakk>
              \<Longrightarrow> snd (ext_cf S n c) x = \<zero>\<^bsub>S\<^esub>"
apply (cut_tac Suc_le_mono[THEN sym, of x "n - Suc 0"], simp,
       cut_tac x = x and y = "Suc x" and z = n in less_le_trans,
       simp, assumption,
       simp add:nat_not_le_less[THEN sym, of x n],
              thin_tac "x \<le> n - Suc 0")
apply (simp add:ext_cf_def)
done

lemma (in PolynRg) ext_special_cf_lo_zero:"\<lbrakk>0 < n; x \<le> (n - Suc 0)\<rbrakk>
              \<Longrightarrow> snd (ext_cf S n (C\<^sub>0 S)) x = \<zero>\<^bsub>S\<^esub>"
by (cut_tac special_cf_pol_coeff,
       frule ext_cf_lo_zero[of "C\<^sub>0 S" n], assumption+)

lemma (in PolynRg) sp_cf_pol_coeff:"\<lbrakk>pol_coeff S c; a \<in> carrier S\<rbrakk> \<Longrightarrow> 
                   pol_coeff S (sp_cf S a c)"
apply (cut_tac subring, frule subring_Ring)
apply (simp add:pol_coeff_def sp_cf_def,
       rule allI, rule impI,
      rule Ring.ring_tOp_closed, assumption+)
apply simp
done

lemma (in PolynRg) sp_cf_len:"\<lbrakk>pol_coeff S c; a \<in> carrier S\<rbrakk> \<Longrightarrow> 
                    fst (sp_cf S a c) = fst c"
by (simp add:sp_cf_def)

lemma (in PolynRg) sp_cf_val:"\<lbrakk>pol_coeff S c; j \<le> (fst c); a \<in> carrier S\<rbrakk> \<Longrightarrow> 
                    snd (sp_cf S a c) j =  a \<cdot>\<^sub>r\<^bsub>S\<^esub> ((snd c) j)"  
by (simp add:sp_cf_def)

lemma (in PolynRg) polyn_ext_cf_lo_zero:"\<lbrakk>pol_coeff S c; 0 < j\<rbrakk> \<Longrightarrow>  
                     polyn_expr R X (j - Suc 0) (ext_cf S j c) = \<zero>"
apply (simp add:polyn_expr_def, cut_tac ring_is_ag,
       rule aGroup.nsum_zeroA, assumption) 
apply (rule allI, rule impI)
 apply (frule_tac x = ja in ext_cf_lo_zero [of c j], assumption+)
 apply (cut_tac X_mem_R, frule_tac n = ja in npClose[of X])
 apply (cut_tac subring,
        simp add:Subring_zero_ring_zero,
        simp add:ring_times_0_x)
done
        
lemma (in PolynRg) monomial_d:"pol_coeff S c \<Longrightarrow>
                  polyn_expr R X d (ext_cf S d c) = ((snd c) 0) \<cdot>\<^sub>r X^\<^bsup>R d\<^esup>"
apply (cut_tac ring_is_ag,
       cut_tac subring,
       cut_tac  X_mem_R,
       frule subring_Ring[of S])
apply (frule pol_coeff_mem [of c 0], simp)
apply (case_tac "d = 0")
 apply simp
 apply (simp add:polyn_expr_def ext_cf_def sliden_def)
apply (frule ext_cf_pol_coeff[of c d]) 
apply (cut_tac polyn_Suc[of "d - Suc 0" "ext_cf S d c"])
apply (simp)
apply (cut_tac polyn_ext_cf_lo_zero[of c d], simp,
       thin_tac "polyn_expr R X (d - Suc 0) (ext_cf S d c) = \<zero>")
 apply (frule monomial_mem[of "ext_cf S d c"], simp add:ext_cf_len,
        drule_tac a = d in forall_spec, simp, simp add:aGroup.ag_l_zero) 
 apply (subst polyn_expr_short[of "ext_cf S d c" d], assumption,
        simp add:ext_cf_len)
 apply (simp,
        subst ext_cf_def, simp add:sliden_def , assumption+,
        simp add:ext_cf_len)
done

lemma (in PolynRg) X_to_d:" X^\<^bsup>R d\<^esup> =  polyn_expr R X d (ext_cf S d (C\<^sub>0 S))"
apply (cut_tac special_cf_pol_coeff)
apply (subst monomial_d[of "C\<^sub>0 S" d], assumption+)
apply (subst special_cf_def, simp)
apply (cut_tac subring, frule subring_Ring)
apply (simp add:Subring_one_ring_one)
apply (cut_tac X_mem_R, frule_tac n = d in npClose[of X])
apply (simp add:ring_l_one)
done

lemma (in PolynRg) c_max_ext_special_cf:"c_max S (ext_cf S n (C\<^sub>0 S)) = n"
apply (cut_tac polyn_ring_S_nonzero,
       cut_tac subring, frule subring_Ring)
apply (simp add:c_max_def special_cf_def ext_cf_def)
 apply (cut_tac n_max[of "{j. (n \<le> j \<longrightarrow> j = n) \<and> n \<le> j}" n])
 apply (erule conjE)+ apply simp
 apply (rule subsetI, simp, erule conjE, simp)
 apply (cut_tac le_refl[of n], blast)
done  

lemma (in PolynRg) scalar_times_polynTr:"a \<in> carrier S \<Longrightarrow> 
       \<forall>f. pol_coeff S (n, f) \<longrightarrow> 
        a \<cdot>\<^sub>r (polyn_expr R X n (n, f)) = polyn_expr R X n (sp_cf S a (n, f))"
apply (cut_tac subring,
       cut_tac X_mem_R,
       frule_tac x = a in mem_subring_mem_ring, assumption)
apply (induct_tac n,
       rule allI, rule impI, simp add:polyn_expr_def sp_cf_def,
       cut_tac n_in_Nsetn[of "0"])
apply (cut_tac subring_Ring,
        frule_tac c = "(0, f)" in pol_coeff_mem[of _ "0"], simp) 
apply (simp,
       frule_tac x = "f 0" in mem_subring_mem_ring, assumption) 
apply (       simp add:Subring_tOp_ring_tOp,
       frule_tac y = "f 0" in ring_tOp_closed[of a], assumption+,
       cut_tac ring_one, simp add:ring_tOp_assoc, assumption)

apply (rule allI, rule impI,
       frule subring_Ring,
       frule_tac n = n and f = f in pol_coeff_pre,
       drule_tac x = f in spec, simp) 
 apply (cut_tac n = n and c = "(Suc n, f)" in polyn_Suc, simp,
         simp del:npow_suc,
        thin_tac "polyn_expr R X (Suc n) (Suc n, f) =
           polyn_expr R X n (Suc n, f) \<plusminus> f (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup>")
 apply (cut_tac n = n and c = "sp_cf S a (Suc n, f)" in polyn_Suc,
        simp add:sp_cf_len)
 apply (frule_tac c = "(Suc n, f)" and a = a in sp_cf_len, assumption+,
        simp only:fst_conv)
 apply (cut_tac k = "Suc n" and f = "sp_cf S a (Suc n, f)" in 
        polyn_expr_split, simp del:npow_suc,
        thin_tac "polyn_expr R X (Suc n) (Suc n, snd (sp_cf S a (Suc n, f))) =
           polyn_expr R X n (sp_cf S a (Suc n, f)) \<plusminus>
           snd (sp_cf S a (Suc n, f)) (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup>",
        thin_tac "polyn_expr R X (Suc n) (sp_cf S a (Suc n, f)) =
           polyn_expr R X n (sp_cf S a (Suc n, f)) \<plusminus>
           snd (sp_cf S a (Suc n, f)) (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup>")
 apply (frule_tac c = "(Suc n, f)" and a = a in sp_cf_pol_coeff, assumption)
 apply (frule_tac c = "(Suc n, f)" and k = n in polyn_mem,
        simp,  
        frule_tac c = "(Suc n, f)" in monomial_mem,
        drule_tac a = "Suc n" in forall_spec, simp,
        simp only:snd_conv)
 apply (subst ring_distrib1, assumption+,
        subst polyn_expr_restrict, assumption+, simp del:npow_suc,
        subst sp_cf_val, assumption, simp, assumption,
              simp only:snd_conv,
        frule_tac c = "(Suc n, f)" and j = "Suc n" in pol_coeff_mem,
              simp, simp only:snd_conv,
        simp del:npow_suc add:Subring_tOp_ring_tOp,
        subst ring_tOp_assoc[THEN sym, of a], assumption+,
        simp add:mem_subring_mem_ring, rule npClose, assumption)
 apply (cut_tac ring_is_ag,
        rule aGroup.ag_pOp_add_r, assumption+,
        rule polyn_mem, rule sp_cf_pol_coeff, assumption+,
        simp add:sp_cf_len,
        rule polyn_mem, assumption, simp add:sp_cf_len,
        frule_tac c = "(Suc n, f)" and j = "Suc n" in pol_coeff_mem_R,
                simp, simp only:snd_conv,
        (rule ring_tOp_closed)+, assumption+, rule npClose, assumption)
 apply (rule_tac c = "sp_cf S a (n, f)" and d = "sp_cf S a (Suc n, f)" and 
        k = n in polyn_exprs_eq, rule sp_cf_pol_coeff, assumption+,
        simp add:sp_cf_len)

 apply (rule allI, rule impI,
        (subst sp_cf_def)+, simp)
done
 
lemma (in PolynRg) scalar_times_pol_expr:"\<lbrakk>a \<in> carrier S; pol_coeff S c; 
       n \<le> fst c\<rbrakk> \<Longrightarrow> 
           a \<cdot>\<^sub>r (polyn_expr R X n c) = polyn_expr R X n (sp_cf S a c)"
apply (cases c) apply (simp only:)
apply (rename_tac m g)
apply (thin_tac "c = (m, g)")
apply (frule_tac c = "(m, g)" and k = n in polyn_expr_short, simp,
       simp)
apply (frule scalar_times_polynTr[of a n],
       drule_tac x = g in spec)
 apply (frule_tac c = "(m, g)" and n = n in pol_coeff_le, simp, simp,
        thin_tac "polyn_expr R X n (m, g) = polyn_expr R X n (n, g)",
        thin_tac "a \<cdot>\<^sub>r polyn_expr R X n (n, g) =
           polyn_expr R X n (sp_cf S a (n, g))")
 apply (frule_tac c = "(m, g)" and n = n in pol_coeff_le, simp, simp,
        frule_tac c = "(n, g)" and a = a in sp_cf_pol_coeff, assumption,
        frule_tac c = "(m, g)" and a = a in sp_cf_pol_coeff, assumption)    
 apply (rule_tac c = "sp_cf S a (n, g)" and d = "sp_cf S a (m, g)" and 
        k = n in polyn_exprs_eq, assumption+)
        apply (simp add:sp_cf_len)
 apply (rule allI, (subst sp_cf_def)+, simp)
done

lemma (in PolynRg) sp_coeff_nonzero:"\<lbrakk>Idomain S; a \<in> carrier S; a \<noteq> \<zero>\<^bsub>S\<^esub>; 
       pol_coeff S c; (snd c) j \<noteq> \<zero>\<^bsub>S\<^esub>; j \<le> (fst c)\<rbrakk> \<Longrightarrow> 
       snd (sp_cf S a c) j \<noteq>  \<zero>\<^bsub>S\<^esub>"
apply (simp add:sp_cf_def)
apply (frule_tac y = "(snd c) j" in Idomain.idom_tOp_nonzeros[of S a], 
       assumption+,
       simp add:pol_coeff_def, simp add:Pi_def, assumption+)
done

lemma (in PolynRg) ext_cf_inductTl:"pol_coeff S (Suc n, f) \<Longrightarrow>
        polyn_expr R X (n + j) (ext_cf S j (Suc n, f)) = 
                      polyn_expr R X (n + j) (ext_cf S j (n, f))"
apply (frule pol_coeff_pre[of n f],
       frule ext_cf_pol_coeff[of "(Suc n, f)" j],
       frule ext_cf_pol_coeff[of "(n, f)" j],
       rule polyn_exprs_eq[of "ext_cf S j (Suc n, f)" "ext_cf S j (n, f)" 
         "n + j"], assumption+)
 apply (simp add:ext_cf_len)
 apply (rule allI, (subst ext_cf_def)+, simp add:sliden_def)
done

lemma (in PolynRg) low_deg_terms_zeroTr:" 
     pol_coeff S (n, f) \<longrightarrow>
     polyn_expr R X (n + j) (ext_cf S j (n, f)) = 
                     (X^\<^bsup>R j\<^esup>) \<cdot>\<^sub>r (polyn_expr R X n (n, f))"
apply (cut_tac ring_is_ag,
       cut_tac X_mem_R, frule npClose[of "X" "j"])
apply (induct_tac n)
 apply (rule impI, simp)
 apply (case_tac "j = 0", simp add:ext_cf_def sliden_def polyn_expr_def) 
 apply (frule_tac c = "(0, f)" and j = 0 in pol_coeff_mem_R, simp, simp)
 apply (simp add:ring_r_one ring_l_one)
 apply (cut_tac polyn_Suc[of "j - Suc 0" "ext_cf S j (0, f)"],
        simp del:npow_suc)
 apply (frule ext_cf_len[of "(0, f)" j],
        cut_tac polyn_expr_split[of j "ext_cf S j (0, f)"], simp,
        thin_tac "polyn_expr R X j (ext_cf S j (0, f)) =
        polyn_expr R X (j - Suc 0) (ext_cf S j (0, f)) \<plusminus>
        snd (ext_cf S j (0, f)) j \<cdot>\<^sub>r X^\<^bsup>R j\<^esup>")
 apply (simp add:polyn_ext_cf_lo_zero[of "(0, f)" j],
        thin_tac "polyn_expr R X j (j, snd (ext_cf S j (0, f))) =
        \<zero> \<plusminus> snd (ext_cf S j (0, f)) j \<cdot>\<^sub>r X^\<^bsup>R j\<^esup>",
        frule ext_cf_hi[THEN sym, of "(0, f)" j], simp add:polyn_expr_def)
  apply (frule_tac c = "(0, f)" and j = 0 in pol_coeff_mem_R, simp, simp)
  apply (subst aGroup.ag_l_zero, assumption, simp add:ring_tOp_closed,
         simp add:ring_r_one, subst ring_tOp_commute, assumption+, simp)

 apply (simp add:ext_cf_len)
apply (rule impI,
       cut_tac subring,
       cut_tac subring_Ring[of S],
       frule_tac n = n in pol_coeff_pre[of _ "f"]) 
       apply simp
 apply (subst polyn_expr_split)
 apply (cut_tac n = "n + j" and c = "ext_cf S j (Suc n, f)" in polyn_Suc,
        simp add:ext_cf_len) 
 apply (subst ext_cf_len, assumption+, simp del:npow_suc add:add.commute[of j],
       thin_tac "polyn_expr R X (Suc (n + j))
          (Suc (n + j), snd (ext_cf S j (Suc n, f))) =
         polyn_expr R X (n + j) (ext_cf S j (Suc n, f)) \<plusminus>
         snd (ext_cf S j (Suc n, f)) (Suc (n + j)) \<cdot>\<^sub>r X^\<^bsup>R (Suc (n + j))\<^esup>",
        subst ext_cf_inductTl, assumption+, simp del:npow_suc,
        thin_tac "polyn_expr R X (n + j) (ext_cf S j (n, f)) =
         X^\<^bsup>R j\<^esup> \<cdot>\<^sub>r polyn_expr R X n (n, f)")
 apply (cut_tac c1 = "(Suc n, f)" and n1 = j in ext_cf_hi[THEN sym], 
        assumption+, 
        simp del:npow_suc add:add.commute[of j])
 apply (cut_tac n = n and c = "(Suc n, f)" in polyn_Suc, simp,
        simp del:npow_suc)
 apply (frule_tac c = "(Suc n, f)" and k = n in polyn_mem, simp,
        frule_tac c = "(Suc n, f)" and j = "Suc n" in pol_coeff_mem_R, simp,
        simp del:npow_suc,
        frule_tac x = "f (Suc n)" and y = "X^\<^bsup>R (Suc n)\<^esup>" in ring_tOp_closed,
        rule npClose, assumption,
        subst ring_distrib1, assumption+)
 apply (subst polyn_expr_restrict, assumption+)
 apply (rule_tac a = "f (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc (n + j))\<^esup> " and 
             b = "X^\<^bsup>R j\<^esup> \<cdot>\<^sub>r (f (Suc n) \<cdot>\<^sub>r X^\<^bsup>R (Suc n)\<^esup>)" and 
             c = "X^\<^bsup>R j\<^esup> \<cdot>\<^sub>r polyn_expr R X n (n, f)" in aGroup.ag_pOp_add_l,
        assumption+,
        rule ring_tOp_closed, assumption+, rule npClose, assumption,
        (rule ring_tOp_closed, assumption+)+,
        simp add:polyn_mem,
        frule_tac n = "Suc n" in npClose[of X],
        subst ring_tOp_assoc[THEN sym], assumption+,
        subst ring_tOp_commute[of "X^\<^bsup>R j\<^esup>"], assumption,
               simp add:pol_coeff_mem,
        subst ring_tOp_assoc, assumption+,
        subst npMulDistr[of X], assumption, simp add:add.commute[of j])
apply simp
done
       
lemma (in PolynRg) low_deg_terms_zero:"pol_coeff S (n, f) \<Longrightarrow> 
  polyn_expr R X (n + j) (ext_cf S j (n, f)) = 
                            (X^\<^bsup>R j\<^esup>) \<cdot>\<^sub>r (polyn_expr R X n (n, f))"
by (simp add:low_deg_terms_zeroTr)

lemma (in PolynRg) low_deg_terms_zero1:"pol_coeff S c \<Longrightarrow> 
  polyn_expr R X ((fst c) + j) (ext_cf S j c) = 
                            (X^\<^bsup>R j\<^esup>) \<cdot>\<^sub>r (polyn_expr R X (fst c) c)"
by (cases c) (simp add: low_deg_terms_zeroTr)


lemma (in PolynRg) polyn_expr_tOpTr:"pol_coeff S (n, f) \<Longrightarrow> 
      \<forall>g. (pol_coeff S (m, g) \<longrightarrow> (\<exists>h. pol_coeff S ((n + m), h) \<and>
           h (n + m) = (f n) \<cdot>\<^sub>r\<^bsub>S\<^esub> (g m) \<and>
  (polyn_expr R X (n + m) (n + m, h) = 
          (polyn_expr R X n (n, f)) \<cdot>\<^sub>r (polyn_expr R X m (m, g)))))"
apply (cut_tac subring,
       cut_tac X_mem_R,
       frule subring_Ring[of S])
apply (induct_tac m)
 apply (rule allI, rule impI, simp)
 apply (simp add:polyn_expr_def [of R X 0]) 
 apply (frule_tac c = "(0,g)" in pol_coeff_mem[of _ 0], simp, simp,
        frule_tac c = "(0,g)" in pol_coeff_mem_R[of _ 0], simp, simp)
 apply (simp add:ring_r_one,
        frule_tac c = "(n, f)" and k = n in polyn_mem, simp,
        simp only:ring_tOp_commute[of "polyn_expr R X n (n, f)"],
        subst scalar_times_pol_expr, assumption+, simp) 
 apply (cut_tac f = "sp_cf S (g 0) (n, f)" in pol_coeff_split)
        apply (simp add:sp_cf_len)
 apply (cut_tac f = "sp_cf S (g 0) (n, f)" in polyn_expr_split[of n],
        simp only:sp_cf_len, simp only:fst_conv,
        frule_tac a = "g 0" in sp_cf_pol_coeff[of "(n, f)"], assumption+,
        simp,
        subgoal_tac "snd (sp_cf S (g 0) (n, f)) n = (f n) \<cdot>\<^sub>r\<^bsub>S\<^esub> (g 0)", blast) 
 apply (thin_tac "pol_coeff S (n, snd (sp_cf S (g 0) (n, f)))",
        thin_tac "polyn_expr R X n (sp_cf S (g 0) (n, f)) =
         polyn_expr R X n (n, snd (sp_cf S (g 0) (n, f)))",
        thin_tac "pol_coeff S (sp_cf S (g 0) (n, f))")
 apply (subst sp_cf_val[of "(n, f)" n], assumption+, simp, assumption, simp,
        frule_tac c = "(n,f)" in pol_coeff_mem[of _ n], simp, simp,
        simp add:Ring.ring_tOp_commute)  

apply (rule allI, rule impI)
apply (frule_tac n = na and f = g in pol_coeff_pre, 
       drule_tac a = g in forall_spec, assumption+)
apply (erule exE, (erule conjE)+) 
apply (cut_tac n = na and c = "(Suc na, g)" in polyn_Suc, (simp del:npow_suc)+,
       thin_tac "polyn_expr R X (Suc na) (Suc na, g) =
        polyn_expr R X na (Suc na, g) \<plusminus> g (Suc na) \<cdot>\<^sub>r X^\<^bsup>R (Suc na)\<^esup>",
       subst polyn_expr_restrict, assumption)
apply (frule_tac c = "(n, f)" and k = n in polyn_mem,simp del:npow_suc,
       frule_tac c = "(na, g)" and k = na in polyn_mem, simp del:npow_suc,
       frule_tac c = "(Suc na, g)" in monomial_mem, simp del:npow_suc,
       drule_tac a = "Suc na" in forall_spec, simp del:npow_suc)
apply (subst ring_distrib1, assumption+)
apply (rotate_tac 8, drule sym,
       simp del:npow_suc)
apply (thin_tac "polyn_expr R X n (n, f) \<cdot>\<^sub>r polyn_expr R X na (na, g) =
        polyn_expr R X (n + na) (n + na, h)")
apply (frule_tac c = "(Suc na, g)" and j ="Suc na" in pol_coeff_mem_R, simp,
       simp del:npow_suc,
       frule_tac c = "(Suc na, g)" and j ="Suc na" in pol_coeff_mem, simp,
       simp del:npow_suc)
apply (subst ring_tOp_commute, assumption+,
       subst ring_tOp_assoc, assumption+, rule npClose, assumption+,
       subst low_deg_terms_zero[THEN sym], assumption+)
apply (frule_tac c = "(n, f)" and n = "Suc na" in ext_cf_pol_coeff)
apply (frule_tac c = "ext_cf S (Suc na) (n, f)" and a = "g (Suc na)" in 
       sp_cf_pol_coeff, assumption)
apply (subst scalar_times_pol_expr, assumption+,
       simp add:ext_cf_len,
       cut_tac k = "n + Suc na" and 
        f = "sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f))" in 
        polyn_expr_split,
       simp only:sp_cf_len,
       thin_tac "polyn_expr R X (n + Suc na)
         (sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f))) =
        polyn_expr R X (n + Suc na)
         (fst (ext_cf S (Suc na) (n, f)),
          snd (sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f))))",
       simp only:ext_cf_len, simp only:fst_conv,
       simp add:add.commute[of _ n])
apply (subst polyn_add, assumption+,
       cut_tac f = "sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f))" in 
       pol_coeff_split, simp only:sp_cf_len, simp only:ext_cf_len,
       simp add:add.commute[of _ n], simp add: max_def,
       frule_tac c = "sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f))"
              in pol_coeff_cartesian,
       simp only:sp_cf_len, simp only:ext_cf_len, 
               simp add:add.commute[of _ n],
       thin_tac "(Suc (n + na),
         snd (sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f)))) =
        sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f))",
       frule_tac c = "(n + na, h)" and 
               d = "sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f))" in 
               add_cf_pol_coeff, assumption)
apply (cut_tac k = "Suc (n + na)" and f = "add_cf S (n + na, h)
       (sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f)))" in polyn_expr_split,
       simp only:mp,
       thin_tac "polyn_expr R X (Suc (n + na))
         (add_cf S (n + na, h)
           (sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f)))) =
        polyn_expr R X (Suc (n + na))
         (fst (add_cf S (n + na, h)
                (sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f)))),
          snd (add_cf S (n + na, h)
                (sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f)))))",
       subst add_cf_len, assumption+,
       simp add:sp_cf_len, simp add:ext_cf_len max_def,
       cut_tac f = "add_cf S (n + na, h)
           (sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f)))" in 
            pol_coeff_split,
       simp only:add_cf_len,
             simp only:sp_cf_len, simp add:ext_cf_len, simp add:max_def,
       thin_tac "pol_coeff S
         (add_cf S (n + na, h)
           (sp_cf S (g (Suc na)) (ext_cf S (Suc na) (n, f))))",
       subgoal_tac "snd (add_cf S (n + na, h) (sp_cf S (g (Suc na)) 
       (ext_cf S (Suc na) (n, f)))) (Suc (n + na)) = f n \<cdot>\<^sub>r\<^bsub>S\<^esub> g (Suc na)",
       simp add:add.commute[of _ n], blast)
 apply (subst add_cf_def, simp add:sp_cf_len ext_cf_len,
        subst sp_cf_def, simp add:ext_cf_len,
        subst ext_cf_def, simp add:sliden_def,
        frule pol_coeff_mem[of "(n, f)" n], simp, 
        simp add:Ring.ring_tOp_commute)
done

lemma (in PolynRg) polyn_expr_tOp:"\<lbrakk>
  pol_coeff S (n, f); pol_coeff S (m, g)\<rbrakk> \<Longrightarrow> \<exists>e. pol_coeff S ((n + m), e) \<and>
  e (n + m) = (f n) \<cdot>\<^sub>r\<^bsub>S\<^esub> (g m) \<and>
  polyn_expr R X (n + m)(n + m, e) = 
           (polyn_expr R X n (n, f)) \<cdot>\<^sub>r (polyn_expr R X m (m, g))"
by (simp add:polyn_expr_tOpTr) 


lemma (in PolynRg) polyn_expr_tOp_c:"\<lbrakk>pol_coeff S c; pol_coeff S d\<rbrakk> \<Longrightarrow>
      \<exists>e. pol_coeff S e \<and> (fst e = fst c + fst d) \<and>
          (snd e) (fst e) = (snd c (fst c)) \<cdot>\<^sub>r\<^bsub>S\<^esub> (snd d) (fst d) \<and>
          polyn_expr R X (fst e) e =
                  (polyn_expr R X (fst c) c) \<cdot>\<^sub>r (polyn_expr R X (fst d) d)"  
by (cases c, cases d) (simp add: polyn_expr_tOpTr)

section "The degree of a polynomial"

lemma (in PolynRg) polyn_degreeTr:"\<lbrakk>pol_coeff S c; k \<le> (fst c)\<rbrakk> \<Longrightarrow>
       (polyn_expr R X k c = \<zero> ) = ({j. j \<le> k \<and> (snd c) j \<noteq> \<zero>\<^bsub>S\<^esub>} = {})"
apply (subst coeff_0_pol_0[THEN sym, of c k], assumption+)
apply blast
done

lemma (in PolynRg) higher_part_zero:"\<lbrakk>pol_coeff S c; k < fst c;
      \<forall>j\<in>nset (Suc k) (fst c). snd c j = \<zero>\<^bsub>S\<^esub>\<rbrakk> \<Longrightarrow>   
             \<Sigma>\<^sub>f R (\<lambda>j. snd c j \<cdot>\<^sub>r X^\<^bsup>R j\<^esup>) (Suc k) (fst c) = \<zero>" 
apply (cut_tac ring_is_ag,
       rule aGroup.fSum_zero1[of R k "fst c" "\<lambda>j. snd c j \<cdot>\<^sub>r X^\<^bsup>R j\<^esup>"],
       assumption+) 
apply (rule ballI, 
       drule_tac x = j in bspec, assumption, simp)
apply (cut_tac subring, 
       simp add:Subring_zero_ring_zero,
       cut_tac X_mem_R,
       frule_tac n = j in npClose[of X],
       simp add:ring_times_0_x)
done

lemma (in PolynRg) coeff_nonzero_polyn_nonzero:"\<lbrakk>pol_coeff S c; k \<le> (fst c)\<rbrakk>
    \<Longrightarrow> (polyn_expr R X k c \<noteq> \<zero>) = (\<exists>j\<le>k. (snd c) j \<noteq> \<zero>\<^bsub>S\<^esub> )" 
by (simp add:coeff_0_pol_0[THEN sym, of c k])


lemma (in PolynRg) pol_expr_unique:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>; 
      pol_coeff S c; p = polyn_expr R X (fst c) c; (snd c) (fst c) \<noteq> \<zero>\<^bsub>S\<^esub>; 
      pol_coeff S d; p = polyn_expr R X (fst d) d; (snd d) (fst d) \<noteq> \<zero>\<^bsub>S\<^esub>\<rbrakk> \<Longrightarrow>
      (fst c) = (fst d) \<and> (\<forall>j \<le> (fst c). (snd c) j = (snd d) j)"
apply (cut_tac ring_is_ag, 
       cut_tac subring, frule subring_Ring,
       frule Ring.ring_is_ag[of S])
apply (frule m_cf_pol_coeff[of d])
apply (frule polyn_minus_m_cf[of d "fst d"], simp)
 apply (drule sym, drule sym, simp)
 apply (rotate_tac -2, drule sym, drule sym)
 apply (frule_tac x = p in aGroup.ag_r_inv1[of R], assumption, simp,
        thin_tac "p = polyn_expr R X (fst c) c",
        thin_tac "polyn_expr R X (fst d) d = polyn_expr R X (fst c) c",
        thin_tac "-\<^sub>a (polyn_expr R X (fst c) c) = 
                                    polyn_expr R X (fst d) (m_cf S d)")
 apply (frule polyn_add1[of c "m_cf S d"], assumption+, simp add:m_cf_len,
        thin_tac "polyn_expr R X (fst c) c \<plusminus> polyn_expr R X (fst d) (m_cf S d)
           = polyn_expr R X (max (fst c) (fst d)) (add_cf S c (m_cf S d))",
        thin_tac "polyn_expr R X (fst c) c \<noteq>
           polyn_expr R X (max (fst c) (fst d)) (add_cf S c (m_cf S d))")
 apply (frule_tac add_cf_pol_coeff[of c "m_cf S d"], simp add:m_cf_len)
 apply (cut_tac coeff_0_pol_0[THEN sym, of "add_cf S c (m_cf S d)" 
                  "max (fst c) (fst d)"],
        drule sym, simp,
        thin_tac "polyn_expr R X (max (fst c) (fst d)) 
                                         (add_cf S c (m_cf S d)) = \<zero>",
        thin_tac "pol_coeff S (add_cf S c (m_cf S d))",
        thin_tac "pol_coeff S (m_cf S d)") 

apply (case_tac "fst c = fst d", simp)
    apply (rule allI, rule impI, 
           drule_tac a = j in forall_spec, assumption)
          apply (simp add:add_cf_def m_cf_def m_cf_len)
     apply (frule_tac j = j in pol_coeff_mem[of c], simp,
            frule_tac j = j in  pol_coeff_mem[of d], simp)
   apply (subst aGroup.ag_eq_diffzero[of S], assumption+)

 apply (simp add:add_cf_def)
 apply (case_tac "\<not> (fst c) \<le> (fst d)", simp)
   apply (simp add:m_cf_len)
  apply (drule_tac a = "fst c" in forall_spec, simp, simp)

 apply simp
 apply (drule_tac a = "fst d" in forall_spec, simp, simp add:m_cf_len)
 apply (case_tac "fst c \<noteq> fst d", 
        frule noteq_le_less[of "fst c" "fst d"], assumption, simp)
        apply (simp add:m_cf_def)
        apply (frule pol_coeff_mem[of d "fst d"], simp)
        apply (frule Ring.ring_is_ag[of S], 
               frule aGroup.ag_inv_inv[of S "snd d (fst d)"], assumption)
               apply (simp add:aGroup.ag_inv_zero)
 apply simp
 apply simp
 apply (simp add:add_cf_len m_cf_len)
done

lemma (in PolynRg) pol_expr_unique2:"\<lbrakk>pol_coeff S c; pol_coeff S d; 
      fst c = fst d\<rbrakk> \<Longrightarrow>
  (polyn_expr R X (fst c) c = polyn_expr R X (fst d) d ) =
      (\<forall>j \<le> (fst c). (snd c) j = (snd d) j)"
apply (cut_tac ring_is_ag, 
       cut_tac subring, frule subring_Ring,
       frule Ring.ring_is_ag[of S])
apply (rule iffI)
apply (frule m_cf_pol_coeff[of d])
 apply (frule polyn_mem[of c "fst c"], simp,
        frule polyn_mem[of d "fst d"], simp)
 apply (frule aGroup.ag_eq_diffzero[of R "polyn_expr R X (fst c) c" 
                   "polyn_expr R X (fst d) d"], assumption+,
        simp,
        simp only:polyn_minus_m_cf[of d "fst d"],
        drule sym, simp)
 apply (frule polyn_add1[of c "m_cf S d"], assumption+, simp add:m_cf_len)
 apply (thin_tac "polyn_expr R X (fst c) d \<plusminus> polyn_expr R X (fst c) 
         (m_cf S d) =
         polyn_expr R X (fst c) (add_cf S c (m_cf S d))",
        thin_tac "polyn_expr R X (fst c) c = polyn_expr R X (fst c) d",
        thin_tac "polyn_expr R X (fst c) d \<in> carrier R",
        drule sym)
 apply (frule_tac add_cf_pol_coeff[of c "m_cf S d"], simp add:m_cf_len)
 apply (frule coeff_0_pol_0[THEN sym, of "add_cf S c (m_cf S d)" 
                "fst c"],
        simp add:add_cf_len, simp add:m_cf_len,
        thin_tac "\<zero> = polyn_expr R X (fst d) (add_cf S c (m_cf S d))",
        thin_tac "pol_coeff S (add_cf S c (m_cf S d))")
 apply (simp add:add_cf_def m_cf_def)
  apply (rule allI, rule impI)
  apply (drule_tac a = j in forall_spec, assumption)
  apply (frule_tac j = j in pol_coeff_mem[of c], simp,
         frule_tac j = j in pol_coeff_mem[of d], simp)
  apply (simp add:aGroup.ag_eq_diffzero[THEN sym])

 apply simp
 apply (rule polyn_exprs_eq[of c d "fst d"], assumption+)
        apply (simp, assumption+)
done

lemma (in PolynRg) pol_expr_unique3:"\<lbrakk>pol_coeff S c; pol_coeff S d; 
      fst c < fst d\<rbrakk> \<Longrightarrow>
  (polyn_expr R X (fst c) c = polyn_expr R X (fst d) d ) =
      ((\<forall>j \<le> (fst c). (snd c) j = (snd d) j) \<and>
                        (\<forall>j\<in>nset (Suc (fst c)) (fst d). (snd d) j = \<zero>\<^bsub>S\<^esub>))"
apply (rule iffI)
apply (cut_tac ring_is_ag, 
       cut_tac subring, frule subring_Ring,
       frule Ring.ring_is_ag[of S])
apply (frule m_cf_pol_coeff[of d])
 apply (frule polyn_mem[of c "fst c"], simp,
        frule polyn_mem[of d "fst d"], simp)
 apply (frule aGroup.ag_eq_diffzero[of R "polyn_expr R X (fst c) c" 
                   "polyn_expr R X (fst d) d"], assumption+,
        simp,
        simp only:polyn_minus_m_cf[of d "fst d"],
        drule sym, simp)
 apply (frule polyn_add1[of c "m_cf S d"], assumption+, simp add:m_cf_len,
        thin_tac "polyn_expr R X (fst c) c \<plusminus> polyn_expr R X (fst d) 
         (m_cf S d) =
         polyn_expr R X (max (fst c) (fst d)) (add_cf S c (m_cf S d))",
        thin_tac "polyn_expr R X (fst d) d = polyn_expr R X (fst c) c",
        thin_tac "polyn_expr R X (fst c) c \<in> carrier R", drule sym)
 apply (frule_tac add_cf_pol_coeff[of c "m_cf S d"], simp add:m_cf_len)
 apply (frule coeff_0_pol_0[THEN sym, of "add_cf S c (m_cf S d)" 
                "max (fst c) (fst d)"],
        simp add:add_cf_len m_cf_len, simp,
        thin_tac "polyn_expr R X (max (fst c) (fst d)) 
                                          (add_cf S c (m_cf S d)) = \<zero>",
        thin_tac "pol_coeff S (add_cf S c (m_cf S d))")
 apply (simp add:add_cf_def m_cf_def max_def)
 apply (rule conjI)
  apply (rule allI, rule impI,
         frule_tac x = j and y = "fst c" and z = "fst d" in le_less_trans, 
         assumption+,
         frule_tac x = j and y = "fst d" in less_imp_le)
  apply (drule_tac a = j in forall_spec, simp, simp)
  apply (frule_tac j = j in pol_coeff_mem[of c], simp,
         frule_tac j = j in pol_coeff_mem[of d], simp)
  apply (simp add:aGroup.ag_eq_diffzero[THEN sym])

  apply (rule ballI, simp add:nset_def, erule conjE)
  apply (cut_tac x = "fst c" and y = "Suc (fst c)" and z = j in 
         less_le_trans, simp, assumption)
  apply (cut_tac m1 = "fst c" and n1 = j in nat_not_le_less[THEN sym], simp)
  apply (drule_tac a = j in forall_spec, assumption, simp,
         frule_tac j = j in pol_coeff_mem[of d], simp)
  apply (frule_tac x = "snd d j" in aGroup.ag_inv_inv[of S], assumption,
         simp add:aGroup.ag_inv_inv aGroup.ag_inv_zero)
 apply (cut_tac polyn_n_m[of d "fst c" "fst d"])
 apply (subst polyn_expr_split[of "fst d" d], simp,
        thin_tac "polyn_expr R X (fst d) d =
     polyn_expr R X (fst c) (fst c, snd d) \<plusminus>
     \<Sigma>\<^sub>f R (\<lambda>j. snd d j \<cdot>\<^sub>r X^\<^bsup>R j\<^esup>) (Suc (fst c)) (fst d)", erule conjE) 
 apply (subst higher_part_zero[of d "fst c"], assumption+)
 apply (frule pol_coeff_le[of d "fst c"], simp add:less_imp_le,
        frule polyn_mem[of "(fst c, snd d)" "fst c"], simp,
        cut_tac ring_is_ag,
        simp add:aGroup.ag_r_zero,
        subst polyn_expr_short[THEN sym, of d "fst c"], assumption+,
        simp add:less_imp_le)
 apply (rule polyn_exprs_eq[of c d "fst c"], assumption+)
        apply (simp, assumption+)
 apply (simp add:less_imp_le)
done

lemma (in PolynRg) polyn_degree_unique:"\<lbrakk>pol_coeff S c; pol_coeff S d;
      polyn_expr R X (fst c) c = polyn_expr R X (fst d) d\<rbrakk> \<Longrightarrow> 
      c_max S c = c_max S d" 
apply (cut_tac ring_is_ag,
       cut_tac subring,
       frule subring_Ring,
       frule Ring.ring_is_ag[of S])

apply (case_tac "polyn_expr R X (fst d) d = \<zero>\<^bsub>R\<^esub>")
 apply (cut_tac coeff_0_pol_0[THEN sym, of d "fst d"], simp,
        cut_tac coeff_0_pol_0[THEN sym, of c "fst c"], simp)
 apply (simp add:c_max_def, assumption, simp, assumption, simp)

apply (frule polyn_mem[of c "fst c"], simp, frule polyn_mem[of d "fst d"], 
       simp)
apply (frule aGroup.ag_eq_diffzero[of "R" "polyn_expr R X (fst c) c" 
               "polyn_expr R X (fst d) d"], assumption+)
apply (simp only:polyn_minus_m_cf[of d "fst d"],
       frule m_cf_pol_coeff [of d])
apply (frule polyn_add1[of c "m_cf S d"], assumption+,
       simp only:m_cf_len) 
apply (rotate_tac -1, drule sym, simp,
       thin_tac "polyn_expr R X (fst d) d \<plusminus>
                         polyn_expr R X (fst d) (m_cf S d) = \<zero>",
       frule add_cf_pol_coeff[of c "m_cf S d"], assumption+)
apply (cut_tac coeff_0_pol_0[THEN sym, of "add_cf S c (m_cf S d)" 
                "fst (add_cf S c (m_cf S d))"],
       simp add:add_cf_len m_cf_len,
       thin_tac "polyn_expr R X (max (fst c) (fst d)) 
                            (add_cf S c (m_cf S d)) = \<zero>",
       thin_tac "pol_coeff S (add_cf S c (m_cf S d))",
       thin_tac "pol_coeff S (m_cf S d)")
 apply (frule coeff_nonzero_polyn_nonzero[of d "fst d"], simp, simp)
 apply (drule sym, simp)
 apply (frule coeff_nonzero_polyn_nonzero[of c "fst c"], simp, simp)
apply (simp add:c_max_def, rule conjI, rule impI, blast,
       rule conjI, rule impI, blast)
apply (rule n_max_eq_sets)
apply (rule equalityI)
apply (rule subsetI, simp)
 apply (erule conjE)

 apply (case_tac "fst c \<le> fst d")
 apply (frule_tac i = x in le_trans[of _ "fst c" "fst d"], assumption+, simp,
        rule contrapos_pp, simp+, simp add:max_def,
        frule_tac i = x in le_trans[of _ "fst c" "fst d"], assumption+,
        drule_tac a = x in forall_spec, assumption,
        drule le_imp_less_or_eq[of "fst c" "fst d"],
        erule disjE, simp add:add_cf_def m_cf_len m_cf_def,
        frule_tac j = x in pol_coeff_mem[of c], assumption+,
        simp add:aGroup.ag_inv_zero aGroup.ag_r_zero[of S])
 
        apply (simp add:add_cf_def m_cf_len m_cf_def,
               rotate_tac -1, drule sym, simp,
               frule_tac j = x in pol_coeff_mem[of c], simp,
               simp add:aGroup.ag_inv_zero aGroup.ag_r_zero[of S])

        apply (simp add:nat_not_le_less) (* \<not> fst c \<le> fst d *)
        apply (case_tac "\<not> x \<le> (fst d)", simp,
               simp add:nat_not_le_less,
               frule_tac x = "fst d" and y = x and z = "fst c" in 
               less_le_trans, assumption+,
               drule_tac x = x in spec, simp add:max_def,
               simp add:add_cf_def m_cf_len m_cf_def)

        apply (simp,
               drule_tac x = x in spec, simp add:max_def,
               rule contrapos_pp, simp+,
               simp add:add_cf_def m_cf_len m_cf_def,
               frule_tac j = x in pol_coeff_mem[of c],
               frule_tac x = x and y = "fst d" and z = "fst c" in
               le_less_trans, assumption+, simp add:less_imp_le,
               simp add:aGroup.ag_inv_zero aGroup.ag_r_zero[of S])

 apply (rule subsetI, simp, erule conjE,
        case_tac "fst d \<le> fst c",
        frule_tac i = x and j = "fst d" and k = "fst c" in le_trans,
        assumption+, simp,
        drule_tac x = x in spec, simp add:max_def,
        rule contrapos_pp, simp+,
        simp add:add_cf_def m_cf_len m_cf_def)
   apply (case_tac "fst d = fst c", simp, rotate_tac -1, drule sym, simp,
          frule_tac j = x in pol_coeff_mem[of d], assumption,
          frule_tac x = "snd d x" in aGroup.ag_mOp_closed, assumption+,
          simp add:aGroup.ag_l_zero,
          frule_tac x = "snd d x" in aGroup.ag_inv_inv[of S],
                 assumption, simp add:aGroup.ag_inv_zero)

   apply (drule noteq_le_less[of "fst d" "fst c"], assumption,
          simp,
          frule_tac j = x in pol_coeff_mem[of d], assumption,
          frule_tac x = "snd d x" in aGroup.ag_mOp_closed, assumption+,
          simp add:aGroup.ag_l_zero,
          frule_tac x = "snd d x" in aGroup.ag_inv_inv[of S],
                 assumption, simp add:aGroup.ag_inv_zero)

   apply (simp add:nat_not_le_less,
          case_tac "\<not> x \<le> fst c", simp,
          simp add:nat_not_le_less,
          drule_tac x = x in spec, simp add:max_def,
          simp add:add_cf_def m_cf_len m_cf_def,
          frule_tac j = x in pol_coeff_mem[of d], assumption,
          frule_tac x = "snd d x" in aGroup.ag_mOp_closed, assumption+,
          simp add:aGroup.ag_l_zero,
          frule_tac x = "snd d x" in aGroup.ag_inv_inv[of S],
                 assumption, simp add:aGroup.ag_inv_zero)

   apply (simp,
          drule_tac x = x in spec, simp add:max_def,
          rule contrapos_pp, simp+,
          simp add:add_cf_def m_cf_len m_cf_def,
          frule_tac x = x and y = "fst c" and z = "fst d" in le_less_trans,
           assumption+, frule_tac x = x and y = "fst d" in less_imp_le,
          frule_tac j = x in pol_coeff_mem[of d], assumption,
          frule_tac x = "snd d x" in aGroup.ag_mOp_closed, assumption+,
          simp add:aGroup.ag_l_zero,
          frule_tac x = "snd d x" in aGroup.ag_inv_inv[of S],
                 assumption, simp add:aGroup.ag_inv_zero)

 apply (thin_tac "\<forall>j\<le>max (fst c) (fst d). snd (add_cf S c (m_cf S d)) j = \<zero>\<^bsub>S\<^esub>")
 apply (rotate_tac -1, drule sym, simp)
 apply (simp add:coeff_0_pol_0[THEN sym, of c "fst c"])
 apply blast
 apply simp+
done

lemma (in PolynRg) ex_polyn_expr:"p \<in> carrier R \<Longrightarrow>
         \<exists>c. pol_coeff S c \<and> p = polyn_expr R X (fst c) c"
apply (cut_tac S_X_generate[of p], blast)
apply assumption
done

lemma (in PolynRg) c_max_eqTr0:"\<lbrakk>pol_coeff S c; k \<le> (fst c);
     polyn_expr R X k c = polyn_expr R X (fst c) c; \<exists>j\<le>k. (snd c) j \<noteq> \<zero>\<^bsub>S\<^esub>\<rbrakk> \<Longrightarrow>
               c_max S (k, snd c) = c_max S c"
apply (simp add:polyn_expr_short[of c k],
       frule pol_coeff_le[of c k], assumption+,
       rule polyn_degree_unique[of "(k, snd c)" c], assumption+,
       simp)
done

definition
  cf_sol :: "[('a, 'b) Ring_scheme, ('a, 'b1) Ring_scheme, 'a, 'a,
                nat \<times> (nat \<Rightarrow> 'a)] \<Rightarrow> bool" where
 "cf_sol R S X p c \<longleftrightarrow> pol_coeff S c \<and> (p = polyn_expr R X (fst c) c)"

definition
  deg_n ::"[('a, 'b) Ring_scheme, ('a, 'b1) Ring_scheme, 'a, 'a] \<Rightarrow> nat" where
  "deg_n R S X p = c_max S (SOME c. cf_sol R S X p c)" 

definition
  deg ::"[('a, 'b) Ring_scheme, ('a, 'b1) Ring_scheme, 'a, 'a] \<Rightarrow> ant" where
  "deg R S X p = (if p = \<zero>\<^bsub>R\<^esub> then -\<infinity> else (an (deg_n R S X p)))"

lemma (in PolynRg) ex_cf_sol:"p \<in> carrier R \<Longrightarrow>
                                    \<exists>c. cf_sol R S X p c"
apply (unfold cf_sol_def) 
apply (frule ex_polyn_expr[of p], (erule exE)+)
apply (cut_tac n = "fst c" in le_refl, blast)
done 

lemma (in PolynRg) deg_in_aug_minf:"p \<in> carrier R \<Longrightarrow>
                                   deg R S X p \<in> Z\<^sub>-\<^sub>\<infinity>"
apply (simp add:aug_minf_def deg_def an_def)
done

lemma (in PolynRg) deg_noninf:"p \<in> carrier R \<Longrightarrow>
                                   deg R S X p \<noteq> \<infinity>"
apply (cut_tac deg_in_aug_minf[of p], simp add:deg_def,
       simp add:aug_minf_def)
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp+)
done

lemma (in PolynRg) deg_ant_int:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>\<rbrakk>
                  \<Longrightarrow> deg R S X p = ant (int (deg_n R S X p))"
by (simp add:deg_def an_def)

lemma (in PolynRg) deg_an:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>\<rbrakk>
        \<Longrightarrow> deg R S X p = an (deg_n R S X p)"
by (simp add:deg_def)

lemma (in PolynRg) pol_SOME_1:"p \<in> carrier R  \<Longrightarrow> 
             cf_sol R S X p (SOME f. cf_sol R S X p f)"
apply (frule ex_cf_sol[of p])
apply (rule_tac P = "cf_sol R S X p" in someI_ex, assumption)
done

lemma (in PolynRg) pol_SOME_2:"p \<in> carrier R \<Longrightarrow>
         pol_coeff S (SOME c. cf_sol R S X p c) \<and>  
           p = polyn_expr R X (fst (SOME c. cf_sol R S X p c))
                                      (SOME c. cf_sol R S X p c)"
apply (frule pol_SOME_1[of p])
apply (simp add:cf_sol_def)
done

lemma (in PolynRg) coeff_max_zeroTr:"pol_coeff S c \<Longrightarrow>
                   \<forall>j. j \<le> (fst c) \<and> (c_max S c) < j \<longrightarrow> (snd c) j = \<zero>\<^bsub>S\<^esub>"
apply (case_tac "\<forall>j \<le> (fst c). (snd c) j = \<zero>\<^bsub>S\<^esub>", rule allI, rule impI,
       erule conjE, simp) 
apply simp
apply (frule coeff_nonzero_polyn_nonzero[THEN sym, of c "fst c"], simp,
       simp)
apply (rule allI, rule impI, erule conjE,
       simp add:c_max_def,
       simp add:polyn_degreeTr[of c "fst c"])
apply (subgoal_tac "{j. j \<le> (fst c) \<and> (snd c) j \<noteq> \<zero>\<^bsub>S\<^esub>} \<subseteq> {j. j \<le> (fst c)}",
       frule n_max[of "{j. j \<le> (fst c) \<and> (snd c) j \<noteq> \<zero>\<^bsub>S\<^esub>}" "fst c"], blast) 
 apply (case_tac "\<forall>x\<le>fst c. snd c x = \<zero>\<^bsub>S\<^esub> ", blast, simp)
 apply (erule conjE)
apply (rule contrapos_pp, simp+,
       thin_tac "\<exists>x\<le>fst c. snd c x \<noteq> \<zero>\<^bsub>S\<^esub>",
       thin_tac "{j. j \<le> fst c \<and> snd c j \<noteq> \<zero>\<^bsub>S\<^esub>} \<subseteq> {j. j \<le> fst c}",
       thin_tac "snd c (n_max {j. j \<le> fst c \<and> snd c j \<noteq> \<zero>\<^bsub>S\<^esub>}) \<noteq> \<zero>\<^bsub>S\<^esub>",
       drule_tac a = j in forall_spec, simp)
apply simp
apply (rule subsetI, simp)
done 

lemma (in PolynRg) coeff_max_nonzeroTr:"\<lbrakk>pol_coeff S c; 
       \<exists>j \<le> (fst c). (snd c) j \<noteq> \<zero>\<^bsub>S\<^esub>\<rbrakk> \<Longrightarrow> (snd c) (c_max S c) \<noteq> \<zero>\<^bsub>S\<^esub>"
apply (simp add:c_max_def)
apply (subgoal_tac "{j. j \<le> (fst c) \<and> (snd c) j \<noteq> \<zero>\<^bsub>S\<^esub>} \<subseteq> {j. j \<le> (fst c)}",
       frule n_max[of "{j. j \<le> (fst c) \<and> (snd c) j \<noteq> \<zero>\<^bsub>S\<^esub>}" "fst c"], blast) 
apply (erule conjE, simp)

apply (rule subsetI, simp)
done

lemma (in PolynRg) coeff_max_bddTr:"pol_coeff S c \<Longrightarrow> c_max S c \<le> (fst c)"
apply (case_tac "\<forall>j\<le>(fst c). (snd c) j = \<zero>\<^bsub>S\<^esub>", simp add:c_max_def)
apply (simp add:c_max_def,
       frule polyn_degreeTr[of c "fst c"], simp, simp,
       subgoal_tac "{j. j \<le> (fst c) \<and> (snd c) j \<noteq> \<zero>\<^bsub>S\<^esub>} \<subseteq> {j. j \<le> (fst c)}",
       frule n_max[of "{j. j \<le> (fst c) \<and> (snd c) j \<noteq> \<zero>\<^bsub>S\<^esub>}" "fst c"],
       blast, erule conjE, simp)
apply (rule subsetI, simp)
done

lemma (in PolynRg) pol_coeff_max:"pol_coeff S c \<Longrightarrow> 
                             pol_coeff S ((c_max S c), snd c)"
apply (rule pol_coeff_le[of c "c_max S c"], assumption)
apply (simp add:coeff_max_bddTr)
done

lemma (in PolynRg) polyn_c_max:"pol_coeff S c \<Longrightarrow>
       polyn_expr R X (fst c) c = polyn_expr R X (c_max S c) c"
apply (case_tac "(c_max S c) = (fst c)", simp)
apply (frule coeff_max_bddTr[of c], 
       frule noteq_le_less[of "c_max S c" "fst c"], assumption)
apply (subst polyn_n_m1[of c "c_max S c" "fst c"], assumption+, simp)

apply (frule_tac polyn_mem[of c "c_max S c"], assumption+)
 apply (subst higher_part_zero[of c "c_max S c"], assumption+)
 apply (frule coeff_max_zeroTr[of c],
        rule ballI, simp add:nset_def)

apply (cut_tac ring_is_ag, simp add:aGroup.ag_r_zero)
done

lemma (in PolynRg) pol_deg_eq_c_max:"\<lbrakk>p \<in> carrier R; 
       pol_coeff S c; p = polyn_expr R X (fst c) c\<rbrakk> \<Longrightarrow> 
                   deg_n R S X p = c_max S c"
apply (cut_tac subring, frule subring_Ring)
 apply (frule polyn_c_max[of c]) 
apply (frule pol_SOME_2[of p])
apply (subst deg_n_def, erule conjE) 
apply (rule polyn_degree_unique[of "Eps (cf_sol R S X p)" "c"], simp,
       assumption)
 apply simp
done

lemma (in PolynRg) pol_deg_le_n:"\<lbrakk>p \<in> carrier R; pol_coeff S c; 
       p = polyn_expr R X (fst c) c\<rbrakk> \<Longrightarrow> deg_n R S X p \<le> (fst c)"
apply (frule  pol_deg_eq_c_max[of p c], assumption+,
       frule  coeff_max_bddTr[of c]) 
apply simp
done

lemma (in PolynRg) pol_deg_le_n1:"\<lbrakk>p \<in> carrier R; pol_coeff S c; k \<le> (fst c); 
       p = polyn_expr R X k c\<rbrakk> \<Longrightarrow> deg_n R S X p \<le> k"
apply (simp add:deg_n_def, drule sym, simp)
apply (frule pol_SOME_2[of p], erule conjE)
apply (frule pol_coeff_le[of c k], assumption)
apply (simp only:polyn_expr_short[of c k])
apply (drule sym)
apply (subst polyn_degree_unique[of "SOME c. cf_sol R S X p c" "(k, snd c)"],
       assumption+, simp)
apply (frule coeff_max_bddTr[of "(k, snd c)"], simp)
done

lemma (in PolynRg) pol_len_gt_deg:"\<lbrakk>p \<in> carrier R; pol_coeff S c; 
       p = polyn_expr R X (fst c) c; deg R S X p < (an j); j \<le> (fst c)\<rbrakk>
       \<Longrightarrow>  (snd c) j = \<zero>\<^bsub>S\<^esub>"
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>", simp, drule sym)
 apply (simp add:coeff_0_pol_0[THEN sym, of c "fst c"])
 apply (simp add:deg_def, simp add:aless_natless)
 apply (drule sym, simp)
 apply (frule coeff_max_zeroTr[of c])
 apply (simp add:pol_deg_eq_c_max)
done

lemma (in PolynRg) pol_diff_deg_less:"\<lbrakk>p \<in> carrier R; pol_coeff S c; 
      p = polyn_expr R X (fst c) c; pol_coeff S d;
      fst c = fst d; (snd c) (fst c) = (snd d) (fst d)\<rbrakk> \<Longrightarrow>
      p \<plusminus> (-\<^sub>a (polyn_expr R X (fst d) d)) = \<zero> \<or> 
     deg_n R S X (p \<plusminus> (-\<^sub>a (polyn_expr R X (fst d) d))) < (fst c)"
apply (cut_tac ring_is_ag, 
       cut_tac subring, frule subring_Ring)
apply (case_tac "p \<plusminus>\<^bsub>R\<^esub> (-\<^sub>a\<^bsub>R\<^esub> (polyn_expr R X (fst d) d)) = \<zero>\<^bsub>R\<^esub>", simp) 
apply simp
 apply (simp add:polyn_minus_m_cf[of d "fst d"],
        frule m_cf_pol_coeff[of d])
 apply (cut_tac  polyn_add1[of c "m_cf S d"], simp add:m_cf_len,
        thin_tac "polyn_expr R X (fst d) c \<plusminus> polyn_expr R X (fst d) (m_cf S d)
        = polyn_expr R X (fst d) (add_cf S c (m_cf S d))")
 apply (frule add_cf_pol_coeff[of c "m_cf S d"], assumption+)
 apply (cut_tac polyn_mem[of "add_cf S c (m_cf S d)" "fst d"],
        frule pol_deg_le_n[of "polyn_expr R X (fst d) (add_cf S c (m_cf S d))"
        "add_cf S c (m_cf S d)"], assumption+,
        simp add:add_cf_len m_cf_len,
        simp add:add_cf_len m_cf_len)
 apply (rule noteq_le_less[of "deg_n R S X (polyn_expr R X (fst d) 
         (add_cf S c (m_cf S d)))" "fst d"], assumption)
 apply (rule contrapos_pp, simp+)
 apply (cut_tac pol_deg_eq_c_max[of "polyn_expr R X (fst d) 
             (add_cf S c (m_cf S d))" "add_cf S c (m_cf S d)"],
        simp,
        thin_tac "deg_n R S X (polyn_expr R X (fst d) (add_cf S c (m_cf S d)))
                 = fst d") 
 apply (frule coeff_nonzero_polyn_nonzero[of "add_cf S c (m_cf S d)" "fst d"],
        simp add:add_cf_len m_cf_len, simp,
              thin_tac "polyn_expr R X (fst d) (add_cf S c (m_cf S d)) \<noteq> \<zero>",
        frule coeff_max_nonzeroTr[of "add_cf S c (m_cf S d)"],
        simp add:add_cf_len m_cf_len,
               thin_tac "\<exists>j\<le>fst d. snd (add_cf S c (m_cf S d)) j \<noteq> \<zero>\<^bsub>S\<^esub>",
               thin_tac "pol_coeff S (m_cf S d)",
               thin_tac "pol_coeff S (add_cf S c (m_cf S d))",
               thin_tac "polyn_expr R X (fst d) (add_cf S c (m_cf S d)) \<in> 
                         carrier R", simp,
               thin_tac "c_max S (add_cf S c (m_cf S d)) = fst d")
   apply (simp add:add_cf_def m_cf_def,
          frule pol_coeff_mem[of d "fst d"], simp,
          frule Ring.ring_is_ag[of S], 
               simp add:aGroup.ag_r_inv1, assumption+,
          simp add:add_cf_len m_cf_len, assumption,
          simp add:add_cf_len m_cf_len, assumption+)
done

lemma (in PolynRg) pol_pre_lt_deg:"\<lbrakk>p \<in> carrier R; pol_coeff S c;
      deg_n R S X p \<le> (fst c); (deg_n R S X p) \<noteq> 0;
      p = polyn_expr R X (deg_n R S X p) c \<rbrakk> \<Longrightarrow> 
 (deg_n R S X (polyn_expr R X ((deg_n R S X p) - Suc 0) c)) < (deg_n R S X p)"
apply (frule polyn_expr_short[of c "deg_n R S X p"], assumption)
apply (cut_tac pol_deg_le_n[of "polyn_expr R X (deg_n R S X p - Suc 0) c"
           "(deg_n R S X p - Suc 0, snd c)"], simp)
 apply (rule polyn_mem[of c "deg_n R S X p - Suc 0"], assumption+,
        arith,
        rule pol_coeff_le[of c "deg_n R S X p - Suc 0"], assumption,
        arith, simp)
 apply (subst polyn_expr_short[of c "deg_n R S X p - Suc 0"],
         assumption+, arith, simp)
done

lemma (in PolynRg) pol_deg_n:"\<lbrakk>p \<in> carrier R; pol_coeff S c; 
       n \<le> fst c; p = polyn_expr R X n c; (snd c) n \<noteq> \<zero>\<^bsub>S\<^esub>\<rbrakk> \<Longrightarrow>
                   deg_n R S X p = n"
apply (simp add:polyn_expr_short[of c n])
 apply (frule pol_coeff_le[of c n], assumption+,
        cut_tac pol_deg_eq_c_max[of p "(n, snd c)"],
        drule sym, simp, simp add:c_max_def)
 apply (rule conjI, rule impI, cut_tac le_refl[of n],
        thin_tac "deg_n R S X p =
        (if \<forall>x\<le>n. snd c x = \<zero>\<^bsub>S\<^esub> then 0
        else n_max {j. j \<le> fst (n, snd c) \<and> snd (n, snd c) j \<noteq> \<zero>\<^bsub>S\<^esub>})",
        drule_tac a = n in forall_spec, assumption, simp)
 apply (rule impI)
 apply (cut_tac n_max[of "{j. j \<le> n \<and> snd c j \<noteq> \<zero>\<^bsub>S\<^esub>}" n], erule conjE,
        drule_tac x = n in bspec, simp, simp)
 apply (rule subsetI, simp, blast,
        drule sym, simp, assumption)
apply simp
done

lemma (in PolynRg) pol_expr_deg:"\<lbrakk>p \<in> carrier R; p \<noteq> \<zero>\<rbrakk> 
       \<Longrightarrow> \<exists>c. pol_coeff S c \<and> deg_n R S X p \<le> (fst c) \<and> 
                p = polyn_expr R X (deg_n R S X p) c \<and> 
               (snd c) (deg_n R S X p) \<noteq> \<zero>\<^bsub>S\<^esub>"  
apply (cut_tac subring,
       frule subring_Ring)
apply (frule ex_polyn_expr[of p], erule exE, erule conjE)
 apply (frule_tac c = c in polyn_c_max)
 apply (frule_tac c = c in pol_deg_le_n[of p], assumption+)
 apply (frule_tac c1 = c and k1 ="fst c" in coeff_0_pol_0[THEN sym], simp) 
 apply (subgoal_tac "p = polyn_expr R X (deg_n R S X p) c \<and>
               snd c (deg_n R S X p) \<noteq> \<zero>\<^bsub>S\<^esub>", blast)
 apply (subst pol_deg_eq_c_max, assumption+)+
 apply simp
 apply (cut_tac c = c in coeff_max_nonzeroTr, simp+)
done

lemma (in PolynRg) deg_n_pos:"p \<in> carrier R \<Longrightarrow> 0 \<le> deg_n R S X p"
by simp

lemma (in PolynRg) pol_expr_deg1:"\<lbrakk>p \<in> carrier R; d = na (deg R S X p)\<rbrakk> \<Longrightarrow> 
                \<exists>c. (pol_coeff S c \<and> p = polyn_expr R X d c)"
apply (cut_tac subring, frule subring_Ring)
apply (case_tac "p = \<zero>\<^bsub>R\<^esub>",
       simp add:deg_def na_minf,
       subgoal_tac "pol_coeff S (0, (\<lambda>j. \<zero>\<^bsub>S\<^esub>))", 
       subgoal_tac "\<zero> = polyn_expr R X d (0, (\<lambda>j. \<zero>\<^bsub>S\<^esub>))", blast,
       cut_tac coeff_0_pol_0[of "(d, \<lambda>j. \<zero>\<^bsub>S\<^esub>)" d], simp+,
       simp add:pol_coeff_def,
       simp add:Ring.ring_zero)

apply (simp add:deg_def na_an,
       frule pol_expr_deg[of p], assumption,
       erule exE, (erule conjE)+,
       unfold split_paired_all, simp, blast)
done

end
