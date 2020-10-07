(*****************************************************************************
 * Copyright (c) 2005-2010 ETH Zurich, Switzerland
 *               2008-2015 Achim D. Brucker, Germany
 *               2009-2017 Université Paris-Sud, France
 *               2015-2017 The University of Sheffield, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *****************************************************************************)

subsection \<open>Normalisation Proofs: Integer Port\<close>
theory 
  NormalisationIntegerPortProof
  imports 
    NormalisationGenericProofs
begin

text\<open>
  Normalisation proofs which are specific to the IntegerPort address representation. 
\<close> 

lemma ConcAssoc: "C((A \<oplus> B) \<oplus> D) = C(A \<oplus> (B \<oplus> D))"
  by (simp add: C.simps)

lemma aux26[simp]: "twoNetsDistinct a b c d \<Longrightarrow> 
             dom (C (AllowPortFromTo a b p)) \<inter> dom (C (DenyAllFromTo c d)) = {}"
  apply (auto simp: PLemmas twoNetsDistinct_def netsDistinct_def)[1] 
  by auto
  
lemma wp2_aux[rule_format]: "wellformed_policy2 (xs @ [x]) \<longrightarrow> 
                             wellformed_policy2 xs"
  apply (induct xs, simp_all)
  subgoal for a xs
    apply (case_tac "a", simp_all)
    done
  done
 
lemma Cdom2: "x \<in> dom(C b) \<Longrightarrow> C (a \<oplus> b) x = (C b) x"
  by (auto simp: C.simps)

lemma wp2Conc[rule_format]: "wellformed_policy2 (x#xs) \<Longrightarrow> wellformed_policy2 xs"
  by (case_tac "x",simp_all)

lemma DAimpliesMR_E[rule_format]: "DenyAll \<in> set p \<longrightarrow>
                                   (\<exists> r. applied_rule_rev C x p = Some r)"
  apply (simp add: applied_rule_rev_def)
  apply (rule_tac xs = p in rev_induct, simp_all)
  by (metis C.simps(1) denyAllDom)


lemma DAimplieMR[rule_format]: "DenyAll \<in> set p \<Longrightarrow> applied_rule_rev C x p \<noteq> None"
  by (auto intro: DAimpliesMR_E)

lemma MRList1[rule_format]: "x \<in> dom (C a) \<Longrightarrow> applied_rule_rev C x (b@[a]) = Some a"
  by (simp add: applied_rule_rev_def)

lemma MRList2: "x \<in> dom (C a) \<Longrightarrow> applied_rule_rev C x (c@b@[a]) = Some a"
  by (simp add: applied_rule_rev_def)

lemma MRList3: 
  "x \<notin> dom (C xa) \<Longrightarrow> applied_rule_rev C x (a @ b # xs @ [xa]) = applied_rule_rev C x (a @ b # xs)"
  by (simp add: applied_rule_rev_def)

lemma CConcEnd[rule_format]: 
  "C a x = Some y \<longrightarrow>  C (list2FWpolicy (xs @ [a])) x = Some y"
 (is "?P xs")
  apply (rule_tac P = ?P in list2FWpolicy.induct)
  by (simp_all add:C.simps)

    
lemma CConcStartaux: " C a x = None \<Longrightarrow> (C aa ++ C a) x = C aa x"
  by (simp add: PLemmas)

lemma CConcStart[rule_format]: 
  "xs \<noteq> [] \<longrightarrow> C a x = None \<longrightarrow> C (list2FWpolicy (xs @ [a])) x = C (list2FWpolicy xs) x"
  apply (rule list2FWpolicy.induct)
  by (simp_all add: PLemmas)

lemma mrNnt[simp]: "applied_rule_rev C x p = Some a \<Longrightarrow> p \<noteq> []"
  apply (simp add: applied_rule_rev_def)
  by auto

lemma mr_is_C[rule_format]: 
   "applied_rule_rev C x p = Some a \<longrightarrow> C (list2FWpolicy (p)) x = C a x"
  apply (simp add: applied_rule_rev_def)
  apply (rule rev_induct,auto)
    apply (metis CConcEnd)
   apply (metis CConcEnd)
  by (metis CConcStart applied_rule_rev_def mrNnt option.exhaust)


lemma CConcStart2: 
  "p \<noteq> [] \<Longrightarrow> x \<notin> dom (C a) \<Longrightarrow> C (list2FWpolicy (p @ [a])) x = C (list2FWpolicy p) x"
  by (erule CConcStart,simp add: PLemmas)

lemma CConcEnd1: 
  "q @ p \<noteq> [] \<Longrightarrow> x \<notin> dom (C a) \<Longrightarrow> C (list2FWpolicy (q @ p @ [a])) x = C (list2FWpolicy (q @ p)) x"
  apply (subst lCdom2)
  by (rule CConcStart2, simp_all)

lemma CConcEnd2[rule_format]: 
  "x \<in> dom (C a) \<longrightarrow> C (list2FWpolicy (xs @ [a])) x = C a x"  (is "?P xs")
  apply (rule_tac P = ?P in list2FWpolicy.induct)
  by (auto simp:C.simps)

lemma bar3: 
   "x \<in> dom (C (list2FWpolicy (xs @ [xa]))) \<Longrightarrow> x \<in> dom (C (list2FWpolicy xs)) \<or> x \<in> dom (C xa)"
  by auto (metis CConcStart eq_Nil_appendI l2p_aux2 option.simps(3))

lemma CeqEnd[rule_format,simp]: 
  "a \<noteq> [] \<longrightarrow> x \<in> dom (C (list2FWpolicy a)) \<longrightarrow> C (list2FWpolicy(b@a)) x = (C (list2FWpolicy a)) x"
  apply (rule rev_induct,simp_all) 
  subgoal for xa xs
    apply (case_tac "xs \<noteq> []", simp_all)
     apply (case_tac "x \<in> dom (C xa)")
      apply (metis CConcEnd2 MRList2 mr_is_C )
     apply (metis CConcEnd1 CConcStart2 Nil_is_append_conv bar3 )
    apply (metis MRList2 eq_Nil_appendI mr_is_C )
    done
  done
    
lemma CConcStartA[rule_format,simp]: 
  "x \<in> dom (C a) \<longrightarrow> x \<in> dom (C (list2FWpolicy (a # b)))" (is "?P b")
  apply (rule_tac P = ?P in list2FWpolicy.induct)  
    apply (simp_all add: C.simps)
  done

lemma domConc: 
  "x \<in> dom (C (list2FWpolicy b)) \<Longrightarrow> b \<noteq> [] \<Longrightarrow> x \<in> dom (C (list2FWpolicy (a @ b)))"
  by (auto simp: PLemmas)

lemma CeqStart[rule_format,simp]:
  "x\<notin>dom(C(list2FWpolicy a)) \<longrightarrow> a\<noteq>[] \<longrightarrow> b\<noteq>[] \<longrightarrow> C(list2FWpolicy(b@a)) x = (C(list2FWpolicy b)) x"
  apply (rule list2FWpolicy.induct,simp_all)
   apply (auto simp: list2FWpolicyconc PLemmas)
  done 

lemma C_eq_if_mr_eq2: 
  "applied_rule_rev C x a = \<lfloor>r\<rfloor> \<Longrightarrow>
   applied_rule_rev C x b = \<lfloor>r\<rfloor> \<Longrightarrow> a \<noteq> [] \<Longrightarrow> b \<noteq> [] \<Longrightarrow> 
   C (list2FWpolicy a) x = C (list2FWpolicy b) x"
by (metis mr_is_C)

lemma nMRtoNone[rule_format]: 
  "p \<noteq> [] \<longrightarrow> applied_rule_rev C x p = None \<longrightarrow> C (list2FWpolicy p) x = None"
  apply (rule rev_induct, simp_all)
  subgoal for xa xs
    apply (case_tac "xs = []", simp_all)
    by (simp_all add: applied_rule_rev_def dom_def)
  done
    
lemma C_eq_if_mr_eq: 
 "applied_rule_rev C x b = applied_rule_rev C x a \<Longrightarrow> a \<noteq> [] \<Longrightarrow> b \<noteq> [] \<Longrightarrow> 
  C (list2FWpolicy a) x = C (list2FWpolicy b) x"
  apply (cases "applied_rule_rev C x a = None", simp_all)
   apply (subst nMRtoNone,simp_all)
   apply (subst nMRtoNone, simp_all)
  by (auto intro: C_eq_if_mr_eq2)

lemma notmatching_notdom: "applied_rule_rev C x (p@[a]) \<noteq> Some a \<Longrightarrow> x \<notin> dom (C a)"
  by (simp add: applied_rule_rev_def split: if_splits)

lemma foo3a[rule_format]: 
  "applied_rule_rev C x (a@[b]@c) = Some b \<longrightarrow>  r \<in> set c \<longrightarrow> b \<notin> set c \<longrightarrow> x \<notin> dom (C r)"
  apply (rule rev_induct) 
   apply simp_all
  apply (intro impI conjI, simp)
  subgoal for xa xs
    apply (rule_tac p = "a @ b # xs" in notmatching_notdom,simp_all)
    done
  by (metis MRList2 MRList3 append_Cons option.inject)

lemma foo3D: 
  "wellformed_policy1 p \<Longrightarrow> p = DenyAll # ps \<Longrightarrow> 
   applied_rule_rev C x p = \<lfloor>DenyAll\<rfloor> \<Longrightarrow> r \<in> set ps \<Longrightarrow> x \<notin> dom (C r)"
  by (rule_tac a = "[]" and b = "DenyAll" and c = "ps"  in foo3a, simp_all)

lemma foo4[rule_format]: 
  "set p = set s \<and> (\<forall> r. r \<in> set p \<longrightarrow> x \<notin> dom (C r)) \<longrightarrow>  (\<forall> r .r \<in> set s \<longrightarrow> x \<notin> dom (C r))"
  by simp

lemma foo5b[rule_format]: 
  "x \<in> dom (C b) \<longrightarrow> (\<forall> r. r \<in> set c \<longrightarrow> x \<notin> dom (C r)) \<longrightarrow> applied_rule_rev C x (b#c) = Some b"
  apply (simp add: applied_rule_rev_def)
  apply (rule_tac xs = c in rev_induct, simp_all)  
  done

lemma mr_first: 
  "x \<in> dom (C b) \<Longrightarrow> \<forall>r. r \<in> set c \<longrightarrow> x \<notin> dom (C r) \<Longrightarrow> s = b # c \<Longrightarrow> applied_rule_rev C x s = \<lfloor>b\<rfloor>"
  by (simp add: foo5b)

lemma mr_charn[rule_format]: 
  "a \<in> set p \<longrightarrow> (x \<in> dom (C a)) \<longrightarrow>   (\<forall> r. r \<in> set p \<and> x \<in> dom (C r) \<longrightarrow> r = a) \<longrightarrow>  
   applied_rule_rev C x p = Some a"
unfolding applied_rule_rev_def
  apply (rule_tac xs = p in rev_induct) 
  apply(simp)
  by(safe,auto)

lemma foo8: 
  "\<forall>r. r \<in> set p \<and> x \<in> dom (C r) \<longrightarrow> r = a \<Longrightarrow> set p = set s \<Longrightarrow> 
   \<forall>r. r \<in> set s \<and> x \<in> dom (C r) \<longrightarrow> r = a"
  by auto

lemma mrConcEnd[rule_format]: 
  "applied_rule_rev C x (b # p) = Some a \<longrightarrow> a \<noteq> b \<longrightarrow>  applied_rule_rev C x p = Some a"
  apply (simp add: applied_rule_rev_def)
  by (rule_tac xs = p in rev_induct,auto) 


lemma wp3tl[rule_format]: "wellformed_policy3 p \<longrightarrow> wellformed_policy3 (tl p)"
  apply (induct p, simp_all)
  subgoal for a p
    apply(case_tac a, simp_all)
    done
  done
    
lemma wp3Conc[rule_format]: "wellformed_policy3 (a#p) \<longrightarrow> wellformed_policy3 p"
  by (induct p, simp_all, case_tac a, simp_all)

lemma foo98[rule_format]:
  "applied_rule_rev C x (aa # p) = Some a \<longrightarrow> x \<in> dom (C r) \<longrightarrow>  r \<in> set p \<longrightarrow> a \<in> set p"
  unfolding applied_rule_rev_def
  apply (rule rev_induct, simp_all)
  subgoal for xa xs
    apply (case_tac "r = xa", simp_all)
    done
  done

lemma mrMTNone[simp]: "applied_rule_rev C x [] = None"
  by (simp add: applied_rule_rev_def)

lemma DAAux[simp]: "x \<in> dom (C DenyAll)"
  by (simp add: dom_def PolicyCombinators.PolicyCombinators C.simps)

lemma mrSet[rule_format]: "applied_rule_rev C x p = Some r \<longrightarrow> r \<in> set p"
  unfolding applied_rule_rev_def
  by (rule_tac xs=p in rev_induct, simp_all)


lemma mr_not_Conc: "singleCombinators p \<Longrightarrow> applied_rule_rev C x p \<noteq> Some (a\<oplus>b)"
  apply (auto simp:  mrSet)
  apply (drule mrSet)
  apply (erule SCnotConc,simp)
  done


lemma foo25[rule_format]: "wellformed_policy3 (p@[x]) \<longrightarrow> wellformed_policy3 p"
  by (induct p, simp_all, case_tac a, simp_all)

lemma mr_in_dom[rule_format]: "applied_rule_rev C x p = Some a \<longrightarrow> x \<in> dom (C a)"
  apply (rule_tac xs = p in rev_induct)
  by (auto simp: applied_rule_rev_def)


lemma wp3EndMT[rule_format]: 
  "wellformed_policy3 (p@[xs]) \<longrightarrow>  AllowPortFromTo a b po \<in> set p \<longrightarrow>
   dom (C (AllowPortFromTo a b po)) \<inter> dom (C xs) = {}"
  apply (induct p,simp_all)
  apply (intro impI,drule mp,erule wp3Conc)
  by clarify auto

lemma foo29: "\<lbrakk>dom (C a) \<noteq> {}; dom (C a) \<inter> dom (C b) = {}\<rbrakk> \<Longrightarrow> a \<noteq> b" by auto

lemma foo28:  
  "AllowPortFromTo a b po \<in> set p \<Longrightarrow> dom (C (AllowPortFromTo a b po)) \<noteq> {} \<Longrightarrow> 
   wellformed_policy3 (p @ [x])   \<Longrightarrow> x \<noteq> AllowPortFromTo a b po"
  by (metis foo29 C.simps(3) wp3EndMT)

lemma foo28a[rule_format]: "x \<in> dom (C a) \<Longrightarrow> dom (C a) \<noteq> {}" by auto

lemma allow_deny_dom[simp]: 
  "dom (C (AllowPortFromTo a b po)) \<subseteq> dom (C (DenyAllFromTo a b))"
  by (simp_all add: twoNetsDistinct_def netsDistinct_def PLemmas) auto 

lemma DenyAllowDisj: 
  "dom (C (AllowPortFromTo a b p)) \<noteq> {} \<Longrightarrow> 
   dom (C (DenyAllFromTo a b)) \<inter> dom (C (AllowPortFromTo a b p))  \<noteq> {}"
  by (metis Int_absorb1 allow_deny_dom)

lemma foo31: 
  "\<forall>r. r \<in> set p \<and> x \<in> dom (C r) \<longrightarrow> 
       r = AllowPortFromTo a b po \<or> r = DenyAllFromTo a b \<or> r = DenyAll \<Longrightarrow>
   set p = set s \<Longrightarrow> 
   \<forall>r. r \<in> set s \<and> x \<in> dom (C r) \<longrightarrow> r=AllowPortFromTo a b po \<or> r = DenyAllFromTo a b \<or> r = DenyAll"
  by auto

lemma wp1_auxa: 
  "wellformed_policy1_strong p\<Longrightarrow>(\<exists> r. applied_rule_rev C x p = Some r)"
  apply (rule DAimpliesMR_E)
  by (erule wp1_aux1aa)

lemma deny_dom[simp]:  
  "twoNetsDistinct a b c d \<Longrightarrow> dom (C (DenyAllFromTo a b)) \<inter> dom (C (DenyAllFromTo c d)) = {}"
  apply (simp add: C.simps)
  by (erule aux6)

lemma domTrans: "dom a \<subseteq> dom b \<Longrightarrow> dom b \<inter> dom c = {} \<Longrightarrow> dom a \<inter> dom c = {}" by auto

lemma DomInterAllowsMT:
  "twoNetsDistinct a b c d  \<Longrightarrow> 
dom (C (AllowPortFromTo a b p)) \<inter> dom (C (AllowPortFromTo c d po)) = {}"
  apply (case_tac "p = po", simp_all)
   apply (rule_tac b = "C (DenyAllFromTo a b)" in domTrans, simp_all)
   apply (metis domComm aux26 tNDComm)
  by (simp add: twoNetsDistinct_def netsDistinct_def PLemmas) auto

lemma DomInterAllowsMT_Ports: 
  "p \<noteq> po \<Longrightarrow> dom (C (AllowPortFromTo a b p)) \<inter> dom (C (AllowPortFromTo c d po)) = {}"
  by (simp add: twoNetsDistinct_def netsDistinct_def PLemmas) auto



lemma wellformed_policy3_charn[rule_format]: 
  "singleCombinators p \<longrightarrow> distinct p \<longrightarrow> allNetsDistinct p \<longrightarrow> 
   wellformed_policy1 p \<longrightarrow> wellformed_policy2 p  \<longrightarrow> wellformed_policy3 p"
  apply (induct_tac p)   
   apply simp_all
  apply (auto intro: singleCombinatorsConc ANDConc waux2 wp2Conc)
  subgoal for a list
    apply (case_tac a, simp_all, clarify)
    apply (metis C.elims DomInterAllowsMT DomInterAllowsMT_Ports aux0_0 aux7aa inf_commute) (* slow *)
    done
  done

lemma DistinctNetsDenyAllow: 
 "DenyAllFromTo b c \<in> set p \<Longrightarrow>
  AllowPortFromTo a d po \<in> set p \<Longrightarrow>
  allNetsDistinct p \<Longrightarrow> dom (C (DenyAllFromTo b c)) \<inter> dom (C (AllowPortFromTo a d po)) \<noteq> {} \<Longrightarrow> 
  b = a \<and> c = d" 
  unfolding allNetsDistinct_def
  apply (frule_tac x = "b" in spec) 
  apply (drule_tac x = "d" in spec)
  apply (drule_tac x = "a" in spec)
  apply (drule_tac x = "c" in spec)
  apply (simp,metis Int_commute ND0aux1 ND0aux3 NDComm aux26 twoNetsDistinct_def ND0aux2 ND0aux4)
  done

lemma DistinctNetsAllowAllow: 
 "AllowPortFromTo b c poo \<in> set p \<Longrightarrow>
    AllowPortFromTo a d po \<in> set p \<Longrightarrow>
    allNetsDistinct p \<Longrightarrow> 
    dom (C (AllowPortFromTo b c poo)) \<inter> dom (C (AllowPortFromTo a d po)) \<noteq> {} \<Longrightarrow> 
    b = a \<and> c = d \<and> poo = po" 
unfolding allNetsDistinct_def
  apply (frule_tac x = "b" in spec) 
  apply (drule_tac x = "d" in spec)
  apply (drule_tac x = "a" in spec)
  apply (drule_tac x = "c" in spec)
  apply (simp,metis DomInterAllowsMT DomInterAllowsMT_Ports ND0aux3 ND0aux4 NDComm 
    twoNetsDistinct_def)
  done

lemma WP2RS2[simp]: 
  "singleCombinators p \<Longrightarrow> distinct p \<Longrightarrow> allNetsDistinct p \<Longrightarrow> 
   wellformed_policy2 (removeShadowRules2 p)"
proof (induct p)
  case Nil thus ?case by simp
next   
  case (Cons x xs) 
  have wp_xs: "wellformed_policy2 (removeShadowRules2 xs)" 
    by (metis Cons ANDConc distinct.simps(2) singleCombinatorsConc)
  show ?case
  proof (cases x) 
    case DenyAll thus ?thesis using wp_xs by simp
  next  
    case (DenyAllFromTo a b) thus ?thesis
      using wp_xs Cons by (simp,metis DenyAllFromTo aux aux7 tNDComm deny_dom)
  next
    case (AllowPortFromTo a b p) thus ?thesis
      using  wp_xs  by (simp, metis aux26 AllowPortFromTo Cons(4) aux aux7a tNDComm)
  next
    case (Conc a b) thus ?thesis
      by (metis Conc Cons(2) singleCombinators.simps(2)) 
  qed
qed

lemma AD_aux: 
  "AllowPortFromTo a b po \<in> set p \<Longrightarrow>  DenyAllFromTo c d \<in> set p \<Longrightarrow>
   allNetsDistinct p \<Longrightarrow>  singleCombinators p \<Longrightarrow> a \<noteq> c \<or> b \<noteq> d \<Longrightarrow> 
   dom (C (AllowPortFromTo a b po)) \<inter> dom (C (DenyAllFromTo c d)) = {}"
  by (rule aux26,rule_tac x ="AllowPortFromTo a b po" and y = "DenyAllFromTo c d" in tND, auto) 
    
lemma sorted_WP2[rule_format]: "sorted p l \<longrightarrow> all_in_list p l \<longrightarrow> distinct p \<longrightarrow> 
            allNetsDistinct p \<longrightarrow> singleCombinators p \<longrightarrow> wellformed_policy2 p"
proof (induct p)
  case Nil thus ?case by simp 
next
  case (Cons a p) thus ?case
  proof (cases a)
    case DenyAll thus ?thesis using  Cons
      by (auto intro: ANDConc singleCombinatorsConc sortedConcEnd)
  next
    case (DenyAllFromTo c d) thus ?thesis using  Cons
      apply simp
      apply (intro impI conjI allI)
       apply (rule deny_dom)
       apply (auto intro:  aux7 tNDComm ANDConc singleCombinatorsConc sortedConcEnd) 
      done
  next
    case (AllowPortFromTo c d e) thus ?thesis using Cons 
      apply simp
      apply (intro impI  conjI allI aux26)
       apply (rule_tac x = "AllowPortFromTo c d e" and  y = "DenyAllFromTo aa b" in tND)
                  apply (assumption,simp_all)
       apply (subgoal_tac "smaller (AllowPortFromTo c d e) (DenyAllFromTo aa b) l") 	
        apply (simp split: if_splits)
        apply metis
       apply (erule sorted_is_smaller, simp_all)
       apply (metis bothNet.simps(2) in_list.simps(2)  in_set_in_list)
      by (auto intro: aux7 tNDComm ANDConc singleCombinatorsConc sortedConcEnd)
  next
    case (Conc a b) thus ?thesis using Cons by simp 
  qed
qed

lemma wellformed2_sorted[simp]: 
  "all_in_list p l \<Longrightarrow> distinct p \<Longrightarrow> allNetsDistinct p \<Longrightarrow> 
   singleCombinators p \<Longrightarrow> wellformed_policy2 (sort p l)"
  apply (rule sorted_WP2,erule sort_is_sorted, simp_all)
  apply (auto elim: all_in_listSubset intro: SC3 singleCombinatorsConc sorted_insort)
  done

lemma wellformed2_sortedQ[simp]: "\<lbrakk>all_in_list p l; distinct p; allNetsDistinct p;
                         singleCombinators p\<rbrakk> \<Longrightarrow> wellformed_policy2 (qsort p l)"
  apply (rule sorted_WP2,erule sort_is_sortedQ, simp_all)
   apply (auto elim: all_in_listSubset intro: SC3Q singleCombinatorsConc distinct_sortQ)
  done

lemma C_DenyAll[simp]: "C (list2FWpolicy (xs @ [DenyAll])) x = Some (deny ())"
  by (auto simp: PLemmas)

lemma C_eq_RS1n:
  "C(list2FWpolicy (removeShadowRules1_alternative p)) = C(list2FWpolicy p)"
proof (cases "p")print_cases  
  case Nil then show ?thesis apply(simp_all) 
    by (metis list2FWpolicy.simps(1) rSR1_eq removeShadowRules1.simps(2))
next
  case (Cons x list) show ?thesis 
    apply (rule rev_induct)
     apply (metis rSR1_eq removeShadowRules1.simps(2))
    subgoal for x xs
      apply (case_tac "xs = []", simp_all)
      unfolding removeShadowRules1_alternative_def
       apply (case_tac x, simp_all)
      by (metis (no_types, hide_lams) CConcEnd2 CConcStart C_DenyAll RS1n_nMT aux114 
          domIff removeShadowRules1_alternative_def 
          removeShadowRules1_alternative_rev.simps(2) rev.simps(2))
    done 
qed

lemma C_eq_RS1[simp]: 
  "p \<noteq> [] \<Longrightarrow>  C(list2FWpolicy (removeShadowRules1 p)) = C(list2FWpolicy p)"
  by (metis rSR1_eq C_eq_RS1n)
    
lemma EX_MR_aux[rule_format]: 
  "applied_rule_rev C x (DenyAll # p) \<noteq> Some DenyAll \<longrightarrow> (\<exists>y. applied_rule_rev C x p = Some y)"
  apply (simp add: applied_rule_rev_def)
  apply (rule_tac xs = p in rev_induct, simp_all)  
  done
    
lemma EX_MR : 
  "applied_rule_rev C x p \<noteq> \<lfloor>DenyAll\<rfloor> \<Longrightarrow> p = DenyAll # ps \<Longrightarrow> 
 applied_rule_rev C x p = applied_rule_rev C x ps"
  apply auto
  apply (subgoal_tac "applied_rule_rev C x (DenyAll#ps) \<noteq> None", auto)
   apply (metis mrConcEnd)
  by (metis DAimpliesMR_E list.sel(1) hd_in_set list.simps(3) not_Some_eq)

lemma mr_not_DA:
  "wellformed_policy1_strong s \<Longrightarrow>
   applied_rule_rev C x p = \<lfloor>DenyAllFromTo a ab\<rfloor> \<Longrightarrow> set p = set s \<Longrightarrow>
   applied_rule_rev C x s \<noteq> \<lfloor>DenyAll\<rfloor>"
  apply (subst wp1n_tl, simp_all)
  apply (subgoal_tac "x \<in> dom (C (DenyAllFromTo a ab))")
   apply (subgoal_tac "DenyAllFromTo a ab \<in> set (tl s)")
    apply (metis wp1n_tl foo98 wellformed_policy1_strong.simps(2))
  using mrSet r_not_DA_in_tl apply blast
  by (simp add: mr_in_dom)

lemma domsMT_notND_DD: 
  "dom (C (DenyAllFromTo a b)) \<inter> dom (C (DenyAllFromTo c d)) \<noteq> {} \<Longrightarrow> \<not> netsDistinct a c"
  using deny_dom twoNetsDistinct_def by blast

lemma domsMT_notND_DD2: 
  "dom (C (DenyAllFromTo a b)) \<inter> dom (C (DenyAllFromTo c d)) \<noteq> {} \<Longrightarrow> \<not> netsDistinct b d"
  using deny_dom twoNetsDistinct_def by blast

lemma domsMT_notND_DD3: 
  "x \<in> dom (C (DenyAllFromTo a b)) \<Longrightarrow> x \<in> dom (C (DenyAllFromTo c d)) \<Longrightarrow>  \<not> netsDistinct a c"
  by(auto intro!:domsMT_notND_DD)

lemma domsMT_notND_DD4: 
  "x \<in> dom (C (DenyAllFromTo a b)) \<Longrightarrow> x \<in> dom (C (DenyAllFromTo c d)) \<Longrightarrow> \<not> netsDistinct b d"
  by(auto intro!:domsMT_notND_DD2)

lemma NetsEq_if_sameP_DD: 
  "allNetsDistinct p \<Longrightarrow>  u \<in> set p \<Longrightarrow>  v \<in> set p \<Longrightarrow> u = DenyAllFromTo a b \<Longrightarrow> 
   v = DenyAllFromTo c d \<Longrightarrow> x \<in> dom (C u) \<Longrightarrow> x \<in> dom (C v) \<Longrightarrow> a = c \<and> b = d"
  apply (simp add: allNetsDistinct_def)
  by (metis ND0aux1 ND0aux2 domsMT_notND_DD3 domsMT_notND_DD4 )

lemma rule_charn1: 
  assumes aND: "allNetsDistinct p"
    and mr_is_allow: "applied_rule_rev C x p = Some (AllowPortFromTo a b po)"
    and SC: "singleCombinators p"
    and inp: "r \<in> set p" 
    and inDom: "x \<in> dom (C r)"
  shows "(r = AllowPortFromTo a b po \<or> r = DenyAllFromTo a b \<or> r = DenyAll)"
proof (cases r) 
  case DenyAll show ?thesis  by (metis DenyAll)
next
  case (DenyAllFromTo x y) show ?thesis 
    by (metis AD_aux DenyAllFromTo SC aND domInterMT inDom inp mrSet mr_in_dom mr_is_allow)
next
  case (AllowPortFromTo x y b) show ?thesis
    by (metis (no_types, lifting) AllowPortFromTo DistinctNetsAllowAllow aND domInterMT 
        inDom inp  mrSet mr_in_dom mr_is_allow)
next
  case (Conc x y) thus ?thesis using assms by (metis aux0_0)
qed
  
lemma none_MT_rulessubset[rule_format]: 
  "none_MT_rules C a \<longrightarrow> set b \<subseteq> set a \<longrightarrow> none_MT_rules C b"
  by (induct b,simp_all) (metis notMTnMT)

lemma nMTSort: "none_MT_rules C p \<Longrightarrow> none_MT_rules C (sort p l)"
  by (metis set_sort nMTeqSet)

lemma nMTSortQ: "none_MT_rules C p \<Longrightarrow> none_MT_rules C (qsort p l)"
  by (metis set_sortQ nMTeqSet)
    
lemma wp3char[rule_format]: 
  "none_MT_rules C xs \<and> C (AllowPortFromTo a b po)=\<emptyset> \<and> wellformed_policy3(xs@[DenyAllFromTo a b]) \<longrightarrow>
 AllowPortFromTo a b po \<notin> set xs"
  apply (induct xs,simp_all)
  by (metis domNMT wp3Conc)

lemma wp3charn[rule_format]: 
  assumes domAllow: "dom (C (AllowPortFromTo a b po)) \<noteq> {}" 
    and     wp3:      "wellformed_policy3 (xs @ [DenyAllFromTo a b])"
  shows             "AllowPortFromTo a b po \<notin> set xs"
  apply (insert assms)
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x xs) show ?case using Cons
    by (simp,auto intro: wp3Conc) (auto simp: DenyAllowDisj domAllow)
qed

lemma rule_charn2: 
  assumes aND: "allNetsDistinct p"
    and wp1: "wellformed_policy1 p"
    and SC: "singleCombinators p"
    and wp3: "wellformed_policy3 p"
    and allow_in_list: "AllowPortFromTo c d po \<in> set p"
    and x_in_dom_allow: "x \<in> dom (C (AllowPortFromTo c d po))"
  shows  "applied_rule_rev C x p = Some (AllowPortFromTo c d po)"
proof  (insert assms, induct p rule: rev_induct)    
  case Nil show ?case using Nil by simp
next 
  case (snoc y ys)
  show ?case using snoc
    apply (case_tac "y = (AllowPortFromTo c d po)", simp_all )
     apply (simp add: applied_rule_rev_def)
    apply (subgoal_tac "ys \<noteq> []")
     apply (subgoal_tac "applied_rule_rev C x ys = Some (AllowPortFromTo c d po)")
      defer 1
      apply (metis ANDConcEnd SCConcEnd WP1ConcEnd foo25) 
     apply (metis inSet_not_MT)
  proof (cases y)
    case DenyAll thus ?thesis using DenyAll snoc    
      apply simp
      by (metis DAnotTL DenyAll inSet_not_MT policy2list.simps(2))
  next
    case (DenyAllFromTo a b) thus ?thesis using snoc apply simp
      apply (simp_all add: applied_rule_rev_def)
      apply (rule conjI)
       apply (metis domInterMT  wp3EndMT)
      apply (rule impI)
      by (metis ANDConcEnd DenyAllFromTo SCConcEnd WP1ConcEnd foo25)
  next
    case (AllowPortFromTo a1 a2 b) thus ?thesis 
      using AllowPortFromTo snoc apply simp
      apply (simp_all add: applied_rule_rev_def)
      apply (rule conjI)
       apply (metis domInterMT  wp3EndMT)
      by (metis ANDConcEnd AllowPortFromTo SCConcEnd WP1ConcEnd foo25 x_in_dom_allow)
  next
    case (Conc a b) thus ?thesis using Conc snoc apply simp
      by (metis Conc aux0_0 in_set_conv_decomp) 
  qed
qed
  
lemma rule_charn3: 
  " wellformed_policy1 p \<Longrightarrow> allNetsDistinct p \<Longrightarrow> singleCombinators p \<Longrightarrow>
   wellformed_policy3 p \<Longrightarrow> applied_rule_rev C x p = \<lfloor>DenyAllFromTo c d\<rfloor> \<Longrightarrow> 
   AllowPortFromTo a b po \<in> set p \<Longrightarrow> x \<notin> dom (C (AllowPortFromTo a b po))"
  by (clarify, auto simp: rule_charn2 dom_def) 
    
lemma rule_charn4: 
  assumes wp1: "wellformed_policy1 p" 
    and aND: "allNetsDistinct p" 
    and SC: "singleCombinators p"
    and wp3: "wellformed_policy3 p"  
    and DA: "DenyAll \<notin> set p" 
    and mr: "applied_rule_rev C x p = Some (DenyAllFromTo a b)"
    and rinp: "r \<in> set p"
    and xindom: "x \<in> dom (C r)"
  shows "r = DenyAllFromTo a b"
proof (cases r)
  case DenyAll thus ?thesis using DenyAll assms by simp 
next
  case (DenyAllFromTo c d) thus ?thesis using assms apply simp
    apply (erule_tac x = x and p = p and v = "(DenyAllFromTo a b)" and
        u = "(DenyAllFromTo c d)"  in NetsEq_if_sameP_DD)
         apply simp_all
     apply (erule mrSet)
    by (erule mr_in_dom) 
next
  case (AllowPortFromTo c d e) thus ?thesis using assms apply simp
    apply (subgoal_tac "x \<notin> dom (C  (AllowPortFromTo c d e))")
     apply simp 
    apply (rule_tac p = p in rule_charn3)
    by (auto intro: SCnotConc) 
next
  case (Conc a b) thus ?thesis using assms apply simp 
    by (metis Conc aux0_0) 
qed

lemma foo31a: 
  "\<forall>r. r \<in> set p \<and> x \<in> dom (C r) \<longrightarrow> r=AllowPortFromTo a b po \<or> r=DenyAllFromTo a b \<or> r=DenyAll \<Longrightarrow>
    set p = set s \<Longrightarrow> r \<in> set s \<Longrightarrow> x \<in> dom (C r) \<Longrightarrow> 
   r = AllowPortFromTo a b po \<or> r = DenyAllFromTo a b \<or> r = DenyAll"
  by auto

lemma aux4[rule_format]: 
  "applied_rule_rev C x (a#p) = Some a \<longrightarrow> a \<notin> set (p) \<longrightarrow> applied_rule_rev C x p = None"
  apply (rule rev_induct,simp_all)
  by (metis aux0_4 empty_iff empty_set insert_iff list.simps(15) mrSet mreq_end3)

lemma mrDA_tl: 
  assumes mr_DA: "applied_rule_rev C x p = Some DenyAll"
    and     wp1n:  "wellformed_policy1_strong p"
  shows          "applied_rule_rev C x (tl p) = None"
  apply (rule aux4 [where a = DenyAll])
   apply (metis wp1n_tl mr_DA wp1n)
  by (metis WP1n_DA_notinSet wp1n)
    
lemma rule_charnDAFT: 
  "wellformed_policy1_strong p \<Longrightarrow>  allNetsDistinct p \<Longrightarrow>  singleCombinators p \<Longrightarrow>
    wellformed_policy3 p \<Longrightarrow> applied_rule_rev C x p = \<lfloor>DenyAllFromTo a b\<rfloor> \<Longrightarrow> r \<in> set (tl p) \<Longrightarrow> 
    x \<in> dom (C r) \<Longrightarrow> r = DenyAllFromTo a b"
  apply (subgoal_tac "p = DenyAll#(tl p)")
   apply (metis AND_tl Combinators.distinct(1) SC_tl list.sel(3) mrConcEnd rule_charn4 waux2 wellformed_policy1_charn wp1_aux1aa wp1_eq wp3tl)
  using wp1n_tl by blast 

lemma mrDenyAll_is_unique: 
  "\<lbrakk>wellformed_policy1_strong p; applied_rule_rev C x p = Some DenyAll;
   r \<in> set (tl p)\<rbrakk> \<Longrightarrow> x \<notin> dom (C r)"
  apply (rule_tac a = "[]" and b = "DenyAll" and c = "tl p"  in foo3a, simp_all)  
   apply (metis wp1n_tl)
  by (metis WP1n_DA_notinSet)

theorem  C_eq_Sets_mr: 
  assumes sets_eq: "set p = set s"
    and SC:          "singleCombinators p"
    and wp1_p:       "wellformed_policy1_strong p"
    and wp1_s:       "wellformed_policy1_strong s"
    and wp3_p:       "wellformed_policy3 p"       
    and wp3_s:       "wellformed_policy3 s"  
    and aND:         "allNetsDistinct p"        
  shows "applied_rule_rev C x p = applied_rule_rev C x s"
proof (cases "applied_rule_rev C x p")
  case None 
  have DA: "DenyAll \<in> set p" using wp1_p by (auto simp: wp1_aux1aa)
  have notDA: "DenyAll \<notin> set p" using None by (auto simp: DAimplieMR) 
  thus ?thesis using DA by (contradiction)
next 
  case (Some y) thus ?thesis
  proof (cases y) 
    have tl_p: "p = DenyAll#(tl p)" by (metis wp1_p wp1n_tl) 
    have tl_s: "s = DenyAll#(tl s)" by (metis wp1_s wp1n_tl)
    have tl_eq: "set (tl p) = set (tl s)"
      by (metis list.sel(3) WP1n_DA_notinSet sets_eq foo2
          wellformed_policy1_charn wp1_aux1aa wp1_eq wp1_p wp1_s)
    {  case DenyAll
      have mr_p_is_DenyAll: "applied_rule_rev C x p = Some DenyAll"
        by (simp add: DenyAll Some)
      hence x_notin_tl_p: "\<forall> r. r \<in> set (tl p) \<longrightarrow>  x \<notin> dom (C r)" using wp1_p
        by (auto simp: mrDenyAll_is_unique)
      hence x_notin_tl_s: "\<forall> r. r \<in> set (tl s) \<longrightarrow>  x \<notin> dom (C r)" using tl_eq
        by auto
      hence mr_s_is_DenyAll: "applied_rule_rev C x s = Some DenyAll" using tl_s
        by (auto simp: mr_first)
      thus ?thesis using mr_p_is_DenyAll by simp
    }
    {case (DenyAllFromTo a b) 
      have mr_p_is_DAFT: "applied_rule_rev C x p = Some (DenyAllFromTo a b)"
        by (simp add: DenyAllFromTo Some)
      have DA_notin_tl: "DenyAll \<notin> set (tl p)"
        by (metis WP1n_DA_notinSet wp1_p)
      have mr_tl_p: "applied_rule_rev C x p = applied_rule_rev C x (tl p)"
        by (metis Combinators.simps(4) DenyAllFromTo Some mrConcEnd tl_p)
      have dom_tl_p: "\<And> r. r \<in> set (tl p) \<and> x \<in> dom (C r) \<Longrightarrow> r = (DenyAllFromTo a b)"
        using wp1_p aND SC wp3_p mr_p_is_DAFT
        by (auto simp: rule_charnDAFT)
      hence dom_tl_s: "\<And> r. r \<in> set (tl s) \<and> x \<in> dom (C r) \<Longrightarrow> r = (DenyAllFromTo a b)"
        using tl_eq  by auto
      have DAFT_in_tl_s: "DenyAllFromTo a b \<in> set (tl s)" using mr_tl_p
        by (metis DenyAllFromTo mrSet mr_p_is_DAFT tl_eq)
      have x_in_dom_DAFT: "x \<in> dom (C (DenyAllFromTo a b))"
        by (metis mr_p_is_DAFT DenyAllFromTo mr_in_dom)
      hence mr_tl_s_is_DAFT: "applied_rule_rev C x (tl s) = Some (DenyAllFromTo a b)"
        using DAFT_in_tl_s dom_tl_s  by (metis  mr_charn)
      hence mr_s_is_DAFT: "applied_rule_rev C x s = Some (DenyAllFromTo a b)"
        using tl_s
        by (metis  DA_notin_tl DenyAllFromTo EX_MR mrDA_tl 
            not_Some_eq tl_eq wellformed_policy1_strong.simps(2))
      thus ?thesis using mr_p_is_DAFT by simp
    }
    {case (AllowPortFromTo a b c)
      have wp1s: "wellformed_policy1 s" by (metis wp1_eq wp1_s)
      have mr_p_is_A: "applied_rule_rev C x p = Some (AllowPortFromTo a b c)"
        by (simp add: AllowPortFromTo Some)
      hence A_in_s: "AllowPortFromTo a b c \<in> set s" using sets_eq
        by (auto intro: mrSet)
      have x_in_dom_A: "x \<in> dom (C (AllowPortFromTo a b c))"
        by (metis mr_p_is_A AllowPortFromTo mr_in_dom)
      have SCs: "singleCombinators s" using SC sets_eq
        by (auto intro: SCSubset)
      hence ANDs: "allNetsDistinct s" using aND sets_eq SC
        by (auto intro: aNDSetsEq)
      hence mr_s_is_A: "applied_rule_rev C x s = Some (AllowPortFromTo a b c)"
        using A_in_s wp1s mr_p_is_A aND SCs wp3_s x_in_dom_A
        by (simp add: rule_charn2)
      thus ?thesis using mr_p_is_A by simp
    }
    case (Conc a b) thus ?thesis by (metis Some mr_not_Conc SC) 
  qed
qed

lemma C_eq_Sets: 
  "singleCombinators p \<Longrightarrow>  wellformed_policy1_strong p \<Longrightarrow>  wellformed_policy1_strong s \<Longrightarrow>
   wellformed_policy3 p \<Longrightarrow>  wellformed_policy3 s \<Longrightarrow> allNetsDistinct p \<Longrightarrow> set p = set s \<Longrightarrow> 
   C (list2FWpolicy p) x = C (list2FWpolicy s) x"
  by(auto intro: C_eq_if_mr_eq C_eq_Sets_mr [symmetric])

lemma C_eq_sorted: 
  "distinct p \<Longrightarrow> all_in_list p l \<Longrightarrow> singleCombinators p \<Longrightarrow> wellformed_policy1_strong p \<Longrightarrow>
    wellformed_policy3 p \<Longrightarrow> allNetsDistinct p \<Longrightarrow> 
   C (list2FWpolicy (FWNormalisationCore.sort p l)) = C (list2FWpolicy p)"
  apply (rule ext)
  by (auto intro: C_eq_Sets simp: nMTSort wellformed1_alternative_sorted 
      wellformed_policy3_charn  wp1_eq)

lemma C_eq_sortedQ: 
  "distinct p \<Longrightarrow> all_in_list p l \<Longrightarrow> singleCombinators p \<Longrightarrow> wellformed_policy1_strong p \<Longrightarrow>
   wellformed_policy3 p \<Longrightarrow> allNetsDistinct p \<Longrightarrow> 
   C (list2FWpolicy (qsort p l)) = C (list2FWpolicy p)"
  apply (rule ext)
  apply (auto intro!: C_eq_Sets simp: nMTSortQ wellformed1_alternative_sorted distinct_sortQ
      wellformed_policy3_charn wp1_eq) 
  by (metis set_qsort wellformed1_sortedQ wellformed_eq wp1_aux1aa)

lemma C_eq_RS2_mr: "applied_rule_rev C x (removeShadowRules2 p)= applied_rule_rev C x p"
proof (induct p)
  case Nil thus ?case by simp 
next
  case (Cons y ys) thus ?case
  proof (cases "ys = []")
    case True thus ?thesis by (cases y, simp_all) 
  next
    case False thus ?thesis
    proof (cases y)
      case DenyAll thus ?thesis by (simp, metis Cons DenyAll mreq_end2) 
    next
      case (DenyAllFromTo a b) thus ?thesis
        by (simp, metis Cons DenyAllFromTo mreq_end2)
    next
      case (AllowPortFromTo a b p) thus ?thesis
      proof (cases "DenyAllFromTo a b \<in> set ys")
        case True thus ?thesis using AllowPortFromTo Cons
          apply (cases "applied_rule_rev C x ys = None", simp_all)
           apply (subgoal_tac "x \<notin> dom (C (AllowPortFromTo a b p))")
            apply (subst mrconcNone, simp_all)
            apply (simp add: applied_rule_rev_def )
           apply (rule contra_subsetD [OF allow_deny_dom])
           apply (erule mrNoneMT,simp)
          apply (metis AllowPortFromTo mrconc)
          done
      next
        case False thus ?thesis using False Cons AllowPortFromTo
          by (simp, metis AllowPortFromTo Cons mreq_end2) qed
    next
      case (Conc a b) thus ?thesis
        by (metis Cons mreq_end2 removeShadowRules2.simps(4))
    qed
  qed
qed

lemma C_eq_None[rule_format]: 
  "p \<noteq> []  --> applied_rule_rev C x p = None \<longrightarrow>  C (list2FWpolicy p) x = None"
  apply (simp add: applied_rule_rev_def)
  apply (rule rev_induct, simp_all)
  apply (intro impI, simp)
  subgoal for xa xs
    apply (case_tac "xs \<noteq> []")
     apply (simp_all add: dom_def)
    done
  done
    
lemma C_eq_None2:
  "a \<noteq> [] \<Longrightarrow> b \<noteq> [] \<Longrightarrow> applied_rule_rev C x a = \<bottom> \<Longrightarrow> applied_rule_rev C x b = \<bottom> \<Longrightarrow> 
   C (list2FWpolicy a) x = C (list2FWpolicy b) x"
  by (auto simp: C_eq_None)
    
lemma C_eq_RS2: 
  "wellformed_policy1_strong p \<Longrightarrow> C (list2FWpolicy (removeShadowRules2 p))= C (list2FWpolicy p)"
  apply (rule ext)
  by (metis C_eq_RS2_mr C_eq_if_mr_eq wellformed_policy1_strong.simps(1) wp1n_RS2)
    
lemma none_MT_rulesRS2: 
  "none_MT_rules C p \<Longrightarrow> none_MT_rules C (removeShadowRules2 p)"
  by (auto simp: RS2Set none_MT_rulessubset)
    
lemma CconcNone: 
  "dom (C a) = {} \<Longrightarrow> p \<noteq> [] \<Longrightarrow> C (list2FWpolicy (a # p)) x = C (list2FWpolicy p) x"
  apply (case_tac "p = []", simp_all)
  apply (case_tac "x\<in> dom (C (list2FWpolicy(p)))")
   apply (metis Cdom2 list2FWpolicyconc)
  apply (metis C.simps(4) map_add_dom_app_simps(2) inSet_not_MT list2FWpolicyconc set_empty2)
  done

lemma none_MT_rulesrd[rule_format]: 
  "none_MT_rules C p \<longrightarrow> none_MT_rules C (remdups p)"
  by (induct p, simp_all)
    
lemma DARS3[rule_format]:
  "DenyAll \<notin> set p\<longrightarrow>DenyAll \<notin> set (rm_MT_rules C p)"
  by (induct p, simp_all)
    
lemma DAnMT: "dom (C DenyAll) \<noteq> {}"
  by (simp add: dom_def C.simps PolicyCombinators.PolicyCombinators)
    
lemma DAnMT2: "C DenyAll \<noteq> Map.empty"
  by (metis DAAux dom_eq_empty_conv empty_iff) 

lemma wp1n_RS3[rule_format,simp]: 
  "wellformed_policy1_strong p \<longrightarrow>  wellformed_policy1_strong (rm_MT_rules C p)"
  by (induct p, simp_all add: DARS3 DAnMT)
    
lemma AILRS3[rule_format,simp]: 
  "all_in_list p l \<longrightarrow> all_in_list (rm_MT_rules C p) l"
  by (induct p, simp_all)
    
lemma SCRS3[rule_format,simp]: 
  "singleCombinators p \<longrightarrow> singleCombinators(rm_MT_rules C p)"
  apply (induct p, simp_all) 
  subgoal for a p 
    apply(case_tac "a", simp_all)
    done
  done
    
lemma RS3subset: "set (rm_MT_rules C p)  \<subseteq> set p "
  by (induct p, auto)

lemma ANDRS3[simp]: 
  "singleCombinators p \<Longrightarrow> allNetsDistinct p \<Longrightarrow> allNetsDistinct (rm_MT_rules C p)"
  using RS3subset SCRS3 aNDSubset by blast

lemma nlpaux: "x \<notin> dom (C b) \<Longrightarrow> C (a \<oplus> b) x = C a x"
  by (metis C.simps(4) map_add_dom_app_simps(3))

lemma notindom[rule_format]: 
  "a \<in> set p \<longrightarrow>  x \<notin> dom (C (list2FWpolicy p)) \<longrightarrow>  x \<notin> dom (C a)"
  apply (induct p, simp_all)
  by (metis CConcStartA Cdom2 domIff empty_iff empty_set l2p_aux)

lemma C_eq_rd[rule_format]: 
  "p \<noteq> [] \<Longrightarrow> C (list2FWpolicy (remdups p)) = C (list2FWpolicy p)"
proof (rule ext,induct p) 
  case Nil thus ?case by simp 
next
  case (Cons y ys) thus ?case
  proof (cases "ys = []")
    case True thus ?thesis by simp 
  next
    case False thus ?thesis using Cons 
      apply (simp)  apply (rule conjI, rule impI)
       apply (cases "x \<in> dom (C (list2FWpolicy ys))")
        apply (metis Cdom2 False list2FWpolicyconc)
       apply (metis False domIff list2FWpolicyconc nlpaux notindom)
      apply (rule impI)
      apply (cases "x \<in> dom (C (list2FWpolicy ys))")
       apply (subgoal_tac "x \<in> dom (C (list2FWpolicy (remdups ys)))")
        apply (metis Cdom2 False list2FWpolicyconc remdups_eq_nil_iff)
       apply (metis domIff)
      apply (subgoal_tac "x \<notin> dom (C (list2FWpolicy (remdups ys)))")
       apply (metis False list2FWpolicyconc nlpaux remdups_eq_nil_iff)
      apply (metis domIff)
      done
  qed
qed

lemma nMT_domMT:
  "\<not> not_MT C  p \<Longrightarrow> p \<noteq> [] \<Longrightarrow> r \<notin> dom (C (list2FWpolicy p))"
proof (induct p)
  case Nil thus ?case by simp 
next
  case (Cons x xs) thus ?case 
    apply (simp split: if_splits)
    apply (cases "xs = []",simp_all )
    by (metis CconcNone domIff)
qed
  
lemma C_eq_RS3_aux[rule_format]: 
  "not_MT C  p \<Longrightarrow>  C (list2FWpolicy p) x = C (list2FWpolicy (rm_MT_rules C p)) x"
proof (induct p)
  case Nil thus ?case by simp 
next
  case (Cons y ys) 
  thus ?case
  proof (cases "not_MT C  ys")
    case True thus ?thesis using Cons 
      apply (simp) apply(rule conjI, rule impI, simp)
       apply (metis CconcNone True not_MTimpnotMT)
      apply (rule impI, simp)
      apply (cases "x \<in> dom (C (list2FWpolicy ys))")
       apply (subgoal_tac "x \<in> dom (C (list2FWpolicy (rm_MT_rules C ys)))") 
        apply (metis Cdom2 NMPrm l2p_aux not_MTimpnotMT)
       apply (simp add: domIff)
      apply (subgoal_tac "x \<notin>  dom (C (list2FWpolicy (rm_MT_rules C ys)))") 
       apply (metis l2p_aux l2p_aux2 nlpaux)
      apply (metis domIff)
      done
  next 
    case False thus ?thesis using Cons False
    proof (cases "ys = []") 
      case True thus ?thesis using Cons by (simp) (rule impI, simp) 
    next
      case False thus ?thesis 
        using Cons False \<open>\<not> not_MT C ys\<close>  apply (simp)
        by (metis SR3nMT l2p_aux list2FWpolicy.simps(2) nMT_domMT nlpaux)
    qed
  qed
qed       

lemma C_eq_id: 
  "wellformed_policy1_strong p \<Longrightarrow>  C(list2FWpolicy (insertDeny p)) = C (list2FWpolicy p)"
  by (rule ext) (auto intro: C_eq_if_mr_eq elim: mr_iD)
    
lemma C_eq_RS3: 
  "not_MT C  p \<Longrightarrow> C(list2FWpolicy (rm_MT_rules C p)) = C (list2FWpolicy p)"
  by (rule ext) (erule C_eq_RS3_aux[symmetric])

lemma NMPrd[rule_format]:  "not_MT C  p \<longrightarrow> not_MT C  (remdups p)"
  by (induct p) (auto simp: NMPcharn)

lemma NMPDA[rule_format]: "DenyAll \<in> set p \<longrightarrow> not_MT C  p"
  by (induct p, simp_all add: DAnMT)

lemma NMPiD[rule_format]: "not_MT C  (insertDeny p)"
  by (simp add: DAiniD NMPDA)

lemma list2FWpolicy2list[rule_format]: "C (list2FWpolicy(policy2list p)) = (C p)"
  apply (rule ext)
  apply (induct_tac p, simp_all)
  by (metis (no_types, lifting) Cdom2 CeqEnd CeqStart domIff nlpaux p2lNmt)

lemmas C_eq_Lemmas = none_MT_rulesRS2 none_MT_rulesrd  SCp2l  wp1n_RS2  wp1ID NMPiD wp1_eq
                     wp1alternative_RS1 p2lNmt list2FWpolicy2list wellformed_policy3_charn waux2 

lemmas C_eq_subst_Lemmas = C_eq_sorted C_eq_sortedQ C_eq_RS2 C_eq_rd C_eq_RS3 C_eq_id 

lemma C_eq_All_untilSorted: 
  "DenyAll\<in>set(policy2list p) \<Longrightarrow> all_in_list(policy2list p) l \<Longrightarrow> allNetsDistinct(policy2list p) \<Longrightarrow>
    C (list2FWpolicy
        (FWNormalisationCore.sort
          (removeShadowRules2 (remdups (rm_MT_rules C 
             (insertDeny (removeShadowRules1 (policy2list p)))))) l)) =
    C p"
  apply (subst C_eq_sorted,simp_all add: C_eq_Lemmas)
  apply (subst C_eq_RS2,simp_all add: C_eq_Lemmas) 
  apply (subst C_eq_rd,simp_all add: C_eq_Lemmas)
  apply (subst C_eq_RS3,simp_all add: C_eq_Lemmas)
  apply (subst C_eq_id,simp_all add: C_eq_Lemmas)
  done

lemma C_eq_All_untilSortedQ: 
  "DenyAll\<in>set(policy2list p) \<Longrightarrow> all_in_list(policy2list p) l \<Longrightarrow> allNetsDistinct(policy2list p) \<Longrightarrow>
    C (list2FWpolicy
        (qsort (removeShadowRules2 (remdups (rm_MT_rules C 
             (insertDeny (removeShadowRules1 (policy2list p)))))) l)) =
    C p"
  apply (subst C_eq_sortedQ,simp_all add: C_eq_Lemmas)
  apply (subst C_eq_RS2,simp_all add: C_eq_Lemmas) 
  apply (subst C_eq_rd,simp_all add: C_eq_Lemmas)
  apply (subst C_eq_RS3,simp_all add: C_eq_Lemmas)
  apply (subst C_eq_id,simp_all add: C_eq_Lemmas)
  done
    
lemma C_eq_All_untilSorted_withSimps: 
  "DenyAll\<in>set(policy2list p) \<Longrightarrow>all_in_list(policy2list p) l \<Longrightarrow> allNetsDistinct (policy2list p) \<Longrightarrow>
    C (list2FWpolicy
        (FWNormalisationCore.sort
          (removeShadowRules2 (remdups (rm_MT_rules C 
              (insertDeny (removeShadowRules1 (policy2list p)))))) l)) =
    C p"
  by (simp_all add: C_eq_Lemmas C_eq_subst_Lemmas)
    
lemma C_eq_All_untilSorted_withSimpsQ: 
  " DenyAll\<in>set(policy2list p)\<Longrightarrow>all_in_list(policy2list p) l \<Longrightarrow> allNetsDistinct(policy2list p) \<Longrightarrow>
    C (list2FWpolicy
        (qsort (removeShadowRules2 (remdups (rm_MT_rules C 
             (insertDeny (removeShadowRules1 (policy2list p)))))) l)) =
    C p"
  by (simp_all add: C_eq_Lemmas C_eq_subst_Lemmas)
    

lemma InDomConc[rule_format]: 
  "p \<noteq> [] \<longrightarrow> x \<in> dom (C (list2FWpolicy (p))) \<longrightarrow> x \<in>  dom (C (list2FWpolicy (a#p)))"
  apply (induct p, simp_all)
  subgoal for a' p  
    apply  (case_tac "p = []", simp_all add: dom_def C.simps)
    done
  done
    
lemma not_in_member[rule_format]: "member a b \<longrightarrow> x \<notin> dom (C b) \<longrightarrow> x \<notin> dom (C a)"
  by (induct b) (simp_all add: dom_def C.simps)
    
lemma src_in_sdnets[rule_format]: 
  "\<not> member DenyAll x \<longrightarrow> p \<in> dom (C x) \<longrightarrow> subnetsOfAdr (src p) \<inter> (fst_set (sdnets x)) \<noteq> {}"
  apply (induct rule: Combinators.induct)
     apply (simp_all add: fst_set_def subnetsOfAdr_def PLemmas fst_set_def)
  apply (intro impI)
  subgoal for x1 x2
    apply (case_tac "p \<in> dom (C x2)")
     apply (rule subnetAux)
      apply (auto simp: PLemmas fst_set_def)
    done
  done
    
lemma dest_in_sdnets[rule_format]: 
  "\<not> member DenyAll x \<longrightarrow> p \<in> dom (C x) \<longrightarrow>  subnetsOfAdr (dest p) \<inter> (snd_set (sdnets x)) \<noteq> {}"
  apply (induct rule: Combinators.induct)
     apply (simp_all add: snd_set_def subnetsOfAdr_def PLemmas)
  apply (intro impI)
  apply (simp add: snd_set_def)
  subgoal for x1 x2
    apply (case_tac "p \<in> dom (C x2)")
     apply (rule subnetAux)
      apply (auto simp: PLemmas)
    done
  done

lemma sdnets_in_subnets[rule_format]: 
  "p\<in> dom (C x) \<longrightarrow> \<not> member DenyAll x \<longrightarrow>
        (\<exists> (a,b)\<in>sdnets x. a \<in> subnetsOfAdr (src p) \<and> b \<in> subnetsOfAdr (dest p))"
  apply (rule Combinators.induct)
     apply (simp_all add: PLemmas subnetsOfAdr_def)
  apply (intro impI, simp)
  subgoal for x1 x2
    apply (case_tac "p \<in> dom (C (x2))")
     apply (auto simp: PLemmas subnetsOfAdr_def)
    done
  done

lemma disjSD_no_p_in_both[rule_format]:   
  "disjSD_2 x y \<Longrightarrow> \<not> member DenyAll x \<Longrightarrow> \<not> member DenyAll y \<Longrightarrow> p \<in> dom(C x) \<Longrightarrow> p \<in> dom(C y) \<Longrightarrow> 
  False"
  apply (rule_tac A = "sdnets x" and B = "sdnets y" and D = "src p" and F = "dest p" in tndFalse)
  by (auto simp: dest_in_sdnets src_in_sdnets sdnets_in_subnets disjSD_2_def)
    
lemma list2FWpolicy_eq: 
  "zs \<noteq> [] \<Longrightarrow>  C (list2FWpolicy (x \<oplus> y # z)) p = C (x \<oplus> list2FWpolicy (y # z)) p"
  by (metis ConcAssoc l2p_aux list2FWpolicy.simps(2))
    
lemma dom_sep[rule_format]: 
  "x \<in> dom (C (list2FWpolicy p)) \<longrightarrow> x \<in> dom (C (list2FWpolicy(separate p)))"
proof (induct p rule: separate.induct, simp_all, goal_cases) 
  case (1 v va y z) then show ?case
    apply (intro conjI impI)
     apply (simp,drule mp)
      apply (case_tac "x \<in> dom (C (DenyAllFromTo v va))")
       apply (metis CConcStartA domIff l2p_aux2 list2FWpolicyconc not_Cons_self )
      apply (metis Conc_not_MT domIff list2FWpolicy_eq, simp)
    by (metis InDomConc domIff list.simps(3) list2FWpolicyconc nlpaux sepnMT)
next
  case (2 v va vb y z) 
  assume * : "{v, va} = first_bothNet y \<Longrightarrow>
                x \<in> dom (C (list2FWpolicy (AllowPortFromTo v va vb \<oplus> y # z))) \<longrightarrow>
                x \<in> dom (C (list2FWpolicy (separate (AllowPortFromTo v va vb \<oplus> y # z))))"
    and    **: "{v, va} \<noteq> first_bothNet y \<Longrightarrow>
              x \<in> dom(C(list2FWpolicy(y#z))) \<longrightarrow> x \<in> dom (C(list2FWpolicy(separate(y#z))))"
  show ?case
    apply (insert * **, rule impI | rule conjI)+
     apply (simp,case_tac "x \<in> dom (C (AllowPortFromTo v va vb))")
      apply (metis CConcStartA domIff  l2p_aux2 list2FWpolicyconc not_Cons_self )
     apply (subgoal_tac "x \<in> dom (C (list2FWpolicy (y #z)))")
      apply (metis CConcStartA Cdom2 domIff l2p_aux2 list2FWpolicyconc nlpaux)
     apply (simp add: dom_def C.simps)
    apply (intro impI, simp_all)
    apply (case_tac "x \<in> dom (C (AllowPortFromTo v va vb))",simp_all)
    by (metis Cdom2 domIff l2p_aux list2FWpolicy.simps(3) nlpaux sepnMT)
next
  case (3 v va y z) 
  assume * : "(first_bothNet v = first_bothNet y \<Longrightarrow> 
                x \<in> dom (C (list2FWpolicy ((v \<oplus> va) \<oplus> y # z))) \<longrightarrow> 
                x \<in> dom (C (list2FWpolicy (separate ((v \<oplus> va) \<oplus> y # z)))))"
    and  ** : "(first_bothNet v \<noteq> first_bothNet y \<Longrightarrow> 
                x \<in> dom(C(list2FWpolicy(y#z))) \<longrightarrow> x \<in> dom (C (list2FWpolicy (separate (y # z)))))"
  show ?case
    apply (insert * **, rule conjI | rule impI)+
     apply (simp,drule mp)
      apply (case_tac "x \<in> dom (C ((v \<oplus> va)))")
       apply (metis C.simps(4) CConcStartA ConcAssoc domIff list2FWpolicy2list list2FWpolicyconc  p2lNmt)
      apply simp_all
     apply (metis Conc_not_MT domIff list2FWpolicy_eq)
    by (metis CConcStartA Conc_not_MT InDomConc domIff nlpaux sepnMT)
qed
  
lemma domdConcStart[rule_format]: 
  "x \<in> dom (C (list2FWpolicy (a#b))) \<longrightarrow> x \<notin> dom (C (list2FWpolicy b)) \<longrightarrow> x \<in> dom (C (a))"
  by (induct b, simp_all) (auto simp: PLemmas)
    
lemma sep_dom2_aux: 
  " x \<in> dom (C (list2FWpolicy (a \<oplus> y # z))) \<Longrightarrow> x \<in> dom (C (a \<oplus> list2FWpolicy (y # z)))"
  by (auto)[1] (metis list2FWpolicy_eq p2lNmt)

lemma sep_dom2_aux2: 
  "x \<in> dom (C (list2FWpolicy (separate (y # z)))) \<longrightarrow> x \<in> dom (C (list2FWpolicy (y # z))) \<Longrightarrow>
    x \<in> dom (C (list2FWpolicy (a # separate (y # z)))) \<Longrightarrow> x \<in> dom (C (list2FWpolicy (a \<oplus> y # z)))"
  by (metis CConcStartA InDomConc domdConcStart list.simps(2) list2FWpolicy.simps(2) list2FWpolicyconc)

lemma sep_dom2[rule_format]: 
  "x \<in> dom (C (list2FWpolicy (separate p))) \<longrightarrow> x \<in> dom (C (list2FWpolicy( p)))"
  by (rule separate.induct) (simp_all add: sep_dom2_aux sep_dom2_aux2)

lemma sepDom: "dom (C (list2FWpolicy p)) = dom (C (list2FWpolicy (separate p)))"
  apply (rule equalityI)
  by (rule subsetI, (erule dom_sep|erule sep_dom2))+

lemma C_eq_s_ext[rule_format]: 
  "p \<noteq> [] \<longrightarrow>  C (list2FWpolicy (separate p)) a  = C (list2FWpolicy p) a "
proof (induct rule: separate.induct, goal_cases)
  case (1 x) thus ?case 
    apply simp
    apply (cases "x = []")
     apply (metis l2p_aux2 separate.simps(5))
    apply simp
    apply (cases "a \<in> dom (C (list2FWpolicy x))")
     apply (subgoal_tac "a \<in> dom (C (list2FWpolicy (separate x)))")
      apply (metis Cdom2 list2FWpolicyconc sepDom sepnMT)
     apply (metis sepDom)
    apply (subgoal_tac "a \<notin> dom (C (list2FWpolicy (separate x)))")
     apply (subst list2FWpolicyconc,simp add: sepnMT)
     apply (subst list2FWpolicyconc,simp add: sepnMT)
     apply (metis nlpaux sepDom)
    apply (metis sepDom)
    done
next
  case (2 v va y z) thus ?case 
    apply (cases "z = []", simp_all)
     apply (rule conjI|rule impI|simp)+
     apply (subst list2FWpolicyconc)
      apply (metis not_Cons_self sepnMT)
     apply (metis C.simps(4) CConcStartaux Cdom2 domIff)
    apply (rule conjI|rule impI|simp)+
     apply (erule list2FWpolicy_eq)
    apply (rule impI, simp)
    apply (subst list2FWpolicyconc) 
     apply (metis list.simps(2) sepnMT) 
    by (metis C.simps(4) CConcStartaux Cdom2 domIff)
next
  case (3 v va vb y z) thus ?case
    apply (cases "z = []", simp_all)
     apply (rule conjI|rule impI|simp)+
     apply (subst list2FWpolicyconc)
      apply (metis not_Cons_self sepnMT)
     apply (metis C.simps(4) CConcStartaux Cdom2 domIff)
    apply (rule conjI|rule impI|simp)+
     apply (erule list2FWpolicy_eq)
    apply (rule impI, simp)
    apply (subst list2FWpolicyconc) 
     apply (metis list.simps(2) sepnMT) 
    by (metis C.simps(4) CConcStartaux Cdom2 domIff)
next
  case (4 v va y z) thus ?case
    apply (cases "z = []", simp_all)
     apply (rule conjI|rule impI|simp)+
     apply (subst list2FWpolicyconc)
      apply (metis not_Cons_self sepnMT)
     apply (metis C.simps(4) CConcStartaux Cdom2 domIff)
    apply (rule conjI|rule impI|simp)+
     apply (erule list2FWpolicy_eq)
    apply (rule impI, simp)
    apply (subst list2FWpolicyconc) 
     apply (metis list.simps(2) sepnMT) 
    by (metis C.simps(4) CConcStartaux Cdom2 domIff)
next
  case 5 thus ?case by simp 
next
  case 6 thus ?case by simp 
next
  case 7 thus ?case by simp
next
  case 8 thus ?case by simp 
qed

lemma C_eq_s: 
  "p \<noteq> [] \<Longrightarrow> C (list2FWpolicy (separate p)) = C (list2FWpolicy p)"
  apply (rule ext) using C_eq_s_ext by blast
    
lemma sortnMTQ: "p \<noteq> [] \<Longrightarrow> qsort p l \<noteq> []"
  by (metis set_sortQ setnMT)

lemmas C_eq_Lemmas_sep =
       C_eq_Lemmas sortnMT sortnMTQ RS2_NMT NMPrd not_MTimpnotMT 

lemma C_eq_until_separated:
  " DenyAll\<in>set(policy2list p) \<Longrightarrow> all_in_list(policy2list p)l \<Longrightarrow> allNetsDistinct (policy2list p) \<Longrightarrow>
    C (list2FWpolicy
        (separate
          (FWNormalisationCore.sort
            (removeShadowRules2 (remdups (rm_MT_rules C 
               (insertDeny (removeShadowRules1 (policy2list p)))))) l))) =
    C p"
  by (simp add: C_eq_All_untilSorted_withSimps C_eq_s wellformed1_alternative_sorted wp1ID wp1n_RS2)

lemma C_eq_until_separatedQ:
  "DenyAll\<in>set(policy2list p) \<Longrightarrow> all_in_list(policy2list p)l \<Longrightarrow> allNetsDistinct(policy2list p) \<Longrightarrow>
    C (list2FWpolicy
        (separate (qsort (removeShadowRules2 (remdups (rm_MT_rules C 
             (insertDeny (removeShadowRules1 (policy2list p)))))) l))) =
    C p"
  by (simp add: C_eq_All_untilSorted_withSimpsQ C_eq_s sortnMTQ wp1ID wp1n_RS2)

lemma domID[rule_format]: "p \<noteq> [] \<and> x \<in> dom(C(list2FWpolicy p)) \<longrightarrow>
                           x \<in> dom (C(list2FWpolicy(insertDenies p)))"
proof(induct p)
  case Nil then show ?case by simp
next 
  case (Cons a p) then show ?case
  proof(cases "p=[]",goal_cases)
    case 1 then show ?case
      apply(simp) apply(rule impI)
      apply (cases a, simp_all)
        apply (simp_all add: C.simps dom_def)+ 
      by auto
  next
    case 2 then show ?case
    proof(cases "x \<in> dom(C(list2FWpolicy p))", goal_cases)
      case 1 then show ?case
        apply simp apply (rule impI)
        apply (cases a, simp_all)
        using InDomConc idNMT apply blast
         apply (rule InDomConc, simp_all add: idNMT)+
        done
    next 
      case 2 then show ?case  
        apply simp apply (rule impI)
      proof(cases "x \<in> dom (C (list2FWpolicy (insertDenies p)))", goal_cases)
        case 1 then show ?case
        proof(induct a)
          case DenyAll then show ?case by simp
        next               
          case (DenyAllFromTo src dest) then show ?case
            apply simp by( rule InDomConc, simp add: idNMT)
        next  
          case (AllowPortFromTo src dest port) then show ?case
            apply simp by(rule InDomConc, simp  add: idNMT)
        next 
          case (Conc _ _) then show ?case
            apply simp by(rule InDomConc, simp add: idNMT)
        qed
      next
        case 2 then show ?case
        proof (induct a)
          case DenyAll then show ?case by simp
        next
          case (DenyAllFromTo src dest) then show ?case
            by(simp,metis domIff CConcStartA list2FWpolicyconc nlpaux Cdom2)
        next
          case (AllowPortFromTo src dest port) then show ?case
            by(simp,metis domIff CConcStartA list2FWpolicyconc nlpaux Cdom2)
        next
          case (Conc _ _) then show ?case
            by (simp,metis CConcStartA Cdom2 domIff domdConcStart)
        qed
      qed
    qed
  qed
qed
   
lemma DA_is_deny: 
  "x \<in> dom (C (DenyAllFromTo a b \<oplus> DenyAllFromTo b a \<oplus> DenyAllFromTo a b)) \<Longrightarrow>
   C (DenyAllFromTo a b\<oplus>DenyAllFromTo b a \<oplus> DenyAllFromTo a b) x = Some (deny ())"
  apply (case_tac "x \<in> dom (C (DenyAllFromTo a b))")
   apply (simp_all add: PLemmas)
   apply (simp_all split: if_splits)
  done

lemma iDdomAux[rule_format]: 
  "p \<noteq> [] \<longrightarrow> x \<notin> dom (C (list2FWpolicy p)) \<longrightarrow>
   x \<in> dom (C (list2FWpolicy (insertDenies p))) \<longrightarrow>
   C (list2FWpolicy (insertDenies p)) x = Some (deny ())"
proof (induct p)
  case Nil thus ?case by simp
next
  case (Cons y ys) thus ?case
  proof (cases y) 
    case DenyAll then show ?thesis by simp 
  next
    case (DenyAllFromTo a b) then show ?thesis using DenyAllFromTo Cons
      apply simp
      apply (intro impI)
    proof (cases "ys = []", goal_cases)
      case 1 then show ?case by (simp add: DA_is_deny) 
    next
      case 2 then show ?case
        apply simp
        apply (drule mp)
         apply (metis DenyAllFromTo InDomConc )
        apply (cases "x \<in> dom (C (list2FWpolicy (insertDenies ys)))", simp_all)
         apply (metis Cdom2 DenyAllFromTo  idNMT list2FWpolicyconc)
        apply (subgoal_tac "C (list2FWpolicy (DenyAllFromTo a b \<oplus>
                                DenyAllFromTo b a \<oplus> DenyAllFromTo a b#insertDenies ys)) x =
                                C ((DenyAllFromTo a b \<oplus> DenyAllFromTo b a \<oplus> DenyAllFromTo a b)) x ")
         apply simp
         apply (rule DA_is_deny)
         apply (metis DenyAllFromTo domdConcStart)
        apply (metis DenyAllFromTo l2p_aux2 list2FWpolicyconc nlpaux)
        done 
    qed
  next
    case (AllowPortFromTo a b c) then show ?thesis using Cons AllowPortFromTo
    proof (cases "ys = []", goal_cases)
      case 1 then show ?case 
        apply simp
        apply (intro impI)
        apply (subgoal_tac "x \<in> dom (C (DenyAllFromTo a b \<oplus> DenyAllFromTo b a))")
         apply (simp_all add: PLemmas)
        apply (simp split: if_splits, auto) 
        done 
    next
      case 2 then show ?case
        apply simp
        apply (intro impI)
        apply (drule mp)
         apply (metis AllowPortFromTo InDomConc)
        apply (cases "x \<in> dom (C (list2FWpolicy (insertDenies ys)))")
         apply simp_all
         apply (metis AllowPortFromTo Cdom2 idNMT list2FWpolicyconc)
        apply (subgoal_tac "C (list2FWpolicy (DenyAllFromTo a b \<oplus>
                                DenyAllFromTo b a \<oplus> AllowPortFromTo a b c#insertDenies ys)) x =
                                C ((DenyAllFromTo a b \<oplus> DenyAllFromTo b a)) x ")
         apply simp
         defer 1 
         apply (metis AllowPortFromTo CConcStartA ConcAssoc idNMT  list2FWpolicyconc nlpaux)
        apply (simp add: PLemmas, simp split: if_splits, auto) 
        done
    qed
  next
    case (Conc a b) then show ?thesis
    proof (cases "ys = []", goal_cases)
      case 1 then show ?case 
        apply simp
        apply (rule impI)+
        apply (subgoal_tac "x \<in> dom (C (DenyAllFromTo (first_srcNet a)
                                (first_destNet a) \<oplus> DenyAllFromTo (first_destNet a) (first_srcNet a)))")
         apply (simp_all add: PLemmas)
        apply (simp split: if_splits, auto) 
        done 
    next
      case 2 then show ?case
        apply simp
        apply (intro impI)
        apply (cases "x \<in> dom (C (list2FWpolicy (insertDenies ys)))")
         apply (metis Cdom2 Conc Cons InDomConc idNMT list2FWpolicyconc)
        apply (subgoal_tac "C (list2FWpolicy (DenyAllFromTo (first_srcNet a) 
                                   (first_destNet a) \<oplus> DenyAllFromTo(first_destNet a)(first_srcNet a)
                                   \<oplus> a \<oplus> b#insertDenies ys)) x =
                                 C ((DenyAllFromTo (first_srcNet a) (first_destNet a) \<oplus>
                                   DenyAllFromTo (first_destNet a)  (first_srcNet a) \<oplus> a \<oplus> b)) x")
        apply simp
        defer 1 
        apply (metis Conc l2p_aux2 list2FWpolicyconc nlpaux)
        apply (subgoal_tac "C((DenyAllFromTo (first_srcNet a)
                                  (first_destNet a) \<oplus> DenyAllFromTo (first_destNet a)
                                  (first_srcNet a) \<oplus> a \<oplus> b)) x = 
                                 C((DenyAllFromTo (first_srcNet a)(first_destNet a) \<oplus> 
                                   DenyAllFromTo(first_destNet a)(first_srcNet a))) x ")
        apply simp
        defer 1 
        apply (metis CConcStartA Conc ConcAssoc nlpaux)
        apply (simp add: PLemmas, simp split: if_splits, auto) 
        done
    qed
  qed
qed         
  

lemma iD_isD[rule_format]: 
  "p \<noteq> [] \<longrightarrow> x \<notin> dom (C (list2FWpolicy p)) \<longrightarrow> 
   C (DenyAll \<oplus> list2FWpolicy (insertDenies p)) x = C DenyAll x"
  apply (case_tac "x \<in> dom (C (list2FWpolicy (insertDenies p)))")
   apply (simp add: Cdom2 PLemmas(1) deny_all_def iDdomAux)
  by (simp add: nlpaux)


lemma inDomConc:"\<lbrakk> x\<notin>dom (C a); x\<notin>dom (C (list2FWpolicy p))\<rbrakk> \<Longrightarrow>
                 x \<notin> dom (C (list2FWpolicy(a#p)))"
  by (metis domdConcStart)
    
lemma domsdisj[rule_format]: 
  "p \<noteq> [] \<longrightarrow> (\<forall> x s. s \<in> set p \<and> x \<in> dom (C A) \<longrightarrow>  x \<notin> dom (C s)) \<longrightarrow> y \<in> dom (C A) \<longrightarrow>
   y \<notin> dom (C (list2FWpolicy p))"
proof (induct p)
  case Nil show ?case by simp
next
  case (Cons a p) then show ?case
    apply (case_tac "p = []") 
     apply fastforce 
    by (meson domdConcStart list.set_intros(1) list.set_intros(2))
qed
        
lemma isSepaux:
  " p \<noteq> [] \<Longrightarrow> noDenyAll (a # p) \<Longrightarrow> separated (a # p) \<Longrightarrow>
    x \<in> dom (C (DenyAllFromTo (first_srcNet a) (first_destNet a) \<oplus> 
                DenyAllFromTo (first_destNet a) (first_srcNet a) \<oplus> a)) \<Longrightarrow>
    x \<notin> dom (C (list2FWpolicy p))"
  apply (rule_tac A = "(DenyAllFromTo (first_srcNet a) (first_destNet a) \<oplus>
                     DenyAllFromTo (first_destNet a) (first_srcNet a) \<oplus> a)" in domsdisj)
    apply simp_all
  by (metis Combinators.distinct(1) FWNormalisationCore.member.simps(1) 
      FWNormalisationCore.member.simps(3) disjSD2aux disjSD_no_p_in_both noDA)

lemma none_MT_rulessep[rule_format]: "none_MT_rules C p \<longrightarrow> none_MT_rules C (separate p)"
  apply(induct p rule: separate.induct)
  by (simp_all add: C.simps map_add_le_mapE map_le_antisym)

lemma dom_id: 
  "noDenyAll(a#p) \<Longrightarrow> separated(a#p) \<Longrightarrow> p \<noteq> [] \<Longrightarrow> x\<notin>dom(C(list2FWpolicy p)) \<Longrightarrow> x\<in>dom (C a) \<Longrightarrow> 
   x \<notin> dom (C (list2FWpolicy (insertDenies p)))"
  apply (rule_tac a = a in isSepaux, simp_all)
  using idNMT apply blast
  using noDAID apply blast
  using id_aux4 noDA1eq sepNetsID apply blast
  by (metis list.set_intros(1) list.set_intros(2) list2FWpolicy.simps(2) list2FWpolicy.simps(3) notindom)

lemma C_eq_iD_aux2[rule_format]: 
  "noDenyAll1 p \<longrightarrow> separated p\<longrightarrow> p \<noteq> []\<longrightarrow> x \<in> dom (C (list2FWpolicy p))\<longrightarrow>
  C(list2FWpolicy (insertDenies p)) x = C(list2FWpolicy p) x"
proof (induct p)
  case Nil thus ?case by simp 
next
  case (Cons y ys)  thus ?case using Cons
  proof (cases y)
    case DenyAll thus ?thesis using Cons DenyAll apply simp
      apply (case_tac "ys = []", simp_all)
      apply (case_tac "x \<in> dom (C (list2FWpolicy ys))",simp_all)
       apply (metis Cdom2 domID idNMT list2FWpolicyconc noDA1eq)
      apply (metis DenyAll iD_isD idNMT list2FWpolicyconc nlpaux)
      done
  next
    case (DenyAllFromTo a b) thus ?thesis using Cons apply simp
      apply (rule impI|rule allI|rule conjI|simp)+
      apply (case_tac "ys = []", simp_all)
       apply (metis Cdom2 ConcAssoc DenyAllFromTo)
      apply (case_tac "x \<in> dom (C (list2FWpolicy ys))", simp_all)
       apply (simp add: Cdom2 domID idNMT l2p_aux noDA1eq)
      apply (case_tac "x \<in> dom (C (list2FWpolicy (insertDenies ys)))")
       apply (meson Combinators.distinct(1) FWNormalisationCore.member.simps(3) dom_id domdConcStart
          noDenyAll.simps(1) separated.simps(1))
      by (metis Cdom2 DenyAllFromTo domIff dom_def domdConcStart l2p_aux l2p_aux2 nlpaux) 
  next
    case (AllowPortFromTo a b c) thus ?thesis 
      using AllowPortFromTo Cons apply simp
      apply (rule impI|rule allI|rule conjI|simp)+
      apply (case_tac "ys = []", simp_all)
       apply (metis Cdom2 ConcAssoc AllowPortFromTo)
      apply (case_tac "x \<in> dom (C (list2FWpolicy ys))", simp_all)
       apply (simp add: Cdom2 domID idNMT list2FWpolicyconc noDA1eq)
      apply (case_tac "x \<in> dom (C (list2FWpolicy (insertDenies ys)))")
       apply (meson Combinators.distinct(3) FWNormalisationCore.member.simps(4) dom_id domdConcStart noDenyAll.simps(1) separated.simps(1))
      by (metis Cdom2 ConcAssoc l2p_aux list2FWpolicy.simps(2) nlpaux)
  next
    case (Conc a b) thus ?thesis using Cons Conc 
      apply simp
      apply (rule impI|rule allI|rule conjI|simp)+
      apply (case_tac "ys = []", simp_all)
       apply (metis Cdom2 ConcAssoc Conc)
      apply (case_tac "x \<in> dom (C (list2FWpolicy ys))",simp_all)
       apply (simp add: Cdom2 domID idNMT list2FWpolicyconc noDA1eq)
      apply (case_tac "x \<in> dom (C (a \<oplus> b))")
       apply (case_tac "x \<notin> dom (C (list2FWpolicy (insertDenies ys)))",simp_all)
        apply (simp add: Cdom2 domIff idNMT list2FWpolicyconc nlpaux)
       apply (metis FWNormalisationCore.member.simps(1) dom_id noDenyAll.simps(1) separated.simps(1))
      by (simp add: inDomConc)
  qed
qed

lemma C_eq_iD: 
  "separated p \<Longrightarrow> noDenyAll1 p \<Longrightarrow> wellformed_policy1_strong p \<Longrightarrow> 
   C (list2FWpolicy (insertDenies p)) = C (list2FWpolicy p)"
  by (rule ext) (metis CConcStartA C_eq_iD_aux2 DAAux wp1_alternative_not_mt wp1n_tl)

lemma noDAsortQ[rule_format]: "noDenyAll1 p \<longrightarrow> noDenyAll1 (qsort p l)"
  apply (case_tac "p",simp_all, rename_tac a list)
  subgoal for a list
    apply (case_tac "a = DenyAll",simp_all)
    using nDAeqSet set_sortQ apply blast 
    apply (rule impI,rule noDA1eq)
    apply (subgoal_tac "noDenyAll (a#list)")
     apply (metis append_Cons append_Nil nDAeqSet qsort.simps(2) set_sortQ)
    by (case_tac a, simp_all)
  done
    
lemma NetsCollectedSortQ: 
  "distinct p \<Longrightarrow>noDenyAll1 p \<Longrightarrow> all_in_list p l \<Longrightarrow>  singleCombinators p \<Longrightarrow> 
   NetsCollected (qsort p l)"
  by (metis NetsCollectedSorted SC3Q all_in_list.elims(2) all_in_list.simps(1) all_in_list.simps(2) 
      all_in_listAppend all_in_list_sublist noDAsortQ qsort.simps(1) qsort.simps(2) 
      singleCombinatorsConc sort_is_sortedQ)


lemmas CLemmas =  nMTSort nMTSortQ none_MT_rulesRS2 none_MT_rulesrd
                  noDAsort noDAsortQ nDASC wp1_eq  wp1ID  
                  SCp2l ANDSep   wp1n_RS2 
                  OTNSEp OTNSC noDA1sep wp1_alternativesep wellformed_eq 
                  wellformed1_alternative_sorted  
                    

lemmas C_eqLemmas_id = CLemmas  NC2Sep NetsCollectedSep 
                       NetsCollectedSort NetsCollectedSortQ separatedNC

lemma C_eq_Until_InsertDenies: 
  "DenyAll\<in>set(policy2list p) \<Longrightarrow> all_in_list(policy2list p)l \<Longrightarrow> allNetsDistinct(policy2list p) \<Longrightarrow>
   C (list2FWpolicy
        (insertDenies
          (separate
            (FWNormalisationCore.sort
              (removeShadowRules2 (remdups (rm_MT_rules C 
                  (insertDeny (removeShadowRules1 (policy2list p)))))) l)))) =
    C p"
  apply (subst C_eq_iD,simp_all add: C_eqLemmas_id)
  apply (rule C_eq_until_separated, simp_all)
  done

lemma C_eq_Until_InsertDeniesQ: 
  "DenyAll\<in>set(policy2list p) \<Longrightarrow> all_in_list(policy2list p)l \<Longrightarrow> allNetsDistinct(policy2list p) \<Longrightarrow>
   C(list2FWpolicy
       (insertDenies
          (separate (qsort (removeShadowRules2 (remdups (rm_MT_rules C 
              (insertDeny (removeShadowRules1 (policy2list p)))))) l)))) =
    C p"
  apply (subst C_eq_iD,simp_all add: C_eqLemmas_id)
   apply (metis WP1rd set_qsort wellformed1_sortedQ wellformed_eq wp1ID wp1_alternativesep wp1_aux1aa wp1n_RS2 wp1n_RS3)
  by (rule C_eq_until_separatedQ, simp_all)
    
lemma C_eq_RD_aux[rule_format]: "C (p) x = C (removeDuplicates p) x" 
  apply (induct p,simp_all)
  by (metis Cdom2 domIff nlpaux not_in_member)
    
lemma C_eq_RAD_aux[rule_format]: 
  "p \<noteq> []  \<longrightarrow> C (list2FWpolicy p) x = C (list2FWpolicy (removeAllDuplicates p)) x"
proof (induct p)
  case Nil show ?case by simp
next
  case (Cons a p) show ?case
    apply (case_tac "p = []", simp_all)
     apply (metis C_eq_RD_aux)
    apply (subst list2FWpolicyconc,simp)
    apply (case_tac "x \<in> dom (C (list2FWpolicy p))")
     apply (simp add: Cdom2 Cons.hyps domIff l2p_aux rADnMT)
    by (metis C_eq_RD_aux Cons.hyps domIff list2FWpolicyconc nlpaux rADnMT)
qed

lemma C_eq_RAD: 
  "p \<noteq> []  \<Longrightarrow> C (list2FWpolicy p) = C (list2FWpolicy (removeAllDuplicates p)) "
  by (rule ext,erule C_eq_RAD_aux)
lemma C_eq_compile: 
  "DenyAll\<in>set(policy2list p) \<Longrightarrow> all_in_list(policy2list p)l \<Longrightarrow> allNetsDistinct(policy2list p) \<Longrightarrow>
    C (list2FWpolicy
        (removeAllDuplicates
          (insertDenies
            (separate
              (FWNormalisationCore.sort
                (removeShadowRules2 (remdups (rm_MT_rules C 
                    (insertDeny (removeShadowRules1 (policy2list p)))))) l))))) =
    C p"
  apply (subst C_eq_RAD[symmetric])
   apply (rule idNMT,simp add: C_eqLemmas_id)
  by (rule C_eq_Until_InsertDenies, simp_all)

lemma C_eq_compileQ: 
  "DenyAll\<in>set(policy2list p) \<Longrightarrow> all_in_list(policy2list p)l \<Longrightarrow> allNetsDistinct(policy2list p) \<Longrightarrow>
   C (list2FWpolicy
       (removeAllDuplicates
         (insertDenies
           (separate
             (qsort (removeShadowRules2 (remdups (rm_MT_rules C 
                  (insertDeny (removeShadowRules1 (policy2list p)))))) l))))) =
    C p"
  apply (subst C_eq_RAD[symmetric],rule idNMT)
   apply (metis WP1rd sepnMT sortnMTQ wellformed_policy1_strong.simps(1) wp1ID wp1n_RS2 wp1n_RS3)
  by (rule C_eq_Until_InsertDeniesQ, simp_all)

lemma C_eq_normalize: 
  "DenyAll \<in> set (policy2list p) \<Longrightarrow> allNetsDistinct (policy2list p) \<Longrightarrow>
 all_in_list(policy2list p)(Nets_List p) \<Longrightarrow> 
 C (list2FWpolicy (normalize p)) = C p"
  unfolding normalize_def
  by (simp add: C_eq_compile)

lemma C_eq_normalizeQ: 
  "DenyAll \<in> set (policy2list p) \<Longrightarrow> allNetsDistinct (policy2list p) \<Longrightarrow> 
   all_in_list (policy2list p) (Nets_List p) \<Longrightarrow> 
   C (list2FWpolicy (normalizeQ p)) = C p"
  by (simp add: normalizeQ_def C_eq_compileQ)

lemma domSubset3: "dom (C (DenyAll \<oplus> x)) = dom (C (DenyAll))"
  by (simp add: PLemmas split_tupled_all split: option.splits)

lemma domSubset4: 
  "dom (C (DenyAllFromTo x y \<oplus> DenyAllFromTo y x \<oplus> AllowPortFromTo x y dn)) = 
   dom (C (DenyAllFromTo x y \<oplus> DenyAllFromTo y x))"
  by (auto simp: PLemmas split: option.splits decision.splits )

lemma domSubset5: 
  "dom (C (DenyAllFromTo x y \<oplus> DenyAllFromTo y x \<oplus> AllowPortFromTo y x dn)) = 
  dom (C (DenyAllFromTo x y \<oplus> DenyAllFromTo y x))"
  by (auto simp: PLemmas split: option.splits decision.splits )

lemma domSubset1: 
  "dom (C (DenyAllFromTo one two \<oplus> DenyAllFromTo two one \<oplus> AllowPortFromTo one two dn \<oplus> x)) = 
   dom (C (DenyAllFromTo one two \<oplus> DenyAllFromTo two one \<oplus> x))"
  by (simp add: PLemmas split: option.splits decision.splits) (auto simp: allow_all_def deny_all_def)

lemma domSubset2: 
  "dom (C (DenyAllFromTo one two \<oplus> DenyAllFromTo two one \<oplus> AllowPortFromTo two one dn \<oplus> x)) = 
  dom (C (DenyAllFromTo one two \<oplus> DenyAllFromTo two one \<oplus> x))"
  by (simp add: PLemmas split: option.splits decision.splits) (auto simp: allow_all_def deny_all_def)

lemma ConcAssoc2: "C (X \<oplus> Y \<oplus> ((A \<oplus> B) \<oplus> D)) = C (X \<oplus> Y \<oplus> A \<oplus> B \<oplus> D)"
  by (simp add: C.simps)

lemma ConcAssoc3: "C (X \<oplus> ((Y \<oplus> A) \<oplus> D)) = C (X \<oplus> Y \<oplus> A \<oplus> D)"
  by (simp add: C.simps)

lemma RS3_NMT[rule_format]: 
  "DenyAll \<in> set p \<longrightarrow> rm_MT_rules C p \<noteq> []"
  by (induct_tac p) (simp_all add: PLemmas)

lemma norm_notMT: "DenyAll \<in> set (policy2list p) \<Longrightarrow> normalize p \<noteq> []"
  by (simp add: DAiniD RS2_NMT RS3_NMT idNMT normalize_def rADnMT sepnMT sortnMT)

lemma norm_notMTQ: "DenyAll \<in> set (policy2list p) \<Longrightarrow> normalizeQ p \<noteq> []"
  by (simp add: DAiniD RS2_NMT RS3_NMT idNMT normalizeQ_def rADnMT sepnMT sortnMTQ)

lemmas domDA = NormalisationIntegerPortProof.domSubset3 (* legacy *)

lemmas domain_reasoning = domDA ConcAssoc2 domSubset1 domSubset2 
                          domSubset3 domSubset4  domSubset5 domSubsetDistr1
                          domSubsetDistr2 domSubsetDistrA domSubsetDistrD coerc_assoc ConcAssoc 
                          ConcAssoc3

text \<open>The following lemmas help with the normalisation\<close>
lemma list2policyR_Start[rule_format]: "p \<in> dom (C a) \<longrightarrow>
                 C (list2policyR (a # list)) p = C a p"
  by (induct "a # list" rule:list2policyR.induct) (auto simp: C.simps dom_def map_add_def) 

lemma list2policyR_End: "p \<notin> dom (C a) \<Longrightarrow>
        C (list2policyR (a # list)) p = (C a \<Oplus> list2policy (map C list)) p"
  by (rule list2policyR.induct)
    (simp_all add: C.simps dom_def map_add_def list2policy_def split: option.splits)

lemma l2polR_eq_el[rule_format]: 
  "N \<noteq> [] \<longrightarrow> C(list2policyR N) p =  (list2policy (map C N)) p"
proof (induct N) 
  case Nil show ?case by (simp_all add: list2policy_def)
next
  case (Cons a N) then show ?case
    apply (case_tac "p \<in> dom (C a)",simp_all add: domStart list2policy_def) 
     apply (rule list2policyR_Start, simp_all)
    apply (rule list2policyR.induct, simp_all)
     apply (simp_all add: C.simps dom_def map_add_def)
    apply (simp split: option.splits)
    done
qed

lemma l2polR_eq: 
  "N \<noteq> [] \<Longrightarrow> C( list2policyR N) =  (list2policy (map C N))"
  by (auto simp: list2policy_def l2polR_eq_el )

lemma list2FWpolicys_eq_el[rule_format]: 
  "Filter \<noteq> []  \<longrightarrow>  C (list2policyR Filter) p =  C (list2FWpolicy (rev Filter)) p"
proof (induct Filter) print_cases
  case Nil show ?case by (simp)
next
  case (Cons a list) then show ?case
    apply simp_all
    apply (case_tac "list = []", simp_all)
    apply (case_tac "p \<in> dom (C a)", simp_all)
     apply (rule list2policyR_Start, simp_all) 
    by (metis C.simps(4) l2polR_eq list2policyR_End nlpaux)
qed

lemma list2FWpolicys_eq: 
  "Filter \<noteq> []  \<Longrightarrow> C (list2policyR Filter) =  C (list2FWpolicy (rev Filter))"
  by (rule ext, erule list2FWpolicys_eq_el)

lemma list2FWpolicys_eq_sym: 
  "Filter \<noteq> [] \<Longrightarrow>C (list2policyR (rev Filter)) =  C (list2FWpolicy Filter)"
  by (metis list2FWpolicys_eq rev_is_Nil_conv rev_rev_ident)

lemma p_eq[rule_format]: 
  "p \<noteq> [] \<longrightarrow>  list2policy (map C (rev p)) = C (list2FWpolicy p)"
  by (metis l2polR_eq list2FWpolicys_eq_sym rev.simps(1) rev_rev_ident)

lemma p_eq2[rule_format]: 
  "normalize x \<noteq> [] \<longrightarrow> C(list2FWpolicy(normalize x)) = C x \<longrightarrow> 
   list2policy(map C (rev(normalize x))) = C x"
  by (simp add: p_eq)

lemma p_eq2Q[rule_format]: 
  "normalizeQ x \<noteq> [] \<longrightarrow>  C (list2FWpolicy (normalizeQ x)) = C x \<longrightarrow>
   list2policy (map C (rev (normalizeQ x))) = C x"
  by (simp add: p_eq)

lemma list2listNMT[rule_format]: "x \<noteq> [] \<longrightarrow>map sem x \<noteq> []"
  by (case_tac x) simp_all

lemma Norm_Distr2: 
  "r o_f ((P \<Otimes>\<^sub>2 (list2policy Q)) o d) = (list2policy ((P \<Otimes>\<^sub>L Q) (\<Otimes>\<^sub>2) r d))"
  by (rule ext, rule Norm_Distr_2)

lemma NATDistr: 
  "N \<noteq> [] \<Longrightarrow> F = C (list2policyR N) \<Longrightarrow>
    (\<lambda>(x, y). x) o\<^sub>f (NAT \<Otimes>\<^sub>2 F \<circ> (\<lambda>x. (x, x))) = 
    list2policy ((NAT \<Otimes>\<^sub>L map C N) (\<Otimes>\<^sub>2) (\<lambda>(x, y). x) (\<lambda>x. (x, x)))"
  apply (simp add: l2polR_eq) 
  apply (rule ext)
  apply (rule Norm_Distr_2)
  done

lemma C_eq_normalize_manual: 
  "DenyAll\<in>set(policy2list p) \<Longrightarrow> allNetsDistinct(policy2list p) \<Longrightarrow> all_in_list(policy2list p) l \<Longrightarrow> 
 C (list2FWpolicy (normalize_manual_order p l)) = C p"
  by (simp add: normalize_manual_order_def C_eq_compile)

lemma p_eq2_manualQ[rule_format]: 
  "normalize_manual_orderQ x l \<noteq> [] \<longrightarrow> C(list2FWpolicy (normalize_manual_orderQ x l)) = C x \<longrightarrow>
   list2policy (map C (rev (normalize_manual_orderQ x l))) = C x"
  by (simp add: p_eq)

lemma norm_notMT_manualQ: "DenyAll \<in> set (policy2list p) \<Longrightarrow> normalize_manual_orderQ p l \<noteq> []"
  by (simp add: DAiniD RS2_NMT RS3_NMT idNMT normalize_manual_orderQ_def rADnMT sepnMT sortnMTQ)

lemma C_eq_normalize_manualQ: 
  "DenyAll\<in>set(policy2list p) \<Longrightarrow> allNetsDistinct(policy2list p) \<Longrightarrow> all_in_list(policy2list p) l \<Longrightarrow> 
   C (list2FWpolicy (normalize_manual_orderQ p l)) = C p"
  by (simp add: normalize_manual_orderQ_def C_eq_compileQ)

lemma p_eq2_manual[rule_format]: 
  "normalize_manual_order x l \<noteq> [] \<longrightarrow> C (list2FWpolicy (normalize_manual_order x l)) = C x \<longrightarrow>
   list2policy (map C (rev (normalize_manual_order x l))) = C x"
  by (simp add: p_eq)

lemma norm_notMT_manual: "DenyAll \<in> set (policy2list p) \<Longrightarrow> normalize_manual_order p l \<noteq> []"
  by (simp add: RS2_NMT idNMT normalize_manual_order_def rADnMT sepnMT sortnMT wp1ID)

text\<open>
  As an example, how this theorems can be used for a concrete normalisation instantiation. 
\<close>

lemma normalizeNAT: 
  "DenyAll \<in> set (policy2list Filter) \<Longrightarrow> allNetsDistinct (policy2list Filter) \<Longrightarrow>
   all_in_list (policy2list Filter) (Nets_List Filter) \<Longrightarrow>
   (\<lambda>(x, y). x) o\<^sub>f (NAT \<Otimes>\<^sub>2 C Filter \<circ> (\<lambda>x. (x, x))) =
   list2policy ((NAT \<Otimes>\<^sub>L map C (rev (FWNormalisationCore.normalize Filter))) (\<Otimes>\<^sub>2) 
       (\<lambda>(x, y). x) (\<lambda>x. (x, x)))"
  by (simp add: C_eq_normalize NATDistr list2FWpolicys_eq_sym norm_notMT)

lemma domSimpl[simp]: "dom (C (A \<oplus> DenyAll)) = dom (C (DenyAll))"
  by (simp add: PLemmas)

text \<open>
  The followin theorems can be applied when prepending the usual normalisation with an 
  additional step and using another semantical interpretation function. This is a general recipe 
  which can be applied whenever one nees to combine several normalisation strategies. 
\<close> 

lemma CRotate_eq_rotateC: "CRotate p = C (rotatePolicy p)" 
  by (induct p rule: rotatePolicy.induct) (simp_all add: C.simps map_add_def)

lemma DAinRotate: 
  "DenyAll \<in> set (policy2list p) \<Longrightarrow> DenyAll \<in> set (policy2list (rotatePolicy p))"
  apply (induct p,simp_all)
  subgoal for p1 p2 
    apply (case_tac "DenyAll \<in> set (policy2list p1)",simp_all)
    done 
  done
    
lemma DAUniv: "dom (CRotate (P \<oplus> DenyAll)) = UNIV"
  by (metis CRotate.simps(1) CRotate.simps(4) CRotate_eq_rotateC DAAux PLemmas(4) UNIV_eq_I domSubset3)

lemma p_eq2R[rule_format]: 
  "normalize (rotatePolicy x) \<noteq> [] \<longrightarrow> C(list2FWpolicy(normalize (rotatePolicy x))) = CRotate x \<longrightarrow>
   list2policy (map C (rev (normalize (rotatePolicy x)))) = CRotate x"
  by (simp add: p_eq)

lemma C_eq_normalizeRotate: 
  "DenyAll \<in> set (policy2list p) \<Longrightarrow> allNetsDistinct (policy2list (rotatePolicy p)) \<Longrightarrow>
   all_in_list (policy2list (rotatePolicy p)) (Nets_List (rotatePolicy p)) \<Longrightarrow>
   C (list2FWpolicy
        (removeAllDuplicates
          (insertDenies
            (separate
              (sort(removeShadowRules2(remdups(rm_MT_rules C 
                        (insertDeny(removeShadowRules1(policy2list(rotatePolicy p)))))))
                (Nets_List (rotatePolicy p))))))) =
   CRotate p"
  by (simp add: CRotate_eq_rotateC C_eq_compile DAinRotate)

lemma C_eq_normalizeRotate2:
  "DenyAll \<in> set (policy2list p) \<Longrightarrow>
   allNetsDistinct (policy2list (rotatePolicy p)) \<Longrightarrow>
   all_in_list (policy2list (rotatePolicy p)) (Nets_List (rotatePolicy p)) \<Longrightarrow>
   C (list2FWpolicy (FWNormalisationCore.normalize (rotatePolicy p))) = CRotate p"
  by (simp add: normalize_def, erule C_eq_normalizeRotate,simp_all)
    
end
