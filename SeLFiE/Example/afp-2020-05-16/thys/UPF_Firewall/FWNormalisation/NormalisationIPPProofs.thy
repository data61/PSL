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

subsection \<open>Normalisation Proofs: Integer Protocol\<close>
theory 
  NormalisationIPPProofs
  imports 
    NormalisationIntegerPortProof
begin

text\<open>
  Normalisation proofs which are specific to the IntegerProtocol address representation. 
\<close> 

lemma ConcAssoc: "Cp((A \<oplus> B) \<oplus> D) = Cp(A \<oplus> (B \<oplus> D))"
  by (simp add: Cp.simps)

lemma aux26[simp]: 
  "twoNetsDistinct a b c d \<Longrightarrow> dom (Cp (AllowPortFromTo a b p)) \<inter> dom (Cp (DenyAllFromTo c d)) = {}"
  by(auto simp:twoNetsDistinct_def netsDistinct_def PLemmas, auto)

lemma wp2_aux[rule_format]: 
  "wellformed_policy2Pr (xs @ [x]) \<longrightarrow> wellformed_policy2Pr xs"
  apply(induct xs, simp_all) 
  subgoal for a as
    apply(case_tac "a", simp_all)
    done
  done
    
lemma Cdom2: "x \<in> dom(Cp b) \<Longrightarrow> Cp (a \<oplus> b) x = (Cp b) x"
  by (auto simp: Cp.simps)

lemma wp2Conc[rule_format]: "wellformed_policy2Pr (x#xs) \<Longrightarrow> wellformed_policy2Pr xs"
  by (case_tac "x",simp_all)
    
lemma DAimpliesMR_E[rule_format]: "DenyAll \<in> set p \<longrightarrow>
                                   (\<exists> r. applied_rule_rev Cp x p = Some r)"
  apply (simp add: applied_rule_rev_def)
  apply (rule_tac xs = p in rev_induct, simp_all)
  by (metis Cp.simps(1) denyAllDom)
    
lemma DAimplieMR[rule_format]: "DenyAll \<in> set p \<Longrightarrow> applied_rule_rev Cp x p \<noteq> None"
  by (auto intro: DAimpliesMR_E)
    
lemma MRList1[rule_format]: "x \<in> dom (Cp a) \<Longrightarrow> applied_rule_rev Cp x (b@[a]) = Some a"
  by (simp add: applied_rule_rev_def)
    
lemma MRList2: "x \<in> dom (Cp a) \<Longrightarrow> applied_rule_rev Cp x (c@b@[a]) = Some a"
  by (simp add: applied_rule_rev_def)
    
lemma MRList3: 
  "x \<notin> dom(Cp xa) \<Longrightarrow> applied_rule_rev Cp x (a@b#xs@[xa]) = applied_rule_rev Cp x (a @ b # xs)"
  by (simp add: applied_rule_rev_def)
    
lemma CConcEnd[rule_format]: 
  "Cp a x = Some y \<longrightarrow> Cp (list2FWpolicy (xs @ [a])) x = Some y" (is "?P xs")
  apply (rule_tac P = ?P in list2FWpolicy.induct)
  by (simp_all add:Cp.simps)
    
lemma CConcStartaux: "Cp a x = None \<Longrightarrow> (Cp aa ++ Cp a) x = Cp aa x"
  by (simp add: PLemmas)
    
lemma CConcStart[rule_format]: 
  "xs \<noteq> [] \<longrightarrow> Cp a x = None \<longrightarrow> Cp (list2FWpolicy (xs @ [a])) x = Cp (list2FWpolicy xs) x"
  by (rule list2FWpolicy.induct) (simp_all add: PLemmas)
    
lemma mrNnt[simp]: "applied_rule_rev Cp x p = Some a \<Longrightarrow> p \<noteq> []"
  by (simp add: applied_rule_rev_def)(auto)
    
lemma mr_is_C[rule_format]: 
  "applied_rule_rev Cp x p = Some a \<longrightarrow> Cp (list2FWpolicy (p)) x = Cp a x"
  apply (simp add: applied_rule_rev_def)
  apply (rule rev_induct, simp_all, safe)
    apply (metis CConcEnd )
   apply (metis CConcEnd)
  by (metis CConcStart applied_rule_rev_def mrNnt option.exhaust)
      
lemma CConcStart2: 
  "p \<noteq> [] \<Longrightarrow> x \<notin> dom (Cp a) \<Longrightarrow> Cp(list2FWpolicy (p@[a])) x = Cp (list2FWpolicy p)x"
  by (erule CConcStart,simp add: PLemmas)
    
lemma CConcEnd1: 
  "q@p \<noteq> [] \<Longrightarrow> x \<notin> dom (Cp a) \<Longrightarrow> Cp(list2FWpolicy(q@p@[a])) x = Cp (list2FWpolicy (q@p))x"
  by (subst lCdom2) (rule CConcStart2, simp_all)
    
lemma CConcEnd2[rule_format]: 
  "x \<in> dom (Cp a) \<longrightarrow> Cp (list2FWpolicy (xs @ [a])) x = Cp a x"  (is "?P xs")
  by (rule_tac P = ?P in list2FWpolicy.induct) (auto simp:Cp.simps)
      
lemma bar3: 
  "x \<in> dom (Cp (list2FWpolicy (xs @ [xa]))) \<Longrightarrow> x \<in> dom (Cp (list2FWpolicy xs)) \<or> x \<in> dom (Cp xa)"
  by auto (metis CConcStart eq_Nil_appendI l2p_aux2 option.simps(3))
    
lemma CeqEnd[rule_format,simp]: 
  "a \<noteq> [] \<longrightarrow> x \<in> dom (Cp(list2FWpolicy a)) \<longrightarrow> Cp(list2FWpolicy(b@a)) x = (Cp(list2FWpolicy a)) x"
proof (induct rule: rev_induct)
  case Nil show ?case by simp
next
  case (snoc xa xs) show ?case  
    apply (case_tac "xs \<noteq> []", simp_all)
     apply (case_tac "x \<in> dom (Cp xa)")
      apply (metis CConcEnd2 MRList2 mr_is_C )
     apply (metis snoc.hyps CConcEnd1 CConcStart2 Nil_is_append_conv bar3 )
    by (metis MRList2 eq_Nil_appendI mr_is_C )
qed
  
lemma CConcStartA[rule_format,simp]: 
  "x \<in> dom (Cp a) \<longrightarrow> x \<in> dom (Cp (list2FWpolicy (a # b)))" (is "?P b")
  by (rule_tac P = ?P in list2FWpolicy.induct)   (simp_all add: Cp.simps)
    
lemma domConc: 
  "x \<in> dom (Cp (list2FWpolicy b)) \<Longrightarrow> b \<noteq> []  \<Longrightarrow> x \<in> dom (Cp (list2FWpolicy (a@b)))"
  by (auto simp: PLemmas)
    
lemma CeqStart[rule_format,simp]:
  "x \<notin> dom (Cp (list2FWpolicy a)) \<longrightarrow> a \<noteq> [] \<longrightarrow> b \<noteq> [] \<longrightarrow>
   Cp (list2FWpolicy (b@a)) x = (Cp (list2FWpolicy b)) x"
  by (rule list2FWpolicy.induct,simp_all) (auto simp: list2FWpolicyconc PLemmas)
    
lemma C_eq_if_mr_eq2: 
  "applied_rule_rev Cp x a = Some r \<Longrightarrow> applied_rule_rev Cp x b = Some r \<Longrightarrow> a\<noteq>[] \<Longrightarrow> b\<noteq>[] \<Longrightarrow>
   (Cp (list2FWpolicy a)) x = (Cp (list2FWpolicy b)) x"
  by (metis mr_is_C)
    
lemma nMRtoNone[rule_format]: 
  "p \<noteq> [] \<longrightarrow> applied_rule_rev Cp x p = None \<longrightarrow> Cp (list2FWpolicy p) x = None"
proof (induct rule: rev_induct) 
  case Nil show ?case by simp
next
  case (snoc xa xs) show ?case
    apply (case_tac "xs = []", simp_all)
    by (simp_all add: snoc.hyps applied_rule_rev_def dom_def)
qed

lemma C_eq_if_mr_eq: 
  "applied_rule_rev Cp x b = applied_rule_rev Cp x a \<Longrightarrow> a \<noteq> [] \<Longrightarrow> b \<noteq> [] \<Longrightarrow>  
  (Cp (list2FWpolicy a)) x = (Cp (list2FWpolicy b)) x"
  apply (cases "applied_rule_rev Cp x a = None", simp_all)
   apply (subst nMRtoNone,simp_all)
   apply (subst nMRtoNone,simp_all)
  by (auto intro: C_eq_if_mr_eq2)
    
lemma notmatching_notdom: 
  "applied_rule_rev Cp x (p@[a]) \<noteq> Some a \<Longrightarrow> x \<notin> dom (Cp a)"
  by (simp add: applied_rule_rev_def split: if_splits)

lemma foo3a[rule_format]: 
  "applied_rule_rev Cp x (a@[b]@c) = Some b \<longrightarrow>  r \<in> set c \<longrightarrow> b \<notin> set c \<longrightarrow> x \<notin> dom (Cp r)"
proof (induct rule: rev_induct) 
  case Nil show ?case by simp
next
  case (snoc xa xs) show ?case
    apply simp_all
    apply (rule impI|rule conjI|simp)+
     apply (rule_tac p = "a @ b # xs" in notmatching_notdom,simp_all)
    by (metis Cons_eq_appendI NormalisationIPPProofs.MRList2 NormalisationIPPProofs.MRList3 
        append_Nil option.inject snoc.hyps)
qed

lemma foo3D: 
  "wellformed_policy1 p \<Longrightarrow> p=DenyAll#ps \<Longrightarrow> applied_rule_rev Cp x p = Some DenyAll \<Longrightarrow> r\<in>set ps \<Longrightarrow> 
   x \<notin> dom (Cp r)"
  by (rule_tac a = "[]" and b = "DenyAll" and c = "ps"  in foo3a, simp_all)
    
lemma foo4[rule_format]: 
  "set p = set s \<and> (\<forall> r. r \<in> set p \<longrightarrow> x \<notin> dom (Cp r)) \<longrightarrow> (\<forall> r .r \<in> set s \<longrightarrow> x \<notin> dom (Cp r))"
  by simp
    
lemma foo5b[rule_format]: 
  "x \<in> dom (Cp b) \<longrightarrow> (\<forall> r. r \<in> set c \<longrightarrow> x \<notin> dom (Cp r))\<longrightarrow> applied_rule_rev Cp x (b#c) = Some b"
  apply (simp add: applied_rule_rev_def)
  apply (rule_tac xs = c in rev_induct, simp_all)  
  done

lemma mr_first: 
  "x \<in> dom (Cp b) \<Longrightarrow> (\<forall> r. r \<in> set c \<longrightarrow> x \<notin> dom (Cp r)) \<Longrightarrow> s = b#c \<Longrightarrow> 
   applied_rule_rev Cp x s = Some b"
  by (simp add: foo5b)
    
lemma mr_charn[rule_format]: 
  "a \<in> set p \<longrightarrow> (x \<in> dom (Cp a)) \<longrightarrow>(\<forall> r. r \<in> set p \<and> x \<in> dom (Cp r) \<longrightarrow> r = a) \<longrightarrow>  
   applied_rule_rev Cp x p = Some a"
  apply(rule_tac xs = p in rev_induct) 
   apply(simp_all only:applied_rule_rev_def)
   apply(simp,safe,simp_all)
  by(auto)

lemma foo8: 
  "\<forall> r. r \<in> set p \<and> x \<in> dom (Cp r) \<longrightarrow> r = a \<Longrightarrow> set p = set s \<Longrightarrow> 
   \<forall> r. r \<in> set s \<and> x \<in> dom (Cp r) \<longrightarrow> r = a"
  by auto
    
lemma mrConcEnd[rule_format]: 
  "applied_rule_rev Cp x (b # p) = Some a \<longrightarrow> a \<noteq> b \<longrightarrow> applied_rule_rev Cp x p = Some a"
  apply (simp add: applied_rule_rev_def)
  apply (rule_tac xs = p in rev_induct,simp_all) 
  by auto
    
    
lemma wp3tl[rule_format]: "wellformed_policy3Pr p \<longrightarrow> wellformed_policy3Pr (tl p)"
  apply (induct p, simp_all) 
  subgoal for a as
    apply(case_tac a, simp_all)
    done
  done
    
lemma wp3Conc[rule_format]: "wellformed_policy3Pr (a#p) \<longrightarrow> wellformed_policy3Pr p"
  by (induct p, simp_all, case_tac a, simp_all)


lemma foo98[rule_format]:
  "applied_rule_rev Cp x (aa # p) = Some a \<longrightarrow> x \<in> dom (Cp r) \<longrightarrow> r \<in> set p \<longrightarrow> a \<in> set p"
  unfolding applied_rule_rev_def
proof (induct rule: rev_induct)
  case Nil show ?case by simp
next
  case (snoc xa xs) then show ?case
    by simp_all (case_tac "r = xa", simp_all)
qed
  
lemma mrMTNone[simp]: "applied_rule_rev Cp x [] = None"
  by (simp add: applied_rule_rev_def)
    
lemma DAAux[simp]: "x \<in> dom (Cp DenyAll)"
  by (simp add: dom_def PolicyCombinators.PolicyCombinators Cp.simps)
    
lemma mrSet[rule_format]: "applied_rule_rev Cp x p = Some r \<longrightarrow> r \<in> set p"
  unfolding  applied_rule_rev_def
  by (rule_tac xs=p in rev_induct) simp_all
    
lemma mr_not_Conc: "singleCombinators p \<Longrightarrow> applied_rule_rev Cp x p \<noteq> Some (a\<oplus>b)"
  by (auto simp:  mrSet dest: mrSet elim: SCnotConc)
    
    
lemma foo25[rule_format]: "wellformed_policy3Pr (p@[x]) \<longrightarrow> wellformed_policy3Pr p"
  apply(induct p, simp_all)
  subgoal for a p
    apply(case_tac a, simp_all)
    done
  done
    
lemma mr_in_dom[rule_format]: "applied_rule_rev Cp x p = Some a \<longrightarrow> x \<in> dom (Cp a)"
  by (rule_tac xs = p in rev_induct) (auto simp: applied_rule_rev_def)
    
    
lemma wp3EndMT[rule_format]: 
  "wellformed_policy3Pr (p@[xs]) \<longrightarrow>  AllowPortFromTo a b po \<in> set p \<longrightarrow>
   dom (Cp (AllowPortFromTo a b po)) \<inter> dom (Cp xs) = {}"
  apply (induct p, simp_all)
  by (metis NormalisationIPPProofs.wp3Conc aux0_4 inf_commute list.set_intros(1) 
      wellformed_policy3Pr.simps(2))
    
lemma foo29: "dom (Cp a) \<noteq> {} \<Longrightarrow> dom (Cp a) \<inter> dom (Cp b) = {} \<Longrightarrow> a \<noteq> b"
  by auto
    
lemma foo28:  
  "AllowPortFromTo a b po\<in>set p \<Longrightarrow> dom(Cp(AllowPortFromTo a b po))\<noteq>{} \<Longrightarrow> 
   (wellformed_policy3Pr(p@[x])) \<Longrightarrow> 
   x \<noteq> AllowPortFromTo a b po"
  by (metis foo29 Cp.simps(3) wp3EndMT)
    
lemma foo28a[rule_format]: "x \<in> dom (Cp a) \<Longrightarrow> dom (Cp a) \<noteq> {}"
  by auto
    
lemma allow_deny_dom[simp]: 
  "dom (Cp (AllowPortFromTo a b po)) \<subseteq> dom (Cp (DenyAllFromTo a b))"
  by (simp_all add: twoNetsDistinct_def netsDistinct_def PLemmas) auto 
    
lemma DenyAllowDisj: 
  "dom (Cp (AllowPortFromTo a b p)) \<noteq> {} \<Longrightarrow> 
   dom (Cp (DenyAllFromTo a b)) \<inter> dom (Cp (AllowPortFromTo a b p))  \<noteq> {}"
  by (metis Int_absorb1 allow_deny_dom)
    
lemma foo31: 
  "\<forall> r. r \<in> set p \<and> x \<in> dom (Cp r) \<longrightarrow> 
         (r = AllowPortFromTo a b po \<or> r = DenyAllFromTo a b \<or> r = DenyAll) \<Longrightarrow> 
   set p = set s \<Longrightarrow> 
   (\<forall>r. r\<in>set s \<and> x\<in>dom(Cp r) \<longrightarrow> r=AllowPortFromTo a b po \<or> r=DenyAllFromTo a b \<or> r = DenyAll)"
  by auto
    
lemma wp1_auxa: "wellformed_policy1_strong p\<Longrightarrow>(\<exists> r. applied_rule_rev Cp x p = Some r)"
  apply (rule DAimpliesMR_E)
  by (erule wp1_aux1aa)
    
lemma deny_dom[simp]:  
  "twoNetsDistinct a b c d \<Longrightarrow> dom (Cp (DenyAllFromTo a b)) \<inter> dom (Cp (DenyAllFromTo c d)) = {}"
  by (simp add: Cp.simps) (erule aux6)
    
lemma domTrans: "\<lbrakk>dom a \<subseteq> dom b; dom(b) \<inter> dom (c) = {}\<rbrakk> \<Longrightarrow> dom(a) \<inter> dom(c) = {}" 
  by auto
    
lemma DomInterAllowsMT: 
  " twoNetsDistinct a b c d \<Longrightarrow> dom (Cp(AllowPortFromTo a b p)) \<inter> dom(Cp(AllowPortFromTo c d po))={}"
  apply (case_tac "p = po", simp_all)
   apply (rule_tac b = "Cp (DenyAllFromTo a b)" in domTrans, simp_all)
   apply (metis domComm aux26 tNDComm)
  apply (simp add: twoNetsDistinct_def netsDistinct_def PLemmas) 
  by (auto simp: prod_eqI)
    
lemma DomInterAllowsMT_Ports: 
  "p \<noteq> po \<Longrightarrow> dom (Cp (AllowPortFromTo a b p)) \<inter> dom (Cp (AllowPortFromTo c d po)) = {}"
  apply (simp add: twoNetsDistinct_def netsDistinct_def PLemmas)
  by (auto simp: prod_eqI)
    
lemma wellformed_policy3_charn[rule_format]: 
  "singleCombinators p \<longrightarrow> distinct p \<longrightarrow> allNetsDistinct p \<longrightarrow> 
   wellformed_policy1 p \<longrightarrow> wellformed_policy2Pr p  \<longrightarrow> wellformed_policy3Pr p"
proof (induct p)
  case Nil show ?case by simp
next
  case (Cons a p) then show ?case  
    apply (auto intro: singleCombinatorsConc ANDConc waux2 wp2Conc)
    apply (case_tac a,simp_all, clarify)
    subgoal for a b c d r 
      apply (case_tac r,simp_all)
        apply (metis Int_commute) 
       apply (metis DomInterAllowsMT aux7aa DomInterAllowsMT_Ports)
      apply (metis aux0_0 )
      done
    done
qed
  
lemma DistinctNetsDenyAllow: 
  "DenyAllFromTo b c \<in> set p \<Longrightarrow> AllowPortFromTo a d po \<in> set p\<Longrightarrow> allNetsDistinct p \<Longrightarrow>
  dom (Cp (DenyAllFromTo b c)) \<inter> dom (Cp (AllowPortFromTo a d po)) \<noteq> {}\<Longrightarrow>
  b = a \<and> c = d" 
  apply (simp add: allNetsDistinct_def)
  apply (frule_tac x = "b" in spec) 
  apply (drule_tac x = "d" in spec)
  apply (drule_tac x = "a" in spec)
  apply (drule_tac x = "c" in spec)
  apply (metis Int_commute ND0aux1 ND0aux3 NDComm aux26 twoNetsDistinct_def ND0aux2 ND0aux4)
  done
    
lemma DistinctNetsAllowAllow: 
  "AllowPortFromTo b c poo \<in> set p \<Longrightarrow> AllowPortFromTo a d po \<in> set p \<Longrightarrow> 
  allNetsDistinct p \<Longrightarrow> dom(Cp(AllowPortFromTo b c poo)) \<inter> dom(Cp(AllowPortFromTo a d po)) \<noteq> {} \<Longrightarrow> 
  b = a \<and> c = d \<and> poo = po" 
  apply (simp add: allNetsDistinct_def)
  apply (frule_tac x = "b" in spec) 
  apply (drule_tac x = "d" in spec)
  apply (drule_tac x = "a" in spec)
  apply (drule_tac x = "c" in spec)
  apply (metis DomInterAllowsMT DomInterAllowsMT_Ports ND0aux3 ND0aux4 NDComm  twoNetsDistinct_def)
  done
    
lemma WP2RS2[simp]: 
  "singleCombinators p \<Longrightarrow> distinct p \<Longrightarrow> allNetsDistinct p \<Longrightarrow> 
   wellformed_policy2Pr (removeShadowRules2 p)"
proof (induct p)
  case Nil
  then show ?case by simp
next
  case (Cons x xs) 
  have wp_xs: "wellformed_policy2Pr (removeShadowRules2 xs)" 
    by (metis Cons ANDConc distinct.simps(2) singleCombinatorsConc)
  show ?case
  proof (cases x) 
    case DenyAll thus ?thesis using wp_xs by simp
  next  
    case (DenyAllFromTo a b) thus ?thesis
      using wp_xs Cons  
      by (simp,metis DenyAllFromTo aux aux7 tNDComm deny_dom)
  next
    case (AllowPortFromTo a b p) thus ?thesis
      using  wp_xs 
      by (simp, metis aux26 AllowPortFromTo Cons(4) aux aux7a tNDComm)
  next
    case (Conc a b) thus ?thesis
      by (metis Conc Cons(2) singleCombinators.simps(2)) 
  qed
qed
  
lemma AD_aux: 
  "AllowPortFromTo a b po \<in> set p \<Longrightarrow> DenyAllFromTo c d \<in> set p \<Longrightarrow> 
   allNetsDistinct  p \<Longrightarrow> singleCombinators p \<Longrightarrow> a \<noteq> c \<or> b \<noteq> d \<Longrightarrow>
   dom (Cp (AllowPortFromTo a b po)) \<inter> dom (Cp (DenyAllFromTo c d)) = {}"
  by (rule aux26,rule_tac x ="AllowPortFromTo a b po" and y = "DenyAllFromTo c d" in tND) auto 
    
lemma sorted_WP2[rule_format]: 
  "sorted p l \<longrightarrow> all_in_list p l \<longrightarrow> distinct p \<longrightarrow> allNetsDistinct p \<longrightarrow> singleCombinators p \<longrightarrow> 
   wellformed_policy2Pr p"
proof (induct p)
  case Nil thus ?case by simp 
next
  case (Cons a p) thus ?case
  proof (cases a)
    case DenyAll thus ?thesis 
      using  Cons by (auto intro: ANDConc singleCombinatorsConc sortedConcEnd)
  next
    case (DenyAllFromTo c d) thus ?thesis 
      using  Cons apply (simp, intro impI conjI allI impI deny_dom)
      by (auto intro: aux7 tNDComm ANDConc singleCombinatorsConc sortedConcEnd) 
  next
    case (AllowPortFromTo c d e) thus ?thesis 
      using Cons  apply simp
      apply (intro impI conjI allI, rename_tac "aa" "b")
       apply (rule aux26)
      subgoal for aa b
        apply (rule_tac x = "AllowPortFromTo c d e" and y = "DenyAllFromTo aa b" in tND, 
            assumption,simp_all)
        apply (subgoal_tac "smaller (AllowPortFromTo c d e) (DenyAllFromTo aa b) l") 	
         apply (simp split: if_splits)
         apply metis
        apply (erule sorted_is_smaller, simp_all)
        apply (metis bothNet.simps(2) in_list.simps(2) in_set_in_list)
        done
      by (auto intro: aux7 tNDComm ANDConc singleCombinatorsConc sortedConcEnd)
  next
    case (Conc a b) thus ?thesis using Cons by simp 
  qed
qed
  
lemma wellformed2_sorted[simp]: 
  "all_in_list p l \<Longrightarrow> distinct p \<Longrightarrow> allNetsDistinct p \<Longrightarrow> singleCombinators p \<Longrightarrow> 
   wellformed_policy2Pr (sort p l)"
  by (metis distinct_sort set_sort sorted_WP2 SC3 aND_sort all_in_listSubset order_refl sort_is_sorted)
    
lemma wellformed2_sortedQ[simp]: 
  "all_in_list p l \<Longrightarrow> distinct p \<Longrightarrow> allNetsDistinct p \<Longrightarrow> singleCombinators p \<Longrightarrow> 
   wellformed_policy2Pr (qsort p l)"
  by (metis sorted_WP2 SC3Q aND_sortQ all_in_listSubset distinct_sortQ set_sortQ sort_is_sortedQ subsetI)
    
lemma C_DenyAll[simp]: "Cp (list2FWpolicy (xs @ [DenyAll])) x = Some (deny ())"
  by (auto simp: PLemmas)
    
lemma C_eq_RS1n:
  "Cp(list2FWpolicy (removeShadowRules1_alternative p)) = Cp(list2FWpolicy p)"
proof (cases "p")
  case Nil then show ?thesis 
    by (simp, metis list2FWpolicy.simps(1) rSR1_eq removeShadowRules1.simps(2))
next
  case (Cons a list) then show ?thesis 
    apply (hypsubst, simp)
    apply (thin_tac "p = a # list")
  proof (induct rule: rev_induct)
    case Nil show ?case  by (metis rSR1_eq removeShadowRules1.simps(2))
  next
    case (snoc x xs) show ?case
      apply (case_tac "xs = []", simp_all)
       apply (simp add: removeShadowRules1_alternative_def)
       apply (insert snoc.hyps, case_tac x, simp_all)
      apply (rule ext, rename_tac xa) 
      apply (case_tac "x = DenyAll",simp_all add: PLemmas)
      apply (rule_tac t = "removeShadowRules1_alternative (xs @ [x])" and
          s = "(removeShadowRules1_alternative xs)@[x]" in subst)
       apply (erule RS1n_assoc)
      subgoal for a
        apply (case_tac "a \<in> dom (Cp x)", simp_all)
        done
      done
  qed
qed
  
lemma C_eq_RS1[simp]: 
  "p \<noteq> [] \<Longrightarrow> Cp(list2FWpolicy (removeShadowRules1 p)) = Cp(list2FWpolicy p)"
  by (metis rSR1_eq C_eq_RS1n)
    
lemma EX_MR_aux[rule_format]: 
  "applied_rule_rev Cp x (DenyAll # p) \<noteq> Some DenyAll \<longrightarrow> (\<exists>y. applied_rule_rev Cp x p = Some y)"
  by (simp add: applied_rule_rev_def) (rule_tac xs = p in rev_induct, simp_all)  
    
lemma EX_MR : 
  "applied_rule_rev Cp x p \<noteq> (Some DenyAll) \<Longrightarrow> p = DenyAll#ps \<Longrightarrow> 
   (applied_rule_rev Cp x p = applied_rule_rev Cp x ps)"
  apply (auto,subgoal_tac "applied_rule_rev Cp x (DenyAll#ps) \<noteq> None", auto)
   apply (metis mrConcEnd)
  by (metis DAimpliesMR_E list.sel(1) hd_in_set list.simps(3) not_Some_eq)

lemma mr_not_DA:
  "wellformed_policy1_strong s \<Longrightarrow> applied_rule_rev Cp x p = Some (DenyAllFromTo a ab) \<Longrightarrow>
    set p = set s \<Longrightarrow> applied_rule_rev Cp x s \<noteq> Some DenyAll"
  apply (subst wp1n_tl, simp_all)
  by (metis (mono_tags, lifting) Combinators.distinct(1) foo98          
      mrSet mr_in_dom WP1n_DA_notinSet set_ConsD wp1n_tl)

lemma domsMT_notND_DD: 
  "dom (Cp (DenyAllFromTo a b)) \<inter> dom (Cp (DenyAllFromTo c d)) \<noteq> {} \<Longrightarrow> \<not> netsDistinct a c"
  by (erule contrapos_nn) (simp add: Cp.simps aux6 twoNetsDistinct_def)
    
lemma domsMT_notND_DD2: 
  "dom (Cp (DenyAllFromTo a b)) \<inter> dom (Cp (DenyAllFromTo c d)) \<noteq> {} \<Longrightarrow> \<not> netsDistinct b d"
  by (erule contrapos_nn) (simp add: Cp.simps aux6 twoNetsDistinct_def)
    
lemma domsMT_notND_DD3: 
  "x \<in> dom (Cp (DenyAllFromTo a b)) \<Longrightarrow> x \<in> dom (Cp (DenyAllFromTo c d)) \<Longrightarrow> \<not> netsDistinct a c"
  by (auto intro!: domsMT_notND_DD)
    
lemma domsMT_notND_DD4: 
  "x \<in> dom (Cp (DenyAllFromTo a b)) \<Longrightarrow> x \<in> dom (Cp (DenyAllFromTo c d)) \<Longrightarrow> \<not> netsDistinct b d"
  by (auto intro!: domsMT_notND_DD2)
    
lemma NetsEq_if_sameP_DD: 
  "allNetsDistinct p \<Longrightarrow> u\<in> set p \<Longrightarrow> v\<in> set p \<Longrightarrow> u = (DenyAllFromTo a b) \<Longrightarrow> 
   v = (DenyAllFromTo c d) \<Longrightarrow> x \<in> dom (Cp (u)) \<Longrightarrow> x \<in> dom (Cp (v)) \<Longrightarrow> 
    a = c \<and> b = d"
  unfolding allNetsDistinct_def
  by (simp)(metis allNetsDistinct_def ND0aux1 ND0aux2 domsMT_notND_DD3 domsMT_notND_DD4 )

lemma rule_charn1: 
  assumes aND         : "allNetsDistinct p"
    and     mr_is_allow : "applied_rule_rev Cp x p = Some (AllowPortFromTo a b po)"
    and     SC          : "singleCombinators p"
    and     inp         : "r \<in> set p" 
    and     inDom       : "x \<in> dom (Cp r)"
  shows   "(r = AllowPortFromTo a b po \<or> r = DenyAllFromTo a b \<or> r = DenyAll)"
proof (cases r) 
  case DenyAll show ?thesis  by (metis DenyAll)
next
  case (DenyAllFromTo x y) show ?thesis 
    by (metis DenyAllFromTo NormalisationIPPProofs.AD_aux NormalisationIPPProofs.mrSet 
        NormalisationIPPProofs.mr_in_dom SC aND domInterMT inDom inp mr_is_allow)
next
  case (AllowPortFromTo x y b) show ?thesis 
    by (metis (mono_tags, lifting) AllowPortFromTo NormalisationIPPProofs.DistinctNetsAllowAllow 
        NormalisationIPPProofs.mrSet NormalisationIPPProofs.mr_in_dom aND domInterMT inDom 
        inp mr_is_allow) 
next
  case (Conc x y) thus ?thesis using assms by (metis aux0_0)
qed

lemma none_MT_rulessubset[rule_format]: 
  "none_MT_rules Cp a \<longrightarrow> set b \<subseteq> set a \<longrightarrow> none_MT_rules Cp b"
  by (induct b,simp_all) (metis notMTnMT)
    
lemma nMTSort: "none_MT_rules Cp p \<Longrightarrow> none_MT_rules Cp (sort p l)"
  by (metis set_sort nMTeqSet)
    
lemma nMTSortQ: "none_MT_rules Cp p \<Longrightarrow> none_MT_rules Cp (qsort p l)"
  by (metis set_sortQ nMTeqSet)

lemma wp3char[rule_format]: "none_MT_rules Cp xs \<and>  Cp (AllowPortFromTo a b po) = Map.empty \<and> 
                            wellformed_policy3Pr (xs @ [DenyAllFromTo a b]) \<longrightarrow> 
                             AllowPortFromTo a b po \<notin> set xs"
  by (induct xs, simp_all) (metis domNMT wp3Conc)

lemma wp3charn[rule_format]: 
  assumes domAllow:     "dom (Cp (AllowPortFromTo a b po)) \<noteq> {}" 
    and     wp3:          "wellformed_policy3Pr (xs @ [DenyAllFromTo a b])"
  shows allowNotInList: "AllowPortFromTo a b po \<notin> set xs"
  apply (insert assms)
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x xs) show ?case using Cons
    by (simp,auto intro: wp3Conc) (auto simp: DenyAllowDisj domAllow)
qed

lemma rule_charn2: 
  assumes aND:        "allNetsDistinct p"
    and wp1:            "wellformed_policy1 p"
    and SC:             "singleCombinators p"
    and wp3:            "wellformed_policy3Pr p"
    and allow_in_list:  "AllowPortFromTo c d po \<in> set p"
    and x_in_dom_allow: "x \<in> dom (Cp (AllowPortFromTo c d po))"
  shows               "applied_rule_rev Cp x p = Some (AllowPortFromTo c d po)"
proof  (insert assms, induct p rule: rev_induct)    
  case Nil show ?case using Nil by simp
next 
  case (snoc y ys) show ?case using snoc
    apply simp
    apply (case_tac "y = (AllowPortFromTo c d po)")
     apply (simp add: applied_rule_rev_def)
    apply simp_all
    apply (subgoal_tac "ys \<noteq> []")
     apply (subgoal_tac "applied_rule_rev Cp x ys = Some (AllowPortFromTo c d po)")
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
    case (AllowPortFromTo a1 a2 b) thus ?thesis using AllowPortFromTo snoc apply simp
      apply (simp_all add: applied_rule_rev_def)
      apply (rule conjI)
       apply (metis domInterMT  wp3EndMT)
      by (metis ANDConcEnd AllowPortFromTo SCConcEnd WP1ConcEnd foo25 x_in_dom_allow)
  next
    case (Conc a b) thus ?thesis 
      using Conc snoc apply simp
      by (metis Conc aux0_0 in_set_conv_decomp) 
  qed
qed

lemma rule_charn3: 
 "wellformed_policy1 p \<Longrightarrow> allNetsDistinct p \<Longrightarrow> singleCombinators p \<Longrightarrow> 
  wellformed_policy3Pr p \<Longrightarrow> applied_rule_rev Cp x p = Some (DenyAllFromTo c d) \<Longrightarrow> 
  AllowPortFromTo a b po \<in> set p \<Longrightarrow> x \<notin> dom (Cp (AllowPortFromTo a b po))"
  by (clarify) (simp add: NormalisationIPPProofs.rule_charn2 domI)

lemma rule_charn4: 
  assumes wp1:    "wellformed_policy1 p" 
    and     aND:    "allNetsDistinct p" 
    and     SC:     "singleCombinators p"
    and     wp3:    "wellformed_policy3Pr p"  
    and     DA:     "DenyAll \<notin> set p" 
    and     mr:     "applied_rule_rev Cp x p = Some (DenyAllFromTo a b)"
    and     rinp:   "r \<in> set p"
    and     xindom: "x \<in> dom (Cp r)"
  shows  "r = DenyAllFromTo a b"
proof (cases r)
  case DenyAll thus ?thesis using DenyAll assms by simp 
next
  case (DenyAllFromTo c d) thus ?thesis 
    using assms apply simp
    apply (erule_tac x = x and p = p and v = "(DenyAllFromTo a b)" and
        u = "(DenyAllFromTo c d)"  in NetsEq_if_sameP_DD, simp_all)
     apply (erule mrSet)
    by (erule mr_in_dom) 
next
  case (AllowPortFromTo c d e) thus ?thesis 
    using assms apply simp
    apply (subgoal_tac "x \<notin> dom (Cp  (AllowPortFromTo c d e))", simp)
    by (rule_tac p = p in rule_charn3, auto intro: SCnotConc) 
next
  case (Conc a b) thus ?thesis 
    using assms apply simp 
    by (metis Conc aux0_0) 
qed

lemma foo31a: 
   "(\<forall> r. r \<in> set p \<and> x \<in> dom (Cp r) \<longrightarrow>
           (r = AllowPortFromTo a b po \<or> r = DenyAllFromTo a b \<or> r = DenyAll)) \<Longrightarrow>
    set p = set s \<Longrightarrow>  r \<in> set s  \<Longrightarrow> x \<in> dom (Cp r) \<Longrightarrow>
           (r = AllowPortFromTo a b po \<or> r = DenyAllFromTo a b \<or> r = DenyAll)"
  by auto

lemma aux4[rule_format]: 
  "applied_rule_rev Cp x (a#p) = Some a \<longrightarrow> a \<notin> set (p) \<longrightarrow> applied_rule_rev Cp x p = None"
  by (rule rev_induct, simp_all) (intro impI,simp add: applied_rule_rev_def split: if_splits)

lemma mrDA_tl: 
  assumes mr_DA: "applied_rule_rev Cp x p = Some DenyAll"
    and     wp1n:  "wellformed_policy1_strong p"
  shows          "applied_rule_rev Cp x (tl p) = None"
  apply (rule aux4 [where a = DenyAll])
   apply (metis wp1n_tl mr_DA wp1n)
  by (metis WP1n_DA_notinSet wp1n)

lemma rule_charnDAFT: 
  "wellformed_policy1_strong p \<Longrightarrow> allNetsDistinct p \<Longrightarrow> singleCombinators p \<Longrightarrow> 
   wellformed_policy3Pr p \<Longrightarrow> applied_rule_rev Cp x p = Some (DenyAllFromTo a b) \<Longrightarrow>
   r \<in> set (tl p) \<Longrightarrow> x \<in> dom (Cp r) \<Longrightarrow> 
   r = DenyAllFromTo a b"
  apply (subgoal_tac "p = DenyAll#(tl p)")
   apply (metis (no_types, lifting) ANDConc Combinators.distinct(1) NormalisationIPPProofs.mrConcEnd 
      NormalisationIPPProofs.rule_charn4 NormalisationIPPProofs.wp3Conc WP1n_DA_notinSet 
      singleCombinatorsConc waux2)
  using wp1n_tl by auto

lemma mrDenyAll_is_unique: 
  "wellformed_policy1_strong p \<Longrightarrow> applied_rule_rev Cp x p = Some DenyAll \<Longrightarrow> r \<in> set (tl p) \<Longrightarrow> 
  x \<notin> dom (Cp r)"
  apply (rule_tac a = "[]" and b = "DenyAll" and c = "tl p"  in foo3a, simp_all)  
   apply (metis wp1n_tl)
  by (metis WP1n_DA_notinSet)

theorem  C_eq_Sets_mr: 
  assumes sets_eq: "set p = set s"
    and     SC:      "singleCombinators p"
    and     wp1_p:   "wellformed_policy1_strong p"
    and     wp1_s:   "wellformed_policy1_strong s"
    and     wp3_p:   "wellformed_policy3Pr p"       
    and     wp3_s:   "wellformed_policy3Pr s"  
    and     aND:     "allNetsDistinct p"          
  shows            "applied_rule_rev Cp x p = applied_rule_rev Cp x s"
proof (cases "applied_rule_rev Cp x p")
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
    {
      case DenyAll
      have mr_p_is_DenyAll: "applied_rule_rev Cp x p = Some DenyAll"
        by (simp add: DenyAll Some)
      hence x_notin_tl_p: "\<forall> r. r \<in> set (tl p) \<longrightarrow>  x \<notin> dom (Cp r)" using wp1_p
        by (auto simp: mrDenyAll_is_unique)
      hence x_notin_tl_s: "\<forall> r. r \<in> set (tl s) \<longrightarrow>  x \<notin> dom (Cp r)" using tl_eq
        by auto
      hence mr_s_is_DenyAll: "applied_rule_rev Cp x s = Some DenyAll" using tl_s
        by (auto simp: mr_first)
      thus ?thesis using mr_p_is_DenyAll by simp
    next
      case (DenyAllFromTo a b) 
      have mr_p_is_DAFT: "applied_rule_rev Cp x p = Some (DenyAllFromTo a b)"
        by (simp add: DenyAllFromTo Some)
      have DA_notin_tl: "DenyAll \<notin> set (tl p)"
        by (metis WP1n_DA_notinSet wp1_p)
      have mr_tl_p: "applied_rule_rev Cp x p = applied_rule_rev Cp x (tl p)"
        by (metis Combinators.simps(4) DenyAllFromTo Some mrConcEnd tl_p)
      have dom_tl_p: "\<And> r. r \<in> set (tl p) \<and> x \<in> dom (Cp r) \<Longrightarrow> 
                        r = (DenyAllFromTo a b)"
        using wp1_p aND SC wp3_p mr_p_is_DAFT
        by (auto simp: rule_charnDAFT)
      hence dom_tl_s: "\<And> r. r \<in> set (tl s) \<and> x \<in> dom (Cp r) \<Longrightarrow> 
                         r = (DenyAllFromTo a b)"
        using tl_eq  by auto
      have DAFT_in_tl_s: "DenyAllFromTo a b \<in> set (tl s)" using mr_tl_p
        by (metis DenyAllFromTo mrSet mr_p_is_DAFT tl_eq)
      have x_in_dom_DAFT: "x \<in> dom (Cp (DenyAllFromTo a b))"
        by (metis mr_p_is_DAFT DenyAllFromTo mr_in_dom)
      hence mr_tl_s_is_DAFT: "applied_rule_rev Cp x (tl s) = Some (DenyAllFromTo a b)"
        using DAFT_in_tl_s dom_tl_s  by (metis mr_charn)
      hence mr_s_is_DAFT: "applied_rule_rev Cp x s = Some (DenyAllFromTo a b)"
        using tl_s
        by (metis  DA_notin_tl DenyAllFromTo EX_MR mrDA_tl 
            not_Some_eq tl_eq wellformed_policy1_strong.simps(2))
      thus ?thesis using mr_p_is_DAFT by simp
    next
      case (AllowPortFromTo a b c)
      have wp1s: "wellformed_policy1 s" by (metis wp1_eq wp1_s)
      have mr_p_is_A: "applied_rule_rev Cp x p = Some (AllowPortFromTo a b c)"
        by (simp add: AllowPortFromTo Some)
      hence A_in_s: "AllowPortFromTo a b c \<in> set s" using sets_eq
        by (auto intro: mrSet)
      have x_in_dom_A: "x \<in> dom (Cp (AllowPortFromTo a b c))"
        by (metis mr_p_is_A AllowPortFromTo mr_in_dom)
      have SCs: "singleCombinators s" using SC sets_eq
        by (auto intro: SCSubset)
      hence ANDs: "allNetsDistinct s" using aND sets_eq SC
        by (auto intro: aNDSetsEq)
      hence mr_s_is_A: "applied_rule_rev Cp x s = Some (AllowPortFromTo a b c)"
        using A_in_s wp1s mr_p_is_A aND SCs wp3_s x_in_dom_A
        by (simp add: rule_charn2)
      thus ?thesis using mr_p_is_A by simp
    }
  next
    case (Conc a b) thus ?thesis by (metis Some mr_not_Conc SC) 
  qed 
qed

lemma C_eq_Sets: 
"singleCombinators p \<Longrightarrow> wellformed_policy1_strong p \<Longrightarrow> wellformed_policy1_strong s \<Longrightarrow>
 wellformed_policy3Pr p \<Longrightarrow> wellformed_policy3Pr s \<Longrightarrow> allNetsDistinct p \<Longrightarrow> set p = set s \<Longrightarrow>
 Cp (list2FWpolicy p) x  = Cp (list2FWpolicy s) x"
  by (metis C_eq_Sets_mr C_eq_if_mr_eq  wellformed_policy1_strong.simps(1))

lemma C_eq_sorted: 
  "distinct p \<Longrightarrow> all_in_list p l \<Longrightarrow> singleCombinators p \<Longrightarrow>
   wellformed_policy1_strong p\<Longrightarrow> wellformed_policy3Pr p\<Longrightarrow> allNetsDistinct p \<Longrightarrow>
   Cp (list2FWpolicy (sort p l))= Cp (list2FWpolicy p)"
  by (rule ext)
    (meson distinct_sort set_sort C_eq_Sets wellformed2_sorted wellformed_policy3_charn SC3 aND_sort 
      wellformed1_alternative_sorted wp1_eq)
    
lemma C_eq_sortedQ: 
  "distinct p \<Longrightarrow> all_in_list p l \<Longrightarrow> singleCombinators p \<Longrightarrow> 
   wellformed_policy1_strong p \<Longrightarrow>  wellformed_policy3Pr p \<Longrightarrow> allNetsDistinct p \<Longrightarrow>
   Cp (list2FWpolicy (qsort p l))= Cp (list2FWpolicy p)"
  by (rule ext)
    (metis C_eq_Sets wellformed2_sortedQ wellformed_policy3_charn SC3Q aND_sortQ distinct_sortQ 
      set_sortQ wellformed1_sorted_auxQ wellformed_eq wp1_aux1aa)

lemma C_eq_RS2_mr: "applied_rule_rev Cp x (removeShadowRules2 p)= applied_rule_rev Cp x p"
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
      case (DenyAllFromTo a b) thus ?thesis by (simp, metis Cons DenyAllFromTo mreq_end2)
    next
      case (AllowPortFromTo a b p) thus ?thesis
      proof (cases "DenyAllFromTo a b \<in> set ys")
        case True thus ?thesis using AllowPortFromTo Cons
          apply (cases "applied_rule_rev Cp x ys = None", simp_all)
           apply (subgoal_tac "x \<notin> dom (Cp (AllowPortFromTo a b p))")
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
  "p \<noteq> [] \<longrightarrow> applied_rule_rev Cp x p = None \<longrightarrow>  Cp (list2FWpolicy p) x = None"
  unfolding applied_rule_rev_def
proof(induct rule: rev_induct)
  case Nil show ?case by simp
next
  case (snoc xa xs) show ?case
    apply (insert snoc.hyps, intro impI, simp)
    apply (case_tac "xs \<noteq> []")
     apply (metis CConcStart2 option.simps(3))
    by (metis append_Nil domIff l2p_aux2 option.distinct(1))
qed    
  
lemma C_eq_None2:
  "a \<noteq> []  \<Longrightarrow> b \<noteq> [] \<Longrightarrow>  applied_rule_rev Cp x a = None  \<Longrightarrow>  applied_rule_rev Cp x b = None \<Longrightarrow>
  (Cp (list2FWpolicy a)) x = (Cp (list2FWpolicy b)) x"
  by (auto simp: C_eq_None)
    
lemma C_eq_RS2: 
  "wellformed_policy1_strong p \<Longrightarrow> 
  Cp (list2FWpolicy (removeShadowRules2 p))= Cp (list2FWpolicy p)"
  apply (rule ext)
  by (metis C_eq_RS2_mr C_eq_if_mr_eq RS2_NMT wp1_alternative_not_mt)

lemma none_MT_rulesRS2: "none_MT_rules Cp p \<Longrightarrow> none_MT_rules Cp (removeShadowRules2 p)"
  by (auto simp: RS2Set none_MT_rulessubset)

lemma CconcNone: 
  "dom (Cp a) = {} \<Longrightarrow> p \<noteq> [] \<Longrightarrow> Cp (list2FWpolicy (a # p)) x = Cp (list2FWpolicy p) x"
  apply (case_tac "p = []", simp_all)
  apply (case_tac "x\<in> dom (Cp (list2FWpolicy(p)))")
   apply (metis Cdom2 list2FWpolicyconc)
  apply (metis Cp.simps(4) map_add_dom_app_simps(2) inSet_not_MT list2FWpolicyconc set_empty2)
  done

lemma none_MT_rulesrd[rule_format]: "none_MT_rules Cp p \<longrightarrow> none_MT_rules Cp (remdups p)"
  by (induct p, simp_all)
    
lemma DARS3[rule_format]:"DenyAll \<notin> set p\<longrightarrow>DenyAll \<notin> set (rm_MT_rules Cp p)"
  by (induct p, simp_all)
    
lemma DAnMT: "dom (Cp DenyAll) \<noteq> {}"
  by (simp add: dom_def Cp.simps PolicyCombinators.PolicyCombinators)
    
lemma DAnMT2: "Cp DenyAll \<noteq> Map.empty"
  by (metis DAAux dom_eq_empty_conv empty_iff) 

lemma wp1n_RS3[rule_format,simp]: 
  "wellformed_policy1_strong p \<longrightarrow>  wellformed_policy1_strong (rm_MT_rules Cp p)"
  apply (induct p, simp_all)
  apply (rule conjI| rule impI|simp)+
   apply (metis DAnMT)
  apply (metis DARS3) 
  done

lemma AILRS3[rule_format,simp]: 
  "all_in_list p l \<longrightarrow> all_in_list (rm_MT_rules Cp p) l"
  by (induct p, simp_all)
    
lemma SCRS3[rule_format,simp]: 
  "singleCombinators p \<longrightarrow> singleCombinators(rm_MT_rules Cp p)"
  apply (induct p, simp_all)
  subgoal for a p
    apply(case_tac "a", simp_all)
    done
  done
    
lemma RS3subset: "set (rm_MT_rules Cp p)  \<subseteq> set p "
  by (induct p, auto)
    
lemma ANDRS3[simp]: 
  "singleCombinators p \<Longrightarrow> allNetsDistinct p \<Longrightarrow> allNetsDistinct (rm_MT_rules Cp p)"
  by (rule_tac b = p in aNDSubset, simp_all add:RS3subset)
  
lemma nlpaux: "x \<notin> dom (Cp b) \<Longrightarrow> Cp (a \<oplus> b) x = Cp a x"
  by (metis Cp.simps(4) map_add_dom_app_simps(3))
    
lemma notindom[rule_format]: 
  "a \<in> set p \<longrightarrow>  x \<notin> dom (Cp (list2FWpolicy p)) \<longrightarrow> x \<notin> dom (Cp a)"
proof (induct p)
  case Nil show ?case by simp
next 
  case (Cons a p) then show ?case
    apply (simp_all,intro conjI impI)
     apply (metis CConcStartA)
    apply simp
    apply (metis Cdom2 List.set_simps(2) domIff insert_absorb list.simps(2) list2FWpolicyconc set_empty)
    done
qed      

lemma C_eq_rd[rule_format]: 
  "p \<noteq> [] \<Longrightarrow> Cp (list2FWpolicy (remdups p)) = Cp (list2FWpolicy p)"
proof (rule ext, induct p) 
  case Nil thus ?case by simp 
next
  case (Cons y ys) thus ?case
  proof (cases "ys = []")
    case True thus ?thesis by simp 
  next
    case False thus ?thesis 
      using Cons apply simp
      apply (intro conjI impI)
       apply (metis Cdom2 nlpaux notindom domIff l2p_aux)
      by (metis (no_types, lifting) Cdom2 nlpaux domIff l2p_aux remDupsNMT)   
  qed
qed
  
lemma nMT_domMT: 
  "\<not> not_MT Cp  p \<Longrightarrow> p \<noteq> [] \<Longrightarrow> r \<notin> dom (Cp (list2FWpolicy p))"
proof (induct p)
  case Nil thus ?case by simp 
next
  case (Cons x xs) thus ?case 
    apply (simp split: if_splits)
    apply (cases "xs = []",simp_all )
    by (metis CconcNone domIff)
qed
            
lemma C_eq_RS3_aux[rule_format]: 
  "not_MT Cp  p \<Longrightarrow>  Cp (list2FWpolicy p) x = Cp (list2FWpolicy (rm_MT_rules Cp p)) x"
proof (induct p)
  case Nil thus ?case by simp 
next
  case (Cons y ys) thus ?case
  proof (cases "not_MT Cp  ys")
    case True thus ?thesis 
      using Cons apply simp
      apply (intro conjI impI, simp)
       apply (metis CconcNone True not_MTimpnotMT)
      apply (cases "x \<in> dom (Cp (list2FWpolicy ys))")
       apply (subgoal_tac "x \<in> dom (Cp (list2FWpolicy (rm_MT_rules Cp ys)))")
        apply (metis (mono_tags) Cons_eq_appendI NMPrm CeqEnd append_Nil not_MTimpnotMT)
       apply (simp add: domIff)
      apply (subgoal_tac "x \<notin>  dom (Cp (list2FWpolicy (rm_MT_rules Cp ys)))") 
       apply (metis l2p_aux l2p_aux2 nlpaux)
      by (metis domIff)
  next 
    case False thus ?thesis 
      using Cons False
    proof (cases "ys = []") 
      case True thus ?thesis using Cons by (simp) (rule impI, simp) 
    next
      case False thus ?thesis 
        using Cons False \<open>\<not> not_MT Cp ys\<close> apply (simp)
        apply (intro conjI impI| simp)+
        apply (subgoal_tac "rm_MT_rules Cp ys = []")
         apply (subgoal_tac "x \<notin> dom (Cp (list2FWpolicy ys))") 
          apply simp_all 
          apply (metis l2p_aux nlpaux)    
         apply (erule nMT_domMT, simp_all)
        by (metis SR3nMT)
    qed
  qed
qed       

lemma C_eq_id: 
  "wellformed_policy1_strong p \<Longrightarrow> Cp(list2FWpolicy (insertDeny p)) = Cp (list2FWpolicy p)"
  by (rule ext) (metis insertDeny.simps(1) wp1n_tl)

lemma C_eq_RS3: 
  "not_MT Cp  p \<Longrightarrow>  Cp(list2FWpolicy (rm_MT_rules Cp p)) = Cp (list2FWpolicy p)"
  by (rule ext) (erule C_eq_RS3_aux[symmetric])

lemma NMPrd[rule_format]: "not_MT Cp  p \<longrightarrow> not_MT Cp  (remdups p)"
  by (induct p, simp_all) (auto simp: NMPcharn)

lemma NMPDA[rule_format]: "DenyAll \<in> set p \<longrightarrow> not_MT Cp  p"
  by (induct p, simp_all add: DAnMT)

lemma NMPiD[rule_format]: "not_MT Cp  (insertDeny p)"
  by (insert DAiniD [of p]) (erule NMPDA)

lemma list2FWpolicy2list[rule_format]: 
  "Cp (list2FWpolicy(policy2list p)) = (Cp p)"
  apply (rule ext)
  apply (induct_tac p, simp_all)
  subgoal for x x1 x2
    apply (case_tac "x \<in> dom (Cp (x2))") 
     apply (metis Cdom2 CeqEnd domIff p2lNmt)
    apply (metis CeqStart domIff p2lNmt nlpaux)
    done
  done
    
lemmas C_eq_Lemmas = none_MT_rulesRS2 none_MT_rulesrd  SCp2l wp1n_RS2  wp1ID NMPiD waux2
                     wp1alternative_RS1 p2lNmt list2FWpolicy2list wellformed_policy3_charn  wp1_eq

lemmas C_eq_subst_Lemmas = C_eq_sorted C_eq_sortedQ C_eq_RS2 C_eq_rd C_eq_RS3 C_eq_id 

lemma C_eq_All_untilSorted: 
  "DenyAll\<in>set(policy2list p) \<Longrightarrow> all_in_list(policy2list p) l \<Longrightarrow> allNetsDistinct(policy2list p) \<Longrightarrow>
    Cp(list2FWpolicy (sort (removeShadowRules2 (remdups (rm_MT_rules Cp (insertDeny 
                           (removeShadowRules1 (policy2list p)))))) l)) = 
    Cp p"
  apply (subst C_eq_sorted,simp_all add: C_eq_Lemmas)
  apply (subst C_eq_RS2,simp_all add: C_eq_Lemmas) 
  apply (subst C_eq_rd,simp_all add: C_eq_Lemmas)
  apply (subst C_eq_RS3,simp_all add: C_eq_Lemmas)
  apply (subst C_eq_id,simp_all add: C_eq_Lemmas)
  done

lemma C_eq_All_untilSortedQ: 
  "DenyAll\<in> set(policy2list p) \<Longrightarrow> all_in_list(policy2list p) l \<Longrightarrow> allNetsDistinct(policy2list p) \<Longrightarrow>
    Cp(list2FWpolicy (qsort (removeShadowRules2 (remdups (rm_MT_rules Cp (insertDeny 
                            (removeShadowRules1 (policy2list p)))))) l)) = 
    Cp p"
  apply (subst C_eq_sortedQ,simp_all add: C_eq_Lemmas)
  apply (subst C_eq_RS2,simp_all add: C_eq_Lemmas) 
  apply (subst C_eq_rd,simp_all add: C_eq_Lemmas)
  apply (subst C_eq_RS3,simp_all add: C_eq_Lemmas)
  apply (subst C_eq_id,simp_all add: C_eq_Lemmas)
  done

lemma C_eq_All_untilSorted_withSimps: 
  "DenyAll \<in> set (policy2list p) \<Longrightarrow>  all_in_list (policy2list p) l \<Longrightarrow>
 allNetsDistinct (policy2list p) \<Longrightarrow>
 Cp(list2FWpolicy(sort(removeShadowRules2(remdups(rm_MT_rules Cp (insertDeny
                      (removeShadowRules1(policy2list p)))))) l)) = 
 Cp p"
  by (simp_all add: C_eq_Lemmas C_eq_subst_Lemmas)
    
lemma C_eq_All_untilSorted_withSimpsQ: 
  "DenyAll \<in> set (policy2list p) \<Longrightarrow>  all_in_list (policy2list p) l \<Longrightarrow>
 allNetsDistinct (policy2list p) \<Longrightarrow>
 Cp(list2FWpolicy(qsort(removeShadowRules2(remdups(rm_MT_rules Cp (insertDeny
                       (removeShadowRules1  (policy2list p)))))) l)) = 
 Cp p"
  by (simp_all add: C_eq_Lemmas C_eq_subst_Lemmas)

lemma InDomConc[rule_format]: "p \<noteq> [] \<longrightarrow> x \<in> dom (Cp (list2FWpolicy (p))) \<longrightarrow>
                               x \<in>  dom (Cp (list2FWpolicy (a#p)))"
  apply (induct p, simp_all)
  subgoal for a p
    apply(case_tac "p = []",simp_all add: dom_def Cp.simps)
    done
  done
    
lemma not_in_member[rule_format]: "member a b \<longrightarrow> x \<notin> dom (Cp b) \<longrightarrow> x \<notin> dom (Cp a)"
  by (induct b)(simp_all add: dom_def Cp.simps)

lemma src_in_sdnets[rule_format]: 
  "\<not> member DenyAll x \<longrightarrow> p \<in> dom (Cp x) \<longrightarrow> subnetsOfAdr (src p) \<inter> (fst_set (sdnets x)) \<noteq> {}"
  apply (induct rule: Combinators.induct)
     apply (simp_all add: fst_set_def subnetsOfAdr_def PLemmas, rename_tac x1 x2)
  apply (intro impI)
  apply (simp add: fst_set_def)
  subgoal for x1 x2
    apply (case_tac "p \<in> dom (Cp x2)")
     apply (rule subnetAux)
      apply (auto simp: PLemmas)
    done
  done
    
lemma dest_in_sdnets[rule_format]: 
  "\<not> member DenyAll x \<longrightarrow> p \<in> dom (Cp x) \<longrightarrow> subnetsOfAdr (dest p) \<inter> (snd_set (sdnets x)) \<noteq> {}"
  apply (induct rule: Combinators.induct)
     apply (simp_all add: snd_set_def subnetsOfAdr_def PLemmas, rename_tac x1 x2)
  apply (intro impI,simp add: snd_set_def)
  subgoal for x1 x2
    apply (case_tac "p \<in> dom (Cp x2)")
     apply (rule subnetAux)
      apply (auto simp: PLemmas)
    done
  done

lemma sdnets_in_subnets[rule_format]: 
  "p\<in> dom (Cp x) \<longrightarrow> \<not> member DenyAll x \<longrightarrow>
   (\<exists> (a,b)\<in>sdnets x. a \<in> subnetsOfAdr (src p) \<and> b \<in> subnetsOfAdr (dest p))"
  apply (rule Combinators.induct)
     apply (simp_all add: PLemmas subnetsOfAdr_def)
  apply (intro impI, simp)
  subgoal for x1 x2
    apply (case_tac "p \<in> dom (Cp (x2))")
     apply (auto simp: PLemmas subnetsOfAdr_def)
    done
  done

lemma disjSD_no_p_in_both[rule_format]:   
  "\<lbrakk>disjSD_2 x y; \<not> member DenyAll x; \<not> member DenyAll y;  
   p \<in> dom (Cp x); p \<in> dom (Cp y)\<rbrakk> \<Longrightarrow> False"
  apply (rule_tac A = "sdnets x" and B = "sdnets y" and D = "src p" and F = "dest p" in tndFalse)
  by (auto simp: dest_in_sdnets src_in_sdnets sdnets_in_subnets disjSD_2_def)

lemma list2FWpolicy_eq: 
  "zs \<noteq> [] \<Longrightarrow> Cp (list2FWpolicy (x \<oplus> y # z)) p = Cp (x \<oplus> list2FWpolicy (y # z)) p"
  by (metis ConcAssoc l2p_aux list2FWpolicy.simps(2))

lemma dom_sep[rule_format]: 
  "x \<in> dom (Cp (list2FWpolicy p)) \<longrightarrow> x \<in> dom (Cp (list2FWpolicy(separate p)))"
proof (induct p rule: separate.induct,simp_all, goal_cases)
  case (1 v va y z) then show ?case
    apply (intro conjI impI)
     apply (simp,drule mp)
      apply (case_tac "x \<in> dom (Cp (DenyAllFromTo v va))")
       apply (metis CConcStartA domIff l2p_aux2 list2FWpolicyconc not_Cons_self )
      apply (subgoal_tac "x \<in> dom (Cp (list2FWpolicy (y #z)))")
       apply (metis CConcStartA Cdom2 domIff l2p_aux2 list2FWpolicyconc nlpaux)
      apply (subgoal_tac "x \<in> dom (Cp (list2FWpolicy ((DenyAllFromTo v va)#y#z)))")
       apply (simp add: dom_def Cp.simps,simp_all)
    apply (case_tac "x \<in> dom (Cp (DenyAllFromTo v va))", simp_all)
    apply (subgoal_tac "x \<in> dom (Cp (list2FWpolicy (y #z)))")
     apply (metis InDomConc sepnMT list.simps(2))
    apply (subgoal_tac "x \<in> dom (Cp (list2FWpolicy ((DenyAllFromTo v va)#y#z)))")
    by (simp_all add: dom_def Cp.simps)
next 
  case (2 v va vb y z) then show ?case 
    apply (intro impI conjI,simp)
     apply (case_tac "x \<in> dom (Cp (AllowPortFromTo v va vb))")
      apply (metis CConcStartA domIff  l2p_aux2 list2FWpolicyconc not_Cons_self )
     apply (subgoal_tac "x \<in> dom (Cp (list2FWpolicy (y #z)))")
      apply (metis CConcStartA Cdom2 InDomConc domIff l2p_aux2 list2FWpolicyconc nlpaux)
     apply (simp add: dom_def Cp.simps, simp_all)
    apply (case_tac "x \<in> dom (Cp (AllowPortFromTo v va vb))", simp_all) 
    apply (subgoal_tac "x \<in> dom (Cp (list2FWpolicy (y #z)))",simp)
     apply (metis Conc_not_MT InDomConc sepnMT)
    apply (metis domIff nlpaux)
    done
next
  case (3 v va y z) then show ?case 
    apply (intro conjI impI,simp)
     apply (drule mp)
      apply (case_tac "x \<in> dom (Cp ((v \<oplus> va)))")
       apply (metis Cp.simps(4) CConcStartA ConcAssoc domIff list2FWpolicy2list list2FWpolicyconc p2lNmt)
      defer 1
      apply simp_all
     apply (case_tac "x \<in> dom (Cp ((v \<oplus> va)))",simp_all)
     apply (drule mp)
      apply (simp add: Cp.simps dom_def)
     apply (metis InDomConc list.simps(2)sepnMT)
    apply (subgoal_tac "x \<in> dom (Cp (list2FWpolicy (y#z)))")
     apply (case_tac "x \<in> dom (Cp y)",simp_all)
      apply (metis CConcStartA Cdom2 ConcAssoc domIff)
     apply (metis InDomConc domIff l2p_aux2 list2FWpolicyconc nlpaux)
    apply (case_tac "x \<in> dom (Cp y)",simp_all)
    by (metis domIff nlpaux)
qed
  
lemma domdConcStart[rule_format]: 
  "x \<in> dom (Cp (list2FWpolicy (a#b))) \<longrightarrow> x \<notin> dom (Cp (list2FWpolicy b)) \<longrightarrow> x \<in> dom (Cp (a))"
  by (induct b, simp_all) (auto simp: PLemmas)
    
lemma sep_dom2_aux: 
  "x \<in> dom (Cp (list2FWpolicy (a \<oplus> y # z))) \<Longrightarrow> x \<in> dom (Cp (a \<oplus> list2FWpolicy (y # z)))"
  by auto (metis list2FWpolicy_eq p2lNmt)
    
lemma sep_dom2_aux2: 
  "(x \<in> dom (Cp (list2FWpolicy (separate (y # z)))) \<longrightarrow> x \<in> dom (Cp (list2FWpolicy (y # z)))) \<Longrightarrow>
  x \<in> dom (Cp (list2FWpolicy (a # separate (y # z)))) \<Longrightarrow> 
  x \<in> dom (Cp (list2FWpolicy (a \<oplus> y # z)))"
  by (metis CConcStartA InDomConc domdConcStart list.simps(2) list2FWpolicy.simps(2) list2FWpolicyconc)
    
lemma sep_dom2[rule_format]: 
  "x \<in> dom (Cp (list2FWpolicy (separate p))) \<longrightarrow> x \<in> dom (Cp (list2FWpolicy( p)))"
  by (rule separate.induct) (simp_all add: sep_dom2_aux sep_dom2_aux2)
    
lemma sepDom: "dom (Cp (list2FWpolicy p)) = dom (Cp (list2FWpolicy (separate p)))"
  by (rule equalityI) (rule subsetI, (erule dom_sep|erule sep_dom2))+

lemma C_eq_s_ext[rule_format]: 
  "p \<noteq> [] \<longrightarrow> Cp (list2FWpolicy (separate p)) a  = Cp (list2FWpolicy p) a "
proof (induct rule: separate.induct, goal_cases) 
  case (1 x) thus ?case 
    apply (cases "x = []",simp_all)
    apply (cases "a \<in> dom (Cp (list2FWpolicy x))")
     apply (subgoal_tac "a \<in> dom (Cp (list2FWpolicy (separate x)))")
      apply (metis Cdom2 list2FWpolicyconc sepDom sepnMT)
     apply (metis sepDom)
    by (metis nlpaux sepDom list2FWpolicyconc sepnMT)
next
  case (2 v va y z) thus ?case 
    apply (cases "z = []",simp_all)
     apply (intro conjI impI|simp)+
     apply (simp add: PLemmas(8) UPFDefs(8) list2FWpolicyconc sepnMT)
    by (metis (mono_tags, lifting) Conc_not_MT Cdom2 list2FWpolicy_eq nlpaux sepDom l2p_aux sepnMT)
next
  case (3 v va vb y z) thus ?case
    apply (cases "z = []", simp_all)
     apply (simp add: PLemmas(8) UPFDefs(8) list2FWpolicyconc sepnMT)
    by (metis (no_types, hide_lams) Conc_not_MT Cdom2  nlpaux domIff l2p_aux sepnMT)
next
  case (4 v va y z) thus ?case
    apply (cases "z = []", simp_all)
     apply (simp add: PLemmas(8) UPFDefs(8) l2p_aux sepnMT)
    by (metis (no_types, lifting) ConcAssoc PLemmas(8) UPFDefs(8) list.distinct(1) 
        list2FWpolicyconc sepnMT) 
next
  case 5 thus ?case by simp 
next
  case 6 thus ?case by simp 
next
  case 7 thus ?case by simp 
next
  case 8 thus ?case by simp
qed

lemma C_eq_s: "p \<noteq> [] \<Longrightarrow> Cp (list2FWpolicy (separate p)) = Cp (list2FWpolicy p)"
  by (rule ext) (simp add: C_eq_s_ext)

lemmas sortnMTQ = NormalisationIntegerPortProof.C_eq_Lemmas_sep(14)
lemmas C_eq_Lemmas_sep = C_eq_Lemmas sortnMT sortnMTQ RS2_NMT NMPrd not_MTimpnotMT 

lemma C_eq_until_separated:
  "DenyAll\<in>set(policy2list p) \<Longrightarrow> all_in_list(policy2list p) l \<Longrightarrow> allNetsDistinct(policy2list p) \<Longrightarrow>
 Cp (list2FWpolicy (separate (sort (removeShadowRules2 (remdups (rm_MT_rules Cp
            (insertDeny (removeShadowRules1 (policy2list p)))))) l))) = 
 Cp p"
  by (simp add: C_eq_All_untilSorted_withSimps C_eq_s wellformed1_alternative_sorted wp1ID wp1n_RS2)

lemma C_eq_until_separatedQ:
  "DenyAll \<in> set (policy2list p) \<Longrightarrow> all_in_list (policy2list p) l \<Longrightarrow>
   allNetsDistinct (policy2list p) \<Longrightarrow>
     Cp(list2FWpolicy(separate(qsort(
           removeShadowRules2(remdups (rm_MT_rules Cp
                 (insertDeny (removeShadowRules1 (policy2list p)))))) l))) = 
     Cp p"
  by (simp add: C_eq_All_untilSorted_withSimpsQ C_eq_s setnMT wp1ID wp1n_RS2)

lemma domID[rule_format]: 
  "p \<noteq> [] \<and> x \<in> dom(Cp(list2FWpolicy p)) \<longrightarrow> x \<in> dom (Cp(list2FWpolicy(insertDenies p)))"
proof(induct p)
  case Nil then show ?case by simp
next 
  case (Cons a p) then show ?case
  proof(cases "p=[]", goal_cases)
    case 1 then show ?case
      apply(simp) apply(rule impI)
      apply (cases a, simp_all)
        apply (simp_all add: Cp.simps dom_def)+ 
      by auto
  next
    case 2 then show ?case
    proof(cases "x \<in> dom(Cp(list2FWpolicy p))", goal_cases)
      case 1 then show ?case
        apply simp apply (rule impI)
        apply (cases a, simp_all)
          apply (metis InDomConc idNMT)
         apply (rule InDomConc, simp_all add: idNMT)+
        done
    next 
      case 2 then show ?case  
        apply simp apply (rule impI)
      proof(cases "x \<in> dom (Cp (list2FWpolicy (insertDenies p)))", goal_cases)
        case 1 then show ?case
        proof(induct a)
          case DenyAll then show ?case by simp
        next               
          case (DenyAllFromTo src dest) then show ?case
            by simp (rule InDomConc, simp add: idNMT)
        next  
          case (AllowPortFromTo src dest port) then show ?case
            by simp (rule InDomConc, simp  add: idNMT)
        next 
          case (Conc _ _) then show ?case
            by simp(rule InDomConc, simp add: idNMT)
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
            by simp (metis CConcStartA Cdom2 Conc(5) ConcAssoc domIff domdConcStart) 
        qed
      qed
    qed
  qed
qed
  
lemma DA_is_deny: 
  "x \<in> dom (Cp (DenyAllFromTo a b \<oplus> DenyAllFromTo b a \<oplus> DenyAllFromTo a b)) \<Longrightarrow>
Cp (DenyAllFromTo a b\<oplus>DenyAllFromTo b a \<oplus> DenyAllFromTo a b) x = Some (deny ())"
  by (case_tac "x \<in> dom (Cp (DenyAllFromTo a b))") (simp_all add: PLemmas split: if_splits)

lemma iDdomAux[rule_format]: 
  "p \<noteq> [] \<longrightarrow> x \<notin> dom (Cp (list2FWpolicy p)) \<longrightarrow> 
   x \<in> dom (Cp (list2FWpolicy (insertDenies p))) \<longrightarrow>
   Cp (list2FWpolicy (insertDenies p)) x = Some (deny ())"
proof (induct p)
  case Nil thus ?case by simp
next
  case (Cons y ys) thus ?case
  proof (cases y) 
    case DenyAll then show ?thesis by simp 
  next
    case (DenyAllFromTo a b) then show ?thesis 
      using DenyAllFromTo Cons apply simp
      apply (rule impI)+
    proof (cases "ys = []", goal_cases)
      case 1 then show ?case by (simp add: DA_is_deny) 
    next
      case 2 then show ?case
        apply simp
        apply (drule mp)
         apply (metis DenyAllFromTo InDomConc )
        apply (cases "x \<in> dom (Cp (list2FWpolicy (insertDenies ys)))",simp_all)
         apply (metis Cdom2 DenyAllFromTo  idNMT list2FWpolicyconc)
        apply (subgoal_tac "Cp (list2FWpolicy (DenyAllFromTo a b \<oplus>
                                    DenyAllFromTo b a \<oplus> DenyAllFromTo a b#insertDenies ys)) x =
                                Cp ((DenyAllFromTo a b \<oplus> DenyAllFromTo b a \<oplus> DenyAllFromTo a b)) x ")
         apply (metis DA_is_deny DenyAllFromTo domdConcStart)
        apply (metis DenyAllFromTo l2p_aux2 list2FWpolicyconc nlpaux)
        done 
    qed
  next
    case (AllowPortFromTo a b c) then show ?thesis using Cons AllowPortFromTo
    proof (cases "ys = []", goal_cases)
      case 1 then show ?case 
        apply (simp,intro impI)
        apply (subgoal_tac "x \<in> dom (Cp (DenyAllFromTo a b \<oplus> DenyAllFromTo b a))")
         apply (auto simp: PLemmas split: if_splits) 
        done 
    next
      case 2 then show ?case
        apply (simp, intro impI)
        apply (drule mp)
         apply (metis AllowPortFromTo InDomConc)
        apply (cases "x \<in> dom (Cp (list2FWpolicy (insertDenies ys)))",simp_all)
         apply (metis AllowPortFromTo Cdom2 idNMT list2FWpolicyconc)
        apply (subgoal_tac "Cp (list2FWpolicy (DenyAllFromTo a b \<oplus>
                                                    DenyAllFromTo b a \<oplus> 
                                                    AllowPortFromTo a b c#insertDenies ys)) x =
                                 Cp ((DenyAllFromTo a b \<oplus> DenyAllFromTo b a)) x ")
         apply (auto simp: PLemmas split: if_splits)[1] 
        by (metis AllowPortFromTo CConcStartA ConcAssoc idNMT list2FWpolicyconc nlpaux)
    qed
  next
    case (Conc a b) then show ?thesis
    proof (cases "ys = []", goal_cases)
      case 1 then show ?case 
        apply(simp,intro impI)
        apply (subgoal_tac "x \<in> dom (Cp (DenyAllFromTo (first_srcNet a) (first_destNet a) \<oplus> 
                                             DenyAllFromTo (first_destNet a) (first_srcNet a)))")
        by (auto simp: PLemmas split: if_splits) 
    next
      case 2 then show ?case
        apply(simp,intro impI)
        apply(cases "x \<in> dom (Cp (list2FWpolicy (insertDenies ys)))")
         apply (metis Cdom2 Conc Cons InDomConc idNMT list2FWpolicyconc)
        apply (subgoal_tac "Cp (list2FWpolicy(DenyAllFromTo (first_srcNet a)(first_destNet a) \<oplus> 
                                                   DenyAllFromTo (first_destNet a) (first_srcNet a)\<oplus> 
                                                   a \<oplus> b#insertDenies ys)) x =
                                 Cp ((DenyAllFromTo(first_srcNet a)  (first_destNet a) \<oplus>
                                      DenyAllFromTo (first_destNet a)(first_srcNet  a) \<oplus> a \<oplus> b)) x")
         apply simp
         defer 1 
         apply (metis Conc l2p_aux2 list2FWpolicyconc nlpaux)
        apply (subgoal_tac "Cp((DenyAllFromTo(first_srcNet a)(first_destNet a) \<oplus> 
                                     DenyAllFromTo (first_destNet a)(first_srcNet a)\<oplus> a \<oplus> b)) x = 
                                 Cp((DenyAllFromTo (first_srcNet a)(first_destNet a)\<oplus> 
                                     DenyAllFromTo (first_destNet a)  (first_srcNet a))) x ")
         apply simp
         defer 1 
         apply (metis CConcStartA Conc ConcAssoc nlpaux)
        by (auto simp: PLemmas split: if_splits) 
    qed
  qed
qed         

lemma iD_isD[rule_format]: 
  "p \<noteq> [] \<longrightarrow> x \<notin> dom (Cp (list2FWpolicy p)) \<longrightarrow> 
   Cp (DenyAll \<oplus> list2FWpolicy (insertDenies p)) x = Cp DenyAll x"
  apply (case_tac "x \<in> dom (Cp (list2FWpolicy (insertDenies p)))")
   apply (simp add: Cp.simps(1) Cdom2 iDdomAux deny_all_def)
  using NormalisationIPPProofs.nlpaux 
  by blast

lemma inDomConc:
  "x\<notin>dom (Cp a) \<Longrightarrow> x\<notin>dom (Cp (list2FWpolicy p)) \<Longrightarrow> x \<notin> dom (Cp (list2FWpolicy(a#p)))"
  by (metis domdConcStart)

lemma domsdisj[rule_format]: 
  "p \<noteq> [] \<longrightarrow> (\<forall> x s. s \<in> set p \<and> x \<in> dom (Cp A) \<longrightarrow>  x \<notin> dom (Cp s)) \<longrightarrow> y \<in> dom (Cp A) \<longrightarrow>
   y \<notin> dom (Cp (list2FWpolicy p))"
proof (induct p)
  case Nil show ?case by simp
next
  case (Cons a p) show ?case    
    apply (case_tac "p = []", simp)
     apply (rule_tac x = y in spec)
     apply (simp add: split_tupled_all)
    by (metis Cons.hyps inDomConc list.set_intros(1) list.set_intros(2))
qed
  
lemma isSepaux:
  "p \<noteq> [] \<Longrightarrow> noDenyAll (a#p) \<Longrightarrow> separated (a # p) \<Longrightarrow>
   x \<in> dom (Cp (DenyAllFromTo (first_srcNet a)  (first_destNet a) \<oplus>
                DenyAllFromTo (first_destNet a) (first_srcNet a)  \<oplus> a)) \<Longrightarrow>
   x \<notin> dom (Cp (list2FWpolicy p))"
  apply (rule_tac A = "(DenyAllFromTo (first_srcNet  a) (first_destNet a) \<oplus>
                      DenyAllFromTo (first_destNet a) (first_srcNet  a) \<oplus> a)" in domsdisj, simp_all)
  apply (rule notI)
  subgoal for xa s
    apply (rule_tac p = xa and x ="(DenyAllFromTo (first_srcNet a) (first_destNet a) \<oplus>
                               DenyAllFromTo (first_destNet a) (first_srcNet  a) \<oplus> a)" 
        and y = s in disjSD_no_p_in_both, simp_all)
    using disjSD2aux noDA apply blast
    using noDA 
    by blast
  done
    
lemma none_MT_rulessep[rule_format]: "none_MT_rules Cp p \<longrightarrow> none_MT_rules Cp (separate p)"
  by (induct p rule: separate.induct) (simp_all add: Cp.simps map_add_le_mapE map_le_antisym)
    
lemma dom_id: 
  "noDenyAll (a#p) \<Longrightarrow> separated (a#p) \<Longrightarrow> p \<noteq> [] \<Longrightarrow>
   x \<notin> dom (Cp (list2FWpolicy p)) \<Longrightarrow> x \<in> dom (Cp (a)) \<Longrightarrow> 
   x \<notin> dom (Cp (list2FWpolicy (insertDenies p)))"
  apply (rule_tac a = a in isSepaux, simp_all)
  using idNMT apply blast
  using noDAID apply blast
  using id_aux4 noDA1eq sepNetsID apply blast
  by (simp add: NormalisationIPPProofs.Cdom2 domIff)

lemma C_eq_iD_aux2[rule_format]: 
  "noDenyAll1 p \<longrightarrow> separated p\<longrightarrow> p \<noteq> []\<longrightarrow> x \<in> dom (Cp (list2FWpolicy p))\<longrightarrow>
  Cp(list2FWpolicy (insertDenies p)) x = Cp(list2FWpolicy p) x"
proof (induct p)
  case Nil thus ?case by simp 
next
  case (Cons y ys)  thus ?case 
    using Cons proof (cases y)
    case DenyAll thus ?thesis using Cons DenyAll apply simp
      apply (case_tac "ys = []", simp_all)
      apply (case_tac "x \<in> dom (Cp (list2FWpolicy ys))",simp_all)
       apply (metis Cdom2 domID idNMT list2FWpolicyconc noDA1eq)
      apply (metis DenyAll iD_isD idNMT list2FWpolicyconc nlpaux)
      done
  next
    case (DenyAllFromTo a b) thus ?thesis 
      using Cons apply simp
      apply (rule impI|rule allI|rule conjI|simp)+
      apply (case_tac "ys = []", simp_all)
       apply (metis Cdom2 ConcAssoc DenyAllFromTo)
      apply (case_tac "x \<in> dom (Cp (list2FWpolicy ys))", simp_all)
       apply (drule mp)
        apply (metis noDA1eq)
       apply (case_tac "x \<in> dom (Cp (list2FWpolicy (insertDenies ys)))")
        apply (metis Cdom2 DenyAllFromTo idNMT list2FWpolicyconc)
       apply (metis domID)
      apply (case_tac "x \<in> dom (Cp (list2FWpolicy (insertDenies ys)))")
       apply (subgoal_tac "Cp (list2FWpolicy (DenyAllFromTo a b \<oplus> DenyAllFromTo b a \<oplus>
                          DenyAllFromTo a b # insertDenies ys)) x = Some (deny ())")
        apply simp_all
        apply (subgoal_tac "Cp (list2FWpolicy (DenyAllFromTo a b # ys)) x =
                           Cp ((DenyAllFromTo a b)) x")
         apply (simp add: PLemmas, simp split: if_splits)
        apply (metis list2FWpolicyconc nlpaux)
       apply (metis Cdom2 DenyAllFromTo iD_isD iDdomAux idNMT list2FWpolicyconc)
      apply (metis Cdom2 DenyAllFromTo domIff idNMT list2FWpolicyconc nlpaux)
      done
  next
    case (AllowPortFromTo a b c) thus ?thesis 
      using AllowPortFromTo Cons apply simp
      apply (rule impI|rule allI|rule conjI|simp)+
      apply (case_tac "ys = []", simp_all)
       apply (metis Cdom2 ConcAssoc AllowPortFromTo)
      apply (case_tac "x \<in> dom (Cp (list2FWpolicy ys))",simp_all)
       apply (drule mp)
        apply (metis noDA1eq)
       apply (case_tac "x \<in> dom (Cp (list2FWpolicy (insertDenies ys)))")
        apply (metis Cdom2 AllowPortFromTo idNMT list2FWpolicyconc)
       apply (metis domID)
      apply (subgoal_tac "x \<in> dom (Cp (AllowPortFromTo a b c))")
       apply (case_tac "x \<notin> dom (Cp (list2FWpolicy (insertDenies ys)))", simp_all)
        apply (metis AllowPortFromTo Cdom2 ConcAssoc l2p_aux2 list2FWpolicyconc nlpaux)
       apply (meson Combinators.distinct(3) FWNormalisationCore.member.simps(4) NormalisationIPPProofs.dom_id noDenyAll.simps(1) separated.simps(1))
      apply (metis AllowPortFromTo domdConcStart)
      done
  next
    case (Conc a b) thus ?thesis 
      using Cons Conc  apply simp
      apply (intro impI allI conjI|simp)+
      apply (case_tac "ys = []",simp_all)
       apply (metis Cdom2 ConcAssoc Conc)
      apply (case_tac "x \<in> dom (Cp (list2FWpolicy ys))",simp_all)
       apply (drule mp)
        apply (metis noDA1eq)
       apply (case_tac "x \<in> dom (Cp (a \<oplus> b))")
        apply (case_tac "x \<notin> dom (Cp (list2FWpolicy (insertDenies ys)))", simp_all)
         apply (subst list2FWpolicyconc)
          apply (rule idNMT, simp)
         apply (metis domID)
        apply (metis Cdom2 Conc idNMT list2FWpolicyconc)
       apply (metis Cdom2 Conc domIff idNMT list2FWpolicyconc )
      apply (case_tac "x \<in> dom (Cp (a \<oplus> b))")
       apply (case_tac "x \<notin> dom (Cp (list2FWpolicy (insertDenies ys)))", simp_all)
        apply (subst list2FWpolicyconc)
         apply (rule idNMT, simp)
        apply (metis Cdom2 Conc ConcAssoc list2FWpolicyconc nlpaux)
       apply (metis (lifting, no_types) FWNormalisationCore.member.simps(1) NormalisationIPPProofs.dom_id noDenyAll.simps(1) separated.simps(1))
      apply (metis Conc domdConcStart)
      done
  qed
qed

lemma C_eq_iD: 
  "separated p \<Longrightarrow> noDenyAll1 p \<Longrightarrow> wellformed_policy1_strong p  \<Longrightarrow> 
   Cp(list2FWpolicy (insertDenies p)) = Cp (list2FWpolicy p)"
  by (rule ext) (metis CConcStartA C_eq_iD_aux2 DAAux wp1_alternative_not_mt wp1n_tl)

lemma noDAsortQ[rule_format]: "noDenyAll1 p \<longrightarrow> noDenyAll1 (qsort p l)"
proof (cases "p") 
  case Nil then show ?thesis by simp
next
  case (Cons a list) show ?thesis  
    apply (insert \<open>p = a # list\<close>, simp_all)
  proof (cases "a = DenyAll")
    case True 
    assume * : "a = DenyAll" 
    show "noDenyAll1(a # list) \<longrightarrow> 
               noDenyAll1(qsort[y\<leftarrow>list . \<not> smaller a y l] l @ a # qsort [y\<leftarrow>list . smaller a y l] l)" 
      using noDAsortQ by fastforce
  next
    case False
    assume * : "a \<noteq> DenyAll"
    have ** : "noDenyAll1 (a # list) \<Longrightarrow> noDenyAll (a # list)" by(case_tac a,simp_all add:*)
    show "noDenyAll1(a # list) \<longrightarrow> 
               noDenyAll1(qsort[y\<leftarrow>list . \<not> smaller a y l] l @ a # qsort [y\<leftarrow>list . smaller a y l] l)" 
      apply (insert *,rule impI)
      apply (rule noDA1eq, frule **)
      by (metis append_Cons append_Nil nDAeqSet qsort.simps(2) set_sortQ)
  qed
qed

lemma NetsCollectedSortQ: 
  "distinct p \<Longrightarrow>noDenyAll1 p \<Longrightarrow> all_in_list p l \<Longrightarrow> singleCombinators p \<Longrightarrow> 
   NetsCollected (qsort p l)"
  by(metis C_eqLemmas_id(22))

lemmas CLemmas =  nMTSort nMTSortQ none_MT_rulesRS2 none_MT_rulesrd
                  noDAsort noDAsortQ nDASC wp1_eq  wp1ID    SCp2l ANDSep   wp1n_RS2 
                  OTNSEp OTNSC noDA1sep wp1_alternativesep wellformed_eq 
                  wellformed1_alternative_sorted  

lemmas C_eqLemmas_id = CLemmas  NC2Sep NetsCollectedSep 
                       NetsCollectedSort NetsCollectedSortQ separatedNC
lemma C_eq_Until_InsertDenies: 
  "DenyAll\<in>set(policy2list p) \<Longrightarrow> all_in_list(policy2list p) l \<Longrightarrow> allNetsDistinct (policy2list p)\<Longrightarrow> 
    Cp (list2FWpolicy((insertDenies(separate(sort(removeShadowRules2 
            (remdups(rm_MT_rules Cp (insertDeny (removeShadowRules1 (policy2list p)))))) l))))) =
    Cp p"
  by (subst C_eq_iD,simp_all add: C_eqLemmas_id) (rule C_eq_until_separated, simp_all)

lemma C_eq_Until_InsertDeniesQ: 
  "DenyAll \<in> set (policy2list p) \<Longrightarrow> all_in_list  (policy2list p) l \<Longrightarrow> 
   allNetsDistinct (policy2list p) \<Longrightarrow> 
     Cp (list2FWpolicy ((insertDenies (separate (qsort  (removeShadowRules2 
          (remdups (rm_MT_rules Cp (insertDeny (removeShadowRules1 (policy2list p)))))) l))))) = 
     Cp p"
  apply (subst C_eq_iD, simp_all add: C_eqLemmas_id)
   apply (metis WP1rd set_qsort wellformed1_sortedQ wellformed_eq wp1ID wp1_alternativesep 
      wp1_aux1aa wp1n_RS2 wp1n_RS3)
  apply (rule C_eq_until_separatedQ)
  by simp_all

lemma C_eq_RD_aux[rule_format]: "Cp (p) x = Cp (removeDuplicates p) x" 
  apply (induct p, simp_all)
  apply (intro conjI impI)
  by (metis Cdom2 domIff nlpaux not_in_member) (metis Cp.simps(4) CConcStartaux Cdom2 domIff)
    
lemma C_eq_RAD_aux[rule_format]: 
  "p \<noteq> []  \<longrightarrow> Cp (list2FWpolicy p) x = Cp (list2FWpolicy (removeAllDuplicates p)) x"
proof (induct p)
  case Nil show ?case by simp
next
  case (Cons a p) then show ?case
    apply simp_all
    apply (case_tac "p = []", simp_all)
     apply (metis C_eq_RD_aux)
    apply (subst list2FWpolicyconc, simp)
    apply (case_tac "x \<in> dom (Cp (list2FWpolicy p))")
     apply (subst list2FWpolicyconc)
      apply (rule rADnMT, simp)
     apply (subst Cdom2,simp)
     apply (simp add: NormalisationIPPProofs.Cdom2 domIff)
    by (metis C_eq_RD_aux nlpaux domIff list2FWpolicyconc rADnMT)
qed

lemma C_eq_RAD: 
  "p \<noteq> []  \<Longrightarrow> Cp (list2FWpolicy p) = Cp (list2FWpolicy (removeAllDuplicates p)) "
  by (rule ext) (erule C_eq_RAD_aux)

lemma C_eq_compile: 
  "DenyAll \<in> set (policy2list p) \<Longrightarrow> all_in_list (policy2list p) l \<Longrightarrow> 
 allNetsDistinct (policy2list p) \<Longrightarrow> 
   Cp (list2FWpolicy (removeAllDuplicates (insertDenies (separate 
          (sort (removeShadowRules2 (remdups (rm_MT_rules Cp (insertDeny 
                   (removeShadowRules1 (policy2list p)))))) l))))) = Cp p"
  by (metis C_eq_RAD C_eq_Until_InsertDenies removeAllDuplicates.simps(2))

lemma C_eq_compileQ: 
  "DenyAll\<in>set(policy2list p) \<Longrightarrow> all_in_list(policy2list p) l \<Longrightarrow>  allNetsDistinct(policy2list p) \<Longrightarrow> 
  Cp (list2FWpolicy (removeAllDuplicates (insertDenies (separate (qsort 
                         (removeShadowRules2 (remdups (rm_MT_rules Cp (insertDeny 
                               (removeShadowRules1 (policy2list p)))))) l))))) = Cp p"
  apply (subst C_eq_RAD[symmetric])
   apply (rule idNMT)
   apply (metis WP1rd sepnMT sortnMTQ wellformed_policy1_strong.simps(1) wp1ID wp1n_RS2 wp1n_RS3)
  apply (rule C_eq_Until_InsertDeniesQ, simp_all)
  done

lemma C_eq_normalizePr: 
  "DenyAll \<in> set (policy2list p) \<Longrightarrow> allNetsDistinct (policy2list p) \<Longrightarrow> 
 all_in_list (policy2list p) (Nets_List p) \<Longrightarrow> 
 Cp (list2FWpolicy (normalizePr p)) = Cp p"
  unfolding normalizePrQ_def
  by (simp add: C_eq_compile normalizePr_def)
    
lemma C_eq_normalizePrQ: 
  "DenyAll \<in> set (policy2list p) \<Longrightarrow> allNetsDistinct (policy2list p) \<Longrightarrow>
 all_in_list (policy2list p) (Nets_List p) \<Longrightarrow> 
 Cp (list2FWpolicy (normalizePrQ p)) = Cp p"
  unfolding normalizePrQ_def
  using C_eq_compileQ by auto

lemma domSubset3: "dom (Cp (DenyAll \<oplus> x)) = dom (Cp (DenyAll))"
  by (simp add: PLemmas split_tupled_all split: option.splits)
    
lemma domSubset4: 
  "dom (Cp (DenyAllFromTo x y \<oplus> DenyAllFromTo y x \<oplus> AllowPortFromTo x y dn)) = 
   dom (Cp (DenyAllFromTo x y \<oplus> DenyAllFromTo y x))"
  by (simp  add: PLemmas split: option.splits decision.splits) auto
    
lemma domSubset5: 
  "dom (Cp (DenyAllFromTo x y \<oplus> DenyAllFromTo y x \<oplus> AllowPortFromTo y x dn)) = 
  dom (Cp (DenyAllFromTo x y \<oplus> DenyAllFromTo y x))"
  by (simp add: PLemmas split: option.splits decision.splits) auto
    
lemma domSubset1: 
  "dom (Cp (DenyAllFromTo one two \<oplus> DenyAllFromTo two one \<oplus> AllowPortFromTo one two dn \<oplus> x)) = 
   dom (Cp (DenyAllFromTo one two \<oplus> DenyAllFromTo two one \<oplus> x))"
  by (simp add: PLemmas allow_all_def deny_all_def split: option.splits decision.splits)  auto
    
lemma domSubset2: 
  "dom (Cp (DenyAllFromTo one two \<oplus> DenyAllFromTo two one \<oplus> AllowPortFromTo two one dn \<oplus> x)) = 
  dom (Cp (DenyAllFromTo one two \<oplus> DenyAllFromTo two one \<oplus> x))"
  by (simp add: PLemmas  allow_all_def deny_all_def split: option.splits decision.splits) auto
    
lemma ConcAssoc2: "Cp (X \<oplus> Y \<oplus> ((A \<oplus> B) \<oplus> D)) = Cp (X \<oplus> Y \<oplus> A \<oplus> B \<oplus> D)"
  by (simp add: Cp.simps)
    
lemma ConcAssoc3: "Cp (X \<oplus> ((Y \<oplus> A) \<oplus> D)) = Cp (X \<oplus> Y \<oplus> A \<oplus> D)"
  by (simp add: Cp.simps)
    
lemma RS3_NMT[rule_format]: "DenyAll \<in> set p \<longrightarrow>
    rm_MT_rules Cp p \<noteq> []"
  by (induct_tac p) (simp_all add: PLemmas)
    
lemma norm_notMT: "DenyAll \<in> set (policy2list p) \<Longrightarrow> normalizePr p \<noteq> []"
  unfolding normalizePrQ_def
  by (simp add: DAiniD RS3_NMT RS2_NMT idNMT normalizePr_def rADnMT sepnMT sortnMT)
    
lemma norm_notMTQ: "DenyAll \<in> set (policy2list p) \<Longrightarrow> normalizePrQ p \<noteq> []"
  unfolding normalizePrQ_def
  by (simp add: DAiniD RS3_NMT sortnMTQ RS2_NMT idNMT rADnMT sepnMT)
    
lemma domDA: "dom (Cp (DenyAll \<oplus> A)) = dom (Cp (DenyAll))"
  by (rule domSubset3)
    
lemmas domain_reasoningPr = domDA ConcAssoc2 domSubset1 domSubset2 
  domSubset3 domSubset4  domSubset5 domSubsetDistr1
  domSubsetDistr2 domSubsetDistrA domSubsetDistrD coerc_assoc ConcAssoc 
  ConcAssoc3
  
text \<open>The following lemmas help with the normalisation\<close>
lemma list2policyR_Start[rule_format]: "p \<in> dom (Cp a) \<longrightarrow>
                 Cp (list2policyR (a # list)) p = Cp a p"
  by (induct "a # list" rule:list2policyR.induct)
    (auto simp: Cp.simps dom_def map_add_def) 
    
lemma list2policyR_End: "p \<notin> dom (Cp a) \<Longrightarrow>
        Cp (list2policyR (a # list)) p = (Cp a \<Oplus> list2policy (map Cp list)) p"
  by (rule list2policyR.induct)
    (simp_all add: Cp.simps dom_def map_add_def list2policy_def split: option.splits)
    
lemma l2polR_eq_el[rule_format]: "N \<noteq> [] \<longrightarrow>
 Cp( list2policyR N) p =  (list2policy (map Cp N)) p"
proof (induct N)
  case Nil show ?case by simp 
next
  case (Cons a p) show ?case
    apply (insert Cons.hyps, simp_all add: list2policy_def)
    by (metis list2policyR_End list2policyR_Start domStart list2policy_def)
qed
  
lemma l2polR_eq: 
  "N \<noteq> [] \<Longrightarrow> Cp( list2policyR N) =  (list2policy (map Cp N))"
  by (auto simp: list2policy_def l2polR_eq_el )
    
lemma list2FWpolicys_eq_el[rule_format]: 
  "Filter \<noteq> []  \<longrightarrow>  Cp (list2policyR Filter) p =  Cp (list2FWpolicy (rev Filter)) p"
  apply (induct_tac Filter)
   apply simp_all
  subgoal for a list
    apply (case_tac "list = []")
     apply simp_all
    apply (case_tac "p \<in> dom (Cp a)")
     apply simp_all
     apply (rule list2policyR_Start)
     apply simp_all
    apply (subgoal_tac "Cp (list2policyR (a # list)) p = Cp (list2policyR list) p")
     apply (subgoal_tac "Cp (list2FWpolicy (rev list @ [a])) p = Cp (list2FWpolicy (rev list)) p")
      apply simp
     apply (rule CConcStart2)
      apply simp
     apply simp
    apply (case_tac list,simp_all)
    apply (simp_all add: Cp.simps dom_def map_add_def)
    done
  done
    
lemma list2FWpolicys_eq: 
  "Filter \<noteq> []  \<Longrightarrow>
  Cp (list2policyR Filter) =  Cp (list2FWpolicy (rev Filter))"
  by (rule ext, erule list2FWpolicys_eq_el)
    
lemma list2FWpolicys_eq_sym: 
  "Filter \<noteq> []  \<Longrightarrow>
  Cp (list2policyR (rev Filter)) =  Cp (list2FWpolicy Filter)"
  by (metis list2FWpolicys_eq rev_is_Nil_conv rev_rev_ident)
    
lemma p_eq[rule_format]: "p \<noteq> [] \<longrightarrow> 
 list2policy (map Cp (rev p)) = Cp (list2FWpolicy p)"
  by (metis l2polR_eq list2FWpolicys_eq_sym rev.simps(1) rev_rev_ident)
    
lemma p_eq2[rule_format]: "normalizePr x \<noteq> [] \<longrightarrow> 
  Cp (list2FWpolicy (normalizePr x)) = Cp x \<longrightarrow>
 list2policy (map Cp (rev (normalizePr x))) = Cp x"
  by (simp add: p_eq)
    
lemma p_eq2Q[rule_format]: "normalizePrQ x \<noteq> [] \<longrightarrow> 
  Cp (list2FWpolicy (normalizePrQ x)) = Cp x \<longrightarrow>
 list2policy (map Cp (rev (normalizePrQ x))) = Cp x"
  by (simp add: p_eq)
    
lemma list2listNMT[rule_format]: "x \<noteq> [] \<longrightarrow>map sem x \<noteq> []"
  by (case_tac x) (simp_all)
    
lemma Norm_Distr2: 
  "r o_f ((P \<Otimes>\<^sub>2 (list2policy Q)) o d) = 
  (list2policy ((P \<Otimes>\<^sub>L Q) (\<Otimes>\<^sub>2) r d))"
  by (rule ext, rule Norm_Distr_2)
    
lemma NATDistr: 
  "N \<noteq> [] \<Longrightarrow> F = Cp (list2policyR N) \<Longrightarrow> 
  ((\<lambda> (x,y). x) o_f ((NAT \<Otimes>\<^sub>2 F) o (\<lambda> x. (x,x)))  = 
   (list2policy (  ((NAT \<Otimes>\<^sub>L (map Cp N)) (\<Otimes>\<^sub>2) 
    (\<lambda> (x,y). x) (\<lambda> x. (x,x))))))"
  by (simp add: l2polR_eq)  (rule ext,rule Norm_Distr_2)
    
lemma C_eq_normalize_manual: 
  "DenyAll \<in> set (policy2list p) \<Longrightarrow> allNetsDistinct (policy2list p) \<Longrightarrow>
   all_in_list (policy2list p) l \<Longrightarrow> 
   Cp (list2FWpolicy (normalize_manual_orderPr p l)) = Cp p"
  unfolding normalize_manual_orderPr_def
  by(simp_all add:C_eq_compile)
    
lemma p_eq2_manualQ[rule_format]: 
  "normalize_manual_orderPrQ x l \<noteq> [] \<longrightarrow> 
   Cp (list2FWpolicy (normalize_manual_orderPrQ x l)) = Cp x \<longrightarrow>
   list2policy (map Cp (rev (normalize_manual_orderPrQ x l))) = Cp x"
  by (simp add: p_eq)
    
lemma norm_notMT_manualQ: "DenyAll \<in> set (policy2list p) \<Longrightarrow> normalize_manual_orderPrQ p l \<noteq> []"
  by (simp add: DAiniD RS3_NMT sortnMTQ RS2_NMT idNMT normalize_manual_orderPrQ_def rADnMT sepnMT)
    
lemma C_eq_normalizePr_manualQ: 
  "DenyAll \<in> set (policy2list p) \<Longrightarrow>
   allNetsDistinct (policy2list p) \<Longrightarrow>
   all_in_list (policy2list p) l \<Longrightarrow> 
   Cp (list2FWpolicy (normalize_manual_orderPrQ p l)) = Cp p"
  by (simp add: normalize_manual_orderPrQ_def C_eq_compileQ)
    
lemma p_eq2_manual[rule_format]: "normalize_manual_orderPr x l \<noteq> [] \<longrightarrow> 
  Cp (list2FWpolicy (normalize_manual_orderPr x l)) = Cp x \<longrightarrow>
 list2policy (map Cp (rev (normalize_manual_orderPr x l))) = Cp x"
  by (simp add: p_eq)
    
lemma norm_notMT_manual: "DenyAll \<in> set (policy2list p) \<Longrightarrow> normalize_manual_orderPr p l \<noteq> []"
  unfolding normalize_manual_orderPr_def
  by (simp add: idNMT rADnMT wellformed1_alternative_sorted wp1ID wp1_alternativesep wp1n_RS2)
    
text\<open>
  As an example, how this theorems can be used for a concrete normalisation instantiation. 
\<close>
  
lemma normalizePrNAT: 
  "DenyAll \<in> set (policy2list Filter) \<Longrightarrow> 
   allNetsDistinct (policy2list Filter) \<Longrightarrow>  
   all_in_list (policy2list Filter) (Nets_List Filter) \<Longrightarrow> 
   ((\<lambda> (x,y). x) o_f (((NAT \<Otimes>\<^sub>2 Cp Filter) o (\<lambda>x. (x,x)))))  = 
   list2policy ((NAT \<Otimes>\<^sub>L (map Cp (rev (normalizePr Filter)))) (\<Otimes>\<^sub>2) (\<lambda> (x,y). x) (\<lambda> x. (x,x)))"
  by (simp add: C_eq_normalizePr NATDistr list2FWpolicys_eq_sym norm_notMT)
    
lemma domSimpl[simp]: "dom (Cp (A \<oplus> DenyAll)) = dom (Cp (DenyAll))"
  by (simp add: PLemmas)

end
