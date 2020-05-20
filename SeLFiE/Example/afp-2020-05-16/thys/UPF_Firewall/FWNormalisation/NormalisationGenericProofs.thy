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

subsection\<open>Normalisation Proofs (Generic)\<close>
  theory
    NormalisationGenericProofs
    imports 
      FWNormalisationCore
begin
  
text \<open>
  This theory contains the generic proofs of the normalisation procedure, i.e. those which 
  are independent from the concrete semantical interpretation function.  
\<close>
    
lemma domNMT: "dom X \<noteq> {} \<Longrightarrow> X \<noteq> \<emptyset>"
  by auto
    
lemma denyNMT: "deny_all \<noteq>  \<emptyset>"
  apply (rule domNMT)
  by (simp add: deny_all_def dom_def)
    
lemma wellformed_policy1_charn[rule_format]: 
"wellformed_policy1 p \<longrightarrow> DenyAll \<in> set p \<longrightarrow> (\<exists> p'. p = DenyAll # p' \<and> DenyAll \<notin> set p')"
  by(induct "p",simp_all)
    
lemma singleCombinatorsConc: "singleCombinators (x#xs) \<Longrightarrow> singleCombinators xs"
  by (case_tac x,simp_all)
    
lemma aux0_0: "singleCombinators x \<Longrightarrow> \<not> (\<exists> a b. (a\<oplus>b) \<in> set x)"
  apply (induct "x", simp_all)
  subgoal for a b 
    by (case_tac "a",simp_all)
  done
  
lemma aux0_4: "(a \<in> set x \<or> a \<in> set y) = (a \<in> set (x@y))"
  by auto
    
lemma aux0_1: "\<lbrakk>singleCombinators xs; singleCombinators [x]\<rbrakk> \<Longrightarrow>
               singleCombinators (x#xs)"
  by (case_tac "x",simp_all) 
    
lemma aux0_6: "\<lbrakk>singleCombinators xs; \<not> (\<exists> a b. x = a \<oplus> b)\<rbrakk> \<Longrightarrow>
               singleCombinators(x#xs)"
  apply (rule aux0_1,simp_all)
  apply (case_tac "x",simp_all)
  done
    
lemma aux0_5: " \<not> (\<exists> a b. (a\<oplus>b) \<in> set x) \<Longrightarrow> singleCombinators x"
  apply (induct "x")   
   apply simp_all 
  by (metis aux0_6)
    
lemma ANDConc[rule_format]: "allNetsDistinct (a#p) \<longrightarrow> allNetsDistinct (p)"
  apply (simp add: allNetsDistinct_def)
  apply (case_tac "a")
  by simp_all
    
lemma aux6: "twoNetsDistinct a1 a2 a b \<Longrightarrow>
            dom (deny_all_from_to a1 a2) \<inter> dom (deny_all_from_to a b) = {}"
  by (auto simp: twoNetsDistinct_def netsDistinct_def src_def dest_def 
      in_subnet_def PolicyCombinators.PolicyCombinators dom_def)
    
lemma aux5[rule_format]: "(DenyAllFromTo a b) \<in> set p \<longrightarrow> a \<in> set (net_list p)"
  by (rule net_list_aux.induct,simp_all) 
    
lemma aux5a[rule_format]: "(DenyAllFromTo b a) \<in> set p \<longrightarrow> a \<in> set (net_list p)"
  by (rule net_list_aux.induct,simp_all) 
    
lemma aux5c[rule_format]:
  "(AllowPortFromTo a b po) \<in> set p \<longrightarrow> a \<in> set (net_list p)"
  by (rule net_list_aux.induct,simp_all) 
    
lemma aux5d[rule_format]:
  "(AllowPortFromTo b a po) \<in> set p \<longrightarrow> a \<in> set (net_list p)"
  by (rule net_list_aux.induct,simp_all) 
    
lemma aux10[rule_format]: "a \<in> set (net_list p) \<longrightarrow> a \<in> set (net_list_aux p)"
  by simp
    
lemma srcInNetListaux[simp]: 
  "\<lbrakk>x \<in> set p; singleCombinators[x]; x \<noteq> DenyAll\<rbrakk> \<Longrightarrow> srcNet x \<in> set (net_list_aux p)"
  apply (induct "p")
   apply simp_all
  subgoal for a p   
    apply (case_tac "x = a", simp_all)
     apply (case_tac a, simp_all)
    apply (case_tac a, simp_all)
    done
  done 
    
lemma destInNetListaux[simp]: 
  "\<lbrakk>x \<in> set p; singleCombinators[x]; x \<noteq> DenyAll\<rbrakk> \<Longrightarrow> destNet x \<in> set (net_list_aux p)"
  apply (induct p)
   apply simp_all
  subgoal for a p
    apply (case_tac "x = a", simp_all)
     apply (case_tac "a", simp_all)
    apply (case_tac "a", simp_all)
    done 
  done 
    
lemma tND1: "\<lbrakk>allNetsDistinct p; x \<in> set p; y \<in> set p; a = srcNet x;
             b = destNet x; c = srcNet y; d = destNet y; a \<noteq> c;
             singleCombinators[x]; x \<noteq> DenyAll; singleCombinators[y];
             y \<noteq> DenyAll\<rbrakk> \<Longrightarrow> twoNetsDistinct a b c d"
  by (simp add: allNetsDistinct_def twoNetsDistinct_def)
    
lemma tND2: "\<lbrakk>allNetsDistinct p; x \<in> set p; y \<in> set p; a = srcNet x;
             b = destNet x; c = srcNet y; d = destNet y; b \<noteq> d;
             singleCombinators[x]; x \<noteq> DenyAll; singleCombinators[y];
             y \<noteq> DenyAll\<rbrakk> \<Longrightarrow> twoNetsDistinct a b c d"
  by (simp add: allNetsDistinct_def twoNetsDistinct_def)
    
lemma tND: "\<lbrakk>allNetsDistinct p; x \<in> set p; y \<in> set p; a = srcNet x;
            b = destNet x; c = srcNet y; d = destNet y; a \<noteq> c \<or> b \<noteq> d;
            singleCombinators[x]; x \<noteq> DenyAll; singleCombinators[y]; y \<noteq> DenyAll\<rbrakk>
            \<Longrightarrow> twoNetsDistinct a b c d"
  apply (case_tac "a \<noteq> c", simp_all)
   apply (erule_tac x = x and y =y in tND1, simp_all)
  apply (erule_tac x = x and y =y in tND2, simp_all)
  done
    
lemma aux7: "\<lbrakk>DenyAllFromTo a b \<in> set p; allNetsDistinct ((DenyAllFromTo c d)#p);
             a\<noteq> c\<or> b\<noteq> d\<rbrakk> \<Longrightarrow> twoNetsDistinct a b c d"
  apply (erule_tac x = "DenyAllFromTo a b" and y = "DenyAllFromTo c d" in tND)
  by simp_all
    
lemma aux7a: "\<lbrakk>DenyAllFromTo a b  \<in> set p;
              allNetsDistinct ((AllowPortFromTo c d po)#p); a \<noteq> c\<or> b \<noteq> d\<rbrakk> \<Longrightarrow> 
              twoNetsDistinct a b c d"
  apply (erule_tac x = "DenyAllFromTo a b" and
      y = "AllowPortFromTo  c d po" in tND)
  by simp_all
    
lemma nDComm: assumes ab: "netsDistinct a b" shows ba: "netsDistinct b a"
  apply (insert ab)
  by (auto simp: netsDistinct_def  in_subnet_def)
    
lemma tNDComm: 
  assumes abcd: "twoNetsDistinct a b c d" shows "twoNetsDistinct c d a b"
  apply (insert abcd)
  by (metis twoNetsDistinct_def nDComm)
    
lemma aux[rule_format]: "a \<in> set (removeShadowRules2 p) \<longrightarrow> a \<in> set p"
  apply (case_tac a)
  by (rule removeShadowRules2.induct, simp_all)+
    
lemma aux12: "\<lbrakk>a \<in> x; b \<notin> x\<rbrakk> \<Longrightarrow> a \<noteq> b"
  by auto
    
lemma ND0aux1[rule_format]: "DenyAllFromTo x y \<in> set b \<Longrightarrow>  
                             x \<in> set (net_list_aux b)"
  by (metis aux5 net_list.simps set_remdups)
    
lemma ND0aux2[rule_format]: "DenyAllFromTo x y \<in> set b \<Longrightarrow>  
                             y \<in> set (net_list_aux b)"
  by (metis aux5a net_list.simps set_remdups)
    
lemma ND0aux3[rule_format]: "AllowPortFromTo x y p \<in> set b \<Longrightarrow>  
                             x \<in> set (net_list_aux b)"
  by (metis aux5c net_list.simps set_remdups)
    
lemma ND0aux4[rule_format]: "AllowPortFromTo x y p \<in> set b \<Longrightarrow>  
                             y \<in> set (net_list_aux b)"
  by (metis aux5d net_list.simps set_remdups)
    
lemma aNDSubsetaux[rule_format]: "singleCombinators a  \<longrightarrow> set a \<subseteq> set b \<longrightarrow> 
                                  set (net_list_aux a) \<subseteq> set (net_list_aux b)"
  apply (induct a)
   apply simp_all
  apply clarify
  apply (drule mp, erule singleCombinatorsConc)
  subgoal for a a' x
    apply (case_tac "a")
       apply (simp_all add: contra_subsetD)
      apply (metis contra_subsetD)
     apply (metis ND0aux1 ND0aux2 contra_subsetD)
    apply (metis ND0aux3 ND0aux4 contra_subsetD)
    done
  done
    
lemma aNDSetsEqaux[rule_format]: "singleCombinators a \<longrightarrow> singleCombinators b \<longrightarrow> 
                 set a = set b \<longrightarrow> set (net_list_aux a) = set (net_list_aux b)"
  apply (rule impI)+
  apply (rule equalityI)
   apply (rule aNDSubsetaux, simp_all)+
  done
    
lemma aNDSubset: "\<lbrakk>singleCombinators a;set a \<subseteq> set b; allNetsDistinct b\<rbrakk> \<Longrightarrow> 
                  allNetsDistinct a"
  apply (simp add: allNetsDistinct_def)
  apply (rule allI)+
  apply (rule impI)+
  subgoal for x y 
    apply (drule_tac x = "x" in spec, drule_tac x = "y" in spec)
    using aNDSubsetaux by blast
  done
    
lemma aNDSetsEq: "\<lbrakk>singleCombinators a; singleCombinators b; set a = set b; 
                  allNetsDistinct b\<rbrakk> \<Longrightarrow> allNetsDistinct a"
  apply (simp add: allNetsDistinct_def)
  apply (rule allI)+
  apply (rule impI)+
  subgoal for x y 
    apply (drule_tac x = "x" in spec, drule_tac x = "y" in spec)
    using aNDSetsEqaux by auto
  done
    
lemma SCConca: "\<lbrakk>singleCombinators p; singleCombinators [a]\<rbrakk> \<Longrightarrow> 
                singleCombinators (a#p)" 
  by(metis aux0_1)
    
lemma aux3[simp]: "\<lbrakk>singleCombinators p; singleCombinators [a];  
                     allNetsDistinct (a#p)\<rbrakk> \<Longrightarrow> allNetsDistinct (a#a#p)"
  by (metis aNDSetsEq aux0_1 insert_absorb2 list.set(2))
    
lemma wp1_aux1a[rule_format]: "xs \<noteq> [] \<longrightarrow> wellformed_policy1_strong (xs @ [x]) \<longrightarrow> 
                               wellformed_policy1_strong xs"
  by (induct xs,simp_all)
    
lemma wp1alternative_RS1[rule_format]: "DenyAll \<in> set p \<longrightarrow> 
                              wellformed_policy1_strong (removeShadowRules1 p)"
  by (induct p,simp_all)
    
lemma wellformed_eq: "DenyAll \<in> set p \<longrightarrow> 
                      ((wellformed_policy1 p) = (wellformed_policy1_strong p))"
  by (induct p,simp_all)
    
lemma set_insort: "set(insort x xs l) = insert x (set xs)"
  by (induct xs) auto
    
lemma set_sort[simp]: "set(sort xs l) = set xs"
  by (induct xs) (simp_all add:set_insort)
    
    
lemma set_sortQ: "set(qsort xs l) = set xs"
  by simp
    
lemma aux79[rule_format]: "y \<in> set (insort x a l) \<longrightarrow>  y \<noteq> x \<longrightarrow> y \<in> set a"
  apply (induct a)
  by auto
    
lemma aux80: "\<lbrakk>y \<notin> set p; y \<noteq> x\<rbrakk> \<Longrightarrow> y \<notin> set (insort x (sort p l) l)"
  apply (metis aux79 set_sort)
  done
    
    
lemma WP1Conca: "DenyAll \<notin> set p \<Longrightarrow> wellformed_policy1 (a#p)"
  by (case_tac a,simp_all)
    
    
lemma saux[simp]: "(insort DenyAll p l) = DenyAll#p"
  by (induct_tac p,simp_all)
    
lemma saux3[rule_format]: "DenyAllFromTo a b \<in> set list \<longrightarrow> 
                          DenyAllFromTo c d \<notin> set list \<longrightarrow> (a \<noteq> c) \<or> (b \<noteq> d)"
  by blast
    
lemma waux2[rule_format]: " (DenyAll \<notin> set xs) \<longrightarrow> wellformed_policy1 xs"
  by (induct_tac xs,simp_all)
    
lemma waux3[rule_format]: "\<lbrakk>x \<noteq> a;  x \<notin> set p\<rbrakk> \<Longrightarrow> x \<notin> set (insort a p l)"
  by (metis aux79)
    
lemma wellformed1_sorted_aux[rule_format]: "wellformed_policy1 (x#p) \<Longrightarrow> 
                                            wellformed_policy1 (insort x p l)" 
  by (metis NormalisationGenericProofs.set_insort list.set(2) saux waux2 wellformed_eq 
            wellformed_policy1_strong.simps(2))
    
lemma wellformed1_sorted_auxQ[rule_format]: "wellformed_policy1 (p) \<Longrightarrow> 
                                            wellformed_policy1 (qsort p l)" 
proof (induct p)
  case Nil show ?case by simp
next
  case (Cons a S) then show ?case
    apply simp_all 
    apply (cases a,simp_all)
    by  (metis Combinators.simps append_Cons append_Nil qsort.simps(2) set_ConsD set_qsort waux2)+
  qed        
    
lemma SR1Subset: "set (removeShadowRules1 p) \<subseteq> set p"
  apply (induct_tac p, simp_all)
  subgoal for x xs
    apply (case_tac "x", simp_all) 
       apply(auto)
    done
  done
    
lemma SCSubset[rule_format]: " singleCombinators b \<longrightarrow> set a \<subseteq> set b \<longrightarrow>
                              singleCombinators a"
proof (induct a)
  case Nil thus ?case by simp
next
  case (Cons x xs)  thus ?case
    by (meson aux0_0 aux0_5 subsetCE)
qed
  
lemma setInsert[simp]: "set list \<subseteq> insert a (set list)"
  by auto
    
lemma SC_RS1[rule_format,simp]: "singleCombinators p \<longrightarrow> allNetsDistinct p \<longrightarrow>
    singleCombinators (removeShadowRules1 p)"
  apply (induct_tac p)
   apply simp_all
  using ANDConc singleCombinatorsConc by blast
    
lemma RS2Set[rule_format]: "set (removeShadowRules2 p) \<subseteq> set p"
  apply(induct p, simp_all)
  subgoal for a as  
    apply(case_tac a)
    by(auto)
  done
    
lemma WP1: "a \<notin> set list \<Longrightarrow> a \<notin> set (removeShadowRules2 list)"
  using RS2Set [of list] by blast
    
    
lemma denyAllDom[simp]: "x \<in> dom (deny_all)"
  by (simp add: UPFDefs(24) domI) 
    
lemma lCdom2: "(list2FWpolicy (a @ (b @ c))) = (list2FWpolicy ((a@b)@c))"
  by auto
    
lemma SCConcEnd: "singleCombinators (xs @ [xa]) \<Longrightarrow> singleCombinators xs"
  apply (induct "xs", simp_all)
  subgoal for a as
    by  (case_tac "a" , simp_all)
  done   
    
lemma list2FWpolicyconc[rule_format]: "a \<noteq> [] \<longrightarrow>
                               (list2FWpolicy (xa # a)) = (xa) \<oplus> (list2FWpolicy a)"
  by (induct a,simp_all)
    
lemma wp1n_tl [rule_format]: "wellformed_policy1_strong p \<longrightarrow>
                              p = (DenyAll#(tl p))"
  by (induct p, simp_all)
    
lemma foo2: "a \<notin> set ps \<Longrightarrow> 
             a \<notin> set ss \<Longrightarrow>
             set p = set s \<Longrightarrow> 
             p = (a#(ps)) \<Longrightarrow> 
             s = (a#ss) \<Longrightarrow> 
             set (ps) = set (ss)"
  by auto
    
    
lemma SCnotConc[rule_format,simp]: "a\<oplus>b \<in> set p \<longrightarrow> singleCombinators p \<longrightarrow>False"
  apply (induct p, simp_all)
  subgoal for p ps  
    by(case_tac p, simp_all)
  done
    
lemma auxx8: "removeShadowRules1_alternative_rev [x] = [x]"
  by (case_tac "x", simp_all)
    
lemma RS1End[rule_format]: "x \<noteq> DenyAll \<longrightarrow> removeShadowRules1 (xs @ [x]) = 
                            (removeShadowRules1 xs)@[x]"
  by (induct_tac xs, simp_all)
    
lemma aux114: "x \<noteq> DenyAll \<Longrightarrow> removeShadowRules1_alternative_rev (x#xs) = 
               x#(removeShadowRules1_alternative_rev xs)"
  apply (induct_tac xs)
  apply (auto simp: auxx8)
  by (case_tac "x", simp_all)
    
lemma aux115[rule_format]: "x \<noteq> DenyAll\<Longrightarrow>removeShadowRules1_alternative (xs@[x]) 
                            = (removeShadowRules1_alternative xs)@[x]"
  apply (simp add: removeShadowRules1_alternative_def aux114)
  done
    
lemma RS1_DA[simp]: "removeShadowRules1 (xs @ [DenyAll]) = [DenyAll]"
  by (induct_tac xs, simp_all)
    
lemma rSR1_eq: "removeShadowRules1_alternative = removeShadowRules1"
  apply (rule ext)
  apply (simp add: removeShadowRules1_alternative_def)
  subgoal for x 
    apply (rule_tac xs = x in rev_induct)
     apply simp_all
    subgoal for x xs
      apply (case_tac "x = DenyAll", simp_all)
      apply (metis RS1End aux114 rev.simps(2))
      done
    done
  done
    
lemma domInterMT[rule_format]: "\<lbrakk>dom a \<inter> dom b = {}; x \<in> dom a\<rbrakk> \<Longrightarrow> x \<notin> dom b"
  by auto
    
lemma domComm: "dom a \<inter> dom b = dom b \<inter> dom a"
  by auto
        
lemma r_not_DA_in_tl[rule_format]: 
  "wellformed_policy1_strong p \<longrightarrow>  a \<in> set p\<longrightarrow> a \<noteq> DenyAll \<longrightarrow> a \<in> set (tl p)"
  by (induct p,simp_all)
    
lemma wp1_aux1aa[rule_format]: "wellformed_policy1_strong p \<longrightarrow> DenyAll \<in> set p"
  by (induct p,simp_all)
    
lemma mauxa: "(\<exists> r. a b = \<lfloor>r\<rfloor>) = (a b \<noteq> \<bottom>)"
  by auto
    
lemma l2p_aux[rule_format]: "list \<noteq> [] \<longrightarrow>
                             list2FWpolicy (a # list) = a \<oplus>(list2FWpolicy list)"
  by (induct "list", simp_all)
    
lemma l2p_aux2[rule_format]: "list = [] \<Longrightarrow> list2FWpolicy (a # list) = a"
  by simp
           
lemma aux7aa: 
  assumes 1 : "AllowPortFromTo a b poo \<in> set p" 
    and    2 : "allNetsDistinct ((AllowPortFromTo c d po) # p)"
    and    3 : "a \<noteq> c \<or> b \<noteq> d"
  shows       "twoNetsDistinct a b c d" (is "?H")
proof(cases "a \<noteq> c") print_cases
  case True assume *:"a \<noteq> c"  show ?H
    by (meson "1" "2" True allNetsDistinct_def aux5c list.set_intros(1) 
        list.set_intros(2) twoNetsDistinct_def)
next
  case False assume *:"\<not>(a \<noteq> c)" show "twoNetsDistinct a b c d"
    by (meson "1" "2" "3" False allNetsDistinct_def aux5d list.set_intros(1) 
        list.set_intros(2) twoNetsDistinct_def)
qed
  
lemma ANDConcEnd: "\<lbrakk> allNetsDistinct (xs @ [xa]); singleCombinators xs\<rbrakk> \<Longrightarrow> 
                   allNetsDistinct xs"
  by (rule aNDSubset, auto)
    
lemma WP1ConcEnd[rule_format]: 
  "wellformed_policy1 (xs@[xa]) \<longrightarrow> wellformed_policy1 xs"
  by (induct xs, simp_all)
    
lemma NDComm: "netsDistinct a b = netsDistinct b a"
  by (auto simp: netsDistinct_def in_subnet_def)
    
    
lemma wellformed1_sorted[simp]: 
  assumes wp1: "wellformed_policy1 p" 
  shows        "wellformed_policy1 (sort p l)"
proof (cases p)
  case Nil thus ?thesis by simp
next
  case (Cons x xs) thus ?thesis
  proof (cases "x = DenyAll") 
    case True thus ?thesis using assms Cons by simp 
  next
    case False thus ?thesis using assms  
      by (metis Cons set_sort False waux2 wellformed_eq 
          wellformed_policy1_strong.simps(2)) 
  qed
qed
  
  
lemma wellformed1_sortedQ[simp]: 
  assumes wp1: "wellformed_policy1 p" 
  shows        "wellformed_policy1 (qsort p l)"
proof (cases p)
  case Nil thus ?thesis by simp
next
  case (Cons x xs) thus ?thesis
  proof (cases "x = DenyAll") 
    case True thus ?thesis using assms Cons by simp 
  next
    case False thus ?thesis using assms  
      by (metis Cons set_qsort False waux2 wellformed_eq 
          wellformed_policy1_strong.simps(2)) 
  qed
qed
  
lemma SC1[simp]: "singleCombinators p \<Longrightarrow>singleCombinators (removeShadowRules1 p)"
  by (erule SCSubset) (rule SR1Subset)
    
lemma SC2[simp]: "singleCombinators p \<Longrightarrow>singleCombinators (removeShadowRules2 p)"
  by (erule SCSubset) (rule RS2Set)
    
lemma SC3[simp]: "singleCombinators p \<Longrightarrow> singleCombinators (sort p l)"
  by (erule SCSubset) simp
    
lemma SC3Q[simp]: "singleCombinators p \<Longrightarrow> singleCombinators (qsort p l)"
  by (erule SCSubset) simp
    
lemma aND_RS1[simp]: "\<lbrakk>singleCombinators p; allNetsDistinct p\<rbrakk> \<Longrightarrow> 
                      allNetsDistinct (removeShadowRules1 p)"
  apply (rule aNDSubset)
  apply (erule SC_RS1, simp_all)
  apply (rule SR1Subset)
  done
    
lemma aND_RS2[simp]: "\<lbrakk>singleCombinators p; allNetsDistinct p\<rbrakk> \<Longrightarrow> 
                      allNetsDistinct (removeShadowRules2 p)"
  apply (rule aNDSubset)
  apply (erule SC2, simp_all)
  apply (rule RS2Set)
  done
    
lemma aND_sort[simp]: "\<lbrakk>singleCombinators p; allNetsDistinct p\<rbrakk> \<Longrightarrow>  
                       allNetsDistinct (sort p l)"
  apply (rule aNDSubset)
  by (erule SC3, simp_all)
    
    
    
lemma aND_sortQ[simp]: "\<lbrakk>singleCombinators p; allNetsDistinct p\<rbrakk> \<Longrightarrow>  
                       allNetsDistinct (qsort p l)"
  apply (rule aNDSubset)
  by (erule SC3Q, simp_all)
    
lemma inRS2[rule_format,simp]: "x \<notin> set p \<longrightarrow> x \<notin> set (removeShadowRules2 p)"
  apply (insert RS2Set [of p])
  by blast
    
lemma distinct_RS2[rule_format,simp]: "distinct p \<longrightarrow> 
                                       distinct (removeShadowRules2 p)"
  apply (induct p)
  apply simp_all
  apply clarify
  subgoal for a p 
    apply (case_tac "a")
    by auto
  done
    
lemma setPaireq: " {x, y} = {a, b} \<Longrightarrow> x = a \<and> y = b \<or> x = b \<and> y = a"
  by (metis  doubleton_eq_iff)
    
lemma position_positive[rule_format]: "a \<in> set l \<longrightarrow> position a l > 0"
  by (induct l, simp_all)
    
lemma pos_noteq[rule_format]: 
  "a \<in> set l \<longrightarrow> b \<in> set l \<longrightarrow> c \<in> set l \<longrightarrow> 
   a \<noteq> b \<longrightarrow> position a l \<le> position b l \<longrightarrow> position b l \<le> position c l \<longrightarrow> 
   a \<noteq> c"
proof(induct l)
  case Nil show ?case by simp
next
  case (Cons a R) show ?case 
    by (metis (no_types, lifting) Cons.hyps One_nat_def Suc_le_mono le_antisym 
        length_greater_0_conv list.size(3) nat.inject position.simps(2) 
        position_positive set_ConsD)
qed
  
lemma setPair_noteq: "{a,b} \<noteq> {c,d} \<Longrightarrow> \<not> ((a = c) \<and> (b = d))" 
  by auto
    
lemma setPair_noteq_allow: "{a,b} \<noteq> {c,d} \<Longrightarrow> \<not> ((a = c) \<and> (b = d) \<and> P)" 
  by auto
    
lemma order_trans:  
  "\<lbrakk>in_list x l; in_list y l; in_list z l; singleCombinators [x]; 
  singleCombinators [y]; singleCombinators [z]; smaller x y l; smaller y z l\<rbrakk> \<Longrightarrow> 
  smaller x z l"
  apply (case_tac x, simp_all)
   apply (case_tac z, simp_all)
     apply (case_tac y, simp_all)
    apply (case_tac y, simp_all)
     apply (rule conjI|rule impI)+ 
      apply (simp add: setPaireq)
     apply (rule conjI|rule impI)+
     apply (simp_all split: if_splits)
       apply metis+
     apply auto[1]
    apply (simp add: setPaireq)
   apply (rule impI,case_tac y, simp_all)
    apply (simp_all split: if_splits, metis,simp_all add: setPair_noteq setPair_noteq_allow)
  apply (case_tac z, simp_all)
    apply (case_tac y, simp_all)
   apply (case_tac y, simp_all)
    apply (intro impI|rule conjI)+
     apply (simp_all split: if_splits)
     apply (simp add: setPair_noteq)
     apply (erule pos_noteq, simp_all)
    apply auto[1]
   apply (rule conjI,simp add: setPair_noteq_allow)
    apply (erule pos_noteq, simp_all)
   apply auto[1]
  apply (rule impI,rule disjI2) 
  apply (case_tac y, simp_all split: if_splits )
    apply metis
   apply (simp_all add: setPair_noteq_allow)
  done
    
lemma sortedConcStart[rule_format]: 
  "sorted (a # aa # p) l \<longrightarrow> in_list a l \<longrightarrow> in_list aa l \<longrightarrow> all_in_list p l\<longrightarrow> 
  singleCombinators [a] \<longrightarrow> singleCombinators [aa] \<longrightarrow> singleCombinators p \<longrightarrow> 
  sorted (a#p) l"
  apply (induct p)
   apply simp_all
  apply (rule impI)+
  apply simp
  apply (rule_tac y = "aa" in order_trans)
         apply simp_all
  subgoal for p ps
    apply (case_tac "p", simp_all)
    done
  done
    
lemma singleCombinatorsStart[simp]: "singleCombinators (x#xs) \<Longrightarrow> 
                                     singleCombinators [x]"
  by (case_tac x, simp_all)
    
    
lemma sorted_is_smaller[rule_format]: 
  "sorted (a # p) l \<longrightarrow> in_list a l \<longrightarrow> in_list b l \<longrightarrow> all_in_list p l \<longrightarrow>  
  singleCombinators [a] \<longrightarrow> singleCombinators p \<longrightarrow> b \<in> set p \<longrightarrow> smaller a b l"
  apply (induct p)
   apply (auto intro: singleCombinatorsConc sortedConcStart) 
  done
    
lemma sortedConcEnd[rule_format]: "sorted (a # p) l \<longrightarrow> in_list a l \<longrightarrow> 
                                   all_in_list p l \<longrightarrow> singleCombinators [a] \<longrightarrow> 
                                   singleCombinators p  \<longrightarrow> sorted p l"
  apply (induct p)
   apply (auto intro: singleCombinatorsConc sortedConcStart)
  done
    
lemma in_set_in_list[rule_format]: "a \<in> set p \<longrightarrow> all_in_list p l\<longrightarrow> in_list a l"
  by (induct p) auto
    
lemma sorted_Consb[rule_format]: 
  "all_in_list (x#xs) l \<longrightarrow> singleCombinators (x#xs) \<longrightarrow> 
    (sorted xs l & (\<forall>y\<in>set xs. smaller x y l)) \<longrightarrow>  (sorted (x#xs) l) "
  apply(induct xs arbitrary: x) 
   apply (auto simp: order_trans)
  done
    
lemma sorted_Cons: "\<lbrakk>all_in_list (x#xs) l; singleCombinators (x#xs)\<rbrakk> \<Longrightarrow> 
              (sorted xs l & (\<forall>y\<in>set xs. smaller x y l)) =  (sorted (x#xs) l)"
  apply auto
    apply (rule sorted_Consb, simp_all)
   apply (metis singleCombinatorsConc singleCombinatorsStart sortedConcEnd)
  apply (erule sorted_is_smaller)
  apply (auto intro: singleCombinatorsConc singleCombinatorsStart in_set_in_list)
  done
    
lemma smaller_antisym: "\<lbrakk>\<not> smaller a b l; in_list a l; in_list b l; 
                        singleCombinators[a]; singleCombinators [b]\<rbrakk> \<Longrightarrow>  
                        smaller b a l"
  apply (case_tac a)
     apply simp_all
   apply (case_tac b)
      apply simp_all
    apply (simp_all split: if_splits)
   apply (rule setPaireq)
   apply simp
  apply (case_tac b)
     apply simp_all
   apply (simp_all split: if_splits)
  done
    
lemma set_insort_insert: "set (insort x xs l) \<subseteq> insert x (set xs)"
  by (induct xs) auto
    
lemma all_in_listSubset[rule_format]: "all_in_list b l \<longrightarrow>singleCombinators a \<longrightarrow> 
                                      set a \<subseteq> set b \<longrightarrow> all_in_list a l"
  by (induct_tac a) (auto intro: in_set_in_list singleCombinatorsConc)
    
lemma singleCombinators_insort: "\<lbrakk>singleCombinators [x]; singleCombinators xs\<rbrakk> \<Longrightarrow> 
                                 singleCombinators (insort x xs l)"
  by (metis NormalisationGenericProofs.set_insort aux0_0 aux0_1 aux0_5 list.simps(15))
    
lemma all_in_list_insort: "\<lbrakk>all_in_list xs l; singleCombinators (x#xs); 
                           in_list x l\<rbrakk> \<Longrightarrow>  all_in_list (insort x xs l) l"
  apply (rule_tac b = "x#xs" in all_in_listSubset)
    apply simp_all
   apply (metis singleCombinatorsConc singleCombinatorsStart
      singleCombinators_insort)
  apply (rule set_insort_insert)
  done
    
lemma sorted_ConsA:"\<lbrakk>all_in_list (x#xs) l; singleCombinators (x#xs)\<rbrakk> \<Longrightarrow> 
              (sorted (x#xs) l)  = (sorted xs l & (\<forall>y\<in>set xs. smaller x y l))"
  by (metis sorted_Cons)
    
lemma is_in_insort: "y \<in> set xs \<Longrightarrow> y \<in> set (insort x xs l)"
  by (simp add: NormalisationGenericProofs.set_insort) 
    
lemma sorted_insorta[rule_format]:
  assumes 1 : "sorted (insort x xs l) l"
    and   2 : "all_in_list (x#xs) l" 
    and   3 : "all_in_list (x#xs) l"
    and   4 : "distinct (x#xs)"
    and   5 : "singleCombinators [x]"
    and   6 : "singleCombinators xs"
  shows       "sorted xs l"
proof (insert 1 2 3 4 5 6, induct xs) 
  case Nil show ?case by simp
next 
  case (Cons a xs)
  then show ?case 
    apply simp
    apply (auto intro: is_in_insort sorted_ConsA set_insort singleCombinators_insort 
        singleCombinatorsConc sortedConcEnd all_in_list_insort) [1]
    apply(cases "smaller x a l", simp_all)
    by (metis NormalisationGenericProofs.set_insort NormalisationGenericProofs.sorted_Cons 
        all_in_list.simps(2) all_in_list_insort aux0_1 insert_iff singleCombinatorsConc 
        singleCombinatorsStart singleCombinators_insort) 
qed
  
  
lemma sorted_insortb[rule_format]: 
  "sorted xs l \<longrightarrow> all_in_list (x#xs) l \<longrightarrow> distinct (x#xs) \<longrightarrow> 
   singleCombinators [x] \<longrightarrow> singleCombinators xs \<longrightarrow> sorted (insort x xs l) l"
proof (induct xs)
  case Nil show ?case by simp_all
next
  case (Cons a xs) 
  have * : "sorted (a # xs) l \<Longrightarrow>      all_in_list (x # a # xs) l \<Longrightarrow>
              distinct (x # a # xs) \<Longrightarrow>  singleCombinators [x] \<Longrightarrow>
              singleCombinators (a # xs) \<Longrightarrow> sorted (insort x xs l) l" 
    apply(insert Cons.hyps, simp_all)
    apply(metis sorted_Cons all_in_list.simps(2)  singleCombinatorsConc)
    done
  show ?case
    apply (insert Cons.hyps)
    apply (rule impI)+
    apply (insert *, auto intro!: sorted_Consb)    
  proof (rule_tac b = "x#xs" in all_in_listSubset)
    show "in_list x l \<Longrightarrow> all_in_list xs l \<Longrightarrow> all_in_list (x # xs) l"
      by simp_all
  next
    show "singleCombinators [x] \<Longrightarrow>
                       singleCombinators (a # xs) \<Longrightarrow>
                       FWNormalisationCore.sorted (FWNormalisationCore.insort x xs l) l \<Longrightarrow>
                       singleCombinators (FWNormalisationCore.insort x xs l)"
      apply (rule singleCombinators_insort, simp_all)
      by (erule singleCombinatorsConc)
  next
    show "set (FWNormalisationCore.insort x xs l) \<subseteq> set (x # xs)"
      using NormalisationGenericProofs.set_insort_insert by auto
  next
    show "singleCombinators [x] \<Longrightarrow>
                       singleCombinators (a # xs) \<Longrightarrow>
                      singleCombinators (a # FWNormalisationCore.insort x xs l)"
      by (metis SCConca singleCombinatorsConc singleCombinatorsStart  
          singleCombinators_insort)
  next
    fix y
    show "FWNormalisationCore.sorted (a # xs) l \<Longrightarrow>
                       singleCombinators [x] \<Longrightarrow>  singleCombinators (a # xs) \<Longrightarrow>
                       in_list x l \<Longrightarrow>  in_list a l \<Longrightarrow> all_in_list xs l \<Longrightarrow>
                       \<not> smaller x a l \<Longrightarrow> y \<in> set (FWNormalisationCore.insort x xs l) \<Longrightarrow> 
                      smaller a y l"
      by (metis NormalisationGenericProofs.set_insort in_set_in_list insert_iff 
          singleCombinatorsConc singleCombinatorsStart smaller_antisym 
          sorted_is_smaller)
  qed
qed
  
lemma sorted_insort: 
  "\<lbrakk>all_in_list (x#xs) l; distinct(x#xs); singleCombinators [x];
                     singleCombinators xs\<rbrakk> \<Longrightarrow>
                  sorted (insort x xs l) l = sorted xs l"
  by (auto intro: sorted_insorta sorted_insortb)
    
lemma distinct_insort: "distinct (insort x xs l) = (x \<notin> set xs \<and> distinct xs)"
  by(induct xs)(auto simp:set_insort)
    
lemma distinct_sort[simp]: "distinct (sort xs l) = distinct xs"
  by(induct xs)(simp_all add:distinct_insort)
    
    
lemma sort_is_sorted[rule_format]: 
  "all_in_list p l \<longrightarrow> distinct p \<longrightarrow> singleCombinators p \<longrightarrow> sorted (sort p l) l"
  apply (induct p)
   apply simp
  by (metis (no_types, lifting) NormalisationGenericProofs.distinct_sort 
      NormalisationGenericProofs.set_sort SC3 all_in_list.simps(2) all_in_listSubset 
      distinct.simps(2) set_subset_Cons singleCombinatorsConc singleCombinatorsStart 
      sort.simps(2) sorted_insortb)
    
lemma smaller_sym[rule_format]: "all_in_list [a] l \<longrightarrow> smaller a a l"
  by (case_tac a,simp_all)
    
lemma SC_sublist[rule_format]: 
  "singleCombinators xs \<Longrightarrow> singleCombinators (qsort [y\<leftarrow>xs. P y] l)"
  by (auto intro: SCSubset)
    
lemma all_in_list_sublist[rule_format]: 
  "singleCombinators xs \<longrightarrow> all_in_list xs l \<longrightarrow> all_in_list (qsort [y\<leftarrow>xs. P y] l) l"
  by (auto intro: all_in_listSubset SC_sublist)
    
lemma SC_sublist2[rule_format]: 
  "singleCombinators xs \<longrightarrow> singleCombinators ([y\<leftarrow>xs. P y])"
  by (auto intro: SCSubset)
    
lemma all_in_list_sublist2[rule_format]: 
  "singleCombinators xs \<longrightarrow> all_in_list xs l \<longrightarrow> all_in_list ( [y\<leftarrow>xs. P y]) l"
  by (auto intro: all_in_listSubset SC_sublist2)
    
lemma all_in_listAppend[rule_format]: 
  "all_in_list (xs) l \<longrightarrow> all_in_list (ys) l \<longrightarrow> all_in_list (xs @ ys) l"
  by (induct xs) simp_all
    
lemma distinct_sortQ[rule_format]: 
  "singleCombinators xs \<longrightarrow> all_in_list xs l \<longrightarrow> distinct xs \<longrightarrow> distinct (qsort xs l)"
  apply (induct xs l rule: qsort.induct) 
   apply simp
  apply (auto simp: SC_sublist2 singleCombinatorsConc all_in_list_sublist2)
  done
        
lemma singleCombinatorsAppend[rule_format]: 
  "singleCombinators (xs) \<longrightarrow> singleCombinators (ys) \<longrightarrow> singleCombinators (xs @ ys)"
  apply (induct xs, auto)
  subgoal for a as
    apply (case_tac a,simp_all)
    done 
  subgoal for a as
    apply (case_tac a,simp_all)
    done       
  done
    
lemma sorted_append1[rule_format]:
  "all_in_list xs l  \<longrightarrow> singleCombinators xs \<longrightarrow>
   all_in_list ys l  \<longrightarrow> singleCombinators ys \<longrightarrow> 
  (sorted (xs@ys) l \<longrightarrow> 
  (sorted xs l & sorted ys l & (\<forall>x \<in> set xs. \<forall>y \<in> set ys. smaller x y l)))"
  apply(induct xs)
   apply(simp_all)
  by (metis NormalisationGenericProofs.sorted_Cons all_in_list.simps(2) all_in_listAppend aux0_1 
      aux0_4 singleCombinatorsAppend singleCombinatorsConc singleCombinatorsStart)
    
lemma sorted_append2[rule_format]:
  "all_in_list xs l\<longrightarrow> singleCombinators xs \<longrightarrow>
   all_in_list ys l \<longrightarrow> singleCombinators ys \<longrightarrow> 
   (sorted xs l & sorted ys l & (\<forall>x \<in> set xs. \<forall>y \<in> set ys. smaller x y l)) \<longrightarrow> 
  (sorted (xs@ys) l)"
  apply (induct xs)
   apply simp_all
  by (metis NormalisationGenericProofs.sorted_Cons all_in_list.simps(2) all_in_listAppend aux0_1 
      aux0_4 singleCombinatorsAppend singleCombinatorsConc singleCombinatorsStart)
    
lemma sorted_append[rule_format]:
  "all_in_list xs l \<longrightarrow> singleCombinators xs \<longrightarrow>
   all_in_list ys l \<longrightarrow> singleCombinators ys \<longrightarrow> 
   (sorted (xs@ys) l) =
   (sorted xs l & sorted ys l & (\<forall>x \<in> set xs. \<forall>y \<in> set ys. smaller x y l))"
  apply (rule impI)+
  apply (rule iffI)
   apply (rule sorted_append1,simp_all)
  apply (rule sorted_append2,simp_all)
  done
    
lemma sort_is_sortedQ[rule_format]: 
  "all_in_list p l  \<longrightarrow> singleCombinators p \<longrightarrow> sorted (qsort p l) l"
proof (induct p l rule: qsort.induct) print_cases
  case 1 show ?case by simp
next
  case 2 fix x::"('a,'b) Combinators" fix xs::"('a,'b) Combinators list" fix l
  show "all_in_list [y\<leftarrow>xs . \<not> smaller x y l] l \<longrightarrow>
                 singleCombinators [y\<leftarrow>xs . \<not> smaller x y l] \<longrightarrow> 
                 sorted (qsort [y\<leftarrow>xs . \<not> smaller x y l] l) l \<Longrightarrow>
                 all_in_list [y\<leftarrow>xs . smaller x y l] l \<longrightarrow>
                 singleCombinators [y\<leftarrow>xs . smaller x y l] \<longrightarrow> 
                 sorted (qsort [y\<leftarrow>xs . smaller x y l] l) l \<Longrightarrow>
                 all_in_list(x#xs) l \<longrightarrow>  singleCombinators(x#xs) \<longrightarrow> sorted (qsort(x#xs) l) l"
    apply (intro impI)
    apply (simp_all add: SC_sublist all_in_list_sublist all_in_list_sublist2 
        singleCombinatorsConc SC_sublist2)
  proof (subst sorted_append)
    show "in_list x l \<and> all_in_list xs l \<Longrightarrow> 
                       singleCombinators (x # xs) \<Longrightarrow> 
                       all_in_list (qsort [y\<leftarrow>xs . \<not> smaller x y l] l) l"
      by (metis all_in_list_sublist singleCombinatorsConc)
  next
    show "in_list x l \<and> all_in_list xs l \<Longrightarrow> 
                       singleCombinators (x # xs) \<Longrightarrow> 
                       singleCombinators (qsort [y\<leftarrow>xs . \<not> smaller x y l] l)"
      apply (auto simp: SC_sublist all_in_list_sublist SC_sublist2
          all_in_list_sublist2 sorted_Cons sorted_append not_le)
      apply (metis SC3Q SC_sublist2 singleCombinatorsConc)
      done
  next
    show "sorted (qsort [y\<leftarrow>xs . \<not> smaller x y l] l) l \<Longrightarrow>
                       sorted (qsort [y\<leftarrow>xs . smaller x y l] l) l \<Longrightarrow>
                       in_list x l \<and> all_in_list xs l \<Longrightarrow> singleCombinators (x # xs) \<Longrightarrow> 
                       all_in_list (x # qsort [y\<leftarrow>xs . smaller x y l] l) l"
      using all_in_list.simps(2) all_in_list_sublist singleCombinatorsConc by blast
  next
    show "sorted (qsort [y\<leftarrow>xs . smaller x y l] l) l \<Longrightarrow>
                       in_list x l \<and> all_in_list xs l \<Longrightarrow> singleCombinators (x # xs) \<Longrightarrow> 
                       singleCombinators (x # qsort [y\<leftarrow>xs . smaller x y l] l)"
      using SC_sublist aux0_1 singleCombinatorsConc singleCombinatorsStart by blast
  next
    show "sorted (qsort [y\<leftarrow>xs . \<not> smaller x y l] l) l \<Longrightarrow>
                       sorted (qsort [y\<leftarrow>xs . smaller x y l] l) l \<Longrightarrow>
                       in_list x l \<and> all_in_list xs l \<Longrightarrow>
                       singleCombinators (x # xs) \<Longrightarrow>
                       FWNormalisationCore.sorted (qsort [y\<leftarrow>xs . \<not> smaller x y l] l) l \<and>
                       FWNormalisationCore.sorted (x # qsort [y\<leftarrow>xs . smaller x y l] l) l \<and>
                       (\<forall>x'\<in>set (qsort [y\<leftarrow>xs . \<not> smaller x y l] l). 
                                \<forall>y\<in>set (x # qsort [y\<leftarrow>xs . smaller x y l] l). smaller x' y l)"
      apply(auto)[1]
      apply (metis (mono_tags, lifting) SC_sublist all_in_list.simps(2) 
          all_in_list_sublist aux0_1 mem_Collect_eq set_filter set_qsort 
          singleCombinatorsConc singleCombinatorsStart sorted_Consb)
      apply (metis aux0_0 aux0_6 in_set_in_list singleCombinatorsConc 
          singleCombinatorsStart smaller_antisym)
      by (metis (no_types, lifting) NormalisationGenericProofs.order_trans aux0_0 
          aux0_6 in_set_in_list 
          singleCombinatorsConc singleCombinatorsStart smaller_antisym)
  qed
qed
  
  
lemma inSet_not_MT: "a \<in> set p \<Longrightarrow> p \<noteq> []"
  by auto 
    
lemma RS1n_assoc: 
  "x \<noteq> DenyAll \<Longrightarrow>  removeShadowRules1_alternative xs @ [x] =
                  removeShadowRules1_alternative (xs @ [x])"
  by (simp add: removeShadowRules1_alternative_def aux114)
    
lemma RS1n_nMT[rule_format,simp]: "p \<noteq> []\<longrightarrow> removeShadowRules1_alternative p \<noteq> []"
  apply (simp add: removeShadowRules1_alternative_def)
  apply (rule_tac xs = p in rev_induct, simp_all) 
  subgoal for x xs
    apply (case_tac "xs = []", simp_all)
     apply (case_tac x, simp_all)
    apply (rule_tac xs = "xs" in rev_induct, simp_all)
     apply (case_tac x, simp_all)+
    done
  done
    
lemma RS1N_DA[simp]: "removeShadowRules1_alternative (a@[DenyAll]) = [DenyAll]"
  by (simp add: removeShadowRules1_alternative_def)
    
lemma WP1n_DA_notinSet[rule_format]: "wellformed_policy1_strong p \<longrightarrow>
                                     DenyAll \<notin> set (tl p)"
  by (induct p) (simp_all) 
    
lemma mt_sym: "dom a \<inter> dom b = {} \<Longrightarrow> dom b \<inter> dom a = {}"
  by auto
    
lemma DAnotTL[rule_format]: 
  "xs \<noteq> [] \<longrightarrow> wellformed_policy1 (xs @ [DenyAll]) \<longrightarrow> False"
  by (induct xs, simp_all)
    
    
lemma AND_tl[rule_format]: "allNetsDistinct ( p) \<longrightarrow> allNetsDistinct (tl p)"
  apply (induct p, simp_all)
  by (auto intro: ANDConc)
    
lemma distinct_tl[rule_format]: "distinct p \<longrightarrow> distinct (tl p)"
  by (induct p, simp_all)
    
lemma SC_tl[rule_format]: "singleCombinators ( p) \<longrightarrow> singleCombinators (tl p)"
  by (induct p, simp_all) (auto intro: singleCombinatorsConc) 
    
lemma Conc_not_MT: "p = x#xs \<Longrightarrow> p \<noteq> []"
  by auto
    
lemma wp1_tl[rule_format]: 
  "p \<noteq> [] \<and> wellformed_policy1 p \<longrightarrow> wellformed_policy1 (tl p)"
  by (induct p) (auto intro: waux2)
    
lemma wp1_eq[rule_format]: 
  "wellformed_policy1_strong p \<Longrightarrow> wellformed_policy1 p"
  apply (case_tac "DenyAll \<in> set p")
   apply (subst wellformed_eq)
    apply (auto elim: waux2)
  done
    
lemma wellformed1_alternative_sorted: 
  "wellformed_policy1_strong p \<Longrightarrow> wellformed_policy1_strong (sort p l)"
  by (case_tac "p", simp_all)
    
lemma wp1n_RS2[rule_format]: 
  "wellformed_policy1_strong p \<longrightarrow> wellformed_policy1_strong (removeShadowRules2 p)"
  by (induct p, simp_all)
    
lemma RS2_NMT[rule_format]: "p \<noteq> [] \<longrightarrow> removeShadowRules2 p \<noteq> []"
  apply (induct p, simp_all)
  subgoal for a p  
    apply (case_tac "p \<noteq> []", simp_all)
     apply (case_tac "a", simp_all)+
    done
  done
    
lemma wp1_alternative_not_mt[simp]: "wellformed_policy1_strong p \<Longrightarrow> p \<noteq> []"
  by auto
    
lemma AIL1[rule_format,simp]: "all_in_list p l \<longrightarrow>
                               all_in_list (removeShadowRules1 p) l"
  by (induct_tac p, simp_all)
    
lemma wp1ID: "wellformed_policy1_strong (insertDeny (removeShadowRules1 p))"
  apply (induct p, simp_all)
  subgoal for a p 
    apply (case_tac a, simp_all)
    done
  done
    
lemma dRD[simp]: "distinct (remdups p)"
  by simp
    
lemma AILrd[rule_format,simp]: "all_in_list p l \<longrightarrow> all_in_list (remdups p) l"
  by (induct p, simp_all)
    
lemma AILiD[rule_format,simp]: "all_in_list p l \<longrightarrow> all_in_list (insertDeny p) l"
  apply (induct p, simp_all)
  apply (rule impI, simp)
  subgoal for a p 
    apply (case_tac a, simp_all)
    done
  done
    
lemma SCrd[rule_format,simp]:"singleCombinators p\<longrightarrow> singleCombinators(remdups p)"
  apply (induct p, simp_all)
  subgoal for a p 
    apply (case_tac a, simp_all)
    done
  done
    
lemma SCRiD[rule_format,simp]: "singleCombinators p \<longrightarrow>
                                singleCombinators(insertDeny p)"
  apply (induct p, simp_all)
  subgoal for a p 
    apply (case_tac a, simp_all)
    done
  done
    
lemma WP1rd[rule_format,simp]: 
  "wellformed_policy1_strong p \<longrightarrow> wellformed_policy1_strong (remdups p)"
  by (induct p, simp_all)
    
lemma ANDrd[rule_format,simp]: 
  "singleCombinators p \<longrightarrow> allNetsDistinct p \<longrightarrow> allNetsDistinct (remdups p)"
  apply (rule impI)+
  apply (rule_tac b = p in aNDSubset)
    apply simp_all
  done
    
lemma ANDiD[rule_format,simp]: 
  "allNetsDistinct p \<longrightarrow>  allNetsDistinct (insertDeny p)"
  apply (induct p, simp_all)
   apply (simp add: allNetsDistinct_def)
  apply (auto intro: ANDConc)
  subgoal for a p 
    apply (case_tac "a",simp_all add: allNetsDistinct_def)
    done
  done
    
lemma mr_iD[rule_format]: 
  "wellformed_policy1_strong p  \<longrightarrow> matching_rule x p = matching_rule x (insertDeny p)"
  by (induct p, simp_all)
    
lemma WP1iD[rule_format,simp]: "wellformed_policy1_strong p \<longrightarrow>
                                wellformed_policy1_strong (insertDeny p)"
  by (induct p, simp_all)
    
lemma DAiniD: "DenyAll \<in> set (insertDeny p)"
  apply (induct p, simp_all)
  subgoal for a p
    apply(case_tac a, simp_all)
    done
  done
    
lemma p2lNmt: "policy2list p \<noteq> []"
  by (rule policy2list.induct, simp_all)
    
lemma AIL2[rule_format,simp]: 
  "all_in_list p l \<longrightarrow> all_in_list (removeShadowRules2 p) l"
  apply (induct_tac p, simp_all)
  subgoal for a p
    apply(case_tac a, simp_all)
    done
  done
    
lemma SCConc: "singleCombinators x \<Longrightarrow>  singleCombinators y \<Longrightarrow> singleCombinators (x@y)"
  apply (rule aux0_5)
  apply (metis aux0_0 aux0_4)
  done 	
    
lemma SCp2l: "singleCombinators (policy2list p)"
  by (induct_tac p) (auto intro: SCConc)
    
lemma subnetAux: "Dd \<inter> A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow>  Dd \<inter> B \<noteq> {}"
  by auto
    
lemma soadisj: "x \<in> subnetsOfAdr a \<Longrightarrow> y \<in> subnetsOfAdr a \<Longrightarrow> \<not> netsDistinct x y"
  by(simp add: subnetsOfAdr_def netsDistinct_def,auto)
    
lemma not_member: "\<not> member a (x\<oplus>y) \<Longrightarrow> \<not> member a x"
  by auto
    
lemma soadisj2: "(\<forall> a x y. x \<in> subnetsOfAdr a \<and> y \<in> subnetsOfAdr a \<longrightarrow> \<not> netsDistinct x y)"
  by (simp add: subnetsOfAdr_def netsDistinct_def, auto)
    
lemma ndFalse1: 
  "(\<forall>a b c d. (a,b)\<in>A  \<and> (c,d)\<in>B \<longrightarrow> netsDistinct a c) \<Longrightarrow>
   \<exists>(a, b)\<in>A. a \<in> subnetsOfAdr D \<Longrightarrow> 
   \<exists>(a, b)\<in>B. a \<in> subnetsOfAdr D \<Longrightarrow> False"
  apply (auto simp: soadisj)
  using soadisj2 by blast
    
lemma ndFalse2: "(\<forall>a b c d. (a,b)\<in>A  \<and> (c,d)\<in>B \<longrightarrow> netsDistinct b d) \<Longrightarrow>
                 \<exists>(a, b)\<in>A. b \<in> subnetsOfAdr D \<Longrightarrow>
                 \<exists>(a, b)\<in>B. b \<in> subnetsOfAdr D \<Longrightarrow> False"
  apply (auto simp: soadisj)
  using soadisj2 by blast
    
lemma tndFalse: "(\<forall>a b c d. (a,b)\<in>A  \<and> (c,d)\<in>B \<longrightarrow> twoNetsDistinct a b c d) \<Longrightarrow>
        \<exists>(a, b)\<in>A. a \<in> subnetsOfAdr (D::('a::adr)) \<and> b \<in> subnetsOfAdr (F::'a) \<Longrightarrow> 
        \<exists>(a, b)\<in>B. a \<in> subnetsOfAdr D\<and> b\<in> subnetsOfAdr F 
    \<Longrightarrow> False"
  apply (simp add: twoNetsDistinct_def)
  apply (auto simp: ndFalse1 ndFalse2)
  apply (metis soadisj)
  done
    
lemma sepnMT[rule_format]: "p \<noteq> [] \<longrightarrow> (separate p) \<noteq> []"
  by (induct p rule: separate.induct)  simp_all
    
lemma sepDA[rule_format]: "DenyAll \<notin> set p \<longrightarrow> DenyAll \<notin> set (separate p)"
  by (induct p rule: separate.induct)  simp_all
    
lemma setnMT: "set a = set b \<Longrightarrow> a \<noteq> [] \<Longrightarrow> b \<noteq> []"
  by auto
    
lemma sortnMT: "p \<noteq> [] \<Longrightarrow> sort p l \<noteq> []"
  by (metis set_sort setnMT)
    
lemma idNMT[rule_format]: "p \<noteq> [] \<longrightarrow> insertDenies p \<noteq> []"
  apply (induct p, simp_all)
  subgoal for a p
    apply(case_tac a, simp_all)
    done
  done
    
lemma OTNoTN[rule_format]: " OnlyTwoNets p \<longrightarrow> x \<noteq> DenyAll \<longrightarrow> x \<in> set p \<longrightarrow>  onlyTwoNets x"
  apply (induct p, simp_all, rename_tac a p)
  apply (intro impI  conjI,  simp)
  subgoal for a p
    apply(case_tac a, simp_all)
    done
  subgoal for a p
    apply(case_tac a, simp_all)
    done
  done
    
lemma first_isIn[rule_format]:  "\<not> member DenyAll x \<longrightarrow> (first_srcNet x,first_destNet x) \<in> sdnets x"
  by (induct x,case_tac x, simp_all)
    
lemma sdnets2: 
  "\<exists>a b. sdnets x = {(a, b), (b, a)} \<Longrightarrow> \<not> member DenyAll x \<Longrightarrow>
   sdnets x = {(first_srcNet x, first_destNet x),  (first_destNet x, first_srcNet x)}"
proof -
  have * : "\<exists>a b. sdnets x = {(a, b), (b, a)} \<Longrightarrow> \<not> member DenyAll x 
            \<Longrightarrow> (first_srcNet x, first_destNet x) \<in> sdnets x" 
    by (erule first_isIn) 
  show     "\<exists>a b. sdnets x = {(a, b), (b, a)} \<Longrightarrow> \<not> member DenyAll x \<Longrightarrow>
               sdnets x = {(first_srcNet x, first_destNet x),  (first_destNet x, first_srcNet x)}"
    using * by auto
qed
  
lemma alternativelistconc1[rule_format]: 
  "a \<in> set (net_list_aux [x]) \<longrightarrow>  a \<in> set (net_list_aux [x,y])"
  by (induct x,simp_all)
    
lemma alternativelistconc2[rule_format]: 
  "a \<in> set (net_list_aux [x]) \<longrightarrow> a \<in> set (net_list_aux [y,x])"
  by (induct y, simp_all)
    
lemma noDA[rule_format]:
  "noDenyAll xs \<longrightarrow> s \<in> set xs \<longrightarrow> \<not> member DenyAll s"
  by (induct xs, simp_all)
    
lemma isInAlternativeList:
  "(aa \<in> set (net_list_aux [a]) \<or> aa \<in> set (net_list_aux p)) \<Longrightarrow> aa \<in> set (net_list_aux (a # p))"
  by (case_tac a,simp_all)
    
lemma netlistaux: 
  "x \<in> set (net_list_aux (a # p))\<Longrightarrow>  x \<in> set (net_list_aux ([a])) \<or> x \<in> set (net_list_aux (p))"
  apply (case_tac " x \<in> set (net_list_aux [a])", simp_all)
  apply (case_tac a, simp_all)
  done
    
lemma firstInNet[rule_format]: 
  "\<not> member DenyAll a \<longrightarrow>  first_destNet a \<in> set (net_list_aux (a # p))"
  apply (rule Combinators.induct, simp_all)
  apply (metis netlistaux)
  done
    
lemma firstInNeta[rule_format]: 
  "\<not> member DenyAll a \<longrightarrow>  first_srcNet a \<in> set (net_list_aux (a # p))"
  apply (rule Combinators.induct, simp_all)
  apply (metis netlistaux)
  done  
    
lemma disjComm: "disjSD_2 a b \<Longrightarrow> disjSD_2 b a"
  apply (simp add: disjSD_2_def)
  apply (intro allI  impI  conjI)
  using tNDComm apply blast
  by (meson tNDComm twoNetsDistinct_def)
    
lemma disjSD2aux:
  "disjSD_2 a b \<Longrightarrow> \<not> member DenyAll a \<Longrightarrow> \<not> member DenyAll b \<Longrightarrow>
  disjSD_2 (DenyAllFromTo (first_srcNet a) (first_destNet a) \<oplus>
            DenyAllFromTo (first_destNet a) (first_srcNet a) \<oplus> a)
           b"
  apply (drule disjComm,rule disjComm)
  apply (simp add: disjSD_2_def)
  using first_isIn by blast
    
lemma noDA1eq[rule_format]: "noDenyAll p \<longrightarrow> noDenyAll1 p"
  apply (induct p, simp,rename_tac a p)
  subgoal for a p
    apply(case_tac a, simp_all)
    done
  done
    
lemma noDA1C[rule_format]: "noDenyAll1 (a#p) \<longrightarrow> noDenyAll1 p"
  by (case_tac a, simp_all,rule impI, rule noDA1eq, simp)+
    
lemma disjSD_2IDa: 
  "disjSD_2 x y \<Longrightarrow>
   \<not> member DenyAll x \<Longrightarrow>
   \<not> member DenyAll y \<Longrightarrow> 
   a = first_srcNet x \<Longrightarrow> 
   b = first_destNet x \<Longrightarrow> 
   disjSD_2 (DenyAllFromTo a b \<oplus> DenyAllFromTo b a \<oplus> x) y"
  by(simp add:disjSD2aux)
    
lemma noDAID[rule_format]: "noDenyAll p \<longrightarrow> noDenyAll (insertDenies p)"
  apply (induct p, simp_all)
  subgoal for a p
    apply(case_tac a, simp_all)
    done
  done
    
lemma isInIDo[rule_format]:  
  "noDenyAll p  \<longrightarrow> s \<in> set (insertDenies p) \<longrightarrow> 
   (\<exists>! a. s = (DenyAllFromTo (first_srcNet a) (first_destNet a)) \<oplus>
   (DenyAllFromTo (first_destNet a) (first_srcNet a)) \<oplus> a \<and> a \<in> set p)"
  apply (induct p, simp, rename_tac a p)
  subgoal for a p
    apply (case_tac "a = DenyAll", simp)
    apply (case_tac a, auto)
    done
  done
    
lemma id_aux1[rule_format]: "DenyAllFromTo (first_srcNet s) (first_destNet s) \<oplus>
      DenyAllFromTo (first_destNet s) (first_srcNet s) \<oplus> s\<in> set (insertDenies p)
    \<longrightarrow> s \<in> set p"
  apply (induct p, simp_all, rename_tac a p)
  subgoal for a p
    apply(case_tac a, simp_all)
    done
  done
    
lemma id_aux2:
  "noDenyAll p \<Longrightarrow>
   \<forall>s. s \<in> set p \<longrightarrow> disjSD_2 a s \<Longrightarrow>
   \<not> member DenyAll a \<Longrightarrow>
   DenyAllFromTo (first_srcNet s) (first_destNet s) \<oplus> 
   DenyAllFromTo (first_destNet s) (first_srcNet s) \<oplus> s \<in> set (insertDenies p) \<Longrightarrow>
   disjSD_2 a (DenyAllFromTo (first_srcNet s) (first_destNet s) \<oplus> 
   DenyAllFromTo (first_destNet s) (first_srcNet s) \<oplus> s)"
  by (metis disjComm disjSD2aux isInIDo noDA)
    
lemma id_aux4[rule_format]: 
  "noDenyAll p \<Longrightarrow> \<forall>s. s \<in> set p \<longrightarrow> disjSD_2 a s \<Longrightarrow> 
   s \<in> set (insertDenies p) \<Longrightarrow> \<not> member DenyAll a \<Longrightarrow> 
   disjSD_2 a s"
  apply (subgoal_tac "\<exists>a. s =
          DenyAllFromTo (first_srcNet a) (first_destNet a) \<oplus>
          DenyAllFromTo (first_destNet a) (first_srcNet a) \<oplus> a \<and>
          a \<in> set p")
   apply (drule_tac Q = "disjSD_2 a s" in exE, simp_all, rule id_aux2, simp_all)
  using isInIDo by blast
    
lemma sepNetsID[rule_format]: 
  "noDenyAll1 p \<longrightarrow> separated p \<longrightarrow> separated (insertDenies p)"
  apply (induct p, simp)
  apply (rename_tac a p, auto)
  using noDA1C apply blast
  subgoal for a p
    apply (case_tac "a = DenyAll", auto)
     apply (simp add: disjSD_2_def)
    apply (case_tac a,auto)
      apply (rule disjSD_2IDa, simp_all, rule id_aux4, simp_all, metis noDA noDAID)+
    done
  done
    
lemma aNDDA[rule_format]: "allNetsDistinct p \<longrightarrow> allNetsDistinct(DenyAll#p)"
  by (case_tac p,auto simp: allNetsDistinct_def)
    
lemma OTNConc[rule_format]: "OnlyTwoNets (y # z) \<longrightarrow>  OnlyTwoNets z"
  by (case_tac y, simp_all)
    
lemma first_bothNetsd: "\<not> member DenyAll x \<Longrightarrow> first_bothNet x = {first_srcNet x, first_destNet x}"
  by (induct x) simp_all
    
lemma bNaux:
  "\<not> member DenyAll x \<Longrightarrow> \<not> member DenyAll y \<Longrightarrow>
   first_bothNet x = first_bothNet y \<Longrightarrow>
   {first_srcNet x, first_destNet x} = {first_srcNet y, first_destNet y}"
  by (simp add: first_bothNetsd)
    
lemma setPair: "{a,b} = {a,d} \<Longrightarrow> b = d"
  by (metis setPaireq)
    
lemma setPair1: "{a,b} = {d,a} \<Longrightarrow> b = d"
  by (metis Un_empty_right Un_insert_right insert_absorb2 setPaireq)
    
lemma setPair4: "{a,b} = {c,d} \<Longrightarrow> a \<noteq> c \<Longrightarrow> a = d"
  by auto
    
lemma otnaux1: " {x, y, x, y} = {x,y}"
  by auto
        
lemma OTNIDaux4: "{x,y,x} = {y,x}"
  by auto
    
lemma setPair5: "{a,b} = {c,d} \<Longrightarrow> a \<noteq> c \<Longrightarrow> a = d"
  by auto
    
lemma otnaux: "   
  \<lbrakk>first_bothNet x = first_bothNet y; \<not> member DenyAll x; \<not> member DenyAll y; 
   onlyTwoNets y; onlyTwoNets x\<rbrakk> \<Longrightarrow> 
   onlyTwoNets (x \<oplus> y)"
  apply (simp add: onlyTwoNets_def)
  apply (subgoal_tac "{first_srcNet x, first_destNet x} =
                     {first_srcNet y, first_destNet y}")
   apply (case_tac "(\<exists>a b. sdnets y = {(a, b)})")
    apply simp_all
    apply (case_tac "(\<exists>a b. sdnets x = {(a, b)})")
     apply simp_all
     apply (subgoal_tac "sdnets x = {(first_srcNet x, first_destNet x)}")
      apply (subgoal_tac "sdnets y = {(first_srcNet y, first_destNet y)}")
       apply simp
       apply (case_tac "first_srcNet x = first_srcNet y")
        apply simp_all
        apply (rule disjI1)
        apply (rule setPair)
        apply simp
       apply (subgoal_tac "first_srcNet x = first_destNet y")
        apply simp
        apply (subgoal_tac "first_destNet x = first_srcNet y")
         apply simp
         apply (rule_tac x ="first_srcNet y" in exI, rule_tac x = "first_destNet y" in exI,simp)
        apply (rule setPair1)
        apply simp
       apply (rule setPair4)
        apply simp_all
      apply (metis first_isIn singletonE)
     apply (metis first_isIn singletonE)
    apply (subgoal_tac "sdnets x = {(first_srcNet x, first_destNet x),
                                    (first_destNet x, first_srcNet x)}")
     apply (subgoal_tac "sdnets y = {(first_srcNet y, first_destNet y)}")
      apply simp
      apply (case_tac "first_srcNet x = first_srcNet y")
       apply simp_all
       apply (subgoal_tac "first_destNet x = first_destNet y")
        apply simp
       apply (rule setPair)
       apply simp
      apply (subgoal_tac "first_srcNet x = first_destNet y")
       apply simp
       apply (subgoal_tac "first_destNet x = first_srcNet y")
        apply simp
        apply (rule_tac x ="first_srcNet y" in exI, rule_tac x = "first_destNet y" in exI)
        apply (metis OTNIDaux4 insert_commute )
       apply (rule setPair1)
       apply simp
      apply (rule setPair5)
       apply assumption
      apply simp
     apply (metis first_isIn singletonE)
    apply (rule sdnets2)
     apply simp_all
   apply (case_tac "(\<exists>a b. sdnets x = {(a, b)})")
    apply simp_all
    apply (subgoal_tac "sdnets x = {(first_srcNet x, first_destNet x)}")
     apply (subgoal_tac "sdnets y = {(first_srcNet y, first_destNet y),
                                 (first_destNet y, first_srcNet y)}")
      apply simp
      apply (case_tac "first_srcNet x = first_srcNet y")
       apply simp_all
       apply (subgoal_tac "first_destNet x = first_destNet y")
        apply simp
        apply (rule_tac x ="first_srcNet y" in exI, rule_tac x = "first_destNet y" in exI)
        apply (metis OTNIDaux4 insert_commute )
       apply (rule setPair)
       apply simp
      apply (subgoal_tac "first_srcNet x = first_destNet y")
       apply simp
       apply (subgoal_tac "first_destNet x = first_srcNet y")
        apply simp
       apply (rule setPair1)
       apply simp
      apply (rule setPair4)
       apply assumption
      apply simp
     apply (rule sdnets2)
      apply simp
     apply simp
    apply (metis singletonE first_isIn)
   apply (subgoal_tac "sdnets x = {(first_srcNet x, first_destNet x),
                                 (first_destNet x, first_srcNet x)}")
    apply (subgoal_tac "sdnets y = {(first_srcNet y, first_destNet y),
                                (first_destNet y, first_srcNet y)}")
     apply simp
     apply (case_tac "first_srcNet x = first_srcNet y")
      apply simp_all
      apply (subgoal_tac "first_destNet x = first_destNet y")
       apply simp
       apply (rule_tac x ="first_srcNet y" in exI, rule_tac x = "first_destNet y" in exI)
       apply (rule otnaux1)
      apply (rule setPair)
      apply simp
     apply (subgoal_tac "first_srcNet x = first_destNet y")
      apply simp
      apply (subgoal_tac "first_destNet x = first_srcNet y")
       apply simp
       apply (rule_tac x ="first_srcNet y" in exI, rule_tac x = "first_destNet y" in exI)
       apply (metis OTNIDaux4 insert_commute)
      apply (rule setPair1)
      apply simp
     apply (rule setPair4)
      apply assumption
     apply simp
    apply (rule sdnets2,simp_all)+
  apply (rule bNaux, simp_all)
  done
    
lemma OTNSepaux: 
  "onlyTwoNets (a \<oplus> y) \<and> OnlyTwoNets z \<longrightarrow> OnlyTwoNets (separate (a \<oplus> y # z)) \<Longrightarrow>
    \<not> member DenyAll a \<Longrightarrow>  \<not> member DenyAll y \<Longrightarrow>
    noDenyAll z \<Longrightarrow> onlyTwoNets a \<Longrightarrow> OnlyTwoNets (y # z) \<Longrightarrow> first_bothNet a = first_bothNet y \<Longrightarrow> 
    OnlyTwoNets (separate (a \<oplus> y # z))"
  apply (drule mp)
   apply simp_all
  apply (rule conjI)
   apply (rule otnaux)
       apply simp_all
   apply (rule_tac p = "(y # z)" in OTNoTN)
     apply simp_all
   apply (metis member.simps(2))
  apply (simp add: onlyTwoNets_def)
  apply (rule_tac y = y in OTNConc,simp)
  done
    
lemma OTNSEp[rule_format]: 
  "noDenyAll1 p \<longrightarrow> OnlyTwoNets p  \<longrightarrow>  OnlyTwoNets (separate p)"
  apply (induct p rule: separate.induct)  
  by (simp_all add: OTNSepaux noDA1eq)
    
lemma nda[rule_format]: 
  "singleCombinators (a#p) \<longrightarrow> noDenyAll p \<longrightarrow> noDenyAll1 (a # p)"
  apply (induct p,simp_all)
   apply (case_tac a, simp_all)+
  done
    
lemma nDAcharn[rule_format]: "noDenyAll p = (\<forall> r \<in> set p. \<not> member DenyAll r)"
  by (induct p, simp_all)
    
lemma nDAeqSet: "set p = set s \<Longrightarrow> noDenyAll p = noDenyAll s"
  by (simp add: nDAcharn)
    
lemma nDASCaux[rule_format]: 
  "DenyAll \<notin> set p \<longrightarrow> singleCombinators p \<longrightarrow>  r \<in> set p \<longrightarrow>  \<not> member DenyAll r"
  apply (case_tac r, simp_all) 
  using SCnotConc by blast
    
    
lemma nDASC[rule_format]: 
  "wellformed_policy1 p \<longrightarrow> singleCombinators p \<longrightarrow>  noDenyAll1 p"
  apply (induct p, simp_all)
  using nDASCaux nDAcharn nda singleCombinatorsConc by blast
    
lemma noDAAll[rule_format]: "noDenyAll p = (\<not> memberP DenyAll p)"
  by (induct p) simp_all
    
lemma memberPsep[symmetric]: "memberP x p = memberP x (separate p)"
  by (induct p rule: separate.induct)  simp_all
    
lemma noDAsep[rule_format]: "noDenyAll p \<Longrightarrow> noDenyAll (separate p)"
  by (simp add:noDAAll,subst memberPsep, simp)
    
lemma noDA1sep[rule_format]: "noDenyAll1 p \<longrightarrow> noDenyAll1 (separate p)"
  by (induct p rule:separate.induct, simp_all add: noDAsep)
    
lemma isInAlternativeLista: 
  "(aa \<in> set (net_list_aux [a]))\<Longrightarrow>  aa \<in> set (net_list_aux (a # p))"
  by (case_tac a,auto)
    
lemma isInAlternativeListb: 
  "(aa \<in> set (net_list_aux p))\<Longrightarrow>  aa \<in> set (net_list_aux (a # p))"
  by (case_tac a,simp_all)
    
lemma ANDSepaux: "allNetsDistinct (x # y # z) \<Longrightarrow> allNetsDistinct (x \<oplus> y # z)"
  apply (simp add: allNetsDistinct_def)
  apply (intro allI impI, rename_tac a b)
  subgoal for a b
    apply (drule_tac x = a in spec, drule_tac x = b in spec)
    by (meson isInAlternativeList)
  done
    
lemma netlistalternativeSeparateaux:
  "net_list_aux [y] @ net_list_aux z = net_list_aux (y # z)"
  by (case_tac y, simp_all)
    
lemma netlistalternativeSeparate: "net_list_aux p = net_list_aux (separate p)"
  by (induct p rule:separate.induct, simp_all) (simp_all add: netlistalternativeSeparateaux)
    
lemma  ANDSepaux2: 
  "allNetsDistinct(x#y#z) \<Longrightarrow> allNetsDistinct(separate(y#z)) \<Longrightarrow> allNetsDistinct(x#separate(y#z))"
  apply (simp add: allNetsDistinct_def)
  by (metis isInAlternativeList netlistalternativeSeparate netlistaux)
    
lemma ANDSep[rule_format]: "allNetsDistinct p \<longrightarrow> allNetsDistinct(separate p)"
  apply (induct p rule: separate.induct, simp_all) 
     apply (metis ANDConc aNDDA)
    apply (metis ANDConc ANDSepaux ANDSepaux2)
   apply (metis ANDConc ANDSepaux ANDSepaux2)
  apply (metis ANDConc ANDSepaux ANDSepaux2)
  done
    
lemma wp1_alternativesep[rule_format]: 
  "wellformed_policy1_strong p \<longrightarrow> wellformed_policy1_strong (separate p)"
  by (metis sepDA separate.simps(1) wellformed_policy1_strong.simps(2) wp1n_tl)
    
    
lemma noDAsort[rule_format]: "noDenyAll1 p \<longrightarrow> noDenyAll1 (sort p l)"
  apply (case_tac "p",simp_all)
  subgoal for a as
    apply (case_tac "a = DenyAll", auto) 
    using NormalisationGenericProofs.set_sort nDAeqSet apply blast
  proof -
    fix a::"('a,'b)Combinators" fix list 
    have * : "a \<noteq> DenyAll \<Longrightarrow> noDenyAll1 (a # list) \<Longrightarrow> noDenyAll (a#list)" by (case_tac a, simp_all)
    show "a \<noteq> DenyAll \<Longrightarrow> noDenyAll1 (a # list) \<Longrightarrow> noDenyAll1 (insort a (sort list l) l)"
      apply(cases "insort a (sort list l) l", simp_all)
      by (metis "*" NormalisationGenericProofs.set_insort NormalisationGenericProofs.set_sort 
          list.simps(15) nDAeqSet noDA1eq)
  qed
  done
  
lemma OTNSC[rule_format]: "singleCombinators p \<longrightarrow> OnlyTwoNets p"
  apply (induct p,simp_all)
  apply (rename_tac a p)
  apply (rule impI,drule mp)
   apply (erule singleCombinatorsConc)
  subgoal for a b
    apply (case_tac a, simp_all)
     apply (simp add: onlyTwoNets_def)+
    done
  done
    
lemma fMTaux: "\<not> member DenyAll x \<Longrightarrow> first_bothNet x \<noteq> {}"
  by (metis first_bothNetsd insert_commute insert_not_empty)
    
lemma fl2[rule_format]: "firstList (separate p) = firstList p"
  by (rule separate.induct) simp_all
    
    
lemma fl3[rule_format]: "NetsCollected p \<longrightarrow> (first_bothNet x \<noteq> firstList p \<longrightarrow>
          (\<forall>a\<in>set p. first_bothNet x \<noteq> first_bothNet a))\<longrightarrow> NetsCollected (x#p)"
  by (induct p) simp_all
        
lemma sortedConc[rule_format]: " sorted (a # p) l \<longrightarrow>  sorted p l"
  by (induct p) simp_all
    
lemma smalleraux2: 
  "{a,b} \<in> set l \<Longrightarrow> {c,d} \<in> set l \<Longrightarrow> {a,b} \<noteq> {c,d} \<Longrightarrow> 
   smaller (DenyAllFromTo a b) (DenyAllFromTo c d) l \<Longrightarrow> 
  \<not> smaller (DenyAllFromTo c d) (DenyAllFromTo a b) l"
  by (metis bothNet.simps(2) pos_noteq smaller.simps(5))
    
lemma smalleraux2a: 
  "{a,b} \<in> set l \<Longrightarrow> {c,d} \<in> set l \<Longrightarrow> {a,b} \<noteq> {c,d} \<Longrightarrow> 
   smaller (DenyAllFromTo a b) (AllowPortFromTo c d p) l \<Longrightarrow> 
  \<not> smaller (AllowPortFromTo c d p) (DenyAllFromTo a b) l"
  by (simp) (metis eq_imp_le pos_noteq)
    
lemma smalleraux2b: 
  "{a,b} \<in> set l \<Longrightarrow> {c,d} \<in> set l \<Longrightarrow> {a,b} \<noteq> {c,d} \<Longrightarrow> y = DenyAllFromTo a b \<Longrightarrow>
   smaller (AllowPortFromTo  c d p) y l \<Longrightarrow> 
  \<not> smaller y (AllowPortFromTo  c d p) l"
  by (simp) (metis eq_imp_le pos_noteq)
    
lemma smalleraux2c: 
  "{a,b} \<in> set l\<Longrightarrow>{c,d}\<in>set l\<Longrightarrow>{a,b} \<noteq> {c,d} \<Longrightarrow> y = AllowPortFromTo a b q \<Longrightarrow> 
    smaller (AllowPortFromTo  c d p) y l \<Longrightarrow> \<not> smaller y (AllowPortFromTo  c d p) l"
  by (simp) (metis pos_noteq)
    
lemma smalleraux3: 
  assumes "x \<in> set l" and " y \<in> set l" and "x \<noteq> y" and "x = bothNet a" and "y = bothNet b"
    and "smaller a b l" and "singleCombinators [a]" and "singleCombinators [b]"  
  shows "\<not> smaller b a l"
proof (cases a)
  case DenyAll thus ?thesis using assms by (case_tac b,simp_all)  
next
  case (DenyAllFromTo c d) thus ?thesis 
  proof (cases b)
    case DenyAll thus ?thesis using assms DenyAll DenyAllFromTo by simp
  next
    case (DenyAllFromTo e f) thus ?thesis using assms  DenyAllFromTo  
      by (metis DenyAllFromTo \<open>a = DenyAllFromTo c d\<close>  bothNet.simps(2) smalleraux2)
  next
    case (AllowPortFromTo e f g) thus ?thesis 
      using assms DenyAllFromTo AllowPortFromTo by simp (metis eq_imp_le pos_noteq)
  next
    case (Conc e f) thus ?thesis using assms by simp
  qed
next
  case (AllowPortFromTo c d p) thus ?thesis
  proof (cases b)
    case DenyAll thus ?thesis using assms AllowPortFromTo DenyAll by simp
  next
    case (DenyAllFromTo e f) thus ?thesis 
      using assms by simp (metis AllowPortFromTo DenyAllFromTo bothNet.simps(3) smalleraux2a)
  next
    case (AllowPortFromTo e f g) thus ?thesis 
      using assms by(simp)(metis AllowPortFromTo \<open>a = AllowPortFromTo c d p\<close> 
          bothNet.simps(3) smalleraux2c)
  next
    case (Conc e f) thus ?thesis using assms by simp
  qed
next
  case (Conc c d) thus ?thesis using assms by simp
qed
  
lemma smalleraux3a: 
  "a \<noteq> DenyAll \<Longrightarrow> b \<noteq> DenyAll \<Longrightarrow> in_list b l \<Longrightarrow> in_list a l \<Longrightarrow>  
   bothNet a \<noteq> bothNet b \<Longrightarrow> smaller a b l \<Longrightarrow> singleCombinators [a] \<Longrightarrow>
    singleCombinators [b] \<Longrightarrow> \<not> smaller b a l"
  apply (rule smalleraux3,simp_all)
   apply (case_tac a, simp_all)
  apply (case_tac b, simp_all)
  done
    
lemma posaux[rule_format]: "position a l < position b l \<longrightarrow> a \<noteq> b"
  by (induct l, simp_all)
    
lemma posaux6[rule_format]: 
  "a \<in> set l \<longrightarrow> b \<in> set l \<longrightarrow> a \<noteq> b \<longrightarrow> position a l \<noteq>  position b l"
  by (induct l) (simp_all add: position_positive)
    
lemma notSmallerTransaux[rule_format]: 
  "x \<noteq> DenyAll \<Longrightarrow> r \<noteq> DenyAll \<Longrightarrow>
  singleCombinators [x] \<Longrightarrow>  singleCombinators [y] \<Longrightarrow>  singleCombinators [r] \<Longrightarrow>
  \<not> smaller y x l \<Longrightarrow> smaller x y l \<Longrightarrow> smaller x r l \<Longrightarrow> smaller y r l \<Longrightarrow> 
   in_list x l \<Longrightarrow> in_list y l \<Longrightarrow> in_list r l \<Longrightarrow> \<not> smaller r x l"
  by (metis order_trans)
    
lemma notSmallerTrans[rule_format]: 
  "x \<noteq> DenyAll \<longrightarrow> r \<noteq> DenyAll \<longrightarrow> singleCombinators (x#y#z) \<longrightarrow> 
  \<not> smaller y x l \<longrightarrow> sorted (x#y#z) l \<longrightarrow> r \<in> set z \<longrightarrow> 
  all_in_list (x#y#z) l \<longrightarrow> \<not> smaller r x l"
  apply (rule impI)+
  apply (rule notSmallerTransaux, simp_all)
        apply (metis singleCombinatorsConc singleCombinatorsStart)
       apply (metis SCSubset equalityE remdups.simps(2) set_remdups
                    singleCombinatorsConc singleCombinatorsStart)
      apply metis
     apply (metis sorted.simps(3) in_set_in_list singleCombinatorsConc
                  singleCombinatorsStart sortedConcStart sorted_is_smaller)
    apply (metis sorted_Cons all_in_list.simps(2)
                 singleCombinatorsConc)
   apply (metis,metis in_set_in_list)
  done
    
lemma  NCSaux1[rule_format]:
  "noDenyAll p \<longrightarrow> {x, y} \<in> set l \<longrightarrow>  all_in_list p l\<longrightarrow> singleCombinators p \<longrightarrow> 
  sorted (DenyAllFromTo x y # p) l \<longrightarrow> {x, y} \<noteq> firstList p \<longrightarrow>
  DenyAllFromTo u v \<in> set p \<longrightarrow> {x, y} \<noteq> {u, v}"
proof (cases p)
  case Nil thus ?thesis by simp 
next
  case (Cons a list) 
  then show ?thesis apply simp
    apply (intro impI conjI)
     apply (metis bothNet.simps(2) first_bothNet.simps(3))
  proof -
    assume 1: "{x, y} \<in> set l" and 2: "in_list a l \<and> all_in_list list l"
      and 3 : "singleCombinators (a # list)"
      and 4 : "smaller (DenyAllFromTo x y) a l \<and> sorted (a # list) l"
      and 5 : "DenyAllFromTo u v \<in> set list"
      and 6 : "\<not> member DenyAll a \<and> noDenyAll list"
    have * : "smaller ((DenyAllFromTo x y)::(('a,'b)Combinators)) (DenyAllFromTo u v) l" 
      apply (insert 1 2 3 4 5, rule_tac y = a in order_trans, simp_all)
      using in_set_in_list apply fastforce
      by (simp add: sorted_ConsA)
        
    have ** :"{x, y} \<noteq> first_bothNet a \<Longrightarrow>  
                       \<not> smaller ((DenyAllFromTo u v)::('a, 'b) Combinators) (DenyAllFromTo x y) l" 
      apply (insert 1 2 3 4 5 6, 
          rule_tac y = "a" and z = "list"  in  notSmallerTrans, 
          simp_all del: smaller.simps)
      apply (rule smalleraux3a,simp_all del: smaller.simps)
       apply (case_tac a, simp_all del: smaller.simps)
      by (metis aux0_0 first_bothNet.elims list.set_intros(1))
    show " {x, y} \<noteq> first_bothNet a \<Longrightarrow>  {x, y} \<noteq> {u, v}"
      using  3  "*" "**" by force
  qed
qed
  
lemma posaux3[rule_format]:"a \<in> set l \<longrightarrow> b \<in> set l \<longrightarrow> a \<noteq> b \<longrightarrow> position a l \<noteq> position b l"
  apply (induct l, auto)
  by(metis position_positive)+
    
lemma posaux4[rule_format]: 
  "singleCombinators [a] \<longrightarrow> a\<noteq> DenyAll \<longrightarrow> b \<noteq> DenyAll \<longrightarrow> in_list a l \<longrightarrow>in_list b l \<longrightarrow>
    smaller a b  l\<longrightarrow> x = (bothNet a) \<longrightarrow>  y = (bothNet b) \<longrightarrow> 
    position x l <= position y l"
proof (cases a) 
  case DenyAll then show ?thesis by simp
next
  case (DenyAllFromTo c d) thus ?thesis
  proof (cases b)
    case DenyAll thus ?thesis by simp 
  next
    case (DenyAllFromTo e f) thus ?thesis using  DenyAllFromTo
      by (auto simp: eq_imp_le  \<open>a = DenyAllFromTo c d\<close>)
  next
    case (AllowPortFromTo e f p) thus ?thesis using \<open>a = DenyAllFromTo c d\<close> by simp 
  next
    case (Conc e f) thus ?thesis using Conc \<open>a = DenyAllFromTo c d\<close> by simp
  qed
next
  case (AllowPortFromTo c d p) thus ?thesis
  proof (cases b)
    case DenyAll thus ?thesis by simp 
  next
    case (DenyAllFromTo e f) thus ?thesis using AllowPortFromTo by simp 
  next
    case (AllowPortFromTo e f p2) thus ?thesis using \<open>a = AllowPortFromTo c d p\<close> by simp 
  next
    case (Conc e f) thus ?thesis using AllowPortFromTo by simp
  qed
next
  case (Conc c d) thus ?thesis by simp
qed
  
lemma  NCSaux2[rule_format]:
  "noDenyAll p \<longrightarrow> {a, b} \<in> set l \<longrightarrow> all_in_list p l \<longrightarrow>singleCombinators p \<longrightarrow>
   sorted (DenyAllFromTo a b # p) l \<longrightarrow> {a, b} \<noteq> firstList p \<longrightarrow>
   AllowPortFromTo u v w \<in> set p \<longrightarrow>  {a, b} \<noteq> {u, v}"
proof (cases p) 
  case Nil then show ?thesis by simp
next
  case (Cons aa list) 
  have *  : "{a, b} \<in> set l \<Longrightarrow>  in_list aa l \<and> all_in_list list l \<Longrightarrow>
                   singleCombinators (aa # list) \<Longrightarrow>  AllowPortFromTo u v w \<in> set list \<Longrightarrow> 
                   smaller (DenyAllFromTo a b) aa l \<and> sorted (aa # list) l \<Longrightarrow>
                   smaller (DenyAllFromTo a b) (AllowPortFromTo u v w) l" 
    apply (rule_tac y = aa in order_trans,simp_all del: smaller.simps)
    using in_set_in_list apply fastforce
    using NormalisationGenericProofs.sorted_Cons all_in_list.simps(2) by blast                   
  have **: "AllowPortFromTo u v w \<in> set list \<Longrightarrow>
                    in_list aa l \<Longrightarrow>   all_in_list list l \<Longrightarrow> 
                    in_list (AllowPortFromTo u v w) l"
    apply (rule_tac p = list in in_set_in_list)
     apply simp_all
    done
  assume  "p = aa # list" 
  then show ?thesis 
    apply simp
    apply (intro impI conjI,hypsubst, simp)
    apply (subgoal_tac "smaller (DenyAllFromTo a b) (AllowPortFromTo u v w) l")
     apply (subgoal_tac "\<not> smaller (AllowPortFromTo u v w) (DenyAllFromTo a b) l")
      apply (rule_tac l = l in posaux) 
      apply (rule_tac y = "position (first_bothNet aa) l" in basic_trans_rules(22))
       apply (simp_all split: if_splits)
         apply (case_tac aa, simp_all)
    subgoal for x x'
      apply (case_tac "a = x \<and> b = x'", simp_all)
      apply (case_tac "a = x", simp_all)
       apply (simp add: order.not_eq_order_implies_strict posaux6)
      apply (simp add: order.not_eq_order_implies_strict posaux6)
      done
         apply (simp add: order.not_eq_order_implies_strict posaux6)  
        apply (rule basic_trans_rules(18))
         apply (rule_tac a = "DenyAllFromTo a b" and b = aa in posaux4, simp_all)
          apply (case_tac aa,simp_all)
         apply (case_tac aa, simp_all)
        apply (rule posaux3, simp_all)
        apply (case_tac aa, simp_all)
       apply (rule_tac a = aa and b = "AllowPortFromTo u v w" in posaux4, simp_all)
         apply (case_tac aa,simp_all)
        apply (rule_tac p = list in sorted_is_smaller, simp_all)
        apply (case_tac aa, simp_all)
       apply (case_tac aa, simp_all)
      apply (rule_tac a = aa and b = "AllowPortFromTo u v w" in posaux4, simp_all)
         apply (case_tac aa,simp_all)
    using ** apply auto[1]       
       apply (metis all_in_list.simps(2) sorted_Cons)
      apply (case_tac aa, simp_all)
     apply (metis ** bothNet.simps(3) in_list.simps(3) posaux6)
    using * by force  
qed
  
lemma  NCSaux3[rule_format]:
  "noDenyAll p \<longrightarrow> {a, b} \<in> set l \<longrightarrow>  all_in_list p l \<longrightarrow>singleCombinators p \<longrightarrow> 
  sorted (AllowPortFromTo a b w # p) l \<longrightarrow> {a, b} \<noteq> firstList p \<longrightarrow>
  DenyAllFromTo u v \<in> set p \<longrightarrow> {a, b} \<noteq> {u, v}"
  apply (case_tac p, simp_all,intro impI conjI,hypsubst,simp)
proof -
  fix aa::"('a, 'b) Combinators" fix list::"('a, 'b) Combinators list"
  assume 1 : "\<not> member DenyAll aa \<and> noDenyAll list" and 2: "{a, b} \<in> set l "
    and  3 : "in_list aa l \<and> all_in_list list l" and 4: "singleCombinators (aa # list)"
    and  5 : "smaller (AllowPortFromTo a b w) aa l \<and> sorted (aa # list) l"
    and  6 : "{a, b} \<noteq> first_bothNet aa" and 7: "DenyAllFromTo u v \<in> set list"
  have *: "\<not> smaller (DenyAllFromTo u v) (AllowPortFromTo a b w) l"
    apply (insert 1 2 3 4 5 6 7, rule_tac y = aa and z = list in notSmallerTrans)
          apply (simp_all del: smaller.simps)
    apply (rule smalleraux3a,simp_all del: smaller.simps)
     apply (case_tac aa, simp_all del: smaller.simps)
    apply (case_tac aa, simp_all del: smaller.simps)
    done
  have **: "smaller (AllowPortFromTo a b w) (DenyAllFromTo u v) l"        
    apply (insert 1 2 3 4 5 6 7,rule_tac y = aa in order_trans,simp_all del: smaller.simps)
     apply (subgoal_tac "in_list (DenyAllFromTo u v) l", simp)
     apply (rule_tac p = list in in_set_in_list, simp_all)
    apply (rule_tac p = list in sorted_is_smaller,simp_all del: smaller.simps)
     apply (subgoal_tac "in_list (DenyAllFromTo u v) l", simp)
    apply (rule_tac p = list in in_set_in_list, simp_all)
    apply (erule singleCombinatorsConc)
    done
  show       "{a, b} \<noteq> {u, v}" by (insert * **, simp split: if_splits)
qed
  
lemma  NCSaux4[rule_format]:
  "noDenyAll p \<longrightarrow> {a, b} \<in> set l \<longrightarrow>  all_in_list p l \<longrightarrow> singleCombinators p \<longrightarrow> 
 sorted (AllowPortFromTo a b c # p) l \<longrightarrow> {a, b} \<noteq> firstList p \<longrightarrow>
 AllowPortFromTo u v w \<in> set p \<longrightarrow> {a, b} \<noteq> {u, v}"
  apply (cases p, simp_all)
  apply (intro impI conjI)
   apply (hypsubst,simp_all)
proof -
  fix aa::"('a, 'b) Combinators" fix list::"('a, 'b) Combinators list"
  assume 1 : "\<not> member DenyAll aa \<and> noDenyAll list" and 2: "{a, b} \<in> set l "
    and  3 : "in_list aa l \<and> all_in_list list l" and 4: "singleCombinators (aa # list)"
    and  5 : "smaller (AllowPortFromTo a b c) aa l \<and> sorted (aa # list) l"
    and  6 : "{a, b} \<noteq> first_bothNet aa" and 7: "AllowPortFromTo u v w \<in> set list"
  have *: "\<not> smaller (AllowPortFromTo u v w) (AllowPortFromTo a b c) l"
    apply (insert 1 2 3 4 5 6 7, rule_tac y = aa and z = list in notSmallerTrans)
          apply (simp_all del: smaller.simps)
    apply (rule smalleraux3a,simp_all del: smaller.simps)
     apply (case_tac aa, simp_all del: smaller.simps)
    apply (case_tac aa, simp_all del: smaller.simps)
    done
  have **: "smaller (AllowPortFromTo a b c) (AllowPortFromTo u v w) l"        
    apply(insert 1 2 3 4 5 6 7)
    apply (case_tac aa, simp_all del: smaller.simps)
     apply (rule_tac y = aa in order_trans,simp_all del: smaller.simps)
      apply (subgoal_tac "in_list (AllowPortFromTo u v w) l", simp)
      apply (rule_tac p = list in in_set_in_list, simp)
      apply (case_tac aa, simp_all del: smaller.simps)
     apply (rule_tac p = list in sorted_is_smaller,simp_all del: smaller.simps)
     apply (subgoal_tac "in_list (AllowPortFromTo u v w) l", simp)
     apply (rule_tac p = list in in_set_in_list, simp, simp)
    apply (rule_tac y = aa in order_trans,simp_all del: smaller.simps)
     apply (subgoal_tac "in_list (AllowPortFromTo u v w) l", simp)
    using in_set_in_list apply blast
    by (metis all_in_list.simps(2) bothNet.simps(3) in_list.simps(3) 
        singleCombinators.simps(5) sorted_ConsA)
  show       "{a, b} \<noteq> {u, v}"  by (insert * **, simp_all split: if_splits)
qed

lemma NetsCollectedSorted[rule_format]: 
  "noDenyAll1 p \<longrightarrow> all_in_list p l \<longrightarrow> singleCombinators p \<longrightarrow> sorted p l \<longrightarrow>  NetsCollected p"
  apply (induct p)
   apply simp
  apply (intro impI,drule mp,erule noDA1C,drule mp,simp)
  apply (drule mp,erule singleCombinatorsConc)
  apply (drule mp,erule sortedConc) 
proof -
  fix a::" ('a, 'b) Combinators" fix p:: " ('a, 'b) Combinators list" 
  assume 1: "noDenyAll1 (a # p)"        and 2:"all_in_list (a # p) l" 
    and  3: "singleCombinators (a # p)" and 4: "sorted (a # p) l"  and   5: "NetsCollected p"
  show "NetsCollected (a # p)"
    apply(insert 1 2 3 4 5, rule fl3)
     apply(simp, rename_tac "aa")
  proof (cases a)
    case DenyAll
    fix aa::"('a, 'b) Combinators" 
    assume 6: "aa \<in> set p" 
    show "first_bothNet a \<noteq> first_bothNet aa"
      apply(insert 1 2 3 4 5 6 \<open>a = DenyAll\<close>, simp_all)
      using fMTaux noDA by blast
  next
    case (DenyAllFromTo x21 x22)
    fix aa::"('a, 'b) Combinators"
    assume 6: "first_bothNet a \<noteq> firstList p" and 7 :"aa \<in> set p"                
    show "first_bothNet a \<noteq> first_bothNet aa"
      apply(insert 1 2 3 4 5 6 7 \<open>a = DenyAllFromTo x21 x22\<close>)
      apply(case_tac aa, simp_all)
        apply (meson NCSaux1)
       apply (meson NCSaux2)
      using SCnotConc by auto[1]
  next
    case (AllowPortFromTo x31 x32 x33) 
    fix aa::"('a, 'b) Combinators" 
    assume 6: "first_bothNet a \<noteq> firstList p" and 7 :"aa \<in> set p"                
    show "first_bothNet a \<noteq> first_bothNet aa"
      apply(insert 1 2 3 4 6 7 \<open>a = AllowPortFromTo x31 x32 x33\<close>)
      apply(case_tac aa, simp_all)
        apply (meson NCSaux3)
       apply (meson NCSaux4)
      using SCnotConc by auto
  next
    case (Conc x41 x42) 
    fix aa::"('a, 'b) Combinators"
    show "first_bothNet a \<noteq> first_bothNet aa"
      by(insert 3 4   \<open>a = x41 \<oplus> x42\<close>,simp)
  qed
qed
  
lemma NetsCollectedSort: "distinct p \<Longrightarrow>noDenyAll1 p \<Longrightarrow> all_in_list p l \<Longrightarrow>
                          singleCombinators p \<Longrightarrow> NetsCollected (sort p l)"
  apply (rule_tac l = l in NetsCollectedSorted,rule noDAsort, simp_all)
   apply (rule_tac b=p in all_in_listSubset)
  by (auto intro: sort_is_sorted)
    
lemma fBNsep[rule_format]: "(\<forall>a\<in>set z. {b,c} \<noteq> first_bothNet a) \<longrightarrow>
                           (\<forall>a\<in>set (separate z). {b,c} \<noteq> first_bothNet a)"
  apply (induct z rule: separate.induct, simp)
  by (rule impI, simp)+
    
lemma fBNsep1[rule_format]: " (\<forall>a\<in>set z. first_bothNet x \<noteq> first_bothNet a) \<longrightarrow>
                        (\<forall>a\<in>set (separate z). first_bothNet x \<noteq> first_bothNet a)"
  apply (induct z rule: separate.induct, simp)
  by (rule impI, simp)+
    
lemma NetsCollectedSepauxa:
  "{b,c}\<noteq>firstList z \<Longrightarrow>  noDenyAll1 z \<Longrightarrow> \<forall>a\<in>set z. {b,c}\<noteq>first_bothNet a \<Longrightarrow> NetsCollected z \<Longrightarrow>  
   NetsCollected (separate z) \<Longrightarrow> {b, c} \<noteq> firstList (separate z) \<Longrightarrow>   a \<in> set (separate z) \<Longrightarrow> 
   {b, c} \<noteq> first_bothNet a"
  by (rule fBNsep) simp_all
    
lemma NetsCollectedSepaux:
  "first_bothNet (x::('a,'b)Combinators) \<noteq> first_bothNet y \<Longrightarrow> \<not> member DenyAll y \<and> noDenyAll z \<Longrightarrow>  
   (\<forall>a\<in>set z. first_bothNet x \<noteq> first_bothNet a) \<and> NetsCollected (y # z) \<Longrightarrow>
   NetsCollected (separate (y # z)) \<Longrightarrow> first_bothNet x \<noteq> firstList (separate (y # z)) \<Longrightarrow>
   a \<in> set (separate (y # z)) \<Longrightarrow>
   first_bothNet (x::('a,'b)Combinators) \<noteq> first_bothNet (a::('a,'b)Combinators)"
  by (rule fBNsep1) auto
    
    
lemma NetsCollectedSep[rule_format]: 
  "noDenyAll1 p \<longrightarrow> NetsCollected p \<longrightarrow>  NetsCollected (separate p)"
proof (induct p rule: separate.induct, simp_all, goal_cases)
  fix x::"('a, 'b) Combinators list" 
  case 1 then show ?case
    by (metis fMTaux noDA noDA1eq noDAsep)
next
  fix v va y fix z::"('a, 'b) Combinators list"
  case 2 then show ?case 
    apply (intro conjI impI, simp)
     apply (metis NetsCollectedSepaux fl3 noDA1eq noDenyAll.simps(1))
    by (metis noDA1eq noDenyAll.simps(1))
next 
  fix v va vb y fix z::"('a, 'b) Combinators list"
  case 3 then show ?case 
    apply (intro conjI impI)
     apply (metis NetsCollectedSepaux fl3 noDA1eq noDenyAll.simps(1))
    by (metis noDA1eq noDenyAll.simps(1))
next 
  fix v va y fix z::"('a, 'b) Combinators list"
  case 4 then show ?case 
    by (metis NetsCollectedSepaux fl3 noDA1eq noDenyAll.simps(1))
qed
  
lemma OTNaux: 
  "onlyTwoNets a \<Longrightarrow> \<not> member DenyAll a \<Longrightarrow> (x,y) \<in> sdnets a \<Longrightarrow> 
   (x = first_srcNet a \<and> y = first_destNet a) \<or>   (x = first_destNet a \<and> y = first_srcNet a)"
  apply (case_tac "(x = first_srcNet a \<and> y = first_destNet a)",simp_all add: onlyTwoNets_def)
  apply (case_tac "(\<exists>aa b. sdnets a = {(aa, b)})", simp_all)
   apply (subgoal_tac "sdnets a = {(first_srcNet a,first_destNet a)}", simp_all)
   apply (metis singletonE first_isIn)
  apply (subgoal_tac"sdnets a = {(first_srcNet a,first_destNet a),(first_destNet a, first_srcNet a)}")
  by(auto intro!: sdnets2)
    
lemma sdnets_charn: "onlyTwoNets a \<Longrightarrow> \<not> member DenyAll a \<Longrightarrow>
sdnets a = {(first_srcNet a,first_destNet a)} \<or> 
sdnets a = {(first_srcNet a, first_destNet a),(first_destNet a, first_srcNet a)}"
  apply (case_tac "sdnets a = {(first_srcNet a, first_destNet a)}", simp_all add: onlyTwoNets_def)
  apply (case_tac "(\<exists>aa b. sdnets a = {(aa, b)})", simp_all)
   apply (metis singletonE first_isIn)
  apply (subgoal_tac "sdnets a = {(first_srcNet a,first_destNet a),(first_destNet a,first_srcNet a)}")
  by( auto intro!: sdnets2)
    
lemma first_bothNet_charn[rule_format]: 
  "\<not> member DenyAll a \<longrightarrow> first_bothNet a = {first_srcNet a, first_destNet a}"
  by (induct a) simp_all
    
    
lemma sdnets_noteq:
  "onlyTwoNets a \<Longrightarrow> onlyTwoNets aa \<Longrightarrow> first_bothNet a \<noteq> first_bothNet aa \<Longrightarrow> 
   \<not> member DenyAll a \<Longrightarrow> \<not> member DenyAll aa \<Longrightarrow> sdnets a \<noteq> sdnets aa"
  apply (insert sdnets_charn [of a])
  apply (insert sdnets_charn [of aa])
  apply (insert first_bothNet_charn [of a])
  apply (insert first_bothNet_charn [of aa])
  by(metis OTNaux first_isIn insert_absorb2 insert_commute)

lemma fbn_noteq: 
  "onlyTwoNets a \<Longrightarrow>  onlyTwoNets aa \<Longrightarrow>  first_bothNet a \<noteq> first_bothNet aa \<Longrightarrow>
    \<not> member DenyAll a \<Longrightarrow>  \<not> member DenyAll aa \<Longrightarrow>  allNetsDistinct [a, aa] \<Longrightarrow>
    first_srcNet a \<noteq> first_srcNet aa \<or> first_srcNet a \<noteq> first_destNet aa \<or> 
    first_destNet a \<noteq> first_srcNet aa \<or> first_destNet a \<noteq> first_destNet aa" 
  apply (insert sdnets_charn [of a])
  apply (insert sdnets_charn [of aa])
  by (metis first_bothNet_charn)    
    
lemma NCisSD2aux: 
  assumes 1: "onlyTwoNets a" and 2 : "onlyTwoNets aa" and 3 : "first_bothNet a \<noteq> first_bothNet aa"
    and   4: "\<not> member DenyAll a" and 5: "\<not> member DenyAll aa" and 6:" allNetsDistinct [a, aa]"
  shows   "disjSD_2 a aa"
  apply (insert 1 2 3 4 5 6) 
  apply (simp add: disjSD_2_def)
  apply (intro allI impI)
  apply (insert sdnets_charn [of a]  sdnets_charn [of aa], simp)
  apply (insert sdnets_noteq [of a aa]  fbn_noteq [of a aa], simp)
  apply (simp add: allNetsDistinct_def twoNetsDistinct_def)
proof -
  fix ab b c d
  assume 7: "\<forall>ab b. ab\<noteq>b \<and> ab\<in>set(net_list_aux[a,aa]) \<and> b\<in>set(net_list_aux [a,aa]) \<longrightarrow> netsDistinct ab b"
    and    8: "(ab, b) \<in> sdnets a \<and> (c, d) \<in> sdnets aa "
    and    9: "sdnets a = {(first_srcNet a, first_destNet a)} \<or>
              sdnets a = {(first_srcNet a, first_destNet a), (first_destNet a, first_srcNet a)} "
    and   10: "sdnets aa = {(first_srcNet aa, first_destNet aa)} \<or>
              sdnets aa = {(first_srcNet aa, first_destNet aa), (first_destNet aa, first_srcNet aa)}"
    and   11: "sdnets a \<noteq> sdnets aa "
    and   12: "first_destNet a = first_srcNet aa \<longrightarrow> first_srcNet a = first_destNet aa \<longrightarrow> 
              first_destNet aa \<noteq> first_srcNet aa"
  show      "(netsDistinct ab c \<or> netsDistinct b d) \<and> (netsDistinct ab d \<or> netsDistinct b c)"
    
  proof (rule conjI)
    show "netsDistinct ab c \<or> netsDistinct b d"         
      apply(insert       7 8 9 10 11 12)
      apply (cases "sdnets a = {(first_srcNet a, first_destNet a)}")
       apply (cases "sdnets aa = {(first_srcNet aa, first_destNet aa)}", simp_all)
        apply (metis 4 5 firstInNeta firstInNet alternativelistconc2)
       apply (case_tac "(c = first_srcNet aa \<and> d = first_destNet aa)", simp_all)
        apply (case_tac "(first_srcNet a) \<noteq> (first_srcNet aa)",simp_all)
         apply (metis 4 5 firstInNeta alternativelistconc2)
        apply (subgoal_tac "first_destNet a \<noteq> first_destNet aa") 
         apply (metis 4 5 firstInNet alternativelistconc2)
        apply (metis 3 4 5 first_bothNetsd)
       apply (case_tac "(first_destNet aa) \<noteq> (first_srcNet a)",simp_all)
        apply (metis 4 5 firstInNeta firstInNet alternativelistconc2)
       apply (case_tac "first_destNet aa \<noteq> first_destNet a",simp_all)
        apply (subgoal_tac "first_srcNet aa \<noteq> first_destNet a")
         apply (metis 4 5 firstInNeta firstInNet alternativelistconc2)
        apply (metis 3 4 5 first_bothNetsd insert_commute)
       apply (metis 5 firstInNeta firstInNet alternativelistconc2)
      apply (case_tac "(c = first_srcNet aa \<and> d = first_destNet aa)", simp_all)
       apply (case_tac "(ab = first_srcNet a \<and> b = first_destNet a)", simp_all)
        apply (case_tac "(first_srcNet a) \<noteq> (first_srcNet aa)",simp_all)
         apply (metis 4 5 firstInNeta alternativelistconc2)
        apply (subgoal_tac "first_destNet a \<noteq> first_destNet aa")
         apply (metis  4 5 firstInNet alternativelistconc2)
        apply (metis 3 4 5 first_bothNetsd )
       apply (case_tac "(first_destNet aa) \<noteq> (first_srcNet a)",simp_all)
        apply (metis 4 5 firstInNeta firstInNet alternativelistconc2)
       apply (case_tac "first_destNet aa \<noteq> first_destNet a", simp)
        apply (subgoal_tac "first_srcNet aa \<noteq> first_destNet a")
         apply (metis 4 5 firstInNeta firstInNet alternativelistconc2)
        apply (metis 3 4 5 first_bothNetsd insert_commute)
       apply (metis)        
    proof - 
      assume  14 : "(ab = first_srcNet a \<and> b = first_destNet a \<or> ab = first_destNet a \<and> b = first_srcNet a) \<and> (c, d) \<in> sdnets aa "
        and     15 : "sdnets a = {(first_srcNet a, first_destNet a), (first_destNet a, first_srcNet a)} "
        and     16 : "sdnets aa = {(first_srcNet aa, first_destNet aa)} \<or> sdnets aa = {(first_srcNet aa, first_destNet aa), (first_destNet aa, first_srcNet aa)} "
        and     17 : "{(first_srcNet a, first_destNet a), (first_destNet a, first_srcNet a)} \<noteq> sdnets aa "
        and     18 : "first_destNet a = first_srcNet aa \<longrightarrow> first_srcNet a = first_destNet aa \<longrightarrow> first_destNet aa \<noteq> first_srcNet aa "
        and     19 : "first_destNet a \<noteq> first_srcNet a"
        and     20 : "c = first_srcNet aa \<longrightarrow> d \<noteq> first_destNet aa" 
      show " netsDistinct ab c \<or> netsDistinct b d"
        apply (case_tac "(ab = first_srcNet a \<and> b = first_destNet a)",simp_all)
         apply (case_tac "c = first_srcNet aa", simp_all)
          apply (metis 2 5 14 20 OTNaux)
         apply (subgoal_tac "c = first_destNet aa", simp)
          apply (subgoal_tac "d = first_srcNet aa", simp)
           apply (case_tac "(first_srcNet a) \<noteq> (first_destNet aa)",simp_all)
            apply (metis 4 5 7 firstInNeta firstInNet alternativelistconc2)
           apply (subgoal_tac "first_destNet a \<noteq> first_srcNet aa")
            apply (metis 4 5 7 firstInNeta firstInNet alternativelistconc2)
           apply (metis 3 4 5 first_bothNetsd insert_commute)
          apply (metis 2 5 14 OTNaux)
         apply (metis 2 5 14 OTNaux)
        apply (case_tac "c = first_srcNet aa", simp_all)
         apply (metis 2 5 14 20 OTNaux)
        apply (subgoal_tac "c = first_destNet aa", simp)
         apply (subgoal_tac "d = first_srcNet aa", simp)
          apply (case_tac "(first_destNet a) \<noteq> (first_destNet aa)",simp_all)
           apply (metis 4 5 7 14 firstInNet alternativelistconc2)
          apply (subgoal_tac "first_srcNet a \<noteq> first_srcNet aa")
           apply (metis 4 5 7 14 firstInNeta alternativelistconc2)
          apply (metis 3 4 5 first_bothNetsd  insert_commute)
         apply (metis 2 5 14 OTNaux)
        apply (metis 2 5 14 OTNaux)
        done
    qed
  next 
    show "netsDistinct ab d \<or> netsDistinct b c"   
      apply (insert 1 2 3 4 5 6 7 8 9 10 11 12)           
      apply (cases "sdnets a = {(first_srcNet a, first_destNet a)}")
       apply (cases "sdnets aa = {(first_srcNet aa, first_destNet aa)}", simp_all)
        apply (case_tac "(c = first_srcNet aa \<and> d = first_destNet aa)", simp_all)
        apply (case_tac "(first_srcNet a) \<noteq> (first_destNet aa)", simp_all)
         apply (metis firstInNeta firstInNet alternativelistconc2)
        apply (subgoal_tac "first_destNet a \<noteq> first_srcNet aa")
         apply (metis firstInNeta firstInNet alternativelistconc2)
        apply (metis first_bothNetsd insert_commute)
       apply (case_tac "(c = first_srcNet aa \<and> d = first_destNet aa)", simp_all)
        apply (case_tac "(ab = first_srcNet a \<and> b = first_destNet a)", simp_all)
        apply (case_tac "(first_destNet a) \<noteq> (first_srcNet aa)",simp_all)
         apply (metis firstInNeta firstInNet alternativelistconc2)
        apply (subgoal_tac "first_srcNet a \<noteq> first_destNet aa")
         apply (metis firstInNeta firstInNet alternativelistconc2)
        apply (metis first_bothNetsd insert_commute)
       apply (case_tac "(first_srcNet aa) \<noteq> (first_srcNet a)",simp_all)
        apply (metis firstInNeta alternativelistconc2)
       apply (case_tac "first_destNet aa \<noteq> first_destNet a",simp_all)
        apply (metis firstInNet alternativelistconc2)
       apply (metis first_bothNetsd)    
    proof - 
      assume 13:" \<forall>ab b. ab \<noteq> b \<and> ab\<in>set(net_list_aux[a,aa]) \<and> b \<in> set(net_list_aux[a,aa])
                             \<longrightarrow> netsDistinct ab b "
        and    14 : "(ab = first_srcNet a \<and> b = first_destNet a \<or> 
                        ab = first_destNet a \<and> b = first_srcNet a) \<and> (c, d) \<in> sdnets aa "
        and    15 : " sdnets a = {(first_srcNet a, first_destNet a), 
                                    (first_destNet a, first_srcNet a)} "
        and    16 : " sdnets aa = {(first_srcNet aa, first_destNet aa)} \<or> 
                        sdnets aa = {(first_srcNet aa, first_destNet aa), 
                                     (first_destNet aa, first_srcNet aa)} "
        and    17 : " {(first_srcNet a, first_destNet a), 
                         (first_destNet a, first_srcNet a)} \<noteq> sdnets aa "
      show   "first_destNet a \<noteq> first_srcNet a \<Longrightarrow> netsDistinct ab d \<or> netsDistinct b c"
        apply (insert 1 2 3 4 5 6   13 14 15 16 17)
        apply (cases "sdnets aa = {(first_srcNet aa, first_destNet aa)}", simp_all)
         apply (case_tac "(c = first_srcNet aa \<and> d = first_destNet aa)", simp_all)
         apply (case_tac "(ab = first_srcNet a \<and> b = first_destNet a)", simp_all)
          apply (case_tac "(first_destNet a) \<noteq> (first_srcNet aa)",simp_all)
           apply (metis firstInNeta firstInNet alternativelistconc2)
          apply (subgoal_tac "first_srcNet a \<noteq> first_destNet aa")
           apply (metis firstInNeta firstInNet alternativelistconc2)
          apply (metis first_bothNetsd insert_commute)
         apply (case_tac "(first_srcNet aa) \<noteq> (first_srcNet a)",simp_all)
          apply (metis firstInNeta alternativelistconc2)
         apply (case_tac "first_destNet aa \<noteq> first_destNet a",simp_all)
          apply (metis firstInNet alternativelistconc2)
         apply (metis first_bothNetsd)
      proof -
        assume 20: "{(first_srcNet a, first_destNet a), (first_destNet a, first_srcNet a)} \<noteq>
                        {(first_srcNet aa, first_destNet aa), (first_destNet aa, first_srcNet aa)}"
          and    21: "first_destNet a \<noteq> first_srcNet a"
        show       "netsDistinct ab d \<or> netsDistinct b c"
          apply (case_tac "(c = first_srcNet aa \<and> d = first_destNet aa)", simp_all)
           apply (case_tac "(ab = first_srcNet a \<and> b = first_destNet a)", simp_all)
            apply (case_tac "(first_destNet a) \<noteq> (first_srcNet aa)", simp_all)
             apply (metis 4 5 7 firstInNeta firstInNet alternativelistconc2)
            apply (subgoal_tac "first_srcNet a \<noteq> first_destNet aa")
             apply (metis 4 5 7 firstInNeta firstInNet alternativelistconc2)
            apply (metis 20 insert_commute)
           apply (case_tac "(first_srcNet aa) \<noteq> (first_srcNet a)", simp_all)
            apply (metis 4 5 13 14  firstInNeta alternativelistconc2)
           apply (case_tac "first_destNet aa \<noteq> first_destNet a", simp_all)
            apply (metis 4 5 13 14  firstInNet alternativelistconc2)
           apply (case_tac "(ab = first_srcNet a \<and> b = first_destNet a)", simp_all)
           apply (case_tac "(first_destNet a) \<noteq> (first_srcNet aa)", simp_all)
            apply (metis  20)
          apply (subgoal_tac "first_srcNet a \<noteq> first_srcNet aa")
            apply (metis  20)
           apply (metis 21)
          apply (case_tac "(first_srcNet aa) \<noteq> (first_destNet a)")
           apply (metis (no_types, lifting)  2 3 4 5 7 14 OTNaux 
              firstInNet firstInNeta first_bothNetsd isInAlternativeList) 
          by (metis 2 4 5 7 20 14 OTNaux doubleton_eq_iff firstInNet 
              firstInNeta isInAlternativeList)
      qed
    qed
  qed
qed
  
lemma ANDaux3[rule_format]: 
  "y \<in> set xs \<longrightarrow> a \<in> set (net_list_aux [y]) \<longrightarrow>  a \<in> set (net_list_aux xs)"
  by (induct xs) (simp_all add: isInAlternativeList)
    
lemma ANDaux2: 
  "allNetsDistinct (x # xs) \<Longrightarrow> y \<in> set xs \<Longrightarrow> allNetsDistinct [x,y]"
  apply (simp add: allNetsDistinct_def)
  by (meson ANDaux3 isInAlternativeList netlistaux)
    
lemma NCisSD2[rule_format]: 
  "\<not> member DenyAll a     \<Longrightarrow>  OnlyTwoNets (a#p) \<Longrightarrow> 
  NetsCollected2 (a # p) \<Longrightarrow> NetsCollected (a#p) \<Longrightarrow>
  noDenyAll ( p) \<Longrightarrow> allNetsDistinct (a # p) \<Longrightarrow> s \<in> set p \<Longrightarrow>
  disjSD_2 a s"
  by (metis ANDaux2 FWNormalisationCore.member.simps(2) NCisSD2aux NetsCollected.simps(1) 
      NetsCollected2.simps(1) OTNConc OTNoTN empty_iff empty_set list.set_intros(1) noDA)
    
    
lemma separatedNC[rule_format]: 
  "OnlyTwoNets p \<longrightarrow> NetsCollected2 p \<longrightarrow> NetsCollected p \<longrightarrow> noDenyAll1 p \<longrightarrow>  
   allNetsDistinct p  \<longrightarrow> separated p"
proof (induct p, simp_all, rename_tac a b, case_tac "a = DenyAll", simp_all, goal_cases)
  fix a fix p::"('a set set, 'b) Combinators list"
  show  "OnlyTwoNets p \<longrightarrow> NetsCollected2 p \<longrightarrow> NetsCollected p \<longrightarrow> noDenyAll1 p \<longrightarrow> 
          allNetsDistinct p \<longrightarrow> separated p \<Longrightarrow> a \<noteq> DenyAll \<Longrightarrow>  OnlyTwoNets (a # p) \<longrightarrow>
          first_bothNet a \<noteq> firstList p \<and> NetsCollected2 p \<longrightarrow>
          (\<forall>aa\<in>set p. first_bothNet a \<noteq> first_bothNet aa) \<and> NetsCollected p \<longrightarrow>
          noDenyAll1 (a # p) \<longrightarrow> allNetsDistinct (a # p) \<longrightarrow> (\<forall>s. s \<in> set p \<longrightarrow> 
          disjSD_2 a s) \<and> separated p"
    apply (intro impI,drule mp, erule OTNConc,drule mp)
     apply (case_tac p, simp_all) 
    apply (drule mp,erule noDA1C, intro conjI  allI impI  NCisSD2, simp_all)
      apply (case_tac a, simp_all)
     apply (case_tac a, simp_all)
    using ANDConc by auto
next
  fix a::"('a set set,'b) Combinators " fix p ::"('a set set,'b) Combinators list"
  show  "OnlyTwoNets p \<longrightarrow> NetsCollected2 p \<longrightarrow> NetsCollected p \<longrightarrow> noDenyAll1 p \<longrightarrow> 
          allNetsDistinct p \<longrightarrow> separated p \<Longrightarrow>  a = DenyAll \<Longrightarrow>  OnlyTwoNets p \<longrightarrow>
          {}\<noteq>firstList p \<and> NetsCollected2 p \<longrightarrow> (\<forall>a\<in>set p. {}\<noteq>first_bothNet a)\<and>NetsCollected p \<longrightarrow>
          noDenyAll p \<longrightarrow> allNetsDistinct (DenyAll # p) \<longrightarrow> 
          (\<forall>s. s \<in> set p \<longrightarrow> disjSD_2 DenyAll s) \<and> separated p"
    by (simp add: ANDConc disjSD_2_def noDA1eq)
qed
  
lemma separatedNC'[rule_format]: 
  "OnlyTwoNets p \<longrightarrow> NetsCollected2 p \<longrightarrow> NetsCollected p \<longrightarrow> noDenyAll1 p \<longrightarrow>  
   allNetsDistinct p  \<longrightarrow> separated p"
proof (induct p)
  case Nil show ?case by simp
next
  case (Cons a p) then show ?case
    apply simp
  proof (cases "a = DenyAll") print_cases 
    case True 
    then show "OnlyTwoNets (a # p) \<longrightarrow>  first_bothNet a \<noteq> firstList p \<and> NetsCollected2 p \<longrightarrow>
                      (\<forall>aa\<in>set p. first_bothNet a \<noteq> first_bothNet aa) \<and> NetsCollected p \<longrightarrow>
                      noDenyAll1 (a # p) \<longrightarrow> allNetsDistinct (a # p) \<longrightarrow> 
                      (\<forall>s. s \<in> set p \<longrightarrow> disjSD_2 a s) \<and> separated p"
      apply(insert Cons.hyps \<open>a = DenyAll\<close>)
      apply (intro impI,drule mp, erule OTNConc,drule mp)
       apply (case_tac p, simp_all) 
      apply (case_tac a, simp_all)
      apply (case_tac a, simp_all)
      by (simp add: ANDConc disjSD_2_def noDA1eq)
  next
    case False 
    then show "OnlyTwoNets (a # p) \<longrightarrow>  first_bothNet a \<noteq> firstList p \<and> NetsCollected2 p \<longrightarrow>
                      (\<forall>aa\<in>set p. first_bothNet a \<noteq> first_bothNet aa) \<and> NetsCollected p \<longrightarrow>
                      noDenyAll1 (a # p) \<longrightarrow> allNetsDistinct (a # p) \<longrightarrow> (\<forall>s. s \<in> set p \<longrightarrow> 
                      disjSD_2 a s) \<and> separated p" 
      apply(insert Cons.hyps \<open>a \<noteq> DenyAll\<close>)
      by (metis NetsCollected.simps(1) NetsCollected2.simps(1) separated.simps(1) separatedNC)
  qed
qed
  
lemma NC2Sep[rule_format]: "noDenyAll1 p \<longrightarrow> NetsCollected2 (separate p)"
proof (induct p rule: separate.induct, simp_all, goal_cases)
  fix x :: "('a, 'b) Combinators list"
  case 1 then show ?case
    by (metis fMTaux firstList.simps(1) fl2 noDA1eq noDenyAll.elims(2) separate.simps(5))
next
  fix v va fix y::" ('a, 'b) Combinators" fix z
  case 2 then show ?case   
    by (simp add: fl2 noDA1eq)
next
  fix v va vb fix y::" ('a, 'b) Combinators" fix z
  case 3 then show ?case
    by (simp add: fl2 noDA1eq)
next
  fix v va fix y::" ('a, 'b) Combinators" fix z
  case 4 then show ?case
    by (simp add: fl2 noDA1eq)         
qed         
  
lemma separatedSep[rule_format]: 
  "OnlyTwoNets p \<longrightarrow> NetsCollected2 p   \<longrightarrow> NetsCollected p \<longrightarrow> 
   noDenyAll1 p  \<longrightarrow> allNetsDistinct p  \<longrightarrow> separated (separate p)"
  by (simp add: ANDSep NC2Sep NetsCollectedSep OTNSEp noDA1sep separatedNC)
    
    
lemma rADnMT[rule_format]: "p \<noteq> []  \<longrightarrow> removeAllDuplicates p \<noteq> []"
  by (induct p) simp_all
        
lemma remDupsNMT[rule_format]: "p \<noteq> [] \<longrightarrow> remdups p \<noteq> []"
  by (metis remdups_eq_nil_iff) 
    
lemma sets_distinct1: "(n::int) \<noteq> m \<Longrightarrow> {(a,b). a = n} \<noteq> {(a,b). a = m}"
  by auto
    
lemma sets_distinct2: "(m::int) \<noteq> n \<Longrightarrow> {(a,b). a = n} \<noteq> {(a,b). a = m}"
  by auto
    
lemma sets_distinct5: "(n::int) < m \<Longrightarrow> {(a,b). a = n} \<noteq> {(a,b). a = m}"
  by auto
    
lemma sets_distinct6: "(m::int) < n \<Longrightarrow> {(a,b). a = n} \<noteq> {(a,b). a = m}"
  by auto
end
  
