(*****************************************************************************
 * Copyright (c) 2005-2010 ETH Zurich, Switzerland
 *               2008-2015 Achim D. Brucker, Germany
 *               2009-2016 Université Paris-Sud, France
 *               2015-2016 The University of Sheffield, UK
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

subsection \<open>Policy Normalisation: Core Definitions\<close>
theory
  FWNormalisationCore
imports
  "../PacketFilter/PacketFilter"
begin

text\<open>
  This theory contains all the definitions used for policy normalisation as described 
  in~\cite{brucker.ea:icst:2010,brucker.ea:formal-fw-testing:2014}.

  The normalisation procedure transforms policies into semantically equivalent  ones which are 
  ``easier'' to test. It is organized into nine phases. We impose the following two restrictions 
  on the input policies: 
  \begin{itemize}
  \item Each policy must contain a $\mathtt{DenyAll}$ rule. If this restriction were to be lifted, 
        the $\mathtt{insertDenies}$ phase would have to be adjusted accordingly.
  \item For each pair of networks $n_1$ and $n_2$, the networks are either disjoint or equal. If 
        this restriction were to be lifted, we would need some additional phases before the start 
        of the normalisation procedure presented below. This rule would split single rules into 
        several by splitting up the networks such that they are all pairwise disjoint or equal. 
        Such a transformation is clearly semantics-preserving and the condition would hold after
        these phases.
  \end{itemize}
  As a result, the procedure generates a list of policies, in which:
  \begin{itemize}
  \item each element of the list contains a policy which completely specifies the blocking behavior 
        between two networks, and
  \item there are no shadowed rules.
  \end{itemize}
  This result is desirable since the test case generation for rules between networks $A$ and $B$ 
  is independent of the rules that specify the behavior for traffic flowing between networks $C$ 
  and $D$. Thus, the different segments of the policy can be processed individually. The 
  normalization procedure does not aim to minimize the number of rules. While it does remove 
  unnecessary ones, it also adds new ones, enabling a policy to be split into several independent
  parts.
\<close>

text\<open>
  Policy transformations are functions that map policies to policies.  We decided to represent
  policy transformations as \emph{syntactic rules}; this choice paves the way for expressing the 
  entire normalisation process inside HOL by functions manipulating abstract policy syntax. 
\<close>


subsubsection\<open>Basics\<close>
text\<open>We define a very simple policy language:\<close>

datatype ('\<alpha>,'\<beta>) Combinators = 
  DenyAll
  | DenyAllFromTo '\<alpha> '\<alpha> 
  | AllowPortFromTo '\<alpha> '\<alpha> '\<beta> 
  | Conc "(('\<alpha>,'\<beta>) Combinators)" "(('\<alpha>,'\<beta>) Combinators)" (infixr "\<oplus>" 80)

text\<open>
  And define the semantic interpretation of it. For technical reasons, we fix here the type to 
  policies over IntegerPort addresses. However, we could easily provide definitions for other
  address types as well, using a generic constants for the type definition and a primitive 
  recursive definition for each desired address model.  
\<close>

subsubsection\<open>Auxiliary definitions and functions.\<close>
text\<open>
  This section defines several functions which are useful later for the combinators, invariants, 
  and proofs. 
\<close>
  
fun srcNet where 
 "srcNet (DenyAllFromTo x y) = x"
|"srcNet (AllowPortFromTo x y p) = x"
|"srcNet DenyAll = undefined"
|"srcNet (v \<oplus> va) = undefined" 

fun destNet where 
 "destNet (DenyAllFromTo x y) = y"
|"destNet (AllowPortFromTo x y p) = y"
|"destNet DenyAll = undefined"
|"destNet (v \<oplus> va) = undefined" 

fun srcnets where
 "srcnets DenyAll = [] " 
|"srcnets (DenyAllFromTo x y) = [x] " 
|"srcnets (AllowPortFromTo x y p) = [x] " 
|"(srcnets (x \<oplus> y)) = (srcnets x)@(srcnets y)"

fun destnets where
 "destnets DenyAll = [] " 
|"destnets (DenyAllFromTo x y) = [y] " 
|"destnets (AllowPortFromTo x y p) = [y] "
|"(destnets (x \<oplus> y)) = (destnets x)@(destnets y)"

fun (sequential) net_list_aux where
 "net_list_aux [] = []"
|"net_list_aux (DenyAll#xs) = net_list_aux xs"
|"net_list_aux ((DenyAllFromTo x y)#xs) = x#y#(net_list_aux xs)"
|"net_list_aux ((AllowPortFromTo x y p)#xs) = x#y#(net_list_aux xs)"
|"net_list_aux ((x\<oplus>y)#xs) = (net_list_aux [x])@(net_list_aux [y])@(net_list_aux xs)"

fun net_list where "net_list p = remdups (net_list_aux p)"

definition bothNets where "bothNets x = (zip (srcnets x) (destnets x))"

fun (sequential) normBothNets where 
 "normBothNets ((a,b)#xs) = (if ((b,a) \<in> set xs) \<or> (a,b) \<in> set (xs) 
                            then (normBothNets xs)
                            else (a,b)#(normBothNets xs))"
|"normBothNets x = x" 

fun makeSets where 
 "makeSets ((a,b)#xs) = ({a,b}#(makeSets xs))"
|"makeSets [] = []"

fun bothNet where
 "bothNet DenyAll = {}"
|"bothNet (DenyAllFromTo a b) = {a,b}"
|"bothNet (AllowPortFromTo a b p) = {a,b}"
|"bothNet (v \<oplus> va) = undefined "

text\<open>
  $Nets\_List$ provides from a list of rules a list where the entries are the appearing sets of 
  source and destination network of each rule. 
\<close>

definition Nets_List 
  where 
  "Nets_List x = makeSets (normBothNets (bothNets x))"

fun (sequential) first_srcNet where 
  "first_srcNet (x\<oplus>y) = first_srcNet x"
| "first_srcNet x = srcNet x"

fun (sequential) first_destNet where 
  "first_destNet (x\<oplus>y) = first_destNet x"
| "first_destNet x = destNet x"

fun (sequential) first_bothNet where
 "first_bothNet (x\<oplus>y) = first_bothNet x"
|"first_bothNet x = bothNet x"

fun (sequential) in_list where 
 "in_list DenyAll l = True"
|"in_list x l = (bothNet x \<in> set l)"

fun all_in_list where 
 "all_in_list [] l = True"
|"all_in_list (x#xs) l = (in_list x l \<and> all_in_list xs l)" 

fun (sequential) member where
 "member a (x\<oplus>xs) = ((member a x) \<or> (member a xs))"
|"member a x = (a = x)"

fun sdnets where
  "sdnets DenyAll = {}"
| "sdnets (DenyAllFromTo a b) = {(a,b)}"
| "sdnets (AllowPortFromTo a b c) = {(a,b)}"
| "sdnets (a \<oplus> b) = sdnets a \<union> sdnets b"

definition packet_Nets  where "packet_Nets x a b = ((src x \<sqsubset> a \<and> dest x \<sqsubset> b) \<or>
                                                    (src x \<sqsubset> b \<and> dest x \<sqsubset> a))"

definition subnetsOfAdr where "subnetsOfAdr a = {x. a \<sqsubset> x}"

definition fst_set where "fst_set s = {a. \<exists> b. (a,b) \<in> s}"

definition snd_set where "snd_set s = {a. \<exists> b. (b,a) \<in> s}"

fun memberP where
 "memberP r (x#xs) = (member r x \<or> memberP r xs)"
|"memberP r [] = False"

fun firstList where 
 "firstList (x#xs) = (first_bothNet x)"
|"firstList [] = {}"

subsubsection\<open>Invariants\<close>

text\<open>If there is a DenyAll, it is at the first position\<close>
fun wellformed_policy1:: "(('\<alpha>, '\<beta>) Combinators) list \<Rightarrow> bool" where 
  "wellformed_policy1 [] = True"
| "wellformed_policy1 (x#xs) = (DenyAll \<notin> (set xs))" 

text\<open>There is a DenyAll at the first position\<close>
fun wellformed_policy1_strong:: "(('\<alpha>, '\<beta>) Combinators) list \<Rightarrow> bool"
where 
  "wellformed_policy1_strong [] = False"
| "wellformed_policy1_strong (x#xs) = (x=DenyAll \<and> (DenyAll \<notin> (set xs)))" 


text\<open>All two networks are either disjoint or equal.\<close>
definition netsDistinct where "netsDistinct a b = (\<not> (\<exists> x. x \<sqsubset> a \<and> x \<sqsubset> b))"

definition twoNetsDistinct where
  "twoNetsDistinct a b c d = (netsDistinct a c \<or> netsDistinct b d)"

definition allNetsDistinct where 
  "allNetsDistinct p = (\<forall> a b. (a \<noteq> b \<and> a \<in> set (net_list p) \<and>
                        b \<in> set (net_list p)) \<longrightarrow> netsDistinct a b)"

definition disjSD_2 where 
 "disjSD_2 x y = (\<forall> a b c d. ((a,b)\<in>sdnets x \<and>  (c,d) \<in>sdnets y \<longrightarrow>
      (twoNetsDistinct a b c d \<and> twoNetsDistinct a b d c)))"

text\<open>The policy is given as a list of single rules.\<close>
fun singleCombinators where 
"singleCombinators [] = True"
|"singleCombinators ((x\<oplus>y)#xs) = False"
|"singleCombinators (x#xs) = singleCombinators xs"

definition onlyTwoNets where
 "onlyTwoNets x = ((\<exists> a b. (sdnets x = {(a,b)})) \<or> (\<exists> a b. sdnets x = {(a,b),(b,a)}))" 

text\<open>Each entry of the list contains rules between two networks only.\<close>
fun OnlyTwoNets where 
 "OnlyTwoNets (DenyAll#xs) = OnlyTwoNets xs"
|"OnlyTwoNets (x#xs) = (onlyTwoNets x \<and> OnlyTwoNets xs)"
|"OnlyTwoNets [] = True"

fun noDenyAll where
 "noDenyAll (x#xs) = ((\<not> member DenyAll x) \<and> noDenyAll xs)"
|"noDenyAll [] = True"

fun noDenyAll1 where 
  "noDenyAll1 (DenyAll#xs) = noDenyAll xs"
| "noDenyAll1 xs = noDenyAll xs"

fun separated where
  "separated (x#xs) = ((\<forall> s. s \<in> set xs \<longrightarrow> disjSD_2 x s) \<and> separated xs)"
| "separated [] = True"

fun NetsCollected where 
  "NetsCollected (x#xs) = (((first_bothNet x \<noteq> firstList xs) \<longrightarrow>
          (\<forall>a\<in>set xs. first_bothNet x \<noteq> first_bothNet a)) \<and> NetsCollected (xs))"
| "NetsCollected [] = True"

fun NetsCollected2 where
 "NetsCollected2 (x#xs) = (xs = [] \<or> (first_bothNet x \<noteq> firstList xs \<and>
                           NetsCollected2 xs))"
|"NetsCollected2 [] = True"

subsubsection\<open>Transformations\<close>

text \<open>
  The following two functions transform a policy into a list of single rules and vice-versa (by 
  staying on the combinator level).
\<close>

fun policy2list::"('\<alpha>, '\<beta>) Combinators \<Rightarrow>
                 (('\<alpha>, '\<beta>) Combinators) list" where
 "policy2list (x \<oplus> y) = (concat [(policy2list x),(policy2list y)])"
|"policy2list x = [x]"

fun list2FWpolicy::"(('\<alpha>, '\<beta>) Combinators) list \<Rightarrow>
                  (('\<alpha>, '\<beta>) Combinators)" where
 "list2FWpolicy [] = undefined "
|"list2FWpolicy (x#[]) = x"
|"list2FWpolicy (x#y) = x \<oplus> (list2FWpolicy y)"

text\<open>Remove all the rules appearing before a DenyAll. There are two alternative versions.\<close>

fun removeShadowRules1 where
  "removeShadowRules1 (x#xs) = (if (DenyAll \<in> set xs) 
                                then ((removeShadowRules1 xs))
                                else x#xs)"
| "removeShadowRules1 [] = []"

fun  removeShadowRules1_alternative_rev where
  "removeShadowRules1_alternative_rev [] = []"
| "removeShadowRules1_alternative_rev (DenyAll#xs) = [DenyAll]"
| "removeShadowRules1_alternative_rev [x] = [x]"
| "removeShadowRules1_alternative_rev (x#xs)=
                 x#(removeShadowRules1_alternative_rev xs)"

definition removeShadowRules1_alternative where
   "removeShadowRules1_alternative p =
                         rev (removeShadowRules1_alternative_rev (rev p))"

text\<open>
  Remove all the rules which allow a port, but are shadowed by a deny between these subnets.
\<close>

fun removeShadowRules2::  "(('\<alpha>, '\<beta>) Combinators) list \<Rightarrow>
                          (('\<alpha>, '\<beta>) Combinators) list"
where
  "(removeShadowRules2 ((AllowPortFromTo x y p)#z)) = 
        (if (((DenyAllFromTo x y) \<in> set z)) 
         then ((removeShadowRules2 z))
         else (((AllowPortFromTo x y p)#(removeShadowRules2 z))))"
| "removeShadowRules2 (x#y) = x#(removeShadowRules2 y)"
| "removeShadowRules2 [] = []"

text\<open>
  Sorting a policies:  We first need to define an ordering on rules.  This ordering depends 
   on the $Nets\_List$ of a policy.  
\<close>

fun smaller :: "('\<alpha>, '\<beta>) Combinators \<Rightarrow> 
                ('\<alpha>, '\<beta>) Combinators \<Rightarrow> 
                (('\<alpha>) set) list \<Rightarrow> bool" 
where
 "smaller DenyAll x l = True" 
| "smaller x DenyAll l = False"
| "smaller x y l = 
 ((x = y) \<or>         (if (bothNet x) = (bothNet y) then 
                       (case y of (DenyAllFromTo a b) \<Rightarrow> (x = DenyAllFromTo b a)  
                            | _ \<Rightarrow>  True)
                    else
                        (position (bothNet x) l <= position (bothNet y) l)))"

text\<open>We provide two different sorting algorithms: Quick Sort (qsort) and Insertion Sort (sort)\<close>

fun qsort where
  "qsort [] l     = []"
| "qsort (x#xs) l = (qsort [y\<leftarrow>xs. \<not> (smaller x y l)] l) @ [x] @ (qsort [y\<leftarrow>xs. smaller x y l] l)"

lemma qsort_permutes:
  "set (qsort xs l) = set xs"
  apply (induct "xs" "l" rule: qsort.induct)
  by (auto)

lemma set_qsort [simp]: "set (qsort xs l)  = set xs" 
  by (simp add: qsort_permutes)
    
fun insort where
	  "insort a [] l = [a]"
	| "insort a (x#xs) l = (if (smaller a x l) then a#x#xs else x#(insort a xs l))"

fun sort where
  "sort [] l = []"
| "sort (x#xs) l = insort x (sort xs l) l"

fun sorted  where
  "sorted [] l = True"
| "sorted [x] l = True"
| "sorted (x#y#zs) l = (smaller x y l \<and> sorted (y#zs) l)"

fun separate where
 "separate (DenyAll#x) = DenyAll#(separate x)"
| "separate (x#y#z) = (if (first_bothNet x = first_bothNet y) 
                   then (separate ((x\<oplus>y)#z))
                   else (x#(separate(y#z))))"
|"separate x = x"                

text \<open>
  Insert the DenyAllFromTo rules, such that traffic between two networks can be tested 
  individually.
\<close>

fun  insertDenies where
 "insertDenies (x#xs) = (case x of DenyAll \<Rightarrow> (DenyAll#(insertDenies xs))
                    | _  \<Rightarrow> (DenyAllFromTo (first_srcNet x) (first_destNet x) \<oplus> 
                       (DenyAllFromTo (first_destNet x) (first_srcNet x)) \<oplus> x)#
                                (insertDenies xs))"
| "insertDenies [] = []"

text\<open>
  Remove duplicate rules. This is especially necessary as insertDenies might have inserted 
  duplicate rules. The second function is supposed to work on a list of policies. Only
  rules which are duplicated within the same policy are removed.  
\<close>


fun removeDuplicates where
  "removeDuplicates (x\<oplus>xs) = (if member x xs then (removeDuplicates xs)
                              else x\<oplus>(removeDuplicates xs))"
| "removeDuplicates x = x"

fun removeAllDuplicates where 
 "removeAllDuplicates (x#xs) = ((removeDuplicates (x))#(removeAllDuplicates xs))"
|"removeAllDuplicates x = x"

text \<open>Insert a DenyAll at the beginning of a policy.\<close>
fun insertDeny where 
 "insertDeny (DenyAll#xs) = DenyAll#xs"
|"insertDeny xs = DenyAll#xs"


definition "sort' p l = sort l p"
definition "qsort' p l = qsort l p"

declare dom_eq_empty_conv [simp del]

fun list2policyR::"(('\<alpha>, '\<beta>) Combinators) list \<Rightarrow>
                   (('\<alpha>, '\<beta>) Combinators)" where
 "list2policyR (x#[]) = x"
|"list2policyR (x#y) = (list2policyR y) \<oplus> x"
|"list2policyR [] = undefined "


text\<open>
  We provide the definitions for two address representations. 
\<close>


subsubsection\<open>IntPort\<close>

fun C :: "(adr\<^sub>i\<^sub>p net, port) Combinators \<Rightarrow> (adr\<^sub>i\<^sub>p,DummyContent) packet \<mapsto> unit"
where
" C DenyAll = deny_all" 
|"C (DenyAllFromTo x y) = deny_all_from_to x y"
|"C (AllowPortFromTo x y p) = allow_from_to_port p x y"
|"C  (x \<oplus> y) =  C x ++ C y"

fun CRotate :: "(adr\<^sub>i\<^sub>p net, port) Combinators \<Rightarrow> (adr\<^sub>i\<^sub>p,DummyContent) packet \<mapsto> unit"
where
" CRotate DenyAll = C DenyAll" 
|"CRotate (DenyAllFromTo x y) = C (DenyAllFromTo x y)"
|"CRotate (AllowPortFromTo x y p) = C (AllowPortFromTo x y p)"
|"CRotate (x \<oplus> y) = ((CRotate y) ++ ((CRotate x)))"

fun rotatePolicy where
  "rotatePolicy DenyAll = DenyAll" 
| "rotatePolicy (DenyAllFromTo a b) = DenyAllFromTo a b"
| "rotatePolicy (AllowPortFromTo a b p) = AllowPortFromTo a b p"
| "rotatePolicy (a\<oplus>b) = (rotatePolicy b) \<oplus> (rotatePolicy a)"

lemma check: "rev (policy2list (rotatePolicy p)) = policy2list p"
  apply (induct "p")
  by (simp_all) 


text\<open>
  All rules appearing at the left of a DenyAllFromTo, have disjunct domains from it 
  (except DenyAll). 
\<close>
fun (sequential) wellformed_policy2 where
  "wellformed_policy2 [] = True"
| "wellformed_policy2 (DenyAll#xs) = wellformed_policy2 xs"
| "wellformed_policy2 (x#xs) = ((\<forall> c a b. c = DenyAllFromTo a b \<and> c \<in> set xs \<longrightarrow>
                 Map.dom (C x) \<inter> Map.dom (C c) = {}) \<and> wellformed_policy2 xs)"

text\<open>
  An allow rule is disjunct with all rules appearing at the right of it. This invariant is not 
  necessary as it is a consequence from others, but facilitates some proofs. 
\<close>

fun (sequential) wellformed_policy3::"((adr\<^sub>i\<^sub>p net,port) Combinators) list \<Rightarrow> bool" where
  "wellformed_policy3 [] = True"
| "wellformed_policy3 ((AllowPortFromTo a b p)#xs) = ((\<forall> r. r \<in> set xs \<longrightarrow>
      dom (C r) \<inter> dom (C (AllowPortFromTo a b p)) = {}) \<and> wellformed_policy3 xs)"
| "wellformed_policy3 (x#xs) = wellformed_policy3 xs"


definition 
  "normalize' p  = (removeAllDuplicates o insertDenies o separate o
                   (sort' (Nets_List p))  o removeShadowRules2 o remdups o
                   (rm_MT_rules C) o insertDeny o removeShadowRules1 o
                   policy2list) p"

definition 
  "normalizeQ' p  = (removeAllDuplicates o insertDenies o separate o
                   (qsort' (Nets_List p))  o removeShadowRules2 o remdups o
                   (rm_MT_rules C) o insertDeny o removeShadowRules1 o
                   policy2list) p"

definition normalize :: 
  "(adr\<^sub>i\<^sub>p net, port) Combinators \<Rightarrow> 
   (adr\<^sub>i\<^sub>p net, port) Combinators list" 
where
   "normalize p = (removeAllDuplicates (insertDenies (separate (sort
                   (removeShadowRules2 (remdups ((rm_MT_rules C) (insertDeny
                  (removeShadowRules1 (policy2list p)))))) ((Nets_List p))))))"

definition
   "normalize_manual_order p l = removeAllDuplicates (insertDenies (separate
    (sort (removeShadowRules2 (remdups ((rm_MT_rules C) (insertDeny
    (removeShadowRules1 (policy2list p)))))) ((l)))))"

definition normalizeQ :: 
  "(adr\<^sub>i\<^sub>p net, port) Combinators \<Rightarrow> 
   (adr\<^sub>i\<^sub>p net, port) Combinators list" 
where
   "normalizeQ p = (removeAllDuplicates (insertDenies (separate (qsort
                   (removeShadowRules2 (remdups ((rm_MT_rules C) (insertDeny
                  (removeShadowRules1 (policy2list p)))))) ((Nets_List p))))))"

definition
   "normalize_manual_orderQ p l = removeAllDuplicates (insertDenies (separate
    (qsort (removeShadowRules2 (remdups ((rm_MT_rules C) (insertDeny
    (removeShadowRules1 (policy2list p)))))) ((l)))))"

text\<open>
  Of course, normalize is equal to normalize', the latter looks nicer though. 
\<close>
lemma "normalize = normalize'"
  by (rule ext, simp add: normalize_def normalize'_def sort'_def)

declare C.simps [simp del]


subsubsection\<open>TCP\_UDP\_IntegerPort\<close>

fun Cp :: "(adr\<^sub>i\<^sub>p\<^sub>p net, protocol \<times> port) Combinators \<Rightarrow> 
          (adr\<^sub>i\<^sub>p\<^sub>p,DummyContent) packet \<mapsto> unit"
where
 " Cp DenyAll = deny_all"  
|"Cp (DenyAllFromTo x y) = deny_all_from_to x y"
|"Cp (AllowPortFromTo x y p) = allow_from_to_port_prot (fst p) (snd p) x y"
|"Cp  (x \<oplus> y) =  Cp x ++ Cp y"


fun Dp :: "(adr\<^sub>i\<^sub>p\<^sub>p net, protocol \<times> port) Combinators \<Rightarrow> 
          (adr\<^sub>i\<^sub>p\<^sub>p,DummyContent) packet \<mapsto> unit"
where
" Dp DenyAll = Cp DenyAll" 
|"Dp (DenyAllFromTo x y) = Cp (DenyAllFromTo x y)"
|"Dp (AllowPortFromTo x y p) = Cp (AllowPortFromTo x y p)"
|"Dp  (x \<oplus> y) =  Cp (y \<oplus> x)"

text\<open>
  All rules appearing at the left of a DenyAllFromTo, have disjunct domains from it 
  (except DenyAll). 
\<close>
fun (sequential) wellformed_policy2Pr where
  "wellformed_policy2Pr [] = True"
| "wellformed_policy2Pr (DenyAll#xs) = wellformed_policy2Pr xs"
| "wellformed_policy2Pr (x#xs) = ((\<forall> c a b. c = DenyAllFromTo a b \<and> c \<in> set xs \<longrightarrow>
                 Map.dom (Cp x) \<inter> Map.dom (Cp c) = {}) \<and> wellformed_policy2Pr xs)"

text\<open>
  An allow rule is disjunct with all rules appearing at the right of it. This invariant is not
  necessary as it is a consequence from others, but facilitates some proofs. 
\<close>

fun (sequential) wellformed_policy3Pr::"((adr\<^sub>i\<^sub>p\<^sub>p net, protocol \<times> port) Combinators) list \<Rightarrow> bool" where
  "wellformed_policy3Pr [] = True"
| "wellformed_policy3Pr ((AllowPortFromTo a b p)#xs) = ((\<forall> r. r \<in> set xs \<longrightarrow>
      dom (Cp r) \<inter> dom (Cp (AllowPortFromTo a b p)) = {}) \<and> wellformed_policy3Pr xs)"
| "wellformed_policy3Pr (x#xs) = wellformed_policy3Pr xs"

definition 
 normalizePr' :: "(adr\<^sub>i\<^sub>p\<^sub>p net, protocol \<times> port) Combinators
  \<Rightarrow> (adr\<^sub>i\<^sub>p\<^sub>p net, protocol \<times> port) Combinators list" where 
 "normalizePr' p = (removeAllDuplicates o insertDenies o separate o
                   (sort' (Nets_List p))  o removeShadowRules2 o remdups o
                   (rm_MT_rules Cp) o insertDeny o removeShadowRules1 o
                   policy2list) p"

definition normalizePr :: 
"(adr\<^sub>i\<^sub>p\<^sub>p net, protocol \<times> port) Combinators
  \<Rightarrow> (adr\<^sub>i\<^sub>p\<^sub>p net, protocol \<times> port) Combinators list" where
   "normalizePr p = (removeAllDuplicates (insertDenies (separate (sort
                   (removeShadowRules2 (remdups ((rm_MT_rules Cp) (insertDeny
                  (removeShadowRules1 (policy2list p)))))) ((Nets_List p))))))"

definition
   "normalize_manual_orderPr p l = removeAllDuplicates (insertDenies (separate
    (sort (removeShadowRules2 (remdups ((rm_MT_rules Cp) (insertDeny
    (removeShadowRules1 (policy2list p)))))) ((l)))))"


definition 
 normalizePrQ' :: "(adr\<^sub>i\<^sub>p\<^sub>p net, protocol \<times> port) Combinators
  \<Rightarrow> (adr\<^sub>i\<^sub>p\<^sub>p net, protocol \<times> port) Combinators list" where 
 "normalizePrQ' p = (removeAllDuplicates o insertDenies o separate o
                   (qsort' (Nets_List p))  o removeShadowRules2 o remdups o
                   (rm_MT_rules Cp) o insertDeny o removeShadowRules1 o
                   policy2list) p"

definition normalizePrQ :: 
"(adr\<^sub>i\<^sub>p\<^sub>p net, protocol \<times> port) Combinators
  \<Rightarrow> (adr\<^sub>i\<^sub>p\<^sub>p net, protocol \<times> port) Combinators list" where
   "normalizePrQ p = (removeAllDuplicates (insertDenies (separate (qsort
                   (removeShadowRules2 (remdups ((rm_MT_rules Cp) (insertDeny
                  (removeShadowRules1 (policy2list p)))))) ((Nets_List p))))))"

definition
   "normalize_manual_orderPrQ p l = removeAllDuplicates (insertDenies (separate
    (qsort (removeShadowRules2 (remdups ((rm_MT_rules Cp) (insertDeny
    (removeShadowRules1 (policy2list p)))))) ((l)))))"

text\<open>
  Of course, normalize is equal to normalize', the latter looks nicer though. 
\<close>
lemma "normalizePr = normalizePr'"
  by (rule ext, simp add: normalizePr_def normalizePr'_def sort'_def)


text\<open>
  The following definition helps in creating the test specification for the individual parts 
  of a normalized policy. 
\<close>
definition makeFUTPr where 
   "makeFUTPr FUT p x n = 
     (packet_Nets x (fst (normBothNets (bothNets p)!n))  
                     (snd(normBothNets (bothNets p)!n)) \<longrightarrow> 
    FUT x = Cp ((normalizePr p)!Suc n) x)"

declare Cp.simps [simp del]

lemmas PLemmas = C.simps Cp.simps dom_def PolicyCombinators.PolicyCombinators
                 PortCombinators.PortCombinatorsCore aux
                 ProtocolPortCombinators.ProtocolCombinatorsCore src_def dest_def in_subnet_def
                 adr\<^sub>i\<^sub>p\<^sub>pLemmas adr\<^sub>i\<^sub>p\<^sub>pLemmas

lemma aux: "\<lbrakk>x \<noteq> a; y\<noteq>b; (x \<noteq> y \<and> x \<noteq> b) \<or>  (a \<noteq> b \<and> a \<noteq> y)\<rbrakk> \<Longrightarrow> {x,a} \<noteq> {y,b}"
  by (auto)

lemma aux2: "{a,b} = {b,a}"
  by auto
end
