(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : A Combined CSP Theory
 *
 * Copyright (c) 2009 Université Paris-Sud, France
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
 ******************************************************************************\<close>
(*>*)

section\<open> The Synchronizing Operator \<close>

theory  Sync
  imports Process "HOL-Library.Infinite_Set"
begin

subsection\<open>Basic Concepts\<close>

fun setinterleaving:: "'a trace \<times> ('a event) set \<times> 'a trace \<Rightarrow> ('a trace)set"
  where

  si_empty1: "setinterleaving([], X, []) = {[]}"
| si_empty2: "setinterleaving([], X, (y # t)) = 
               (if (y \<in> X) 
                then {} 
                else {z.\<exists> u. z = (y # u) \<and> u \<in> setinterleaving ([], X, t)})"
| si_empty3: "setinterleaving((x # s), X, []) = 
               (if (x \<in> X) 
                then {} 
                else {z.\<exists> u. z = (x # u) \<and> u \<in> setinterleaving (s, X, [])})"
 
| si_neq   : "setinterleaving((x # s), X, (y # t)) = 
               (if (x \<in> X) 
                then if (y \<in> X) 
                     then if (x = y) 
                          then {z.\<exists> u. z = (x#u) \<and> u \<in> setinterleaving(s, X, t)} 
                          else {}
                     else {z.\<exists> u. z = (y#u) \<and> u \<in> setinterleaving ((x#s), X, t)}
                else if (y \<notin> X) 
                     then {z.\<exists> u. z = (x # u) \<and> u \<in> setinterleaving (s, X, (y # t))} 
                          \<union> {z.\<exists> u. z = (y # u) \<and> u \<in> setinterleaving((x # s), X, t)} 
                     else {z.\<exists> u. z = (x # u) \<and> u \<in> setinterleaving (s, X, (y # t))})"

fun setinterleavingList::"'a trace \<times> ('a event) set \<times> 'a trace \<Rightarrow> ('a trace)list" 
  where

  si_empty1l: "setinterleavingList([], X, []) = [[]]"
| si_empty2l: "setinterleavingList([], X, (y # t)) = 
               (if (y \<in> X) 
                then [] 
                else map (\<lambda>z. y#z) (setinterleavingList ([], X, t)))"
| si_empty3l: "setinterleavingList((x # s), X, []) = 
               (if (x \<in> X) 
                then [] 
                else map (\<lambda>z. x#z) (setinterleavingList (s, X, [])))"

 
 
| si_neql   : "setinterleavingList((x # s), X, (y # t)) = 
               (if (x \<in> X) 
                then if (y \<in> X) 
                     then if (x = y) 
                          then map (\<lambda>z. x#z)  (setinterleavingList(s, X, t))
                          else []
                     else map (\<lambda>z. y#z)  (setinterleavingList ((x#s), X, t))
                else if (y \<notin> X) 
                     then map (\<lambda>z. x#z)  (setinterleavingList (s, X, (y # t)))
                          @ map (\<lambda>z. y#z)  (setinterleavingList ((x#s), X, t)) 
                     else map (\<lambda>z. x#z)  (setinterleavingList (s, X, (y # t))))"

lemma finiteSetinterleavingList: "finite (set (setinterleavingList(s, X, t)))" 
  by auto

lemma sym : "setinterleaving(s, X, t)= setinterleaving(t, X, s)"
  by (rule setinterleaving.induct[of "\<lambda>(s,X,t). setinterleaving (s, X, t) 
  = setinterleaving (t, X, s)" "(s, X, t)", simplified], auto)

 

abbreviation "setinterleaves_syntax"  
                         ("_ setinterleaves '(()'(_, _')(), _')" [60,0,0,0]70)
where
 "u setinterleaves ((s, t), X) == (u \<in> setinterleaving(s, X, t))"

 
subsection\<open>Definition\<close>

definition sync :: "['a process,'a set,'a process] => 'a process" 
           ("(3_ \<lbrakk>_\<rbrakk>/ _)" [14,0,15] 14)  
where
 "P \<lbrakk> A \<rbrakk> Q == 
       Abs_process({(s,R).\<exists> t u X Y. (t,X) \<in> F P \<and> (u,Y) \<in> F Q \<and> 
                                     (s setinterleaves ((t,u),(ev`A) \<union> {tick})) \<and> 
                                     R = (X \<union> Y) \<inter> ((ev`A) \<union> {tick}) \<union> X \<inter> Y} \<union> 
                   {(s,R).\<exists> t u r v. front_tickFree v \<and> (tickFree r \<or> v=[]) \<and> 
                                     s = r@v \<and> 
                                     (r setinterleaves ((t,u),(ev`A) \<union> {tick})) \<and> 
          (t \<in> D P \<and> u \<in> T Q \<or> t \<in> D Q \<and> u \<in> T P)},

                   {s.    \<exists> t u r v. front_tickFree v \<and> (tickFree r \<or> v=[]) \<and> 
                                     s = r@v \<and> 
                                     (r setinterleaves ((t,u),(ev`A) \<union> {tick})) \<and> 
                                     (t \<in> D P \<and> u \<in> T Q \<or> t \<in> D Q \<and> u \<in> T P)})"

subsection\<open>Consequences\<close>

lemma emptyLeftProperty:"\<forall>s. s setinterleaves (([], t), A)\<longrightarrow>s=t" 
  apply(induct_tac t)  
   apply simp 
  by auto 

lemma emptyLeftSelf: " (\<forall>t1. t1\<in> set t\<longrightarrow>t1\<notin>A)\<longrightarrow>t setinterleaves (([], t), A) "
  apply(induct_tac t)
   apply simp 
  by auto

lemma emptyLeftNonSync: "\<forall>s. s setinterleaves (([], t), A)\<longrightarrow>(\<forall>t1. t1\<in> set t\<longrightarrow>t1\<notin>A)"
  apply(induct_tac t)
   apply simp
proof-
  fix a list
  assume a: "\<forall>s. s setinterleaves (([], list), A) \<longrightarrow> (\<forall>t1. t1 \<in> set list \<longrightarrow> t1 \<notin> A)"
  thus "\<forall>s. s setinterleaves (([], a # list), A) \<longrightarrow> (\<forall>t1. t1 \<in> set (a # list) \<longrightarrow> t1 \<notin> A)"
  proof-
    have th: "s setinterleaves (([], a # list), A)\<longrightarrow>a\<notin>A" by auto
    obtain s1 where th1: "s setinterleaves (([], a # list), A)\<longrightarrow>s1 setinterleaves (([], list), A)"  
      using mem_Collect_eq th by fastforce
    from a th1 have th2: "\<forall>s. s setinterleaves (([], a # list), A)\<longrightarrow>(\<forall>t. t\<in> set list\<longrightarrow>t \<notin> A)" 
      by auto
    with a show ?thesis   
      by (metis (no_types, lifting) empty_iff set_ConsD setinterleaving.simps(2))   
  qed
qed
 

lemma ftf_syn1: "a \<notin> set(u) \<and> a \<notin> set(t) \<and> s setinterleaves ((t, u), A) \<longrightarrow> a \<notin> set(s)"
proof (induction "length t + length u" arbitrary:s t u rule:nat_less_induct)
  case 1
  show ?case 
    apply(cases t) using sym emptyLeftProperty apply blast
    apply(cases u) using sym emptyLeftProperty apply blast
    apply(simp split:if_splits, intro conjI impI, elim conjE disjE exE)
         apply (metis "1.hyps" add_less_le_mono length_Cons lessI order_refl set_ConsD)
        apply (metis "1.hyps" add_Suc_right length_Cons lessI set_ConsD) 
       apply (metis "1.hyps" add_less_mono length_Cons lessI set_ConsD) 
      apply (metis "1.hyps" add_Suc_right length_Cons lessI set_ConsD) 
     apply (metis (no_types, hide_lams) "1.hyps" add.commute add_Suc_right insert_iff 
                                         length_Cons lessI list.simps(15)) 
    by (metis "1.hyps" add_less_le_mono length_Cons lessI order_refl set_ConsD)
qed

lemma addNonSyncEmpty: "sa setinterleaves (([], u), A) \<and> y1 \<notin> A \<longrightarrow>
    (sa @ [y1]) setinterleaves (([y1], u), A) \<and> (sa @ [y1]) setinterleaves (([], u @ [y1]), A)"
  proof (induction "length u" arbitrary:sa u rule:nat_less_induct)
    case 1
    then show ?case 
      apply(cases u) 
       apply simp 
    proof-
      fix a list
      assume a: "\<forall>m<length u. \<forall>x. m = length x \<longrightarrow>(\<forall>xa. xa setinterleaves (([], x), A) \<and> y1 \<notin> A \<longrightarrow>
       (xa @ [y1]) setinterleaves (([y1], x), A) \<and> (xa @ [y1]) setinterleaves (([], x @ [y1]), A))"
      and b: "u = a # list"
      from b have th: "sa setinterleaves (([], u), A)\<Longrightarrow>(tl sa) setinterleaves (([], list), A)"  
        by (metis emptyLeftNonSync emptyLeftProperty emptyLeftSelf list.distinct(1) list.sel(3) 
        list.set_sel(2))
      from a b th have th1: "sa setinterleaves (([], u), A) \<and> y1 \<notin> A\<longrightarrow> ((tl sa) @ [y1]) 
      setinterleaves (([y1], list), A)\<and>((tl sa)@[y1]) setinterleaves (([], list@[y1]), A)" by auto
      thus "sa setinterleaves (([], u), A) \<and> y1 \<notin> A \<longrightarrow>
        (sa @ [y1]) setinterleaves (([y1], u), A) \<and> (sa @ [y1]) setinterleaves (([], u @ [y1]), A)"
        using  b th by auto  
    qed
  qed

lemma addNonSync: "sa setinterleaves ((t,u),A)\<and> y1 \<notin> A\<longrightarrow>
(sa@[y1]) setinterleaves ((t@[y1],u),A)\<and>(sa@[y1]) setinterleaves ((t,u@[y1]),A)"
proof (induction "length t + length u" arbitrary:sa t u rule:nat_less_induct)
  case 1
  then show ?case  
    apply(cases t)   
     apply (simp add: addNonSyncEmpty) 
    apply (cases u) 
     apply (metis Sync.sym addNonSyncEmpty append_self_conv2) 
  proof-
    fix a list aa lista
    assume a: "\<forall>m<length t + length u. \<forall>x xa. m = length x + length xa \<longrightarrow>
    (\<forall>xb. xb setinterleaves ((x, xa), A) \<and> y1 \<notin> A \<longrightarrow>(xb @ [y1]) setinterleaves ((x @ [y1], xa), A) 
    \<and> (xb @ [y1]) setinterleaves ((x, xa @ [y1]), A))"
    and b: " t = a # list" 
    and c: "u = aa # lista"
    thus " sa setinterleaves ((t, u), A) \<and> y1 \<notin> A \<longrightarrow>
     (sa @ [y1]) setinterleaves ((t @ [y1], u), A) \<and> (sa @ [y1]) setinterleaves ((t, u @ [y1]), A)"
     proof-
       from b c have th0pre: "a=aa\<and>aa\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A) \<Longrightarrow>
                              (tl sa) setinterleaves ((list,lista), A)" by auto
       from th0pre a b c have th0pre1: "a=aa\<and>aa\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A)\<and> y1 \<notin> A\<Longrightarrow>
       ((tl sa) @ [y1]) setinterleaves ((list@ [y1], lista), A)\<and>
       ((tl sa) @ [y1]) setinterleaves ((list, lista@ [y1]), A)"  
        by (metis add_less_mono length_Cons lessI)  
      from  th0pre th0pre1 b c have th0: "a=aa\<and>aa\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A) \<and> y1 \<notin> A \<longrightarrow>
      (sa @ [y1]) setinterleaves ((t @ [y1], u), A)\<and>(sa @ [y1]) setinterleaves ((t, u @ [y1]), A)"  
        by auto 
      from b c have th1pre: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A) \<Longrightarrow>
                             (tl sa) setinterleaves ((list,aa#lista), A)" by auto
      from th1pre a b c have th1pre1: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A)\<and> y1 \<notin> A\<Longrightarrow>
      ((tl sa) @ [y1]) setinterleaves ((list@ [y1], aa#lista), A)\<and>
      ((tl sa) @ [y1]) setinterleaves ((list, aa#lista@ [y1]), A)"  
        by (metis add_Suc append_Cons length_Cons lessI) 
      from  th1pre th1pre1 b c  have th1: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A) \<and> y1 \<notin> A \<longrightarrow>  
      (sa @ [y1]) setinterleaves ((t @ [y1], u), A)\<and>(sa @ [y1]) setinterleaves ((t, u @ [y1]), A)" 
        by auto  
      from b c have th2pre: "aa\<notin>A\<and>a\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A) \<Longrightarrow>
                             (tl sa) setinterleaves ((a#list,lista), A)" by auto
      from th2pre a b c have th2pre1: "aa\<notin>A\<and>a\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A)\<and> y1 \<notin> A\<Longrightarrow>
      ((tl sa) @ [y1]) setinterleaves ((a#list@ [y1], lista), A)\<and>
      ((tl sa) @ [y1]) setinterleaves ((a#list, lista@ [y1]), A)"  
        by (metis add_Suc_right append_Cons length_Cons lessI)  
      from  th2pre th2pre1 b c have th2: "aa\<notin>A\<and>a\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A) \<and> y1 \<notin> A \<longrightarrow> 
      (sa @ [y1]) setinterleaves ((t @ [y1], u), A)\<and>(sa @ [y1]) setinterleaves ((t, u @ [y1]), A)" 
        by auto
      from b c have th3pre: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>sa setinterleaves ((t, u), A)\<Longrightarrow>
     (tl sa) setinterleaves ((a#list,lista), A)\<or>(tl sa)setinterleaves ((list,aa#lista), A)" by auto
      from th3pre a b c have th3pre1: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>sa setinterleaves ((t, u), A)\<and>
      (tl sa) setinterleaves ((a#list,lista), A)\<and> y1 \<notin> A \<Longrightarrow>
      ((tl sa) @ [y1]) setinterleaves ((a#list@ [y1], lista ), A)\<and>((tl sa) @ [y1]) setinterleaves 
      ((a#list, lista@ [y1] ), A)" 
        by (metis add_Suc_right append_Cons length_Cons lessI)  
      from th3pre a b c have th3pre2: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>sa setinterleaves ((t, u), A)\<and>
      (tl sa) setinterleaves ((list,aa#lista), A)\<and> y1 \<notin> A \<Longrightarrow>((tl sa) @ [y1]) setinterleaves 
      ((list@ [y1], aa#lista ), A)\<and>((tl sa) @ [y1]) setinterleaves ((list, aa#lista @ [y1]), A)"  
        by (metis add_Suc append_Cons length_Cons lessI)         
      from th3pre th3pre1 th3pre2 a b c have th3: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>sa setinterleaves ((t, u), A) \<and> 
      y1 \<notin> A \<longrightarrow>(sa @ [y1]) setinterleaves ((t @ [y1], u), A) \<and> 
      (sa @ [y1]) setinterleaves ((t, u @ [y1]), A)" by auto 
      show ?thesis  
        using b c th0 th1 th2 th3 by auto
    qed
  qed
qed

lemma addSyncEmpty: "sa setinterleaves (([], u), A) \<and> y1 \<in> A \<longrightarrow> 
                    (sa @ [y1]) setinterleaves (([y1], u @ [y1]), A)"
  proof (induction "length u" arbitrary:sa u rule:nat_less_induct)
    case 1
    then show ?case 
      apply(cases u) 
       apply simp 
    proof-
      fix a list
      assume a: "\<forall>m<length u. \<forall>x. m = length x \<longrightarrow>(\<forall>xa. xa setinterleaves (([], x), A) \<and> y1 \<in> A 
                 \<longrightarrow> (xa @ [y1]) setinterleaves (([y1], x @ [y1]), A))"
      and b: "u = a # list"  
      from b have th: "sa setinterleaves (([], u), A)\<Longrightarrow>(tl sa) setinterleaves (([], list), A)"  
        by (metis emptyLeftNonSync emptyLeftProperty emptyLeftSelf list.distinct(1) list.sel(3) 
           list.set_sel(2))
      from a th have th1: "sa setinterleaves (([], u), A) \<and> y1 \<in> A\<Longrightarrow> 
      ((tl sa) @ [y1]) setinterleaves (([y1], list @ [y1]), A)" using b by auto
      thus "sa setinterleaves (([], u), A) \<and> y1 \<in> A \<longrightarrow> 
           (sa @ [y1]) setinterleaves (([y1], u @ [y1]), A)" using b th by auto  
    qed
  qed 
 
lemma addSync: "sa setinterleaves ((t,u),A)\<and> y1 \<in> A\<longrightarrow>(sa@[y1]) setinterleaves ((t@[y1],u@[y1]),A)"
proof (induction "length t + length u" arbitrary:sa t u rule:nat_less_induct)
  case 1
  then show ?case 
    apply(cases t) 
     apply (simp add: addSyncEmpty)
    apply(cases u) 
     apply (metis Sync.sym addSyncEmpty append.left_neutral) 
  proof-
    fix a list aa lista
    assume a: "\<forall>m<length t + length u. \<forall>x xa. m = length x + length xa \<longrightarrow>
                 (\<forall>xb. xb setinterleaves ((x, xa), A) \<and> y1 \<in> A \<longrightarrow> (xb @ [y1]) setinterleaves 
                 ((x @ [y1], xa @ [y1]), A))"
    and b: "t = a # list "
    and c: " u = aa # lista"
    thus "sa setinterleaves((t, u),A)\<and>y1 \<in>A\<longrightarrow>(sa @ [y1]) setinterleaves ((t @ [y1], u @ [y1]), A)"
    proof-
      from b c have th0pre: "a=aa\<and>aa\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A) \<Longrightarrow>
      (tl sa) setinterleaves ((list,lista), A)" by auto
      from th0pre a b c have th0pre1: "a=aa\<and>aa\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A)\<and> y1 \<in> A\<Longrightarrow>
      ((tl sa) @ [y1]) setinterleaves ((list@ [y1], lista @ [y1]), A)"  
        by (metis add_less_mono length_Cons lessI)  
      from  th0pre th0pre1 b c have th0: "a=aa\<and>a\<in>A\<Longrightarrow>sa setinterleaves ((t, u), A) \<and> y1 \<in> A \<longrightarrow> 
      (sa @ [y1]) setinterleaves ((t @ [y1], u @ [y1]), A)" by auto 
      from b c have th1pre: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A) \<Longrightarrow>
      (tl sa) setinterleaves ((list,aa#lista), A)" by auto
      from th1pre a b c have th1pre1: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A)\<and> y1 \<in> A\<Longrightarrow>
      ((tl sa) @ [y1]) setinterleaves ((list@ [y1], aa#lista @ [y1]), A)"  
        by (metis add_Suc append_Cons length_Cons lessI) 
      from  th1pre th1pre1 b c  have th1: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A) \<and> y1 \<in> A \<longrightarrow> 
      (sa @ [y1]) setinterleaves ((t @ [y1], u @ [y1]), A)" by auto  
      from b c have th2pre: "aa\<notin>A\<and>a\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A) \<Longrightarrow>
      (tl sa) setinterleaves ((a#list,lista), A)" by auto
      from th2pre a b c have th2pre1: "aa\<notin>A\<and>a\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A)\<and> y1 \<in> A\<Longrightarrow>
      ((tl sa) @ [y1]) setinterleaves ((a#list@ [y1], lista @ [y1]), A)"  
        by (metis add_Suc_right append_Cons length_Cons lessI)  
      from  th2pre th2pre1 b c have th2: "aa\<notin>A\<and>a\<in> A\<Longrightarrow>sa setinterleaves ((t, u), A) \<and> y1 \<in> A \<longrightarrow> 
      (sa @ [y1]) setinterleaves ((t @ [y1], u @ [y1]), A)" by auto
      from b c have th3pre: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>sa setinterleaves ((t, u), A)\<Longrightarrow>
      (tl sa) setinterleaves((a#list,lista), A)\<or>(tl sa)setinterleaves ((list,aa#lista), A)" by auto
      from th3pre a b c have th3pre1: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>sa setinterleaves ((t, u), A)\<and>
      (tl sa) setinterleaves ((a#list,lista), A)\<and> y1 \<in> A \<Longrightarrow>
      ((tl sa) @ [y1]) setinterleaves ((a#list@ [y1], lista @ [y1]), A)" 
        by (metis add_Suc_right append_Cons length_Cons lessI)  
      from th3pre a b c have th3pre2: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>sa setinterleaves ((t, u), A)\<and>
      (tl sa) setinterleaves ((list,aa#lista), A)\<and> y1 \<in> A \<Longrightarrow>
      ((tl sa) @ [y1]) setinterleaves ((list@ [y1], aa#lista @ [y1]), A)" 
        by (metis add_Suc append_Cons length_Cons lessI)         
      from th3pre th3pre1 th3pre2 a b c have th3: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>sa setinterleaves ((t, u), A) \<and> 
      y1 \<in> A \<longrightarrow> (sa @ [y1]) setinterleaves ((t @ [y1], u @ [y1]), A)" by auto 
      show ?thesis  
        using b c th0 th1 th2 th3 by auto
    qed
  qed
qed
 

lemma doubleReverse: "s1 setinterleaves ((t, u), A)\<longrightarrow>(rev s1) setinterleaves ((rev t, rev u), A)"
proof (induction "length t + length u" arbitrary:s1 t u rule:nat_less_induct)
  case 1
  then show ?case 
    apply(cases t)  
    using emptyLeftNonSync 
     apply (metis emptyLeftProperty emptyLeftSelf rev.simps(1) set_rev)  
    apply(cases u) 
    using sym 
     apply (metis (no_types, lifting) emptyLeftNonSync emptyLeftProperty emptyLeftSelf 
     rev.simps(1) set_rev) 
  proof-
    fix a list aa lista
    assume a: "\<forall>m<length t + length u. \<forall>x xa. m = length x + length xa \<longrightarrow>
               (\<forall>xb. xb setinterleaves ((x, xa), A) \<longrightarrow>rev xb setinterleaves ((rev x, rev xa), A))"
    and b: "t = a # list"
    and c: "u = aa # lista"
    thus "s1 setinterleaves ((t, u), A) \<longrightarrow>rev s1 setinterleaves ((rev t, rev u), A)"  
    proof-
      from b c have th0pre: "a=aa\<and>aa\<in> A\<Longrightarrow>s1 setinterleaves ((t, u), A)\<Longrightarrow>
      (tl s1) setinterleaves ((list,lista), A)" by auto
      from th0pre a b c have th0pre1: "a=aa\<and>aa\<in> A\<Longrightarrow>s1 setinterleaves ((t, u), A)\<Longrightarrow>
      ((rev (tl s1)) setinterleaves ((rev list, rev lista), A))"  
        by (metis add_less_mono length_Cons lessI)
      from  th0pre th0pre1 b c have th0: "a=aa\<and>aa\<in> A\<Longrightarrow>s1 setinterleaves ((t, u), A) \<longrightarrow>
      rev s1 setinterleaves ((rev t, rev u), A)"   using addSync by fastforce 
      from b c have th1pre: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>s1 setinterleaves ((t, u), A)\<Longrightarrow>
      (tl s1) setinterleaves ((list,aa#lista), A)" by auto
      from th1pre a b c have th1pre1: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>s1 setinterleaves ((t, u), A)\<Longrightarrow>
      ((rev (tl s1)) setinterleaves ((rev list, rev (aa#lista)), A))"  
        by (metis add_less_mono1 length_Cons lessI)          
      from  th1pre th1pre1 b c have th1: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>s1 setinterleaves ((t, u), A) \<longrightarrow>
      rev s1 setinterleaves ((rev t, rev u), A)"  using addNonSync by fastforce  
      from b c have th2pre: "aa\<notin>A\<and>a\<in> A\<Longrightarrow>s1 setinterleaves ((t, u), A)\<Longrightarrow>
      (tl s1) setinterleaves ((a#list,lista), A)" by auto
      from th2pre a b c have th2pre1: "aa\<notin>A\<and>a\<in> A\<Longrightarrow>s1 setinterleaves ((t, u), A)\<Longrightarrow>
      ((rev (tl s1)) setinterleaves ((rev (a#list), rev lista), A))"  
        by (metis add_Suc_right length_Cons lessI)        
      from  th2pre th2pre1 b c have th2: "aa\<notin>A\<and>a\<in> A\<Longrightarrow>s1 setinterleaves ((t, u), A) \<longrightarrow>
      rev s1 setinterleaves ((rev t, rev u), A)"  
        using addNonSync by fastforce 
      from b c have th3pre: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>s1 setinterleaves ((t, u), A)\<Longrightarrow>
      (tl s1) setinterleaves ((a#list,lista),A)\<or>(tl s1) setinterleaves((list,aa#lista), A)" by auto
      from th3pre a b c have th3pre1: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>s1 setinterleaves ((t, u), A)\<and>
      (tl s1) setinterleaves ((a#list,lista), A) \<Longrightarrow>
      ((rev (tl s1)) setinterleaves ((rev (a#list), rev (lista)), A))"   
        by (metis add_Suc_right length_Cons lessI)
      from th3pre a b c have th3pre2: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>s1 setinterleaves ((t, u), A)\<and>
      (tl s1) setinterleaves ((list,aa#lista), A) \<Longrightarrow>
      ((rev (tl s1)) setinterleaves ((rev (list), rev (aa#lista)), A))"  
        by (metis add_less_mono1 length_Cons lessI)
      from  th3pre1 have th3pre31: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>s1 setinterleaves ((t, u), A)\<and>
      ((rev (tl s1)) setinterleaves ((rev (a#list), rev (lista)), A))\<longrightarrow>
      ((rev (tl s1))@[aa]) setinterleaves ((rev (a#list), (rev (lista))@[aa]), A)"
        by (simp add: addNonSync)
      from  th3pre2 have th3pre32: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>s1 setinterleaves ((t, u), A)\<and>
      ((rev (tl s1)) setinterleaves ((rev (list), rev (aa#lista)), A))\<longrightarrow>
      ((rev (tl s1))@[a]) setinterleaves (((rev (list)@[a]), (rev (aa#lista))), A)"
        by (simp add: addNonSync)
      from th3pre th3pre1 th3pre2 th3pre31 th3pre32 a b c have th3: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>
      s1 setinterleaves ((t, u), A) \<longrightarrow>rev s1 setinterleaves ((rev t, rev u), A)" by force
      show?thesis  
        using b c th0 th1 th2 th3 by auto
    qed 
  qed
qed
 
 
lemma  ftf_syn21: "(a\<in>set(u)\<and>a\<notin>set(t)\<or>a\<in>set(t)\<and>a\<notin>set(u))\<and>a\<in>A\<longrightarrow>setinterleaving(u, A ,t)= {}"
proof (induction "length t + length u" arbitrary: t u rule:nat_less_induct)
  case 1
  then show ?case 
    apply(cases t)  
    using Sync.sym emptyLeftNonSync apply fastforce 
    apply(cases u)  
     apply auto[1]
    apply(simp split:if_splits, intro conjI impI, elim conjE disjE exE)
             apply blast
            apply auto[1]  
           apply blast 
          apply auto[1]  
         apply auto[1]  
    using less_SucI apply blast  
       apply auto[1] 
      apply auto[1]  
    using list.simps(15) apply auto[1] 
    by auto 
qed

lemma ftf_syn32: "u=u1@[tick]\<and>t=t1@[tick]\<and>s setinterleaves ((t, u), insert tick (ev ` A))\<Longrightarrow>
                  \<exists>s1. s1 setinterleaves ((t1, u1), insert tick (ev ` A))\<and> (s=s1@[tick])"
proof-
  assume h: "u=u1@[tick]\<and>t=t1@[tick]\<and>s setinterleaves ((t, u), insert tick (ev ` A))"
  thus "\<exists>s1. s1 setinterleaves ((t1, u1), insert tick (ev ` A))\<and> (s=s1@[tick])"
  proof-
    from h have a:"rev u=tick#rev u1" by auto
    from h have b:"rev t=tick#rev t1" by auto
    from h have ab: "(rev s)  setinterleaves ((tick#rev t1, tick#rev u1), insert tick (ev ` A))" 
      using doubleReverse by fastforce
    from h obtain ss where c: "ss  setinterleaves  ((rev t1, rev u1), insert tick (ev ` A))\<and> 
    ss=tl(rev s)" using ab by auto 
    from c have d: "(rev ss)  setinterleaves  (( t1,  u1), insert tick (ev ` A))" 
      using doubleReverse by fastforce
    from d have e: "rev s=tick#ss"  
      using ab append_Cons_eq_iff c by auto
    show ?thesis  
      using d e by blast
  qed
qed


lemma syncWithTick_imp_NTF: "(s @ [tick]) setinterleaves ((t, u),insert tick (ev ` A)) \<Longrightarrow>t\<in> T P\<Longrightarrow>
  u\<in> T Q\<Longrightarrow> \<exists>t1 u1. t=t1@[tick] \<and> u=u1@[tick]\<and> s setinterleaves ((t1, u1), insert tick (ev ` A))"  
proof-
  assume h: "(s @ [tick]) setinterleaves ((t, u), insert tick (ev ` A))"
  and h1: "t\<in> T P"
  and h2: "u\<in> T Q"
  thus "\<exists>t1 u1. t=t1@[tick] \<and> u=u1@[tick]\<and> s setinterleaves ((t1, u1), insert tick (ev ` A))"
  proof-
    from h have a: "(tick#rev s) setinterleaves ((rev t, rev u), insert tick (ev ` A))" 
      using doubleReverse by fastforce
    from h obtain tt uu where b: "t=tt@[tick]\<and>u=uu@[tick]"  
      by (metis T_nonTickFree_imp_decomp empty_iff ftf_syn1 ftf_syn21 h1 h2 insertI1 
          non_tickFree_tick tickFree_append tickFree_def)
    from h b have d: "s setinterleaves ((tt, uu), insert tick (ev ` A))"  
      using ftf_syn32 by blast
    show ?thesis  
      using b d by blast
  qed 
qed

lemma synPrefix1: " ta = [] \<Longrightarrow> \<exists>t1 u1. (s @ t) setinterleaves ((ta, u), A) \<longrightarrow> 
                    t1 \<le> ta \<and> u1 \<le> u \<and> s setinterleaves ((t1, u1), A)"
proof-
  assume a: "ta = []"
  obtain u1 where th: "u1=s" by blast
  from a have th2: "(s @ t) setinterleaves ((ta, u), A) \<longrightarrow> (s @ t)= u"  
    by (simp add: a emptyLeftProperty)
  from a have th3: "(s @ t) setinterleaves ((ta, u), A) \<longrightarrow> (\<forall>t1. t1\<in>set u\<longrightarrow>t1\<notin>A)"  
    by (simp add: emptyLeftNonSync)
  from a th have th1: "(s @ t) setinterleaves ((ta, u), A) \<longrightarrow> [] \<le> ta \<and> u1 \<le> u " 
    using le_list_def th2 by blast 
  from a th have thh1: "(s @ t) setinterleaves ((ta, u), A)\<and> (\<forall>t1. t1\<in>set u1\<longrightarrow>t1\<notin>A) \<longrightarrow> 
  s setinterleaves (([], u1), A)"  by (simp add: emptyLeftSelf)
  thus "\<exists>t1 u1. (s @ t) setinterleaves ((ta, u), A) \<longrightarrow> t1 \<le> ta \<and> u1 \<le> u \<and> 
  s setinterleaves ((t1, u1), A)" using th th1 th2 th3 thh1 by fastforce 
qed
 

lemma synPrefix: "\<exists>t1 u1. (s @ t) setinterleaves ((ta, u), A)\<longrightarrow>
                  t1\<le>ta\<and>u1\<le>u\<and>s setinterleaves ((t1, u1), A)"
proof (induction "length ta + length u" arbitrary: s t ta u rule:nat_less_induct)
  case 1
  then show ?case 
    apply(cases ta)  
     using synPrefix1 apply fastforce 
    apply(cases u) 
     using sym synPrefix1 apply metis 
   proof-
     fix a list aa lista s t
     assume a: " \<forall>m<length ta + length u. \<forall>x xa. m = length x + length xa \<longrightarrow>
                 (\<forall>xb xc. \<exists>t1 u1. (xb @ xc) setinterleaves ((x, xa), A) \<longrightarrow>
                 t1 \<le> x \<and> u1 \<le> xa \<and> xb setinterleaves ((t1, u1), A))"
     and b: "ta = a # list"
     and c: "u = aa # lista " 
     thus " \<exists>t1 u1. (s @ t) setinterleaves ((ta, u), A) \<longrightarrow> t1 \<le> ta \<and> u1 \<le> u \<and> 
            s setinterleaves ((t1, u1), A)" 
     proof-
       from a have th0: "\<forall>xb xc. \<exists>t1 u1. (xb @ xc) setinterleaves ((list, lista), A) \<longrightarrow>
                                  t1 \<le> list \<and> u1 \<le> lista \<and> xb setinterleaves ((t1, u1), A)"  
         by (metis add_less_le_mono b c impossible_Cons le_cases not_le_imp_less)
       from b c obtain yb where thp: "a=aa\<and>a\<in> A\<and>(s@t) setinterleaves ((ta, u), A)\<and>length s >1 \<Longrightarrow>
       yb=tl s" by blast
       with b c have thp4: "a=aa\<and>a\<in> A\<and>(s @ t) setinterleaves ((ta, u), A)\<and>length s >1 \<Longrightarrow>s=a#yb" 
         by (auto, metis Cons_eq_append_conv list.sel(3) list.size(3) not_less0)
       have thp5: "a=aa\<and>a\<in> A\<and>(s @ t) setinterleaves ((ta, u), A)\<and>length s >1 \<Longrightarrow>
       (yb @ t) setinterleaves ((list, lista), A)"  using b c thp4 by auto 
       from th0 obtain yt yu where thp1: "a = aa \<and> a \<in> A \<Longrightarrow> (s @ t) setinterleaves ((ta, u), A) \<and> 
       1 < length s\<Longrightarrow>yb setinterleaves ((yt, yu), A)\<and>yt\<le>list\<and>yu\<le>lista"  using thp5 by blast 
       from thp thp1 have thp2: "a=aa\<and>a\<in> A\<Longrightarrow> (s @ t) setinterleaves ((ta, u), A)\<and> length s >1\<longrightarrow> 
       s setinterleaves ((a#yt, aa#yu), A)" using thp4 by auto 
       from b c have thp3: "a=aa\<and>a\<in> A\<Longrightarrow> (s @ t) setinterleaves ((ta, u), A) \<and> length s=1\<longrightarrow>
       s setinterleaves (([a], [aa]), A)" 
         using append_eq_append_conv2[of s t "[aa]"] by (auto, metis append_Nil2 
         append_eq_append_conv length_Cons list.size(3))
       have thp6: "a=aa\<and>a\<in> A\<Longrightarrow> (s @ t) setinterleaves ((ta, u), A) \<and> length s=0\<longrightarrow>
       s setinterleaves (([], []), A)" by auto
       from thp1 have thp7: "a=aa\<and>a\<in> A\<Longrightarrow> (s @ t) setinterleaves ((ta, u), A)\<and> length s >1\<Longrightarrow>
       (a # yt)\<le>ta \<and>(aa # yu)\<le>u"  by (metis b c le_less less_cons)  
       have th: "a=aa\<and>a\<in> A\<Longrightarrow>\<exists>t1 u1. (s @ t) setinterleaves ((ta, u), A) \<longrightarrow> 
       t1 \<le> ta \<and> u1 \<le> u \<and> s setinterleaves ((t1, u1), A)"
       proof -
         assume dd:"a=aa \<and> a\<in> A"
         consider (aa) "length s = 0" | (bb) "length s = 1" | (cc) "length s > 1"
           by linarith
         then show ?thesis 
         proof cases 
           case aa
           with thp6 show ?thesis 
             by (rule_tac x="[]" in exI, rule_tac x="[]" in exI, simp) 
         next
           case bb
           with dd thp3 b c show ?thesis 
             by (rule_tac x="[a]" in exI, rule_tac x="[a]" in exI, auto simp add: le_list_def)            
         next
           case cc
           with dd thp2 thp7 b c show ?thesis
             by (rule_tac x="a#yt" in exI, rule_tac x="a#yu" in exI, auto simp add: le_list_def)   
        qed
      qed
      from b c have th1pre: "a\<notin>A\<and>aa\<in> A\<and>(s @ t) setinterleaves ((ta, u), A) \<longrightarrow>
      tl (s @ t) setinterleaves ((list, u), A)\<and>hd (s@t)=a" by auto 
      from a b c obtain yt1 yu1 where th1pre1: "a\<notin>A\<and>aa\<in> A\<and>(s @ t) setinterleaves ((ta, u), A)\<and>
      length s>0\<longrightarrow>yt1\<le>list\<and> yu1 \<le> u\<and> tl s setinterleaves ((yt1, yu1), A)"  
        by (metis (no_types, lifting) length_Cons length_greater_0_conv lessI plus_nat.simps(2) 
        th1pre tl_append2)
      from b have th1pre2: "yt1\<le>list\<longrightarrow>a#yt1\<le>ta"  
        by (simp add: le_less less_cons) 
      from b c have th1pre3: "a\<notin>A\<and>aa\<in> A\<and>tl s setinterleaves ((yt1, yu1), A)\<longrightarrow>
      (a#(tl s)) setinterleaves ((a#yt1, yu1), A)"  
        by (metis (mono_tags, lifting) addNonSync doubleReverse rev.simps(2) rev_rev_ident)  
      from b c th1pre1 th1pre2 have th1pre4: "a\<notin>A\<and>aa\<in> A\<and>(s @ t) setinterleaves ((ta, u), A)\<and>
      length s>0 \<longrightarrow>a#yt1\<le>ta\<and> yu1 \<le>u\<and> s setinterleaves ((a#yt1, yu1), A)" 
        using th1pre th1pre3  by fastforce  
      have th1pre5:"a\<notin>A\<and>aa\<in> A\<and>(s @ t) setinterleaves ((ta, u), A)\<and>length s=0 \<longrightarrow>[]\<le>ta\<and> [] \<le>u\<and> 
      s setinterleaves (([], []), A)" by auto
      have th1: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>\<exists>t1 u1. (s @ t) setinterleaves ((ta, u), A) \<longrightarrow> 
      t1 \<le> ta \<and> u1 \<le> u \<and> s setinterleaves ((t1, u1), A)"  using th1pre4 th1pre5 by blast 
      from b c have th2pre: "aa\<notin>A\<and>a\<in> A\<and>(s @ t) setinterleaves ((ta, u), A) \<longrightarrow>
      tl (s @ t) setinterleaves ((ta, lista), A)\<and>hd (s@t)=aa" by auto 
      from a b c obtain yt2 yu2 where th2pre1: "aa\<notin>A\<and>a\<in> A\<and>(s @ t) setinterleaves ((ta, u), A)\<and>
      length s>0\<longrightarrow>yt2\<le>ta\<and> yu2 \<le> lista\<and> (tl s) setinterleaves ((yt2, yu2), A)"  
        by (metis (no_types, lifting) add_Suc_right length_Cons length_greater_0_conv lessI 
        th2pre tl_append2)  
      from c have th2pre2: "yu2\<le>lista\<longrightarrow>aa#yu2\<le>u"   
        by (simp add: le_less less_cons) 
      from b c have th2pre3: "aa\<notin>A\<and>a\<in> A\<and>tl s setinterleaves ((yt2, yu2), A)\<longrightarrow>
      (aa#(tl s)) setinterleaves ((yt2, aa#yu2), A)"  
        by (metis (mono_tags, lifting) addNonSync doubleReverse rev.simps(2) rev_rev_ident)  
      from b c th2pre1 th2pre2 have th2pre4: "aa\<notin>A\<and>a\<in> A\<and>(s @ t) setinterleaves ((ta, u), A)\<and>
      length s>0 \<longrightarrow>yt2\<le>ta\<and> aa#yu2 \<le>u\<and> s setinterleaves ((yt2, aa#yu2), A)" 
        using th2pre th2pre3  by fastforce  
      have th2pre5:"aa\<notin>A\<and>a\<in> A\<and>(s @ t) setinterleaves ((ta, u), A)\<and>length s=0 \<longrightarrow>
      []\<le>ta\<and> [] \<le>u\<and> s setinterleaves (([], []), A)" by auto
      have th2: "aa\<notin>A\<and>a\<in> A\<Longrightarrow>\<exists>t1 u1. (s @ t) setinterleaves ((ta, u), A) \<longrightarrow> 
      t1 \<le> ta \<and> u1 \<le> u \<and> s setinterleaves ((t1, u1), A)"  using th2pre4 th2pre5 by blast      
      from b c have th3pre: "aa\<notin>A\<and>a\<notin> A\<and>(s @ t) setinterleaves ((ta, u), A)\<longrightarrow>tl (s @ t) 
      setinterleaves ((ta, lista), A)\<and>hd (s@t)=aa\<or>tl (s @ t)setinterleaves((list, u), A)\<and>hd(s@t)=a" 
        by auto
      from a b c th3pre obtain yt31 yu31 where th3pre1: "aa\<notin>A\<and>a\<notin> A\<and>
      (s @ t) setinterleaves ((ta, u), A)\<and>tl (s @ t) setinterleaves ((ta, lista), A)\<and>
      hd (s@t)=aa\<and>length s>0\<longrightarrow>yt31\<le>ta\<and> yu31 \<le> lista\<and> (tl s) setinterleaves ((yt31, yu31), A)" 
        by(metis(no_types,lifting)add_Suc_right length_Cons length_greater_0_conv lessI tl_append2) 
      from a b c th3pre obtain yt32 yu32 where th3pre2: "aa\<notin>A\<and>a\<notin>A\<and>(s@t)setinterleaves ((ta, u),A)\<and>
      tl (s @ t) setinterleaves ((list, u), A)\<and>hd (s@t)=a\<and>length s>0\<longrightarrow>yt32\<le>list\<and> yu32 \<le>u\<and> 
      (tl s) setinterleaves ((yt32, yu32), A)"  
        by (metis add_less_mono1 impossible_Cons le_neq_implies_less length_greater_0_conv 
        nat_le_linear tl_append2)
      from b c have th3pre3: "aa\<notin>A\<and>a\<notin> A\<and>tl s setinterleaves ((yt31, yu31), A)\<longrightarrow>
      (aa#(tl s)) setinterleaves ((yt31, aa#yu31), A)"  
        by (metis (mono_tags, lifting) addNonSync doubleReverse rev.simps(2) rev_rev_ident) 
      from b c th3pre1 th3pre2 have th3pre4: "aa\<notin>A\<and>a\<notin> A\<and>(s @ t) setinterleaves ((ta, u), A)\<and>
      length s>0\<and>tl (s @ t) setinterleaves ((ta, lista), A)\<and>hd (s@t)=aa \<longrightarrow>yt31\<le>ta\<and> aa#yu31 \<le>u\<and> 
      s setinterleaves ((yt31, aa#yu31), A)"  
        by (metis hd_append2 le_less length_greater_0_conv less_cons list.exhaust_sel th3pre3)
      from b c have th3pre5: "aa\<notin>A\<and>a\<notin> A\<and>tl s setinterleaves ((yt32, yu32), A)\<longrightarrow>
      (a#(tl s)) setinterleaves ((a#yt32, yu32), A)"  
        by (metis (mono_tags, lifting) addNonSync doubleReverse rev.simps(2) rev_rev_ident) 
      from b c th3pre1 th3pre2 have th3pre6: "aa\<notin>A\<and>a\<notin> A\<and>(s @ t) setinterleaves ((ta, u), A)\<and>
      length s>0\<and>tl (s @ t) setinterleaves ((list, u), A)\<and>hd (s@t)=a \<longrightarrow>a#yt32\<le>ta\<and> yu32 \<le>u\<and> 
      s setinterleaves ((a#yt32, yu32), A)" 
        using th3pre th3pre5  by (metis hd_append2 le_less length_greater_0_conv less_cons 
        list.exhaust_sel)
      have th3pre7:"aa\<notin>A\<and>a\<notin> A\<and>(s @ t) setinterleaves ((ta, u), A)\<and>length s=0 \<longrightarrow>
      []\<le>ta\<and> [] \<le>u\<and> s setinterleaves (([], []), A)" by auto
      have th3: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>\<exists>t1 u1. (s @ t) setinterleaves ((ta, u), A) \<longrightarrow> 
      t1 \<le> ta \<and> u1 \<le> u \<and> s setinterleaves ((t1, u1), A)"  
        using th3pre th3pre4 th3pre6 th3pre7 by blast 
      with a b c th th1 th2 show ?thesis
        by fastforce
    qed
  qed
qed

lemma syncWithTick_imp_NTF1: "(s @ [tick]) setinterleaves ((t, u), insert tick (ev ` A)) \<Longrightarrow>
t\<in> T P\<Longrightarrow>u\<in> T Q\<Longrightarrow> \<exists> t u Xa Y. (t, Xa) \<in> F P \<and> ( (u, Y) \<in> F Q \<and> s setinterleaves 
((t, u), insert tick (ev ` A)) \<and> X - {tick} = (Xa \<union> Y) \<inter> insert tick (ev ` A) \<union> Xa \<inter> Y)"
  apply (drule syncWithTick_imp_NTF)
    apply simp
   apply simp 
proof -
  assume A: "t \<in> T P"
  and B: "u \<in> T Q"
  and C: "\<exists>t1 u1. t = t1 @ [tick]\<and>u = u1@[tick]\<and>s setinterleaves ((t1, u1), insert tick (ev ` A))" 
  from C obtain t1 u1 where D: "t = t1 @ [tick] \<and> u = u1 @ [tick] \<and> s setinterleaves 
  ((t1, u1), insert tick (ev ` A))" by blast
  from A B D have E: "(t1, X-{tick}) \<in> F P\<and>(u1, X-{tick}) \<in> F Q"  
    by (simp add: T_F process_charn)  
  thus  " \<exists>t u Xa Y. (t, Xa) \<in> F P \<and> (u, Y) \<in> F Q \<and> s setinterleaves ((t, u), insert tick (ev ` A)) 
          \<and> X - {tick} = (Xa \<union> Y) \<inter> insert tick (ev ` A) \<union> Xa \<inter> Y"
    using A B C D E by blast
qed

lemma ftf_syn: "front_tickFree u\<Longrightarrow>front_tickFree t\<Longrightarrow>s setinterleaves ((t, u),insert tick (ev ` A))
      \<Longrightarrow>front_tickFree s"
proof-
  assume A: "front_tickFree u"
  assume B: "front_tickFree t"
  assume C: "s setinterleaves ((t, u), insert tick (ev ` A))"
  thus "front_tickFree s" 
  proof-
    from A obtain u1 where A1: "\<forall> u2. u1\<le>u\<and>tickFree u1\<and>  (u2\<le>u\<and>tickFree u2\<longrightarrow>u2\<le>u1)"   
      by (metis append.right_neutral append_eq_first_pref_spec front_tickFree_charn le_list_def 
         tickFree_Nil)
    from A A1 have AA1: "u1=u\<or>u=u1@[tick]" 
      by (metis(no_types, lifting) antisym append_Nil2 append_eq_first_pref_spec append_is_Nil_conv 
      front_tickFree_charn le_list_def less_list_def less_self nonTickFree_n_frontTickFree)
    from B obtain t1 where B1: "\<forall> t2. t1\<le>t\<and>tickFree t1\<and>  (t2\<le>t\<and>tickFree t2\<longrightarrow>t2\<le>t1)"
      by (metis append.right_neutral append_eq_first_pref_spec front_tickFree_charn le_list_def 
      tickFree_Nil)
    from B B1 have BB1: "t1=t\<or>t=t1@[tick]" 
      by (metis(no_types, lifting) antisym append_Nil2 append_eq_first_pref_spec append_is_Nil_conv 
      front_tickFree_charn le_list_def less_list_def less_self nonTickFree_n_frontTickFree)
    from A1 B1 have C1: "\<forall>s1. s1 setinterleaves ((t1, u1), insert tick (ev ` A))\<longrightarrow>tickFree s1"  
      by (meson ftf_syn1 tickFree_def)
    from AA1 BB1 have CC1: "u1=u\<and>t1=t\<longrightarrow>tickFree s" 
      by (simp add: C C1)
    from AA1 BB1 have CC2: "u1=u\<and>t=t1@[tick]\<longrightarrow>tickFree s"  using ftf_syn21  
      by (metis A1 C equals0D insertI1 non_tickFree_tick tickFree_append tickFree_def)
    from AA1 BB1 have CC3: "u=u1@[tick]\<and>t1=t\<longrightarrow>tickFree s"  using ftf_syn21 
      by (metis B1 C insertI1 insert_not_empty mk_disjoint_insert non_tickFree_tick tickFree_append 
      tickFree_def) 
    from AA1 BB1 have CC4: "u=u1@[tick]\<and>t=t1@[tick]\<Longrightarrow>
    \<exists>s1. s1 setinterleaves ((t1, u1), insert tick (ev ` A))\<and>(s=s1@[tick])"  
      using C ftf_syn32 by blast  
    from C1 CC4 have CC5: "front_tickFree s"  
      using AA1 BB1 CC1 CC2 CC3 tickFree_implies_front_tickFree 
      tickFree_implies_front_tickFree_single by auto
    with A1 B1 C1 AA1 BB1 show ?thesis  
      using CC1 CC2 CC3 tickFree_implies_front_tickFree by auto
    qed
  qed

lemma is_processT5_SYNC2: "\<And> sa Y t u Xa Ya.  (t,Xa) \<in> F P \<and> (u,Ya) \<in> F Q \<and>  
(sa setinterleaves ((t,u),insert tick (ev ` A))) \<Longrightarrow>\<forall>c. c \<in> Y \<longrightarrow>(\<forall> t1 u1. (sa@[c]) setinterleaves 
((t1,u1),insert tick (ev ` A))\<longrightarrow>(((t1,{})\<in>F P\<longrightarrow>(u1, {})\<notin>F Q)\<and>((t1,{})\<in>F Q\<longrightarrow>(u1, {})\<notin>F P))) \<Longrightarrow>
\<exists>t2 u2 Xb. (t2, Xb) \<in> F P \<and> (\<exists>Yb.(u2, Yb) \<in> F Q \<and>sa setinterleaves ((t2, u2), insert tick (ev ` A)) 
\<and>(Xa \<union> Ya) \<inter> insert tick (ev ` A) \<union> Xa \<inter> Ya \<union> Y = (Xb \<union> Yb) \<inter> insert tick (ev ` A) \<union> Xb \<inter> Yb)"  
proof -
  fix sa Y t u Xa Ya
  assume A: "(t,Xa) \<in> F P \<and> (u,Ya) \<in> F Q \<and>(sa setinterleaves ((t,u),insert tick (ev ` A)))" 
  and B: " \<forall>c. c \<in> Y \<longrightarrow>(\<forall> t1 u1. (sa@[c]) setinterleaves ((t1,u1),insert tick (ev ` A))\<longrightarrow>
  (((t1,{})\<in>F P\<longrightarrow>(u1, {})\<notin>F Q)\<and>((t1,{})\<in>F Q\<longrightarrow>(u1, {})\<notin>F P)))"
  thus "\<exists>t2 u2 Xb. (t2, Xb) \<in> F P \<and> (\<exists>Yb. (u2, Yb) \<in> F Q \<and> sa setinterleaves 
  ((t2, u2), insert tick (ev ` A)) \<and>(Xa \<union> Ya) \<inter> insert tick (ev ` A) \<union> Xa \<inter> Ya \<union> Y = (Xb \<union> Yb) \<inter> 
  insert tick (ev ` A) \<union> Xb \<inter> Yb)"
  proof-
    from A B obtain Y1 Y2 where A1: "(Y1=(Y\<inter>insert tick (ev ` A)))\<and>(Y2=(Y - insert tick (ev ` A)))" 
      by blast
    from A1 have AA1: "Y1 \<union> Y2 = Y" 
      by blast 
    from A1 have newAA: "\<forall>y\<in>Y1. y\<in> insert tick (ev ` A)" 
      by blast
    from A1 have newAAA: "\<forall>y\<in>Y2. y\<notin> insert tick (ev ` A)" 
      by blast
    from B A1 have AA2: "\<forall>z\<in>Y1.(t@[z], {})\<notin>F P\<or>(u@[z], {})\<notin>F Q" 
    proof(cases "\<exists>z\<in>Y1. (t@[z], {})\<in>F P\<and>(u@[z], {})\<in>F Q")
      case True
      from True obtain z1 where TrA: "z1\<in>Y1\<and>(t@[z1], {})\<in>F P\<and>(u@[z1], {})\<in>F Q" 
        by blast
      from TrA A have TrB: "\<lbrakk>sa setinterleaves ((t,u),insert tick(ev ` A)); z1\<in>insert tick (ev ` A)\<rbrakk>
      \<Longrightarrow>(sa@[z1]) setinterleaves ((t@[z1],(u@[z1])),insert tick (ev ` A))"    
      proof- 
        have a: "(rev sa) setinterleaves ((rev t,rev u),insert tick (ev ` A))"  
          using local.A doubleReverse by blast
        have b: "(z1#rev sa)  setinterleaves  ((z1#rev t,z1# rev u),insert tick (ev ` A))"  
          using TrA a newAA by auto
        show ?thesis  
          using b doubleReverse by fastforce
      qed
      then show ?thesis  
        using A1 B TrA local.A by blast  
    next
      case False
      then show ?thesis 
        by blast
    qed
    from A B A1 obtain Z1 Z2 where A2: "(Z1=Y1\<inter>{z.(t@[z], {})\<notin>F P})\<and>(Z2=Y1-{z.(t@[z], {})\<notin>F P})" 
      by blast
    from A2 have BA: "Y1=Z1\<union>Z2" 
      by blast
    from A2 have BAA: "\<forall>z\<in>Z1. (t@[z], {})\<notin>F P" 
      by blast
    from A2 have BAAA: "\<forall>z\<in>Z2. (u@[z], {})\<notin>F Q"  
      using AA2 by blast
    from A2 BA BAA have A3: "(t, Z1)\<in> F P"   
      by (meson F_T NF_NT is_processT5_S7 local.A)  
    from A A1 have A43: "\<forall>y\<in>Y2. (t@[y], {})\<notin> F P\<and>(u@[y], {})\<notin> F Q" 
    proof(cases "\<exists>y\<in>Y2. ((t@[y], {})\<in> F P)\<or>((u@[y], {})\<in> F Q)")
      case True
      from True obtain y1 where innAA: "y1\<in>Y2\<and>(((t@[y1], {})\<in> F P)\<or>((u@[y1], {})\<in> F Q))" by blast
      from innAA have innAAA: "y1\<notin> insert tick (ev ` A)"  
        using newAAA by auto
      from innAA have innAA1: "\<lbrakk>sa setinterleaves ((t,u),insert tick (ev ` A)); 
      y1 \<notin> insert tick (ev ` A)\<rbrakk>\<Longrightarrow>((t@[y1], {})\<in> F P\<longrightarrow>(sa@[y1]) setinterleaves 
      ((t@[y1],u),insert tick (ev ` A)))\<and>((u@[y1], {})\<in> F Q\<longrightarrow>(sa@[y1]) setinterleaves 
      ((t,u@[y1]),insert tick (ev ` A)))" 
        by (simp add: addNonSync)        
      with A B innAA1 innAA show ?thesis  
        by (metis A1 DiffD1 innAAA is_processT4_empty)
    next
      case False
      then show ?thesis by blast
    qed
    from A1  A2 obtain Xbb where B1: "Xbb=(Xa\<union>Z1\<union>Y2)" 
      by blast
    from A B1 A3 A43  have A5: "(t, Xbb)\<in> F P"   
      by (meson BAA is_processT5_S1)
    from A1 A2 obtain Ybb where B2: "Ybb=(Ya\<union>Z2\<union>Y2)" 
      by blast
    from A B have A52: "(u, Ybb)\<in> F Q"  
      by (metis A43 B2 BAAA is_processT5_S1)   
    from A1 A2 have A61: "(Xbb \<union> Ybb)\<inter>insert tick (ev ` A)=((Xa\<union>Ya\<union>Y1\<union>Y2) \<inter> insert tick (ev ` A))"  
      using B1 B2 by blast
    from A1 have A62: "(Y1) \<inter> insert tick (ev ` A)=Y1"  
      using inf.orderE by auto
    from A1 have A63: "(Y2) \<inter> insert tick (ev ` A)={}"  
      by (simp add: AA1 Int_commute) 
    from A61 A62 A63 have A64:"((Xa\<union>Ya\<union>Y1\<union>Y2)\<inter>insert tick(ev `A))=((Xa\<union>Ya)\<inter>insert tick(ev `A)\<union>Y1)" 
      by (simp add: Int_Un_distrib2)
    from AA1 BA B1 B2 have A65: "(Xbb\<inter>Ybb)\<subseteq>((Xa\<inter>Ya)\<union>Y) " 
      by auto  
    from AA1 BA B1 B2 have A66:"(Xbb\<inter>Ybb)\<supseteq>((Xa\<inter>Ya)\<union>Y2)" 
      by auto    
    from A1 A2  have A66: "((Xa \<union> Ya) \<inter> insert tick (ev ` A) \<union> Xa \<inter> Ya \<union> Y) = ((Xbb \<union> Ybb) \<inter> 
    insert tick (ev ` A) \<union> Xbb \<inter> Ybb)"
    proof -
      have f1: "(Xa \<union> Ya) \<inter> insert tick (ev ` A) \<union> Xa \<inter> Ya \<union> Y = Y \<union> Xa \<inter> Ya \<union> ((Xa \<union> Ya) \<inter> 
      insert tick (ev ` A) \<union> Xbb \<inter> Ybb)"using A65 by auto
      have "Xa \<inter> Ya \<union> Y2 \<union> Xbb \<inter> Ybb = Xbb \<inter> Ybb"
        by (meson A66 le_iff_sup)
      then have "(Xa \<union> Ya) \<inter> insert tick (ev ` A) \<union> Xa \<inter> Ya \<union> Y = Xbb \<inter> Ybb \<union> ((Xa \<union> Ya) \<inter> 
      insert tick (ev ` A) \<union> Y1)" using f1 A1 by auto
      then show ?thesis
        using A61 A64 by force
    qed
    with A5 A52 A66 show ?thesis  
      using local.A by blast  
  qed
qed

lemma pt3: "ta \<in> T P \<Longrightarrow>u \<in> T Q \<Longrightarrow> (s @ t) setinterleaves ((ta, u), insert tick (ev ` A))\<Longrightarrow>
        \<exists>t u X. (t, X) \<in> F P \<and>(\<exists>Y. (u, Y) \<in> F Q \<and>s setinterleaves ((t, u), insert tick (ev ` A)) \<and>
                 tick \<notin> X \<and> tick \<notin> Y \<and> (X \<union> Y) \<inter> ev ` A = {} \<and> X \<inter> Y = {})"  
proof-
  assume a1: "ta \<in> T P"
  assume a2: "u \<in> T Q"
  assume a3: "(s @ t) setinterleaves ((ta, u), insert tick (ev ` A))"
  have aa: "ta \<in> T P \<Longrightarrow>u \<in> T Q \<Longrightarrow> (s @ t) setinterleaves ((ta, u), insert tick (ev ` A))\<Longrightarrow>
                \<exists>t u. t \<in> T P \<and>(u \<in> T Q \<and>s setinterleaves ((t, u), insert tick (ev ` A)))" 
    using is_processT3_ST_pref synPrefix by blast
  thus "\<exists>t u X. (t, X) \<in> F P \<and>(\<exists>Y. (u, Y) \<in> F Q \<and>s setinterleaves ((t, u), insert tick (ev ` A)) \<and>
                 tick \<notin> X \<and> tick \<notin> Y \<and> (X \<union> Y) \<inter> ev ` A = {} \<and> X \<inter> Y = {})"  
    using NF_NT a1 a2 a3 by blast
qed
  

lemma sync_maintains_is_process:
 "is_process ({(s,R).\<exists> t u X Y. (t,X) \<in> F P \<and> (u,Y) \<in> F Q \<and> 
                                     (s setinterleaves ((t,u),(ev`A) \<union> {tick})) \<and> 
                                     R = (X \<union> Y) \<inter> ((ev`A) \<union> {tick}) \<union> X \<inter> Y} \<union> 
                   {(s,R).\<exists> t u r v. front_tickFree v \<and> (tickFree r \<or> v=[]) \<and> 
                                     s = r@v \<and> 
                                     (r setinterleaves ((t,u),(ev`A) \<union> {tick})) \<and>      
          (t \<in> D P \<and> u \<in> T Q \<or> t \<in> D Q \<and> u \<in> T P)},

                   {s.    \<exists> t u r v. front_tickFree v \<and> (tickFree r \<or> v=[]) \<and> 
                                     s = r@v \<and> 
                                     (r setinterleaves ((t,u),(ev`A) \<union> {tick})) \<and> 
                                     (t \<in> D P \<and> u \<in> T Q \<or> t \<in> D Q \<and> u \<in> T P)})"
                    (is "is_process(?f, ?d)") 
proof(simp only: fst_conv snd_conv F_def is_process_def FAILURES_def DIVERGENCES_def,
      fold FAILURES_def DIVERGENCES_def,fold F_def,intro conjI) 
  show "([], {}) \<in> ?f" 
    apply auto 
    by (metis Int_commute Int_empty_right Sync.si_empty1 Un_empty empty_iff insert_iff is_processT1) 
next 
  show " \<forall>s X. (s, X) \<in> ?f \<longrightarrow> front_tickFree s" 
    apply (auto simp:is_processT2 append_T_imp_tickFree front_tickFree_append D_imp_front_tickFree) 
      using ftf_syn is_processT2 apply blast
     using D_imp_front_tickFree ftf_syn is_processT2_TR apply blast
    using D_imp_front_tickFree ftf_syn is_processT2_TR by blast  
next
  show "\<forall>s t. (s @ t, {}) \<in> ?f \<longrightarrow> (s, {}) \<in> ?f" 
    apply auto   
        apply(drule F_T) 
        apply(drule F_T) 
  proof(goal_cases)
    case (1 s t ta u X Y)
    then show ?case 
      using pt3 by fastforce
next
  case (2 s t ta u r v)
  have aa: "front_tickFree v \<Longrightarrow>s@t = r @ v \<Longrightarrow> r setinterleaves ((ta, u), insert tick (ev ` A)) \<Longrightarrow>
  \<forall>t u r. r setinterleaves ((t,u),insert tick(ev `A))\<longrightarrow>(\<forall>v. s=r@v\<longrightarrow>front_tickFree v\<longrightarrow>\<not>tickFree r 
  \<and> v\<noteq>[]\<or>(t \<in> D P\<longrightarrow>u \<notin> T Q) \<and> (t \<in> D Q \<longrightarrow> u \<notin> T P)) \<Longrightarrow>tickFree r \<Longrightarrow>ta \<in> D P \<Longrightarrow>u \<in> T Q \<Longrightarrow>s<r" 
    apply(simp add: append_eq_append_conv2) 
    by (metis append_Nil2 front_tickFree_Nil front_tickFree_dw_closed le_list_def less_list_def)
  from 2(1,2,3,4,5,6,7) Sync.sym aa have a1: "s<r" by blast
  have aaa: "r setinterleaves ((ta, u), insert tick (ev ` A)) \<Longrightarrow>tickFree r \<Longrightarrow>ta \<in> D P \<Longrightarrow>
  u \<in> T Q \<Longrightarrow>s<r\<Longrightarrow>\<exists>t u X. (t, X) \<in> F P \<and>(\<exists>Y. (u, Y) \<in> F Q \<and>s setinterleaves 
  ((t, u), insert tick (ev ` A)) \<and>tick \<notin> X \<and> tick \<notin> Y \<and> (X \<union> Y) \<inter> ev ` A = {} \<and> X \<inter> Y = {})"
    apply(drule D_T) 
    apply(simp add: le_list_def less_list_def)  
    using Sync.sym pt3 by blast
  have aab: "\<exists>t u X. (t, X) \<in> F P \<and>(\<exists>Y. (u, Y) \<in> F Q \<and> s setinterleaves 
  ((t, u), insert tick (ev ` A)) \<and> tick \<notin> X \<and> tick \<notin> Y \<and> (X \<union> Y) \<inter> ev ` A = {} \<and> X \<inter> Y = {})" 
    using 2(1,2,3,4,5,6,7) aa aaa Sync.sym by auto
  then show ?case by auto  
next
  case (3 s t ta u r v)
  have aa: "front_tickFree v \<Longrightarrow>s @ t = r @ v \<Longrightarrow> r setinterleaves ((ta, u), insert tick (ev ` A)) 
  \<Longrightarrow>\<forall>t u r. r setinterleaves ((t, u), insert tick (ev ` A)) \<longrightarrow>(\<forall>v. s = r @ v \<longrightarrow>front_tickFree v 
  \<longrightarrow>\<not> tickFree r \<and> v \<noteq> [] \<or> (t \<in> D P \<longrightarrow> u \<notin> T Q) \<and> (t \<in> D Q \<longrightarrow> u \<notin> T P)) \<Longrightarrow>tickFree r \<Longrightarrow>
  ta \<in> D Q \<Longrightarrow>u \<in> T P \<Longrightarrow>s<r"  
    apply(simp add: append_eq_append_conv2) 
    by (metis append_Nil2 front_tickFree_Nil front_tickFree_dw_closed le_list_def less_list_def)
  
  have aaa: "r setinterleaves ((ta, u), insert tick (ev ` A)) \<Longrightarrow>tickFree r \<Longrightarrow>ta \<in> D Q \<Longrightarrow>u \<in> T P 
  \<Longrightarrow>s<r\<Longrightarrow>\<exists>t u X. (t, X) \<in> F P \<and>(\<exists>Y. (u, Y) \<in> F Q \<and>s setinterleaves ((t, u), insert tick (ev ` A)) 
  \<and>tick \<notin> X \<and> tick \<notin> Y \<and> (X \<union> Y) \<inter> ev ` A = {} \<and> X \<inter> Y = {})" 
    apply(drule D_T) 
    apply(simp add: le_list_def less_list_def)  
    using Sync.sym pt3 by blast
  from 3(1,2,3,4,5,6,7) Sync.sym aa have a1: "s<r"  
    by blast
  have aab: "\<exists>t u X. (t, X) \<in> F P \<and> (\<exists>Y. (u, Y) \<in> F Q \<and> s setinterleaves 
  ((t, u), insert tick (ev ` A)) \<and> tick \<notin> X \<and> tick \<notin> Y \<and> (X \<union> Y) \<inter> ev ` A = {} \<and> X \<inter> Y = {})" 
    using 3(1,2,3,4,5,6,7) aa aaa Sync.sym by auto 
  then show ?case 
    by auto 
next
  case (4 s t ta u)
  from 4(3) have a1: "ta \<in> T P"  
    by (simp add: D_T)
  then show ?case  
    using "4"(1) "4"(4) pt3 by blast  
next
  case (5 s t ta u)
  from 5(3) have a1: "ta \<in> T Q"  
    by (simp add: D_T)
  then show ?case  
    using "5"(1) "5"(4) Sync.sym pt3 by blast
qed      
next 
  show "\<forall>s X Y. (s, Y) \<in> ?f \<and> X \<subseteq> Y \<longrightarrow> (s, X) \<in> ?f"   
    apply auto 
  proof(goal_cases)
    case (1 s X t u Xa Ya)
    have aa: "X \<subseteq> ((Xa \<union> Ya) \<inter> insert tick (ev ` A) \<union> Xa \<inter> Ya )\<Longrightarrow>\<exists>x1 y1. x1\<subseteq>Xa \<and> y1\<subseteq>Ya \<and> 
    X=((x1 \<union> y1) \<inter> insert tick (ev ` A) \<union> x1 \<inter> y1)" 
      apply(simp add: Set.subset_iff_psubset_eq) 
      apply(erule disjE) 
       defer 
       apply blast 
    proof-
      assume A: "X \<subset> (Xa \<union> Ya) \<inter> insert tick (ev ` A) \<union> Xa \<inter> Ya" 
      from A obtain X1 where B: "X1=((Xa \<union> Ya) \<inter> insert tick (ev ` A) \<union> Xa \<inter> Ya)-X" 
        by blast
      from A obtain x where C: "x=Xa-X1" 
        by blast
      from A obtain y where D: "y=Ya-X1" 
        by blast
      from A B C D have E: "X = (x \<union> y) \<inter> insert tick (ev ` A) \<union> x \<inter> y" 
        by blast
      thus " \<exists>x1. (x1 \<subset> Xa \<or> x1 = Xa) \<and> (\<exists>y1. (y1 \<subset> Ya \<or> y1 = Ya) \<and> X = (x1 \<union> y1) \<inter> 
      insert tick (ev ` A) \<union> x1 \<inter> y1)"
        using A B C D E by (metis Un_Diff_Int inf.strict_order_iff inf_sup_absorb) 
    qed 
    then show ?case using 1(1,2,3,4,5)  
      by (meson process_charn)
  qed
 
next  
  let ?f1 = "{(s,R).\<exists> t u X Y. (t,X) \<in> F P \<and> (u,Y) \<in> F Q \<and> (s setinterleaves 
  ((t,u),(ev`A) \<union> {tick}))\<and> R = (X \<union> Y) \<inter> ((ev`A) \<union> {tick}) \<union> X \<inter> Y}" 
  have is_processT5_SYNC3: "\<And>sa X Y.(sa, X) \<in>?f1 \<Longrightarrow>(\<forall>c. c\<in>Y\<longrightarrow>(sa@[c],{})\<notin>?f)\<Longrightarrow>(sa, X\<union>Y) \<in> ?f1" 
    apply(clarsimp) 
    apply(rule is_processT5_SYNC2[simplified]) 
     apply(auto simp:is_processT5) apply blast  
    by (metis Sync.sym Un_empty_right inf_sup_absorb inf_sup_aci(5) insert_absorb insert_not_empty)  
  show "\<forall>s X Y. (s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f) \<longrightarrow> (s, X \<union> Y) \<in> ?f"
    apply(intro allI impI, elim conjE UnE)
     apply(rule rev_subsetD)
      apply(rule is_processT5_SYNC3)
    by(auto)  
next
  show "\<forall>s X. (s @ [tick], {}) \<in> ?f \<longrightarrow> (s, X - {tick}) \<in> ?f" 
    apply auto 
        apply(drule F_T) 
        apply(drule F_T)  
        using syncWithTick_imp_NTF1 apply fastforce 
       apply(metis append_assoc append_same_eq front_tickFree_dw_closed nonTickFree_n_frontTickFree 
       non_tickFree_tick tickFree_append) 
      apply(metis butlast_append butlast_snoc front_tickFree_charn non_tickFree_tick tickFree_append 
      tickFree_implies_front_tickFree) 
     apply (metis NT_ND append_Nil2 front_tickFree_Nil is_processT3_ST is_processT9_S_swap 
     syncWithTick_imp_NTF) 
    by (metis NT_ND append_Nil2 front_tickFree_Nil is_processT3_ST is_processT9_S_swap 
    syncWithTick_imp_NTF)
    
next
  show "\<forall>s t. s \<in> ?d \<and> tickFree s \<and> front_tickFree t \<longrightarrow> s @ t \<in> ?d" 
    apply auto
       using front_tickFree_append apply blast 
      using front_tickFree_append apply blast 
     apply blast
    by blast
next  
  show "\<forall>s X. s \<in> ?d \<longrightarrow>  (s, X) \<in> ?f"
    by blast
next  
  show "\<forall>s. s @ [tick] \<in> ?d \<longrightarrow> s \<in> ?d"  
    apply auto
       apply (metis butlast_append butlast_snoc front_tickFree_charn non_tickFree_tick 
       tickFree_append tickFree_implies_front_tickFree)
      apply (metis butlast_append butlast_snoc front_tickFree_charn non_tickFree_tick 
      tickFree_append tickFree_implies_front_tickFree) 
     apply (metis D_T append.right_neutral front_tickFree_Nil is_processT3_ST is_processT9 
     syncWithTick_imp_NTF) 
    by (metis D_T append.right_neutral front_tickFree_Nil is_processT3_ST is_processT9 
    syncWithTick_imp_NTF) 
qed

lemmas  Rep_Abs_Sync[simp] = Abs_process_inverse[simplified, OF sync_maintains_is_process]

subsection\<open>Projections\<close>

lemma
  F_sync    : "F(P \<lbrakk> A \<rbrakk> Q) = 
                   {(s,R).\<exists> t u X Y. (t,X) \<in> F P \<and> 
                                       (u,Y) \<in> F Q \<and> 
                                       s setinterleaves ((t,u),(ev`A) \<union> {tick}) \<and> 
                                       R = (X \<union> Y) \<inter> ((ev`A) \<union> {tick}) \<union> X \<inter> Y} \<union> 
                   {(s,R).\<exists> t u r v. front_tickFree v \<and> 
                                       (tickFree r \<or> v=[]) \<and> 
                                       s = r@v \<and> 
                                       r setinterleaves ((t,u),(ev`A)\<union>{tick}) \<and> 
                                       (t \<in> D P \<and> u \<in> T Q \<or> t \<in> D Q \<and> u \<in> T P)}"
       
       
  unfolding sync_def 
  apply(subst F_def) 
  apply(simp only: Rep_Abs_Sync) 
  by(auto simp: FAILURES_def)
   

lemma
  D_sync    : "D(P \<lbrakk> A \<rbrakk> Q) = 
                   {s.    \<exists> t u r v. front_tickFree v \<and> (tickFree r \<or> v=[]) \<and> 
                            s = r@v \<and> r setinterleaves ((t,u),(ev`A) \<union> {tick}) \<and> 
                            (t \<in> D P \<and> u \<in> T Q \<or> t \<in> D Q \<and> u \<in> T P)}"

  unfolding sync_def
  apply(subst D_def)
  apply(simp only: Rep_Abs_Sync)
  by(simp add: DIVERGENCES_def)
 

lemma
  T_sync    : "T(P \<lbrakk> A \<rbrakk> Q) = 
                   {s.    \<exists> t u. t \<in> T P \<and> u \<in> T Q \<and> 
                                 s setinterleaves ((t,u),(ev`A) \<union> {tick})}\<union>
 {s.    \<exists> t u r v. front_tickFree v \<and> (tickFree r \<or> v=[]) \<and> 
                            s = r@v \<and> r setinterleaves ((t,u),(ev`A) \<union> {tick}) \<and> 
                            (t \<in> D P \<and> u \<in> T Q \<or> t \<in> D Q \<and> u \<in> T P)}"

  unfolding sync_def
  apply(subst T_def, simp only: Rep_Abs_Sync, simp add:TRACES_def FAILURES_def)
  apply auto 
   apply (meson F_T)
  using T_F by blast
  
subsection\<open>Syntax for Interleave and Parallel Operator \<close>

abbreviation Inter_syntax  ("(_|||_)" [14,15] 14)
  where "P ||| Q == (P \<lbrakk> {} \<rbrakk> Q)"

abbreviation Par_syntax  ("(_||_)" [14,15] 14)
  where "P || Q == (P \<lbrakk> UNIV \<rbrakk> Q)"

subsection\<open> Continuity Rule \<close>

lemma mono_Sync_D1:  
"P \<sqsubseteq> Q \<Longrightarrow> D (Q \<lbrakk> A \<rbrakk> S) \<subseteq> D (P \<lbrakk> A \<rbrakk> S)"
  apply(auto simp: D_sync)
  using le_approx1 apply blast
  using le_approx_lemma_T apply blast
   apply (metis append_Nil2 le_approx1 subsetCE tickFree_Nil tickFree_implies_front_tickFree) 
  by (metis append_Nil2 le_approx_lemma_T subsetCE tickFree_Nil tickFree_implies_front_tickFree)

lemma mono_Sync_D2:
"P \<sqsubseteq> Q\<Longrightarrow>(\<forall> s. s \<notin> D (P  \<lbrakk> A \<rbrakk>  S) \<longrightarrow> Ra (P  \<lbrakk> A \<rbrakk>  S) s = Ra (Q  \<lbrakk> A \<rbrakk>  S) s)"
  apply auto 
   apply(simp add: Ra_def D_sync F_sync)
   apply (metis (no_types, lifting) F_T append_Nil2 front_tickFree_Nil le_approx2)
  apply(simp add: Ra_def D_sync F_sync)
  apply(insert le_approx_lemma_F[of P Q] le_approx_lemma_T[of P Q] le_approx1[of P Q] 
  le_approx2T[of P Q], auto) 
      apply blast
     apply blast
    apply blast
  using front_tickFree_Nil apply blast
  using front_tickFree_Nil by blast

lemma interPrefixEmpty: "s setinterleaves ((t,[]),A)\<and>t1<t\<Longrightarrow>\<exists>s1<s. s1 setinterleaves ((t1, []), A)"
  by (metis (no_types, lifting) Sync.sym emptyLeftProperty le_list_def nil_le2 
  order.strict_implies_order synPrefix1)

lemma interPrefix:"\<exists>u1 s1. s setinterleaves((t,u),A)\<and>t1<t\<longrightarrow>u1\<le>u\<and>s1<s\<and>s1 setinterleaves((t1,u1),A)"
proof (induction "length t + length u" arbitrary:s t u t1 rule:nat_less_induct)
  case 1
  then show ?case 
    apply(cases t)
     apply auto[1]
    apply(cases u)   
     apply (meson interPrefixEmpty nil_le2)   
  proof- 
    fix a list aa lista 
    assume a: " \<forall>m<length t + length u.  \<forall>x xa. m = length x + length xa \<longrightarrow> (\<forall>xb xc. \<exists>u1 s1. 
    xb setinterleaves((x, xa),A)\<and>xc < x \<longrightarrow> u1 \<le> xa \<and> s1 < xb \<and> s1 setinterleaves ((xc, u1), A))"
    and b: "t = a # list"
    and c: "u = aa # lista"
    thus "\<exists>u1 s1. s setinterleaves((t, u),A)\<and>t1<t\<longrightarrow>u1 \<le>u\<and>s1<s\<and>s1 setinterleaves ((t1, u1), A)"  
    proof-
      from b c have th0pre: "a=aa\<and>aa\<in> A\<Longrightarrow>s setinterleaves ((t, u), A) \<Longrightarrow>
      (tl s) setinterleaves ((list,lista), A)" by auto    
      from a obtain yu ys  where th0pre1: "a=aa\<and>aa\<in> A\<and>s setinterleaves ((t, u), A)\<and> t1 < a # list\<and>
      length t1>0\<Longrightarrow>yu\<le>lista\<and>ys<tl s\<and>ys setinterleaves ((tl t1, yu), A)"    
        apply (simp add: le_list_def less_list_def append_eq_Cons_conv) 
        by (metis add_less_mono b c length_Cons lessI list.sel(3) th0pre)        
      from th0pre th0pre1  b c have th0pre2: "a=aa\<and>aa\<in>A\<Longrightarrow>s setinterleaves ((a # list, u), A)\<and> 
      t1<a#list\<and>length t1>0\<Longrightarrow>(a#ys)setinterleaves((a#tl t1, a#yu), A)\<and>a#ys<s\<and>a#yu\<le>u\<and>t1=a#tl t1"   
        apply (simp add: le_list_def less_list_def  Cons_eq_append_conv)  
        by (metis append_Cons list.exhaust_sel list.inject list.sel(3))
      have th0pre3: "a=aa\<and>aa\<in>A\<Longrightarrow>s setinterleaves ((a # list, u), A)\<and>t1 < a # list\<and>length t1=0\<Longrightarrow>
      []<s\<and>[]\<le>u\<and> [] setinterleaves ((t1, []), A)"  
        apply (simp add: le_list_def less_list_def) using c by auto
      from  th0pre2 th0pre3 c  have th0 : "a=aa\<and>aa\<in>A\<Longrightarrow>s setinterleaves ((a # list, u), A)\<and> 
      t1 < a # list\<Longrightarrow>\<exists>u1\<le>u. \<exists>s1<s. s1 setinterleaves ((t1, u1), A)"  by fastforce
      from b c have th1pre: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>s setinterleaves ((a # list, u), A) \<Longrightarrow>
      (tl s) setinterleaves ((list,aa#lista), A)" by auto
      from a obtain yu1 ys1  where th1pre1: "a\<notin>A\<and>aa\<in> A\<and>s setinterleaves ((a # list, u), A)\<and> 
      t1 < a # list\<and>length t1>0\<Longrightarrow>yu1\<le>u\<and>ys1<tl s\<and>ys1 setinterleaves ((tl t1, yu1), A)"  
        apply (simp add: le_list_def less_list_def append_eq_Cons_conv)  
        by (metis add_Suc b c length_Cons lessI list.sel(3) th1pre)
      from th1pre1 have th1pre2: "a\<notin>A\<and>aa\<in> A \<and> ys1 setinterleaves ((tl t1, yu1), A)\<Longrightarrow>
      (a#ys1) setinterleaves ((a#tl t1, yu1), A)" apply simp  
        by (metis (mono_tags, lifting) addNonSync doubleReverse rev.simps(2) rev_rev_ident)
      from th1pre th1pre1  b c have th1pre3: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>s setinterleaves ((a # list, u), A)\<and> 
      t1<a#list\<and>length t1>0\<Longrightarrow>(a#ys1) setinterleaves ((a#tl t1, yu1), A)\<and>a#ys1<s\<and>yu1\<le>u\<and>t1=a#tl t1"  
        apply (simp add: le_list_def less_list_def )  
        by (metis append_Cons list.exhaust_sel list.inject list.sel(3) th1pre2)
      have th1preEmpty: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>s setinterleaves ((a # list, u), A)\<and>t1 < a # list\<and>length t1=0
      \<Longrightarrow>[]<s\<and>[]\<le>u\<and> [] setinterleaves ((t1, []), A)" apply (simp add: le_list_def less_list_def) 
        using c by auto
      from c have th1: "a\<notin>A\<and>aa\<in> A\<Longrightarrow>s setinterleaves ((a # list, u), A)\<and>t1 < a # list\<Longrightarrow>
      \<exists>u1\<le>u. \<exists>s1<s. s1 setinterleaves ((t1, u1), A)"   using th1pre3 th1preEmpty by fastforce
      from b c have th2pre: "aa\<notin>A\<and>a\<in> A\<Longrightarrow>s setinterleaves ((a # list, u), A) \<Longrightarrow>
      (tl s) setinterleaves ((a#list,lista), A)" by auto
      from a  th2pre obtain yu2 ys2  where th2pre1: "aa\<notin>A\<and>a\<in> A\<and>s setinterleaves ((a # list, u), A)\<and> 
      t1 < a # list\<and>length t1>0\<Longrightarrow>yu2\<le>lista\<and>ys2<tl s\<and>ys2 setinterleaves ((t1, yu2), A)"  
        apply (simp add: le_list_def less_list_def)   
        by (metis add_Suc_right b c length_Cons lessI)    
      from th2pre1 have th2pre2: "aa\<notin>A\<and>a\<in> A \<and> ys2 setinterleaves ((t1, yu2), A)\<Longrightarrow>
      (aa#ys2) setinterleaves ((t1, aa#yu2), A)" apply simp  
        by (metis (mono_tags, lifting) addNonSync doubleReverse rev.simps(2) rev_rev_ident)
      from th2pre th2pre1  b c have th2pre3: "aa\<notin>A\<and>a\<in> A \<Longrightarrow>s setinterleaves ((a # list, u), A)\<and> 
      t1 < a # list\<and>length t1>0\<Longrightarrow>(aa#ys2) setinterleaves ((t1, aa#yu2), A)\<and>aa#ys2<s\<and>aa#yu2\<le>u"  
        apply (simp add: le_list_def less_list_def )  using th2pre2 by auto
      have th2preEmpty: "aa\<notin>A\<and>a\<in> A\<Longrightarrow>s setinterleaves ((a # list, u), A)\<and>t1 < a # list\<and>length t1=0
      \<Longrightarrow>[]<s\<and>[]\<le>u\<and> [] setinterleaves ((t1, []), A)" apply (simp add: le_list_def less_list_def) 
        using c by auto
      from th2pre3 b c have th2: "aa\<notin>A\<and>a\<in> A\<Longrightarrow>s setinterleaves ((a # list, u), A)\<and>t1 < a # list\<Longrightarrow>
      \<exists>u1\<le>u. \<exists>s1<s. s1 setinterleaves ((t1, u1), A)"  
        using th2preEmpty by blast
      from b c have th3pre: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>s setinterleaves ((a # list, u), A) \<Longrightarrow>
      (tl s) setinterleaves ((a#list,lista), A)\<and>hd s=aa\<or>(tl s) setinterleaves ((list,u), A)\<and>hd s=a" 
        by auto
      from a c b th3pre obtain yu3 ys3  where th3pre1: "(aa\<notin>A\<and>a\<notin> A\<and>s setinterleaves 
      ((a # list, u), A)\<and> t1 < a # list\<and>length t1>0\<and>(tl s) setinterleaves ((a#list,lista), A)\<longrightarrow>
      yu3\<le>lista\<and>ys3<tl s\<and>ys3 setinterleaves((t1,yu3),A))" apply(simp add:le_list_def less_list_def) 
        by (metis (no_types, lifting) add_Suc length_Cons lessI) 
      have adsmallPrefix: "t1<a # list\<and>length t1>0\<Longrightarrow>tl t1<list"  
        using less_tail by fastforce
      from a b c th3pre adsmallPrefix obtain yu30 ys30   where th3pre12: "(aa\<notin>A\<and>a\<notin> A\<Longrightarrow>
      (tl s) setinterleaves ((list,u), A)\<and>hd s=a\<and>tl t1< list\<longrightarrow>yu30\<le>u\<and>ys30<tl s\<and>
      ys30 setinterleaves ((tl t1, yu30), A))" apply (simp add: le_list_def less_list_def)  
        by (metis (no_types, lifting) add_Suc_right length_Cons lessI)  
      have th3pre1more1: "yu3\<le>lista \<Longrightarrow>aa#yu3\<le>u " using c  
        by (metis le_less less_cons)
      have th3pre1more2: "aa\<notin>A\<and>a\<notin> A\<and>s setinterleaves ((a # list, aa#lista), A) \<and>
      (tl s) setinterleaves ((a#list,lista), A)\<and>hd s=aa\<and>ys3<tl s \<Longrightarrow>aa#ys3<s " using c 
        by (metis less_cons list.exhaust_sel list.sel(2) nil_less)
      have  th3pre1more21: "aa \<notin> A \<and>a \<notin> A \<and> ys3<tl s\<and>ys3 setinterleaves ((t1, yu3), A) \<and> 
      hd s = aa \<longrightarrow>(aa # ys3) setinterleaves ((t1, aa # yu3), A)"
        by (metis (mono_tags, lifting) addNonSync doubleReverse rev.simps(2) rev_rev_ident)
      from th3pre1more1 th3pre1more2 th3pre1more21 th3pre1 have th3pre1more3: "(aa\<notin>A\<and>a\<notin> A\<and>
      s setinterleaves ((a # list, u), A)\<and> t1 < a # list\<and>length t1>0\<and>(tl s) setinterleaves 
      ((a#list,lista), A)\<and>hd s=aa\<longrightarrow>aa#yu3\<le>u\<and>aa#ys3<s\<and>(aa#ys3) setinterleaves ((t1, aa#yu3), A))" 
        using c by blast     
      have th3pre1more32: "aa\<notin>A\<and>a\<notin> A\<and>s setinterleaves ((a # list, aa#lista), A) \<and>
      (tl s) setinterleaves ((list,aa#lista), A)\<and>hd s=a\<and>ys30<tl s \<Longrightarrow>a#ys30<s " using c 
        by (metis less_cons list.exhaust_sel list.sel(2) nil_less)
      have  th3pre1more213: "aa \<notin> A \<and>a \<notin> A \<and> ys30<tl s\<and>ys30 setinterleaves ((tl t1, yu30), A) \<and> 
      hd s = a \<and>t1<a#list\<longrightarrow>(a # ys30) setinterleaves ((a#tl t1, yu30), A)"  
        by (metis (mono_tags, lifting) addNonSync doubleReverse rev.simps(2) rev_rev_ident)
      from  th3pre1more32 th3pre12 th3pre1more213 have th3pre1more33: "(aa\<notin>A\<and>a\<notin> A\<and>s setinterleaves 
      ((a # list, u), A)\<and> t1 < a # list\<and>length t1>0\<and>(tl s) setinterleaves ((list,aa#lista), A)\<and>
      hd s=a\<longrightarrow>yu30\<le>u\<and>a#ys30<s\<and>(a#ys30) setinterleaves ((t1, yu30), A))" 
        by (metis adsmallPrefix c hd_append2 le_list_def length_greater_0_conv list.exhaust_sel 
        list.sel(1) order.strict_implies_order)  
      from th3pre1more3 th3pre1more33 b c th3pre  have th3NoEmpty: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>s setinterleaves 
      ((a # list, u), A)\<and>t1 < a # list\<and>length t1>0\<Longrightarrow>\<exists>u1\<le>u. \<exists>s1<s. s1 setinterleaves ((t1, u1), A)" 
        apply (simp add: le_list_def less_list_def)  
        by (metis append.simps(2))   
      have th3preEmpty: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>s setinterleaves ((a # list, u), A)\<and>t1 < a # list\<and>length t1=0
      \<Longrightarrow>[]<s\<and>[]\<le>u\<and> [] setinterleaves ((t1, []), A)"
        apply (simp add: le_list_def less_list_def) using c by auto    
      from th3NoEmpty th3preEmpty have th3: "aa\<notin>A\<and>a\<notin> A\<Longrightarrow>s setinterleaves ((a # list, u), A)\<and>t1 < 
      a # list\<Longrightarrow>\<exists>u1\<le>u. \<exists>s1<s. s1 setinterleaves ((t1, u1), A)" 
        by blast      
      show?thesis  
        using b c th0 th1 th2 th3 by auto
    qed 
  qed  
qed

lemma mono_sync2a:"r\<in>min_elems(D (P \<lbrakk>A\<rbrakk> S))\<Longrightarrow>\<exists>t u. r setinterleaves ((t, u),insert tick (ev ` A))\<and>
(t \<in> min_elems(D P) \<and> u \<in> T S \<or> t \<in> min_elems(D S) \<and> u \<in> T P\<and> u \<in> (T P-(D P-min_elems(D P))))" 
proof- 
  fix r
  assume A: "r \<in> min_elems(D (P  \<lbrakk>A\<rbrakk> S))"
  thus "\<exists>t u. r setinterleaves ((t, u), insert tick (ev ` A))\<and>(t \<in> min_elems(D P) \<and> u \<in> 
  T S \<or> t \<in> min_elems(D S) \<and> u \<in> T P\<and> u \<in> (T P-(D P-min_elems(D P))))" 
  proof(cases "\<forall>t u r1. r1\<le>r\<and> r1 setinterleaves((t, u),insert tick (ev ` A))\<longrightarrow>(t \<notin> min_elems(D P)) 
  \<and> (t \<notin> min_elems(D S))")
    case True
    from A have AA: "r\<in> D (P  \<lbrakk>A\<rbrakk> S)"  
      using elem_min_elems by blast
    from AA obtain t1 u1 where A1: "\<exists>r1\<le>r. r1 setinterleaves ((t1, u1), insert tick (ev ` A))\<and>
    (t1\<in>D P\<or>t1\<in>D S)" apply(simp add: D_sync) 
      using le_list_def by blast
    from True A1 have A2: "(t1 \<notin> min_elems(D P)) \<and> (t1 \<notin> min_elems(D S))"  
      by blast
    from A1 A2 min_elems5 obtain tm1 tm2 where tmA: "(t1\<in>D P\<longrightarrow>(tm1\<le>t1\<and>tm1\<in> min_elems(D P)))\<and>
    (t1\<in>D S\<longrightarrow>(tm2\<le>t1\<and>tm2\<in> min_elems(D S)))"  by blast  
    from A2 tmA have AB1: "(t1\<in>D P\<longrightarrow>tm1<t1)\<and>(t1\<in>D S\<longrightarrow>tm2<t1)" 
      by (metis A1 order.not_eq_order_implies_strict)
    from A1 AB1 obtain um1 rm1 um2 rm2 where AB2: " (t1\<in>D P\<longrightarrow>um1\<le>u1 \<and> rm1 setinterleaves 
    ((tm1, um1),insert tick (ev ` A)))\<and>(t1\<in>D S\<longrightarrow>um2\<le>u1 \<and> rm2 setinterleaves 
    ((tm2, um2), insert tick (ev ` A)))" by (meson interPrefix)     
    from A1 A2 True tmA AB1 have A3: "(t1\<in>D P\<longrightarrow>rm1<r\<and>rm1\<in>D(P\<lbrakk>A\<rbrakk>S))\<and>(t1\<in>D S\<longrightarrow>rm2<r\<and>rm2\<in> D(P\<lbrakk>A\<rbrakk>S))"  
      by (meson dual_order.strict_implies_order interPrefix order_trans) 
    from A3 AA have ATrue: "r \<notin> min_elems(D (P  \<lbrakk>A\<rbrakk> S))" using min_elems_def  
      using A1 by blast   
    with A ATrue show ?thesis 
      by blast 
  next
    case False
    from A have dsync: "r\<in>D (P \<lbrakk>A\<rbrakk> S)"  
      by (simp add: local.A elem_min_elems)
    from dsync obtain r1 t2 u2 where C: "r1\<le>r\<and> r1 setinterleaves ((t2, u2), insert tick (ev ` A))\<and>
    ((t2 \<in> D P\<and>u2\<in>T S)\<or>(t2\<in>D S\<and>u2\<in> T P))" apply(simp add: D_sync)  
      using le_list_def by blast
    from C have r1D: "r1\<in>D (P \<lbrakk>A\<rbrakk> S)" apply(simp add: D_sync)  
      using front_tickFree_Nil by blast
    from A C r1D have eq: "r1=r" apply(simp add: min_elems_def) 
      using le_neq_trans by blast
    from A False have minAa: "(t2 \<in> D P\<and>u2\<in>T S)\<longrightarrow>(t2 \<in> min_elems(D P))"  
    proof(cases "t2 \<in> D P \<and>u2\<in>T S\<and> t2 \<notin> min_elems(D P)")
      case True
      from True obtain t3 where inA: "t3<t2\<and>t3\<in>min_elems(D P)" 
        by (metis le_imp_less_or_eq min_elems5)
      from inA obtain r3 u3 where inA1:"u3\<le>u2\<and>r3 setinterleaves((t3,u3),insert tick(ev ` A))\<and>r3<r"  
        using C eq interPrefix by blast 
      from inA1 have inA3: "u3\<in>T S"  
        using True is_processT3_ST_pref by blast
      from inA1 have inA2: "r3\<in>D (P \<lbrakk>A\<rbrakk> S)" apply (simp add: D_sync)  
        using elem_min_elems front_tickFree_Nil inA inA3 by blast 
      with A eq inA1 show ?thesis 
        by(simp add: min_elems_def) 
    next
      case False
      then show ?thesis 
        by blast
    qed
    from A False have minAb1: "(t2 \<in> D S\<and>u2\<in> T P)\<longrightarrow>(t2 \<in> min_elems(D S))"  
    proof(cases "t2 \<in> D S \<and>u2\<in>T P\<and> t2 \<notin> min_elems(D S)")
      case True
      from True obtain t3 r3 u3 where inA: "t3<t2\<and>t3\<in>min_elems(D S)" 
      and inA1: "u3\<le>u2\<and>r3 setinterleaves ((t3, u3), insert tick (ev ` A))\<and>r3<r"
        by (metis C eq interPrefix le_less min_elems5)
      from inA1 have inA3: "u3\<in>T P"  
        using True is_processT3_ST_pref by blast
      from inA1 have inA2: "r3\<in>D (P \<lbrakk>A\<rbrakk> S)" apply (simp add: D_sync)  
        using elem_min_elems front_tickFree_Nil inA inA3 by blast 
      with A eq inA1 show ?thesis 
        by(simp add: min_elems_def)
    next
      case False
      then show ?thesis 
        by blast
    qed
    from A False have minAb2: "(t2 \<in> D S\<and>u2\<in> T P)\<longrightarrow>(u2 \<in> (T P-(D P-min_elems(D P))))" 
    proof(cases "t2 \<in> D S \<and>u2\<in>T P\<and> u2 \<in>(D P-min_elems(D P))")
      case True
      from True have inAAA: "u2\<in>D P\<and>u2\<notin>min_elems(D P)" 
        by blast
      from inAAA obtain u3  where inA: "u3<u2\<and>u3\<in>min_elems(D P)"  
        by (metis le_neq_trans min_elems5) 
      from inA obtain t3 r3 where inA1: "t3\<le>t2\<and>r3 setinterleaves((t3,u3),insert tick(ev ` A))\<and>r3<r"  
        using C Sync.sym eq interPrefix by blast
      from inA1 have inA3: "u3\<in>D P\<and>t3\<in>T S"  
        using D_T True elem_min_elems inA is_processT3_ST_pref by blast 
      from inA1 have inA2: "r3\<in>D (P \<lbrakk>A\<rbrakk> S)" apply (simp add: D_sync)  
        using Sync.sym front_tickFree_Nil inA3 by blast  
      with A inA1 inA2 show ?thesis 
        by(simp add: min_elems_def)
    next
      case False
      then show ?thesis 
        by blast
    qed
    with A C show ?thesis   
      using eq minAa minAb1 by blast  
  qed
qed
 
lemma mono_Sync_D3: 
  assumes ordered: "P \<sqsubseteq> Q" 
  shows "min_elems (D (P  \<lbrakk>A\<rbrakk> S)) \<subseteq> T (Q  \<lbrakk>A\<rbrakk> S)" 
proof- 
  have mono_sync2b:"P \<sqsubseteq> Q \<Longrightarrow>\<forall>r. r \<in> min_elems(D (P  \<lbrakk>A\<rbrakk> S))\<longrightarrow>r\<in> T (Q  \<lbrakk>A\<rbrakk> S)" 
    apply(frule impI)
    apply(auto simp: mono_sync2a) 
  proof - 
    fix r
    assume A: "P \<sqsubseteq> Q"
    and B: "r \<in> min_elems (D (P \<lbrakk>A\<rbrakk> S))" 
    from B obtain t u where E: "r setinterleaves ((t, u), insert tick (ev ` A))\<and>(t \<in> min_elems(D P) 
    \<and> u \<in> T S \<or> t \<in> min_elems(D S) \<and> u \<in> (T P-(D P-min_elems(D P))))" using mono_sync2a
      by blast
    from E have F:"(t\<in>T Q\<and>u\<in>T S) \<or> (t\<in> T S\<and>u\<in>T Q)"  
      using le_approx2T le_approx3 ordered by blast     
    thus "r \<in> T (Q \<lbrakk>A\<rbrakk> S)"  
      by (metis (no_types, lifting) E Sync.sym T_sync UnCI Un_commute insert_is_Un mem_Collect_eq) 
  qed 
  show ?thesis 
    apply(insert ordered) 
    apply(frule mono_sync2b) 
    by blast
qed
  
lemma mono_D_syn: "D (S \<lbrakk> A \<rbrakk> Q) = D (Q \<lbrakk> A \<rbrakk> S)"
  by(auto simp: D_sync)

lemma mono_T_syn: "T (S \<lbrakk> A \<rbrakk> Q) = T (Q \<lbrakk> A \<rbrakk> S)"
  apply(auto simp: T_sync)  
  using Sync.sym by fastforce+
   

lemma mono_F_syn: "F (S \<lbrakk> A \<rbrakk> Q)  = F (Q \<lbrakk> A \<rbrakk> S) "
  apply auto  
   apply (simp add: F_sync)
  using Sync.sym apply blast
  apply (simp add: F_sync)
  using Sync.sym by blast

lemma mono_Ra_syn: "Ra (S \<lbrakk> A \<rbrakk> Q) s = Ra (Q \<lbrakk> A \<rbrakk> S) s"
  apply auto
   apply (auto simp: Ra_def)
  by (auto simp: mono_F_syn)

lemma mono_Sync[simp]     : "P \<sqsubseteq> Q \<Longrightarrow> (P \<lbrakk> A \<rbrakk> S) \<sqsubseteq> (Q \<lbrakk> A \<rbrakk> S)"
  by(auto simp: le_approx_def mono_Sync_D1 mono_Sync_D2 mono_Sync_D3)

lemma mono_Sync_sym [simp]    : "P \<sqsubseteq> Q \<Longrightarrow> (S \<lbrakk> A \<rbrakk> P) \<sqsubseteq> (S \<lbrakk> A \<rbrakk> Q)"
  by (metis Process_eq_spec mono_D_syn mono_F_syn mono_Sync)

lemma chain_Sync1: "chain Y \<Longrightarrow> chain (\<lambda>i. Y i  \<lbrakk> A \<rbrakk> S)"
  by(simp add: chain_def) 

lemma chain_Sync2: "chain Y \<Longrightarrow> chain (\<lambda>i. S  \<lbrakk> A \<rbrakk> Y i)"
  by(simp add: chain_def)

lemma empty_setinterleaving : "[] setinterleaves ((t, u), A) \<Longrightarrow> t = []"  
  by (cases t, cases u, auto, cases u, simp_all split:if_splits) 

lemma inters_fin_fund: "finite{(t, u). s setinterleaves ((t, u), A)}"
proof (induction "length s" arbitrary:s rule:nat_less_induct)
  case 1
  have A:"{(t, u). s setinterleaves((t, u), A)} \<subseteq> {([],[])} \<union> {(t, u). s setinterleaves ((t, u), A) 
  \<and> (\<exists> a list. t = a#list  \<and> a \<notin> A) \<and> u = []} \<union> {(t, u). s setinterleaves ((t, u), A) \<and> 
  (\<exists> a list. u = a#list \<and> a \<notin> A) \<and> t = []} \<union> {(t, u). s setinterleaves ((t, u), A) \<and> 
  (\<exists> a list aa lista. u = a#list \<and> t = aa#lista)}" (is "?A \<subseteq> {([],[])} \<union> ?B \<union> ?C \<union> ?D") 
    apply (rule subsetI, safe)
          apply(simp_all add: neq_Nil_conv)   
         apply (metis Sync.si_empty2 Sync.sym empty_iff list.exhaust_sel)
        using list.exhaust_sel apply blast
       apply (metis Sync.sym emptyLeftNonSync list.exhaust_sel list.set_intros(1))    
      using list.exhaust_sel apply blast
     apply (metis emptyLeftNonSync list.exhaust_sel list.set_intros(1))
    by (metis Sync.si_empty2 Sync.sym empty_iff list.exhaust_sel)
  have a1:"?B \<subseteq> { ((hd s#list), [])| list. (tl s) setinterleaves ((list, []), A) \<and> (hd s) \<notin> A}" 
  (is "?B  \<subseteq> ?B1") by auto
  define f where a2:"f = (\<lambda>a (t, (u::'a event list)). ((a::'a event)#t, ([]::'a event list)))"
  have a3:"?B1 \<subseteq> {(hd s # list, []) |list. tl s setinterleaves ((list, []), A)} " (is "?B1  \<subseteq> ?B2") 
    by blast
  from a1 a3 have a13:"?B \<subseteq> ?B2" 
    by simp
  have AA: "finite ?B" 
  proof (cases s)
    case Nil
    then show ?thesis 
      using not_finite_existsD by fastforce
  next
    case (Cons a list)
    hence aa:"finite{(t,u).(tl s) setinterleaves((t, u), A)}"using 1[THEN spec, of "length (tl s)"] 
      by (simp)
    have "{(hd s#list, [])|list. tl s setinterleaves((list,[]),A)}\<subseteq>(\<lambda>(t, u).f(hd s)(t, u)) `{(t, u). 
    tl s setinterleaves ((t, u), A)}" using a2 by auto
    hence "finite ?B2" using finite_imageI [of "{(t, u). (tl s) setinterleaves ((t, u), A)}" 
    "\<lambda>(t, u). f (hd s) (t, u)", OF aa] using rev_finite_subset by auto 
    then show ?thesis using a13 
      by (meson rev_finite_subset)
  qed
  have a1:"?C \<subseteq> { ([],(hd s#list))| list. (tl s) setinterleaves (([],list), A) \<and> (hd s) \<notin> A}" 
  (is "?C  \<subseteq> ?C1") by auto
  define f where a2:"f = (\<lambda>a ((t::'a event list), u). (([]::'a event list), (a::'a event)#u))"
  have a3:"?C1 \<subseteq> {([],hd s # list) |list. tl s setinterleaves (([],list), A)} " (is "?C1  \<subseteq> ?C2") 
    by blast
  from a1 a3 have a13:"?C \<subseteq> ?C2" 
    by simp
  have AAA:"finite ?C"
  proof (cases s)
    case Nil
    then show ?thesis 
      using not_finite_existsD by fastforce
  next
    case (Cons a list)
    hence aa:"finite {(t,u).(tl s)setinterleaves((t, u), A)}"using 1[THEN spec, of "length (tl s)"] 
      by (simp)
    have "{([], hd s # list) |list. tl s setinterleaves (([], list), A)} \<subseteq> (\<lambda>(t, u). 
    f (hd s) (t, u)) ` {(t, u). tl s setinterleaves ((t, u), A)}" using a2 by auto
    hence "finite ?C2" using finite_imageI [of "{(t, u). (tl s) setinterleaves ((t, u), A)}" 
    "\<lambda>(t, u). f (hd s) (t, u)", OF aa] using rev_finite_subset by auto 
    then show ?thesis using a13 
      by (meson rev_finite_subset)
  qed
  have dd0:"?D \<subseteq> {(a#l, aa#la)|a aa l la. s setinterleaves ((a#l, aa#la), A)}" (is "?D \<subseteq> ?D1")
    apply (rule subsetI, auto, simp split:if_splits) 
    by (blast, blast, metis, blast)
  have AAAA:"finite ?D" 
  proof (cases s)
    case Nil
    hence "?D \<subseteq> {([],[])}" 
      using empty_setinterleaving by auto
    then show ?thesis 
      using infinite_super by auto
  next
    case (Cons a list)
    hence dd1:"?D1 \<subseteq> {(a#l, u)| l u. list setinterleaves ((l, u), A)} 
                \<union> {(t, a#la)| t la. list setinterleaves ((t, la), A)} 
                \<union> {(a#l, a#la)|l la. list setinterleaves ((l, la), A)}"(is "?D1 \<subseteq> ?D2 \<union> ?D3 \<union> ?D4") 
      by (rule_tac subsetI, auto split:if_splits)
    with Cons have aa:"finite {(t,u). list setinterleaves ((t, u), A)}" 
      using 1[THEN spec, of "length list"] by (simp)
    define f where a2:"f = (\<lambda> (t, (u::'a event list)). ((a::'a event)# t, u))" 
    with Cons have "?D2 \<subseteq> (f ` {(t, u). list setinterleaves ((t, u), A)})" 
      using a2 by auto
    hence dd2:"finite ?D2"
      using finite_imageI [of "{(t, u). list setinterleaves ((t, u), A)}" f, OF aa]
      by (meson rev_finite_subset)
    define f where a2:"f = (\<lambda> ((t::'a event list),u). (t,(a::'a event)#u))" 
    with Cons have "?D3 \<subseteq> (f ` {(t, u). list setinterleaves ((t, u), A)})" 
      using a2 by auto
    hence dd3:"finite ?D3"       
      using finite_imageI [of "{(t, u). list setinterleaves ((t, u), A)}" f, OF aa]
      by (meson rev_finite_subset) 
    define f where a2:"f = (\<lambda> (t,u). ((a::'a event)#t,(a::'a event)#u))" 
    with Cons have "?D4 \<subseteq> (f ` {(t, u). list setinterleaves ((t, u), A)})" 
      using a2 by auto
    hence dd4:"finite ?D4"
      using finite_imageI [of "{(t, u). list setinterleaves ((t, u), A)}" f, OF aa]
      by (meson rev_finite_subset)       
    with dd0 dd1 dd2 dd3 dd4 show ?thesis 
      by (simp add: finite_subset) 
  qed    
  from A AA AAA AAAA show ?case 
    by (simp add: finite_subset)    
qed

lemma inters_fin: "finite{(t, u, r). r setinterleaves ((t, u), insert tick (ev ` A))\<and> 
(\<exists>v. x = r @ v \<and> front_tickFree v \<and> (tickFree r \<or> v = []))}" (is "finite ?A")
proof -
  have a:"?A\<subseteq>(\<Union>r \<in> {r. r \<le> x}. {a. \<exists>t u. a=(t,u,r)\<and>r setinterleaves((t,u),insert tick(ev ` A))})" 
  (is "?A \<subseteq> (\<Union>r \<in> {r. r \<le> x}. ?P r)")
    using le_list_def by fastforce
  have b:"\<forall>(r::'a event list). finite (?P r)"
  proof(rule allI)
    fix r::"'a event list"
    define f where "f= (\<lambda>((t::'a event list), (u::'a event list)). (t,u,r))"
    hence "?P r \<subseteq> (f ` {(t, u). r setinterleaves ((t, u), insert tick (ev ` A) )})" 
      by auto
    then show "finite (?P r)" 
      using inters_fin_fund[of r "insert tick (ev ` A)"] finite_imageI[of "{(t, u). r setinterleaves 
      ((t, u), insert tick (ev ` A))}" f]  by (meson rev_finite_subset)   
  qed
  have "{t. \<exists>t2. x = t @ t2} = {r. \<exists>ra. r @ ra = x}" 
    by blast
  hence "finite {r. r \<le> x}" using prefixes_fin[of x, simplified Let_def, THEN conjunct1] 
    by (auto simp add:le_list_def) 
  with a b show ?thesis 
    by (meson finite_UN_I infinite_super)
qed  

 
lemma limproc_Sync_D: "chain Y\<Longrightarrow>D(lim_proc(range Y)\<lbrakk> A \<rbrakk> S)=D(lim_proc(range(\<lambda>i. Y i \<lbrakk> A \<rbrakk> S)))" 
  apply(auto simp:Process_eq_spec  F_sync D_sync T_sync F_LUB D_LUB T_LUB chain_Sync1) 
      apply blast 
     apply blast 
    using front_tickFree_Nil apply blast
    using front_tickFree_Nil apply blast 
  proof - 
    fix x
    assume A: "chain Y"
    and B: " \<forall>xa. \<exists>t u r v. front_tickFree v \<and> (tickFree r \<or> v = []) \<and> x = r @ v \<and> r setinterleaves 
    ((t, u), insert tick (ev ` A)) \<and> (t \<in> D (Y xa) \<and> u \<in> T S \<or> t \<in> D S \<and> u \<in> T (Y xa))"
    thus "\<exists>t u r v. front_tickFree v \<and> (tickFree r \<or> v = []) \<and> x = r @ v \<and> r setinterleaves 
    ((t, u), insert tick (ev ` A)) \<and> ((\<forall>x. t \<in> D (Y x)) \<and> u \<in> T S \<or> t \<in> D S \<and> (\<forall>x. u \<in> T (Y x)))" 
    proof(cases "\<forall>t u r. r setinterleaves ((t, u), insert tick (ev ` A)) \<longrightarrow>
            (r\<le>x \<longrightarrow> ((\<exists>x. t \<notin> D (Y x)) \<or> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> (\<exists>x. u \<notin> T (Y x))))") 
      case True 
      from A obtain tryunion where Ctryy: "tryunion={(t, u, r). r setinterleaves 
      ((t, u), insert tick (ev ` A))\<and>(\<exists>v.(x = r @ v \<and> front_tickFree v \<and> (tickFree r \<or> v = [])))}" 
        by simp
      from Ctryy inters_fin have tolfin: "finite tryunion" 
        by auto
      obtain tryunion1 where Ctryy1: "tryunion1={n. \<exists>(t,u, r)\<in>tryunion.(t \<in> D (Y n) \<and> u\<in>T S \<or> t \<in> 
      D S \<and> u \<in> T (Y n))}" by simp
      from B Ctryy1 Ctryy have Ctryy3: "\<forall>n. n\<in>tryunion1"  
        by blast  
      from Ctryy3 have Ctryy2: "infinite tryunion1"   
        using finite_nat_set_iff_bounded by auto  
      from Ctryy2 Ctryy1 tolfin obtain  r2 t2 u2 where Ee: "(t2,u2, r2)\<in>tryunion \<and>  
      infinite {n. (t2 \<in> D (Y n) \<and> u2 \<in> T S \<or> t2 \<in> D S \<and> u2 \<in> T (Y n))}"  
        by auto
      from True Ee  Ctryy obtain x1 x2 where Ee1: "((t2 \<notin> D (Y x1)) \<or> u2 \<notin> T S) \<and> (t2 \<in> D S \<longrightarrow> 
      (u2 \<notin> T (Y x2)))" 
        apply (simp add: le_list_def) by blast       
      from Ee Ee1 Ctryy obtain x3 where Ee2: "(x1\<le>x3) \<and> (x2\<le>x3) \<and> (t2 \<in> D (Y x3) \<and> u2 \<in> T S \<or> 
      t2 \<in> D S \<and> u2 \<in> T (Y x3))"  
        apply(simp add: infinite_nat_iff_unbounded_le)  
      proof - 
        assume a1: "r2 setinterleaves ((t2, u2), insert tick (ev ` A)) \<and> (\<exists>v. x = r2 @ v \<and> 
        front_tickFree v \<and> (tickFree r2 \<or> v = [])) \<and> ((\<forall>m. \<exists>n\<ge>m. t2 \<in> D (Y n) \<and> u2 \<in> T S) \<or> 
        (\<forall>m. \<exists>n\<ge>m. t2 \<in> D S \<and> u2 \<in> T (Y n)))"
        assume a2: "\<And>x3. x1 \<le> x3 \<and> x2 \<le> x3\<and>(t2 \<in> D (Y x3) \<and> u2 \<in> T S \<or> t2 \<in> D S \<and> u2 \<in> T (Y x3)) 
        \<Longrightarrow> thesis"
        obtain nn :: "nat \<Rightarrow> nat" where f3: "\<forall>x0. (\<exists>v1\<ge>x0. t2 \<in> D S \<and> u2 \<in> T (Y v1)) = 
        (x0 \<le> nn x0 \<and> t2 \<in> D S \<and> u2 \<in> T (Y (nn x0)))" by moura
        obtain nna :: "nat \<Rightarrow> nat" where "\<forall>x0. (\<exists>v1\<ge>x0. t2 \<in> D (Y v1) \<and> u2 \<in> T S) = 
        (x0 \<le> nna x0 \<and> t2 \<in> D (Y (nna x0)) \<and> u2 \<in> T S)" by moura
        then have f4: "(\<forall>n. n \<le> nna n \<and> t2 \<in> D (Y (nna n)) \<and> u2 \<in> T S) \<or> (\<forall>n. n \<le> nn n \<and> t2 \<in> D S 
        \<and> u2 \<in> T (Y (nn n)))" using f3 a1 by presburger
        have "(\<exists>n. \<not> n \<le> nn n \<or> t2 \<notin> D S \<or> u2 \<notin> T (Y (nn n))) \<or> (\<exists>n\<ge>x1. x2 \<le> n \<and> (t2 \<in> D (Y n) \<and> 
        u2 \<in> T S \<or> t2 \<in> D S \<and> u2 \<in> T (Y n)))" by (metis le_cases order.trans) 
        moreover 
        { assume "\<exists>n. \<not> n \<le> nn n \<or> t2 \<notin> D S \<or> u2 \<notin> T (Y (nn n))"
          then have "\<forall>n. n \<le> nna n \<and> t2 \<in> D (Y (nna n)) \<and> u2 \<in> T S" 
            using f4 by blast
          then have "\<exists>n\<ge>x1. x2 \<le> n \<and> (t2 \<in> D (Y n) \<and> u2 \<in> T S \<or> t2 \<in> D S \<and> u2 \<in> T (Y n))"
            by (metis (no_types) le_cases order.trans) 
        } 
        ultimately show ?thesis 
          using a2 by blast 
      qed 
      from A have Abb1: "\<forall>n1 n2. n1\<le>n2 \<longrightarrow> Y n1 \<sqsubseteq> Y n2" 
        by (simp add: po_class.chain_mono)
      from A Abb1 have Abb2: "\<forall>n1 n2. n1>n2\<and>t \<notin> D (Y n2)\<longrightarrow>t \<notin> D (Y n1)" 
        using le_approx1 less_imp_le_nat by blast
      from A Abb1 have Abb3: "\<forall>n1 n2. n1>n2\<and>t \<notin> T (Y n2)\<longrightarrow>t \<notin> T (Y n1)"  
        by (meson NT_ND le_approx2T less_imp_le_nat)
      from Abb2 Ee2 have Ab1: "t2 \<notin> D (Y x1)\<longrightarrow>t2 \<notin> D (Y x3)"  
        by (meson Abb1 le_approx1 less_imp_le_nat subsetCE)
      from Abb3 have Ab2: "u2 \<notin> T (Y x2)\<longrightarrow>u2 \<notin> T (Y x3)"  
        by (meson Abb1 Ee2 NT_ND le_approx2T less_imp_le_nat)
      from True Ee Ee1  Ee2 Ab1 Ab2 show ?thesis  
        by blast 
    next 
      case False 
      from A B False obtain t u r where Bb1: "r setinterleaves ((t, u), insert tick (ev ` A)) \<and> 
      r \<le> x \<and> ((\<forall>x. t \<in> D (Y x)) \<and> u \<in> T S \<or> t \<in> D S \<and> (\<forall>x. u \<in> T (Y x)))"   
        by auto
      from B have Bb21: "front_tickFree x"  
        by (metis D_imp_front_tickFree append_Nil2 front_tickFree_append ftf_syn is_processT2_TR)
      from B Bb1 have Bb2: "\<exists>v. front_tickFree v \<and> (tickFree r \<or> v = [])\<and> x = r @ v"  
        by (metis Bb21 front_tickFree_Nil front_tickFree_mono le_list_def)  
      then show ?thesis  
        using Bb1 by blast  
    qed  
  qed  
   

lemma limproc_Sync_F_annex1: " chain Y\<Longrightarrow>\<forall>n. (a, b) \<in> F (Y n \<lbrakk>A\<rbrakk> S) \<Longrightarrow> \<exists>x. a \<notin> D (Y x \<lbrakk>A\<rbrakk> S) \<Longrightarrow>
\<exists>t u X. (\<forall>x. (t, X) \<in> F (Y x)) \<and> (\<exists>Y. (u, Y) \<in> F S \<and> a setinterleaves((t, u),insert tick (ev ` A))
\<and> b = (X \<union> Y) \<inter> insert tick (ev ` A) \<union> X \<inter> Y)"
proof - 
  fix a b
  assume A: "chain Y"
  assume B: "\<forall>n. (a, b) \<in> F (Y n \<lbrakk>A\<rbrakk> S)"
  assume C: "\<exists>x. a \<notin> D (Y x \<lbrakk>A\<rbrakk> S)"
  thus "\<exists>t u X. (\<forall>x. (t, X) \<in> F (Y x)) \<and>
        (\<exists>Y. (u, Y) \<in> F S \<and> a setinterleaves ((t, u), insert tick (ev ` A)) \<and> b = (X \<union> Y) \<inter> 
        insert tick (ev ` A) \<union> X \<inter> Y)" 
  proof- 
    from B C obtain x1 where D: "a \<notin> D (Y x1 \<lbrakk>A\<rbrakk> S)" 
      by blast
    from B D obtain t1 u1 X1 Y1 where E: "a setinterleaves ((t1, u1), insert tick (ev ` A))\<and>
    (t1, X1)\<in>F (Y x1)\<and>(u1, Y1)\<in>F S\<and>b = (X1 \<union> Y1) \<inter> insert tick (ev ` A) \<union> X1 \<inter> Y1" 
      apply(auto simp: D_sync F_sync) 
      by fastforce
    from B D E have F: "t1 \<notin> D (Y x1) \<and> t1\<in>T(Y x1)" apply(auto simp: D_sync)  
      using F_T front_tickFree_Nil apply blast  
      by (simp add: F_T)
    from F have ee: "\<forall>i. (t1, X1) \<in> F (Y i)\<and>(u1, Y1)\<in> F S\<and> a setinterleaves 
    ((t1, u1), insert tick (ev ` A))\<and> b = (X1 \<union> Y1) \<inter> insert tick (ev ` A) \<union> X1 \<inter> Y1"  
      using E chain_lemma is_processT8_S le_approx2 local.A by metis
    with A B C D E F ee  show?thesis 
      by blast 
  qed
qed

lemma limproc_Sync_F_annex2: "chain Y\<Longrightarrow>\<forall>t u r. r setinterleaves ((t, u), insert tick (ev ` A)) \<longrightarrow>
(\<forall>v. a = r @ v \<longrightarrow> front_tickFree v \<longrightarrow>\<not> tickFree r \<and> v \<noteq> [] \<or> ((\<exists>x. t \<notin> D (Y x)) \<or> u \<notin> T S) \<and> 
(t \<in> D S \<longrightarrow> (\<exists>x. u \<notin> T (Y x))))\<Longrightarrow>\<exists>x. a \<notin> D(Y x \<lbrakk> A \<rbrakk> S)" 
  apply(auto simp: D_sync) 
proof-
  fix a
  assume A: "\<forall>t u r. r setinterleaves ((t, u), insert tick (ev ` A)) \<longrightarrow> (\<forall>v. a = r @ v \<longrightarrow>
  front_tickFree v \<longrightarrow> \<not> tickFree r \<and> v \<noteq> [] \<or> ((\<exists>x. t \<notin> D (Y x)) \<or> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> 
  (\<exists>x. u \<notin> T (Y x))))"
  assume B: "chain Y"
  thus "\<exists>x. \<forall>t u r. r setinterleaves ((t, u), insert tick (ev ` A)) \<longrightarrow>(\<forall>v. a = r @ v \<longrightarrow> 
  front_tickFree v\<longrightarrow>\<not> tickFree r\<and>v\<noteq>[] \<or> (t \<in> D (Y x) \<longrightarrow> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> u \<notin> T (Y x)))" 
  proof- 
    from B have D: "((\<exists>x. t \<notin> D (Y x)) \<or> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> (\<exists>x. u \<notin> T (Y x)))\<Longrightarrow> 
    (\<exists>x. ((t \<in> D (Y x) \<longrightarrow> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> u \<notin> T (Y x))))" 
      by (meson D_T chain_lemma le_approx1 le_approx2T subsetCE)
    from A obtain tryunion where Ctryy: "tryunion={(t, u, r). r setinterleaves 
    ((t, u), insert tick (ev ` A))\<and>(\<exists>v. a = r @ v \<and> front_tickFree v \<and> (tickFree r \<or> v = []))}" 
      by simp
    from Ctryy have tolfin: "finite tryunion" 
      using inters_fin by auto 
    from B have Abb1: "\<forall>n1 n2. n1\<le>n2 \<longrightarrow> Y n1 \<sqsubseteq> Y n2"  
      by (simp add: po_class.chain_mono)
   from A Abb1 have Abb2: "\<forall>n1 n2 t. n1>n2\<and>t \<notin> D (Y n2)\<longrightarrow>t \<notin> D (Y n1)" 
      using le_approx1 less_imp_le_nat by blast
   from A Abb1 have Abb3: "\<forall>n1 n2 t. n1>n2\<and>t \<notin> T (Y n2)\<longrightarrow>t \<notin> T (Y n1)"  
      by (meson NT_ND le_approx2T less_imp_le_nat)
    from Abb2 Abb3 have oneIndexPre: "\<forall>t u. ((\<exists>x. t \<notin> D (Y x)) \<or> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> 
    (\<exists>x. u \<notin> T (Y x)))\<longrightarrow>(\<exists>x. (t \<notin> D (Y x) \<or> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> u \<notin> T (Y x)))"
      by (meson B D_T ND_F_dir2' chain_lemma le_approx1 subsetCE)  
    from A B oneIndexPre Abb2 Abb3  have oneIndex: "\<forall>t u r. r setinterleaves 
    ((t, u), insert tick (ev ` A)) \<longrightarrow> (\<forall>v. a = r @ v \<longrightarrow>front_tickFree v \<longrightarrow> \<not> tickFree r\<and>v\<noteq>[] \<or>
    ( \<exists>x.( (( t \<notin> D (Y x)) \<or> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> (u \<notin> T (Y x))))))" by blast
    define proUnion1 where finiUnion: "proUnion1={n. \<exists>(t,u, r)\<in>tryunion.(((t \<in> D (Y n) \<longrightarrow> u \<notin> T S) 
    \<and>(t \<in> D S \<longrightarrow> u\<notin>T (Y n)))\<and> (\<forall>m. ( (t \<in> D (Y m)\<longrightarrow>u \<notin> T S)\<and>(t \<in> D S\<longrightarrow>u \<notin> T (Y m)))\<longrightarrow>n\<le>m))}"
    from B have finiSet1: "\<And>r t u. (t,u, r) \<in> tryunion \<Longrightarrow> finite {n1.(((t \<in> D (Y n1)\<longrightarrow>u \<notin> T S)\<and> 
    (t\<in>D S\<longrightarrow>u\<notin>T(Y n1)))\<and>(\<forall>m1. ((t \<in> D (Y m1)\<longrightarrow>u \<notin> T S)\<and>(t \<in> D S \<longrightarrow> u \<notin> T (Y m1)))\<longrightarrow>n1\<le>m1))}"  
     by (metis (no_types, lifting) infinite_nat_iff_unbounded mem_Collect_eq not_less)
   from B tolfin finiUnion oneIndex finiSet1  have finiSet: "finite proUnion1"  
     by auto   
   from finiSet obtain proMax where ann: "proMax=Max(proUnion1)"  
     by blast   
   from ann Abb2 have ann1: "\<forall>num\<in>proUnion1. \<forall>t. t \<notin> D (Y num)\<longrightarrow>t \<notin> D (Y proMax)"  
     by (meson Abb1 Max_ge finiSet le_approx1 subsetCE)    
   from ann Abb3 have ann2: "\<forall>num\<in>proUnion1.  \<forall>t. t \<notin> T (Y num)\<longrightarrow>t \<notin> T (Y proMax)"  
     by (meson Abb1 D_T Max_ge finiSet le_approx2T)
   from finiUnion have ann3: "\<forall>num\<in>proUnion1. \<exists>r t u. r setinterleaves((t, u),insert tick (ev ` A)) 
   \<longrightarrow> (\<forall>v. a = r @ v \<longrightarrow>front_tickFree v \<longrightarrow> \<not> tickFree r \<and> v \<noteq> [] \<or>(( ((t\<notin>D(Y num))\<or>u \<notin> T S) \<and> 
   (t \<in> D S \<longrightarrow> (u \<notin> T (Y num))))))" by auto
   obtain proUnion2 where ann0: " proUnion2 ={(t, u, r).\<exists>n. (t, u, r)\<in>tryunion\<and>
   ((t \<in> D (Y n)\<longrightarrow>u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> u \<notin> T (Y n)))}" by auto 
   from ann0 Ctryy finiUnion have ann1: "\<And>t u r.  (t, u, r)\<in> proUnion2\<Longrightarrow>\<exists>num. num\<in>proUnion1\<and>
   ((t \<in> D (Y num) \<longrightarrow> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> u \<notin> T (Y num)))"    
   proof- 
     fix t u r
     assume a:  "(t, u, r)\<in> proUnion2"
     define P where PP:"P = (\<lambda>num. ((t \<in> D (Y num) \<longrightarrow> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> u \<notin> T (Y num))))"
     thus "\<exists>num. num\<in>proUnion1\<and> P num" 
     proof- 
       from finiUnion obtain minIndexRB where ann1preB: "minIndexRB={n. (P n)}" 
         by auto
       from B ann1preB obtain minmin where ab: "(minmin::nat) = Inf (minIndexRB)" 
         by auto
       from ann0 ann1preB PP have ann1preNoEmpty1: "minIndexRB \<noteq> {}" 
         using a by blast
       from ab ann1preNoEmpty1 have ann1pre0:"minmin \<in> minIndexRB" 
         using Inf_nat_def wellorder_Least_lemma(1) by force        
       have "minmin\<in> {n. \<exists>t u r. (t,u,r)\<in>tryunion \<and> ((t \<in> D (Y n) \<longrightarrow> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> 
       u \<notin> T (Y n))) \<and> (\<forall>m. (t \<in> D (Y m) \<longrightarrow> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> u \<notin> T (Y m)) \<longrightarrow> n \<le> m)}"  
         apply(rule CollectI,rule_tac x=t in exI,rule_tac x=u in exI,rule_tac x=r in exI,intro conjI)
            using a ann0 apply blast          
           using PP ann1pre0 ann1preB apply blast
           using PP ann1pre0 ann1preB apply blast 
          by (simp add: Inf_nat_def PP ab ann1preB wellorder_Least_lemma(2)) 
       then show ?thesis  
         using ann1pre0 ann1preB finiUnion by blast 
     qed 
   qed 
   from ann1 have ann12: "\<forall>t u r.\<exists>num.(t, u, r)\<in> proUnion2\<longrightarrow> num\<in>proUnion1\<and>
   ((t \<in> D (Y num) \<longrightarrow> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> u \<notin> T (Y num)))" by auto
   from ann0 Ctryy have ann2: "\<forall>t u r. (t, u, r) \<in> proUnion2\<longrightarrow>(r setinterleaves 
   ((t, u), insert tick (ev ` A)) \<and>(\<exists>v. a = r @ v \<and> front_tickFree v \<and> (tickFree r \<or> v = [])) \<and> 
   (\<exists>nu1. (t \<in> D (Y nu1) \<longrightarrow> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> u \<notin> T (Y nu1))))" by simp 
   have ann15: " \<forall>t u r. (r setinterleaves ((t, u), insert tick (ev ` A)) \<and> (\<exists>v. a = r @ v \<and> 
   front_tickFree v \<and> (tickFree r \<or> v = [])) \<and> (\<exists>nu1. (t \<in> D (Y nu1) \<longrightarrow> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> 
   u \<notin> T (Y nu1))))\<longrightarrow>(t, u, r) \<in> proUnion2"  
     using Ctryy ann0 by blast   
   from  ann12 ann15 have ann01: "\<forall>t u r. ((r setinterleaves ((t, u), insert tick (ev ` A)) \<and>
   (\<exists>v. a = r @ v \<and> front_tickFree v \<and> (tickFree r \<or> v = [])) \<and> (\<exists>nu1. (t \<in> D (Y nu1)\<longrightarrow>u \<notin> T S)\<and> 
   (t \<in> D S \<longrightarrow> u \<notin> T (Y nu1))))\<longrightarrow>(\<exists>num\<in>proUnion1. ((t \<in> D (Y num) \<longrightarrow> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> 
   u \<notin> T (Y num)))))"    by blast  
   from ann01  have annhelp: " \<forall>t u r. r setinterleaves ((t, u), insert tick (ev ` A)) \<longrightarrow>
   (\<forall>v. a = r @ v \<longrightarrow> front_tickFree v \<longrightarrow>(tickFree r \<or> v = [])\<longrightarrow>( \<exists>num\<in>proUnion1.((t \<in> D (Y num) 
   \<longrightarrow> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> u \<notin> T (Y num)))))"
     by (metis oneIndex)     
   from Abb1 Abb2 have annHelp2: "\<forall>nn t u. (nn\<in>proUnion1\<and>((t \<in> D (Y nn)\<longrightarrow>u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> 
   u \<notin> T (Y nn)))) \<longrightarrow>((t \<in> D (Y proMax) \<longrightarrow> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> u \<notin> T (Y proMax)))" 
     by (metis Abb3 Max_ge ann finiSet le_neq_trans) 
   from  annHelp2 annhelp have annHelp1: " \<forall>t u r. r setinterleaves ((t, u), insert tick (ev ` A)) 
   \<longrightarrow>(\<forall>v. a = r @ v \<longrightarrow> front_tickFree v\<longrightarrow>(tickFree r \<or> v = [])\<longrightarrow>(t \<in> D (Y proMax)\<longrightarrow>u \<notin> T S) \<and> 
   (t \<in> D S \<longrightarrow> u \<notin> T (Y proMax)))" by blast       
   with A B  show ?thesis  
     by blast 
 qed 
qed

lemma limproc_Sync_F: "chain Y\<Longrightarrow>F(lim_proc (range Y)\<lbrakk> A \<rbrakk>S)=F(lim_proc (range (\<lambda>i. Y i \<lbrakk> A \<rbrakk> S)))" 
  apply(auto simp add: Process_eq_spec D_sync F_sync F_LUB D_LUB T_LUB chain_Sync1) 
       apply blast 
      apply blast 
     apply blast 
    using front_tickFree_Nil apply blast
   using front_tickFree_Nil apply blast     
  proof- 
    fix a b
    assume A1: " \<forall>x. (\<exists>t u X. (t, X) \<in> F (Y x) \<and> (\<exists>Y. (u, Y) \<in> F S \<and> a setinterleaves 
    ((t, u), insert tick (ev ` A)) \<and> b = (X \<union> Y) \<inter> insert tick (ev ` A) \<union> X \<inter> Y))\<or>
    (\<exists>t u r v. front_tickFree v \<and> (tickFree r \<or> v = []) \<and> a = r @ v \<and> r setinterleaves 
    ((t, u), insert tick (ev ` A)) \<and> (t \<in> D (Y x) \<and> u \<in> T S \<or> t \<in> D S \<and> u \<in> T (Y x)))"
    and B: " \<forall>t u r. r setinterleaves ((t, u), insert tick (ev ` A)) \<longrightarrow> (\<forall>v. a = r @ v \<longrightarrow> 
    front_tickFree v \<longrightarrow>\<not> tickFree r \<and> v \<noteq> [] \<or> ((\<exists>x. t \<notin> D (Y x)) \<or> u \<notin> T S) \<and> (t \<in> D S \<longrightarrow> 
    (\<exists>x. u \<notin> T (Y x))))"
    and C: "chain Y"
    thus  "\<exists>t u X. (\<forall>x. (t, X) \<in> F (Y x)) \<and>(\<exists>Y. (u, Y) \<in> F S \<and> a setinterleaves 
    ((t, u), insert tick (ev ` A)) \<and> b = (X \<union> Y) \<inter> insert tick (ev ` A) \<union> X \<inter> Y)" 
    proof (cases "\<exists>m. a \<notin> D (Y m \<lbrakk> A \<rbrakk> S)") 
      case True 
      then obtain m where "a \<notin> D(Y m \<lbrakk> A \<rbrakk> S)" 
        by blast
      with A1 have D: "\<forall>n. (a, b)\<in> F (Y n \<lbrakk> A \<rbrakk> S)"
        by (auto simp: F_sync)
      with A1 B C  show ?thesis 
        apply(erule_tac x=m in allE)    
        apply(frule limproc_Sync_F_annex2) 
         apply simp 
        by(simp add: limproc_Sync_F_annex1) 
    next 
      case False
      with False have E: "\<forall>n.  a \<in> D (Y n \<lbrakk> A \<rbrakk> S)" 
        by blast
      with C E B show ?thesis 
        apply auto 
        apply(drule limproc_Sync_F_annex2) 
         apply blast 
        by fast 
    qed 
  qed
  
lemma cont_left_sync : "chain Y \<Longrightarrow> ((\<Squnion> i. Y i) \<lbrakk> A \<rbrakk> S) = (\<Squnion> i. (Y i \<lbrakk> A \<rbrakk> S))"
  by(simp add: Process_eq_spec chain_Sync1 limproc_Sync_D limproc_Sync_F limproc_is_thelub) 
  
lemma cont_right_sync : "chain Y \<Longrightarrow> (S \<lbrakk> A \<rbrakk> (\<Squnion> i. Y i)) = (\<Squnion> i. (S \<lbrakk> A \<rbrakk> Y i))"
  by (metis (no_types, lifting) Process_eq_spec cont_left_sync lub_eq mono_D_syn mono_F_syn)

lemma Sync_cont[simp]: 
assumes f:"cont f" 
and     g:"cont g"
shows     "cont (\<lambda>x. (f x) \<lbrakk>A\<rbrakk> (g x))" 
proof - 
  have A : "\<And>x. cont g \<Longrightarrow> cont (\<lambda>y. y \<lbrakk>A\<rbrakk> (g x))" 
    apply (rule contI2, rule monofunI) 
     apply(auto) 
    by (simp add: cont_left_sync)
  have B : "\<And>y. cont g \<Longrightarrow> cont (\<lambda>x. y \<lbrakk>A\<rbrakk> g x)" 
    apply(rule_tac c="(\<lambda> x. y  \<lbrakk>A\<rbrakk> x)" in cont_compose) 
     apply(rule contI2, rule monofunI) 
      apply (simp) 
     apply (simp add: cont_right_sync) 
    by simp 
  show ?thesis using f g  
    apply(rule_tac  f="(\<lambda>x. (\<lambda> f. f  \<lbrakk>A\<rbrakk> g x))" in cont_apply) 
    by(auto intro:contI2 simp:A B)
qed 



end
