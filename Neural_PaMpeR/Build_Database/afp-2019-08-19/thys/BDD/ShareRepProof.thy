(*  Title:       BDD

    Author:      Veronika Ortner and Norbert Schirmer, 2004
    Maintainer:  Norbert Schirmer,  norbert.schirmer at web de
    License:     LGPL
*)

(*  
ShareRepProof.thy

Copyright (C) 2004-2008 Veronika Ortner and Norbert Schirmer 
Some rights reserved, TU Muenchen

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

section \<open>Proof of Procedure ShareRep\<close>
theory ShareRepProof imports ProcedureSpecs Simpl.HeapList begin

lemma (in ShareRep_impl) ShareRep_modifies:
  shows "\<forall>\<sigma>. \<Gamma>\<turnstile>{\<sigma>}  PROC ShareRep (\<acute>nodeslist, \<acute>p) 
             {t. t may_only_modify_globals \<sigma> in [rep]}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done


lemma hd_filter_cons: 
"\<And> i. \<lbrakk> P (xs ! i) p; i < length xs; \<forall> no \<in> set (take i xs). \<not> P no p; \<forall> a b.  P a b = P b a\<rbrakk>
  \<Longrightarrow> xs ! i = hd (filter (P p) xs)"
apply (induct xs)
apply simp
apply (case_tac "P a p")
apply simp
apply (case_tac i)
apply simp
apply simp
apply (case_tac i)
apply simp
apply auto
done

lemma (in ShareRep_impl) ShareRep_spec_total:
shows 
  "\<forall>\<sigma> ns. \<Gamma>,\<Theta>\<turnstile>\<^sub>t 
  \<lbrace>\<sigma>. List \<acute>nodeslist \<acute>next ns \<and>
     (\<forall>no \<in> set ns. no \<noteq> Null  \<and> 
       ((no\<rightarrow>\<acute>low = Null) = (no\<rightarrow>\<acute>high = Null)) \<and>
       (isLeaf_pt \<acute>p \<acute>low \<acute>high \<longrightarrow> isLeaf_pt no \<acute>low \<acute>high) \<and>
       no\<rightarrow>\<acute>var = \<acute>p\<rightarrow>\<acute>var) \<and> 
       \<acute>p \<in> set ns\<rbrace> 
  PROC ShareRep (\<acute>nodeslist, \<acute>p)
  \<lbrace> (\<^bsup>\<sigma>\<^esup>p \<rightarrow> \<acute>rep = hd (filter (\<lambda> sn. repNodes_eq sn \<^bsup>\<sigma>\<^esup>p \<^bsup>\<sigma>\<^esup>low \<^bsup>\<sigma>\<^esup>high \<^bsup>\<sigma>\<^esup>rep) ns)) \<and>
    (\<forall>pt.  pt \<noteq> \<^bsup>\<sigma>\<^esup>p \<longrightarrow> pt\<rightarrow>\<^bsup>\<sigma>\<^esup>rep = pt\<rightarrow>\<acute>rep) \<and> 
    (\<^bsup>\<sigma>\<^esup>p\<rightarrow>\<acute>rep\<rightarrow>\<^bsup>\<sigma>\<^esup>var = \<^bsup>\<sigma>\<^esup>p \<rightarrow> \<^bsup>\<sigma>\<^esup>var)\<rbrace>"
apply (hoare_rule HoareTotal.ProcNoRec1)
apply (hoare_rule anno=  
  "IF (isLeaf_pt \<acute>p \<acute>low \<acute>high) 
   THEN \<acute>p \<rightarrow> \<acute>rep :== \<acute>nodeslist
   ELSE
     WHILE (\<acute>nodeslist \<noteq> Null)  
     INV \<lbrace>\<exists>prx sfx. List \<acute>nodeslist \<acute>next sfx \<and> ns=prx@sfx \<and> 
           \<not> isLeaf_pt \<acute>p \<acute>low \<acute>high \<and>
           (\<forall>no \<in> set ns. no \<noteq> Null \<and> 
             ((no\<rightarrow>\<^bsup>\<sigma>\<^esup>low = Null) = (no\<rightarrow>\<^bsup>\<sigma>\<^esup>high = Null)) \<and>
             (isLeaf_pt \<^bsup>\<sigma>\<^esup>p \<^bsup>\<sigma>\<^esup>low \<^bsup>\<sigma>\<^esup>high \<longrightarrow> isLeaf_pt no \<^bsup>\<sigma>\<^esup>low \<^bsup>\<sigma>\<^esup>high) \<and>
             no\<rightarrow>\<^bsup>\<sigma>\<^esup>var = \<^bsup>\<sigma>\<^esup>p\<rightarrow>\<^bsup>\<sigma>\<^esup>var) \<and> 
        \<^bsup>\<sigma>\<^esup>p \<in> set ns \<and> 
        ((\<exists>pt \<in> set prx.  repNodes_eq pt \<^bsup>\<sigma>\<^esup>p \<^bsup>\<sigma>\<^esup>low \<^bsup>\<sigma>\<^esup>high \<^bsup>\<sigma>\<^esup>rep) 
         \<longrightarrow> \<acute>rep  \<^bsup>\<sigma>\<^esup>p =  hd (filter (\<lambda> sn. repNodes_eq sn \<^bsup>\<sigma>\<^esup>p \<^bsup>\<sigma>\<^esup>low \<^bsup>\<sigma>\<^esup>high \<^bsup>\<sigma>\<^esup>rep) prx) \<and>
             (\<forall>pt. pt \<noteq> \<^bsup>\<sigma>\<^esup>p \<longrightarrow> pt\<rightarrow>\<^bsup>\<sigma>\<^esup>rep = pt\<rightarrow>\<acute>rep)) \<and>
        ((\<forall>pt \<in> set prx.  \<not> repNodes_eq pt \<^bsup>\<sigma>\<^esup>p \<^bsup>\<sigma>\<^esup>low \<^bsup>\<sigma>\<^esup>high \<^bsup>\<sigma>\<^esup>rep) \<longrightarrow>  \<^bsup>\<sigma>\<^esup>rep = \<acute>rep) \<and>
        (\<acute>nodeslist \<noteq> Null \<longrightarrow> 
           (\<forall>pt \<in> set prx. \<not> repNodes_eq pt \<^bsup>\<sigma>\<^esup>p \<^bsup>\<sigma>\<^esup>low \<^bsup>\<sigma>\<^esup>high \<^bsup>\<sigma>\<^esup>rep)) \<and>  
        (\<acute>p = \<^bsup>\<sigma>\<^esup>p \<and> \<acute>high = \<^bsup>\<sigma>\<^esup>high \<and> \<acute>low = \<^bsup>\<sigma>\<^esup>low)\<rbrace>
     VAR MEASURE (length (list \<acute>nodeslist \<acute>next))  
     DO
       IF (repNodes_eq \<acute>nodeslist \<acute>p \<acute>low \<acute>high \<acute>rep)
       THEN \<acute>p\<rightarrow>\<acute>rep :== \<acute>nodeslist;; \<acute>nodeslist :== Null
       ELSE \<acute>nodeslist :== \<acute>nodeslist\<rightarrow>\<acute>next
       FI
     OD
  FI" in HoareTotal.annotateI)
apply vcg
using  [[simp_depth_limit = 2]]
apply   (rule conjI)
apply    clarify
apply    (simp (no_asm_use))
prefer 2
apply    clarify
apply    (rule_tac x="[]" in exI)
apply    (rule_tac x=ns in exI)
apply    (simp (no_asm_use))
prefer 2
apply   clarify
apply   (rule conjI)
apply    clarify
apply    (rule conjI)
apply     (clarsimp simp add: List_list) (* solving termination contraint *)
apply    (simp (no_asm_use))
apply    (rule conjI)
apply    assumption
prefer 2
apply    clarify
apply    (simp (no_asm_use))
apply    (rule conjI)
apply    (clarsimp simp add: List_list) (* solving termination constraint *)
apply    (simp only: List_not_Null simp_thms triv_forall_equality)
apply    clarify
apply    (simp only: triv_forall_equality)
apply    (rename_tac sfx)
apply    (rule_tac x="prx@[nodeslist]" in exI)
apply    (rule_tac x="sfx" in exI)
apply    (rule conjI)
apply     assumption
apply    (rule conjI)
apply     simp
prefer 4
apply   (elim exE conjE)
apply   (simp (no_asm_use))
apply   hypsubst
using  [[simp_depth_limit = 100]]
proof -
  (* IF-THEN to postcondition *)
  fix ns var low high rep "next" p nodeslist
  assume ns: "List nodeslist next ns"
  assume no_prop:  "\<forall>no\<in>set ns.
           no \<noteq> Null \<and>
           (low no = Null) = (high no = Null) \<and>
           (isLeaf_pt p low high \<longrightarrow> isLeaf_pt no low high) \<and> var no = var p"
  assume p_in_ns: "p \<in> set ns" 
  assume p_Leaf: "isLeaf_pt p low high"
  show "nodeslist = hd [sn\<leftarrow>ns . repNodes_eq sn p low high rep] \<and>
        var nodeslist = var p"
  proof -
    from p_in_ns no_prop have p_not_Null: "p\<noteq>Null"
      using [[simp_depth_limit=2]]
      by auto
    from p_in_ns have "ns \<noteq> []"
      by (cases ns) auto
    with ns obtain ns' where ns': "ns = nodeslist#ns'" 
      by (cases "nodeslist=Null") auto
    with no_prop p_Leaf obtain 
      "isLeaf_pt nodeslist low high" and
      var_eq: "var nodeslist = var p" and
      "nodeslist\<noteq>Null"
      using [[simp_depth_limit=2]]
      by auto
    with p_not_Null p_Leaf have "repNodes_eq nodeslist p low high rep"
      by (simp add: repNodes_eq_def isLeaf_pt_def null_comp_def)
    with ns' var_eq
    show ?thesis
      by simp
  qed
next
  (* From invariant to postcondition *)
  fix var::"ref\<Rightarrow>nat" and low high rep repa p prx sfx "next"
  assume sfx: "List Null next sfx"
  assume p_in_ns: "p \<in> set (prx @ sfx)"
  assume no_props: "\<forall>no\<in>set (prx @ sfx).
           no \<noteq> Null \<and>
           (low no = Null) = (high no = Null) \<and>
           (isLeaf_pt p low high \<longrightarrow> isLeaf_pt no low high) \<and> var no = var p"
  assume match_prx: "(\<exists>pt\<in>set prx. repNodes_eq pt p low high rep) \<longrightarrow>
                       repa p = hd [sn\<leftarrow>prx . repNodes_eq sn p low high rep] \<and>
                      (\<forall>pt. pt \<noteq> p \<longrightarrow> rep pt = repa pt)"
  show "repa p = hd [sn\<leftarrow>prx @ sfx . repNodes_eq sn p low high rep] \<and>
          (\<forall>pt. pt \<noteq> p \<longrightarrow> rep pt = repa pt) \<and> var (repa p) = var p"
  proof -
    from sfx
    have sfx_Nil: "sfx=[]"
      by simp
    with p_in_ns have ex_match: "(\<exists>pt\<in>set prx. repNodes_eq pt p low high rep)"
      apply -
      apply (rule_tac x=p in bexI)
      apply  (simp add: repNodes_eq_def)
      apply simp
      done
    hence not_empty: "[sn\<leftarrow>prx . repNodes_eq sn p low high rep] \<noteq> []"
      apply -
      apply (erule bexE)
      apply (rule filter_not_empty)
      apply auto
      done
    from ex_match match_prx obtain
      found: "repa p = hd [sn\<leftarrow>prx . repNodes_eq sn p low high rep]" and
      unmodif: "\<forall>pt. pt \<noteq> p \<longrightarrow> rep pt = repa pt"
      by blast
    from hd_filter_in_list [OF not_empty] found
    have "repa p \<in> set prx"
      by simp
    with no_props
    have "var (repa p) = var p"
      using [[simp_depth_limit=2]]
      by simp
    with found unmodif sfx_Nil
    show ?thesis
      by simp
  qed
next
  (* Invariant to invariant; ELSE part *)
  fix var low high p repa "next" nodeslist prx sfx
  assume nodeslist_not_Null: "nodeslist \<noteq> Null" 
  assume p_no_Leaf: "\<not> isLeaf_pt p low high"
  assume no_props: "\<forall>no\<in>set prx \<union> set (nodeslist # sfx).
           no \<noteq> Null \<and> (low no = Null) = (high no = Null) \<and> var no = var p"
  assume p_in_ns: "p \<in> set prx \<or> p \<in> set (nodeslist # sfx)"
  assume match_prx: "(\<exists>pt\<in>set prx. repNodes_eq pt p low high repa) \<longrightarrow>
            repa p = hd [sn\<leftarrow>prx . repNodes_eq sn p low high repa]"
  assume nomatch_prx: "\<forall>pt\<in>set prx. \<not> repNodes_eq pt p low high repa"
  assume nomatch_nodeslist: "\<not> repNodes_eq nodeslist p low high repa"
  assume sfx: "List (next nodeslist) next sfx"
  show "(\<forall>no\<in>set prx \<union> set (nodeslist # sfx).
              no \<noteq> Null \<and> (low no = Null) = (high no = Null) \<and> var no = var p) \<and>
        ((\<exists>pt\<in>set (prx @ [nodeslist]). repNodes_eq pt p low high repa) \<longrightarrow>
           repa p = hd [sn\<leftarrow>prx @ [nodeslist] . repNodes_eq sn p low high repa]) \<and>
        (next nodeslist \<noteq> Null \<longrightarrow>
            (\<forall>pt\<in>set (prx @ [nodeslist]). \<not> repNodes_eq pt p low high repa))"
  proof -
    from nomatch_prx nomatch_nodeslist
    have "((\<exists>pt\<in>set (prx @ [nodeslist]). repNodes_eq pt p low high repa) \<longrightarrow>
           repa p = hd [sn\<leftarrow>prx @ [nodeslist] . repNodes_eq sn p low high repa])" 
      by auto
    moreover
    from nomatch_prx nomatch_nodeslist
    have "(next nodeslist \<noteq> Null \<longrightarrow>
            (\<forall>pt\<in>set (prx @ [nodeslist]). \<not> repNodes_eq pt p low high repa))"
      by auto
    ultimately show ?thesis
      using no_props
      by (intro conjI)
  qed
next
  (* Invariant to invariant: THEN part *)
  fix var low high p repa "next" nodeslist prx sfx
  assume nodeslist_not_Null: "nodeslist \<noteq> Null" 
  assume sfx: "List nodeslist next sfx" 
  assume p_not_Leaf: "\<not> isLeaf_pt p low high"
  assume no_props: "\<forall>no\<in>set prx \<union> set sfx.
           no \<noteq> Null \<and>
           (low no = Null) = (high no = Null) \<and>
           (isLeaf_pt p low high \<longrightarrow> isLeaf_pt no low high) \<and> var no = var p"
  assume p_in_ns: "p \<in> set prx \<or> p \<in> set sfx"
  assume match_prx: "(\<exists>pt\<in>set prx. repNodes_eq pt p low high repa) \<longrightarrow>
        repa p = hd [sn\<leftarrow>prx . repNodes_eq sn p low high repa]"
  assume nomatch_prx: "\<forall>pt\<in>set prx. \<not> repNodes_eq pt p low high repa"
  assume match: "repNodes_eq nodeslist p low high repa"
  show "(\<forall>no\<in>set prx \<union> set sfx.
              no \<noteq> Null \<and>
              (low no = Null) = (high no = Null) \<and>
              (isLeaf_pt p low high \<longrightarrow> isLeaf_pt no low high) \<and> var no = var p) \<and>
        (p \<in> set prx \<or> p \<in> set sfx) \<and>
        ((\<exists>pt\<in>set prx \<union> set sfx. repNodes_eq pt p low high repa) \<longrightarrow>
           nodeslist =
           hd ([sn\<leftarrow>prx . repNodes_eq sn p low high repa] @
               [sn\<leftarrow>sfx . repNodes_eq sn p low high repa])) \<and>
        ((\<forall>pt\<in>set prx \<union> set sfx. \<not> repNodes_eq pt p low high repa) \<longrightarrow>
           repa = repa(p := nodeslist))"
  proof -
    from nodeslist_not_Null sfx
    obtain sfx' where sfx': "sfx=nodeslist#sfx'"
      by (cases "nodeslist=Null") auto
    from nomatch_prx match sfx'
    have hd: "hd ([sn\<leftarrow>prx . repNodes_eq sn p low high repa] @
               [sn\<leftarrow>sfx . repNodes_eq sn p low high repa]) = nodeslist"
      by simp
    from match sfx'
    have triv: "((\<forall>pt\<in>set prx \<union> set sfx. \<not> repNodes_eq pt p low high repa) \<longrightarrow>
           repa = repa(p := nodeslist))" 
      by simp
    show ?thesis
      apply (rule conjI)
      apply (rule no_props)
      apply (intro conjI)
      apply   (rule p_in_ns)
      apply  (simp add: hd)
      apply (rule triv)
      done
  qed
qed

end
