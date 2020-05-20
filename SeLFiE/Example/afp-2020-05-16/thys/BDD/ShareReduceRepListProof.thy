(*  Title:       BDD

    Author:      Veronika Ortner and Norbert Schirmer, 2004
    Maintainer:  Norbert Schirmer,  norbert.schirmer at web de
    License:     LGPL
*)

(*  
ShareReduceRepListProof.thy

Copyright (C) 2004 Veronika Ortner and Norbert Schirmer 
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

section \<open>Proof of Procedure ShareReduceRepList\<close>
theory ShareReduceRepListProof imports ShareRepProof begin

lemma (in ShareReduceRepList_impl) ShareReduceRepList_modifies:
  shows "\<forall>\<sigma>. \<Gamma>\<turnstile>{\<sigma>}  PROC ShareReduceRepList (\<acute>nodeslist)
        {t. t may_only_modify_globals \<sigma> in [rep]}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done

lemma hd_filter_app: "\<lbrakk>filter P xs \<noteq> []; zs=xs@ys\<rbrakk> \<Longrightarrow> 
       hd (filter P zs) =  hd (filter P xs)"
  by (induct xs arbitrary: n m) auto


lemma (in ShareReduceRepList_impl) ShareReduceRepList_spec_total: 
defines "var_eq \<equiv> (\<lambda>ns var. (\<forall>no1 \<in> set ns. \<forall>no2 \<in> set ns. no1\<rightarrow>var = no2\<rightarrow>var))"
shows
  "\<forall>\<sigma> ns. \<Gamma>\<turnstile>\<^sub>t
   \<lbrace>\<sigma>. List \<acute>nodeslist \<acute>next ns \<and>
       (\<forall>no \<in> set ns.
            no \<noteq> Null \<and> ((no\<rightarrow>\<acute>low = Null) = (no\<rightarrow>\<acute>high = Null)) \<and> 
             no\<rightarrow>\<acute>low \<notin> set ns \<and> no\<rightarrow>\<acute>high \<notin> set ns \<and>
             (isLeaf_pt no \<acute>low \<acute>high = (no\<rightarrow>\<acute>var \<le> 1)) \<and>
             (no\<rightarrow>\<acute>low \<noteq> Null \<longrightarrow> (no\<rightarrow>\<acute>low)\<rightarrow>\<acute>rep \<noteq> Null) \<and>
             ((\<acute>rep \<propto> \<acute>low) no \<notin> set ns)) \<and>
        var_eq ns \<acute>var\<rbrace> 
    PROC  ShareReduceRepList (\<acute>nodeslist)
   \<lbrace>(\<forall>no. no \<notin> set ns \<longrightarrow> no\<rightarrow>\<^bsup>\<sigma>\<^esup>rep = no\<rightarrow>\<acute>rep)  \<and>
    (\<forall>no \<in> set ns. no\<rightarrow>\<acute>rep \<noteq> Null \<and> 
      (if ((\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>low) no = (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>high) no \<and> no\<rightarrow> \<^bsup>\<sigma>\<^esup>low \<noteq> Null) 
       then (no\<rightarrow>\<acute>rep = (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>low) no )
       else ((no\<rightarrow>\<acute>rep) \<in> set ns \<and> no\<rightarrow>\<acute>rep\<rightarrow>\<acute>rep = no\<rightarrow>\<acute>rep \<and> 
             (\<forall> no1 \<in> set ns. 
                 ((\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>high) no1 = (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>high) no \<and> 
                 (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>low) no1 = (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>low) no) = (no\<rightarrow>\<acute>rep = no1\<rightarrow>\<acute>rep)))))\<rbrace>"
apply (hoare_rule HoareTotal.ProcNoRec1)
apply (hoare_rule anno=
       " \<acute>node :== \<acute>nodeslist;;
         WHILE (\<acute>node \<noteq> Null ) 
         INV \<lbrace>\<exists>prx sfx. List \<acute>node \<acute>next sfx \<and> 
              List \<acute>nodeslist \<acute>next ns \<and> ns=prx@sfx \<and> 
              (\<forall>no \<in> set ns.
                 no \<noteq> Null \<and> ((no\<rightarrow>\<^bsup>\<sigma>\<^esup>low = Null) = (no\<rightarrow>\<^bsup>\<sigma>\<^esup>high = Null)) \<and> 
                 no\<rightarrow>\<^bsup>\<sigma>\<^esup>low \<notin> set ns \<and> no\<rightarrow>\<^bsup>\<sigma>\<^esup>high \<notin> set ns \<and>
                 (isLeaf_pt no  \<^bsup>\<sigma>\<^esup>low \<^bsup>\<sigma>\<^esup>high = (no\<rightarrow>\<^bsup>\<sigma>\<^esup>var \<le> 1)) \<and>
                 (no\<rightarrow>\<^bsup>\<sigma>\<^esup>low \<noteq> Null \<longrightarrow> (no\<rightarrow>\<^bsup>\<sigma>\<^esup>low)\<rightarrow>\<^bsup>\<sigma>\<^esup>rep \<noteq> Null) \<and>
                 ((\<^bsup>\<sigma>\<^esup>rep \<propto> \<^bsup>\<sigma>\<^esup>low) no  \<notin> set ns)) \<and>
              var_eq ns \<acute>var \<and>
              (\<forall>no.  no \<notin> set prx \<longrightarrow> no\<rightarrow>\<^bsup>\<sigma>\<^esup>rep = no \<rightarrow>\<acute>rep)  \<and>
              (\<forall> no \<in> set prx. no\<rightarrow>\<acute>rep \<noteq> Null \<and> 
               (if ((\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>low) no = (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>high) no \<and> no\<rightarrow>\<^bsup>\<sigma>\<^esup>low \<noteq> Null) 
                then (no\<rightarrow>\<acute>rep = (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>low) no )
                else ((no\<rightarrow>\<acute>rep)=hd (filter (\<lambda>sn. repNodes_eq sn no \<^bsup>\<sigma>\<^esup>low \<^bsup>\<sigma>\<^esup>high \<acute>rep) 
                                     prx) \<and> 
                     ((no\<rightarrow>\<acute>rep)\<rightarrow>\<acute>rep) = no\<rightarrow>\<acute>rep \<and> 
                     (\<forall>no1 \<in> set prx. 
                        ((\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>high) no1 = (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>high) no \<and> 
                         (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>low) no1 = (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>low) no) = 
                         (no\<rightarrow>\<acute>rep = no1\<rightarrow>\<acute>rep))))) \<and>
                 \<acute>nodeslist= \<^bsup>\<sigma>\<^esup>nodeslist \<and> \<acute>high=\<^bsup>\<sigma>\<^esup>high \<and> \<acute>low=\<^bsup>\<sigma>\<^esup>low \<and> \<acute>var=\<^bsup>\<sigma>\<^esup>var\<rbrace>
         VAR MEASURE (length (list \<acute>node \<acute>next))
         DO
         IF (\<not> isLeaf_pt \<acute>node \<acute>low \<acute>high \<and> 
            \<acute>node \<rightarrow> \<acute>low \<rightarrow> \<acute>rep = \<acute>node \<rightarrow> \<acute>high \<rightarrow> \<acute>rep )
         THEN \<acute>node \<rightarrow> \<acute>rep :== \<acute>node \<rightarrow> \<acute>low \<rightarrow> \<acute>rep
         ELSE CALL ShareRep (\<acute>nodeslist , \<acute>node)   
         FI;;
         \<acute>node :==\<acute>node \<rightarrow> \<acute>next
         OD" in HoareTotal.annotateI)
apply (vcg spec=spec_total)
apply   (rule_tac x="[]" in exI)
apply   (rule_tac x="ns" in exI)
using [[simp_depth_limit = 2]]
apply   (simp (no_asm_use))
prefer 2
using [[simp_depth_limit = 4]]
apply (clarsimp)
prefer 2
apply  (rule conjI)
apply   clarify
apply   (rule conjI)
apply    (clarsimp simp add: List_list) (* termination *)
apply   (simp only: List_not_Null simp_thms triv_forall_equality)
apply   clarify
apply   (simp only: triv_forall_equality)
apply   (rename_tac sfx)
apply   (rule_tac x="prx@[node]" in exI)
apply   (rule_tac x="sfx" in exI)
apply   (rule conjI)
apply    assumption
apply   (rule conjI)
apply    (simp (no_asm))
apply   (rule conjI)
apply    (assumption)
prefer 2
apply   clarify
apply   (simp only: List_not_Null simp_thms triv_forall_equality)
apply   clarify
apply   (simp only: triv_forall_equality)
apply   (rename_tac sfx)
apply   (rule_tac x="prx@node#sfx" in exI) (* Precondition for ShareRep *)
apply   (rule conjI)
apply    assumption
apply   (rule conjI)
apply    (rule ballI)
apply    (frule_tac x=no in bspec, assumption)
apply    (drule_tac x=node in bspec)
apply     (simp (no_asm_use))
apply    (elim conjE)
apply    (rule conjI)
apply     assumption
apply    (rule conjI)
apply     assumption
apply    (unfold var_eq_def)
apply    (drule_tac x=node in bspec, simp)
apply    (drule_tac x=no in bspec,assumption)
apply    (simp add: isLeaf_pt_def )
apply   (rule conjI)
apply    (simp (no_asm))
apply   (clarify)
apply   (rule conjI)
apply    (subgoal_tac "List node next (node#sfx)") (* termination *)
apply     (simp only: List_list)
apply     (simp (no_asm))
apply    (simp (no_asm_simp))
apply   (rule_tac x="prx@[node]" in exI)
apply   (rule_tac x="sfx" in exI)
apply   (rule conjI)
apply    assumption
apply   (rule conjI)
apply    (simp (no_asm))
apply   (rule conjI)
apply    (assumption)
using [[simp_depth_limit = 100]]
proof - (* From invariant to postcondition *)
  fix var low high rep nodeslist ns repa "next" no
  assume ns: "List nodeslist next ns"
  assume no_in_ns: "no \<in> set ns"
  assume while_inv: "\<forall>no\<in>set ns.
           repa no \<noteq> Null \<and>
           (if (repa \<propto> low) no = (repa \<propto> high) no \<and> high no \<noteq> Null
            then repa no = (repa \<propto> low) no
            else repa no = hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa] \<and>
                 repa (repa no) = repa no \<and>
                 (\<forall>no1\<in>set ns.
                     ((repa \<propto> high) no1 = (repa \<propto> high) no \<and>
                      (repa \<propto> low) no1 = (repa \<propto> low) no) =
                     (repa no = repa no1)))"
  assume pre: "\<forall>no\<in>set ns.
           no \<noteq> Null \<and>
           (low no = Null) = (high no = Null) \<and>
           low no \<notin> set ns \<and>
           high no \<notin> set ns \<and>
           isLeaf_pt no low high = (var no \<le> Suc 0) \<and>
           (low no \<noteq> Null \<longrightarrow> rep (low no) \<noteq> Null) \<and> (rep \<propto> low) no \<notin> set ns"
  assume same_var: "\<forall>no1\<in>set ns. \<forall>no2\<in>set ns. var no1 = var no2"
  assume share_case: "(repa \<propto> low) no = (repa \<propto> high) no \<longrightarrow> high no = Null"
  assume unmodif: "\<forall>no. no \<notin> set ns \<longrightarrow> rep no = repa no"
  show "hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa] \<in> set ns \<and>
        repa (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]) =
        hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]"
  proof -
    from no_in_ns pre obtain
      no_nNull: " no \<noteq> Null" and
      no_balanced: "(low no = Null) = (high no = Null)" and
      isLeaf_var: "isLeaf_pt no low high = (var no \<le> Suc 0)"
      by blast
    have repNodes_eq_same_node: "repNodes_eq no no low high repa"
      by (simp add: repNodes_eq_def)
    from no_in_ns have ns_nempty: "ns \<noteq> []"
      by auto
    from no_in_ns repNodes_eq_same_node 
    have repNodes_not_empty: "[sn\<leftarrow>ns . repNodes_eq sn no low high repa] \<noteq> []"
      by (rule filter_not_empty)
    then have hd_term_in_ns: "hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa] \<in> set ns"
      by (rule hd_filter_in_list)
    with while_inv obtain 
      repa_hd_nNull: "repa  (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]) \<noteq> Null"
      by auto
    let ?hd = "hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]"
    from hd_term_in_ns  pre obtain
      hd_nNull: " ?hd \<noteq> Null" and
      hd_balanced: 
        "(low (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]) = Null) = 
         (high (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]) = Null)" and
      hd_isLeaf_var: 
      "isLeaf_pt (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]) low high = 
      (var (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]) \<le> Suc 0)"
      by blast
    have "repa (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]) = 
      hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]"
    proof (cases "high no = Null")
      case True
      with no_balanced have "low no = Null"
        by simp
      with True have no_Leaf: "isLeaf_pt no low high"
        by (simp add: isLeaf_pt_def)
      with isLeaf_var have varno: "var no <= 1"
        by simp
      from same_var [rule_format, OF no_in_ns hd_term_in_ns] varno
      have "var (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]) \<le> 1"
        by simp
      with hd_isLeaf_var have 
        "isLeaf_pt (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]) low high"
        by simp
      with while_inv hd_term_in_ns repNodes_not_empty show ?thesis
        apply (simp add: isLeaf_pt_def)
        apply (erule_tac x=
          "hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]" in ballE)
        prefer 2
        apply simp
        apply (simp (no_asm_use) add: repNodes_eq_def)
        apply (rule filter_hd_P_rep_indep)
        apply   (simp (no_asm_simp))
        apply  (simp (no_asm_simp))
        apply assumption
        done
    next
      assume hno_nNull:  "high no \<noteq> Null"
      with share_case have repchildren_neq: "(repa \<propto> low) no \<noteq> (repa \<propto> high) no"
        by simp
      from repNodes_not_empty have 
        "repNodes_eq  (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]) no low high repa"
        by (rule hd_filter_prop)
      then 
      have "(repa \<propto> low) (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]) = 
              (repa \<propto> low) no \<and> 
            (repa \<propto> high) (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]) = 
              (repa \<propto> high) no"
        by (simp add: repNodes_eq_def)
      with repchildren_neq have 
        "(repa \<propto> low) (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa])
        \<noteq> (repa \<propto> high) (hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa])"
        by simp
      with while_inv hd_term_in_ns repNodes_not_empty show ?thesis
        apply (simp add: isLeaf_pt_def)
        apply (erule_tac x=
          "hd [sn\<leftarrow>ns . repNodes_eq sn no low high repa]" in ballE)
        prefer 2
        apply simp
        apply (simp (no_asm_use) add: repNodes_eq_def)
        apply (rule filter_hd_P_rep_indep)
        apply simp
        apply fastforce
        apply fastforce
        done
    qed
    with hd_term_in_ns
    show ?thesis
      by simp
  qed
next
  (* invariant to invariant, THEN part  --  REDUCING*)
  fix var low high rep nodeslist repa "next" node prx sfx
  assume ns: "List nodeslist next (prx @ node # sfx)"
  assume sfx: "List (next node) next sfx"
  assume node_not_Null: "node \<noteq> Null"
  assume nodes_balanced_ordered: "\<forall>no\<in>set (prx @ node # sfx).
           no \<noteq> Null \<and>
           (low no = Null) = (high no = Null) \<and>
           low no \<notin> set (prx @ node # sfx) \<and>
           high no \<notin> set (prx @ node # sfx) \<and>
           isLeaf_pt no low high = (var no \<le> (1::nat)) \<and>
           (low no \<noteq> Null \<longrightarrow> rep (low no) \<noteq> Null) \<and>
           (rep \<propto> low) no \<notin> set (prx @ node # sfx)"
  assume all_nodes_same_var: "\<forall>no1\<in>set (prx @ node # sfx).
           \<forall>no2\<in>set (prx @ node # sfx). var no1 = var no2"
  assume rep_repa_nc: "\<forall>no. no \<notin> set prx \<longrightarrow> rep no = repa no"
  assume while_inv: "\<forall>no\<in>set prx.
           repa no \<noteq> Null \<and>
           (if (repa \<propto> low) no = (repa \<propto> high) no \<and> low no \<noteq> Null
            then repa no = (repa \<propto> low) no
            else repa no = hd [sn\<leftarrow>prx . repNodes_eq sn no low high repa] \<and>
                 repa (repa no) = repa no \<and>
                 (\<forall>no1\<in>set prx.
                     ((repa \<propto> high) no1 = (repa \<propto> high) no \<and>
                      (repa \<propto> low) no1 = (repa \<propto> low) no) =
                     (repa no = repa no1)))"
  assume not_Leaf: "\<not> isLeaf_pt node low high" 
  assume repchildren_eq_nln: "repa (low node) = repa (high node)"
  show "(\<forall>no. no \<notin> set (prx @ [node]) \<longrightarrow>
                rep no = (repa(node := repa (high node))) no) \<and>
        (\<forall>no\<in>set (prx @ [node]).
              (repa(node := repa (high node))) no \<noteq> Null \<and>
              (if (repa(node := repa (high node)) \<propto> low) no =
                  (repa(node := repa (high node)) \<propto> high) no \<and>
                  low no \<noteq> Null
               then (repa(node := repa (high node))) no =
                    (repa(node := repa (high node)) \<propto> low) no
               else (repa(node := repa (high node))) no =
                    hd [sn\<leftarrow>prx @ [node] .
                        repNodes_eq sn no low high
                         (repa(node := repa (high node)))] \<and>
                    (repa(node := repa (high node)))
                     ((repa(node := repa (high node))) no) =
                    (repa(node := repa (high node))) no \<and>
                    (\<forall>no1\<in>set (prx @ [node]).
                        ((repa(node := repa (high node)) \<propto> high) no1 =
                         (repa(node := repa (high node)) \<propto> high) no \<and>
                         (repa(node := repa (high node)) \<propto> low) no1 =
                         (repa(node := repa (high node)) \<propto> low) no) =
                        ((repa(node := repa (high node))) no =
                         (repa(node := repa (high node))) no1))))"
    (is "?NodesUnmodif \<and> ?NodesModif")
  proof -
    \<comment> \<open>This proof was originally conducted without the
          substitution @{term "repa (low node) = repa (high node)"} preformed.
          So don't be confused if we show everythin for @{text "repa (low node)"}.\<close>
    from rep_repa_nc
    have nodes_unmodif: ?NodesUnmodif
      by auto
    hence rep_Sucna_nc:
      "(\<forall>no. no \<notin> set (prx @ [node]) 
      \<longrightarrow> rep no = (repa(node := repa (low (node )))) no)"
      by auto
    have nodes_modif: ?NodesModif (is "\<forall>no\<in>set (prx @ [node]). ?P no \<and> ?Q no")
    proof (rule ballI)
      fix no
      assume no_in_take_Sucna: " no \<in> set (prx @ [node])"
      show "?P no \<and> ?Q no"
      proof (cases "no = node")
        case False
        note no_noteq_nln=this
        with no_in_take_Sucna 
        have no_in_take_n: "no \<in> set prx"
          by auto
        with no_in_take_n while_inv obtain 
          repa_no_nNull: " repa no \<noteq> Null" and
          repa_cases: "(if (repa \<propto> low) no = (repa \<propto> high) no \<and> low no \<noteq> Null 
          then repa no = (repa \<propto> low) no
          else  repa no = hd [sn\<leftarrow>prx . repNodes_eq sn no low high repa] 
          \<and> repa (repa no) = repa no \<and> 
          (\<forall>no1\<in>set prx. ((repa \<propto> high) no1 = (repa \<propto> high) no 
          \<and> (repa \<propto> low) no1 = (repa \<propto> low) no) 
          = (repa no = repa no1)))"
          using [[simp_depth_limit = 2]]
          by auto 
        from no_in_take_n 
        have no_in_nodeslist: "no \<in> set (prx @ node # sfx)"
          by auto
        from repa_no_nNull no_noteq_nln have ext_repa_nNull: "?P no"
          by auto
        from no_in_nodeslist nodes_balanced_ordered obtain
          nln_nNull: "node \<noteq> Null" and
          nln_balanced_children: "(low node = Null) = (high node = Null)" and
          lnln_notin_nodeslist: "low node \<notin> set (prx @ node # sfx)" and
          hnln_notin_nodeslist: "high node \<notin> set (prx @ node # sfx)" and
          isLeaf_var_nln: "isLeaf_pt node low high = (var node \<le> 1)" and
          node_nNull_rap_nNull_nln: "(low node \<noteq> Null 
          \<longrightarrow> rep (low node) \<noteq> Null)" and
          nln_varrep_le_var: "(rep \<propto> low) node \<notin> set (prx @ node # sfx)"
          apply (erule_tac x="node" in ballE)
          apply auto
          done
        from  no_in_nodeslist nodes_balanced_ordered no_in_take_Sucna 
        obtain 
          no_nNull: "no \<noteq> Null" and
          balanced_children: "(low no = Null) = (high no = Null)" and
          lno_notin_nodeslist: "low no \<notin> set (prx @ node # sfx)" and
          hno_notin_nodeslist: "high no \<notin> set (prx @ node # sfx)" and
          isLeaf_var_no: "isLeaf_pt no low high = (var no \<le> 1)" and
          node_nNull_rep_nNull: "(low no \<noteq> Null \<longrightarrow> rep (low no) \<noteq> Null)" and
          varrep_le_var: "(rep \<propto> low) no \<notin> set (prx @ node # sfx)"
          apply -
          apply (erule_tac x=no in ballE)
          apply auto
          done
        from lno_notin_nodeslist  
        have ext_rep_null_comp_low: 
          "(repa (node := repa (low node)) \<propto> low) no = (repa \<propto> low) no"
          by (auto simp add: null_comp_def)
        from hno_notin_nodeslist 
        have ext_rep_null_comp_high: 
          "(repa (node := repa (low node)) \<propto> high) no = (repa \<propto> high) no"
          by (auto simp add: null_comp_def)
        have share_reduce_if: "?Q no"
        proof (cases "(repa (node := repa (low node)) \<propto> low) no = 
            (repa(node := repa (low node)) \<propto> high) no \<and> low no \<noteq> Null")
          case True
          then obtain 
            red_case: "(repa (node := repa (low node)) \<propto> low) no = 
            (repa(node := repa (low node)) \<propto> high) no" and
            lno_nNull: "low no \<noteq> Null"
            by simp
          from lno_nNull balanced_children have hno_nNull: "high no \<noteq> Null"
            by simp
          from True ext_rep_null_comp_low ext_rep_null_comp_high 
          have repchildren_eq_no: "(repa \<propto> low) no = (repa \<propto> high) no"
            by simp
          with repa_cases lno_nNull have "repa no = (repa \<propto> low) no"
            by auto
          with ext_rep_null_comp_low no_noteq_nln 
          have "(repa(node := repa (low node))) no = 
            (repa (node := repa (low node)) \<propto> low) no"
            by simp
          with True repchildren_eq_nln show ?thesis
            by auto
        next
          assume share_case_ext: 
            " \<not> ((repa(node := repa (low node)) \<propto> low) no = 
            (repa(node := repa (low node)) \<propto> high) no \<and> low no \<noteq> Null)"
          from not_Leaf isLeaf_var_nln 
          have "1 < var node"
            by simp
          with all_nodes_same_var 
          have all_nodes_nl_Suc0_l_var: "\<forall>x \<in> set (prx @ node # sfx). 1 < var x"
            using [[simp_depth_limit=1]]
            by auto
          with nodes_balanced_ordered 
          have all_nodes_nl_noLeaf: 
            "\<forall>x \<in> set (prx @ node # sfx). \<not> isLeaf_pt x low high"
            apply -
            apply rule
            apply (drule_tac x=x in bspec,assumption)
            apply (drule_tac x=x in bspec,assumption)
            apply auto
            done
          from nodes_balanced_ordered 
          have all_nodes_nl_balanced: 
            "\<forall>x \<in> set (prx @ node # sfx). (low x = Null) = (high x = Null)"
            apply -
            apply rule
            apply (drule_tac x=x in bspec,assumption)
            apply auto
            done
          from all_nodes_nl_Suc0_l_var no_in_nodeslist 
          have Suc0_l_var_no: "1 < var no"
            by auto
          with isLeaf_var_no have no_nLeaf: " \<not> isLeaf_pt no low high"
            by simp
          with balanced_children have lno_nNull: "low no \<noteq> Null"
            by (simp add: isLeaf_pt_def)
          with balanced_children have hno_nNull: "high no \<noteq> Null"
            by simp
          with share_case_ext ext_rep_null_comp_low ext_rep_null_comp_high lno_nNull 
          have repchildren_neq_no: "(repa \<propto> low) no \<noteq> (repa \<propto> high) no"
            by (simp add: null_comp_def)
          with repa_cases 
          have share_case_inv: 
          "repa no = hd [sn\<leftarrow>prx . repNodes_eq sn no low high repa] \<and> 
            repa (repa no) = repa no \<and> 
            (\<forall>no1\<in>set prx. ((repa \<propto> high) no1 = (repa \<propto> high) no \<and> 
            (repa \<propto> low) no1 = (repa \<propto> low) no) = (repa no = repa no1))"
            by auto
          then have repa_no: "repa no = hd [sn\<leftarrow>prx . repNodes_eq sn no low high repa]"
            by simp
          from Suc0_l_var_no have "\<forall>x \<in> set (prx @ node # sfx). 1 < var no"
            by auto
          from no_in_take_n have "[sn\<leftarrow>prx . repNodes_eq sn no low high repa] \<noteq> []"
            apply -
            apply (rule filter_not_empty)
            apply (auto simp add: repNodes_eq_def)
            done
          then have "repNodes_eq 
            (hd [sn\<leftarrow>prx. repNodes_eq sn no low high repa]) no low high repa"
            by (rule hd_filter_prop)
          with repa_no 
          have rep_children_eq_no_repa_no: 
            "(repa \<propto> low) (repa no) = (repa \<propto> low) no \<and> 
             (repa \<propto> high) (repa no) = (repa \<propto> high) no"
            by (simp add: repNodes_eq_def) 
          from lno_notin_nodeslist rep_repa_nc 
          have rep_repa_nc_low_no: "rep (low no) = repa (low no)"
            apply -
            apply (erule_tac x="low no" in allE)
            apply auto
            done
          have "\<forall>x \<in> set (prx @ [node]). 
            repNodes_eq x no low high (repa(node := repa (low node))) = 
            repNodes_eq x no low high repa"
          proof (rule ballI, unfold repNodes_eq_def)
            fix x
            assume x_in_take_Sucn: " x \<in> set (prx @ [node])"
            hence x_in_nodeslist: "x \<in> set (prx @ node # sfx)"
              by auto
            with all_nodes_nl_noLeaf nodes_balanced_ordered 
            have children_nNull_x: "low x \<noteq> Null \<and> high x \<noteq> Null"
              apply -
              apply (drule_tac x=x in bspec,assumption)
              apply (drule_tac x=x in bspec,assumption)
              apply (auto simp add: isLeaf_pt_def) 
              done
            from x_in_nodeslist nodes_balanced_ordered 
            have "low x \<notin> set (prx @ node # sfx) \<and> high x \<notin> set (prx @ node # sfx)"
              apply -
              apply (drule_tac x=x in bspec,assumption)
              apply auto
              done
            with lno_notin_nodeslist hno_notin_nodeslist 
              children_nNull_x lno_nNull hno_nNull
            show "((repa(node := repa (low node)) \<propto> high) x = 
              (repa(node := repa (low node)) \<propto> high) no \<and>
              (repa(node := repa (low node)) \<propto> low) x = 
              (repa(node := repa (low node)) \<propto> low) no) =
              ((repa \<propto> high) x = (repa \<propto> high) no \<and> 
              (repa \<propto> low) x = (repa \<propto> low) no)"
              by (simp add: null_comp_def)
          qed
          then have filter_extrep_rep: 
            "[sn\<leftarrow>(prx @ [node]). repNodes_eq sn no low high 
                                   (repa(node := repa (low node)))] = 
            [sn\<leftarrow>(prx @ [node]) . repNodes_eq sn no low high repa]"
            by (rule P_eq_list_filter)
          from no_in_take_n 
          have filter_n_notempty: "[sn\<leftarrow>prx. repNodes_eq sn no low high repa] \<noteq> []"
            apply (rule filter_not_empty)
            apply (simp add: repNodes_eq_def)
            done
          then have "hd [sn\<leftarrow>prx. repNodes_eq sn no low high repa] = 
            hd [sn\<leftarrow>prx@[node]. repNodes_eq sn no low high repa]"
            by auto
          with no_noteq_nln filter_extrep_rep repa_no 
          have ext_repa_no: "(repa(node:= repa (low node))) no = 
            hd [sn\<leftarrow>prx@[node] . repNodes_eq sn no low high 
            (repa(node := repa (low node)))]"
            by simp
          have "(repa(node := repa (low node))) (repa no) = repa no"
          proof (cases "repa no =  node")
            case True
            note rno_nln=this
            from rep_repa_nc_low_no rep_children_eq_no_repa_no lno_nNull 
              node_nNull_rep_nNull 
            have low_rep_no_nNull: "low (repa no) \<noteq> Null"
              apply (simp add: null_comp_def)
              apply auto
              done
            with nodes_balanced_ordered rno_nln 
            have high_rap_no_nNull: "high (repa no) \<noteq> Null"
              apply -
              apply (drule_tac x="repa no" in bspec)
              apply auto
              done
            with low_rep_no_nNull rno_nln rep_children_eq_no_repa_no 
            have "repa (low node) = (repa \<propto> low) no \<and> 
              repa (high node) = (repa \<propto> high) no" 
              by (simp add: null_comp_def)
            with repchildren_eq_nln have " (repa \<propto> low) no = (repa \<propto> high) no"
              by simp
            with repchildren_neq_no show ?thesis
              by simp
          next
            assume rno_not_nln: "repa no \<noteq> node"
            from share_case_inv have "repa (repa no) = repa no"
              by auto
            with rno_not_nln show ?thesis
              by simp
          qed
          with no_noteq_nln have ext_repa_ext_repa: 
            "(repa(node := repa (low node))) 
            ((repa(node := repa (low node))) no) 
            = (repa(node := repa (low node))) no" 
            by simp
          have "(\<forall>no1\<in>set (prx@[node]).
            ((repa(node := repa (low node)) \<propto> high) no1 = 
            (repa(node  := repa (low node)) \<propto> high) no \<and>
            (repa(node  := repa (low node)) \<propto> low) no1 = 
            (repa(node  := repa (low node)) \<propto> low) no) =
            ((repa(node  := repa (low node))) no = 
            (repa(node  := repa (low node))) no1))"
          proof (rule ballI)
            fix no1
            assume no1_in_take_Sucn: " no1 \<in> set (prx@[node])"
            hence no1_in_nodeslist: "no1 \<in> set (prx @ node # sfx)"
              by auto
            show "((repa(node := repa (low node)) \<propto> high) no1 = 
                 (repa(node := repa (low node)) \<propto> high) no \<and>
                 (repa(node := repa (low node)) \<propto> low) no1 = 
                 (repa(node := repa (low node)) \<propto> low) no) =
                 ((repa(node := repa (low node))) no = 
                  (repa(node := repa (low node))) no1)"
            proof (cases "no1 = node")
              case True
              show ?thesis
              proof (rule, elim conjE)
                assume ext_repa_no_no1: 
                  "(repa(node := repa (low node))) no = 
                    (repa(node := repa (low node))) no1"
                with True no_noteq_nln 
                have repa_no_repa_low_nln: "repa no = repa (low node)"
                  by simp
                from filter_n_notempty 
                have repa_no_in_take_n:  
                  "hd [sn\<leftarrow>prx. repNodes_eq sn no low high repa] 
                    \<in> set prx "
                  apply -
                  apply (rule hd_filter_in_list)
                  apply auto
                  done
                with repa_no 
                have repa_no_in_nodeslist: "repa no \<in> set (prx @ node # sfx)"
                  by auto
                from lnln_notin_nodeslist rep_repa_nc 
                have rep_repa_low_nln: "rep (low node) = repa (low node)"
                  by auto
                from all_nodes_nl_noLeaf nln_balanced_children
                have "low node \<noteq> Null"
                  by (auto simp add: isLeaf_pt_def)
                with rep_repa_low_nln lnln_notin_nodeslist lno_nNull 
                  nln_varrep_le_var 
                have "repa (low node) \<notin> set (prx @ node # sfx)"
                  by (simp add: null_comp_def) 
                with repa_no_repa_low_nln repa_no_in_nodeslist 
                show "(repa(node := repa (low node)) \<propto> high) no1 = 
                  (repa(node := repa (low node)) \<propto> high) no \<and>
                  (repa(node := repa (low node)) \<propto> low) no1 = 
                  (repa(node := repa (low node)) \<propto> low) no"
                  by simp
              next
                assume no_no1_high: 
                  "(repa(node := repa (low node)) \<propto> high) no1 = 
                  (repa(node := repa (low node)) \<propto> high) no"
                assume no_no1_low: 
                  "(repa(node := repa (low node)) \<propto> low) no1 = 
                  (repa(node := repa (low node)) \<propto> low) no"
                from True repchildren_eq_nln 
                have repachildren_eq_no1: " repa (low no1) = repa (high no1)"
                  by simp
                from not_Leaf True nln_balanced_children 
                have children_nNull_no1: "(low no1) \<noteq> Null \<and> high no1 \<noteq> Null"
                  by (simp add: isLeaf_pt_def)
                with repachildren_eq_no1 
                have repchildren_eq_no1: "(repa \<propto> low) no1 = (repa \<propto> high) no1"
                  by (simp add: null_comp_def)
                from no_no1_low children_nNull_no1 lno_nNull 
                  lnln_notin_nodeslist lno_notin_nodeslist True 
                have rep_low_eq_no_no1: "(repa \<propto> low) no1 = (repa \<propto> low) no"
                  by (simp add: null_comp_def)
                from no_no1_high children_nNull_no1 hno_nNull 
                  hnln_notin_nodeslist hno_notin_nodeslist True 
                have rep_high_eq_no_no1: "(repa \<propto> high) no1 = (repa \<propto> high) no"
                  by (simp add: null_comp_def)
                with rep_low_eq_no_no1 repchildren_eq_no1 
                have "(repa \<propto> low) no = (repa \<propto> high) no"
                  by simp
                with repchildren_neq_no 
                show "(repa(node := repa (low node))) no = 
                  (repa(node := repa (low node))) no1"
                  by simp
              qed
            next
              assume no1_neq_nln: "no1 \<noteq> node"
              from no1_in_nodeslist nodes_balanced_ordered 
              have children_notin_nl_no1: 
              "low no1 \<notin> set (prx @ node # sfx) \<and> high no1 \<notin> set (prx @ node # sfx)"
                apply -
                apply (drule_tac x=no1 in bspec,assumption)
                by auto
              from no1_neq_nln no1_in_take_Sucn 
              have no1_in_take_n: "no1 \<in> set prx"
                by auto
              from no1_in_nodeslist all_nodes_nl_noLeaf all_nodes_nl_balanced 
              have children_nNull_no1: "(low no1) \<noteq> Null \<and> high no1 \<noteq> Null"
                by  (auto simp add: isLeaf_pt_def)
              show ?thesis
              proof (rule, elim conjE)
                assume ext_repa_high_no1_no: 
                "(repa(node := repa (low node)) \<propto> high) no1 
                  = (repa(node := repa (low node)) \<propto> high) no" 
                assume ext_repa_low_no1_no: 
                  "(repa(node := repa (low node)) \<propto> low) no1 
                  = (repa(node := repa (low node)) \<propto> low) no"
                from children_nNull_no1 hno_nNull ext_repa_high_no1_no 
                  children_notin_nl_no1 
                  hno_notin_nodeslist 
                have repa_high_no1_no: "(repa \<propto> high) no1 = (repa \<propto> high) no"
                  by (simp add: null_comp_def)
                from children_nNull_no1 lno_nNull ext_repa_low_no1_no 
                  children_notin_nl_no1 lno_notin_nodeslist 
                have repa_low_no1_no: "(repa \<propto> low) no1 = (repa \<propto> low) no"
                  by (simp add: null_comp_def)
                from repchildren_neq_no repa_high_no1_no repa_low_no1_no 
                have "(repa \<propto> low) no1 \<noteq> (repa \<propto> high) no1"
                  by simp
                from no1_in_take_n share_case_inv repa_high_no1_no repa_low_no1_no 
                have "repa no = repa no1"
                  by auto
                with no_noteq_nln no1_neq_nln 
                show " (repa(node := repa (low node))) no = 
                  (repa(node := repa (low node))) no1"
                  by simp
              next
                assume "(repa(node := repa (low node))) no = 
                  (repa(node := repa (low node))) no1"
                with no_noteq_nln no1_neq_nln 
                have "repa no = repa no1"
                  by simp
                with share_case_inv no1_in_take_n 
                have "((repa \<propto> high) no1 = (repa \<propto> high) no \<and> 
                  (repa \<propto> low) no1 = (repa \<propto> low) no)"
                  by auto
                with children_notin_nl_no1 children_nNull_no1 lno_notin_nodeslist 
                  hno_notin_nodeslist lno_nNull hno_nNull 
                show "(repa(node := repa (low node)) \<propto> high) no1 = 
                (repa(node := repa (low node)) \<propto> high) no \<and>
                (repa(node := repa (low node)) \<propto> low) no1 = 
                (repa(node := repa (low node)) \<propto> low) no"
                  by (auto simp add: null_comp_def)
              qed 
            qed
          qed
          from ext_repa_ext_repa ext_repa_no share_case_ext repchildren_eq_nln this 
          show ?thesis
            using [[simp_depth_limit=4]]
            by auto 
        qed
        with ext_repa_nNull show ?thesis
          by auto
      next
        assume no_nln: "no = node"
        hence no_in_nodeslist: "no \<in> set (prx @ node # sfx)"
          by simp
        from no_nln not_Leaf no_in_nodeslist 
          nodes_balanced_ordered [rule_format, OF this] obtain  
          low_no_nNull: "low no \<noteq> Null" and
          high_no_nNull: "high no \<noteq> Null" and
          rep_low_no_nNull: "rep (low no) \<noteq> Null" and
          lno_notin_nl: "low no \<notin> set (prx @ node # sfx)" and
          hno_notin_nl: "high no \<notin> set (prx @ node # sfx)" and
          children_nNull_no: "(low no \<noteq> Null) \<and> (high no \<noteq> Null)"
          apply (unfold isLeaf_pt_def)
          apply blast
          done
        then have "low no \<notin> set prx"
          by auto
        with rep_repa_nc no_nln rep_low_no_nNull 
        have "(repa(node := repa (low node))) no \<noteq> Null"
          by simp
        moreover
        have "(if (repa(node := repa (low node)) \<propto> low) no = 
                  (repa(node := repa (low node)) \<propto> high) no \<and> low no \<noteq> Null
          then (repa(node := repa (low node))) no = 
               (repa(node := repa (low node)) \<propto> low) no
          else (repa(node := repa (low node))) no =
            hd [sn\<leftarrow>prx@[node]. repNodes_eq sn no low high 
                (repa(node := repa (low node)))] \<and>
          (repa(node := repa (low node))) 
            ((repa(node := repa (low node))) no) =
            (repa(node := repa (low node))) no \<and>
          (\<forall>no1\<in>set (prx@[node]).
            ((repa(node := repa (low node)) \<propto> high) no1 = 
            (repa(node := repa (low node)) \<propto> high) no \<and>
            (repa(node := repa (low node)) \<propto> low) no1 = 
            (repa(node := repa (low node)) \<propto> low) no) =
            ((repa(node := repa (low node))) no = 
            (repa(node := repa (low node))) no1)))"
        proof (cases "(repa(node := repa (low node)) \<propto> low) no = 
          (repa(node := repa (low node)) \<propto> high) no \<and> low no \<noteq> Null")
          case True
          note red_case=this
          with children_nNull_no lno_notin_nl hno_notin_nl 
          have "(repa \<propto> low) no = (repa \<propto> high) no"
            by (auto simp add: null_comp_def)
          from children_nNull_no lno_notin_nl 
          have ext_repa_eq_repa_low: "(repa(node := repa (low node)) \<propto> low) no 
            = (repa \<propto> low) no "
            by (auto simp add: null_comp_def)
          from children_nNull_no hno_notin_nl 
          have ext_repa_eq_repa_high: 
            "(repa(node := repa (low node)) \<propto> high) no 
            = (repa \<propto> high) no "
            by (auto simp add: null_comp_def)
          from no_nln children_nNull_no 
          have "repa (low node) = (repa \<propto> low) no"
            by (simp add: null_comp_def)
          with red_case ext_repa_eq_repa_high ext_repa_eq_repa_low no_nln 
          show ?thesis 
            using [[simp_depth_limit=2]]
            by (auto simp del: null_comp_not_Null)
        next
          assume share_case: " \<not> ((repa(node := repa (low node)) \<propto> low) no 
            = (repa(node := repa (low node)) \<propto> high) no \<and> low no \<noteq> Null)"
          with low_no_nNull have "(repa(node := repa (low node)) \<propto> low) no 
            \<noteq> (repa(node := repa (low node)) \<propto> high) no"
            by simp
          with children_nNull_no lno_notin_nl hno_notin_nl 
          have "(repa \<propto> low) no \<noteq> (repa \<propto> high) no"
            by (auto simp add: null_comp_def)
          with children_nNull_no have "repa (low no) \<noteq> repa (high no)"
            by (simp add: null_comp_def)
          with repchildren_eq_nln no_nln show ?thesis
            by simp
        qed
        ultimately show ?thesis
          using repchildren_eq_nln
          apply -
          apply (simp only:)
          apply (simp (no_asm))
          done
      qed
    qed
    from nodes_unmodif nodes_modif
    show ?thesis by iprover
  qed
next
  fix var low high rep nodeslist repa "next" node prx sfx repb
  assume ns: "List nodeslist next (prx @ node # sfx)"
  assume sfx: "List (next node) next sfx"
  assume nodes_balanced_ordered: "\<forall>no\<in>set (prx @ node # sfx).
           no \<noteq> Null \<and>
           (low no = Null) = (high no = Null) \<and>
           low no \<notin> set (prx @ node # sfx) \<and>
           high no \<notin> set (prx @ node # sfx) \<and>
           isLeaf_pt no low high = (var no \<le> (1::nat)) \<and>
           (low no \<noteq> Null \<longrightarrow> rep (low no) \<noteq> Null) \<and>
           (rep \<propto> low) no \<notin> set (prx @ node # sfx)"
  assume all_nodes_same_var: "\<forall>no1\<in>set (prx @ node # sfx).
           \<forall>no2\<in>set (prx @ node # sfx). var no1 = var no2"
  assume rep_repa_nc: "\<forall>no. no \<notin> set prx \<longrightarrow> rep no = repa no"
  assume while_inv: "\<forall>no\<in>set prx.
           repa no \<noteq> Null \<and>
           (if (repa \<propto> low) no = (repa \<propto> high) no \<and> low no \<noteq> Null
            then repa no = (repa \<propto> low) no
            else repa no = hd [sn\<leftarrow>prx . repNodes_eq sn no low high repa] \<and>
                 repa (repa no) = repa no \<and>
                 (\<forall>no1\<in>set prx.
                     ((repa \<propto> high) no1 = (repa \<propto> high) no \<and>
                      (repa \<propto> low) no1 = (repa \<propto> low) no) =
                     (repa no = repa no1)))"
  assume share_cond: 
    "\<not> (\<not> isLeaf_pt node low high \<and> repa (low node) = repa (high node))"
  assume repb_node: 
          "repb node = hd [sn\<leftarrow>prx @ node # sfx . repNodes_eq sn node low high repa]"
  assume repa_repb_nc: "\<forall>pt. pt \<noteq> node \<longrightarrow> repa pt = repb pt" 
  assume var_repb_node: "var (repb node) = var node"
  show "(\<forall>no. no \<notin> set (prx @ [node]) \<longrightarrow> rep no = repb no) \<and>
          (\<forall>no\<in>set (prx @ [node]).
              repb no \<noteq> Null \<and>
              (if (repb \<propto> low) no = (repb \<propto> high) no \<and> low no \<noteq> Null
               then repb no = (repb \<propto> low) no
               else repb no =
                    hd [sn\<leftarrow>prx @ [node] . repNodes_eq sn no low high repb] \<and>
                    repb (repb no) = repb no \<and>
                    (\<forall>no1\<in>set (prx @ [node]).
                        ((repb \<propto> high) no1 = (repb \<propto> high) no \<and>
                         (repb \<propto> low) no1 = (repb \<propto> low) no) =
                        (repb no = repb no1))))"
  proof -
    have rep_repb_nc: "(\<forall>no. no \<notin> set (prx @ [node]) \<longrightarrow> rep no = repb no)"
    proof (intro allI impI)
      fix no
      assume no_notin_take_Sucn: "no \<notin> set (prx @ [node])"
      with rep_repa_nc 
      have rep_repa_nc_Sucn: "rep no = repa no"
        by auto
      from no_notin_take_Sucn have "no \<noteq> node"
        by auto
      with repa_repb_nc have "repa no = repb no"
        by auto
      with rep_repa_nc_Sucn show "rep no = repb no"
        by simp
    qed
    moreover
    have repb_no_share_def: 
      "(\<forall>no\<in>set (prx @ [node]). 
      \<not> ((repb \<propto> low) no = (repb \<propto> high) no \<and> low no \<noteq> Null) \<longrightarrow> 
          repb no = hd [sn\<leftarrow>(prx @ [node]) . repNodes_eq sn no low high repb])" 
    proof (intro ballI impI)
      fix no
      assume no_in_take_Sucn: " no \<in> set (prx @ [node])"
      assume share_prop: "\<not> ((repb \<propto> low) no = (repb \<propto> high) no \<and> low no \<noteq> Null)"
      from share_prop have share_or: 
        "(repb \<propto> low) no \<noteq> (repb \<propto> high) no \<or> low no = Null"
        using [[simp_depth_limit=2]]
        by simp
      from no_in_take_Sucn have no_in_nl: "no \<in> set (prx @ node # sfx)"
        by auto
      from nodes_balanced_ordered [rule_format, OF this] obtain
        no_nNull: "no \<noteq> Null" and
        balanced_no: "(low no = Null) = (high no = Null)" and
        lno_notin_nl: "low no \<notin> set (prx @ node # sfx)" and
        hno_notin_nl: "high no \<notin> set (prx @ node # sfx)" and
        isLeaf_var_no: "isLeaf_pt no low high = (var no \<le> 1)"
        by auto
      have nodes_notin_nl_neq_nln: "\<forall>p. p \<notin> set (prx @ node # sfx) \<longrightarrow> p \<noteq> node "
        by auto 
      show " repb no = hd [sn\<leftarrow>(prx @ [node]). repNodes_eq sn no low high repb]"
      proof (cases "no = node")
        case False
        note no_notin_nl=this
        with no_in_take_Sucn have no_in_take_n: "no \<in> set prx"
          by auto
        from False repa_repb_nc have repb_repa_no: "repb no = repa no" 
          by auto
        with while_inv [rule_format, OF no_in_take_n] no_in_take_n obtain 
          repa_no_nNull: "repa no \<noteq> Null" and
          while_share_red_exp: 
          "(if (repa \<propto> low) no = (repa \<propto> high) no \<and> low no \<noteq> Null 
              then repa no = (repa \<propto> low) no
              else repa no = hd [sn\<leftarrow>prx . repNodes_eq sn no low high repa] \<and>
              repa (repa no) = repa no \<and> 
              (\<forall>no1\<in>set prx. ((repa \<propto> high) no1 = (repa \<propto> high) no \<and> 
              (repa \<propto> low) no1 = (repa \<propto> low) no) = (repa no = repa no1)))"
          using [[simp_depth_limit = 2]]
          by auto 
        from no_in_take_n 
        have filter_take_n_notempty: "[sn\<leftarrow>prx. 
          repNodes_eq sn no low high repa] \<noteq> []"
          apply -
          apply (rule filter_not_empty)
          apply (auto simp add: repNodes_eq_def)
          done
        then have hd_term_n_Sucn: 
          "hd [sn\<leftarrow>prx. repNodes_eq sn no low high repa] 
              = hd [sn\<leftarrow>prx@[node] . repNodes_eq sn no low high repa]"
          by auto
        thus ?thesis
        proof (cases "low no = Null")
          case True
          note lno_Null=this
          with balanced_no have hno_Null: "high no = Null" 
            by simp
          from lno_Null hno_Null have isLeaf_no: "isLeaf_pt no low high"
            by (simp add: isLeaf_pt_def)
          from True while_share_red_exp 
          have while_low_Null: 
            "repa no = hd [sn\<leftarrow>prx. repNodes_eq sn no low high repa] \<and>
             repa (repa no) = repa no \<and> 
             (\<forall>no1\<in>set prx. ((repa \<propto> high) no1 = (repa \<propto> high) no 
             \<and> (repa \<propto> low) no1 = (repa \<propto> low) no) = (repa no = repa no1))"
            by auto
          have all_nodes_in_nl_Leafs: 
            "\<forall>x \<in> set (prx @ node # sfx). isLeaf_pt x low high"
          proof (intro ballI)
            fix x
            assume x_in_nodeslist: "x \<in> set (prx @ node # sfx)"
            from isLeaf_no isLeaf_var_no have "var no \<le> 1"
              by simp
            with all_nodes_same_var [rule_format, OF x_in_nodeslist no_in_nl]
            have "var x \<le> 1"
              by simp
            with nodes_balanced_ordered [rule_format, OF x_in_nodeslist]
            show "isLeaf_pt x low high"
              by (auto simp add: isLeaf_pt_def)  
          qed
          have "\<forall> x \<in> set (prx@[node]). repNodes_eq x no low high repb 
                = repNodes_eq x no low high repa"
          proof (rule ballI)
            fix x
            assume x_in_take_Sucn: "x \<in> set (prx@[node])"
            hence x_in_nodeslist: "x \<in> set (prx @ node # sfx)"
              by auto
            with all_nodes_in_nl_Leafs have "isLeaf_pt x low high"
              by auto
            with isLeaf_no repa_repb_nc show "repNodes_eq x no low high repb 
                  = repNodes_eq x no low high repa"
              by (simp add: repNodes_eq_def null_comp_def isLeaf_pt_def)
          qed
          then have " [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repa] 
                = [sn\<leftarrow>(prx@[node]) . repNodes_eq sn no low high repb]"
            apply -
            apply (rule P_eq_list_filter)
            apply simp
            done
          with hd_term_n_Sucn while_low_Null repb_repa_no show ?thesis 
            by auto
        next
          assume lno_nNull: " low no \<noteq> Null"
          with balanced_no have hno_nNull: "high no \<noteq> Null"
            by simp
          with lno_nNull have no_nLeaf: "\<not> isLeaf_pt no low high"
            by (simp add: isLeaf_pt_def)
          with isLeaf_var_no have Sucn_s_varno: "1 < var no"
            by auto
          with no_in_nl all_nodes_same_var 
          have all_nodes_nl_var: "\<forall> x \<in> set (prx @ node # sfx). 1 < var x"
            apply -
            apply (rule ballI)
            apply (drule_tac x=no in bspec,assumption)
            apply (drule_tac x=x in bspec,assumption)
            apply auto
            done
          with nodes_balanced_ordered 
          have all_nodes_nl_nLeaf: 
            "\<forall>x \<in> set (prx @ node # sfx). \<not> isLeaf_pt x low high"
            apply -
            apply (rule ballI)
            apply (drule_tac x=x in bspec,assumption)
            apply (drule_tac x=x in bspec,assumption)
            apply auto
            done
          from lno_nNull share_or 
          have repbchildren_eq_no: "(repb \<propto> low) no \<noteq> (repb \<propto> high) no"
            by simp
          with lno_nNull hno_nNull lno_notin_nl hno_notin_nl repa_repb_nc  
            nodes_notin_nl_neq_nln 
          have repachildren_eq_no: "(repa \<propto> low) no \<noteq> (repa \<propto> high) no"
            using [[simp_depth_limit=2]]
            by (simp add: null_comp_def) 
          with while_share_red_exp 
          have repa_no_def: 
            "repa no = hd [sn\<leftarrow>prx . repNodes_eq sn no low high repa] "
            by auto
          with no_notin_nl repa_repb_nc 
          have "repb no =  hd [sn\<leftarrow>prx. repNodes_eq sn no low high repa] "
            by simp
          with hd_term_n_Sucn 
          have repb_no_hd_term_repa: "repb no = 
                 hd [sn\<leftarrow>prx@[node] . repNodes_eq sn no low high repa] "
            by simp
          have "\<forall>x \<in> set (prx@[node]). 
            repNodes_eq x no low high repa = repNodes_eq x no low high repb" 
          proof (intro ballI)
            fix x
            assume x_in_take_Sucn: "x \<in> set (prx@[node]) "
            hence x_in_nodeslist: "x \<in> set (prx @ node # sfx)"
              by auto
            with all_nodes_nl_nLeaf have x_nLeaf: "\<not> isLeaf_pt x low high"
              by auto
            from nodes_balanced_ordered [rule_format, OF x_in_nodeslist] obtain
              balanced_x: "(low x = Null) = (high x = Null)" and
              lx_notin_nl: "low x \<notin> set (prx @ node # sfx)" and
              hx_notin_nl: "high x \<notin> set (prx @ node # sfx)" 
              by auto
            with nodes_notin_nl_neq_nln lno_notin_nl hno_notin_nl lno_nNull 
              hno_nNull repa_repb_nc 
            show " repNodes_eq x no low high repa = repNodes_eq x no low high repb"
              by (simp add: repNodes_eq_def null_comp_def)
          qed
          then have " [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repa] = 
            [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]"
            apply -
            apply (rule P_eq_list_filter)
            apply auto
            done
          with repb_no_hd_term_repa show ?thesis
            by simp
        qed
      next 
        assume no_nln: "no = node"
        with repb_node have repb_no_def: "repb no = 
          hd [sn\<leftarrow>(prx @ node # sfx). repNodes_eq sn node low high repa]" 
          by simp
        show ?thesis
        proof (cases "isLeaf_pt no low high")
          case True
          note isLeaf_no=this
          have "\<forall>x \<in> set (prx @ node # sfx). repNodes_eq x no low high repb 
            = repNodes_eq x no low high repa"
          proof (rule ballI)
            fix x
            assume x_in_nodeslist: "x \<in> set (prx @ node # sfx)"
            have all_nodes_in_nl_Leafs: 
              "\<forall>x \<in> set (prx @ node # sfx). isLeaf_pt x low high"
            proof (intro ballI)
              fix x
              assume x_in_nodeslist: " x \<in> set (prx @ node # sfx)"
              from isLeaf_no isLeaf_var_no have "var no \<le> 1"
                by simp
              with all_nodes_same_var [rule_format, OF x_in_nodeslist no_in_nl]
              have "var x \<le> 1"
                by simp
              with nodes_balanced_ordered [rule_format, OF x_in_nodeslist]
              show "isLeaf_pt x low high"
                by (auto simp add: isLeaf_pt_def)
            qed
            with x_in_nodeslist have "isLeaf_pt x low high"
              by auto
            with isLeaf_no repa_repb_nc 
            show "repNodes_eq x no low high repb = repNodes_eq x no low high repa"
              by (simp add: repNodes_eq_def null_comp_def isLeaf_pt_def)
          qed
          with repb_no_def no_nln have repb_no_whole_nl: "repb no = 
            hd [sn\<leftarrow> (prx @ node # sfx). repNodes_eq sn node low high repb]"
            apply -
            apply (subgoal_tac 
              "[sn\<leftarrow> (prx@node#sfx). repNodes_eq sn node low high repa] 
              = [sn\<leftarrow>(prx @ node # sfx) . repNodes_eq sn node low high repb]")
            apply simp
            apply (rule P_eq_list_filter)
            apply auto
            done
          from no_in_take_Sucn no_nln 
          have "[sn\<leftarrow> (prx@[node]). repNodes_eq sn node low high repb]  \<noteq> []"
            apply -
            apply (rule filter_not_empty)
            apply (auto simp add: repNodes_eq_def)
            done
          then
          have "hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn node low high repb] = 
                hd [sn\<leftarrow>(prx @ node # sfx). repNodes_eq sn node low high repb]"
            apply -
            apply (rule hd_filter_app [symmetric])
            apply auto
            done
          with repb_no_whole_nl no_nln show ?thesis
            by simp         
        next
          assume no_nLeaf: " \<not> isLeaf_pt no low high"
          with share_or balanced_no have "(repb \<propto> low) no \<noteq> (repb \<propto> high) no"
            using [[simp_depth_limit=2]]
            by (simp add: isLeaf_pt_def)
          from no_nLeaf share_cond no_nln have "repa (low no) \<noteq> repa (high no)"
            by auto
          with no_nLeaf balanced_no have "(repa \<propto> low) no \<noteq> (repa \<propto> high) no "
            by (simp add: null_comp_def isLeaf_pt_def)
          have "\<forall> x \<in> set (prx@node#sfx). repNodes_eq x no low high repb 
            = repNodes_eq x no low high repa"
          proof (rule ballI)
            fix x
            assume x_in_nodeslist: " x \<in> set (prx@node#sfx)"
            have all_nodes_in_nl_Leafs: 
              "\<forall>x \<in> set (prx@node#sfx). \<not> isLeaf_pt x low high"
            proof (intro ballI)
              fix x
              assume x_in_nodeslist: " x \<in> set (prx@node#sfx)"
              from no_nLeaf isLeaf_var_no have "1 < var no "
                by simp
              with all_nodes_same_var [rule_format, OF x_in_nodeslist no_in_nl]
              have "1 < var x" 
                by auto
              with nodes_balanced_ordered [rule_format, OF x_in_nodeslist]
              show "\<not> isLeaf_pt x low high"
                apply (unfold isLeaf_pt_def)
                apply fastforce
                done
            qed
            with x_in_nodeslist have x_nLeaf: "\<not> isLeaf_pt x low high"
              by auto
            from nodes_balanced_ordered [rule_format, OF x_in_nodeslist]
            have "(low x = Null) = (high x = Null) 
                  \<and> low x \<notin> set (prx@node#sfx) \<and> high x \<notin> set (prx@node#sfx)"
              by auto
            with x_nLeaf balanced_no no_nLeaf repa_repb_nc 
              nodes_notin_nl_neq_nln lno_notin_nl hno_notin_nl
            show "repNodes_eq x no low high repb = repNodes_eq x no low high repa"
              using [[simp_depth_limit=2]]
              by (simp add: repNodes_eq_def null_comp_def isLeaf_pt_def)
          qed
          with repb_no_def no_nln 
          have repb_no_whole_nl: 
            "repb no = hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn node low high repb]"
            apply -
            apply (subgoal_tac 
                  "[sn\<leftarrow>(prx@node#sfx). repNodes_eq sn node low high repa] 
                  = [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn node low high repb]")
            apply simp
            apply (rule P_eq_list_filter)
            apply auto
            done
          from no_in_take_Sucn no_nln 
          have "[sn\<leftarrow>(prx@[node]) . repNodes_eq sn node low high repb]  \<noteq> []"
            apply -
            apply (rule filter_not_empty)
            apply (auto simp add: repNodes_eq_def)
            done
          then have 
            "hd [sn\<leftarrow> (prx@[node]) . repNodes_eq sn node low high repb] = 
            hd [sn\<leftarrow>(prx@node#sfx) . repNodes_eq sn node low high repb]"
            apply -
            apply (rule hd_filter_app [symmetric])
            apply auto
            done
          with repb_no_whole_nl no_nln show ?thesis
            by simp        
        qed
      qed
    qed
    have repb_no_red_def: "(\<forall>no\<in>set (prx@[node]).(repb \<propto> low) no = (repb \<propto> high) no 
      \<and> low no \<noteq> Null \<longrightarrow>  repb no = (repb \<propto> low) no)" 
    proof (intro ballI impI)
      fix no
      assume no_in_take_Sucn: "no \<in> set (prx@[node])"
      assume red_cond_no: " (repb \<propto> low) no = (repb \<propto> high) no \<and> low no \<noteq> Null"
      from no_in_take_Sucn have no_in_nl: "no \<in> set (prx@node#sfx)"
        by auto
      from nodes_balanced_ordered [rule_format, OF this]obtain
        no_nNull: "no \<noteq> Null" and
        balanced_no: "(low no = Null) = (high no = Null)" and
        lno_notin_nl: "low no \<notin> set (prx@node#sfx)" and
        hno_notin_nl: "high no \<notin> set (prx@node#sfx)" and
        isLeaf_var_no: "isLeaf_pt no low high = (var no \<le> 1)"
        by auto
      have nodes_notin_nl_neq_nln: "\<forall> p. p \<notin> set (prx@node#sfx) \<longrightarrow> p \<noteq> node"
        by auto
      show " repb no = (repb \<propto> low) no"
      proof (cases "no = node")
        case False
        note no_notin_nl=this
        with no_in_take_Sucn have no_in_take_n: "no \<in> set prx"
          by auto
        from False repa_repb_nc have repb_repa_no: "repb no = repa no" 
          by auto
        with while_inv [rule_format, OF no_in_take_n] obtain 
          repa_no_nNull: "repa no \<noteq> Null" and
          while_share_red_exp: 
          "(if (repa \<propto> low) no = (repa \<propto> high) no \<and> low no \<noteq> Null 
          then repa no = (repa \<propto> low) no
          else repa no = hd [sn\<leftarrow>prx. repNodes_eq sn no low high repa] \<and>
          repa (repa no) = repa no \<and> 
          (\<forall>no1\<in>set prx. ((repa \<propto> high) no1 = (repa \<propto> high) no \<and> 
          (repa \<propto> low) no1 = (repa \<propto> low) no) = (repa no = repa no1)))"
          using [[simp_depth_limit=2]]
          by auto
        from red_cond_no nodes_notin_nl_neq_nln lno_notin_nl 
          hno_notin_nl while_share_red_exp balanced_no repa_repb_nc 
        have red_repa_no: "repa no = (repa \<propto> low) no"
          by (auto simp add: null_comp_def)
        from red_cond_no nodes_notin_nl_neq_nln lno_notin_nl repa_repb_nc 
        have "(repb \<propto> low) no =  (repa \<propto> low) no"
          by (auto simp add: null_comp_def)
        with red_repa_no no_notin_nl balanced_no repa_repb_nc 
        have "repb no = (repb \<propto> low) no"
          by auto
        with red_cond_no show ?thesis
          by auto
      next
        assume "no = node"
        with share_cond 
        have share_cond_pre: 
          "isLeaf_pt no low high \<or> repa (low no) \<noteq> repa (high no)" 
          by simp
        show ?thesis
        proof (cases "isLeaf_pt no low high")
          case True
          with red_cond_no show ?thesis
            by (simp add: isLeaf_pt_def)
        next
          assume no_nLeaf: "\<not> isLeaf_pt no low high"
          with share_cond_pre 
          have "repa (low no) \<noteq> repa (high no)"
            by simp
          with no_nLeaf lno_notin_nl hno_notin_nl nodes_notin_nl_neq_nln 
            balanced_no repa_repb_nc
          have "repb (low no) \<noteq> repb (high no)"
            using [[simp_depth_limit=2]]
            by (auto simp add: isLeaf_pt_def)
          with no_nLeaf balanced_no have "(repb \<propto> low) no \<noteq> (repb \<propto> high) no"
            by (simp add: null_comp_def isLeaf_pt_def)
          with red_cond_no show ?thesis
            by simp
        qed
      qed
    qed
    have while_while: "(\<forall>no\<in>set (prx@[node]).
          repb no \<noteq> Null \<and>
          (if (repb \<propto> low) no = (repb \<propto> high) no \<and> low no \<noteq> Null 
          then repb no = (repb \<propto> low) no
          else repb no = hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb] \<and>
          repb (repb no) = repb no \<and>
          (\<forall>no1\<in>set ((prx@[node])). ((repb \<propto> high) no1 = (repb \<propto> high) no 
          \<and> (repb \<propto> low) no1 = (repb \<propto> low) no) = (repb no = repb no1))))"
      (is "\<forall>no\<in>set (prx@[node]). ?P no \<and> ?Q no")
    proof (intro ballI)
      fix no
      assume no_in_take_Sucn: "no \<in> set (prx@[node])"
      hence no_in_nl: "no \<in> set (prx@node#sfx)"
        by auto
      from nodes_balanced_ordered [rule_format, OF this] obtain
        no_nNull: "no \<noteq> Null" and
        balanced_no: "(low no = Null) = (high no = Null)" and
        lno_notin_nl: "low no \<notin> set (prx@node#sfx)" and
        hno_notin_nl: "high no \<notin> set (prx@node#sfx)" and
        isLeaf_var_no: "isLeaf_pt no low high = (var no \<le> 1)"
        by auto
      from no_in_take_Sucn 
      have filter_take_Sucn_not_empty: 
            "[sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb] \<noteq> []"
        apply -
        apply (rule filter_not_empty)
        apply (auto simp add: repNodes_eq_def)
        done
      then have hd_filter_Sucn_in_Sucn: 
            "hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb] \<in> 
            set (prx@[node])"
        by (rule hd_filter_in_list)
      have nodes_notin_nl_neq_nln: "\<forall>p. p \<notin> set (prx@node#sfx) \<longrightarrow> p \<noteq> node"
        by auto
      show "?P no \<and> ?Q no"
      proof (cases "no = node")
        case False
        note no_notin_nl=this
        with no_in_take_Sucn 
        have no_in_take_n: "no \<in> set prx"
          by auto
        from False repa_repb_nc have repb_repa_no: "repb no = repa no" 
          by auto
        with while_inv [rule_format, OF no_in_take_n] obtain 
          repa_no_nNull: "repa no \<noteq> Null" and
          while_share_red_exp: 
          "(if (repa \<propto> low) no = (repa \<propto> high) no \<and> low no \<noteq> Null 
              then repa no = (repa \<propto> low) no
              else repa no = hd [sn\<leftarrow>prx. repNodes_eq sn no low high repa] \<and>
              repa (repa no) = repa no \<and> 
              (\<forall>no1\<in>set prx. ((repa \<propto> high) no1 = (repa \<propto> high) no \<and> 
              (repa \<propto> low) no1 = (repa \<propto> low) no) = (repa no = repa no1)))"
          using [[simp_depth_limit=2]]
          by auto
        from repb_repa_no repa_no_nNull have repb_no_nNull: "?P no"
          by simp
        have "?Q no"
        proof (cases "(repb \<propto> low) no = (repb \<propto> high) no \<and> low no \<noteq> Null")
          case True
          with no_in_take_Sucn repb_no_red_def show ?thesis
            by auto
        next
          assume share_case_repb: 
            " \<not> ((repb \<propto> low) no = (repb \<propto> high) no \<and> low no \<noteq> Null)"
          with repb_no_share_def no_in_take_Sucn 
          have repb_no_def: "repb no = hd [sn\<leftarrow> (prx@[node]). 
            repNodes_eq sn no low high repb]"
            by auto
          with share_case_repb 
          have "(repb \<propto> low) no \<noteq> (repb \<propto> high) no \<or> low no = Null"
            using [[simp_depth_limit=2]]
            by simp
          thus ?thesis
          proof (cases "low no = Null")
            case True
            note lno_Null=this
            with balanced_no have hno_Null: "high no = Null" 
              by simp
            from lno_Null hno_Null have isLeaf_no: "isLeaf_pt no low high"
              by (simp add: isLeaf_pt_def)
            from True while_share_red_exp 
            have while_low_Null: 
              "repa no = hd [sn\<leftarrow>prx. repNodes_eq sn no low high repa] \<and>
                  repa (repa no) = repa no \<and> 
                  (\<forall>no1\<in>set prx. ((repa \<propto> high) no1 = (repa \<propto> high) no 
              \<and> (repa \<propto> low) no1 = (repa \<propto> low) no) = (repa no = repa no1))"
              by auto
            from no_in_take_n 
            have "[sn\<leftarrow>prx. repNodes_eq sn no low high repa] \<noteq> []"
              apply -
              apply (rule filter_not_empty)
              apply (auto simp add: repNodes_eq_def)
              done
            then have hd_term_n_Sucn: "hd [sn\<leftarrow>prx. repNodes_eq sn no low high repa] = 
                  hd [sn\<leftarrow>(prx@[node]) . repNodes_eq sn no low high repa]"
              apply -
              apply (rule hd_filter_app [symmetric])
              apply auto
              done
            have all_nodes_in_nl_Leafs: 
              "\<forall>x \<in> set (prx@node#sfx). isLeaf_pt x low high"
            proof (intro ballI)
              fix x
              assume x_in_nodeslist: " x \<in> set (prx@node#sfx)"
              from isLeaf_no isLeaf_var_no have "var no \<le> 1"
                by simp
              with all_nodes_same_var [rule_format, OF x_in_nodeslist no_in_nl] 
              have "var x \<le> 1" 
                by simp
              with nodes_balanced_ordered [rule_format, OF x_in_nodeslist]
              show "isLeaf_pt x low high"
                by (auto simp add: isLeaf_pt_def)
            qed
            from no_in_take_Sucn have 
              filter_Sucn_no_notempty: 
              "[sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb] \<noteq> []"
              apply -
              apply (rule filter_not_empty)
              apply (auto simp add: repNodes_eq_def)
              done
            then have hd_term_in_take_Sucn: 
              "hd [sn\<leftarrow>(prx@[node]) . repNodes_eq sn no low high repb] 
                  \<in> set (prx@[node])"
              by (rule hd_filter_in_list)
            then have hd_term_in_nl: 
              "hd [sn\<leftarrow>(prx@[node]) . repNodes_eq sn no low high repb] 
              \<in> set (prx@node#sfx)"
              by auto 
            with all_nodes_in_nl_Leafs 
            have hd_term_Leaf: "isLeaf_pt (hd [sn\<leftarrow> (prx@[node]). 
              repNodes_eq sn no low high repb]) low high "
              by auto            
            from while_low_Null have "repa (repa no) = repa no"
              by auto
            with no_notin_nl repa_repb_nc 
            have repa_repb_no_repb: "repa (repb no) = repb no"
              by auto
            have repb_repb_no: "repb (repb no) = repb no" 
            proof (cases "repb no = node")
              case False
              with repa_repb_nc repa_repb_no_repb show ?thesis
                by auto
            next
              assume repb_no_nln: " repb no = node"
              with hd_term_Leaf isLeaf_no all_nodes_in_nl_Leafs  
              have nested_hd_repa_repb: 
                "hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn 
                   (hd [sn\<leftarrow>(prx@[node]) . repNodes_eq sn no low high repb]) 
                        low high repa] =  
                 hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn 
                    ( hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]) 
                        low high repb]"
                by (simp add: isLeaf_pt_def repNodes_eq_def null_comp_def)
              from  hd_term_in_take_Sucn 
              have "[sn\<leftarrow>(prx@[node]). repNodes_eq sn 
                      (hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]) 
                       low high repb] \<noteq> []"
                apply -
                apply (rule filter_not_empty)
                apply (auto simp add: repNodes_eq_def)
                done
              then have "hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn 
                    ( hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]) 
                          low high repb] = 
                    hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn 
                    ( hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]) 
                           low high repb]"
                apply -
                apply (rule hd_filter_app [symmetric])
                apply auto
                done
              then have hd_term_nodeslist_Sucn: 
                "hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn 
                    ( hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]) 
                             low high repb] =
                    hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn 
                    ( hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]) 
                          low high repb]"
                by simp
              from no_in_take_Sucn filter_Sucn_no_notempty 
              have filter_filter: "hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn  
                    (hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]) 
                          low high repb] =  
                    hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]"
                apply -
                apply (rule filter_hd_P_rep_indep)
                apply (auto simp add: repNodes_eq_def)
                done
              from repb_no_def repb_no_nln repb_node 
              have "repb (repb no) =  hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn 
                    ( hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]) 
                           low high repa]"
                by simp
              with nested_hd_repa_repb 
              have "repb (repb no) =  hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn 
                    (hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]) 
                        low high repb]"
                by simp
              with hd_term_nodeslist_Sucn 
              have "repb (repb no) =  hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn 
                    ( hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]) 
                         low high repb]"
                by simp
              with filter_filter 
              have "repb (repb no) = hd [sn\<leftarrow>(prx@[node]). 
                repNodes_eq sn no low high repb]"
                by simp
              with repb_no_def show ?thesis
                by simp
            qed
            have two_nodes_repb: "(\<forall>no1\<in>set (prx@[node]). 
                  ((repb \<propto> high) no1 = (repb \<propto> high) no 
                  \<and> (repb \<propto> low) no1 = (repb \<propto> low) no) = (repb no = repb no1))"
            proof (intro ballI)
              fix no1
              assume no1_in_take_Sucn: " no1 \<in> set (prx@[node])"
              then have "no1 \<in> set (prx@node#sfx)" by auto
              with all_nodes_in_nl_Leafs 
              have isLeaf_no1: "isLeaf_pt no1 low high"
                by auto
              with isLeaf_no 
              have repbchildren_eq_no_no1: "(repb \<propto> high) no1 = (repb \<propto> high) no 
                \<and> (repb \<propto> low) no1 = (repb \<propto> low) no"
                by (simp add: null_comp_def isLeaf_pt_def)
              from isLeaf_no1 isLeaf_no 
              have repachildren_eq_no_no1: "(repa \<propto> high) no1 = (repa \<propto> high) no 
                \<and> (repa \<propto> low) no1 = (repa \<propto> low) no"
                by (simp add: null_comp_def isLeaf_pt_def)
              from while_low_Null 
              have while_low_same_rep: "(\<forall>no1\<in>set prx. 
                ((repa \<propto> high) no1 = (repa \<propto> high) no 
                    \<and> (repa \<propto> low) no1 = (repa \<propto> low) no) = (repa no = repa no1))"
                by auto
              show "((repb \<propto> high) no1 = (repb \<propto> high) no \<and> 
                    (repb \<propto> low) no1 = (repb \<propto> low) no) = (repb no = repb no1)"
              proof (cases "no1 = node")
                case False
                with no1_in_take_Sucn have "no1 \<in> set prx"
                  by auto
                with while_low_same_rep repachildren_eq_no_no1 
                have "repa no = repa no1"
                  by auto
                with repa_repb_nc no_notin_nl False repbchildren_eq_no_no1 
                show ?thesis 
                  by auto
              next
                assume no1_nln: "no1 = node"
                hence no1_in_take_Sucn: "no1 \<in> set (prx@[node])"
                  by auto
                hence no1_in_nl: "no1 \<in> set (prx@node#sfx)"
                  by auto
                from nodes_balanced_ordered [rule_format, OF this] have 
                  balanced_no1: "(low no1 = Null) = (high no1 = Null)"
                  by auto
                with no1_in_take_Sucn repb_no_share_def isLeaf_no1 
                have repb_no1: "repb no1 = hd [sn\<leftarrow>(prx@[node]). 
                  repNodes_eq sn no1 low high repb]"
                  by (auto simp add: isLeaf_pt_def)
                from balanced_no1 isLeaf_no1 isLeaf_no balanced_no 
                have repbchildren_eq_no1_no: "(repb \<propto> high) no1 = (repb \<propto> high) no 
                      \<and> (repb \<propto> low) no1 = (repb \<propto> low) no"
                  by (simp add: null_comp_def isLeaf_pt_def)
                have "\<forall> x \<in> set (prx@[node]).  repNodes_eq x no low high repb 
                  =  repNodes_eq x no1 low high repb"
                proof (intro ballI)
                  fix x
                  assume x_in_take_Sucn: " x \<in> set (prx@[node])"
                  with repbchildren_eq_no1_no show "repNodes_eq x no low high repb 
                    = repNodes_eq x no1 low high repb"
                    by (simp add: repNodes_eq_def)
                qed
                then have " [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb] 
                      = [sn\<leftarrow>(prx@[node]). repNodes_eq sn no1 low high repb]"
                  by (rule P_eq_list_filter)
                with repb_no_def repb_no1 have repb_no_no1: "repb no = repb no1"
                  by simp
                with repbchildren_eq_no1_no show ?thesis
                  by simp
              qed
            qed
            with repb_repb_no repb_no_share_def no_in_take_Sucn share_case_repb 
            show ?thesis
              using [[simp_depth_limit=4]]
              by auto
          next
            assume lno_nNull: "low no \<noteq> Null"
            with share_case_repb 
            have repbchildren_neq_no: "(repb \<propto> low) no \<noteq> (repb \<propto> high) no"
              by auto
            from balanced_no lno_nNull 
            have hno_nNull: "high no \<noteq> Null"
              by simp
            with repbchildren_neq_no lno_nNull repa_repb_nc 
              lno_notin_nl hno_notin_nl nodes_notin_nl_neq_nln 
            have repachildren_neq_no: "(repa \<propto> low) no \<noteq> (repa \<propto> high) no"
              using [[simp_depth_limit=2]]
              by (auto simp add: null_comp_def)
            with while_share_red_exp 
            have repa_while_inv: "repa (repa no) = repa no 
              \<and> (\<forall>no1\<in>set prx. ((repa \<propto> high) no1 = (repa \<propto> high) no 
              \<and> (repa \<propto> low) no1 = (repa \<propto> low) no) = (repa no = repa no1))"
              by auto
            from lno_nNull hno_nNull 
            have no_nLeaf: "\<not> isLeaf_pt no low high"
              by (simp add: isLeaf_pt_def)
            have all_nodes_in_nl_nLeafs: 
              "\<forall>x \<in> set (prx@node#sfx). \<not> isLeaf_pt x low high"
            proof (intro ballI)
              fix x
              assume x_in_nodeslist: " x \<in> set (prx@node#sfx)"
              from no_nLeaf isLeaf_var_no have "1 < var no "
                by simp
              with all_nodes_same_var [rule_format, OF x_in_nodeslist no_in_nl] 
              have "1 < var x"
                by simp
              with nodes_balanced_ordered [rule_format, OF x_in_nodeslist]
              show " \<not> isLeaf_pt x low high"
                using [[simp_depth_limit = 2]]
                by (auto simp add: isLeaf_pt_def)
            qed
            have repb_repb_no: "repb (repb no) = repb no"
            proof -
              from repa_while_inv no_notin_nl repa_repb_nc 
              have "repa (repb no) = repb no"
                by simp
              from hd_filter_Sucn_in_Sucn repb_no_def 
              have repb_no_in_take_Sucn: "repb no \<in> set (prx@[node])"
                by simp
              hence repb_no_in_nl: "repb no \<in> set (prx@node#sfx)"
                by auto
              from all_nodes_in_nl_nLeafs repb_no_in_nl 
              have repb_no_nLeaf: "\<not> isLeaf_pt (repb no) low high"
                by auto
              from nodes_balanced_ordered [rule_format, OF repb_no_in_nl]
              have "(low (repb no) = Null) = (high (repb no) = Null) 
                \<and> low (repb no) \<notin> set (prx@node#sfx) \<and> 
                high (repb no) \<notin> set (prx@node#sfx)"
                by auto
              from filter_take_Sucn_not_empty 
              have " repNodes_eq (hd [sn\<leftarrow>(prx@[node]). 
                repNodes_eq sn no low high repb]) no low high repb"
                by (rule hd_filter_prop)
              with repb_no_def have "repNodes_eq (repb no) no low high repb"
                by simp
              then have "(repb \<propto> low) (repb no) = (repb \<propto> low) no 
                \<and> (repb \<propto> high) (repb no) = (repb \<propto> high) no"
                by (simp add: repNodes_eq_def)
              with repbchildren_neq_no have "(repb \<propto> low) (repb no) 
                \<noteq> (repb \<propto> high) (repb no)"
                by simp
              with repb_no_in_take_Sucn repb_no_share_def 
              have repb_repb_no_double_hd: 
                "repb (repb no) = hd [sn\<leftarrow>(prx@[node]). 
                repNodes_eq sn (repb no) low high repb]"
                by auto
              from filter_take_Sucn_not_empty 
              have " hd [sn\<leftarrow>(prx@[node]). 
                repNodes_eq sn (repb no) low high repb] = repb no"
                apply (simp only: repb_no_def )
                apply (rule filter_hd_P_rep_indep)
                apply (auto simp add: repNodes_eq_def)
                done
              with repb_repb_no_double_hd show ?thesis
                by simp
            qed
            have "(\<forall>no1\<in>set (prx@[node]). 
                ((repb \<propto> high) no1 = (repb \<propto> high) no \<and> 
                (repb \<propto> low) no1 = (repb \<propto> low) no) = (repb no = repb no1))"
            proof (intro ballI)
              fix no1
              assume no1_in_take_Sucn: "no1 \<in> set (prx@[node])"
              hence no1_in_nl: "no1 \<in> set (prx@node#sfx)"
                by auto
              from all_nodes_in_nl_nLeafs no1_in_nl 
              have no1_nLeaf: "\<not> isLeaf_pt no1 low high"
                by auto
              from nodes_balanced_ordered [rule_format, OF no1_in_nl]
              have no1_props: "(low no1 = Null) = (high no1 = Null) 
                \<and> low no1 \<notin> set (prx@node#sfx) \<and> high no1 \<notin> set (prx@node#sfx)"
                by auto
              show "((repb \<propto> high) no1 = (repb \<propto> high) no 
                \<and> (repb \<propto> low) no1 = (repb \<propto> low) no) = (repb no = repb no1)"
              proof (cases "no1 = node")
                case False
                note no1_neq_nln=this
                with no1_in_take_Sucn 
                have no1_in_take_n: "no1 \<in> set prx"
                  by auto
                with repa_while_inv have "((repa \<propto> high) no1 = (repa \<propto> high) no 
                  \<and> (repa \<propto> low) no1 = (repa \<propto> low) no) = (repa no = repa no1)"
                  by fastforce
                with no1_props no1_nLeaf no_nLeaf balanced_no lno_notin_nl 
                  hno_notin_nl nodes_notin_nl_neq_nln no_notin_nl 
                  no1_neq_nln repa_repb_nc
                show ?thesis
                  using [[simp_depth_limit=1]]
                  by (auto simp add: null_comp_def isLeaf_pt_def)
              next
                assume no1_nln: " no1 = node"
                show ?thesis
                proof
                  assume repbchildren_eq_no1_no: 
                    "(repb \<propto> high) no1 = (repb \<propto> high) no 
                    \<and> (repb \<propto> low) no1 = (repb \<propto> low) no"
                  with repbchildren_neq_no 
                  have "(repb \<propto> high) no1 \<noteq> (repb \<propto> low) no1"
                    by auto
                  with repb_no_share_def no1_in_take_Sucn 
                  have repb_no1_def: " repb no1 = hd [sn\<leftarrow>(prx@[node]). 
                    repNodes_eq sn no1 low high repb]"
                    by auto
                  have filter_no1_eq_filter_no: "[sn\<leftarrow>(prx@[node]). 
                    repNodes_eq sn no1 low high repb] =  
                    [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]"
                  proof -
                    have "\<forall>x \<in> set (prx@[node]). 
                      repNodes_eq x no1 low high repb = 
                      repNodes_eq x no low high repb"
                    proof (intro ballI)
                      fix x
                      assume x_in_take_Sucn: "x \<in> set (prx@[node])"
                      with repbchildren_eq_no1_no 
                      show "repNodes_eq x no1 low high repb = 
                        repNodes_eq x no low high repb"
                        by (simp add: repNodes_eq_def)
                    qed
                    then show ?thesis
                      by (rule P_eq_list_filter)
                  qed
                  with repb_no1_def repb_no_def show " repb no = repb no1"
                    by simp
                next
                  assume repb_no_no1_eq: "repb no = repb no1"
                  from no1_nln repb_node repb_no_def have repb_no1_def: 
                    "repb no1 =  
                    hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn node low high repa]"
                    by auto
                  with no1_nln repb_no_def repb_no_no1_eq 
                  have repb_Sucn_repa_nl_hd: " hd [sn\<leftarrow>(prx@[node]). 
                    repNodes_eq sn no low high repb] = 
                    hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn no1 low high repa]"
                    by simp
                  from filter_take_Sucn_not_empty 
                  have " hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb] 
                    =  hd [sn\<leftarrow>(prx@node#sfx) . repNodes_eq sn no low high repb]"
                    apply -
                    apply (rule hd_filter_app [symmetric])
                    apply auto
                    done
                  then have hd_Sucn_hd_whole_list: 
                    "hd [sn\<leftarrow>(prx@[node]) . 
                    repNodes_eq sn no low high repb] =  
                    hd [sn\<leftarrow> (prx@node#sfx). repNodes_eq sn no low high repb]"
                    by simp
                  have hd_nl_repb_repa: 
                    "[sn\<leftarrow> (prx@node#sfx). repNodes_eq sn no low high repb] 
                    = [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn no low high repa]"
                  proof -
                    have "\<forall>x \<in> set (prx@node#sfx).  
                      repNodes_eq x no low high repb =  
                      repNodes_eq x no low high repa"
                    proof (intro ballI)
                      fix x
                      assume x_in_nl: "x \<in> set (prx@node#sfx)"
                      from all_nodes_in_nl_nLeafs x_in_nl 
                      have x_nLeaf: "\<not> isLeaf_pt x low high"
                        by auto
                      from  nodes_balanced_ordered [rule_format, OF x_in_nl]
                      have x_props: "(low x = Null) = (high x = Null) \<and> 
                        low x \<notin> set (prx@node#sfx) \<and> high x \<notin> set (prx@node#sfx)"
                        by auto
                      with x_nLeaf lno_nNull hno_nNull lno_notin_nl hno_notin_nl 
                        nodes_notin_nl_neq_nln repa_repb_nc 
                      show "repNodes_eq x no low high repb = 
                        repNodes_eq x no low high repa"
                        using [[simp_depth_limit=1]]
                        by (simp add: repNodes_eq_def isLeaf_pt_def null_comp_def)
                    qed
                    then show ?thesis
                      by (rule P_eq_list_filter)
                  qed
                  with repb_Sucn_repa_nl_hd hd_Sucn_hd_whole_list 
                  have filter_nl_no_no1: 
                    "hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn no low high repa] 
                    =  hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn no1 low high repa]"
                    by simp
                  from no_in_nl have filter_no_not_empty: 
                    "[sn\<leftarrow>(prx@node#sfx). repNodes_eq sn no low high repa] \<noteq> []"
                    apply -
                    apply (rule filter_not_empty)
                    apply (auto simp add: repNodes_eq_def)
                    done
                  from no1_in_nl have filter_no1_not_empty: 
                    "[sn\<leftarrow>(prx@node#sfx). repNodes_eq sn no1 low high repa] \<noteq> []"
                    apply -
                    apply (rule filter_not_empty)
                    apply (auto simp add: repNodes_eq_def)
                    done
                  from repb_no_def hd_Sucn_hd_whole_list hd_nl_repb_repa 
                  have "repb no =
                    hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn no low high repa]" 
                    by simp
                  with hd_filter_prop [OF filter_no_not_empty ]
                  have repNodes_no_repa: "repNodes_eq (repb no) no low high repa"
                    by auto
                  from repb_no1_def no1_nln 
                  have 
                    "repb no1 = hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn no1 
                    low high repa]"
                    by simp
                  with hd_filter_prop [OF filter_no1_not_empty ]
                  have "repNodes_eq (repb no1) no1 low high repa"
                    by auto
                  with filter_nl_no_no1 repNodes_no_repa repb_no_no1_eq 
                  have "(repa \<propto> high) no1 = 
                    (repa \<propto> high) no \<and> (repa \<propto> low) no1 = (repa \<propto> low) no"
                    by (simp add: repNodes_eq_def)
                  with hno_nNull no1_props no1_nLeaf lno_nNull lno_notin_nl 
                    hno_notin_nl nodes_notin_nl_neq_nln repa_repb_nc
                  show "(repb \<propto> high) no1 = 
                    (repb \<propto> high) no \<and> (repb \<propto> low) no1 = (repb \<propto> low) no"
                    using [[simp_depth_limit=1]]
                    by (auto simp add: isLeaf_pt_def null_comp_def)
                qed
              qed
            qed
            with repb_repb_no repb_no_share_def share_case_repb no_in_take_Sucn 
            show ?thesis
              using [[simp_depth_limit=1]]
              by auto
          qed
        qed
        with repb_no_nNull show ?thesis
          by simp
      next
        assume no_nln: "no = node"
        with repb_node have repb_no_def: 
          "repb no = hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn no low high repa]"
          by simp
        from no_nln have "no \<in> set (prx@node#sfx)"
          by auto
        then have filter_nl_repa_not_empty: 
          "[sn\<leftarrow>(prx@node#sfx). repNodes_eq sn no low high repa] \<noteq> []"
          apply -
          apply (rule filter_not_empty)
          apply (auto simp add: repNodes_eq_def)
          done
        then have hd_filter_nl_in_nl: 
          "hd [sn\<leftarrow>(prx@node#sfx). repNodes_eq sn no low high repa] \<in> set (prx@node#sfx)"
          by (rule hd_filter_in_list)
        with repb_no_def 
        have repb_no_in_nodeslist: "repb no \<in> set (prx@node#sfx)"
          by simp
        from nodes_balanced_ordered [rule_format,OF this]
        have repb_no_nNull: "repb no \<noteq> Null"
          by auto
        from share_cond no_nln have share_cond_or: 
          "isLeaf_pt no low high \<or> repa (low no) \<noteq> repa (high no)"
          by auto
        have share_reduce_if: " (if (repb \<propto> low) no = (repb \<propto> high) no \<and> low no \<noteq> Null 
              then repb no = (repb \<propto> low) no
              else repb no = hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb] \<and>
              repb (repb no) = repb no 
              \<and> (\<forall>no1\<in>set (prx@[node]). ((repb \<propto> high) no1 = (repb \<propto> high) no 
              \<and> (repb \<propto> low) no1 = (repb \<propto> low) no) = (repb no = repb no1)))"
        proof (cases "isLeaf_pt no low high")
          case True
          note isLeaf_no=this
          then have lno_Null: "low no = Null" by (simp add: isLeaf_pt_def)
          from isLeaf_no no_in_take_Sucn repb_no_share_def 
          have repb_no_repb_def: "repb no 
                = hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]"
            by (auto simp add: isLeaf_pt_def)
          from isLeaf_no nodes_balanced_ordered [rule_format, OF no_in_nl]
          have var_no: "var no \<le> 1" 
            by auto
          have all_nodes_nl_var_l_1: "\<forall>x \<in> set (prx@node#sfx). var x \<le> 1"
          proof (intro ballI)
            fix x
            assume x_in_nl: " x \<in> set (prx@node#sfx)"
            from all_nodes_same_var [rule_format, OF x_in_nl no_in_nl] var_no 
            show " var x \<le> 1"
              by auto
          qed              
          have all_nodes_nl_Leafs: "\<forall>x \<in> set (prx@node#sfx). isLeaf_pt x low high" 
          proof (intro ballI)
            fix x
            assume x_in_nl: " x \<in> set (prx@node#sfx)"
            with all_nodes_nl_var_l_1 have "var x \<le> 1"
              by auto
            with nodes_balanced_ordered [rule_format, OF x_in_nl ]
            show "isLeaf_pt x low high"
              by auto
          qed 
          have repb_repb_no: "repb (repb no) = repb no"
          proof -
            from repb_no_share_def no_in_take_Sucn lno_Null 
            have repb_no_def: " repb no = 
              hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]"
              by auto
            with hd_filter_Sucn_in_Sucn 
            have repb_no_in_take_Sucn: "repb no \<in> set (prx@[node])"
              by simp
            hence repb_no_in_nl: "repb no \<in> set (prx@[node])"
              by auto
            with all_nodes_nl_Leafs 
            have repb_no_Leaf: "isLeaf_pt (repb no) low high" 
              by auto
            with repb_no_in_take_Sucn repb_no_share_def 
            have repb_repb_no_def: "repb (repb no) = 
              hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn (repb no) low high repb] "
              by (auto simp add: isLeaf_pt_def)
            from filter_take_Sucn_not_empty 
            show ?thesis
              apply (simp only: repb_repb_no_def  )
              apply (simp only: repb_no_def)
              apply (rule filter_hd_P_rep_indep)
              apply (auto simp add: repNodes_eq_def)
              done
          qed
          have two_nodes_repb: "(\<forall>no1\<in>set (prx@[node]). 
                ((repb \<propto> high) no1 = (repb \<propto> high) no \<and> 
                (repb \<propto> low) no1 = (repb \<propto> low) no) = (repb no = repb no1))"
          proof (intro ballI)
            fix no1 
            assume no1_in_take_Sucn: "no1 \<in> set (prx@[node])"
            from no1_in_take_Sucn 
            have "no1 \<in> set (prx@node#sfx)"
              by auto
            with all_nodes_nl_Leafs 
            have isLeaf_no1: "isLeaf_pt no1 low high"
              by auto
            with repb_no_share_def no1_in_take_Sucn 
            have repb_no1_def: "repb no1 =  
                  hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no1 low high repb]" 
              by (auto simp add: isLeaf_pt_def)
            show "((repb \<propto> high) no1 = (repb \<propto> high) no 
                  \<and> (repb \<propto> low) no1 = (repb \<propto> low) no) = (repb no = repb no1)"
            proof 
              assume repbchildren_eq_no1_no: "(repb \<propto> high) no1 = (repb \<propto> high) no 
                    \<and> (repb \<propto> low) no1 = (repb \<propto> low) no"
              have "[sn\<leftarrow>(prx@[node]). repNodes_eq sn no1 low high repb] 
                    = [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]"
              proof -
                have "\<forall>x \<in> set (prx@[node]). 
                      repNodes_eq x no1 low high repb = repNodes_eq x no low high repb"
                proof (intro ballI)
                  fix x
                  assume x_in_take_Sucn: " x \<in> set (prx@[node])"
                  with repbchildren_eq_no1_no 
                  show " repNodes_eq x no1 low high repb = repNodes_eq x no low high repb"
                    by (simp add: repNodes_eq_def)
                qed
                then show ?thesis
                  by (rule P_eq_list_filter)
              qed
              with repb_no1_def repb_no_repb_def 
              show "repb no = repb no1"
                by simp
            next
              assume repb_no_no1: "repb no = repb no1"
              with isLeaf_no isLeaf_no1 
              show "(repb \<propto> high) no1 = (repb \<propto> high) no 
                \<and> (repb \<propto> low) no1 = (repb \<propto> low) no"
                by (simp add: null_comp_def isLeaf_pt_def)
            qed
          qed
          with repb_repb_no lno_Null no_in_take_Sucn repb_no_share_def show ?thesis
            by auto
        next
          assume no_nLeaf: "\<not> isLeaf_pt no low high"
          with balanced_no obtain 
            lno_nNull: "low no \<noteq> Null" and 
            hno_nNull: "high no \<noteq> Null"
            by (simp add: isLeaf_pt_def)
          from no_nLeaf nodes_balanced_ordered [rule_format, OF no_in_nl]
          have var_no: "1 < var no" 
            by auto
          have all_nodes_nl_var_l_1: "\<forall>x \<in> set (prx@node#sfx). 1 < var x"
          proof (intro ballI)
            fix x
            assume x_in_nl: " x \<in> set (prx@node#sfx)"
            with all_nodes_same_var [rule_format, OF x_in_nl no_in_nl] var_no 
            show "1 < var x"
              by simp
          qed         
          have all_nodes_nl_nLeafs: "\<forall> x \<in> set (prx@node#sfx). \<not> isLeaf_pt x low high" 
          proof (intro ballI)
            fix x
            assume x_in_nl: " x \<in> set (prx@node#sfx)"
            with all_nodes_nl_var_l_1 have "1 < var x"
              by auto
            with nodes_balanced_ordered [rule_format, OF x_in_nl] show " \<not> isLeaf_pt x low high"
              by auto
          qed 
          from no_nLeaf share_cond_or 
          have repachildren_neq_no: "repa (low no) \<noteq> repa (high no)"
            by auto
          with lno_nNull hno_nNull 
          have "(repa \<propto> low) no \<noteq> (repa \<propto> high) no"
            by (simp add: null_comp_def)
          with repa_repb_nc lno_notin_nl hno_notin_nl 
            nodes_notin_nl_neq_nln lno_nNull hno_nNull 
          have repbchildren_neq_no: "(repb \<propto> low) no \<noteq> (repb \<propto> high) no"
            using [[simp_depth_limit=1]]
            by (auto simp add: null_comp_def)
          have repb_repb_no: "repb (repb no) = repb no"
          proof -
            from repb_no_share_def no_in_take_Sucn repbchildren_neq_no 
            have repb_no_def: "repb no = 
              hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]"
              by auto
            from filter_take_Sucn_not_empty 
            have "repNodes_eq (repb no) no low high repb"
              apply (simp only: repb_no_def)
              apply (rule hd_filter_prop)
              apply simp
              done
            with repbchildren_neq_no 
            have repbchildren_neq_repb_no: "(repb \<propto> low) (repb no) \<noteq> (repb \<propto> high) (repb no)"
              by (simp add: repNodes_eq_def)
            from filter_take_Sucn_not_empty 
            have "repb no \<in> set (prx@[node])"
              apply (simp only: repb_no_def )
              apply (rule hd_filter_in_list)
              apply simp
              done
            with repbchildren_neq_repb_no repb_no_share_def 
            have repb_repb_no_def: " repb (repb no) = 
              hd [sn\<leftarrow>(prx@[node]) . repNodes_eq sn (repb no) low high repb] "
              by auto
            from filter_take_Sucn_not_empty show ?thesis
              apply (simp only: repb_repb_no_def )
              apply (simp only: repb_no_def)
              apply (rule filter_hd_P_rep_indep)
              apply (auto simp add: repNodes_eq_def)
              done
          qed
          have two_nodes_repb: "(\<forall>no1\<in>set (prx@[node]). 
            ((repb \<propto> high) no1 = (repb \<propto> high) no \<and> 
            (repb \<propto> low) no1 = (repb \<propto> low) no) = (repb no = repb no1))"
            (is "(\<forall>no1\<in>set (prx@[node]). ?P no1)")
          proof (intro ballI)
            fix no1
            assume no1_in_take_Sucn: " no1 \<in> set (prx@[node])"
            hence no1_in_nodeslist: "no1 \<in> set (prx@node#sfx)"
              by auto
            with all_nodes_nl_nLeafs 
            have no1_nLeaf: "\<not> isLeaf_pt no1 low high"
              by auto
            show "?P no1"
            proof
              assume repbchildren_eq_no1_no: "(repb \<propto> high) no1 = (repb \<propto> high) no 
                \<and> (repb \<propto> low) no1 = (repb \<propto> low) no"
              with repbchildren_neq_no have "(repb \<propto> high) no1 \<noteq> (repb \<propto> low) no1"
                by auto
              with no1_in_take_Sucn repb_no_share_def have repb_no1_def: "repb no1 = 
                hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no1 low high repb]"
                by auto
              from repb_no_share_def no_in_take_Sucn repbchildren_neq_no 
              have repb_no_def: "repb no = 
                hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]"
                by auto
              have "[sn\<leftarrow>(prx@[node]). repNodes_eq sn no1 low high repb] = 
                [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]"
              proof -
                have "\<forall> x \<in> set (prx@[node]). 
                  repNodes_eq x no1 low high repb = repNodes_eq x no low high repb"
                proof (intro ballI)
                  fix x
                  assume x_in_take_Sucn: " x \<in> set (prx@[node])"
                  with repbchildren_eq_no1_no 
                  show " repNodes_eq x no1 low high repb = repNodes_eq x no low high repb"
                    by (simp add: repNodes_eq_def)
                qed
                then show ?thesis
                  by (rule P_eq_list_filter)
              qed
              with repb_no_def repb_no1_def show " repb no = repb no1"
                by simp
            next
              assume repb_no_no1: "repb no = repb no1"
              from repb_no_share_def no_in_take_Sucn repbchildren_neq_no 
              have repb_no_def: "repb no = 
                hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no low high repb]"
                by auto
              from filter_take_Sucn_not_empty 
              have "repb no \<in> set (prx@[node])"
                apply (simp only: repb_no_def)
                apply (rule hd_filter_in_list)
                apply simp
                done
              then have repb_no_in_nl: "repb no \<in> set (prx@node#sfx)"
                by auto
              from filter_take_Sucn_not_empty 
              have repNodes_repb_no: "repNodes_eq (repb no) no low high repb"
                apply (simp only: repb_no_def)
                apply (rule hd_filter_prop)
                apply simp
                done
              show "(repb \<propto> high) no1 = (repb \<propto> high) no 
                \<and> (repb \<propto> low) no1 = (repb \<propto> low) no"
              proof (cases "(repb \<propto> low) no1 = (repb \<propto> high) no1")
                case True
                note red_cond=this
                from no1_in_nodeslist all_nodes_nl_nLeafs
                have no1_nLeaf: "\<not> isLeaf_pt no1 low high"
                  by auto
                from nodes_balanced_ordered [rule_format, OF no1_in_nodeslist]
                have no1_props: "(low no1 \<notin> set (prx@node#sfx)) 
                      \<and> (high no1 \<notin> set (prx@node#sfx)) \<and>(low no1 = Null) = (high no1 = Null) 
                      \<and> ((rep \<propto> low) no1 \<notin> set (prx@node#sfx))"
                  by auto
                with red_cond no1_nLeaf no1_in_take_Sucn repb_no_red_def 
                have repb_no1_def: "repb no1 = (repb \<propto> low) no1"
                  by (auto simp add: isLeaf_pt_def)
                with no1_nLeaf no1_props have "repb no1 = repb (low no1)"
                  by (simp add: null_comp_def isLeaf_pt_def)
                from no1_props no1_nLeaf have "rep (low no1) \<notin> set (prx@node#sfx)"
                  by (auto simp add: isLeaf_pt_def null_comp_def)
                with rep_repb_nc no1_props 
                have "repb (low no1) \<notin> set (prx@node#sfx)"
                  by auto
                with repb_no1_def repb_no_no1 no1_props no1_nLeaf 
                have "repb no \<notin> set (prx@node#sfx)"
                  by (simp add: isLeaf_pt_def null_comp_def)
                with repb_no_in_nl show ?thesis
                  by simp
              next
                assume "(repb \<propto> low) no1 \<noteq> (repb \<propto> high) no1"
                with repb_no_share_def no1_in_take_Sucn 
                have repb_no1_def: " repb no1 = 
                  hd [sn\<leftarrow>(prx@[node]). repNodes_eq sn no1 low high repb]"
                  by auto
                from no1_in_take_Sucn 
                have "[sn\<leftarrow>(prx@[node]). repNodes_eq sn no1 low high repb] \<noteq> []" 
                  apply -
                  apply (rule filter_not_empty)
                  apply (auto simp add: repNodes_eq_def)
                  done
                then 
                have repNodes_repb_no1: "repNodes_eq (repb no1) no1 low high repb"
                  apply (simp only: repb_no1_def ) 
                  apply (rule hd_filter_prop)
                  apply simp
                  done
                with repNodes_repb_no repb_no_no1 
                have "repNodes_eq no1 no low high repb"
                  by (simp add: repNodes_eq_def)
                then show ?thesis
                  by (simp add: repNodes_eq_def)
              qed
            qed
          qed
          with repb_repb_no repb_no_share_def no_in_take_Sucn repbchildren_neq_no
          show ?thesis
            using [[simp_depth_limit=2]]
            by fastforce
        qed
        with repb_no_nNull show ?thesis
          by simp
      qed
    qed
    with rep_repb_nc show ?thesis
      by (intro conjI)
  qed
qed

end




