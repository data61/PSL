(*  Title:       BDD
    Author:      Veronika Ortner and Norbert Schirmer, 2004
    Maintainer:  Norbert Schirmer,  norbert.schirmer at web de
    License:     LGPL
*)

(*  
NormalizeTotalProof.thy

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

section \<open>Proof of Procedure Normalize\<close>
theory NormalizeTotalProof imports LevellistProof ShareReduceRepListProof 
                        RepointProof begin

hide_const (open) DistinctTreeProver.set_of tree.Node tree.Tip

lemma  (in Normalize_impl) Normalize_modifies:
  shows
   "\<forall>\<sigma>. \<Gamma>\<turnstile>{\<sigma>} \<acute>p :== PROC Normalize (\<acute>p) 
     {t. t may_only_modify_globals \<sigma> in [rep,mark,low,high,next]}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done

lemma (in Normalize_impl) Normalize_spec: 
  shows "\<forall>\<sigma> pret prebdt. \<Gamma>\<turnstile>\<^sub>t
  \<lbrace>\<sigma>. Dag \<acute>p \<acute>low \<acute>high pret \<and> ordered pret \<acute>var \<and> 
   \<acute>p \<noteq> Null \<and> (\<forall>n. n \<in> set_of pret \<longrightarrow> \<acute>mark n = \<acute>mark \<acute>p) \<and> 
   bdt pret \<acute>var = Some prebdt\<rbrace>  
  \<acute>p :== PROC Normalize(\<acute>p)
  \<lbrace>(\<forall>pt. pt \<notin> set_of pret 
    \<longrightarrow> \<^bsup>\<sigma>\<^esup>rep pt = \<acute>rep pt \<and> \<^bsup>\<sigma>\<^esup>low pt = \<acute>low pt \<and> \<^bsup>\<sigma>\<^esup>high pt = \<acute>high pt \<and> 
        \<^bsup>\<sigma>\<^esup>mark pt = \<acute>mark pt \<and> \<^bsup>\<sigma>\<^esup>next pt = \<acute>next pt) \<and> 
  (\<exists>postt. Dag \<acute>p \<acute>low \<acute>high postt \<and> reduced postt \<and> 
  shared postt \<^bsup>\<sigma>\<^esup>var \<and> ordered postt \<^bsup>\<sigma>\<^esup>var \<and>
  set_of postt \<subseteq> set_of pret \<and> 
  (\<exists>postbdt.  bdt postt \<^bsup>\<sigma>\<^esup>var = Some postbdt \<and> prebdt \<sim> postbdt)) \<and> 
  (\<forall> no. no \<in> set_of pret \<longrightarrow> \<acute>mark no = (\<not> \<^bsup>\<sigma>\<^esup>mark \<^bsup>\<sigma>\<^esup>p)) \<rbrace>"
  apply (hoare_rule HoareTotal.ProcNoRec1)
  apply (hoare_rule anno="
    \<acute>levellist :==replicate (\<acute>p\<rightarrow>\<acute>var + 1) Null;;
    \<acute>levellist :== CALL Levellist (\<acute>p, (\<not> \<acute>p\<rightarrow>\<acute>mark) , \<acute>levellist);;
    (ANNO (\<tau>,ll). \<lbrace>\<tau>. Levellist \<acute>levellist \<acute>next ll \<and>
                   Dag \<^bsup>\<sigma>\<^esup>p \<^bsup>\<sigma>\<^esup>low \<^bsup>\<sigma>\<^esup>high pret \<and> ordered pret \<^bsup>\<sigma>\<^esup>var \<and> \<^bsup>\<sigma>\<^esup>p \<noteq> Null \<and> 
                 (bdt pret \<^bsup>\<sigma>\<^esup>var  = Some prebdt) \<and> 
                 wf_ll pret ll \<^bsup>\<sigma>\<^esup>var \<and> 
                 length \<acute>levellist = ((\<^bsup>\<sigma>\<^esup>p \<rightarrow> \<^bsup>\<sigma>\<^esup>var) + 1) \<and> 
                 wf_marking pret \<^bsup>\<sigma>\<^esup>mark \<acute>mark (\<not> \<^bsup>\<sigma>\<^esup>mark \<^bsup>\<sigma>\<^esup>p) \<and> 
                 (\<forall>pt. pt \<notin> set_of pret \<longrightarrow> \<^bsup>\<sigma>\<^esup>next pt = \<acute>next pt) \<and>
                 \<acute>low = \<^bsup>\<sigma>\<^esup>low \<and> \<acute>high = \<^bsup>\<sigma>\<^esup>high  \<and>  \<acute>p = \<^bsup>\<sigma>\<^esup>p \<and> \<acute>rep = \<^bsup>\<sigma>\<^esup>rep \<and> 
                 \<acute>var = \<^bsup>\<sigma>\<^esup>var\<rbrace> 
    \<acute>n :==0;;
    WHILE (\<acute>n < length \<acute>levellist) 
    INV \<lbrace>Levellist \<acute>levellist \<acute>next ll \<and>
         Dag \<^bsup>\<sigma>\<^esup>p \<^bsup>\<sigma>\<^esup>low \<^bsup>\<sigma>\<^esup>high pret \<and> ordered pret \<^bsup>\<sigma>\<^esup>var \<and> \<^bsup>\<sigma>\<^esup>p \<noteq> Null \<and> 
         (bdt pret \<^bsup>\<sigma>\<^esup>var  = Some prebdt) \<and> wf_ll pret ll \<^bsup>\<sigma>\<^esup>var  \<and> 
         length \<^bsup>\<tau>\<^esup>levellist = ((\<^bsup>\<sigma>\<^esup>p \<rightarrow> \<^bsup>\<sigma>\<^esup>var) + 1) \<and> 
         wf_marking pret \<^bsup>\<sigma>\<^esup>mark \<^bsup>\<tau>\<^esup>mark (\<not> \<^bsup>\<sigma>\<^esup>mark \<^bsup>\<sigma>\<^esup>p) \<and>
         \<^bsup>\<tau>\<^esup>low = \<^bsup>\<sigma>\<^esup>low \<and> \<^bsup>\<tau>\<^esup>high = \<^bsup>\<sigma>\<^esup>high  \<and>  \<^bsup>\<tau>\<^esup>p = \<^bsup>\<sigma>\<^esup>p \<and> \<^bsup>\<tau>\<^esup>rep = \<^bsup>\<sigma>\<^esup>rep  \<and> \<^bsup>\<tau>\<^esup>var = \<^bsup>\<sigma>\<^esup>var \<and>
         \<acute>n \<le> length  \<^bsup>\<tau>\<^esup>levellist \<and>
         (\<forall>pt i. (pt \<notin> set_of pret \<or> (\<acute>n <= i \<and> pt \<in> set (ll ! i) \<and>
                  i <length \<^bsup>\<tau>\<^esup>levellist ) 
                  \<longrightarrow> \<^bsup>\<sigma>\<^esup>rep pt = \<acute>rep pt)) \<and> 
         \<acute>rep ` Nodes \<acute>n ll \<subseteq> Nodes \<acute>n ll \<and> 
         (\<forall>no \<in> Nodes \<acute>n ll.
            no\<rightarrow>\<acute>rep\<rightarrow>\<^bsup>\<sigma>\<^esup>var <= no\<rightarrow>\<^bsup>\<sigma>\<^esup>var \<and> 
            (\<exists>not nort. Dag (\<acute>rep no) (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>low ) (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>high ) nort \<and>
               Dag no \<^bsup>\<sigma>\<^esup>low \<^bsup>\<sigma>\<^esup>high not \<and> reduced nort \<and> 
               ordered nort \<^bsup>\<sigma>\<^esup>var \<and> set_of nort \<subseteq> \<acute>rep ` Nodes \<acute>n ll \<and> 
               (\<forall> no \<in> set_of nort. \<acute>rep no = no) \<and> 
               (\<exists>nobdt norbdt. bdt not \<^bsup>\<sigma>\<^esup>var = Some nobdt \<and> 
                  bdt nort \<^bsup>\<sigma>\<^esup>var = Some norbdt \<and> nobdt \<sim> norbdt))) \<and>
         (\<forall>t1 t2. 
             t1\<in>Dags (\<acute>rep `(Nodes \<acute>n ll))(\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>low )(\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>high)\<and>
             t2\<in>Dags (\<acute>rep `(Nodes \<acute>n ll))(\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>low )(\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>high)
             \<longrightarrow> 
             isomorphic_dags_eq t1 t2  \<^bsup>\<sigma>\<^esup>var) \<and>
         \<acute>levellist = \<^bsup>\<tau>\<^esup>levellist \<and> \<acute>next = \<^bsup>\<tau>\<^esup>next \<and> \<acute>mark = \<^bsup>\<tau>\<^esup>mark \<and> \<acute>low = \<^bsup>\<sigma>\<^esup>low \<and> 
         \<acute>high = \<^bsup>\<sigma>\<^esup>high  \<and> \<acute>p = \<^bsup>\<sigma>\<^esup>p \<and>  \<acute>var = \<^bsup>\<sigma>\<^esup>var \<rbrace>
    VAR MEASURE (length \<acute>levellist - \<acute>n)
    DO
    CALL ShareReduceRepList(\<acute>levellist ! \<acute>n);;
    \<acute>n :==\<acute>n + 1
    OD
    \<lbrace>(\<exists>postnormt. Dag (\<acute>rep \<^bsup>\<sigma>\<^esup>p) (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>low ) (\<acute>rep \<propto> \<^bsup>\<sigma>\<^esup>high ) postnormt \<and> 
      reduced postnormt \<and> shared postnormt \<^bsup>\<sigma>\<^esup>var \<and> 
      ordered postnormt \<^bsup>\<sigma>\<^esup>var \<and> set_of postnormt \<subseteq> set_of pret \<and> 
      (\<exists>postnormbdt. bdt postnormt \<^bsup>\<sigma>\<^esup>var = Some postnormbdt \<and> prebdt \<sim> postnormbdt) \<and>
      (\<forall> no \<in> set_of postnormt. (\<acute>rep no = no))) \<and> 
      ordered pret \<^bsup>\<sigma>\<^esup>var  \<and> \<^bsup>\<sigma>\<^esup>p \<noteq> Null \<and> 
      (\<forall> pt. pt \<notin> set_of pret \<longrightarrow> \<^bsup>\<sigma>\<^esup>rep pt = \<acute>rep pt) \<and> 
      \<acute>levellist = \<^bsup>\<tau>\<^esup>levellist \<and> \<acute>next = \<^bsup>\<tau>\<^esup>next \<and> \<acute>mark = \<^bsup>\<tau>\<^esup>mark \<and> \<acute>low = \<^bsup>\<sigma>\<^esup>low \<and> \<acute>high = \<^bsup>\<sigma>\<^esup>high \<and>
      \<acute>p = \<^bsup>\<sigma>\<^esup>p \<and> (\<forall> no. no \<in> set_of pret \<longrightarrow> \<acute>mark no = (\<not> \<^bsup>\<sigma>\<^esup>mark \<^bsup>\<sigma>\<^esup>p)) \<rbrace>)
    ;;
    \<acute>p :== CALL Repoint (\<acute>p)"
    in HoareTotal.annotateI)
  apply (vcg spec=spec_total)
  prefer 2
    (*from precondition of inner spec to invariant *)
  apply    (simp add: Nodes_def null_comp_def)
    (*from inner spec to postcondition *) 
  apply   (rule_tac x=pret in exI)
  apply   clarify
  apply   (rule conjI)
  apply    clarsimp
  apply    (case_tac i)
  apply     simp
  apply    simp
  apply   (rule conjI)
  apply    simp
  apply   (rule conjI)
  apply    simp
  apply   (rule conjI)
  apply    simp
  apply   clarify
  apply   (simp (no_asm_use) only: simp_thms) 
  apply   (rule_tac x="ll" in exI)
  apply   (rule conjI)
  apply    assumption
  apply   clarify
  apply   (simp only: simp_thms triv_forall_equality True_implies_equals) 
  apply   (rule_tac x=postnormt in exI)
  apply   (rule conjI)
  apply    simp
  apply   (rule conjI)
  apply    simp
  apply   clarify
  apply   (simp (no_asm_simp))
  prefer 2
    (*while-while-Fall: while nb und Schleifenbdg gelten \<longrightarrow> while (nb+1)*)
  apply   clarify
  apply   (simp only: simp_thms triv_forall_equality True_implies_equals)
  apply   (rule_tac x="ll!n" in exI)
  apply   (rule conjI)
  apply   (simp add: Levellist_def)
  prefer 3
    (*while-end-Fall: INV nb gilt und Schleifenbdg falsch \<longrightarrow> Nachbdg while*)
  apply   (clarify)
  apply   (simp (no_asm_use) only: simp_thms triv_forall_equality True_implies_equals) 
proof -
  \<comment> \<open>End of while (invariant + false condition) to end of inner SPEC\<close>
  fix var p rep mark vara lowa higha pa levellista repa marka nexta varb ll  
    nb pret prebdt  and low :: "ref \<Rightarrow> ref" and 
    high :: "ref \<Rightarrow> ref" and repb :: "ref \<Rightarrow> ref"
  assume ll: "Levellist levellista nexta ll"
  assume wf_lla: "wf_ll pret ll var"
  assume length_lla: "length levellista = var p + 1"
  assume ord_pret: "ordered pret var"
  assume pnN: " p \<noteq> Null"
  assume rep_repb_nc: 
    "\<forall>pt i. pt \<notin> set_of pret \<or> nb \<le> i \<and> pt \<in> set (ll ! i) \<and> 
    i < length levellista 
    \<longrightarrow> rep pt = repb pt"

  assume wf_marking_prop: " wf_marking pret mark marka (\<not> mark p)"
  assume pret_dag: "Dag p low high pret"
  assume prebdt: "bdt pret var = Some prebdt"
  assume not_nbslla: "\<not> nb < length levellista"
  assume nb_le_lla: " nb \<le> length levellista"
  
  assume normalize_prop: "\<forall>no\<in>Nodes nb ll.
    var (repb no) \<le> var no \<and>
    (\<exists>not nort. Dag (repb no) (repb \<propto> low) (repb \<propto> high) nort \<and>
    Dag no low high not \<and> reduced nort \<and> ordered nort var \<and> 
    set_of nort \<subseteq> repb ` Nodes nb ll \<and> 
    (\<forall>no\<in>set_of nort. repb no = no) \<and> 
    (\<exists>nobdt norbdt. bdt not var = Some nobdt \<and> 
    bdt nort var = Some norbdt \<and> nobdt \<sim> norbdt))"
  assume repbNodes_in_Nodes: " repb ` Nodes nb ll \<subseteq> Nodes nb ll"
  assume shared_mult_dags: 
    "\<forall>t1 t2. t1 \<in> Dags (repb ` Nodes nb ll) (repb \<propto> low) (repb \<propto> high) \<and> 
    t2 \<in> Dags (repb ` Nodes nb ll) (repb \<propto> low) (repb \<propto> high) 
    \<longrightarrow> isomorphic_dags_eq t1 t2 var"
  show "(\<exists>postnormt. Dag (repb p) (repb \<propto> low) (repb \<propto> high) postnormt \<and>
    reduced postnormt \<and> shared postnormt var \<and>
    ordered postnormt var \<and> set_of postnormt \<subseteq> set_of pret \<and> 
    (\<exists>postnormbdt. 
    bdt postnormt var = Some postnormbdt \<and> prebdt \<sim> postnormbdt) \<and> 
    (\<forall> no \<in> set_of postnormt. repb no = no)) \<and>
    ordered pret var \<and> p \<noteq> Null \<and> 
    (\<forall>pt. pt \<notin> set_of pret \<longrightarrow> rep pt = repb pt) \<and>  
    (\<forall>no. no \<in> set_of pret \<longrightarrow> marka no = (\<not> mark p))"

  proof -
    from ll have length_ll_eq: "length levellista = length ll"
      by (simp add: Levellist_length)
    from rep_repb_nc have rep_nc_post: "\<forall>pt. pt \<notin> set_of pret \<longrightarrow> rep pt = repb pt"
      by auto
    from pnN pret_dag obtain lt rt where pret_def: "pret = Node lt p rt"
      by auto
    from wf_marking_prop pret_def 
    have marking_inverted: "(\<forall>no. no \<in> set_of pret \<longrightarrow> marka no = (\<not> mark p))"
      by (simp add: wf_marking_def)
    from not_nbslla nb_le_lla have nb_length_lla: "nb = length levellista"
      by simp
    with length_lla have varp_s_nb: "var p < nb"
      by simp
    from pret_def have p_in_pret: "p \<in> set_of pret"
      by simp
    with wf_lla have "p \<in> set (ll ! (var p))" 
      by (simp add: wf_ll_def)
    with varp_s_nb have p_in_Nodes: "p \<in> Nodes nb ll"
      by (auto simp add: Nodes_def)
    with normalize_prop obtain not nort where
      varrepno_varno: " var (repb p) \<le> var p" and
      nort_dag: "Dag (repb p) (repb \<propto> low) (repb \<propto> high) nort" and
      not_dag: " Dag p low high not" and
      red_nort: "reduced nort" and
      ord_nort: "ordered nort var" and
      nort_in_repNodes: " set_of nort \<subseteq> repb ` Nodes nb ll" and
      nort_repb: "(\<forall>no\<in>set_of nort. repb no = no)" and
      bdt_prop: "\<exists>nobdt norbdt. bdt not var = Some nobdt \<and> bdt nort var = Some norbdt \<and>
      nobdt \<sim> norbdt"
      by auto
    
    from wf_lla nb_length_lla have Nodes_in_pret: "Nodes nb ll \<subseteq> set_of pret"
      apply -
      apply (rule Nodes_in_pret)
      apply (auto simp add: length_ll_eq)
      done
    from pret_dag wf_lla nb_length_lla have "Null \<notin> Nodes nb ll"
      apply -
      apply (rule Null_notin_Nodes)
      apply (auto simp add: length_ll_eq)
      done
    with p_in_Nodes repbNodes_in_Nodes have rp_nNull: "repb p \<noteq> Null"
      by auto
    with nort_dag have nort_nTip: "nort\<noteq> Tip"
      by auto
    have "\<exists>postnormt. Dag (repb p) (repb \<propto> low) (repb \<propto> high) postnormt \<and>
      reduced postnormt \<and> shared postnormt var \<and>
      ordered postnormt var \<and> set_of postnormt \<subseteq> set_of pret \<and> 
      (\<exists>postnormbdt.  
      bdt postnormt var = Some postnormbdt \<and> prebdt \<sim> postnormbdt) \<and> 
      (\<forall>no \<in> set_of postnormt. repb no = no)"
    proof (rule_tac x=nort in exI)
      from nort_in_repNodes repbNodes_in_Nodes Nodes_in_pret 
      have nort_in_pret: "set_of nort \<subseteq> set_of pret"
        by blast
      from not_dag pret_dag have not_pret: "not = pret"
        by (simp add: Dag_unique)
      with bdt_prop prebdt have pret_bdt_prop: 
        "\<exists>postnormbdt.
        bdt nort var = Some postnormbdt \<and> prebdt \<sim> postnormbdt"
        by auto
      from shared_mult_dags have "shared nort var"
      proof (auto simp add: shared_def isomorphic_dags_eq_def)
        fix st1 st2 bdt1
        assume shared_imp: 
          "\<forall>t1 t2. t1\<in>Dags (repb ` Nodes nb ll) (repb \<propto> low) (repb \<propto> high) \<and> 
          t2 \<in> Dags (repb ` Nodes nb ll) (repb \<propto> low) (repb \<propto> high)
          \<longrightarrow>
          (\<exists>bdt1. bdt t1 var = Some bdt1 \<and> bdt t2 var = Some bdt1) \<longrightarrow> t1 = t2"
        assume st1_nort: " st1 \<le> nort"
        assume st2_nort: "st2 \<le> nort"
        assume bdt_st1: "bdt st1 var = Some bdt1"
        assume bdt_st2: " bdt st2 var = Some bdt1"
        from nort_in_repNodes nort_dag nort_nTip 
        have nort_in_DagsrNodes: 
          "nort \<in> Dags (repb `(Nodes nb ll)) (repb \<propto> low) (repb \<propto> high)"
          apply -
          apply (rule DagsI)
          apply auto
          done
        show "st1 = st2"
        proof (cases st1)
          case Tip
          note st1_Tip=this
          with bdt_st1 bdt_st2 show ?thesis
            by auto
        next
          case (Node lst1 st1p rst1)
          note st1_Node=this
          then have st1_nTip: "st1 \<noteq> Tip"
            by simp
          show ?thesis
          proof (cases st2)
            case Tip
            with bdt_st1 bdt_st2 show ?thesis
              by auto
          next
            case (Node lst2 st2p rst2)
            note st2_Node=this
            then have st2_nTip: "st2 \<noteq> Tip"
              by simp 
            from nort_in_DagsrNodes st1_nort ord_nort wf_lla st1_nTip 
            have st1_in_Dags: 
              "st1 \<in> Dags (repb ` Nodes nb ll) (repb \<propto> low) (repb \<propto> high)"
              apply -
              apply (rule Dags_subdags)
              apply auto
              done
            from nort_in_DagsrNodes st2_nort ord_nort wf_lla  st2_nTip 
            have st2_in_Dags: 
              "st2 \<in> Dags (repb ` Nodes nb ll) (repb \<propto> low) (repb \<propto> high)"
              apply -
              apply (rule Dags_subdags) 
              apply auto
              done
            from st1_in_Dags st2_in_Dags bdt_st1 bdt_st2 shared_imp show "st1=st2"
              by simp
          qed
        qed
      qed
      with nort_dag red_nort ord_nort nort_in_pret pret_bdt_prop nort_repb 
      show "Dag (repb p) (repb \<propto> low) (repb \<propto> high) nort \<and>
        reduced nort \<and> shared nort var \<and> ordered nort var \<and> 
        set_of nort \<subseteq> set_of pret \<and> 
        (\<exists>postnormbdt. 
        bdt nort var = Some postnormbdt \<and> prebdt \<sim> postnormbdt) \<and> 
        (\<forall>no \<in> set_of nort.  repb no = no)"
        apply -
        apply (intro conjI)
        apply assumption+
        done
    qed
    with wf_lla length_lla ord_pret pnN rep_nc_post marking_inverted
    show ?thesis
      by simp
  qed
next
  \<comment> \<open>From postcondition inner SPEC to final postcondition\<close>
  fix var low high p rep levellist marka "next" 
    nexta lowb highb pb levellista ll repa pret prebdt 
    and mark::"ref\<Rightarrow>bool" and postnormt postnormbdt
  assume ll: "Levellist levellista nexta ll"
  assume repoint_spec: 
         "Dag pb lowb highb postnormt"
         "\<forall>pt. pt \<notin> set_of postnormt \<longrightarrow> low pt = lowb pt \<and> high pt = highb pt"
  assume pret_dag: "Dag p low high pret"
  assume ord_pret: "ordered pret var"
  assume pnN: " p \<noteq> Null"
  assume onemark_pret: 
    "\<forall>n. n \<in> set_of pret \<longrightarrow> mark n = mark p" (is "\<forall>n. ?in_pret n \<longrightarrow> ?eq_mark_p n")
  assume pret_bdt: " bdt pret var = Some prebdt"
  
  assume  wf_ll: "wf_ll pret ll var"  and
    length_ll:"length levellist =var p + 1" and
    wf_marking_ll: "wf_marking pret mark marka (\<not> mark p)"
  assume  
    postnormt_dag: "Dag (repa p) (repa \<propto> low) (repa \<propto> high) postnormt" and
    reduced_postnormt: "reduced postnormt" and
    shared_postnormt: "shared postnormt var" and
    ordered_postnormt: "ordered postnormt var" and
    subset_pret: "set_of postnormt \<subseteq> set_of pret"and
    sim_bdt: "bdt postnormt var = Some postnormbdt" "prebdt \<sim> postnormbdt"  and
    postdag_repa: "\<forall>no \<in> set_of postnormt. repa no = no" and
    rep_eq: "\<forall>pt. pt \<notin> set_of pret \<longrightarrow> rep pt = repa pt"  and
    pret_marked: "\<forall>no. no \<in> set_of pret \<longrightarrow> marka no = (\<not> mark p)"
  assume unmodif_next: "\<forall>p. p \<notin> set_of pret \<longrightarrow> next p = nexta p"
  show "(\<forall>pt. pt \<notin> set_of pret 
    \<longrightarrow> low pt = lowb pt \<and> high pt = highb pt \<and> 
    mark pt = marka pt ) "

  proof -
    from ll have length_ll_eq: "length levellista = length ll"
      by (simp add: Levellist_length)
    from repoint_spec  pnN subset_pret
    have repoint_nc: "(\<forall>pt. pt \<notin> set_of pret 
      \<longrightarrow> low pt = lowb pt \<and> high pt = highb pt) \<and> Dag pb lowb highb postnormt"
      by auto
    then have lowhigh_b_eq: "\<forall>pt. pt \<notin> set_of pret 
      \<longrightarrow> low pt = lowb pt \<and> high pt = highb pt"
      by fastforce
    from wf_marking_ll pret_dag pnN 
    have mark_b_eq: "\<forall>pt. pt \<notin> set_of pret \<longrightarrow> mark pt = marka pt"
      apply -
      apply (simp add: wf_marking_def)
      apply (split dag.splits)
      apply  simp
      apply (rule allI)
      apply (rule impI)
      apply (elim conjE)
      apply (erule_tac x=pt in allE)
      apply fastforce
      done
    with lowhigh_b_eq rep_eq unmodif_next
    have pret_nc: "\<forall>pt. pt \<notin> set_of pret 
      \<longrightarrow> rep pt = repa pt \<and> low pt = lowb pt \<and> high pt = highb pt \<and> 
      mark pt = marka pt \<and> next pt = nexta pt"
      by blast
(*    from repoint_nc have rept_dag: "Dag pb lowb highb postnormt"
      by simp
    with reduced_postnormt shared_postnormt ordered_postnormt subset_pret sim_bdt 
      pret_bdt 
    have post_same_prop: 
      "\<exists>postt. Dag pb lowb highb postt \<and> reduced postt \<and>
      shared postt var \<and> ordered postt var \<and> set_of postt \<subseteq> set_of pret \<and>
      (\<exists>postbdt. bdt postt var = Some postbdt \<and> prebdt \<sim> postbdt)" 
      apply -
      apply (rule_tac x=postnormt in exI)
      apply fastforce
      done*)
    from pret_nc  
    show ?thesis
      by fastforce
  qed
next
  \<comment> \<open>invariant to invariant\<close>
  fix var low high p rep mark pret prebdt levellist ll "next" marka n repc 
    and repb :: "ref \<Rightarrow> ref"  
  assume ll: "Levellist levellist next ll"
  assume pret_dag: "Dag p low high pret"
  assume ord_pret: " ordered pret var"
  assume pnN: "p \<noteq> Null"
  assume prebdt_pret: "bdt pret var = Some prebdt"
  assume wf_ll: "wf_ll pret ll var"
  assume lll: "length levellist = var p + 1"
  assume n_Suc_var_p: "n < var p + 1"
  assume wf_marking_m_ma: "wf_marking pret mark marka (\<not> mark p)"

(*  assume rep_nc: " \<forall>pt. pt \<notin> set_of pret \<or> 
    (\<exists>i. n \<le> i \<and> pt \<in> set (ll ! i) \<and> i < var p + 1) 
    \<longrightarrow> rep pt = repb pt" *)
  assume rep_nc:      "\<forall>pt i.
           pt \<notin> set_of pret \<or> n \<le> i \<and> pt \<in> set (ll ! i) \<and> i < var p + 1 \<longrightarrow>
           rep pt = repb pt"
  assume repbNodes_in_Nodes: "repb ` Nodes n ll \<subseteq> Nodes n ll"
  assume
    normalize_prop: "\<forall>no\<in>Nodes n ll.
    var (repb no) \<le> var no \<and>
    (\<exists>not nort. Dag (repb no) (repb \<propto> low) (repb \<propto> high) nort \<and>
    Dag no low high not \<and> reduced nort \<and> ordered nort var \<and>
    set_of nort \<subseteq> repb ` Nodes n ll \<and>
    (\<forall>no\<in>set_of nort. repb no = no) \<and>
    (\<exists>nobdt. bdt not var = Some nobdt \<and> 
    (\<exists>norbdt. bdt nort var = Some norbdt \<and> 
    nobdt \<sim> norbdt)))" 
  assume 
    isomorphic_dags_eq: 
    "\<forall>t1 t2. t1 \<in> Dags (repb ` Nodes n ll) (repb \<propto> low) (repb \<propto> high)\<and>
    t2 \<in> Dags (repb ` Nodes n ll) (repb \<propto> low) (repb \<propto> high) 
    \<longrightarrow> isomorphic_dags_eq t1 t2 var"
  show "(\<forall>no\<in>set (ll ! n).
              no \<noteq> Null \<and>
              (low no = Null) = (high no = Null) \<and>
              low no \<notin> set (ll ! n) \<and>
              high no \<notin> set (ll ! n) \<and>
              isLeaf_pt no low high = (var no \<le> 1) \<and>
              (low no \<noteq> Null \<longrightarrow> repb (low no) \<noteq> Null) \<and> (repb \<propto> low) no \<notin> set (ll ! n)) \<and>
          (\<forall>no1\<in>set (ll ! n). \<forall>no2\<in>set (ll ! n). var no1 = var no2) \<and>
          (\<forall>repa. (\<forall>no. no \<notin> set (ll ! n) \<longrightarrow> repb no = repa no) \<and>
                  (\<forall>no\<in>set (ll ! n).
                      repa no \<noteq> Null \<and>
                      (if (repa \<propto> low) no = (repa \<propto> high) no \<and> low no \<noteq> Null
                       then repa no = (repa \<propto> low) no
                       else repa no \<in> set (ll ! n) \<and>
                            repa (repa no) = repa no \<and>
                            (\<forall>no1\<in>set (ll ! n).
                                ((repa \<propto> high) no1 = (repa \<propto> high) no \<and>
                                 (repa \<propto> low) no1 = (repa \<propto> low) no) =
                                (repa no = repa no1)))) \<longrightarrow>
                  var p + 1 - (n + 1) < var p + 1 - n \<and>
                  n + 1 \<le> var p + 1 \<and>
                  (\<forall>pt i. pt \<notin> set_of pret \<or> (n + 1 \<le> i \<and> pt \<in> set (ll ! i) \<and> i < var p + 1) \<longrightarrow>
                        rep pt = repa pt) \<and>
                  repa ` Nodes (n + 1) ll \<subseteq> Nodes (n + 1) ll \<and>
                  (\<forall>no\<in>Nodes (n + 1) ll.
                      var (repa no) \<le> var no \<and>
                      (\<exists>not nort.
                          Dag (repa no) (repa \<propto> low) (repa \<propto> high) nort \<and>
                          Dag no low high not \<and>
                          reduced nort \<and>
                          ordered nort var \<and>
                          set_of nort \<subseteq> repa ` Nodes (n + 1) ll \<and>
                          (\<forall>no\<in>set_of nort. repa no = no) \<and>
                          (\<exists>nobdt.
                              bdt not var = Some nobdt \<and>
                              (\<exists>norbdt. bdt nort var = Some norbdt \<and> nobdt \<sim> norbdt)))) \<and>
                  (\<forall>t1 t2.
                      t1 \<in> Dags (repa ` Nodes (n + 1) ll) (repa \<propto> low) (repa \<propto> high) \<and>
                      t2 \<in> Dags (repa ` Nodes (n + 1) ll) (repa \<propto> low) (repa \<propto> high) \<longrightarrow>
                      isomorphic_dags_eq t1 t2 var))"
  proof -
    from ll have length_ll_eq: "length levellist = length ll"
      by (simp add: Levellist_length)
    from n_Suc_var_p lll have nsll: "n < length levellist" by simp
    hence nseqll: "n \<le> length levellist" by simp
    have srrl_precond: "(\<forall>no \<in> set (ll ! n).
      no \<noteq> Null \<and>
      (low no = Null) = (high no = Null) \<and>
      low no \<notin> set (ll ! n) \<and>
      high no \<notin> set (ll ! n) \<and> 
      isLeaf_pt no low high = (var no \<le> 1) \<and> 
      (low no \<noteq> Null \<longrightarrow> repb (low no) \<noteq> Null) \<and> 
      (repb \<propto> low) no \<notin> set (ll ! n))"
    proof (intro ballI)
      fix no
      assume no_in_lln: "no \<in> set (ll ! n)"
      with wf_ll nsll have no_in_pret_var: "no \<in> set_of pret \<and> var no = n"
        by (simp add: wf_ll_def length_ll_eq)
      with pret_dag have no_nNull: "no \<noteq> Null"
        apply -
        apply (rule set_of_nn)
        apply auto
        done
      from pret_dag prebdt_pret no_in_pret_var 
      have balanced_no: "(low no = Null) = (high no = Null)"
        apply -
        apply (erule conjE)
        apply (rule_tac p=p and low=low in balanced_bdt)
        apply auto
        done
      have low_no_notin_lln: "low no \<notin> set (ll ! n)"
      proof (cases "low no = Null")
        case True
        note lno_Null=this
        with balanced_no have hno_Null: "high no = Null"
          by simp
        show ?thesis
        proof (cases "low no \<in> set (ll ! n)") 
          case True
          with wf_ll nsll have "low no \<in> set_of pret \<and> var (low no) = n"
            by (auto simp add: wf_ll_def length_ll_eq)
          with pret_dag have "low no \<noteq> Null"
            apply -
            apply (rule set_of_nn)
            apply auto
            done
          with lno_Null show ?thesis
            by simp
        next
          assume lno_notin_lln: "low no \<notin> set (ll ! n)"
          then show ?thesis
            by simp
        qed
      next
        assume lno_nNull: "low no \<noteq> Null"
        with balanced_no have hno_nNull: "high no \<noteq> Null"
          by simp
        with lno_nNull pret_dag ord_pret no_in_pret_var 
        have var_children_smaller: "var (low no) < var no \<and> var (high no) < var no" 
          apply -
          apply (rule var_ordered_children)
          apply auto
          done
        show ?thesis
        proof (cases "low no \<in> set (ll ! n)")
          case True
          with wf_ll nsll have "low no \<in> set_of pret \<and> var (low no) = n"
            by (simp add: wf_ll_def length_ll_eq)
          with var_children_smaller no_in_pret_var show ?thesis
            by simp
        next
          assume "low no \<notin> set (ll ! n)"
          thus ?thesis
            by simp
        qed
      qed
      have high_no_notin_lln: "high no \<notin> set (ll ! n)"
      proof (cases "high no = Null")
        case True
        note hno_Null=this
        with balanced_no have lno_Null: "low no = Null"
          by simp
        show ?thesis
        proof (cases "high no \<in> set (ll ! n)") 
          case True
          with wf_ll nsll have "high no \<in> set_of pret \<and> var (high no) = n"
            by (auto simp add: wf_ll_def length_ll_eq)
          with pret_dag have "high no \<noteq> Null"
            apply -
            apply (rule set_of_nn)
            apply auto
            done
          with hno_Null show ?thesis
            by simp
        next
          assume hno_notin_lln: "high no \<notin> set (ll ! n)"
          then show ?thesis
            by simp
        qed
      next
        assume hno_nNull: "high no \<noteq> Null"
        with balanced_no have lno_nNull: "low no \<noteq> Null"
          by simp
        with hno_nNull pret_dag ord_pret no_in_pret_var 
        have var_children_smaller: "var (low no) < var no \<and> var (high no) < var no" 
          apply -
          apply (rule var_ordered_children)
          apply auto
          done
        show ?thesis
        proof (cases "high no \<in> set (ll ! n)")
          case True
          with wf_ll nsll have "high no \<in> set_of pret \<and> var (high no) = n"
            by (simp add: wf_ll_def length_ll_eq)
          with var_children_smaller no_in_pret_var show ?thesis
            by simp
        next
          assume "high no \<notin> set (ll ! n)"
          thus ?thesis
            by simp
        qed
      qed 
      from no_in_pret_var pret_dag no_nNull obtain not where 
        no_dag_ex: "Dag no low high not"
        apply -
        apply (rotate_tac 2)
        apply (drule subnode_dag_cons)
        apply (auto simp del: Dag_Ref)
        done
      with pret_dag prebdt_pret no_in_pret_var obtain nobdt 
        where nobdt_ex: 
        "bdt not var = Some nobdt"
        apply -
        apply (drule subbdt_ex_dag_def)
        apply auto
        done
      have isLeaf_var: "isLeaf_pt no low high = (var no \<le> 1)"
      proof
        assume no_isLeaf: "isLeaf_pt no low high"
        from nobdt_ex no_dag_ex no_isLeaf show "var no \<le> 1"
          apply -
          apply (rule bdt_Some_Leaf_var_le_1)
          apply auto
          done
      next
        assume varno_le_1: "var no \<le> 1"
        show "isLeaf_pt no low high"
        proof (cases "var no = 0")
          case True
          with nobdt_ex no_nNull no_dag_ex have "not = Node Tip no Tip" 
            apply -
            apply (drule bdt_Some_var0_Zero)
            apply auto
            done
          with no_dag_ex show "isLeaf_pt no low high"
            by (simp add: isLeaf_pt_def)
        next
          assume "var no \<noteq> 0"
          with varno_le_1 have "var no = 1"
            by simp
          with nobdt_ex no_nNull no_dag_ex have "not = Node Tip no Tip"
            apply -
            apply (drule bdt_Some_var1_One)
            apply auto
            done
          with no_dag_ex show "isLeaf_pt no low high"
            by (simp add: isLeaf_pt_def)
        qed
      qed
      have repb_low_nNull: "(low no \<noteq> Null \<longrightarrow> repb (low no) \<noteq> Null)"
      proof
        assume lno_nNull: "low no \<noteq> Null"
        with no_nNull no_in_pret_var pret_dag have lno_in_pret: "low no \<in> set_of pret"
          apply -
          apply (rule_tac low=low in subelem_set_of_low)
          apply auto
          done
        from lno_nNull balanced_no have hno_nNull: "high no \<noteq> Null"
          by simp
        with lno_nNull pret_dag ord_pret no_in_pret_var 
        have var_children_smaller: "var (low no) < var no \<and> var (high no) < var no" 
          apply -
          apply (rule var_ordered_children)
          apply auto
          done 
        with no_in_pret_var have var_lno_l_n: "var (low no) <n"
          by simp
        with wf_ll lno_in_pret nsll have "low no \<in> set (ll ! (var (low no)))"
          by (simp add: wf_ll_def length_ll_eq)
        with lno_in_pret var_lno_l_n have "low no \<in> Nodes n ll"
          apply (simp add: Nodes_def)
          apply (rule_tac x="var (low no)" in exI)
          apply simp
          done
        hence "repb (low no) \<in> repb ` Nodes n ll"
          by simp
        with repbNodes_in_Nodes have repb_lno_in_Nodes: 
          "repb (low no) \<in> Nodes n ll"
          by blast
        from pret_dag wf_ll nsll have "Null \<notin> Nodes n ll"
          apply -
          apply (rule Null_notin_Nodes)
          apply (auto simp add: length_ll_eq)
          done 
        with repb_lno_in_Nodes show "repb (low no) \<noteq> Null"
          by auto
      qed
      have Null_notin_lln: "Null \<notin> set (ll ! n)"
      proof (cases "Null \<in> set (ll ! n)")
        case True
        with wf_ll nsll have "Null \<in> set_of pret \<and> var (Null) = n" 
          by (simp add: wf_ll_def length_ll_eq)
        with pret_dag have "Null \<noteq> Null"
          apply -
          apply (rule set_of_nn)
          apply auto
          done
        thus ?thesis
          by auto
      next
        assume "Null \<notin> set (ll ! n)"
        thus ?thesis
          by simp
      qed
      have "(repb \<propto> low) no \<notin> set (ll ! n)"
      proof (cases "low no = Null")  
        case True
        with Null_notin_lln show ?thesis
          by (simp add: null_comp_def)
      next
        assume lno_nNull: "low no \<noteq> Null"
        with no_nNull no_in_pret_var pret_dag have lno_in_pret: "low no \<in> set_of pret"
          apply -
          apply (rule_tac low=low in subelem_set_of_low)
          apply auto
          done
        from lno_nNull have propto_eq_comp: "(repb \<propto> low) no = repb (low no)"
          by (simp add: null_comp_def)
        from lno_nNull balanced_no have hno_nNull: "high no \<noteq> Null"
          by simp
        with lno_nNull pret_dag ord_pret no_in_pret_var 
        have var_children_smaller: "var (low no) < var no \<and> var (high no) < var no" 
          apply -
          apply (rule var_ordered_children)
          apply auto
          done 
        with no_in_pret_var have var_lno_l_n: "var (low no) <n"
          by simp
        with wf_ll lno_in_pret nsll have "low no \<in> set (ll ! (var (low no)))"
          by (simp add: wf_ll_def length_ll_eq)
        with lno_in_pret var_lno_l_n have lno_in_Nodes_n: "low no \<in> Nodes n ll"
          apply (simp add: Nodes_def)
          apply (rule_tac x="var (low no)" in exI)
          apply simp
          done
        hence "repb (low no) \<in> repb ` Nodes n ll"
          by simp
        with  repbNodes_in_Nodes have repb_lno_in_Nodes: 
          "repb (low no) \<in> Nodes n ll"
          by blast
        with lno_in_Nodes_n normalize_prop have "var (repb (low no)) \<le> var (low no)" 
          by auto
        with var_lno_l_n have var_rep_lno_l_n: " var (repb (low no)) < n"
          by simp
        with repb_lno_in_Nodes have "\<exists> k < n. repb (low no) \<in> set (ll ! k)"
          by (auto simp add: Nodes_def)
        with wf_ll propto_eq_comp nsll show " (repb \<propto> low) no \<notin> set (ll ! n)"
          apply -
          apply (erule exE)
          apply (rule_tac i=k and j=n in no_in_one_ll)
          apply (auto simp add: length_ll_eq)
          done
      qed
      with no_nNull balanced_no low_no_notin_lln high_no_notin_lln isLeaf_var repb_low_nNull
      show " no \<noteq> Null \<and>
        (low no = Null) = (high no = Null) \<and>
        low no \<notin> set (ll ! n) \<and> high no \<notin> set (ll ! n) \<and> 
        isLeaf_pt no low high = (var no \<le> 1) \<and> 
        (low no \<noteq> Null \<longrightarrow> repb (low no) \<noteq> Null) \<and> 
        (repb \<propto> low) no \<notin> set (ll ! n)"
        by auto
    qed
    have all_nodes_same_var: "\<forall>no1 \<in> set (ll ! n). \<forall>no2 \<in> set (ll ! n). var no1 = var no2"
    proof (intro ballI impI)
      fix no1 no2
      assume "no1 \<in> set (ll ! n)"
      with wf_ll nsll have var_lln_i: "var no1 = n"
        by (simp add: wf_ll_def length_ll_eq)
      assume "no2 \<in> set (ll ! n)"
      with wf_ll nsll have "var no2 = n"
        by (simp add: wf_ll_def length_ll_eq)
      with var_lln_i show " var no1 = var no2"
        by simp
    qed
    have  "(\<forall>repa. (\<forall>no. no \<notin> set (ll ! n) \<longrightarrow> repb no = repa no) \<and>
                  (\<forall>no\<in>set (ll ! n).
                      repa no \<noteq> Null \<and>
                      (if (repa \<propto> low) no = (repa \<propto> high) no \<and> low no \<noteq> Null
                       then repa no = (repa \<propto> low) no
                       else repa no \<in> set (ll ! n) \<and>
                            repa (repa no) = repa no \<and>
                            (\<forall>no1\<in>set (ll ! n).
                                ((repa \<propto> high) no1 = (repa \<propto> high) no \<and>
                                 (repa \<propto> low) no1 = (repa \<propto> low) no) =
                                (repa no = repa no1)))) \<longrightarrow>
                  var p + 1 - (n + 1) < var p + 1 - n \<and>
                  n + 1 \<le> var p + 1 \<and>
                  (\<forall>pt i. pt \<notin> set_of pret \<or> (n + 1 \<le> i \<and> pt \<in> set (ll ! i) \<and> i < var p + 1) \<longrightarrow>
                        rep pt = repa pt) \<and>
                  repa ` Nodes (n + 1) ll \<subseteq> Nodes (n + 1) ll \<and>
                  (\<forall>no\<in>Nodes (n + 1) ll.
                      var (repa no) \<le> var no \<and>
                      (\<exists>not nort.
                          Dag (repa no) (repa \<propto> low) (repa \<propto> high) nort \<and>
                          Dag no low high not \<and>
                          reduced nort \<and>
                          ordered nort var \<and>
                          set_of nort \<subseteq> repa ` Nodes (n + 1) ll \<and>
                          (\<forall>no\<in>set_of nort. repa no = no) \<and>
                          (\<exists>nobdt.
                              bdt not var = Some nobdt \<and>
                              (\<exists>norbdt. bdt nort var = Some norbdt \<and> nobdt \<sim> norbdt)))) \<and>
                  (\<forall>t1 t2.
                      t1 \<in> Dags (repa ` Nodes (n + 1) ll) (repa \<propto> low) (repa \<propto> high) \<and>
                      t2 \<in> Dags (repa ` Nodes (n + 1) ll) (repa \<propto> low) (repa \<propto> high) \<longrightarrow>
                      isomorphic_dags_eq t1 t2 var))"
      (is "(\<forall>repc. ?srrl_post repc \<longrightarrow> ?norm_inv repc) ") 
    proof (intro allI impI, elim conjE)
      fix repc
      assume repbc_nc: "\<forall>no. no \<notin> set (ll ! n) \<longrightarrow> repb no = repc no"
      assume rep_prop: " \<forall>no\<in>set (ll ! n).
        repc no \<noteq> Null \<and>
               (if (repc \<propto> low) no = (repc \<propto> high) no \<and> low no \<noteq> Null
                then repc no = (repc \<propto> low) no
                else repc no \<in> set (ll ! n) \<and>
                     repc (repc no) = repc no \<and>
                     (\<forall>no1\<in>set (ll ! n).
                         ((repc \<propto> high) no1 = (repc \<propto> high) no \<and>
                          (repc \<propto> low) no1 = (repc \<propto> low) no) =
                         (repc no = repc no1)))"
      show "?norm_inv repc"
      proof -
        from n_Suc_var_p have termi: "var p + 1 - (n + 1) < var p + 1 - n"
          by arith
        from wf_ll repbc_nc nsll 
        have Nodes_n_rep_nc: "\<forall>p. p \<in> Nodes n ll \<longrightarrow> repb p = repc p"
          apply -
          apply (rule allI)
          apply (rule impI)
          apply (simp add: Nodes_def)
          apply (erule exE)
          apply (erule_tac x=p in allE)
          apply (drule_tac i=x and j=n in no_in_one_ll)
          apply (auto simp add: length_ll_eq)
          done
        from repbNodes_in_Nodes 
        have Nodes_n_rep_in_Nodesn: 
          "\<forall> p. p \<in> Nodes n ll \<longrightarrow> repb p \<in> Nodes n ll"
          by auto
        from wf_ll nsll have "Nodes n ll \<subseteq> set_of pret"
          apply -
          apply (rule Nodes_in_pret)
          apply (auto simp add: length_ll_eq)
          done
        with Nodes_n_rep_in_Nodesn  
        have Nodes_n_rep_in_pret: "\<forall>p. p \<in> Nodes n ll \<longrightarrow> repb p \<in> set_of pret"
          apply -
          apply (intro allI impI)
          apply blast
          done
        have Nodes_repbc_Dags_eq: "\<forall>p t. p \<in> Nodes n ll 
          \<longrightarrow> Dag (repb p) (repb \<propto> low) (repb \<propto> high) t = 
          Dag (repc p) (repc \<propto> low) (repc \<propto> high) t"
        proof (intro allI impI)
          fix p t
          assume p_in_Nodes: " p \<in> Nodes n ll"
          then have repp_nc: "repb p = repc p"
            by (rule Nodes_n_rep_nc [rule_format])
          from p_in_Nodes normalize_prop obtain nort where
            nort_repb_dag: "Dag (repb p) (repb \<propto> low) (repb \<propto> high) nort" and
            nort_in_repbNodes: "set_of nort \<subseteq> repb ` Nodes n ll"
            apply -
            apply (erule_tac x=p in ballE)
            prefer 2
            apply auto
            done
          from nort_in_repbNodes repbNodes_in_Nodes 
          have nort_in_Nodesn: "set_of nort \<subseteq> Nodes n ll"
            by blast
          from pret_dag wf_ll nsll have "Null \<notin> Nodes n ll"
            apply -
            apply (rule Null_notin_Nodes)
            apply (auto simp add: length_ll_eq)
            done
          with p_in_Nodes repbNodes_in_Nodes have repp_nNull: "repb p \<noteq> Null"
            by auto
          from nort_repb_dag repp_nc 
          have nort_repbc_dag: "Dag (repc p) (repb \<propto> low) (repb \<propto> high) nort"
            by simp
          from nort_in_Nodesn have "\<forall>x \<in> set_of nort. x \<in> Nodes n ll"
            apply -
            apply (rule ballI)
            apply blast
            done
          with wf_ll nsll  have "\<forall>x \<in> set_of nort. x \<in> set_of pret \<and> var x < n"
            apply -
            apply (rule ballI)
            apply (rule wf_ll_Nodes_pret)
            apply (auto simp add: length_ll_eq)
            done
          with pret_dag prebdt_pret nort_repbc_dag ord_pret wf_ll  nsll repbc_nc 
          have 
            "\<forall> x \<in> set_of nort. (repc \<propto> low) x = (repb \<propto> low) x \<and> 
            (repc \<propto> high) x = (repb \<propto> high) x"
            apply -
            apply (rule nort_null_comp)
            apply (auto simp add: length_ll_eq)
            done
          with nort_repbc_dag repp_nc 
          have "Dag (repc p) (repb \<propto> low) (repb \<propto> high) nort = 
            Dag (repc p) (repc \<propto> low) (repc \<propto> high) nort"
            apply -
            apply (rule heaps_eq_Dag_eq)
            apply (rule ballI)
            apply (erule_tac x=x in ballE)
            apply (elim conjE)
            apply (rule conjI)
            apply auto
            done
          with nort_repbc_dag repp_nc show 
            "Dag (repb p) (repb \<propto> low) (repb \<propto> high) t = 
            Dag (repc p) (repc \<propto> low) (repc \<propto> high) t"
            apply auto
            apply (rotate_tac 2)
            apply (frule_tac Dag_unique)
            apply (rotate_tac 1)
            apply simp
            apply simp
            apply (frule Dag_unique)
            apply (rotate_tac 3)
            apply simp
            apply simp
            done
        qed
        from rep_prop have repbc_changes: "\<forall>no\<in>set (ll ! n).
          repc no \<noteq> Null \<and>
          (if (repc \<propto> low) no = (repc \<propto> high) no \<and> low no \<noteq> Null 
          then repc no = (repc \<propto> low) no
          else repc no \<in> set (ll ! n) \<and> repc (repc no) = repc no \<and> 
          (\<forall>no1\<in>set (ll ! n). ((repc \<propto> high) no1 = (repc \<propto> high) no \<and> 
          (repc \<propto> low) no1 = (repc \<propto> low) no) = (repc no = repc no1)))"
          by blast
        from nsll lll  have n_var_prop: "n + 1 <= var p + 1"
          by simp
        from rep_nc have Sucn_repb_nc: "(\<forall>pt. pt \<notin> set_of pret \<or> 
          (\<exists>i. n + 1 \<le> i \<and> pt \<in> set (ll ! i) \<and> i < var p + 1)  
          \<longrightarrow> rep pt = repb pt)" 
          apply -
          apply (intro allI impI)
          apply (erule_tac x=pt in allE)
          apply auto
          apply (rule_tac x="i" in exI)
          apply auto
          done
        have repc_nc: 
          "(\<forall>pt. pt \<notin> set_of pret \<or> 
          (\<exists>i. n + 1 \<le> i \<and> pt \<in> set (ll ! i) \<and> i < var p + 1) 
          \<longrightarrow> rep pt = repc pt)" 
        proof (intro allI impI)
          fix pt 
          assume pt_notin_lower_ll: "pt \<notin> set_of pret \<or> 
            (\<exists>i. n + 1 \<le> i \<and> pt \<in> set (ll ! i) \<and> i < var p + 1)"
          show "rep pt = repc pt"
          proof (cases "pt \<notin> set_of pret")
            case True
            with wf_ll nsll have "pt \<notin> set (ll ! n)"
              apply (simp add: wf_ll_def length_ll_eq)
              apply (case_tac "pt \<in> set (ll ! n)")
              apply (subgoal_tac "pt \<in> set_of pret")
              apply (auto)
              done
            with repbc_nc have "repb pt = repc pt"
              by auto
            with Sucn_repb_nc True show ?thesis
              by auto
          next
            assume pt_in_pret: "\<not> pt \<notin> set_of pret"
            with pt_notin_lower_ll have pt_in_higher_ll: 
              "\<exists>i. n + 1 \<le> i \<and> pt \<in> set (ll ! i) \<and> i < var p + 1"
              by simp
            with nsll wf_ll lll have pt_notin_lln: "pt \<notin> set (ll ! n)"
              apply -
              apply (erule exE)
              apply (rule_tac i=i and j=n in no_in_one_ll)
              apply (auto simp add: length_ll_eq)
              done
            with repbc_nc have "repb pt = repc pt"
              by auto
            with Sucn_repb_nc pt_in_higher_ll show ?thesis
              by auto 
          qed
        qed
        from wf_ll nsll  
        have Nodesn_notin_lln: "\<forall>no \<in> Nodes n ll. no \<notin> set (ll ! n)"
          apply (simp add: Nodes_def)
          apply clarify
          apply (drule no_in_one_ll)
          apply (auto simp add: length_ll_eq)
          done
        with repbc_nc  
        have Nodesn_repnc: "\<forall>no \<in> Nodes n ll. repb no = repc no"
          apply -
          apply (rule ballI)
          apply (erule_tac x=no in allE)
          apply simp
          done
        then have repbNodes_repcNodes: 
          "repb `(Nodes n ll) = repc `(Nodes n ll)"
          apply -
          apply rule
          apply blast
          apply rule
          apply (erule imageE)
          apply (erule_tac x=xa in ballE)
          prefer 2
          apply simp
          apply rule
          apply auto
          done
        have repcNodes_in_Nodes: 
          "repc ` Nodes (n + 1) ll \<subseteq> Nodes (n + 1) ll"
        proof
          fix x
          assume x_in_repcNodesSucn: " x \<in> repc ` Nodes (n + 1) ll"
          show "x \<in> Nodes (n + 1) ll"
          proof (cases "x \<in> repc `Nodes n ll")
            case True
            with repbNodes_repcNodes repbNodes_in_Nodes have "x \<in> Nodes n ll" 
              by auto
            with Nodes_subset show ?thesis 
              by auto
          next
            assume " x \<notin> repc `Nodes n ll"
            with x_in_repcNodesSucn have x_in_repclln: "x \<in> repc `set (ll ! n)"
              apply (auto simp add: Nodes_def)
              apply (case_tac "k<n")
              apply auto
              apply (case_tac "k = n")
              apply simp
              apply arith
              done
            from x_in_repclln show ?thesis
            proof (elim imageE)
              fix y
              assume x_repcy: "x = repc y"
              assume y_in_repclln: "y \<in> set (ll ! n)"
              from rep_prop y_in_repclln  obtain
                repcy_nNull: "repc y \<noteq> Null" and
                red_prop: "(repc \<propto> low) y = (repc \<propto> high) y \<and> 
                low y \<noteq> Null \<longrightarrow> repc y = (repc \<propto> high) y" and
                share_prop: "((repc \<propto> low) y = (repc \<propto> high) y \<longrightarrow> low y = Null) 
                \<longrightarrow> repc y \<in> set (ll ! n) \<and> repc (repc y) = repc y \<and> 
                (\<forall>no1\<in>set (ll ! n). 
                ((repc \<propto> high) no1 = (repc \<propto> high) y \<and> 
                (repc \<propto> low) no1 = (repc \<propto> low) y) = (repc y = repc no1))"
                using [[simp_depth_limit = 4]]
                by auto
              from wf_ll nsll  y_in_repclln obtain
                y_in_pret: "y \<in> set_of pret" and
                vary_n: "var y = n"
                by (auto simp add: wf_ll_def length_ll_eq)
              from y_in_pret pret_dag have y_nNull: "y \<noteq> Null"
                apply -
                apply (rule set_of_nn)
                apply auto
                done
              show "x \<in> Nodes (n + 1) ll"
              proof (cases "low y = Null")
                case True
                from pret_dag prebdt_pret True y_in_pret 
                have highy_Null: "high y = Null"
                  apply -
                  apply (drule balanced_bdt)
                  apply auto
                  done
                with share_prop True obtain 
                  repcy_in_llb: "repc y \<in> set (ll ! n)" and
                  rry_ry: " repc (repc y) = repc y" and
                  y_other_node_prop: "\<forall>no1\<in>set (ll ! n). 
                  ((repc \<propto> high) no1 = (repc \<propto> high) y \<and> 
                  (repc \<propto> low) no1 = (repc \<propto> low) y) = (repc y = repc no1)"
                  by simp
                from repcy_in_llb  x_repcy show ?thesis
                  by (auto simp add: Nodes_def)
              next
                assume lowy_nNull: "low y \<noteq> Null"
                with pret_dag prebdt_pret y_in_pret 
                have highy_nNull: "high y \<noteq> Null"
                  apply -
                  apply (drule balanced_bdt)
                  apply auto
                  done
                show ?thesis
                proof (cases "(repc \<propto> low) y = (repc \<propto> high) y")
                  case True
                  with red_prop lowy_nNull have "repc y = (repc \<propto> high) y"
                    by auto
                  with highy_nNull have red_repc_y: "repc y = repc (high y)"
                    by (simp add: null_comp_def)
                  from pret_dag ord_pret y_in_pret lowy_nNull  highy_nNull 
                  
                  have "var (low y) < var y \<and> var (high y) < var y"
                    apply -
                    apply (rule var_ordered_children) 
                    apply auto
                    done
                  with  vary_n have varhighy: "var (high y) < n"
                    by auto
                  from y_in_pret y_nNull highy_nNull pret_dag  
                  have "high y \<in> set_of pret" 
                    apply -
                    apply (drule subelem_set_of_high)
                    apply auto
                    done
                  with wf_ll varhighy have "high y \<in> Nodes n ll"
                    by (auto simp add: wf_ll_def Nodes_def)
                  with red_repc_y have "repc y \<in> repc `Nodes n ll"
                    by simp
                  with x_repcy have "x \<in> repc `Nodes n ll"
                    by simp
                  with repbNodes_repcNodes repbNodes_in_Nodes 
                  have "x \<in> Nodes n ll" 
                    by auto
                  with Nodes_subset show ?thesis 
                    by auto
                next
                  assume "(repc \<propto> low) y \<noteq> (repc \<propto> high) y"
                  with share_prop obtain 
                    repcy_in_llbn: "repc y \<in> set (ll ! n)" and
                    rry_ry: "repc (repc y) = repc y" and 
                    y_other_node_share: "\<forall>no1\<in>set (ll ! n). 
                    ((repc \<propto> high) no1 = (repc \<propto> high) y \<and> 
                    (repc \<propto> low) no1 = (repc \<propto> low) y) = (repc y = repc no1)"
                    by auto
                  with repcy_in_llbn  x_repcy have "x \<in> set (ll ! n)"
                    by auto
                  then show ?thesis
                    by (auto simp add: Nodes_def)
                qed
              qed
            qed
          qed
        qed
        have "(\<forall>no\<in>Nodes (n + 1) ll.
          var (repc no) \<le> var no \<and> 
          (\<exists>not nort. Dag (repc no) (repc \<propto> low) (repc \<propto> high) nort \<and>
          Dag no low high not \<and>
          reduced nort \<and> ordered nort var \<and> 
          set_of nort \<subseteq> repc ` Nodes (n + 1) ll \<and> 
          (\<forall>no\<in>set_of nort. repc no = no) \<and>
          (\<exists>nobdt. bdt not var = Some nobdt \<and> 
          (\<exists>norbdt. bdt nort var = Some norbdt \<and> nobdt \<sim> norbdt))))"
          (is "\<forall>no\<in>Nodes (n + 1) ll. ?Q i no")
        proof (intro ballI)
          fix no
          assume no_in_Nodes: "no \<in> Nodes (n + 1) ll"
          from wf_ll no_in_Nodes nsll  have no_in_pret: "no \<in> set_of pret"
            apply (simp add: wf_ll_def Nodes_def length_ll_eq)
            apply (erule conjE)
            apply (thin_tac "\<forall>q. q \<in> set_of pret \<longrightarrow> q \<in> set (ll ! var q)")
            apply (erule exE)
            apply (erule_tac x=x in allE)
            apply (erule impE)
            apply arith
            apply (erule_tac x=no in ballE)
            apply auto
            done
          from pret_dag no_in_pret have nonNull: "no\<noteq> Null" 
            apply -
            apply (rule set_of_nn [rule_format])
            apply auto
            done  
          show "?Q i no"
          proof (cases "no \<in> Nodes n ll")
            case True
            note no_in_Nodesn=this
            with wf_ll nsll  no_in_Nodes 
            have no_notin_llbn: "no \<notin> set (ll ! n)"
              apply -
              apply (simp add: Nodes_def length_ll_eq)
              apply (elim exE)
              apply (drule_tac ?i=xa and ?j=n in no_in_one_ll)
              apply arith
              apply simp
              apply auto
              done
            with repbc_nc have repb_no_eq_repc_no: "repb no = repc no" 
              by simp
            from repbc_nc no_in_Nodes no_notin_llbn normalize_prop True 
            have varrep_eq_var: "var (repc no) \<le> var no" 
              apply -
              apply (erule_tac x=no in ballE)
              prefer 2
              apply simp
              apply (erule_tac x=no in allE)
              apply simp
              done
            moreover
            from True normalize_prop no_in_Nodes obtain not nort where
              nort_dag: "Dag (repb no) (repb \<propto> low) (repb \<propto> high) nort" and
              ord_nort: "ordered nort var" and
              subset_nort_not:  "set_of nort \<subseteq> repb `(Nodes n ll)" and
              not_dag:  " Dag no low high not" and
              red_nort: "reduced nort" and 
              nort_repb: "(\<forall>no\<in>set_of nort. repb no = no)" and
              bdt_prop: "\<exists>nobdt norbdt. bdt not var = Some nobdt \<and> 
              bdt nort var = Some norbdt \<and> nobdt \<sim> norbdt" 
              by blast
            moreover
            from Nodesn_notin_lln repbc_nc nort_repb subset_nort_not repbNodes_in_Nodes 
            have nort_repc: 
              "(\<forall>no\<in>set_of nort. repc no = no)"
              apply auto
              apply (subgoal_tac "no \<in> Nodes n ll")
              apply fastforce
              apply blast
              done
            moreover
            from nort_dag have nortnodesnN: "(\<forall>no. no \<in> set_of nort \<longrightarrow> no \<noteq> Null)"
              apply -
              apply (rule allI)
              apply (rule impI)
              apply (rule set_of_nn)
              apply auto
              done
            moreover  
            have "Dag (repc no) (repc \<propto> low) (repc \<propto> high) nort"
            proof -
              from no_notin_llbn repbc_nc have repbc_no: "repc no = repb no"
                by fastforce
              with nort_dag 
              have nortrepbc_dag: "Dag (repc no) (repb \<propto> low) (repb \<propto> high) nort"
                by simp
              from wf_ll nseqll have "Nodes n ll \<subseteq> set_of pret"
                apply -
                apply (rule Nodes_levellist_subset_t)
                apply assumption+
                apply (simp add: length_ll_eq)
                done
              with repbNodes_in_Nodes subset_nort_not 
              have subset_nort_pret:  "set_of nort \<subseteq> set_of pret"
                by simp
              have vxsn_in_pret: "\<forall> x \<in> set_of nort. var x < n \<and> x \<in> set_of pret"
              proof (rule ballI)
                fix x
                assume x_in_nort: "x \<in> set_of nort"
                from x_in_nort subset_nort_not repbNodes_in_Nodes 
                have "x \<in> Nodes n ll"
                  by blast
                with wf_ll nsll  have xsn: "var x < n"
                  apply (simp add: wf_ll_def Nodes_def length_ll_eq)
                  apply (erule conjE)
                  apply (thin_tac " \<forall>q. q \<in> set_of pret \<longrightarrow> q \<in> set (ll ! var q)")
                  apply (erule exE)
                  apply (erule_tac x=xa in allE)
                  apply (erule impE)
                  apply arith
                  apply (erule_tac x=x in ballE)
                  apply auto
                  done
                from x_in_nort subset_nort_pret have x_in_pret: "x \<in> set_of pret"
                  by blast
                with xsn show "var x < n \<and> x \<in> set_of pret" by simp
              qed
              with pret_dag prebdt_pret nortrepbc_dag ord_pret wf_ll  nsll 
                repbc_nc 
              have "\<forall> x \<in> set_of nort. ((repc \<propto> low) x = (repb \<propto> low) x \<and> 
                (repc \<propto> high) x = (repb \<propto> high) x)"
                apply -
                apply (rule nort_null_comp)
                apply (auto simp add: length_ll_eq)
                done
              with nort_dag 
              have "Dag (repc no) (repc \<propto> low) (repc \<propto> high) nort = 
                Dag (repc no) (repb \<propto> low) (repb \<propto> high) nort"
                apply -
                apply (rule heaps_eq_Dag_eq)
                apply simp
                done
              with nortrepbc_dag show ?thesis
                by simp
            qed
            moreover 
            have "set_of nort \<subseteq> repc `(Nodes (n + 1) ll)"
            proof -
              have Nodesn_in_NodesSucn: "Nodes n ll \<subseteq> Nodes (n + 1) ll"
                by (simp add: Nodes_def set_split)
              then have repbNodesn_in_repbNodesSucn: 
                "repb `(Nodes n ll) \<subseteq> repb `(Nodes (n + 1) ll)"
                by blast
              from wf_ll nsll  
              have Nodes_n_notin_lln: "\<forall>no \<in> Nodes n ll. no \<notin> set (ll ! n)"
                apply (simp add: Nodes_def length_ll_eq)
                apply clarify
                apply (drule no_in_one_ll)
                apply auto
                done
              with repbc_nc  have "\<forall>no \<in> Nodes n ll. repb no = repc no"
                apply -
                apply (rule ballI)
                apply (erule_tac x=no in allE)
                apply simp
                done
              then have repbNodes_repcNodes: 
                "repb `(Nodes n ll) = repc `(Nodes n ll)"
                apply -
                apply rule
                apply blast
                apply rule
                apply (erule imageE)
                apply (erule_tac x=xa in ballE)
                prefer 2
                apply simp
                apply rule
                apply auto
                done
              from Nodesn_in_NodesSucn 
              have "repc `(Nodes n ll) \<subseteq> repc `(Nodes (n + 1) ll)"
                by blast
              with repbNodes_repcNodes subset_nort_not repbNodesn_in_repbNodesSucn 
              show ?thesis by simp
            qed
            ultimately show ?thesis 
              by blast
          next
            assume " no \<notin> Nodes n ll"
            with no_in_Nodes  have no_in_llbn: "no \<in> set (ll ! n)"
              apply (simp add: Nodes_def)
              apply (erule exE)
              apply (erule_tac x=x in allE)
              apply (case_tac "x<n")
              apply simp
              apply simp
              apply (elim conjE)
              apply (case_tac "x=n")
              apply simp
              apply arith
              done
            with wf_ll  nsll have varno: "var no = n"
              by (simp add: wf_ll_def length_ll_eq)
            from repbc_changes no_in_llbn 
            have repbcno_changes: "repc no \<noteq> Null \<and>
              ((repc \<propto> low) no = (repc \<propto> high) no \<and> low no \<noteq> Null 
              \<longrightarrow> repc no = (repc \<propto> high) no) \<and>
              (((repc \<propto> low) no = (repc \<propto> high) no \<longrightarrow> low no = Null) 
              \<longrightarrow> repc no \<in> set (ll ! n)  \<and> repc (repc no) = repc no \<and> 
              (\<forall>no1\<in>set (ll ! n). ((repc \<propto> high) no1 = (repc \<propto> high) no \<and>
              (repc \<propto> low) no1 = (repc \<propto> low) no) = (repc no = repc no1)))"
              (is "?rnonN \<and> ?repreduce \<and> ?repshare")
              using [[simp_depth_limit=4]]
              by (simp split: if_split)
            then obtain 
              rnonN: "?rnonN" and
              repreduce: "?repreduce" and
              repshare: "?repshare"
              by blast
            have repcn_normalize: "var (repc no) \<le> var no \<and>
              (\<exists>not nort. Dag (repc no) (repc \<propto> low) (repc \<propto> high) nort \<and>
              Dag no low high not \<and> reduced nort \<and> ordered nort var \<and>
              set_of nort \<subseteq> repc ` Nodes (n + 1) ll \<and>
              (\<forall>no\<in>set_of nort. repc no = no) \<and>
              (\<exists>nobdt. bdt not var = Some nobdt \<and> 
              (\<exists>norbdt. bdt nort var = Some norbdt \<and> nobdt \<sim> norbdt)))"
              (is "?varrep \<and> ?repcn_prop" 
                is "?varrep \<and> 
                (\<exists>not nort. ?nort_dag nort \<and> ?not_dag not \<and> ?red nort \<and> 
                ?ord nort \<and> ?nort_in_Nodes nort \<and> ?repcno_no_n nort \<and> ?bdt_equ not nort)")
            proof (cases "high no = Null")
              case True
              note highnoNull=this
              with pret_dag prebdt_pret no_in_pret   
              have lownoNull: "low no = Null"
                apply -
                apply (drule balanced_bdt)
                apply assumption+
                apply simp
                done
              with repshare have repcnoinlln:"repc no \<in> set (ll ! n)"
                by simp
              with wf_ll  nsll have varrno_n: "var (repc no) = n"
                by (simp add: wf_ll_def length_ll_eq)
              with varno have varrep: "?varrep"
                by simp
              from wf_ll  nsll no_in_llbn varrno_n 
              have varrno_varno: "var (repc no) = var no"
                by (simp add: wf_ll_def length_ll_eq)
              from wf_ll  nsll repcnoinlln 
              have rno_in_pret: "repc no \<in> set_of pret" 
                by (simp add: wf_ll_def length_ll_eq)
              from repcnoinlln repshare lownoNull 
              have reprep_eq_rep: "repc (repc no) = repc no" 
                by simp
              with repcnoinlln repshare lownoNull 
              have repchildreneq: 
                "((repc \<propto> high) (repc no) = (repc \<propto> high) no \<and> 
                (repc \<propto> low) (repc no) = (repc \<propto> low) no)"
                by simp
              have repcn_prop: "?repcn_prop"
                apply -         
                apply (rule_tac x="(Node Tip no Tip)" in exI)
                apply (rule_tac x="(Node Tip (repc no) Tip)" in exI)
                apply (intro conjI)
                apply simp
                prefer 3
                apply simp
                prefer 3
                apply simp
              proof -
                from pret_dag pnN rno_in_pret have rnonN: "repc no \<noteq> Null"
                  apply (case_tac "repc no = Null")
                  apply auto
                  done
                from highnoNull repchildreneq 
                have rhighNull: "(repc \<propto> high) (repc no) = Null" 
                  by (simp add: null_comp_def)
                from lownoNull repchildreneq 
                have rlowNull: "(repc \<propto> low) (repc no) = Null" 
                  by (simp add: null_comp_def)
                with rhighNull rnonN   
                show "repc no \<noteq> Null \<and> (repc \<propto> low) (repc no) = Null \<and> 
                  (repc \<propto> high) (repc no) = Null"
                  by simp
              next
                from nonNull lownoNull highnoNull   
                show "?not_dag (Node Tip no Tip)"
                  by simp
              next
                from no_in_Nodes 
                show "set_of (Node Tip (repc no) Tip) \<subseteq>  repc ` Nodes (n + 1) ll"
                  by simp
              next
                show "\<forall>no\<in>set_of (Node Tip (repc no) Tip). repc no = no"
                proof 
                  fix pt
                  assume pt_in_repcLeaf: "pt \<in> set_of (Node Tip (repc no) Tip)"
                  with reprep_eq_rep show "repc pt = pt"
                    by simp
                qed
              next
                show "?bdt_equ (Node Tip no Tip) (Node Tip (repc no) Tip)"
                proof (cases "var no = 0")
                  case True 
                  note vno_Null=this
                  then have nobdt: "bdt (Node Tip no Tip) var = Some Zero" by simp
                  from varrep  vno_Null have varrno: "var (repc no) = 0" by simp
                  then have norbdt: "bdt (Node Tip (repc no) Tip) var = Some Zero" by simp
                  from nobdt norbdt vno_Null varrno show ?thesis
                    by (simp add: cong_eval_def)
                next
                  assume vno_not_Null: "var no \<noteq> 0"
                  show ?thesis
                  proof (cases "var no = 1")
                    case True
                    note vno_One=this
                    then have nobdt: "bdt (Node Tip no Tip) var = Some One" by simp
                    from varrno_varno vno_One 
                    have "bdt (Node Tip (repc no) Tip) var = Some One" by simp 
                    with nobdt show ?thesis by (auto simp add: cong_eval_def)
                  next
                    assume vno_nOne: "var no \<noteq> 1"
                    with vno_not_Null have onesvno: "1 < var no" by simp
                    from nonNull lownoNull highnoNull   
                    have no_dag: "Dag no low high (Node Tip no Tip)"
                      by simp 
                    with pret_dag no_in_pret have not_in_pret: "(Node Tip no Tip) \<le> pret"
                      by (metis set_of_subdag)
                    with prebdt_pret have "\<exists>bdt2. bdt (Node Tip no Tip) var = Some bdt2"
                      by (metis subbdt_ex)
                    with onesvno show ?thesis 
                      by simp
                  qed
                qed
              qed
              with varrep reprep_eq_rep show ?thesis by simp
            next
              assume hno_nNull: "high no \<noteq> Null"
              with pret_dag prebdt_pret no_in_pret   have lno_nNull: "low no \<noteq> Null"
                by (metis balanced_bdt)
                  (*-------------------normalize_prop fuer (high no)------------------------*)
              
              from no_in_pret nonNull hno_nNull pret_dag  
              have hno_in_pret: "high no \<in> set_of pret"
                by (metis subelem_set_of_high)
              with wf_ll 
              have hno_in_ll: "high no \<in> set (ll ! (var (high no)))" 
                by (simp add: wf_ll_def)
              from pret_dag ord_pret  no_in_pret lno_nNull hno_nNull 
              
              have varhnos_varno: "var (high no) < var no"
                by (metis var_ordered_children)
              with varno have varhnos_n: "var (high no) < n" by simp
              with hno_in_ll have hno_in_Nodesn: "high no \<in> Nodes n ll"
                apply (simp add: Nodes_def)
                apply (rule_tac x="var (high no)" in exI)
                apply simp
                done
              from wf_ll nsll hno_in_ll   varhnos_n 
              have "high no \<notin> set (ll ! n)"
                apply -
                apply (rule no_in_one_ll)
                apply (auto simp add: length_ll_eq)
                done
              with repbc_nc have repb_repc_high: "repb (high no) = repc (high no)" by simp
              with normalize_prop hno_in_Nodesn varhnos_varno varno 
              have high_normalize: "var (repc (high no)) \<le> var (high no) \<and>
                (\<exists>not nort. Dag (repc (high no)) (repb \<propto> low) (repb \<propto> high) nort \<and>
                Dag (high no) low high not \<and> reduced nort \<and>
                ordered nort var \<and> set_of nort \<subseteq> repb `(Nodes n ll) \<and>
                (\<forall>no\<in>set_of nort. repb no = no) \<and>
                (\<exists>nobdt norbdt. bdt not var = Some nobdt \<and> bdt nort var = 
                Some norbdt \<and> nobdt \<sim> norbdt))"
                (is "?varrep_high \<and> 
                  (\<exists>not nort. ?repbchigh_dag nort \<and> ?high_dag not \<and> 
                  ?redhigh nort \<and> ?ordhigh nort \<and> ?rephigh_in_Nodes nort \<and> 
                  ?repbno_no nort \<and> ?highdd_prop not nort)"
                  is "?varrep_high \<and> ?not_nort_prop")
                apply simp
                apply (erule_tac x="high no" in ballE)
                apply (simp del: Dag_Ref)
                apply simp
                done
              then have varrep_high: "?varrep_high" by simp
              from varhnos_n varrep_high have varrephno_s_n: 
                "var (repc (high no)) < n"
                by simp
              from Nodes_subset 
              have "Nodes n ll \<subseteq> Nodes (Suc n) ll"
                by auto
              with hno_in_Nodesn repcNodes_in_Nodes 
              have "repc (high no) \<in> Nodes (Suc n) ll"
                apply simp
                apply blast
                done
              with wf_ll nsll  have "repc (high no) \<in> set_of pret"
                apply (simp add: wf_ll_def Nodes_def length_ll_eq)
                apply (elim conjE exE)
                apply (thin_tac " \<forall>q. q \<in> set_of pret \<longrightarrow> q \<in> set (ll ! var q)")
                apply (erule_tac x=x in allE)
                apply (erule impE)
                apply simp
                apply (erule_tac x="repc (high no)" in ballE)
                apply auto
                done
              with wf_ll varrephno_s_n 
              have "\<exists> k<n. repc (high no) \<in> set (ll ! k)"
                by (auto simp add: wf_ll_def)
              with wf_ll nsll  have "repc (high no) \<notin> set (ll ! n)"
                apply -
                apply (erule exE)
                apply (rule_tac i=k and j=n in no_in_one_ll)
                apply (auto simp add: length_ll_eq)
                done
              with repbc_nc 
              have repbchigh_idem: "repb (repc (high no)) = repc (repc (high no))"
                by auto
              from high_normalize 
              have not_nort_prop_high: "?not_nort_prop" by (simp del: Dag_Ref)
              from not_nort_prop_high obtain hnot where high_dag: "?high_dag hnot"
                by auto
              from wf_ll nsll  
              have "\<forall>no \<in> Nodes n ll. no \<notin> set (ll ! n)"
                apply (simp add: Nodes_def length_ll_eq)
                apply clarify
                apply (drule no_in_one_ll)
                apply auto
                done
              with repbc_nc  have "\<forall>no \<in> Nodes n ll. repb no = repc no"
                apply -
                apply (rule ballI)
                apply (erule_tac x=no in allE)
                apply simp
                done
              then 
              have repbNodes_repcNodes: 
                "repb `(Nodes n ll) = repc `(Nodes n ll)"
                apply -
                apply rule
                apply blast
                apply rule
                apply (erule imageE)
                apply (erule_tac x=xa in ballE)
                prefer 2
                apply simp
                apply rule
                apply auto
                done
              then have repcNodes_repbNodes: 
                "repc `(Nodes n ll) = repb `(Nodes n ll)"
                by simp
              from pret_dag nsll  wf_ll 
              have null_notin_Nodesn: "Null \<notin> Nodes n ll"
                apply -
                apply (rule Null_notin_Nodes)
                apply (auto simp add: length_ll_eq)
                done
              from hno_in_Nodesn have "repc (high no) \<in> repc `(Nodes n ll)"
                by blast
              with repbNodes_in_Nodes repcNodes_repbNodes 
              have "repc (high no) \<in> Nodes n ll"
                apply simp
                apply blast
                done
              with null_notin_Nodesn have rhn_nNull: "repc (high no) \<noteq> Null"
                by auto

                  (*-------------------normalize_prop fuer (low no)--------------------------*)

              from no_in_pret nonNull lno_nNull pret_dag  
              have lno_in_pret: "low no \<in> set_of pret"
                by (rule subelem_set_of_low)
              with wf_ll 
              have lno_in_ll: "low no \<in> set (ll ! (var (low no)))" 
                by (simp add: wf_ll_def)
              from pret_dag ord_pret  no_in_pret lno_nNull hno_nNull  
              have varlnos_varno: "var (low no) < var no"
                apply -
                apply (drule var_ordered_children)
                apply assumption+
                apply auto
                done
              with varno have varlnos_n: "var (low no) < n" by simp
              with lno_in_ll have lno_in_Nodesn: "low no \<in> Nodes n ll"
                apply (simp add: Nodes_def)
                apply (rule_tac x="var (low no)" in exI)
                apply simp
                done
              from varlnos_n wf_ll nsll lno_in_ll   
              have "low no \<notin> set (ll ! n)"
                apply -
                apply (rule no_in_one_ll)
                apply (auto simp add: length_ll_eq)
                done
              with repbc_nc have repb_repc_low: "repb (low no) = repc (low no)" by simp
              with normalize_prop lno_in_Nodesn varlnos_varno varno 
              have low_normalize: "var (repc (low no)) \<le> var (low no) \<and>
                (\<exists>not nort. Dag (repc (low no)) (repb \<propto> low) (repb \<propto> high) nort \<and>
                Dag (low no) low high not \<and> reduced nort \<and> ordered nort var \<and>
                set_of nort \<subseteq> repb `(Nodes n ll) \<and>
                (\<forall>no\<in>set_of nort. repb no = no) \<and>
                (\<exists>nobdt norbdt. bdt not var = Some nobdt \<and> bdt nort var = Some norbdt \<and> 
                nobdt \<sim> norbdt))"
                (is "?varrep_low \<and> 
                  (\<exists>not nort. ?repbclow_dag nort \<and> ?low_dag not \<and> ?redhigh nort \<and> 
                  ?ordhigh nort \<and> ?replow_in_Nodes nort  \<and> ?low_repno_no nort 
                  \<and> ?lowdd_prop not nort)"
                  is "?varrep_low \<and> ?not_nort_prop_low")
                apply simp
                apply (erule_tac x="low no" in ballE)
                apply (simp del: Dag_Ref)
                apply simp
                done
              then have varrep_low: "?varrep_low" by simp
              from low_normalize have not_nort_prop_low: "?not_nort_prop_low" 
                by (simp del: Dag_Ref)
              from lno_in_Nodesn have "repc (low no) \<in> repc `(Nodes n ll)"
                by blast
              with repbNodes_in_Nodes repcNodes_repbNodes 
              have "repc (low no) \<in> Nodes n ll"
                apply simp
                apply blast
                done
              with null_notin_Nodesn have rln_nNull: "repc (low no) \<noteq> Null"
                by auto

              
              show ?thesis
              proof (cases "repc (low no) = repc (high no)")
                case True
                note red_case=this
                with repreduce lno_nNull hno_nNull 
                have rno_eq_hrno: "repc no = repc (high no)" 
                  by (simp add: null_comp_def)
                from varhnos_varno rno_eq_hrno varrep_high have varrep: "?varrep" by simp
                from not_nort_prop_high not_nort_prop_low have repcn_prop: "?repcn_prop"
                  apply -
                  apply (elim exE)
                  apply (rename_tac rnot lnot rnort lnort )
                  apply (rule_tac x="(Node lnot no rnot)" in exI)
                  apply (rule_tac x=rnort in exI)
                  apply (elim conjE)
                  apply (intro conjI)
                  prefer 7
                  apply (elim exE)
                  apply (rename_tac rnot lnot rnort lnort rnobdt lnobdt rnorbdt lnorbdt)
                  apply (elim conjE)
                  apply (case_tac  "Suc 0 < var no")
                  apply (rule_tac x="(Bdt_Node lnobdt (var no) rnobdt)" in exI)
                  apply (rule conjI)
                  prefer 2
                  apply (rule_tac x=rnorbdt in exI)
                  apply (rule conjI)
                proof -
                  fix rnot lnot rnort lnort
                  assume highnort_dag: 
                    "Dag (repc (high no)) (repb \<propto> low) (repb \<propto> high) rnort"
                  assume ord_nort: " ordered rnort var"
                  assume rnort_in_repNodes: " set_of rnort \<subseteq>  repb ` Nodes n ll"
                  from rnort_in_repNodes repbNodes_in_Nodes 
                  have nort_in_Nodes: "set_of rnort \<subseteq> Nodes n ll"
                    by blast
                  from varhnos_n varrep_high 
                  have vrhnos_n: "var (repc (high no)) < n" by simp
                  from rhn_nNull highnort_dag 
                  have "\<exists>lno rno. rnort = Node lno (repc (high no)) rno" by fastforce
                  with highnort_dag rhn_nNull have "root rnort = repc (high no)" by auto
                  with ord_nort have "\<forall>x \<in> set_of rnort. var x <= var (repc (high no))"
                    apply -
                    apply (rule ballI)
                    apply (drule ordered_set_of)
                    apply auto
                    done
                  with vrhnos_n have vxsn: "\<forall>x \<in> set_of rnort. var x < n" 
                    by fastforce
                  from nort_in_Nodes have "\<forall>x \<in> set_of rnort. x \<in> Nodes n ll" 
                    by auto
                  with wf_ll nsll  
                  have x_in_pret: "\<forall>x \<in> set_of rnort. x \<in> set_of pret"
                    apply -
                    apply (rule ballI)
                    apply (drule wf_ll_Nodes_pret)
                    apply (auto simp add: length_ll_eq)
                    done
                  from vxsn x_in_pret 
                  have vxsn_in_nort: "\<forall>x \<in> set_of rnort. var x <n \<and> x \<in> set_of pret"
                    by auto
                  with pret_dag prebdt_pret highnort_dag ord_pret wf_ll  nsll 
                    repbc_nc 
                  have "\<forall>x \<in> set_of rnort. (repc \<propto> low) x = (repb \<propto> low) x \<and> 
                    (repc \<propto> high) x = (repb \<propto> high) x"
                    apply -
                    apply (rule nort_null_comp)
                    apply (auto simp add: length_ll_eq)
                    done
                  with rno_eq_hrno 
                  have "Dag (repc no) (repc \<propto> low) (repc \<propto> high) rnort = 
                    Dag (repc no) (repb \<propto> low) (repb \<propto> high) rnort"
                    apply -
                    apply (rule heaps_eq_Dag_eq)
                    apply simp
                    done
                  with highnort_dag rno_eq_hrno 
                  show "Dag (repc no) (repc \<propto> low) (repc \<propto> high) rnort" by simp
                next
                  fix rnot lnot rnort lnort
                  assume lnot_dag: "Dag (low no) low high lnot"
                  assume rnot_dag: "Dag (high no) low high rnot"
                  with lnot_dag   nonNull 
                  show "Dag no low high (Node lnot no rnot)" by simp
                next
                  fix rnot lnot rnort lnort
                  assume " reduced rnort"
                  then show "reduced rnort" by simp
                next
                  fix rnort
                  assume "ordered rnort var"
                  then show "ordered rnort var" by simp
                next
                  fix rnort
                  assume rnort_in_Nodes: " set_of rnort \<subseteq> repb ` Nodes n ll"
                  have "Nodes n ll \<subseteq> Nodes (n + 1) ll" 
                    by (simp add: Nodes_def set_split) 
                  then have "repc ` Nodes n ll \<subseteq> repc ` Nodes (n + 1) ll"
                    by blast
                  with rnort_in_Nodes repbNodes_repcNodes 
                  show " set_of rnort \<subseteq> repc ` Nodes (n + 1) ll" 
                    by (simp add: Nodes_def)
                next
                  fix rnort rnorbdt
                  assume " bdt rnort var = Some rnorbdt"
                  then show " bdt rnort var = Some rnorbdt" by simp
                next
                  fix rnot lnot rnort lnort rnobdt lnobdt rnorbdt lnorbdt
                  assume rcongeval: "rnobdt \<sim> rnorbdt"
                  assume lnort_dag: 
                    "Dag (repc (low no)) (repb \<propto> low) (repb \<propto> high) lnort"
                  assume rnort_dag: 
                    "Dag (repc (high no)) (repb \<propto> low) (repb \<propto> high) rnort"
                  assume lnorbdt_def: " bdt lnort var = Some lnorbdt"
                  assume rnorbdt_def: " bdt rnort var = Some rnorbdt"
                  assume lcongeval:"lnobdt \<sim> lnorbdt"
                  from red_case lnort_dag rnort_dag 
                  have lnort_rnort: "lnort = rnort" 
                    by (simp add: Dag_unique del: Dag_Ref)
                  with lnorbdt_def lcongeval rnorbdt_def 
                  have lnobdt_rnorbdt: "lnobdt \<sim> rnorbdt" by simp
                  with rcongeval have "lnobdt \<sim> rnobdt" 
                    apply -
                    apply (rule cong_eval_trans)
                    apply (auto simp add: cong_eval_sym)
                    done
                  then have " Bdt_Node lnobdt (var no) rnobdt \<sim> rnobdt"
                    apply -
                    apply (simp add: cong_eval_sym [rule_format])
                    apply (rule cong_eval_child_high)
                    apply assumption
                    done
                  with rcongeval show "Bdt_Node lnobdt (var no) rnobdt \<sim> rnorbdt"
                    apply -
                    apply (rotate_tac 1)
                    apply (rule cong_eval_trans)
                    apply auto
                    done
                next
                  fix lnot rnot lnobdt rnobdt
                  assume lnot_dag: "Dag (low no) low high lnot"
                  assume rnot_dag: " Dag (high no) low high rnot"
                  assume lnobdt_def: " bdt lnot var = Some lnobdt"
                  assume rnobdt_def: " bdt rnot var = Some rnobdt"
                  assume onesvarno: " Suc 0 < var no"
                  with rnobdt_def lnot_dag rnot_dag lnobdt_def 
                  show "bdt (Node lnot no rnot) var = 
                    Some (Bdt_Node lnobdt (var no) rnobdt)" 
                    by simp
                next
                  fix rnot lnot rnort lnort rnobdt lnobdt rnorbdt lnorbdt
                  assume lnobdt_def: " bdt lnot var = Some lnobdt"
                  assume rnobdt_def: " bdt rnot var = Some rnobdt"
                  assume rnorbdt_def: " bdt rnort var = Some rnorbdt"
                  assume cong_rno_rnor: " rnobdt \<sim> rnorbdt"
                  assume lnot_dag: "Dag (low no) low high lnot"
                  assume rnot_dag: "Dag (high no) low high rnot"
                  assume "\<not> Suc 0 < var no"
                  then have varnoseq1: "var no = 0 \<or> var no = 1" by auto
                  show "\<exists>nobdt. bdt (Node lnot no rnot) var = Some nobdt \<and> 
                    (\<exists>norbdt. bdt rnort var = Some norbdt \<and> nobdt \<sim> norbdt)"
                  proof (cases "var no = 0")
                    case True
                    note vnoNull=this
                    with pret_dag ord_pret no_in_pret lno_nNull hno_nNull  
                    show ?thesis
                      apply -
                      apply (drule var_ordered_children)
                      apply auto
                      done
                  next
                    assume "var no \<noteq> 0"
                    with varnoseq1 have vnoOne: "var no = 1" by simp
                    from pret_dag  ord_pret no_in_pret lno_nNull hno_nNull  
                      vnoOne 
                    have vlvrNull: "var (low no) = 0 \<and> var (high no) = 0"
                      apply -
                      apply (drule var_ordered_children)
                      apply auto
                      done
                    then have vlNull: "var (low no) = 0" by simp
                    from vlvrNull have vrNull: "var (high no) = 0" by simp
                    from lnobdt_def lnot_dag vlNull  lno_nNull 
                    have lnobdt_Zero: "lnobdt = Zero"
                      apply -
                      apply (drule bdt_Some_var0_Zero)
                      apply auto
                      done
                    from rnobdt_def rnot_dag vrNull  hno_nNull 
                    have rnobdt_Zero: "rnobdt = Zero"
                      apply -
                      apply (drule bdt_Some_var0_Zero)
                      apply auto
                      done
                    from lnobdt_Zero lnobdt_def have "bdt lnot var = Some Zero" by simp
                    with lnot_dag vlNull  
                    have lnot_Node: "lnot = (Node Tip (low no) Tip)"
                      by auto
                    from rnobdt_Zero rnobdt_def rnot_dag vrNull  
                    have rnot_Node: "rnot = (Node Tip (high no) Tip)" 
                      by auto
                    from pret_dag no_in_pret obtain not where 
                      not_ex: "Dag no low high not"
                      apply -
                      apply (drule dag_setof_exD)
                      apply auto
                      done
                    with pret_dag no_in_pret have not_ex_in_pret: "not <= pret" 
                      apply -
                      apply (rule set_of_subdag)
                      apply auto
                      done
                    from not_ex lnot_dag rnot_dag   nonNull 
                    have not_def: "not = (Node lnot no rnot)" 
                      by (simp add: Dag_unique del: Dag_Ref)
                    with not_ex_in_pret prebdt_pret 
                    have nobdt_ex: "\<exists>nobdt. bdt (Node lnot no rnot) var = Some nobdt"
                      apply -
                      apply (rule subbdt_ex)
                      apply auto
                      done
                    then obtain nobdt where 
                      nobdt_def: "bdt (Node lnot no rnot) var = Some nobdt" by auto
                    from not_def have "root not = no" by simp
                    with nobdt_def vnoOne not_def have "not = (Node Tip no Tip)"
                      apply -
                      apply (drule bdt_Some_var1_One)
                      apply auto
                      done
                    with not_def have "rnot = Tip" by simp
                    with rnot_Node show ?thesis by simp
                  qed
                next
                  fix rnot lnot rnort lnort
                  assume rnort_in_repb_Nodesn: "set_of rnort \<subseteq> repb ` Nodes n ll"
                  assume rnort_repb_no: "\<forall>no\<in>set_of rnort. repb no = no"
                  from repbNodes_in_Nodes rnort_in_repb_Nodesn 
                  have rnort_in_Nodesn: "set_of rnort \<subseteq> Nodes n ll"
                    by blast
                  show "\<forall>no\<in>set_of rnort. repc no = no"
                  proof
                    fix pt
                    assume pt_in_rnort: " pt \<in> set_of rnort"
                    with rnort_in_Nodesn have "pt \<in> Nodes n ll" 
                      by blast
                    with Nodesn_notin_lln have "pt \<notin> set (ll ! n)"
                      by auto
                    with repbc_nc have "repb pt = repc pt"
                      by auto
                    with rnort_repb_no pt_in_rnort show "repc pt = pt"
                      by auto
                  qed
                qed
                with varrep show ?thesis by simp
              next
                assume share_case_cond: "repc (low no) \<noteq> repc (high no)"
                with lno_nNull hno_nNull 
                have share_case_cond_propto: "(repc \<propto> low) no \<noteq> (repc \<propto> high) no"
                  by (simp add: null_comp_def)
                with repshare obtain 
                  rno_in_llbn: "repc no \<in> set (ll ! n)" and
                  rrno_eq_rno: "repc (repc no) = repc no" and
                  twonodes_in_llbn_prop: "(\<forall>no1\<in>set (ll ! n). 
                  ((repc \<propto> high) no1 = (repc \<propto> high) no \<and> 
                  (repc \<propto> low) no1 = (repc \<propto> low) no) = (repc no = repc no1))"
                  by auto
                from wf_ll rno_in_llbn  nsll 
                have varrepno_n: "var (repc no) = n" 
                  by (simp add: wf_ll_def length_ll_eq)
                with varno have varrep: "?varrep" 
                  by simp
                from not_nort_prop_high not_nort_prop_low have repcn_prop: "?repcn_prop"
                  apply-
                  apply (elim exE)
                  apply (rename_tac rnot lnot rnort lnort)
                  apply (rule_tac x="Node lnot no rnot" in exI)
                  apply (rule_tac x="Node lnort (repc no) rnort" in exI)
                  apply (elim conjE)
                  apply (intro conjI)
                  prefer 7
                  apply (elim exE)
                  apply (rename_tac rnot lnot rnort lnort rnobdt lnobdt rnorbdt lnorbdt)
                  apply (elim conjE)
                  apply (case_tac  "Suc 0 < var no")
                  apply (rule_tac x="(Bdt_Node lnobdt (var no) rnobdt)" in exI)
                  apply (rule conjI)
                  prefer 2
                  apply (rule_tac x="(Bdt_Node lnorbdt (var (repc no)) rnorbdt)" in exI)
                  apply (rule conjI)
                proof -
                  fix rnot lnot rnort lnort
                  assume rnort_dag: 
                    "Dag (repc (high no)) (repb \<propto> low) (repb \<propto> high) rnort"
                  assume lnort_dag: 
                    "Dag (repc (low no)) (repb \<propto> low) (repb \<propto> high) lnort"
                  assume rnort_in_repNodes: "set_of rnort \<subseteq> repb ` Nodes n ll"
                  assume lnort_in_repNodes: "set_of lnort \<subseteq> repb ` Nodes n ll"
                  from rnort_in_repNodes repbNodes_in_Nodes 
                  have rnort_in_Nodes: "set_of rnort \<subseteq> Nodes n ll"
                    by simp
                  from lnort_in_repNodes repbNodes_in_Nodes 
                  have lnort_in_Nodes: "set_of lnort \<subseteq> Nodes n ll"
                    by simp
                  from rnort_in_Nodes 
                  have rnortx_in_Nodes: "\<forall> x \<in> set_of rnort. x \<in> Nodes n ll"
                    by blast
                  with wf_ll nsll  
                  have "\<forall> x \<in> set_of rnort. x \<in> set_of pret \<and> var x < n"
                    apply -
                    apply (rule ballI)
                    apply (rule wf_ll_Nodes_pret)
                    apply (auto simp add: length_ll_eq)
                    done
                  with pret_dag prebdt_pret rnort_dag ord_pret wf_ll  nsll 
                    repbc_nc 
                  have "\<forall>x \<in> set_of rnort. (repc \<propto> low) x = (repb \<propto> low) x \<and> 
                    (repc \<propto> high) x = (repb \<propto> high) x"
                    apply -
                    apply (rule nort_null_comp)
                    apply (auto simp add: length_ll_eq)
                    done
                  then have "Dag (repc (high no)) (repc \<propto> low) (repc \<propto> high) rnort = 
                    Dag (repc (high no)) (repb \<propto> low) (repb \<propto> high) rnort" 
                    apply -
                    apply (rule heaps_eq_Dag_eq)
                    apply assumption
                    done
                  with rnort_dag 
                  have rnort_dag_repc: 
                    "Dag (repc (high no)) (repc \<propto> low) (repc \<propto> high) rnort" 
                    by simp
                  from lnort_in_Nodes 
                  have lnortx_in_Nodes: "\<forall>x \<in> set_of lnort. x \<in> Nodes n ll"
                    by blast
                  with wf_ll nsll  
                  have "\<forall> x \<in> set_of lnort. x \<in> set_of pret \<and> var x < n"
                    apply -
                    apply (rule ballI)
                    apply (rule wf_ll_Nodes_pret)
                    apply (auto simp add: length_ll_eq)
                    done
                  with pret_dag prebdt_pret lnort_dag ord_pret wf_ll  nsll 
                    repbc_nc 
                  have "\<forall> x \<in> set_of lnort. (repc \<propto> low) x = (repb \<propto> low) x \<and> 
                    (repc \<propto> high) x = (repb \<propto> high) x"
                    apply -
                    apply (rule nort_null_comp)
                    apply (auto simp add: length_ll_eq)
                    done
                  then have 
                    "Dag (repc (low no)) (repc \<propto> low) (repc \<propto> high) lnort = 
                    Dag (repc (low no)) (repb \<propto> low) (repb \<propto> high) lnort" 
                    apply -
                    apply (rule heaps_eq_Dag_eq)
                    apply assumption
                    done
                  with lnort_dag 
                  have lnort_dag_repc: 
                    "Dag (repc (low no)) (repc \<propto> low) (repc \<propto> high) lnort" 
                    by simp
                  from lno_nNull hno_nNull   
                  have propto_comp: "(repc \<propto> low) no = repc (low no) \<and> 
                    (repc \<propto> high) no = repc (high no)" 
                    by (simp add: null_comp_def)
                  from rno_in_llbn twonodes_in_llbn_prop rrno_eq_rno 
                  have "(repc \<propto> high) (repc no) = (repc \<propto> high) no \<and> 
                    (repc \<propto> low) (repc no) = (repc \<propto> low) no"
                    by simp
                  with propto_comp lnort_dag_repc rnort_dag_repc lno_nNull hno_nNull 
                    rnonN   
                  show "Dag(repc no)(repc \<propto> low)(repc \<propto> high)(Node lnort (repc no) rnort)"
                    by auto
                next
                  fix rnot lnot rnort lnort
                  assume rnot_dag: "Dag (high no) low high rnot"
                  assume lnot_dag: "Dag (low no) low high lnot"
                  with rnot_dag nonNull   
                  show "Dag no low high (Node lnot no rnot)" 
                    by simp
                next
                  fix rnort lnort
                  assume rnort_dag: 
                    "Dag (repc (high no)) (repb \<propto> low) (repb \<propto> high) rnort"
                  assume lnort_dag: 
                    "Dag (repc (low no)) (repb \<propto> low) (repb \<propto> high) lnort"
                  assume red_rnort: "reduced rnort"
                  assume red_lnort: " reduced lnort"
                  from rhn_nNull rnort_dag obtain lrnort rrnort where 
                    rnort_Node: "rnort = (Node lrnort (repc (high no)) rrnort)"
                    by auto
                  from rln_nNull lnort_dag obtain llnort rlnort where 
                    lnort_Node: "lnort = (Node llnort (repc (low no)) rlnort)"
                    by auto
                  from twonodes_in_llbn_prop rrno_eq_rno rno_in_llbn hno_nNull lno_nNull 
                  have "((repc \<propto> high) (repc no)) = repc (high no) \<and> 
                    ((repc \<propto> low) (repc no)) = repc (low no)"
                    apply -
                    apply (erule_tac x="repc no" in ballE)
                    apply (auto simp add: null_comp_def)
                    done
                  with share_case_cond 
                  have "((repc \<propto> high) (repc no)) \<noteq> ((repc \<propto> low) (repc no))"
                    by auto
                  with red_lnort red_rnort rnort_Node lnort_Node share_case_cond 
                  show "reduced (Node lnort (repc no) rnort)"
                    apply -
                    apply (rule_tac lp="repc (low no)" and rp="repc (high no)" and 
                      llt=llnort and rlt = rlnort and lrt=lrnort and rrt=rrnort 
                      in reduced_children_parent)
                    apply auto
                    done
                next
                  fix lnort rnort
                  assume lnort_dag: 
                    "Dag (repc (low no)) (repb \<propto> low) (repb \<propto> high) lnort"
                  assume ord_lnort: "ordered lnort var"
                  assume rnort_dag: 
                    "Dag (repc (high no)) (repb \<propto> low) (repb \<propto> high) rnort"
                  assume ord_rnort: " ordered rnort var"
                  assume lnort_in_repNodes: "set_of lnort \<subseteq> repb `Nodes n ll"
                  assume rnort_in_repNodes: "set_of rnort \<subseteq> repb `Nodes n ll"
                  from lnort_in_repNodes repbNodes_in_Nodes 
                  have lnort_in_Nodes: "set_of lnort \<subseteq> Nodes n ll"
                    by simp
                  from rnort_in_repNodes repbNodes_in_Nodes 
                  have rnort_in_Nodes: "set_of rnort \<subseteq> Nodes n ll"
                    by simp

                  from rhn_nNull rnort_dag obtain lrnort rrnort where 
                    rnort_Node: "rnort = (Node lrnort (repc (high no)) rrnort)"
                    by auto
                  from rln_nNull lnort_dag obtain llnort rlnort where 
                    lnort_Node: "lnort = (Node llnort (repc (low no)) rlnort)"
                    by auto
                  from lnort_dag rln_nNull lnort_in_Nodes 
                  have "repc (low no) \<in> set_of lnort" 
                    by auto
                  with lnort_in_Nodes 
                  have "repc (low no) \<in> Nodes n ll"
                    by blast
                  with wf_ll nsll  
                  have vrlno_sn: "var (repc (low no)) < n"
                    apply -
                    apply (drule wf_ll_Nodes_pret)
                    apply (auto simp add: length_ll_eq)
                    done
                  from rnort_dag rhn_nNull rnort_in_Nodes 
                  have "repc (high no) \<in> set_of rnort" 
                    by auto
                  with rnort_in_Nodes 
                  have "repc (high no) \<in> Nodes n ll"
                    by blast
                  with wf_ll nsll  have vrhno_sn: "var (repc (high no)) < n"
                    apply -
                    apply (drule wf_ll_Nodes_pret)
                    apply (auto simp add: length_ll_eq)
                    done
                  with varrepno_n vrlno_sn lnort_dag ord_lnort rnort_dag rnort_Node 
                    lnort_Node ord_rnort 
                  show "ordered (Node lnort (repc no) rnort) var"
                    by auto
                next
                  fix lnort rnort
                  assume lnort_in_Nodes: "set_of lnort \<subseteq> repb `Nodes n ll"
                  assume rnort_in_Nodes: "set_of rnort \<subseteq> repb `Nodes n ll"
                  from lnort_in_Nodes repbNodes_repcNodes 
                  have lnort_in_repcNodes: "set_of lnort \<subseteq> repc `Nodes n ll"
                    by simp
                  from rnort_in_Nodes repbNodes_repcNodes 
                  have rnort_in_repcNodes: "set_of rnort \<subseteq> repc `Nodes n ll"
                    by simp
                  have nNodessubset: "Nodes n ll \<subseteq> Nodes (n+1) ll"
                    by (simp add: Nodes_subset)
                  then have repc_Nodes_subset:
                    "repc `Nodes n ll \<subseteq> repc `Nodes (n+1) ll"
                    by blast
                  from no_in_Nodes have "repc no \<in> repc `Nodes (n+1) ll"
                    by blast
                  with repc_Nodes_subset lnort_in_repcNodes rnort_in_repcNodes 
                  show "set_of (Node lnort (repc no) rnort) \<subseteq> 
                    repc `Nodes (n + 1) ll"
                    apply simp
                    apply blast
                    done
                next
                  fix rnot lnot rnort lnort rnobdt lnobdt rnorbdt lnorbdt
                  assume lnobdt_def: " bdt lnot var = Some lnobdt"
                  assume rnobdt_def: " bdt rnot var = Some rnobdt"
                  assume rnorbdt_def: " bdt rnort var = Some rnorbdt"
                  assume cong_rno_rnor: " rnobdt \<sim> rnorbdt"
                  assume lnot_dag: "Dag (low no) low high lnot"
                  assume rnot_dag: "Dag (high no) low high rnot"
                  assume "\<not> Suc 0 < var no"
                  then have varnoseq1: "var no = 0 \<or> var no = 1" by auto
                  show "\<exists>nobdt. bdt (Node lnot no rnot) var = Some nobdt \<and> 
                    (\<exists>norbdt. bdt (Node lnort (repc no) rnort) var = Some norbdt \<and> 
                    nobdt \<sim> norbdt)"
                  proof (cases "var no = 0")
                    case True
                    note vnoNull=this
                    with pret_dag ord_pret no_in_pret lno_nNull hno_nNull  
                    show ?thesis
                      apply -
                      apply (drule var_ordered_children)
                      apply auto
                      done
                  next
                    assume "var no \<noteq> 0"
                    with varnoseq1 have vnoOne: "var no = 1" by simp
                    from pret_dag  ord_pret no_in_pret lno_nNull hno_nNull  
                      vnoOne 
                    have vlvrNull: "var (low no) = 0 \<and> var (high no) = 0"
                      apply -
                      apply (drule var_ordered_children)
                      apply auto
                      done
                    then have vlNull: "var (low no) = 0" by simp
                    from vlvrNull have vrNull: "var (high no) = 0" by simp
                    from lnobdt_def lnot_dag vlNull  lno_nNull 
                    have lnobdt_Zero: "lnobdt = Zero"
                      apply -
                      apply (drule bdt_Some_var0_Zero)
                      apply auto
                      done
                    from rnobdt_def rnot_dag vrNull  hno_nNull 
                    have rnobdt_Zero: "rnobdt = Zero"
                      apply -
                      apply (drule bdt_Some_var0_Zero)
                      apply auto
                      done
                    from lnobdt_Zero lnobdt_def 
                    have "bdt lnot var = Some Zero" by simp
                    with lnot_dag vlNull  
                    have lnot_Node: "lnot = (Node Tip (low no) Tip)"
                      by auto
                    from rnobdt_Zero rnobdt_def rnot_dag vrNull  
                    have rnot_Node: "rnot = (Node Tip (high no) Tip)" 
                      by auto
                    from pret_dag no_in_pret obtain not 
                      where not_ex: "Dag no low high not"
                      apply -
                      apply (drule dag_setof_exD)
                      apply auto
                      done
                    with pret_dag no_in_pret have not_ex_in_pret: "not <= pret" 
                      apply -
                      apply (rule set_of_subdag)
                      apply auto
                      done
                    from not_ex lnot_dag rnot_dag   nonNull 
                    have not_def: "not = (Node lnot no rnot)" 
                      by (simp add: Dag_unique del: Dag_Ref)
                    with not_ex_in_pret prebdt_pret 
                    have nobdt_ex: "\<exists> nobdt. bdt (Node lnot no rnot) var = Some nobdt"
                      apply -
                      apply (rule subbdt_ex)
                      apply auto
                      done
                    then obtain nobdt where 
                      nobdt_def: "bdt (Node lnot no rnot) var = Some nobdt" by auto
                    from not_def have "root not = no" by simp
                    with nobdt_def vnoOne not_def 
                    have "not = (Node Tip no Tip)"
                      apply -
                      apply (drule bdt_Some_var1_One)
                      apply auto
                      done
                    with not_def have "rnot = Tip" by simp
                    with rnot_Node show ?thesis by simp
                  qed
                next
                  fix lnot rnot lnobdt rnobdt
                  assume lnot_dag: "Dag (low no) low high lnot"
                  assume rnot_dag: " Dag (high no) low high rnot"
                  assume lnobdt_def: " bdt lnot var = Some lnobdt"
                  assume rnobdt_def: " bdt rnot var = Some rnobdt"
                  assume onesvarno: " Suc 0 < var no"
                  with rnobdt_def lnot_dag rnot_dag lnobdt_def 
                  show "bdt (Node lnot no rnot) var = 
                    Some (Bdt_Node lnobdt (var no) rnobdt)" by simp
                next
                  fix rnot lnot rnort lnort rnobdt lnobdt rnorbdt lnorbdt
                  assume rnort_dag: 
                    "Dag (repc (high no)) (repb \<propto> low) (repb \<propto> high) rnort"
                  assume lnort_dag: 
                    "Dag (repc (low no)) (repb \<propto> low) (repb \<propto> high) lnort"
                  assume rnorbdt_def: " bdt rnort var = Some rnorbdt"
                  assume lnorbdt_def: "bdt lnort var = Some lnorbdt"
                  assume varno_bOne: "Suc 0 < var no"
                  with varno have "Suc 0 < n" by simp
                  with varrepno_n have "Suc 0 < var (repc no)" by simp
                  with rnorbdt_def lnorbdt_def 
                  show "bdt (Node lnort (repc no) rnort) var = 
                    Some (Bdt_Node lnorbdt (var (repc no)) rnorbdt)"
                    by simp
                next
                  fix rnobdt lnobdt rnorbdt lnorbdt 
                  assume lcong_eval: "lnobdt \<sim> lnorbdt"
                  assume rcong_eval: " rnobdt \<sim> rnorbdt"
                  from varno varrepno_n have "var (repc no) = var no" by simp
                  with lcong_eval rcong_eval 
                  show "Bdt_Node lnobdt (var no) rnobdt \<sim> 
                    Bdt_Node lnorbdt (var (repc no)) rnorbdt"
                    apply (unfold cong_eval_def)
                    apply (rule ext)
                    by simp
                next
                  fix rnot lnot rnort lnort
                  assume lnort_repb: "\<forall>no\<in>set_of lnort. repb no = no"
                  assume rnort_repb: "\<forall>no\<in>set_of rnort. repb no = no"
                  assume rnort_in_repb_Nodesn: "set_of rnort \<subseteq> repb ` Nodes n ll"
                  assume lnort_in_repb_Nodesn: "set_of lnort \<subseteq> repb ` Nodes n ll"
                  from repbNodes_in_Nodes rnort_in_repb_Nodesn 
                  have rnort_in_Nodesn: "set_of rnort \<subseteq> Nodes n ll"
                    by blast
                  from repbNodes_in_Nodes lnort_in_repb_Nodesn 
                  have lnort_in_Nodesn: "set_of lnort \<subseteq> Nodes n ll"
                    by blast
                  have rnort_repc: "\<forall>no\<in>set_of rnort. repc no = no"
                  proof
                    fix pt
                    assume pt_in_rnort: " pt \<in> set_of rnort"
                    with rnort_in_Nodesn have "pt \<in> Nodes n ll" 
                      by blast
                    with Nodesn_notin_lln have "pt \<notin> set (ll ! n)"
                      by auto
                    with repbc_nc have "repb pt = repc pt"
                      by auto
                    with rnort_repb pt_in_rnort show "repc pt = pt"
                      by auto
                  qed
                  have lnort_repc: "\<forall>no\<in>set_of lnort. repc no = no"
                  proof
                    fix pt
                    assume pt_in_lnort: " pt \<in> set_of lnort"
                    with lnort_in_Nodesn have "pt \<in> Nodes n ll" 
                      by blast
                    with Nodesn_notin_lln have "pt \<notin> set (ll ! n)"
                      by auto
                    with repbc_nc have "repb pt = repc pt"
                      by auto
                    with lnort_repb pt_in_lnort show "repc pt = pt"
                      by auto
                  qed
                  show "\<forall>no\<in>set_of (Node lnort (repc no) rnort). repc no = no"
                  proof
                    fix pt
                    assume pt_in_rept: "pt \<in> set_of (Node lnort (repc no) rnort)"
                    show "repc pt = pt"
                    proof (cases "pt \<in> set_of lnort")
                      case True
                      with lnort_repc show ?thesis
                        by auto
                    next
                      assume pt_notin_lnort: "pt \<notin> set_of lnort"
                      show ?thesis
                      proof (cases "pt \<in> set_of rnort")
                        case True
                        with rnort_repc show ?thesis
                          by auto
                      next 
                        assume pt_notin_rnort: "pt \<notin> set_of rnort"
                        with pt_notin_lnort pt_in_rept have "pt = repc no"
                          by simp
                        with rrno_eq_rno show "repc pt = pt"
                          by simp
                      qed
                    qed
                  qed
                qed
                
                with varrep rrno_eq_rno show ?thesis by simp
              qed
            qed
            with rnonN show ?thesis by simp
          qed
        qed
        note while_while_prop=this
        from wf_ll nsll  
        have "\<forall>no \<in> Nodes n ll. no \<notin> set (ll ! n)"
          apply (simp add: Nodes_def length_ll_eq)
          apply clarify
          apply (drule no_in_one_ll)
          apply auto
          done
        with repbc_nc  have "\<forall>no \<in> Nodes n ll. repb no = repc no"
          apply -
          apply (rule ballI)
          apply (erule_tac x=no in allE)
          apply simp
          done
        then have repbNodes_repcNodes: 
          "repb `(Nodes n ll) = repc `(Nodes n ll)"
          apply -
          apply rule
          apply blast
          apply rule
          apply (erule imageE)
          apply (erule_tac x=xa in ballE)
          prefer 2
          apply simp
          apply rule
          apply auto
          done
        then have repcNodes_repbNodes: 
          "repc `(Nodes n ll) = repb `(Nodes n ll)"
          by simp
        have repbc_dags_eq: 
          "Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high) = 
          Dags (repb  ` Nodes n ll) (repb \<propto> low) (repb \<propto> high)"
          apply -
          apply rule
          apply rule
          apply (erule Dags.cases)
          apply (rule DagsI)
          prefer 4
          apply rule
          apply (erule Dags.cases)
          apply (rule DagsI)
        proof -
          fix x p t
          assume t_in_repcNodes: "set_of t \<subseteq> repc ` Nodes n ll"
          assume x_t: "x=t"
          with t_in_repcNodes repcNodes_repbNodes 
          show "set_of x \<subseteq> repb ` Nodes n ll" 
            by simp
        next
          fix x p t
          assume t_in_repcNodes: "set_of t \<subseteq> repc ` Nodes n ll"
          assume t_dag: "Dag p (repc \<propto> low) (repc \<propto> high) t"
          assume t_nTip: " t \<noteq> Tip"
          assume x_t: "x=t"
          from t_nTip t_dag have "p \<noteq> Null"
            apply -
            apply (case_tac "p=Null")
            apply auto
            done
          with t_nTip t_dag obtain lt rt where t_Node: "t=Node lt p rt"
            by auto
          from t_in_repcNodes t_dag t_nTip t_Node obtain q where 
            rq_p: "repc q = p" and q_in_Nodes: "q \<in> Nodes n ll"
            apply simp
            apply (elim conjE)
            apply (erule imageE)
            apply auto
            done
          from q_in_Nodes have "repb q = repc q"
            by (rule Nodes_n_rep_nc [rule_format])
          with rq_p have repbq_p: "repb q = p" by simp
          from q_in_Nodes 
          have "Dag (repb q) (repb \<propto> low) (repb \<propto> high) t = 
            Dag (repc q) (repc \<propto> low) (repc \<propto> high) t"
            by (rule Nodes_repbc_Dags_eq [rule_format])
          with t_dag rq_p have "Dag (repb q) (repb \<propto> low) (repb \<propto> high) t" by simp
          with repbq_p x_t show "Dag p (repb \<propto> low) (repb \<propto> high) x"
            by simp
        next
          fix x p t
          assume t_in_repcNodes: "set_of t \<subseteq> repb ` Nodes n ll"
          assume x_t: "x=t"
          with t_in_repcNodes repbNodes_repcNodes 
          show "set_of x \<subseteq> repc ` Nodes n ll" 
            by simp
        next
          fix x p t
          assume t_in_repcNodes: "set_of t \<subseteq> repb ` Nodes n ll"
          assume t_dag: "Dag p (repb \<propto> low) (repb \<propto> high) t"
          assume t_nTip: " t \<noteq> Tip"
          assume x_t: "x=t"
          from t_nTip t_dag have "p \<noteq> Null"
            apply -
            apply (case_tac "p=Null")
            apply auto
            done
          with t_nTip t_dag obtain lt rt where t_Node: "t=Node lt p rt"
            by auto
          from t_in_repcNodes t_dag t_nTip t_Node obtain q where 
            rq_p: "repb q = p" and q_in_Nodes: "q \<in> Nodes n ll"
            apply simp
            apply (elim conjE)
            apply (erule imageE)
            apply auto
            done
          from q_in_Nodes have "repb q = repc q"
            by (rule Nodes_n_rep_nc [rule_format])
          with rq_p have repbq_p: "repc q = p" by simp
          from q_in_Nodes 
          have "Dag (repb q) (repb \<propto> low) (repb \<propto> high) t = 
            Dag (repc q) (repc \<propto> low) (repc \<propto> high) t"
            by (rule Nodes_repbc_Dags_eq [rule_format])
          with t_dag rq_p have "Dag (repc q) (repc \<propto> low) (repc \<propto> high) t" by simp
          with repbq_p x_t show "Dag p (repc \<propto> low) (repc \<propto> high) x"
            by simp
        next
          fix x p and t :: "dag"
          assume x_t: "x = t"
          assume t_nTip: " t \<noteq> Tip"
          with x_t show "x\<noteq> Tip" by simp
        next
          fix x p and t :: "dag"
          assume x_t: "x = t"
          assume t_nTip: " t \<noteq> Tip"
          with x_t show "x\<noteq> Tip" by simp
        qed
        from pret_dag wf_ll nsll 
        have null_notin_Nodes_Suc_n: "Null \<notin> Nodes (Suc n) ll"
          by  - (rule Null_notin_Nodes,auto simp add: length_ll_eq)
        { fix t1 t2
          assume t1_in_DagsNodesn: 
            "t1 \<in> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
          assume t2_notin_DagsNodesn: 
            "t2 \<notin> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
          assume t2_in_DagsNodesSucn: 
            "t2 \<in> Dags (repc ` Nodes (Suc n) ll) (repc \<propto> low) (repc \<propto> high)"
          assume isomorphic_dags_eq_asm: 
            "\<forall>t1 t2. t1 \<in> Dags (repb ` Nodes n ll) (repb \<propto> low) (repb \<propto> high) 
            \<and> t2 \<in> Dags (repb ` Nodes n ll) (repb \<propto> low) (repb \<propto> high) 
            \<longrightarrow> isomorphic_dags_eq t1 t2 var"
          assume repbc_Dags: 
            "Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high) = 
            Dags (repb ` Nodes n ll) (repb \<propto> low) (repb \<propto> high)"
          from t1_in_DagsNodesn repbc_Dags 
          have t1_repb_subnode: 
            "t1 \<in> Dags (repb ` Nodes n ll) (repb \<propto> low) (repb \<propto> high)" 
            by simp
          from t2_in_DagsNodesSucn 
          have t2_in_DagsNodesSucn: 
            "t2 \<in> Dags (repc ` Nodes (Suc n) ll) (repc \<propto> low) (repc \<propto> high)" 
            by simp
          from repbNodes_in_Nodes repbNodes_repcNodes 
          have repcNodesn_in_Nodesn: "repc `Nodes n ll \<subseteq> Nodes n ll"
            by simp
          from t1_in_DagsNodesn obtain q where 
            Dag_q_Nodes_n: 
            "Dag (repc q) (repc \<propto> low) (repc \<propto> high) t1 \<and> q \<in> Nodes n ll"
          proof (elim Dags.cases)
            fix p t
            assume t1_t: "t1 = t"
            assume t_in_repcNodesn: "set_of t \<subseteq> repc ` Nodes n ll"
            assume t_dag: "Dag p (repc \<propto> low) (repc \<propto> high) t"
            assume t_nTip: " t \<noteq> Tip"
            assume obtain_prop: "\<And>q. Dag (repc q) (repc \<propto> low) (repc \<propto> high) t1 \<and> 
              q \<in> Nodes n ll \<Longrightarrow> ?thesis"
            from t_nTip t_dag have "p \<noteq> Null"
              apply -
              apply (case_tac "p=Null")
              apply auto
              done
            with t_nTip t_dag obtain lt rt where t_Node: "t=Node lt p rt"
              by auto
            from t_in_repcNodesn t_dag t_nTip t_Node obtain k where 
              rk_p: "repc k = p" and k_in_Nodes: "k \<in> Nodes n ll"
              apply simp
              apply (elim conjE)
              apply (erule imageE)
              apply auto
              done
            with t1_t t_dag obtain_prop rk_p k_in_Nodes show ?thesis
              by auto
          qed
          with wf_ll  nsll  have varq_sn: "(var q < n)"         
            apply (simp add: Nodes_def)
            apply (elim conjE)
            apply (erule exE)
            apply (simp add: wf_ll_def length_ll_eq)
            apply (elim conjE)
            apply (thin_tac " \<forall>q. q \<in> set_of pret \<longrightarrow> q \<in> set (ll ! var q)")
            apply (erule_tac x=x in allE)
            apply auto
            done
          from Dag_q_Nodes_n have q_in_Nodesn: "q \<in> Nodes n ll"
            by simp
          then have "\<exists> k<n. q \<in> set (ll ! k)"
            by (simp add: Nodes_def)
          with wf_ll nsll  have "q \<notin> set (ll ! n)"
            apply -
            apply (erule exE)
            apply (rule_tac i=k and j=n in no_in_one_ll)
            apply (auto simp add: length_ll_eq)
            done
          with repbc_nc  have repbc_q: "repc q = repb q"
            apply -
            apply (erule_tac x=q in allE)
            apply auto
            done
          from normalize_prop q_in_Nodesn have "var (repb q) <= var q"
            apply -
            apply (erule_tac x=q in ballE)
            apply auto
            done
          with repbc_q have var_repc_q: "var (repc q) <= var q"
            by simp
          with varq_sn have var_repc_q_n: "var (repc q) < n"
            by simp
          
          from Nodes_subset Dag_q_Nodes_n while_while_prop 
          have ord_t1_var_rep: "ordered t1 var \<and> var (repc q) <= var q" 
            apply (elim conjE)
            apply (erule_tac x=q in ballE)
            apply auto
            done
          then have ord_t1: "ordered t1 var" by simp
          from ord_t1_var_rep have varrep_q: "var (repc q) <= var q" by simp
          from t2_in_DagsNodesSucn have ord_t2: "ordered t2 var"
          proof (elim Dags.cases)
            fix p t
            assume t_in_repcNodes: "set_of t \<subseteq> repc ` Nodes (Suc n) ll"
            assume t_nTip: " t \<noteq> Tip"
            assume t2t: "t2 = t"
            assume t_dag: "Dag p (repc \<propto> low) (repc \<propto> high) t"
            from t_in_repcNodes have x_in_repcNodesSucn:  
              "\<forall>x. x \<in> set_of t \<longrightarrow> x \<in> repc ` Nodes (Suc n) ll" 
              apply -
              apply auto
              done
            from t_nTip t_dag have "p \<noteq> Null"
              apply -
              apply (case_tac "p=Null")
              apply auto
              done
            with t_nTip t_dag obtain lt rt where t_Node: "t=Node lt p rt"
              by auto
            then have "p \<in> set_of t"
              by auto
            with x_in_repcNodesSucn have "p \<in> repc ` Nodes (Suc n) ll"
              by simp
            then obtain a where repca_p: "p=repc a" and 
              a_in_NodesSucn: "a \<in> Nodes (Suc n) ll"
              by auto
            with repca_p while_while_prop t_dag t2t show ?thesis
              apply -
              apply (erule_tac x=a in ballE)
              apply (elim conjE exE)
              apply (subgoal_tac "nort = t") 
              prefer 2
              apply (simp add: Dag_unique)
              apply auto
              done
          qed
          from while_while_prop have while_prop_part: 
            "\<forall>no \<in> Nodes (Suc n) ll. 
            var (repc no) <= var no"
            by auto
          from while_while_prop have rep_rep_nort: 
            "\<forall>no\<in>Nodes (n + 1) ll. (\<exists>nort. Dag (repc no) (repc \<propto> low) (repc \<propto> high) nort \<and> 
            (\<forall>no\<in>set_of nort. repc no = no))"
            by auto
          from repcNodes_in_Nodes null_notin_Nodes_Suc_n 
          have "\<forall>no \<in> Nodes (n+1) ll. repc no \<noteq> Null"
            by auto
          with rep_rep_nort have "\<forall> no \<in> Nodes (n+1) ll. repc (repc no) = (repc no)"
            apply -
            apply (rule ballI)
            apply (erule_tac x=no in ballE)
            prefer 2
            apply simp
            apply (erule_tac x=no in ballE)
            apply (erule exE)
            apply (subgoal_tac "repc no \<in> set_of nort")
            apply (elim conjE)
            apply (erule_tac x="repc no" in ballE)
            apply simp
            apply simp
            apply (simp)
            apply (elim conjE)
            apply (thin_tac "\<forall>no\<in>set_of nort. repc no = no")
            apply auto
            done
          with t2_in_DagsNodesSucn t2_notin_DagsNodesn ord_t2 while_prop_part 
            wf_ll nsll  repcNodes_in_Nodes obtain a where
            t2_repc_dag: "Dag (repc a) (repc \<propto> low) (repc \<propto> high) t2" and
            a_in_lln: "a \<in> set (ll ! n)"
            apply -
            apply (drule restrict_root_Node)
            apply (auto simp add: length_ll_eq)
            done
          with wf_ll nsll  have a_in_pret: "a \<in> set_of pret" 
            by (simp add: wf_ll_def length_ll_eq)
          from wf_ll nsll  a_in_lln have vara_n: "var a = n" 
            by (simp add: wf_ll_def length_ll_eq)
          from a_in_lln rep_prop  obtain
            repp_nNull: " repc a \<noteq> Null" and
            repp_reduce: "(repc \<propto> low) a = (repc \<propto> high) a \<and> low a \<noteq> Null 
            \<longrightarrow> repc a = (repc \<propto> high) a" and
            repp_share: "((repc \<propto> low) a = (repc \<propto> high) a \<longrightarrow> low a = Null) 
            \<longrightarrow> repc a \<in> set (ll ! n) \<and>
            repc (repc a) = repc a \<and> 
            (\<forall>no1\<in>set (ll ! n). ((repc \<propto> high) no1 = (repc \<propto> high) a \<and> 
            (repc \<propto> low) no1 = (repc \<propto> low) a) = (repc a = repc no1))"
            using [[simp_depth_limit=4]]
            by auto
          from t2_repc_dag a_in_lln repp_nNull obtain lt2 rt2 where 
            t2_Node: "t2 = (Node lt2 (repc a) rt2)"
            by auto
          have "isomorphic_dags_eq t1 t2 var"
          proof (cases "(repc \<propto> low) a = (repc \<propto> high) a \<and> low a \<noteq> Null")
            case True
            note red=this
            then have red_case: "(repc \<propto> low) a = (repc \<propto> high) a"
              by simp
            from red have low_nNull: "low a \<noteq> Null"
              by simp
            with pret_dag prebdt_pret a_in_pret have highp_nNull: "high a \<noteq> Null" 
              apply -
              apply (drule balanced_bdt)
              apply auto
              done
            from pret_dag ord_pret a_in_pret low_nNull highp_nNull 
            have var_children_smaller: "var (low a) < var a \<and> var (high a) < var a"
              apply -
              apply (rule var_ordered_children)
              apply auto
              done
            from pret_dag a_in_pret have a_nNull: "a \<noteq> Null" 
              apply -
              apply (rule set_of_nn [rule_format])
              apply auto
              done
            with a_in_pret highp_nNull pret_dag have "high a \<in> set_of pret" 
              apply -
              apply (drule subelem_set_of_high)
              apply auto
              done
            with wf_ll have "high a \<in> set (ll ! (var (high a)))" 
              by (simp add: wf_ll_def)
            with a_in_lln t2_repc_dag var_children_smaller vara_n 
            have "\<exists> k<n. (high a) \<in> set (ll ! k)"
              by auto
            then have higha_in_Nodesn: "(high a) \<in> Nodes n ll"
              by (simp add: Nodes_def)
            then have rhigha_in_rNodesn: "repc (high a) \<in> repc ` Nodes n ll"
              by simp
            from higha_in_Nodesn normalize_prop obtain rt where 
              rt_dag:  "Dag (repb (high a)) (repb \<propto> low) (repb \<propto> high) rt" and
              rt_in_repbNort: "set_of rt \<subseteq> repb `Nodes n ll"
              apply -
              apply (erule_tac x="high a" in ballE)
              apply auto
              done
            from rt_in_repbNort repbNodes_repcNodes 
            have rt_in_repcNodesn: "set_of rt \<subseteq> repc `Nodes n ll"
              by blast
            from rt_dag higha_in_Nodesn 
            have repcrt_dag: "Dag (repc (high a)) (repc \<propto> low) (repc \<propto> high) rt"
              apply -
              apply (drule Nodes_repbc_Dags_eq [rule_format])
              apply auto
              done
            have rt_nTip: "rt \<noteq> Tip"
            proof -
              have "repc (high a) \<noteq> Null"
              proof -
                note rhigha_in_rNodesn
                also have "repc `Nodes n ll \<subseteq> repc `Nodes (Suc n) ll"
                  using Nodes_subset 
                  by blast
                also have "\<dots> \<subseteq> Nodes (Suc n) ll"
                  using repcNodes_in_Nodes
                  by simp
                finally show ?thesis
                  using null_notin_Nodes_Suc_n
                  by auto
              qed
              with repcrt_dag show ?thesis by auto
            qed
            from a_nNull a_in_pret low_nNull pret_dag have "low a \<in> set_of pret" 
              apply -
              apply (drule subelem_set_of_low)
              apply auto
              done
            with wf_ll have "low a \<in> set (ll ! (var (low a)))" 
              by (simp add: wf_ll_def)
            with a_in_lln t2_repc_dag var_children_smaller vara_n 
            have "\<exists>k<n. (low a) \<in> set (ll ! k)"
              by auto
            then have "(low a) \<in> Nodes n ll"
              by (simp add: Nodes_def)
            then have rlow_in_rNodesn: "repc (low a) \<in> repc ` Nodes n ll"
              by simp
            show ?thesis
            proof -
              from repp_reduce low_nNull  highp_nNull  red_case 
              have repc_p_def: "repc a = repc (high a)" 
                by (simp add: null_comp_def)
              with rt_in_repcNodesn repcrt_dag rhigha_in_rNodesn a_in_lln t2_repc_dag
                repc_p_def  rt_nTip 
              have t2_in_Dags_Nodesn: 
                "t2 \<in> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
                apply -
                apply (rule DagsI)
                apply simp
                apply (subgoal_tac "t2=rt")
                apply (auto simp add: Dag_unique)
                done
              from t1_in_DagsNodesn t2_in_Dags_Nodesn repbc_dags_eq isomorphic_dags_eq_asm 
              show shared_t1_t2: "isomorphic_dags_eq t1 t2 var"
                apply -
                apply (erule_tac x=t1 in allE)
                apply (erule_tac x=t2 in allE)
                apply simp
                done
            qed
          next
            assume share: " \<not> ((repc \<propto> low) a = (repc \<propto> high) a \<and> low a \<noteq> Null)"
            then
            have share: "(repc \<propto> low) a \<noteq> (repc \<propto> high) a \<or> low a = Null"
              using [[simp_depth_limit=1]]
              by simp
            with repp_share obtain 
              ra_in_llbn: "repc a \<in> set (ll ! n)" and 
              rra_ra: "repc (repc a) = repc a" and
              two_nodes_share: "(\<forall>no1\<in>set (ll ! n). 
              ((repc \<propto> high) no1 = (repc \<propto> high) a \<and> 
              (repc \<propto> low) no1 = (repc \<propto> low) a) = (repc a = repc no1))"
              using [[simp_depth_limit=3]]
              by simp
            from wf_ll ra_in_llbn  nsll have var_repc_a_n: "var (repc a) = n" 
              by (auto simp add: wf_ll_def length_ll_eq)
            show ?thesis
            proof (auto simp add: isomorphic_dags_eq_def)
              fix bdt1
              assume bdt_t1: "bdt t1 var = Some bdt1"
              assume bdt_t2: "bdt t2 var = Some bdt1"
              show "t1 = t2"
              proof (cases t1)
                case Tip
                with bdt_t1 show ?thesis
                  by simp
              next
                case (Node lt1 p1 rt1)
                note t1_Node=this
                with Dag_q_Nodes_n have "p1=(repc q)"
                  by simp
                with t2_Node bdt_t1 bdt_t2 t1_Node have "var (repc q) = var (repc a)"
                  apply -
                  apply (rule same_bdt_var)
                  apply auto
                  done
                with var_repc_q_n var_repc_a_n show ?thesis
                  by simp
              qed
            qed
          qed }
        note mixed_Dags_case = this
        from repbc_dags_eq isomorphic_dags_eq 
        have dags_shared: 
          "\<forall>t1 t2. t1 \<in> Dags (repc ` Nodes (Suc n) ll)(repc \<propto> low)(repc \<propto> high)\<and>
          t2 \<in> Dags (repc ` Nodes (Suc n) ll) (repc \<propto> low) (repc \<propto> high) 
          \<longrightarrow> isomorphic_dags_eq t1 t2 var"
          apply -
          apply (rule Dags_Nodes_cases)
          apply (rule isomorphic_dags_eq_sym)
        proof -
          fix t1 t2
          assume t1_in_Dagsn: 
            "t1 \<in> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
          assume t2_in_Dagsn: 
            "t2 \<in> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
          assume isomorphic_dags_eq_asm: 
            "\<forall>t1 t2. t1 \<in> Dags (repb ` Nodes n ll) (repb \<propto> low) (repb \<propto> high) \<and>
            t2 \<in> Dags (repb ` Nodes n ll) (repb \<propto> low) (repb \<propto> high) 
            \<longrightarrow> isomorphic_dags_eq t1 t2 var"
          assume repb_repc_Dags: 
            "Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high) = 
            Dags (repb ` Nodes n ll) (repb \<propto> low) (repb \<propto> high)"
          with t1_in_Dagsn t2_in_Dagsn isomorphic_dags_eq_asm 
          show "isomorphic_dags_eq t1 t2 var" by simp
        next
          fix t1 t2
          assume t1_in_DagsNodesn: 
            "t1 \<in> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
          assume t2_notin_DagsNodesn: 
            "t2 \<notin> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
          assume t2_in_DagsNodesSucn: 
            "t2 \<in> Dags (repc ` Nodes (Suc n) ll) (repc \<propto> low) (repc \<propto> high)"
          assume isomorphic_dags_eq_asm: 
            "\<forall>t1 t2. t1 \<in> Dags (repb ` Nodes n ll) (repb \<propto> low) (repb \<propto> high) \<and>
            t2 \<in> Dags (repb ` Nodes n ll) (repb \<propto> low) (repb \<propto> high) 
            \<longrightarrow> isomorphic_dags_eq t1 t2 var"
          assume repbc_Dags: 
            "Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high) = 
            Dags (repb ` Nodes n ll) (repb \<propto> low) (repb \<propto> high)"
          from t1_in_DagsNodesn t2_notin_DagsNodesn t2_in_DagsNodesSucn 
            isomorphic_dags_eq_asm repbc_Dags
          show "isomorphic_dags_eq t1 t2 var"
            apply -
            apply (rule mixed_Dags_case)
            apply auto
            done
        next
          fix t1 t2
          assume t1_in_DagsNodesSucn: 
            "t1 \<in> Dags (repc ` Nodes (Suc n) ll) (repc \<propto> low) (repc \<propto> high)"
          assume t1_notin_DagsNodesn: 
            "t1 \<notin> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
          assume t2_in_DagsNodesSucn: 
            "t2 \<in> Dags (repc ` Nodes (Suc n) ll) (repc \<propto> low) (repc \<propto> high)"
          assume t2_notin_DagsNodesn: 
            "t2 \<notin> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
          
          
            (* ab hier gehts um t1 *)
          from t1_in_DagsNodesSucn have ord_t1: "ordered t1 var"
          proof (elim Dags.cases)
            fix p t
            assume t_in_repcNodes: "set_of t \<subseteq> repc ` Nodes (Suc n) ll"
            assume t_nTip: " t \<noteq> Tip"
            assume t2t: "t1 = t"
            assume t_dag: "Dag p (repc \<propto> low) (repc \<propto> high) t"
            from t_in_repcNodes 
            have x_in_repcNodesSucn:  
              "\<forall> x. x \<in> set_of t \<longrightarrow> x \<in> repc ` Nodes (Suc n) ll" 
              apply -
              apply auto
              done
            from t_nTip t_dag have "p \<noteq> Null"
              apply -
              apply (case_tac "p=Null")
              apply auto
              done
            with t_nTip t_dag obtain lt rt where t_Node: "t=Node lt p rt"
              by auto
            then have "p \<in> set_of t"
              by auto
            with x_in_repcNodesSucn have "p \<in> repc ` Nodes (Suc n) ll"
              by simp
            then obtain a where 
              repca_p: "p=repc a" and a_in_NodesSucn: "a \<in> Nodes (Suc n) ll"
              by auto
            with repca_p while_while_prop t_dag t2t show ?thesis
              apply -
              apply (erule_tac x=a in ballE)
              apply (elim conjE exE)
              apply (subgoal_tac "nort = t") 
              prefer 2
              apply (simp add: Dag_unique)
              apply auto
              done
          qed
          from while_while_prop 
          have while_prop_part: "\<forall>no \<in> Nodes (Suc n) ll. 
            var (repc no) <= var no"
            by auto
          from while_while_prop have rep_rep_nort: 
            "\<forall>no\<in>Nodes (n + 1) ll. 
               (\<exists>nort. Dag (repc no) (repc \<propto> low) (repc \<propto> high) nort \<and> 
               (\<forall>no\<in>set_of nort. repc no = no))"
            by auto
          from repcNodes_in_Nodes null_notin_Nodes_Suc_n 
          have "\<forall> no \<in> Nodes (n+1) ll. repc no \<noteq> Null"
            by auto
          with rep_rep_nort 
          have rep_rep_no:  "\<forall>no \<in> Nodes (n+1) ll. repc (repc no) = (repc no)"
            apply -
            apply (rule ballI)
            apply (erule_tac x=no in ballE)
            prefer 2
            apply simp
            apply (erule_tac x=no in ballE)
            apply (erule exE)
            apply (subgoal_tac "repc no \<in> set_of nort")
            apply (elim conjE)
            apply (erule_tac x="repc no" in ballE)
            apply simp
            apply simp
            apply (simp)
            apply (elim conjE)
            apply (thin_tac "\<forall>no\<in>set_of nort. repc no = no")
            apply auto
            done
          with t1_in_DagsNodesSucn t1_notin_DagsNodesn ord_t1 while_prop_part wf_ll 
            nsll  repcNodes_in_Nodes obtain a1 where
            t1_repc_dag: "Dag (repc a1) (repc \<propto> low) (repc \<propto> high) t1" and
            a1_in_lln: "a1 \<in> set (ll ! n)"
            apply -
            apply (drule restrict_root_Node)
            apply (auto simp add: length_ll_eq)
            done
          with wf_ll nsll  have a1_in_pret: "a1 \<in> set_of pret" 
            by (simp add: wf_ll_def length_ll_eq)
          from wf_ll nsll  a1_in_lln have vara1_n: "var a1 = n" 
            by (simp add: wf_ll_def length_ll_eq)
          from a1_in_lln rep_prop  obtain
            repa1_nNull: " repc a1 \<noteq> Null" and
            repa1_reduce: "(repc \<propto> low) a1 = (repc \<propto> high) a1 \<and> low a1 \<noteq> Null 
            \<longrightarrow> repc a1 = (repc \<propto> high) a1" and
            repa1_share: "((repc \<propto> low) a1 = (repc \<propto> high) a1 \<longrightarrow> low a1 = Null) 
            \<longrightarrow> repc a1 \<in> set (ll ! n) \<and> repc (repc a1) = repc a1 \<and> 
            (\<forall>no1\<in>set (ll ! n). ((repc \<propto> high) no1 = (repc \<propto> high) a1 \<and> 
            (repc \<propto> low) no1 = (repc \<propto> low) a1) = (repc a1 = repc no1))"
            using [[simp_depth_limit=4]]
            by auto
          from t1_repc_dag a1_in_lln repa1_nNull obtain lt1 rt1 where 
            t1_Node: "t1 = (Node lt1 (repc a1) rt1)"
            by auto



              (* ab hier gehts um t2 *)
          from t2_in_DagsNodesSucn have ord_t2: "ordered t2 var"
          proof (elim Dags.cases)
            fix p t
            assume t_in_repcNodes: "set_of t \<subseteq> repc ` Nodes (Suc n) ll"
            assume t_nTip: " t \<noteq> Tip"
            assume t2t: "t2 = t"
            assume t_dag: "Dag p (repc \<propto> low) (repc \<propto> high) t"
            from t_in_repcNodes 
            have x_in_repcNodesSucn:  
              "\<forall> x. x \<in> set_of t \<longrightarrow> x \<in> repc ` Nodes (Suc n) ll" 
              apply -
              apply auto
              done
            from t_nTip t_dag have "p \<noteq> Null"
              apply -
              apply (case_tac "p=Null")
              apply auto
              done
            with t_nTip t_dag obtain lt rt where t_Node: "t=Node lt p rt"
              by auto
            then have "p \<in> set_of t"
              by auto
            with x_in_repcNodesSucn have "p \<in> repc ` Nodes (Suc n) ll"
              by simp
            then obtain a where 
              repca_p: "p=repc a" and a_in_NodesSucn: "a \<in> Nodes (Suc n) ll"
              by auto
            with repca_p while_while_prop t_dag t2t show ?thesis
              apply -
              apply (erule_tac x=a in ballE)
              apply (elim conjE exE)
              apply (subgoal_tac "nort = t") 
              prefer 2
              apply (simp add: Dag_unique)
              apply auto
              done
          qed
          from rep_rep_no t2_in_DagsNodesSucn t2_notin_DagsNodesn ord_t2 while_prop_part wf_ll 
            nsll  repcNodes_in_Nodes obtain a2 where
            t2_repc_dag: "Dag (repc a2) (repc \<propto> low) (repc \<propto> high) t2" and
            a2_in_lln: "a2 \<in> set (ll ! n)"
            apply -
            apply (drule restrict_root_Node)
            apply (auto simp add: length_ll_eq)
            done
          with wf_ll nsll  have a2_in_pret: "a2 \<in> set_of pret" 
            by (simp add: wf_ll_def length_ll_eq)
          from wf_ll nsll  a2_in_lln have vara2_n: "var a2 = n" 
            by (simp add: wf_ll_def length_ll_eq)
          from a2_in_lln rep_prop  obtain
            repa2_nNull: " repc a2 \<noteq> Null" and
            repa2_reduce: "(repc \<propto> low) a2 = (repc \<propto> high) a2 \<and> low a2 \<noteq> Null 
            \<longrightarrow> repc a2 = (repc \<propto> high) a2" and
            repa2_share: "((repc \<propto> low) a2 = (repc \<propto> high) a2 \<longrightarrow> low a2 = Null) 
            \<longrightarrow> repc a2 \<in> set (ll ! n) \<and> repc (repc a2) = repc a2 \<and> 
            (\<forall>no1\<in>set (ll ! n). ((repc \<propto> high) no1 = (repc \<propto> high) a2 \<and> 
            (repc \<propto> low) no1 = (repc \<propto> low) a2) = (repc a2 = repc no1))"
            using [[simp_depth_limit = 4]]
            by auto
          from t2_repc_dag a2_in_lln repa2_nNull obtain lt2 rt2 where 
            t2_Node: "t2 = (Node lt2 (repc a2) rt2)"
            by auto
          show "isomorphic_dags_eq t1 t2 var"
          proof (cases "(repc \<propto> low) a1 = (repc \<propto> high) a1 \<and> low a1 \<noteq> Null")
            case True
            note t1_red_cond=this              
            with t1_red_cond have t1_red_case: "(repc \<propto> low) a1 = (repc \<propto> high) a1"
              by simp
            from t1_red_cond have lowa1_nNull: "low a1 \<noteq> Null"
              by simp
            with pret_dag prebdt_pret a1_in_pret have higha1_nNull: "high a1 \<noteq> Null" 
              apply -
              apply (drule balanced_bdt)
              apply auto
              done
            from pret_dag ord_pret a1_in_pret lowa1_nNull higha1_nNull 
            have var_children_smaller_a1: "var (low a1) < var a1 \<and> var (high a1) < var a1"
              apply -
              apply (rule var_ordered_children)
              apply auto
              done
            from pret_dag a1_in_pret have a1_nNull: "a1 \<noteq> Null" 
              apply -
              apply (rule set_of_nn [rule_format])
              apply auto
              done
            with a1_in_pret higha1_nNull pret_dag have "high a1 \<in> set_of pret" 
              apply -
              apply (drule subelem_set_of_high)
              apply auto
              done
            with wf_ll have "high a1 \<in> set (ll ! (var (high a1)))" 
              by (simp add: wf_ll_def)
            with a1_in_lln t1_repc_dag var_children_smaller_a1 vara1_n 
            have "\<exists>k<n. (high a1) \<in> set (ll ! k)"
              by auto
            then have higha1_in_Nodesn: "(high a1) \<in> Nodes n ll"
              by (simp add: Nodes_def)
            then have rhigha1_in_rNodesn: "repc (high a1) \<in> repc ` Nodes n ll"
              by simp
            from higha1_in_Nodesn normalize_prop obtain rt1 where 
              rt1_dag:  "Dag (repb (high a1)) (repb \<propto> low) (repb \<propto> high) rt1" and
              rt1_in_repbNort: "set_of rt1 \<subseteq> repb `Nodes n ll"
              apply -
              apply (erule_tac x="high a1" in ballE)
              apply auto
              done
            from rt1_in_repbNort repbNodes_repcNodes 
            have rt1_in_repcNodesn: "set_of rt1 \<subseteq> repc `Nodes n ll"
              by blast
            from rt1_dag higha1_in_Nodesn 
            have repcrt1_dag: "Dag (repc (high a1)) (repc \<propto> low) (repc \<propto> high) rt1"
              apply -
              apply (drule Nodes_repbc_Dags_eq [rule_format])
              apply auto
              done
            have rt1_nTip: "rt1 \<noteq> Tip"
            proof -
              have "repc (high a1) \<noteq> Null"
              proof -
                note rhigha1_in_rNodesn
                also have "repc `Nodes n ll \<subseteq> repc `Nodes (Suc n) ll"
                  using Nodes_subset 
                  by blast
                also have "\<dots> \<subseteq> Nodes (Suc n) ll"
                  using repcNodes_in_Nodes
                  by simp
                finally show ?thesis
                  using null_notin_Nodes_Suc_n
                  by auto
              qed
              with repcrt1_dag show ?thesis by auto
            qed
            from repa1_reduce lowa1_nNull  higha1_nNull  t1_red_case 
            have repc_a1_def: "repc a1 = repc (high a1)" 
              by (simp add: null_comp_def)
            with rt1_in_repcNodesn repcrt1_dag rhigha1_in_rNodesn a1_in_lln 
              t1_repc_dag repc_a1_def  rt1_nTip 
            have t1_in_Dags_Nodesn: 
              "t1 \<in> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
              apply -
              apply (rule DagsI)
              apply simp
              apply (subgoal_tac "t1=rt1")
              apply (auto simp add: Dag_unique)
              done
            show ?thesis
            proof (cases "(repc \<propto> low) a2 = (repc \<propto> high) a2 \<and> low a2 \<noteq> Null")
              case True
              note t2_red_cond=this              
              with t2_red_cond have t2_red_case: "(repc \<propto> low) a2 = (repc \<propto> high) a2"
                by simp
              from t2_red_cond have lowa2_nNull: "low a2 \<noteq> Null"
                by simp
              with pret_dag prebdt_pret a2_in_pret have higha2_nNull: "high a2 \<noteq> Null" 
                apply -
                apply (drule balanced_bdt)
                apply auto
                done
              from pret_dag ord_pret a2_in_pret lowa2_nNull higha2_nNull 
              have var_children_smaller_a2: 
                "var (low a2) < var a2 \<and> var (high a2) < var a2"
                apply -
                apply (rule var_ordered_children)
                apply auto
                done
              from pret_dag a2_in_pret have a2_nNull: "a2 \<noteq> Null" 
                apply -
                apply (rule set_of_nn [rule_format])
                apply auto
                done
              with a2_in_pret higha2_nNull pret_dag have "high a2 \<in> set_of pret" 
                apply -
                apply (drule subelem_set_of_high)
                apply auto
                done
              with wf_ll have "high a2 \<in> set (ll ! (var (high a2)))" 
                by (simp add: wf_ll_def)
              with a2_in_lln t2_repc_dag var_children_smaller_a2 vara2_n 
              have "\<exists> k<n. (high a2) \<in> set (ll ! k)"
                by auto
              then have higha2_in_Nodesn: "(high a2) \<in> Nodes n ll"
                by (simp add: Nodes_def)
              then have rhigha2_in_rNodesn: "repc (high a2) \<in> repc ` Nodes n ll"
                by simp
              from higha2_in_Nodesn normalize_prop obtain rt2 where 
                rt2_dag:  "Dag (repb (high a2)) (repb \<propto> low) (repb \<propto> high) rt2" and
                rt2_in_repbNort: "set_of rt2 \<subseteq> repb `Nodes n ll"
                apply -
                apply (erule_tac x="high a2" in ballE)
                apply auto
                done
              from rt2_in_repbNort repbNodes_repcNodes 
              have rt2_in_repcNodesn: "set_of rt2 \<subseteq> repc `Nodes n ll"
                by blast
              from rt2_dag higha2_in_Nodesn 
              have repcrt2_dag: "Dag (repc (high a2)) (repc \<propto> low) (repc \<propto> high) rt2"
                apply -
                apply (drule Nodes_repbc_Dags_eq [rule_format])
                apply auto
                done
              have rt2_nTip: "rt2 \<noteq> Tip"
              proof -
                have "repc (high a2) \<noteq> Null"
                proof -
                  note rhigha2_in_rNodesn
                  also have "repc `Nodes n ll \<subseteq> repc `Nodes (Suc n) ll"
                    using Nodes_subset 
                    by blast
                  also have "\<dots> \<subseteq> Nodes (Suc n) ll"
                    using repcNodes_in_Nodes
                    by simp
                  finally show ?thesis
                    using null_notin_Nodes_Suc_n
                    by auto
                qed
                with repcrt2_dag show ?thesis by auto
              qed
              from repa2_reduce lowa2_nNull  higha2_nNull  t2_red_case 
              have repc_a2_def: "repc a2 = repc (high a2)" 
                by (simp add: null_comp_def)
              with rt2_in_repcNodesn repcrt2_dag rhigha2_in_rNodesn a2_in_lln 
                t2_repc_dag repc_a2_def  rt2_nTip 
              have t2_in_Dags_Nodesn: 
                "t2 \<in> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
                apply -
                apply (rule DagsI)
                apply simp
                apply (subgoal_tac "t2=rt2")
                apply (auto simp add: Dag_unique)
                done
              from isomorphic_dags_eq t1_in_Dags_Nodesn t2_in_Dags_Nodesn repbc_dags_eq 
              show ?thesis
                by auto
            next
              assume t2_share_cond: 
                "\<not> ((repc \<propto> low) a2 = (repc \<propto> high) a2 \<and> low a2 \<noteq> Null)"
              from t1_in_Dags_Nodesn t2_notin_DagsNodesn t2_in_DagsNodesSucn 
                isomorphic_dags_eq repbc_dags_eq
              show ?thesis
                apply -
                apply (rule mixed_Dags_case)
                apply auto
                done
            qed
          next
            assume t1_share_cond: 
              "\<not>((repc \<propto> low) a1 = (repc \<propto> high) a1 \<and> low a1 \<noteq> Null)"
            with repa1_share obtain
              repca1_in_llbn: "repc a1 \<in> set (ll ! n)" and 
              reprepa1: "repc (repc a1) = repc a1" and
              twonodes_llbn_a1: 
              "(\<forall>no1\<in>set (ll ! n). ((repc \<propto> high) no1 = (repc \<propto> high) a1 \<and> 
              (repc \<propto> low) no1 = (repc \<propto> low) a1) = (repc a1 = repc no1))"
              using [[simp_depth_limit=2]]
              by auto
            show ?thesis
            proof (cases "(repc \<propto> low) a2 = (repc \<propto> high) a2 \<and> low a2 \<noteq> Null")
              case True
              note t2_red_cond=this              
              with t2_red_cond have t2_red_case: "(repc \<propto> low) a2 = (repc \<propto> high) a2"
                by simp
              from t2_red_cond have lowa2_nNull: "low a2 \<noteq> Null"
                by simp
              with pret_dag prebdt_pret a2_in_pret have higha2_nNull: "high a2 \<noteq> Null" 
                apply -
                apply (drule balanced_bdt)
                apply auto
                done
              from pret_dag ord_pret a2_in_pret lowa2_nNull higha2_nNull 
              have var_children_smaller_a2: 
                "var (low a2) < var a2 \<and> var (high a2) < var a2"
                apply -
                apply (rule var_ordered_children)
                apply auto
                done
              from pret_dag a2_in_pret have a2_nNull: "a2 \<noteq> Null" 
                apply -
                apply (rule set_of_nn [rule_format])
                apply auto
                done
              with a2_in_pret higha2_nNull pret_dag have "high a2 \<in> set_of pret" 
                apply -
                apply (drule subelem_set_of_high)
                apply auto
                done
              with wf_ll 
              have "high a2 \<in> set (ll ! (var (high a2)))" 
                by (simp add: wf_ll_def)
              with a2_in_lln t2_repc_dag var_children_smaller_a2 vara2_n 
              have "\<exists> k<n. (high a2) \<in> set (ll ! k)"
                by auto
              then have higha2_in_Nodesn: "(high a2) \<in> Nodes n ll"
                by (simp add: Nodes_def)
              then have rhigha2_in_rNodesn: "repc (high a2) \<in> repc ` Nodes n ll"
                by simp
              from higha2_in_Nodesn normalize_prop obtain rt2 where 
                rt2_dag:  "Dag (repb (high a2)) (repb \<propto> low) (repb \<propto> high) rt2" and
                rt2_in_repbNort: "set_of rt2 \<subseteq> repb `Nodes n ll"
                apply -
                apply (erule_tac x="high a2" in ballE)
                apply auto
                done
              from rt2_in_repbNort repbNodes_repcNodes 
              have rt2_in_repcNodesn: "set_of rt2 \<subseteq> repc `Nodes n ll"
                by blast
              from rt2_dag higha2_in_Nodesn 
              have repcrt2_dag: "Dag (repc (high a2)) (repc \<propto> low) (repc \<propto> high) rt2"
                apply -
                apply (drule Nodes_repbc_Dags_eq [rule_format])
                apply auto
                done
              have rt2_nTip: "rt2 \<noteq> Tip"
              proof -
                have "repc (high a2) \<noteq> Null"
                proof -
                  note rhigha2_in_rNodesn
                  also have "repc `Nodes n ll \<subseteq> repc `Nodes (Suc n) ll"
                    using Nodes_subset 
                    by blast
                  also have "\<dots> \<subseteq> Nodes (Suc n) ll"
                    using repcNodes_in_Nodes
                    by simp
                  finally show ?thesis
                    using null_notin_Nodes_Suc_n
                    by auto
                qed
                with repcrt2_dag show ?thesis by auto
              qed
              from repa2_reduce lowa2_nNull  higha2_nNull  t2_red_case 
              have repc_a2_def: "repc a2 = repc (high a2)" 
                by (simp add: null_comp_def)
              with rt2_in_repcNodesn repcrt2_dag rhigha2_in_rNodesn a2_in_lln 
                t2_repc_dag repc_a2_def  rt2_nTip 
              have t2_in_Dags_Nodesn: 
                "t2 \<in> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
                apply -
                apply (rule DagsI)
                apply simp
                apply (subgoal_tac "t2=rt2")
                apply (auto simp add: Dag_unique)
                done
              from t2_in_Dags_Nodesn t1_notin_DagsNodesn t1_in_DagsNodesSucn 
                isomorphic_dags_eq repbc_dags_eq 
              have "isomorphic_dags_eq t2 t1 var"
                apply -
                apply (rule mixed_Dags_case)
                apply auto
                done
              then show ?thesis
                by (simp add: isomorphic_dags_eq_sym)
            next
              assume t2_shared_cond: 
                "\<not> ((repc \<propto> low) a2 = (repc \<propto> high) a2 \<and> low a2 \<noteq> Null)"
              with repa2_share obtain
                repca2_in_llbn: "repc a2 \<in> set (ll ! n)" and 
                reprepa2: "repc (repc a2) = repc a2" and
                twonodes_llbn_a2: "(\<forall>no1\<in>set (ll ! n). 
                ((repc \<propto> high) no1 = (repc \<propto> high) a2 \<and> 
                (repc \<propto> low) no1 = (repc \<propto> low) a2) = (repc a2 = repc no1))"
                using [[simp_depth_limit=2]]
                by auto 
              from twonodes_llbn_a2 a1_in_lln  
              have share_a1_a2: 
                "((repc \<propto> high) a1 = (repc \<propto> high) a2 \<and> 
                (repc \<propto> low) a1 = (repc \<propto> low) a2) = (repc a2 = repc a1)"
                by auto
              from twonodes_llbn_a1 repca1_in_llbn reprepa1   
              have children_repc_eq_a1: "(repc \<propto> high) (repc a1) = (repc \<propto> high) a1 \<and> 
                (repc \<propto> low) (repc a1) = (repc \<propto> low) a1"
                by auto
              from twonodes_llbn_a2 repca2_in_llbn reprepa2  
              have children_repc_eq_a2: "(repc \<propto> high) (repc a2) = (repc \<propto> high) a2 \<and> 
                (repc \<propto> low) (repc a2) = (repc \<propto> low) a2"
                by auto
              from  t1_Node t2_Node show ?thesis
              proof (clarsimp simp add: isomorphic_dags_eq_def)
                fix bdt1
                assume t1_bdt: "bdt (Node lt1 (repc a1) rt1) var = Some bdt1"
                assume t2_bdt: "bdt (Node lt2 (repc a2) rt2) var = Some bdt1"
                show "lt1 = lt2 \<and> repc a1 = repc a2 \<and> rt1 = rt2"
                proof (cases bdt1)
                  case Zero
                  with t1_bdt t1_Node obtain
                    lt1_Tip: "lt1 = Tip" and
                    rt1_Tip: "rt1 = Tip"
                    by simp
                  from Zero t2_bdt t2_Node obtain 
                    lt2_Tip: "lt2 = Tip" and
                    rt2_Tip: "rt2 = Tip"
                    by simp
                  from t1_repc_dag t1_Node lt1_Tip have "(repc \<propto> low) (repc a1) = Null" 
                    by simp
                  with children_repc_eq_a1  
                  have repc_low_a1_Null: "(repc \<propto> low) a1 = Null"
                    by simp
                  from t1_repc_dag t1_Node rt1_Tip 
                  have "(repc \<propto> high) (repc a1) = Null"
                    by simp
                  with children_repc_eq_a1  
                  have repc_high_a1_Null: "(repc \<propto> high) a1 = Null"
                    by simp
                  from t2_repc_dag t2_Node lt2_Tip have "(repc \<propto> low) (repc a2) = Null" 
                    by simp
                  with children_repc_eq_a2  
                  have repc_low_a2_Null: "(repc \<propto> low) a2 = Null"
                    by simp
                  from t2_repc_dag t2_Node rt2_Tip 
                  have "(repc \<propto> high) (repc a2) = Null"
                    by simp
                  with children_repc_eq_a2  
                  have repc_high_a2_Null: "(repc \<propto> high) a2 = Null"
                    by simp
                  with share_a1_a2   repc_low_a1_Null repc_high_a1_Null 
                    repc_low_a2_Null repc_high_a2_Null
                  have "repc a2 = repc a1"
                    by auto
                  with lt1_Tip rt1_Tip lt2_Tip rt2_Tip show ?thesis
                    by auto
                next
                  case One
                  with t1_bdt t1_Node obtain
                    lt1_Tip: "lt1 = Tip" and
                    rt1_Tip: "rt1 = Tip"
                    by simp
                  from One t2_bdt t2_Node obtain 
                    lt2_Tip: "lt2 = Tip" and
                    rt2_Tip: "rt2 = Tip"
                    by simp
                  from t1_repc_dag t1_Node lt1_Tip have "(repc \<propto> low) (repc a1) = Null" 
                    by simp
                  with children_repc_eq_a1  
                  have repc_low_a1_Null: "(repc \<propto> low) a1 = Null"
                    by simp
                  from t1_repc_dag t1_Node rt1_Tip have "(repc \<propto> high) (repc a1) = Null"
                    by simp
                  with children_repc_eq_a1  
                  have repc_high_a1_Null: "(repc \<propto> high) a1 = Null"
                    by simp
                  from t2_repc_dag t2_Node lt2_Tip have "(repc \<propto> low) (repc a2) = Null" 
                    by simp
                  with children_repc_eq_a2  
                  have repc_low_a2_Null: "(repc \<propto> low) a2 = Null"
                    by simp
                  from t2_repc_dag t2_Node rt2_Tip have "(repc \<propto> high) (repc a2) = Null"
                    by simp
                  with children_repc_eq_a2  
                  have repc_high_a2_Null: "(repc \<propto> high) a2 = Null"
                    by simp
                  with share_a1_a2   repc_low_a1_Null repc_high_a1_Null 
                    repc_low_a2_Null repc_high_a2_Null
                  have "repc a2 = repc a1"
                    by auto
                  with lt1_Tip rt1_Tip lt2_Tip rt2_Tip show ?thesis
                    by auto
                next
                  case (Bdt_Node lbdt v rbdt)
                  note bdt_Node_case=this
                  with t1_bdt t1_Node obtain
                    lbdt_def_lt1: "bdt lt1 var = Some lbdt" and
                    rbdt_def_rt1: "bdt rt1 var = Some rbdt"
                    by auto
                  from t2_bdt bdt_Node_case t2_Node obtain
                    lbdt_def_lt2: "bdt lt2 var = Some lbdt" and
                    rbdt_def_rt2: "bdt rt2 var = Some rbdt"
                    by auto
                  from lbdt_def_lt1 t1_Node t1_repc_dag children_repc_eq_a1  
                  have "(repc \<propto> low) a1 \<noteq> Null"
                    by auto
                  then have low_a1_nNull: "(low a1) \<noteq> Null" 
                    by (auto simp: null_comp_def)
                  from rbdt_def_rt1 t1_Node t1_repc_dag children_repc_eq_a1  
                  have "(repc \<propto> high) a1 \<noteq> Null"
                    by auto
                  then have high_a1_nNull: "(high a1) \<noteq> Null" 
                    by (auto simp: null_comp_def)
                  from lbdt_def_lt2 t2_Node t2_repc_dag children_repc_eq_a2  
                  have "(repc \<propto> low) a2 \<noteq> Null"
                    by auto
                  then have low_a2_nNull: "(low a2) \<noteq> Null" 
                    by (auto simp: null_comp_def)
                  from rbdt_def_rt2 t2_Node t2_repc_dag children_repc_eq_a2  
                  have "(repc \<propto> high) a2 \<noteq> Null"
                    by auto
                  then have high_a2_nNull: "(high a2) \<noteq> Null" 
                    by (auto simp: null_comp_def)

                      (*hier gehts um t1*)
                  from pret_dag ord_pret a1_in_pret low_a1_nNull high_a1_nNull 
                  have var_children_smaller_a1: 
                    "var (low a1) < var a1 \<and> var (high a1) < var a1"
                    apply -
                    apply (rule var_ordered_children)
                    apply auto
                    done
                  from pret_dag a1_in_pret have a1_nNull: "a1 \<noteq> Null" 
                    apply -
                    apply (rule set_of_nn [rule_format])
                    apply auto
                    done
                  
                      (*hier gehts um rt1 *)
                  with a1_in_pret high_a1_nNull pret_dag have "high a1 \<in> set_of pret" 
                    apply -
                    apply (drule subelem_set_of_high)
                    apply auto
                    done
                  with wf_ll 
                  have "high a1 \<in> set (ll ! (var (high a1)))" 
                    by (simp add: wf_ll_def)
                  with a1_in_lln t1_repc_dag var_children_smaller_a1 vara1_n 
                  have "\<exists> k<n. (high a1) \<in> set (ll ! k)"
                    by auto
                  then have higha1_in_Nodesn: "(high a1) \<in> Nodes n ll"
                    by (simp add: Nodes_def)
                  then have rhigha1_in_rNodesn: 
                    "repc (high a1) \<in> repc ` Nodes n ll"
                    by simp
                  from higha1_in_Nodesn normalize_prop obtain rt1h where
                    rt1_dag:  "Dag (repb (high a1)) (repb \<propto> low) (repb \<propto> high) rt1h" and
                    rt1_in_repbNort: "set_of rt1h \<subseteq> repb `Nodes n ll"
                    apply -
                    apply (erule_tac x="high a1" in ballE)
                    apply auto
                    done
                  from rt1_in_repbNort repbNodes_repcNodes 
                  have rt1_in_repcNodesn: "set_of rt1h \<subseteq> repc `Nodes n ll"
                    by blast
                  from rt1_dag higha1_in_Nodesn 
                  have repcrt1_dag: 
                    "Dag (repc (high a1)) (repc \<propto> low) (repc \<propto> high) rt1h"
                    apply -
                    apply (drule Nodes_repbc_Dags_eq [rule_format])
                    apply auto
                    done
                  from t1_Node t1_repc_dag high_a1_nNull children_repc_eq_a1 
                  have "Dag (repc (high a1)) (repc \<propto> low) (repc \<propto> high) rt1"
                    by (auto simp add: null_comp_def)
                  with repcrt1_dag have rt1h_rt1: "rt1h = rt1" by (simp add: Dag_unique)
                  have rt1_nTip: "rt1 \<noteq> Tip"
                  proof -
                    have "repc (high a1) \<noteq> Null"
                    proof -
                      note rhigha1_in_rNodesn
                      also have 
                        "repc `Nodes n ll \<subseteq> repc `Nodes (Suc n) ll"
                        using Nodes_subset 
                        by blast
                      also have "\<dots> \<subseteq> Nodes (Suc n) ll"
                        using repcNodes_in_Nodes
                        by simp
                      finally show ?thesis
                        using null_notin_Nodes_Suc_n
                        by auto
                    qed
                    with repcrt1_dag rt1h_rt1 show ?thesis by auto
                  qed
                  with rt1_in_repcNodesn repcrt1_dag rhigha1_in_rNodesn a1_in_lln 
                    t1_repc_dag  rt1h_rt1 
                  have rt1_in_Dags_Nodesn: 
                    "rt1 \<in> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
                    apply -
                    apply (rule DagsI)
                    apply auto
                    done 

                  
                      (*hier gehts um lt1 *)
                  from a1_nNull a1_in_pret low_a1_nNull pret_dag 
                  have "low a1 \<in> set_of pret"
                    apply -
                    apply (drule subelem_set_of_low)
                    apply auto
                    done
                  with wf_ll have 
                    "low a1 \<in> set (ll ! (var (low a1)))" by (simp add: wf_ll_def)
                  with a1_in_lln t1_repc_dag var_children_smaller_a1 vara1_n 
                  have "\<exists> k<n. (low a1) \<in> set (ll ! k)"
                    by auto
                  then have lowa1_in_Nodesn: "(low a1) \<in> Nodes n ll"
                    by (simp add: Nodes_def)
                  then have rlowa1_in_rNodesn: "repc (low a1) \<in> repc ` Nodes n ll"
                    by simp
                  from lowa1_in_Nodesn normalize_prop obtain lt1h where
                    lt1_dag:  "Dag (repb (low a1)) (repb \<propto> low) (repb \<propto> high) lt1h" and
                    lt1_in_repbNort: "set_of lt1h \<subseteq> repb `Nodes n ll"
                    apply -
                    apply (erule_tac x="low a1" in ballE)
                    apply auto
                    done
                  from lt1_in_repbNort repbNodes_repcNodes 
                  have lt1_in_repcNodesn: "set_of lt1h \<subseteq> repc `Nodes n ll"
                    by blast
                  from lt1_dag lowa1_in_Nodesn 
                  have repclt1_dag: "Dag (repc (low a1)) (repc \<propto> low) (repc \<propto> high) lt1h"
                    apply -
                    apply (drule Nodes_repbc_Dags_eq [rule_format])
                    apply auto
                    done
                  from t1_Node t1_repc_dag low_a1_nNull children_repc_eq_a1 
                  have "Dag (repc (low a1)) (repc \<propto> low) (repc \<propto> high) lt1"
                    by (auto simp add: null_comp_def)
                  with repclt1_dag have lt1h_lt1: "lt1h = lt1" by (simp add: Dag_unique)
                  have lt1_nTip: "lt1 \<noteq> Tip"
                  proof -
                    have "repc (low a1) \<noteq> Null"
                    proof -
                      note rlowa1_in_rNodesn
                      also have 
                        "repc `Nodes n ll \<subseteq> repc `Nodes (Suc n) ll"
                        using Nodes_subset 
                        by blast
                      also have "\<dots> \<subseteq> Nodes (Suc n) ll"
                        using repcNodes_in_Nodes
                        by simp
                      finally show ?thesis
                        using null_notin_Nodes_Suc_n
                        by auto
                    qed
                    with repclt1_dag lt1h_lt1 show ?thesis by auto
                  qed
                  with lt1_in_repcNodesn repclt1_dag rlowa1_in_rNodesn a1_in_lln 
                    t1_repc_dag  lt1h_lt1 
                  have lt1_in_Dags_Nodesn: 
                    "lt1 \<in> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
                    apply -
                    apply (rule DagsI)
                    apply auto
                    done 
                  
                  
                      (*hier gehts um t2*)
                  from pret_dag ord_pret a2_in_pret low_a2_nNull high_a2_nNull 
                  have var_children_smaller_a2: 
                    "var (low a2) < var a2 \<and> var (high a2) < var a2"
                    apply -
                    apply (rule var_ordered_children)
                    apply auto
                    done
                  from pret_dag a2_in_pret have a2_nNull: "a2 \<noteq> Null" 
                    apply -
                    apply (rule set_of_nn [rule_format])
                    apply auto
                    done
                  
                      (*hier gehts um rt1 *)
                  with a2_in_pret high_a2_nNull pret_dag have "high a2 \<in> set_of pret" 
                    apply -
                    apply (drule subelem_set_of_high)
                    apply auto
                    done
                  with wf_ll have "high a2 \<in> set (ll ! (var (high a2)))" 
                    by (simp add: wf_ll_def)
                  with a2_in_lln t2_repc_dag var_children_smaller_a2 vara2_n 
                  have "\<exists> k<n. (high a2) \<in> set (ll ! k)"
                    by auto
                  then have higha2_in_Nodesn: "(high a2) \<in> Nodes n ll"
                    by (simp add: Nodes_def)
                  then have rhigha2_in_rNodesn: 
                    "repc (high a2) \<in> repc ` Nodes n ll"
                    by simp
                  from higha2_in_Nodesn normalize_prop obtain rt2h where
                    rt2_dag:  "Dag (repb (high a2)) (repb \<propto> low) (repb \<propto> high) rt2h" and
                    rt2_in_repbNort: "set_of rt2h \<subseteq> repb `Nodes n ll"
                    apply -
                    apply (erule_tac x="high a2" in ballE)
                    apply auto
                    done
                  from rt2_in_repbNort repbNodes_repcNodes 
                  have rt2_in_repcNodesn: "set_of rt2h \<subseteq> repc `Nodes n ll"
                    by blast
                  from rt2_dag higha2_in_Nodesn 
                  have repcrt2_dag: 
                    "Dag (repc (high a2)) (repc \<propto> low) (repc \<propto> high) rt2h"
                    apply -
                    apply (drule Nodes_repbc_Dags_eq [rule_format])
                    apply auto
                    done
                  from t2_Node t2_repc_dag high_a2_nNull children_repc_eq_a2 
                  have "Dag (repc (high a2)) (repc \<propto> low) (repc \<propto> high) rt2"
                    by (auto simp add: null_comp_def)
                  with repcrt2_dag have rt2h_rt2: "rt2h = rt2" by (simp add: Dag_unique)
                  have rt2_nTip: "rt2 \<noteq> Tip"
                  proof -
                    have "repc (high a2) \<noteq> Null"
                    proof -
                      note rhigha2_in_rNodesn
                      also have 
                        "repc `Nodes n ll \<subseteq> repc `Nodes (Suc n) ll"
                        using Nodes_subset 
                        by blast
                      also have "\<dots> \<subseteq> Nodes (Suc n) ll"
                        using repcNodes_in_Nodes
                        by simp
                      finally show ?thesis
                        using null_notin_Nodes_Suc_n
                        by auto
                    qed
                    with repcrt2_dag rt2h_rt2 show ?thesis by auto
                  qed
                  with rt2_in_repcNodesn repcrt2_dag rhigha2_in_rNodesn a2_in_lln 
                    t2_repc_dag  rt2h_rt2 
                  have rt2_in_Dags_Nodesn: 
                    "rt2 \<in> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
                    apply -
                    apply (rule DagsI)
                    apply auto
                    done 

                  
                      (*hier gehts um lt2 *)
                  from a2_nNull a2_in_pret low_a2_nNull pret_dag 
                  have "low a2 \<in> set_of pret"
                    apply -
                    apply (drule subelem_set_of_low)
                    apply auto
                    done
                  with wf_ll have "low a2 \<in> set (ll ! (var (low a2)))" 
                    by (simp add: wf_ll_def)
                  with a2_in_lln t2_repc_dag var_children_smaller_a2 vara2_n 
                  have "\<exists> k<n. (low a2) \<in> set (ll ! k)"
                    by auto
                  then have lowa2_in_Nodesn: "(low a2) \<in> Nodes n ll"
                    by (simp add: Nodes_def)
                  then have rlowa2_in_rNodesn: "repc (low a2) \<in> repc ` Nodes n ll"
                    by simp
                  from lowa2_in_Nodesn normalize_prop obtain lt2h where
                    lt2_dag:  "Dag (repb (low a2)) (repb \<propto> low) (repb \<propto> high) lt2h" and
                    lt2_in_repbNort: "set_of lt2h \<subseteq> repb `Nodes n ll"
                    apply -
                    apply (erule_tac x="low a2" in ballE)
                    apply auto
                    done
                  from lt2_in_repbNort repbNodes_repcNodes 
                  have lt2_in_repcNodesn: "set_of lt2h \<subseteq> repc `Nodes n ll"
                    by blast
                  from lt2_dag lowa2_in_Nodesn 
                  have repclt2_dag: "Dag (repc (low a2)) (repc \<propto> low) (repc \<propto> high) lt2h"
                    apply -
                    apply (drule Nodes_repbc_Dags_eq [rule_format])
                    apply auto
                    done
                  from t2_Node t2_repc_dag low_a2_nNull children_repc_eq_a2 
                  have "Dag (repc (low a2)) (repc \<propto> low) (repc \<propto> high) lt2"
                    by (auto simp add: null_comp_def)
                  with repclt2_dag have lt2h_lt2: "lt2h = lt2" by (simp add: Dag_unique)
                  have lt2_nTip: "lt2 \<noteq> Tip"
                  proof -
                    have "repc (low a2) \<noteq> Null"
                    proof -
                      note rlowa2_in_rNodesn
                      also have 
                        "repc `Nodes n ll \<subseteq> repc `Nodes (Suc n) ll"
                        using Nodes_subset 
                        by blast
                      also have "\<dots> \<subseteq> Nodes (Suc n) ll"
                        using repcNodes_in_Nodes
                        by simp
                      finally show ?thesis
                        using null_notin_Nodes_Suc_n
                        by auto
                    qed
                    with repclt2_dag lt2h_lt2 show ?thesis by auto
                  qed
                  with lt2_in_repcNodesn repclt2_dag rlowa2_in_rNodesn a2_in_lln 
                    t2_repc_dag  lt2h_lt2 
                  have lt2_in_Dags_Nodesn: 
                    "lt2 \<in> Dags (repc ` Nodes n ll) (repc \<propto> low) (repc \<propto> high)"
                    apply -
                    apply (rule DagsI)
                    apply auto
                    done 
                  
                  
                  from isomorphic_dags_eq lt1_in_Dags_Nodesn lt2_in_Dags_Nodesn repbc_dags_eq 
                  have shared_lt1_lt2: "isomorphic_dags_eq lt1 lt2 var"
                    by auto
                  from isomorphic_dags_eq rt1_in_Dags_Nodesn rt2_in_Dags_Nodesn repbc_dags_eq 
                  have shared_rt1_rt2: "isomorphic_dags_eq rt1 rt2 var"
                    by auto
                  
                  from shared_lt1_lt2 lbdt_def_lt1 lbdt_def_lt2 have lt1_lt2: "lt1 = lt2"
                    by (auto simp add: isomorphic_dags_eq_def)
                  then have root_lt1_lt2: "root lt1 = root lt2"
                    by auto
                  from lt1_nTip t1_repc_dag t1_Node have "(repc \<propto> low) (repc a1) \<noteq> Null"
                    by auto
                  with lt1_nTip t1_repc_dag t1_Node obtain llt1 lt1p rlt1 where 
                    lt1_Node: "lt1 = Node llt1 lt1p rlt1"
                    by auto
                  with t1_repc_dag t1_Node children_repc_eq_a1 lt1_nTip 
                  have root_lt1: "root lt1 = (repc \<propto> low) a1"
                    by auto
                  from lt2_nTip t2_repc_dag t2_Node have "(repc \<propto> low) (repc a2) \<noteq> Null"
                    by auto
                  with lt2_nTip t2_repc_dag t2_Node obtain llt2 lt2p rlt2 where 
                    lt2_Node: "lt2 = Node llt2 lt2p rlt2"
                    by auto
                  with t2_repc_dag t2_Node children_repc_eq_a2 lt2_nTip 
                  have root_lt2: "root lt2 = (repc \<propto> low) a2"
                    by auto
                  from root_lt1_lt2 root_lt2 root_lt1 
                  have low_a1_a2: "(repc \<propto> low) a1 = (repc \<propto> low) a2"
                    by auto
                  from shared_rt1_rt2 rbdt_def_rt1 rbdt_def_rt2 have rt1_rt2: "rt1 = rt2"
                    by (auto simp add: isomorphic_dags_eq_def)
                  then have root_rt1_rt2: "root rt1 = root rt2"
                    by auto
                  from rt1_nTip t1_repc_dag t1_Node have "(repc \<propto> high) (repc a1) \<noteq> Null"
                    by auto
                  with rt1_nTip t1_repc_dag t1_Node obtain lrt1 rt1p rrt1 where 
                    rt1_Node: "rt1 = Node lrt1 rt1p rrt1"
                    by auto
                  with t1_repc_dag t1_Node children_repc_eq_a1 rt1_nTip 
                  have root_rt1: "root rt1 = (repc \<propto> high) a1"
                    by auto
                  from rt2_nTip t2_repc_dag t2_Node 
                  have "(repc \<propto> high) (repc a2) \<noteq> Null"
                    by auto
                  with rt2_nTip t2_repc_dag t2_Node obtain lrt2 rt2p rrt2 where 
                    rt2_Node: "rt2 = Node lrt2 rt2p rrt2"
                    by auto
                  with t2_repc_dag t2_Node children_repc_eq_a2 rt2_nTip 
                  have root_rt2: "root rt2 = (repc \<propto> high) a2"
                    by auto
                  from root_rt1_rt2 root_rt2 root_rt1 
                  have high_a1_a2: "(repc \<propto> high) a1 = (repc \<propto> high) a2"
                    by auto
                  from low_a1_a2 high_a1_a2 share_a1_a2   
                  have "repc a1 = repc a2"
                    by auto
                  with lt1_lt2 rt1_rt2 show ?thesis
                    by auto
                qed
              qed
            qed
          qed
        qed
        from termi dags_shared while_while_prop repcNodes_in_Nodes repc_nc n_var_prop 
          wf_marking_m_ma  
        show ?thesis
          by auto
      qed
    qed
    with srrl_precond all_nodes_same_var 
    show ?thesis
      apply -
      apply (intro conjI)
      apply assumption+
      done
  qed
qed

end
