(*  Title:       BDD

    Author:      Veronika Ortner and Norbert Schirmer, 2004
    Maintainer:  Norbert Schirmer,  norbert.schirmer at web de
    License:     LGPL
*)

(*  
RepointProof.thy

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

section \<open>Proof of Procedure Repoint\<close>
theory RepointProof imports ProcedureSpecs begin

hide_const (open) DistinctTreeProver.set_of tree.Node tree.Tip

lemma (in Repoint_impl) Repoint_modifies:
  shows "\<forall>\<sigma>. \<Gamma>\<turnstile>{\<sigma>} \<acute>p :==  PROC Repoint (\<acute>p)
        {t. t may_only_modify_globals \<sigma> in [low,high]}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done

lemma low_high_exchange_dag: 
assumes pt_same: "\<forall>pt. pt \<notin> set_of lt \<longrightarrow> low pt = lowa pt \<and> high pt = higha pt"
assumes pt_changed: "\<forall>pt \<in> set_of lt. lowa pt = (rep \<propto> low) pt \<and> 
                            higha pt = (rep \<propto> high) pt"
assumes rep_pt: "\<forall>pt \<in> set_of rt. rep pt = pt"
shows "\<And>q.  Dag q (rep \<propto> low) (rep \<propto> high) rt \<Longrightarrow> 
            Dag q (rep \<propto> lowa) (rep \<propto> higha) rt"
using rep_pt
proof (induct rt)
  case Tip thus ?case by simp
next
  case (Node lrt q' rrt)
  have "Dag q (rep \<propto> low) (rep \<propto> high) (Node lrt q' rrt)" by fact
  then obtain 
    q': "q = q'"  and
    q_notNull: "q \<noteq> Null" and 
    lrt: "Dag ((rep \<propto> low) q) (rep \<propto> low) (rep \<propto> high) lrt" and
    rrt: "Dag ((rep \<propto> high) q) (rep \<propto> low) (rep \<propto> high) rrt" 
    by auto
  have rlowa_rlow: "((rep \<propto> lowa) q) = ((rep \<propto> low) q)"
  proof (cases "q \<in> set_of lt")
    case True
    note q_in_lt=this
    with pt_changed have lowa_q: "lowa q = (rep \<propto> low) q"
      by simp
    thus "(rep \<propto> lowa) q = (rep \<propto> low) q"
    proof (cases "low q = Null")
      case True
      with lowa_q have "lowa q = Null"
        by (simp add: null_comp_def)
      with True show ?thesis
        by (simp add: null_comp_def)
    next
      assume lq_nNull: "low q \<noteq> Null"
      show ?thesis
      proof (cases "(rep \<propto> low) q = Null")
        case True 
        with lowa_q have "lowa q = Null"
          by simp
        with True show ?thesis
          by (simp add: null_comp_def)
      next
        assume rlq_nNull: "(rep \<propto> low) q \<noteq> Null"
        with lrt lowa_q have "lowa q \<in> set_of lrt"
          by auto
        with Node.prems Node have "lowa q \<in> set_of (Node lrt q' rrt)"
          by simp
        with Node.prems have "rep (lowa q) = lowa q"
          by auto
        with lowa_q rlq_nNull show ?thesis
          by (simp add: null_comp_def)
      qed
    qed
  next
    assume q_notin_lt: " q \<notin> set_of lt"
    with pt_same have "low q = lowa q"
      by auto
    thus ?thesis
      by (simp add: null_comp_def)
  qed
  have rhigha_rhigh: "((rep \<propto> higha) q) = ((rep \<propto> high) q)"
  proof (cases "q \<in> set_of lt")
    case True
    note q_in_lt=this
    with pt_changed have higha_q: "higha q = (rep \<propto> high) q"
      by simp
    thus ?thesis
    proof (cases "high q = Null")
      case True
      with higha_q have "higha q = Null"
        by (simp add: null_comp_def)
      with True show ?thesis
        by (simp add: null_comp_def)
    next
      assume hq_nNull: "high q \<noteq> Null"
      show ?thesis
      proof (cases "(rep \<propto> high) q = Null")
        case True 
        with higha_q have "higha q = Null"
          by simp
        with True show ?thesis
          by (simp add: null_comp_def)
      next
        assume rhq_nNull: "(rep \<propto> high) q \<noteq> Null"
        with rrt higha_q have "higha q \<in> set_of rrt"
          by auto
        with Node.prems Node have "higha q \<in> set_of (Node lrt q' rrt)"
          by simp
        with Node.prems have "rep (higha q) = higha q"
          by auto
        with higha_q rhq_nNull show ?thesis
          by (simp add: null_comp_def)
      qed
    qed
  next
    assume q_notin_lt: " q \<notin> set_of lt"
    with pt_same have "high q = higha q"
      by auto
    thus ?thesis
      by (simp add: null_comp_def)
  qed
  with rrt have rhigha_mixed_dag: 
    "Dag ((rep \<propto> higha) q) (rep \<propto> low) (rep \<propto> high) rrt"
    by simp
  from lrt rlowa_rlow have rlowa_mixed_dag: 
    " Dag ((rep \<propto> lowa) q) (rep \<propto> low) (rep \<propto> high) lrt"
    by simp
  from Node.prems have lrt_rep_eq: " \<forall>pt\<in>set_of lrt. rep pt = pt"
    by simp
  from Node.prems have rrt_rep_eq: "\<forall>pt\<in>set_of rrt. rep pt = pt"
    by simp
  from rlowa_mixed_dag lrt_rep_eq have lowa_lrt: 
    " Dag ((rep \<propto> lowa) q) (rep \<propto> lowa) (rep \<propto> higha) lrt"
    apply -
    apply (rule Node.hyps)
    apply auto
    done
  from rhigha_mixed_dag rrt_rep_eq have higha_rrt: 
    " Dag ((rep \<propto> higha) q) (rep \<propto> lowa) (rep \<propto> higha) rrt"
    apply -
    apply (rule Node.hyps)
    apply auto
    done
  with lowa_lrt q' q_notNull 
  show " Dag q (rep \<propto> lowa) (rep \<propto> higha) (Node lrt q' rrt)"
    by simp
qed

(*lemma Repoint_spec :
includes Repoint_impl 
shows  
  "\<forall>\<sigma> rept. \<Gamma>\<turnstile> \<lbrace>\<sigma>. (Dag ((\<^bsup>\<sigma>\<^esup>rep \<propto> id) \<^bsup>\<sigma>\<^esup>p) (\<^bsup>\<sigma>\<^esup>rep \<propto> \<^bsup>\<sigma>\<^esup>low) (\<^bsup>\<sigma>\<^esup>rep \<propto> \<^bsup>\<sigma>\<^esup>high) rept) 
  \<and> (\<forall> no \<in> set_of rept. \<^bsup>\<sigma>\<^esup>rep no = no) \<rbrace>
  \<acute>p :== CALL Repoint (\<acute>p)
  \<lbrace>Dag \<acute>p \<acute>low \<acute>high rept \<and>
  (\<forall>pt. pt \<notin> set_of rept \<longrightarrow> \<^bsup>\<sigma>\<^esup>low pt = \<acute>low pt \<and> \<^bsup>\<sigma>\<^esup>high pt = \<acute>high pt)\<rbrace>"
apply (hoare_rule CallRec1_SamePost)
apply (vcg)
apply  (rule conjI)
apply  clarify
prefer 2
apply (intro impI allI )
apply (simp add: null_comp_def)
apply (rule conjI)
prefer 2
apply (clarsimp)
apply clarify
*)



lemma (in Repoint_impl) Repoint_spec':
shows 
  "\<forall>\<sigma>. \<Gamma>\<turnstile> {\<sigma>}
  \<acute>p :== PROC Repoint (\<acute>p)
  \<lbrace>\<forall> rept. ((Dag ((\<^bsup>\<sigma>\<^esup>rep \<propto> id) \<^bsup>\<sigma>\<^esup>p) (\<^bsup>\<sigma>\<^esup>rep \<propto> \<^bsup>\<sigma>\<^esup>low) (\<^bsup>\<sigma>\<^esup>rep \<propto> \<^bsup>\<sigma>\<^esup>high) rept) 
  \<and> (\<forall> no \<in> set_of rept. \<^bsup>\<sigma>\<^esup>rep no = no))
  \<longrightarrow> Dag \<acute>p \<acute>low \<acute>high rept \<and>
  (\<forall>pt. pt \<notin> set_of rept \<longrightarrow> \<^bsup>\<sigma>\<^esup>low pt = \<acute>low pt \<and> \<^bsup>\<sigma>\<^esup>high pt = \<acute>high pt)\<rbrace>"
apply (hoare_rule HoarePartial.ProcRec1)
apply vcg
apply  (rule conjI)
apply  clarify
prefer 2
apply (intro impI allI )
apply (simp add: null_comp_def)
apply (rule conjI)
prefer 2
apply (clarsimp)
apply clarify
proof -
  fix low high p rep lowa higha pa lowb highb pb rept
  assume p_nNull: "p \<noteq> Null"
  assume rp_nNull: " rep p \<noteq> Null"
  assume rec_spec_lrept: 
    "\<forall>rept. Dag ((rep \<propto> id) (low (rep p))) (rep \<propto> low) (rep \<propto> high) rept
    \<and> (\<forall>no\<in>set_of rept. rep no = no)
    \<longrightarrow> Dag pa lowa higha rept \<and> 
        (\<forall>pt. pt \<notin> set_of rept \<longrightarrow> low pt = lowa pt \<and> high pt = higha pt)"
  assume rec_spec_rrept: 
    "\<forall>rept. Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> lowa(rep p := pa)) (rep \<propto> higha) rept
    \<and> (\<forall>no\<in>set_of rept. rep no = no)
    \<longrightarrow> Dag pb lowb highb rept \<and> 
        (\<forall>pt. pt \<notin> set_of rept \<longrightarrow> (lowa(rep p := pa)) pt = lowb pt \<and> higha pt = highb pt)"
  assume rept_dag: "Dag ((rep \<propto> id) p) (rep \<propto> low) (rep \<propto> high) rept"
  assume rno_rept: "\<forall>no\<in>set_of rept. rep no = no"
  show " Dag (rep p) lowb (highb(rep p := pb)) rept \<and> 
    (\<forall>pt. pt \<notin> set_of rept \<longrightarrow> low pt = lowb pt \<and> high pt = (highb(rep p := pb)) pt)"
  proof -
    from rp_nNull rept_dag p_nNull obtain lrept rrept where
      rept_def: "rept = Node lrept (rep p) rrept"
      by auto
    with rept_dag p_nNull have lrept_dag: 
      "Dag ((rep \<propto> low) (rep p)) (rep \<propto> low) (rep \<propto> high) lrept"
      by simp
    from rept_def rept_dag p_nNull have rrept_dag: 
      "Dag ((rep \<propto> high) (rep p)) (rep \<propto> low) (rep \<propto> high) rrept"
      by simp
    from rno_rept rept_def have rno_lrept: "\<forall> no \<in> set_of lrept. rep no = no"
      by auto
    from rno_rept rept_def have rno_rrept: "\<forall> no \<in> set_of rrept. rep no = no"
      by auto
    have repoint_post_low: 
      " Dag pa lowa higha lrept \<and> 
      (\<forall>pt. pt \<notin> set_of lrept \<longrightarrow> low pt = lowa pt \<and> high pt = higha pt)"
    proof -
      from lrept_dag have " Dag ((rep \<propto> id) (low (rep p))) (rep \<propto> low) (rep \<propto> high) lrept"
        by (simp add: id_trans)
      with  rec_spec_lrept rno_lrept show ?thesis
        apply -
        apply (erule_tac x=lrept in allE)
        apply (erule impE)
        apply simp
        apply assumption
        done
    qed
    hence low_lowa_nc: "(\<forall>pt. pt \<notin> set_of lrept \<longrightarrow> low pt = lowa pt \<and> high pt = higha pt)"
      by simp
    from lrept_dag  repoint_post_low obtain 
      pa_def: "pa = (rep \<propto> low) (rep p)" and
      lowa_higha_def: "(\<forall> no \<in> set_of lrept. lowa no = (rep \<propto> low) no \<and> higha no = (rep \<propto> high) no)"
      apply -
      apply (drule Dags_eq_hp_eq)
      apply auto
      done
    from rept_dag have rept_DAG: "DAG rept"
      by (rule Dag_is_DAG)
    with rept_def have rp_notin_lrept: "rep p \<notin> set_of lrept"
      by simp
    from rept_DAG rept_def have rp_notin_rrept: "rep p \<notin> set_of rrept"
      by simp
    have "Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> lowa(rep p := pa)) (rep \<propto> higha) rrept"
    proof -
      from low_lowa_nc rp_notin_lrept have "(rep \<propto> high) (rep p) = (rep \<propto> higha) (rep p)"
        by (auto simp add: null_comp_def)
      with rrept_dag have higha_mixed_rrept: 
        "Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> low) (rep \<propto> high) rrept"
        by (simp add: id_trans)
      thm low_high_exchange_dag
      with low_lowa_nc lowa_higha_def rno_rrept have lowa_higha_rrept:
        "Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> lowa) (rep \<propto> higha) rrept"
        apply -
        apply (rule low_high_exchange_dag)
        apply auto
        done
      have "Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> lowa) (rep \<propto> higha) rrept = 
        Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> lowa(rep p := pa)) (rep \<propto> higha) rrept"
      proof -
        have "\<forall> no \<in> set_of rrept. (rep \<propto> lowa) no = (rep \<propto> lowa(rep p := pa)) no \<and>
          (rep \<propto> higha) no = (rep \<propto> higha) no"
        proof 
          fix no
          assume no_in_rrept: "no \<in> set_of rrept"
          with rp_notin_rrept have "no \<noteq> rep p" 
            by blast
          thus "(rep \<propto> lowa) no = (rep \<propto> lowa(rep p := pa)) no \<and> 
            (rep \<propto> higha) no = (rep \<propto> higha) no"
            by (simp add: null_comp_def)
        qed
        thus ?thesis
          by (rule heaps_eq_Dag_eq)
      qed
      with lowa_higha_rrept show ?thesis
        by simp
    qed
    with rec_spec_rrept rno_rrept have repoint_rrept: "Dag pb lowb highb rrept \<and> 
      (\<forall>pt. pt \<notin> set_of rrept \<longrightarrow> 
      (lowa(rep p := pa)) pt = lowb pt \<and> higha pt = highb pt)"
      apply -
      apply (erule_tac x=rrept in allE)
      apply (erule impE)
      apply simp
      apply assumption
      done
    then have ab_nc: "(\<forall>pt. pt \<notin> set_of rrept \<longrightarrow> 
      (lowa(rep p := pa)) pt = lowb pt \<and> higha pt = highb pt)"
      by simp
    from repoint_rrept rrept_dag obtain
      pb_def: "pb = ((rep \<propto> high) (rep p))" and
      lowb_highb_def: "(\<forall> no \<in> set_of rrept. lowb no = (rep \<propto> low) no \<and> highb no = (rep \<propto> high) no)"
      apply -
      apply (drule Dags_eq_hp_eq)
      apply auto
      done
    have rept_end_dag: " Dag (rep p) lowb (highb(rep p := pb)) rept"
    proof -
      have "\<forall> no \<in> set_of rept. lowb no = (rep \<propto> low) no \<and> (highb(rep p := pb)) no = (rep \<propto> high) no"
      proof
        fix no
        assume no_in_rept: " no \<in> set_of rept"
        show "lowb no = (rep \<propto> low) no \<and> (highb(rep p := pb)) no = (rep \<propto> high) no"
        proof (cases "no \<in> set_of rrept")
          case True
          with lowb_highb_def pb_def show ?thesis
            by simp
        next
          assume no_notin_rrept: " no \<notin> set_of rrept"
          show ?thesis
          proof (cases "no \<in> set_of lrept")
            case True
            with no_notin_rrept rp_notin_lrept ab_nc
            have ab_nc_no: "lowa no = lowb no \<and> higha no = highb no"
              apply -
              apply (erule_tac x=no in allE)
              apply (erule impE)
              apply simp
              apply (subgoal_tac "no \<noteq> rep p")
              apply simp
              apply blast
              done
            from lowa_higha_def True have 
              "lowa no = (rep \<propto> low) no \<and> higha no = (rep \<propto> high) no"
              by auto
            with ab_nc_no have "lowb no = (rep \<propto> low) no \<and> highb no =(rep \<propto> high) no" 
              by simp
            with rp_notin_lrept True show ?thesis
              apply (subgoal_tac "no \<noteq> rep p")
              apply simp
              apply blast
              done
          next
            assume no_notin_lrept: " no \<notin> set_of lrept"
            with no_in_rept rept_def no_notin_rrept have no_rp: "no = rep p"
              by simp
            with rp_notin_lrept low_lowa_nc have a_nc:  
              "low no = lowa no \<and> high no = higha no"
              by auto
            from rp_notin_rrept no_rp ab_nc have 
              "(lowa(rep p := pa)) no = lowb no \<and> higha no = highb no"
              by auto
            with a_nc pa_def no_rp have "(rep \<propto> low) no = lowb no \<and> high no = highb no"
              by auto
            with pb_def no_rp show ?thesis
              by simp
          qed
        qed
      qed
      with rept_dag have " Dag (rep p) lowb (highb(rep p := pb)) rept = 
        Dag (rep p) (rep \<propto> low) (rep \<propto> high) rept"      
        apply -
        thm heaps_eq_Dag_eq
        apply (rule heaps_eq_Dag_eq)
        apply auto
        done
      with rept_dag p_nNull show ?thesis
        by simp
    qed
    have "(\<forall>pt. pt \<notin> set_of rept \<longrightarrow> low pt = lowb pt \<and> high pt = (highb(rep p := pb)) pt)"
    proof (intro allI impI)
      fix pt
      assume pt_notin_rept: "pt \<notin> set_of rept"
      with rept_def obtain
        pt_notin_lrept: "pt \<notin> set_of lrept" and
        pt_notin_rrept: "pt \<notin> set_of rrept" and
        pt_neq_rp: "pt \<noteq> rep p"
        by simp
      with low_lowa_nc ab_nc show "low pt = lowb pt \<and> high pt = (highb(rep p := pb)) pt"
        by auto
    qed
    with rept_end_dag show ?thesis
      by simp
  qed
qed
        
lemma (in Repoint_impl) Repoint_spec:
shows 
  "\<forall>\<sigma> rept. \<Gamma>\<turnstile> \<lbrace>\<sigma>. Dag ((\<acute>rep \<propto> id) \<acute>p) (\<acute>rep \<propto> \<acute>low) (\<acute>rep \<propto> \<acute>high) rept 
  \<and> (\<forall> no \<in> set_of rept. \<acute>rep no = no) \<rbrace> 
  \<acute>p :== PROC Repoint (\<acute>p)
  \<lbrace>Dag \<acute>p \<acute>low \<acute>high rept \<and>
  (\<forall>pt. pt \<notin> set_of rept \<longrightarrow> \<^bsup>\<sigma>\<^esup>low pt = \<acute>low pt \<and> \<^bsup>\<sigma>\<^esup>high pt = \<acute>high pt)\<rbrace>"
apply (hoare_rule HoarePartial.ProcRec1)
apply vcg
apply (rule conjI)
prefer 2
apply  (clarsimp simp add: null_comp_def)
apply clarify
apply (rule conjI)
prefer 2
apply  clarsimp
apply clarify
proof -
  fix rept low high rep p
  assume rept_dag: "Dag ((rep \<propto> id) p) (rep \<propto> low) (rep \<propto> high) rept"
  assume rno_rept: "\<forall>no\<in>set_of rept. rep no = no"
  assume p_nNull: "p \<noteq> Null"
  assume rp_nNull: " rep p \<noteq> Null"
  show "\<exists>lrept.
             Dag ((rep \<propto> id) (low (rep p))) (rep \<propto> low) (rep \<propto> high) lrept \<and>
             (\<forall>no\<in>set_of lrept. rep no = no) \<and>
             (\<forall>lowa higha pa.
                 Dag pa lowa higha lrept \<and>
                 (\<forall>pt. pt \<notin> set_of lrept \<longrightarrow>
                       low pt = lowa pt \<and> high pt = higha pt) \<longrightarrow>
                 (\<exists>rrept.
                     Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> lowa(rep p := pa))
                      (rep \<propto> higha) rrept \<and>
                     (\<forall>no\<in>set_of rrept. rep no = no) \<and>
                     (\<forall>lowb highb pb.
                         Dag pb lowb highb rrept \<and>
                         (\<forall>pt. pt \<notin> set_of rrept \<longrightarrow>
                               (lowa(rep p := pa)) pt = lowb pt \<and>
                               higha pt = highb pt) \<longrightarrow>
                         Dag (rep p) lowb (highb(rep p := pb)) rept \<and>
                         (\<forall>pt. pt \<notin> set_of rept \<longrightarrow>
                               low pt = lowb pt \<and>
                               high pt = (highb(rep p := pb)) pt))))" 
  proof -
    from rp_nNull rept_dag p_nNull obtain lrept rrept where
      rept_def: "rept = Node lrept (rep p) rrept"
      by auto
    with rept_dag p_nNull have lrept_dag: 
      "Dag ((rep \<propto> low) (rep p)) (rep \<propto> low) (rep \<propto> high) lrept"
      by simp
    from rept_def rept_dag p_nNull have rrept_dag: 
      "Dag ((rep \<propto> high) (rep p)) (rep \<propto> low) (rep \<propto> high) rrept"
      by simp
    from rno_rept rept_def have rno_lrept: "\<forall> no \<in> set_of lrept. rep no = no"
      by auto
    from rno_rept rept_def have rno_rrept: "\<forall> no \<in> set_of rrept. rep no = no"
      by auto
    show ?thesis
      apply (rule_tac x=lrept in exI)
      apply (rule conjI)
      apply  (simp add: id_trans lrept_dag)
      apply (rule conjI)
      apply (rule rno_lrept)
      apply clarify
      subgoal premises prems for lowa higha pa
      proof -
        have lrepta: "Dag pa lowa higha lrept" by fact
        have low_lowa_nc: 
          "\<forall>pt. pt \<notin> set_of lrept \<longrightarrow> low pt = lowa pt \<and> high pt = higha pt" by fact
        from lrept_dag lrepta  obtain 
          pa_def: "pa = (rep \<propto> low) (rep p)" and
          lowa_higha_def: "\<forall>no \<in> set_of lrept. 
          lowa no = (rep \<propto> low) no \<and> higha no = (rep \<propto> high) no"
          apply -
          apply (drule Dags_eq_hp_eq)
          apply auto
          done
        from rept_dag have rept_DAG: "DAG rept"
          by (rule Dag_is_DAG)
        with rept_def have rp_notin_lrept: "rep p \<notin> set_of lrept"
          by simp
        from rept_DAG rept_def have rp_notin_rrept: "rep p \<notin> set_of rrept"
          by simp
        have rrepta: "Dag ((rep \<propto> id) (higha (rep p))) 
                         (rep \<propto> lowa(rep p := pa)) (rep \<propto> higha) rrept"
        proof -
          from low_lowa_nc rp_notin_lrept 
          have "(rep \<propto> high) (rep p) = (rep \<propto> higha) (rep p)"
            by (auto simp add: null_comp_def)
          with rrept_dag have higha_mixed_rrept: 
            "Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> low) (rep \<propto> high) rrept"
            by (simp add: id_trans)
          thm low_high_exchange_dag
          with low_lowa_nc lowa_higha_def rno_rrept 
          have lowa_higha_rrept:
              "Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> lowa) (rep \<propto> higha) rrept"
            apply -
            apply (rule low_high_exchange_dag)
            apply auto
            done
          have "Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> lowa) (rep \<propto> higha) rrept = 
                Dag ((rep \<propto> id) (higha (rep p))) 
                        (rep \<propto> lowa(rep p := pa)) (rep \<propto> higha) rrept"
          proof -
            have "\<forall>no \<in> set_of rrept. 
                      (rep \<propto> lowa) no = (rep \<propto> lowa(rep p := pa)) no \<and>
                      (rep \<propto> higha) no = (rep \<propto> higha) no"
            proof 
              fix no
              assume no_in_rrept: "no \<in> set_of rrept"
              with rp_notin_rrept have "no \<noteq> rep p" 
                by blast
              thus "(rep \<propto> lowa) no = (rep \<propto> lowa(rep p := pa)) no \<and> 
                (rep \<propto> higha) no = (rep \<propto> higha) no"
                by (simp add: null_comp_def)
            qed
            thus ?thesis
              by (rule heaps_eq_Dag_eq)
          qed
          with lowa_higha_rrept show ?thesis
            by simp
        qed
        show ?thesis
          apply (rule_tac x=rrept in exI)
          apply (rule conjI)
          apply  (rule rrepta)
          apply (rule conjI)
          apply  (rule rno_rrept)
          apply clarify
          subgoal premises prems for lowb highb pb
          proof -
            have rreptb: "Dag pb lowb highb rrept" by fact
            have ab_nc: "\<forall>pt. pt \<notin> set_of rrept \<longrightarrow> 
                            (lowa(rep p := pa)) pt = lowb pt \<and> higha pt = highb pt" by fact
            from rreptb rrept_dag obtain
              pb_def: "pb = ((rep \<propto> high) (rep p))" and
              lowb_highb_def: "\<forall>no \<in> set_of rrept. 
                                  lowb no = (rep \<propto> low) no \<and> highb no = (rep \<propto> high) no"
              apply -
              apply (drule Dags_eq_hp_eq)
              apply auto
              done
            have rept_end_dag: " Dag (rep p) lowb (highb(rep p := pb)) rept"
            proof -
              have "\<forall>no \<in> set_of rept. 
                    lowb no = (rep \<propto> low) no \<and> (highb(rep p := pb)) no = (rep \<propto> high) no"
              proof
                fix no
                assume no_in_rept: " no \<in> set_of rept"
                show "lowb no = (rep \<propto> low) no \<and> 
                      (highb(rep p := pb)) no = (rep \<propto> high) no"
                proof (cases "no \<in> set_of rrept")
                  case True
                  with lowb_highb_def pb_def show ?thesis
                    by simp
                next
                  assume no_notin_rrept: " no \<notin> set_of rrept"
                  show ?thesis
                  proof (cases "no \<in> set_of lrept")
                    case True
                    with no_notin_rrept rp_notin_lrept ab_nc
                    have ab_nc_no: "lowa no = lowb no \<and> higha no = highb no"
                      apply -
                      apply (erule_tac x=no in allE)
                      apply (erule impE)
                      apply simp
                      apply (subgoal_tac "no \<noteq> rep p")
                      apply simp
                      apply blast
                      done
                    from lowa_higha_def True have 
                      "lowa no = (rep \<propto> low) no \<and> higha no = (rep \<propto> high) no"
                      by auto
                    with ab_nc_no 
                    have "lowb no = (rep \<propto> low) no \<and> highb no =(rep \<propto> high) no" 
                      by simp
                    with rp_notin_lrept True show ?thesis
                      apply (subgoal_tac "no \<noteq> rep p")
                      apply simp
                      apply blast
                      done
                  next
                    assume no_notin_lrept: " no \<notin> set_of lrept"
                    with no_in_rept rept_def no_notin_rrept have no_rp: "no = rep p"
                      by simp
                    with rp_notin_lrept low_lowa_nc 
                    have a_nc: "low no = lowa no \<and> high no = higha no"
                      by auto
                    from rp_notin_rrept no_rp ab_nc 
                    have "(lowa(rep p := pa)) no = lowb no \<and> higha no = highb no"
                      by auto
                    with a_nc pa_def no_rp 
                    have "(rep \<propto> low) no = lowb no \<and> high no = highb no"
                      by auto
                    with pb_def no_rp show ?thesis
                      by simp
                  qed
                qed
              qed
              with rept_dag 
              have "Dag (rep p) lowb (highb(rep p := pb)) rept = 
                    Dag (rep p) (rep \<propto> low) (rep \<propto> high) rept"      
                apply -
                apply (rule heaps_eq_Dag_eq)
                apply auto
                done
              with rept_dag p_nNull show ?thesis
                by simp
            qed
            have "(\<forall>pt. pt \<notin> set_of rept \<longrightarrow> low pt = lowb pt \<and> 
                        high pt = (highb(rep p := pb)) pt)"
            proof (intro allI impI)
              fix pt
              assume pt_notin_rept: "pt \<notin> set_of rept"
              with rept_def obtain
                pt_notin_lrept: "pt \<notin> set_of lrept" and
                pt_notin_rrept: "pt \<notin> set_of rrept" and
                pt_neq_rp: "pt \<noteq> rep p"
                by simp
              with low_lowa_nc ab_nc 
              show "low pt = lowb pt \<and> high pt = (highb(rep p := pb)) pt"
                by auto
            qed
            with rept_end_dag show ?thesis
              by simp
          qed
        done
      qed
    done
  qed
qed

lemma (in Repoint_impl) Repoint_spec_total:
shows 
  "\<forall>\<sigma> rept. \<Gamma>\<turnstile>\<^sub>t \<lbrace>\<sigma>. Dag ((\<acute>rep \<propto> id) \<acute>p) (\<acute>rep \<propto> \<acute>low) (\<acute>rep \<propto> \<acute>high) rept 
  \<and> (\<forall> no \<in> set_of rept. \<acute>rep no = no) \<rbrace> 
  \<acute>p :== PROC Repoint (\<acute>p)
  \<lbrace>Dag \<acute>p \<acute>low \<acute>high rept \<and>
  (\<forall>pt. pt \<notin> set_of rept \<longrightarrow> \<^bsup>\<sigma>\<^esup>low pt = \<acute>low pt \<and> \<^bsup>\<sigma>\<^esup>high pt = \<acute>high pt)\<rbrace>"

apply (hoare_rule HoareTotal.ProcRec1
          [where r="measure (\<lambda>(s,p). size 
                       (dag ((\<^bsup>s\<^esup>rep \<propto> id) \<^bsup>s\<^esup>p) (\<^bsup>s\<^esup>rep \<propto> \<^bsup>s\<^esup>low) (\<^bsup>s\<^esup>rep \<propto> \<^bsup>s\<^esup>high)))"])
apply vcg
apply (rule conjI)
prefer 2
apply  (clarsimp simp add: null_comp_def)
apply clarify
apply (rule conjI)
prefer 2
apply  clarsimp
apply clarify
proof -
  fix rept low high rep p
  assume rept_dag: "Dag ((rep \<propto> id) p) (rep \<propto> low) (rep \<propto> high) rept"
  assume rno_rept: "\<forall>no\<in>set_of rept. rep no = no"
  assume p_nNull: "p \<noteq> Null"
  assume rp_nNull: " rep p \<noteq> Null"
  show "\<exists>lrept.
             Dag ((rep \<propto> id) (low (rep p))) (rep \<propto> low) (rep \<propto> high) lrept \<and>
             (\<forall>no\<in>set_of lrept. rep no = no) \<and>
             size (dag ((rep \<propto> id) (low (rep p))) (rep \<propto> low) (rep \<propto> high))
             < size (dag ((rep \<propto> id) p) (rep \<propto> low) (rep \<propto> high)) \<and>
             (\<forall>lowa higha pa.
                 Dag pa lowa higha lrept \<and>
                 (\<forall>pt. pt \<notin> set_of lrept \<longrightarrow>
                       low pt = lowa pt \<and> high pt = higha pt) \<longrightarrow>
                 (\<exists>rrept.
                     Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> lowa(rep p := pa))
                      (rep \<propto> higha) rrept \<and>
                     (\<forall>no\<in>set_of rrept. rep no = no) \<and>
                     size (dag ((rep \<propto> id) (higha (rep p)))
                            (rep \<propto> lowa(rep p := pa)) (rep \<propto> higha))
                     < size (dag ((rep \<propto> id) p) (rep \<propto> low) (rep \<propto> high)) \<and>
                     (\<forall>lowb highb pb.
                         Dag pb lowb highb rrept \<and>
                         (\<forall>pt. pt \<notin> set_of rrept \<longrightarrow>
                               (lowa(rep p := pa)) pt = lowb pt \<and>
                               higha pt = highb pt) \<longrightarrow>
                         Dag (rep p) lowb (highb(rep p := pb)) rept \<and>
                         (\<forall>pt. pt \<notin> set_of rept \<longrightarrow>
                               low pt = lowb pt \<and>
                               high pt = (highb(rep p := pb)) pt))))"
  proof -
    from rp_nNull rept_dag p_nNull obtain lrept rrept where
      rept_def: "rept = Node lrept (rep p) rrept"
      by auto
    with rept_dag p_nNull have lrept_dag: 
      "Dag ((rep \<propto> low) (rep p)) (rep \<propto> low) (rep \<propto> high) lrept"
      by simp
    from rept_def rept_dag p_nNull have rrept_dag: 
      "Dag ((rep \<propto> high) (rep p)) (rep \<propto> low) (rep \<propto> high) rrept"
      by simp
    from rno_rept rept_def have rno_lrept: "\<forall> no \<in> set_of lrept. rep no = no"
      by auto
    from rno_rept rept_def have rno_rrept: "\<forall> no \<in> set_of rrept. rep no = no"
      by auto
    show ?thesis
      apply (rule_tac x=lrept in exI)
      apply (rule conjI)
      apply  (simp add: id_trans lrept_dag)
      apply (rule conjI)
      apply (rule rno_lrept)
      apply (rule conjI)
      using rept_dag rept_def
      apply  (simp only: Dag_dag)
      apply  (clarsimp simp add: id_trans Dag_dag)
      apply clarify
      subgoal premises prems for lowa higha pa
      proof -
        have lrepta: "Dag pa lowa higha lrept" by fact
        have low_lowa_nc: 
          "\<forall>pt. pt \<notin> set_of lrept \<longrightarrow> low pt = lowa pt \<and> high pt = higha pt" by fact
        from lrept_dag lrepta  obtain 
          pa_def: "pa = (rep \<propto> low) (rep p)" and
          lowa_higha_def: "\<forall>no \<in> set_of lrept. 
          lowa no = (rep \<propto> low) no \<and> higha no = (rep \<propto> high) no"
          apply -
          apply (drule Dags_eq_hp_eq)
          apply auto
          done
        from rept_dag have rept_DAG: "DAG rept"
          by (rule Dag_is_DAG)
        with rept_def have rp_notin_lrept: "rep p \<notin> set_of lrept"
          by simp
        from rept_DAG rept_def have rp_notin_rrept: "rep p \<notin> set_of rrept"
          by simp
        have rrepta: "Dag ((rep \<propto> id) (higha (rep p))) 
                         (rep \<propto> lowa(rep p := pa)) (rep \<propto> higha) rrept"
        proof -
          from low_lowa_nc rp_notin_lrept 
          have "(rep \<propto> high) (rep p) = (rep \<propto> higha) (rep p)"
            by (auto simp add: null_comp_def)
          with rrept_dag have higha_mixed_rrept: 
            "Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> low) (rep \<propto> high) rrept"
            by (simp add: id_trans)
          thm low_high_exchange_dag
          with low_lowa_nc lowa_higha_def rno_rrept 
          have lowa_higha_rrept:
              "Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> lowa) (rep \<propto> higha) rrept"
            apply -
            apply (rule low_high_exchange_dag)
            apply auto
            done
          have "Dag ((rep \<propto> id) (higha (rep p))) (rep \<propto> lowa) (rep \<propto> higha) rrept = 
                Dag ((rep \<propto> id) (higha (rep p))) 
                        (rep \<propto> lowa(rep p := pa)) (rep \<propto> higha) rrept"
          proof -
            have "\<forall>no \<in> set_of rrept. 
                      (rep \<propto> lowa) no = (rep \<propto> lowa(rep p := pa)) no \<and>
                      (rep \<propto> higha) no = (rep \<propto> higha) no"
            proof 
              fix no
              assume no_in_rrept: "no \<in> set_of rrept"
              with rp_notin_rrept have "no \<noteq> rep p" 
                by blast
              thus "(rep \<propto> lowa) no = (rep \<propto> lowa(rep p := pa)) no \<and> 
                (rep \<propto> higha) no = (rep \<propto> higha) no"
                by (simp add: null_comp_def)
            qed
            thus ?thesis
              by (rule heaps_eq_Dag_eq)
          qed
          with lowa_higha_rrept show ?thesis
            by simp
        qed
        show ?thesis
          apply (rule_tac x=rrept in exI)
          apply (rule conjI)
          apply  (rule rrepta)
          apply (rule conjI)
          apply  (rule rno_rrept)
          apply (rule conjI)
          using rept_dag rept_def rrepta
          apply  (simp only: Dag_dag)
          apply  (clarsimp simp add: id_trans Dag_dag)
          apply clarify
          subgoal premises prems for lowb highb pb
          proof -
            have rreptb: "Dag pb lowb highb rrept" by fact
            have ab_nc: "\<forall>pt. pt \<notin> set_of rrept \<longrightarrow> 
                            (lowa(rep p := pa)) pt = lowb pt \<and> higha pt = highb pt" by fact
            from rreptb rrept_dag obtain
              pb_def: "pb = ((rep \<propto> high) (rep p))" and
              lowb_highb_def: "\<forall>no \<in> set_of rrept. 
                                  lowb no = (rep \<propto> low) no \<and> highb no = (rep \<propto> high) no"
              apply -
              apply (drule Dags_eq_hp_eq)
              apply auto
              done
            have rept_end_dag: " Dag (rep p) lowb (highb(rep p := pb)) rept"
            proof -
              have "\<forall>no \<in> set_of rept. 
                    lowb no = (rep \<propto> low) no \<and> (highb(rep p := pb)) no = (rep \<propto> high) no"
              proof
                fix no
                assume no_in_rept: " no \<in> set_of rept"
                show "lowb no = (rep \<propto> low) no \<and> 
                      (highb(rep p := pb)) no = (rep \<propto> high) no"
                proof (cases "no \<in> set_of rrept")
                  case True
                  with lowb_highb_def pb_def show ?thesis
                    by simp
                next
                  assume no_notin_rrept: " no \<notin> set_of rrept"
                  show ?thesis
                  proof (cases "no \<in> set_of lrept")
                    case True
                    with no_notin_rrept rp_notin_lrept ab_nc
                    have ab_nc_no: "lowa no = lowb no \<and> higha no = highb no"
                      apply -
                      apply (erule_tac x=no in allE)
                      apply (erule impE)
                      apply simp
                      apply (subgoal_tac "no \<noteq> rep p")
                      apply simp
                      apply blast
                      done
                    from lowa_higha_def True have 
                      "lowa no = (rep \<propto> low) no \<and> higha no = (rep \<propto> high) no"
                      by auto
                    with ab_nc_no 
                    have "lowb no = (rep \<propto> low) no \<and> highb no =(rep \<propto> high) no" 
                      by simp
                    with rp_notin_lrept True show ?thesis
                      apply (subgoal_tac "no \<noteq> rep p")
                      apply simp
                      apply blast
                      done
                  next
                    assume no_notin_lrept: " no \<notin> set_of lrept"
                    with no_in_rept rept_def no_notin_rrept have no_rp: "no = rep p"
                      by simp
                    with rp_notin_lrept low_lowa_nc 
                    have a_nc: "low no = lowa no \<and> high no = higha no"
                      by auto
                    from rp_notin_rrept no_rp ab_nc 
                    have "(lowa(rep p := pa)) no = lowb no \<and> higha no = highb no"
                      by auto
                    with a_nc pa_def no_rp 
                    have "(rep \<propto> low) no = lowb no \<and> high no = highb no"
                      by auto
                    with pb_def no_rp show ?thesis
                      by simp
                  qed
                qed
              qed
              with rept_dag 
              have "Dag (rep p) lowb (highb(rep p := pb)) rept = 
                    Dag (rep p) (rep \<propto> low) (rep \<propto> high) rept"      
                apply -
                apply (rule heaps_eq_Dag_eq)
                apply auto
                done
              with rept_dag p_nNull show ?thesis
                by simp
            qed
            have "(\<forall>pt. pt \<notin> set_of rept \<longrightarrow> low pt = lowb pt \<and> 
                        high pt = (highb(rep p := pb)) pt)"
            proof (intro allI impI)
              fix pt
              assume pt_notin_rept: "pt \<notin> set_of rept"
              with rept_def obtain
                pt_notin_lrept: "pt \<notin> set_of lrept" and
                pt_notin_rrept: "pt \<notin> set_of rrept" and
                pt_neq_rp: "pt \<noteq> rep p"
                by simp
              with low_lowa_nc ab_nc 
              show "low pt = lowb pt \<and> high pt = (highb(rep p := pb)) pt"
                by auto
            qed
            with rept_end_dag show ?thesis
              by simp
          qed
        done
      qed
    done
  qed
qed
     
end
