(*  Title:       BDD
    Author:      Veronika Ortner and Norbert Schirmer, 2004
    Maintainer:  Norbert Schirmer,  norbert.schirmer at web de
    License:     LGPL
*)

(*
LevellistProof.thy

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

section \<open>Proof of Procedure Levellist\<close>
theory LevellistProof imports ProcedureSpecs Simpl.HeapList begin

hide_const (open) DistinctTreeProver.set_of tree.Node tree.Tip

lemma (in Levellist_impl) Levellist_modifies:
  shows "\<forall>\<sigma>. \<Gamma>\<turnstile>{\<sigma>} \<acute>levellist :== PROC Levellist (\<acute>p, \<acute>m, \<acute>levellist)
             {t. t may_only_modify_globals \<sigma> in [mark,next]}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done

(*a well formed levellist is a list that contains all nodes with variable
i on position i
because the elements of levellist can contain old elements before the call of Levellist,
subdag_eq t pt can not be postulated for all elements of the sublists. One has to make
shure that the initial call of Levellist is parameterized with a levellist with empty sublists.
Otherwise some problems could arise in the call of Reduce!
(\<exists> ptt. (Dag pt low high ptt \<and> subdag_eq (Node lt p rt) ptt \<and> pt\<rightarrow>var = i))
consts wf_levellist :: "dag \<Rightarrow> ref list list \<Rightarrow> ref list list \<Rightarrow>
                        (ref \<Rightarrow> nat) \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> bool"
defs wf_levellist_def: "wf_levellist t levellist_old levellist_new var low high \<equiv>
case t of Tip \<Rightarrow> levellist_old = levellist_new
| (Node lt p rt) \<Rightarrow>
  (\<forall> q. q \<in> set_of t \<longrightarrow> q \<in> set (levellist_new ! (q\<rightarrow>var))) \<and>
  (\<forall> i \<le> p\<rightarrow>var. (\<exists> prx. (levellist_new ! i) = prx@(levellist_old ! i)
                       \<and> (\<forall> pt \<in> set prx. pt \<in> set_of t \<and> pt\<rightarrow>var = i))) \<and>
  (\<forall> i. (p\<rightarrow>var) < i \<longrightarrow> (levellist_new ! i) = (levellist_old ! i)) \<and>
  (length levellist_new = length levellist_old)"
*)


lemma all_stop_cong: "(\<forall>x. P x) = (\<forall>x. P x)"
  by simp

lemma Dag_RefD:
  "\<lbrakk>Dag p l r t; p\<noteq>Null\<rbrakk> \<Longrightarrow>
    \<exists>lt rt. t=Node lt p rt \<and> Dag (l p) l r lt \<and> Dag (r p) l r rt"
  by simp

lemma Dag_unique_ex_conjI:
  "\<lbrakk>Dag p l r t;   P t\<rbrakk> \<Longrightarrow> (\<exists>t. Dag p l r t \<and> P t)"
  by simp

(* FIXME: To BinDag *)
lemma dag_Null [simp]: "dag Null l r = Tip"
  by (simp add: dag_def)

definition first:: "ref list \<Rightarrow> ref" where
"first ps = (case ps of [] \<Rightarrow> Null | (p#rs) \<Rightarrow> p)"

lemma first_simps [simp]:
 "first [] = Null"
 "first (r#rs) = r"
by (simp_all add: first_def)

definition Levellist:: "ref list \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> (ref list list) \<Rightarrow> bool" where
"Levellist hds next ll \<longleftrightarrow> (map first ll = hds) \<and>
                         (\<forall>i < length hds. List (hds ! i) next (ll!i))"

lemma Levellist_unique:
  assumes ll: "Levellist hds next ll"
  assumes ll': "Levellist hds next ll'"
  shows "ll=ll'"
proof -
  from ll have "length ll = length hds"
    by (clarsimp simp add: Levellist_def)
  moreover
  from ll' have "length ll' = length hds"
    by (clarsimp simp add: Levellist_def)
  ultimately have leq: "length ll = length ll'" by simp
  show ?thesis
  proof (rule nth_equalityI [OF leq, rule_format])
    fix i
    assume "i < length ll"
    with ll ll'
    show "ll!i = ll'!i"
      apply (clarsimp simp add: Levellist_def)
      apply (erule_tac x=i in allE)
      apply (erule_tac x=i in allE)
      apply simp
      by (erule List_unique)
  qed
qed

lemma Levellist_unique_ex_conj_simp [simp]:
"Levellist hds next ll \<Longrightarrow> (\<exists>ll. Levellist hds next ll \<and> P ll) = P ll"
by (auto dest: Levellist_unique)


lemma in_set_concat_idx:
  "x \<in> set (concat xss) \<Longrightarrow> \<exists>i < length xss. x \<in> set (xss!i)"
apply (induct xss)
apply  simp
apply clarsimp
apply (erule disjE)
apply  (rule_tac x=0 in exI)
apply  simp
apply auto
done

definition wf_levellist :: "dag \<Rightarrow> ref list list \<Rightarrow> ref list list \<Rightarrow>
                       (ref \<Rightarrow> nat) \<Rightarrow> bool" where
"wf_levellist t levellist_old levellist_new var =
(case t of Tip \<Rightarrow> levellist_old = levellist_new
| (Node lt p rt) \<Rightarrow>
  (\<forall> q. q \<in> set_of t \<longrightarrow> q \<in> set (levellist_new ! (var q))) \<and>
  (\<forall> i \<le> var p. (\<exists> prx. (levellist_new ! i) = prx@(levellist_old ! i)
                       \<and> (\<forall> pt \<in> set prx. pt \<in> set_of t \<and> var pt = i))) \<and>
  (\<forall> i. (var p) < i \<longrightarrow> (levellist_new ! i) = (levellist_old ! i)) \<and>
  (length levellist_new = length levellist_old))"

lemma wf_levellist_subset:
  assumes wf_ll: "wf_levellist t ll ll' var"
  shows "set (concat ll') \<subseteq>  set (concat ll) \<union> set_of t"
proof (cases t)
  case Tip with wf_ll show ?thesis by (simp add: wf_levellist_def)
next
  case (Node lt p rt)
  show ?thesis
  proof -
    {
      fix n
      assume "n \<in> set (concat ll')"
      from in_set_concat_idx [OF this]
      obtain i where i_bound: "i < length ll'" and n_in: "n \<in> set (ll' ! i)"
        by blast
      have "n \<in> set (concat ll) \<union> set_of t"
      proof (cases "i \<le> var p")
        case True
        with wf_ll obtain prx where
          ll'_ll: "ll' ! i = prx @ ll ! i" and
          prx: "\<forall>pt \<in> set prx. pt \<in> set_of t"  and
          leq: "length ll' = length ll"
          apply (clarsimp simp add: wf_levellist_def Node)
          apply (erule_tac x="i" in allE)
          apply clarsimp
          done
        show ?thesis
        proof (cases "n \<in> set prx")
          case True
          with prx have "n \<in> set_of t"
            by simp
          thus ?thesis by simp
        next
          case False
          with n_in ll'_ll
          have "n \<in> set (ll ! i)"
            by simp
          with i_bound leq
          have "n \<in> set (concat ll)"
            by auto
          thus ?thesis by simp
        qed
      next
        case False
        with wf_ll obtain "ll'!i = ll!i" "length ll' = length ll"
          by (auto simp add: wf_levellist_def Node)
        with n_in i_bound
        have "n \<in> set (concat ll)"
          by auto
        thus ?thesis by simp
      qed
    }
    thus ?thesis by auto
  qed
qed
(*
  next
    show "set (concat ll) \<union> set_of t \<subseteq> set (concat ll')"
    proof -
      {
        fix n
        assume "n \<in> set (concat ll)"
        from in_set_concat_idx [OF this]
        obtain i where i_bound: "i < length ll" and n_in: "n \<in> set (ll ! i)"
          by blast
        with wf_ll
        obtain "n \<in> set (ll' ! i)" "length ll = length ll'"
          apply (clarsimp simp add: wf_levellist_def Node)
          apply (case_tac "i \<le> var p")
          apply  fastforce
          apply fastforce
          done
        with i_bound have "n \<in> set (concat ll')"
          by auto
      }
      moreover
      {
        fix n
        assume "n \<in> set_of t"
        with wf_ll obtain "n \<in> set (ll' ! var n)" "length ll' = length ll"
          by (auto simp add: wf_levellist_def Node)
        with root

            next

          proof (cases prx)
            case Nil
            with ll'_ll i_bound leq n_in
            have "n \<in> set (concat ll)"
              by auto
            thus ?thesis by simp
          next
            case (Cons p prx')
            show ?thesis

              apply auto
        *)


(*
consts wf_levellist :: "dag \<Rightarrow> ref list \<Rightarrow> ref list \<Rightarrow>
                        (ref \<Rightarrow> ref) \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow>
                       (ref \<Rightarrow> nat) \<Rightarrow> bool"
defs wf_levellist_def:
"wf_levellist t levellist_old levellist_new next_old next_new var  \<equiv>
case t of Tip \<Rightarrow> levellist_old = levellist_new
| (Node lt p rt) \<Rightarrow>
  (\<forall> q. q \<in> set_of t \<longrightarrow> (\<exists>ns. List (levellist_new ! (var q)) next_new ns \<and>
                                q \<in> set ns)) \<and>
  (\<forall> i \<le> var p. (\<exists>ns_new ns_old.
                  List (levellist_new ! i) next_new ns_new \<and>
                  List (levellist_old ! i) next_old ns_old \<and>
                 (\<exists> prx. ns_new = prx@ns_old
                       \<and> (\<forall> pt \<in> set prx. pt \<in> set_of t \<and> var pt = i)))) \<and>
  (\<forall> i. (var p) < i \<longrightarrow> (\<exists>ns_new ns_old.
                          List (levellist_new ! i) next_new ns_new \<and>
                          List (levellist_old ! i) next_old ns_old \<and>
                          ns_new = ns_old)) \<and>
  (length levellist_new = length levellist_old)"
*)

lemma Levellist_ext_to_all: "((\<exists>ll. Levellist hds next ll \<and> P ll) \<longrightarrow> Q)
       =
       (\<forall>ll. Levellist hds next ll \<and> P ll \<longrightarrow> Q)"
apply blast
done

lemma Levellist_length: "Levellist hds p ll \<Longrightarrow> length ll = length hds"
  by (auto simp add: Levellist_def)


lemma map_update:
  "\<And>i. i < length xss \<Longrightarrow> map f (xss[i := xs]) = (map f xss) [i := f xs]"
apply (induct xss)
apply  simp
apply (case_tac i)
apply  simp
apply simp
done


lemma (in Levellist_impl) Levellist_spec_total':
shows "\<forall>ll \<sigma> t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t
        \<lbrace>\<sigma>. Dag \<acute>p \<acute>low \<acute>high t \<and> (\<acute>p \<noteq> Null \<longrightarrow> (\<acute>p\<rightarrow>\<acute>var) < length \<acute>levellist) \<and>
             ordered t \<acute>var \<and> Levellist \<acute>levellist \<acute>next ll \<and>
             (\<forall>n \<in> set_of t.
              (if \<acute>mark n = \<acute>m
               then n \<in> set (ll ! \<acute>var n) \<and>
                    (\<forall>nt p. Dag n \<acute>low \<acute>high nt \<and> p \<in> set_of nt
                     \<longrightarrow> \<acute>mark p = \<acute>m)
               else n \<notin> set (concat ll)))\<rbrace>
          \<acute>levellist :== PROC Levellist (\<acute>p, \<acute>m, \<acute>levellist)
       \<lbrace>\<exists>ll'. Levellist \<acute>levellist \<acute>next ll' \<and> wf_levellist t ll ll' \<^bsup>\<sigma>\<^esup>var \<and>
        wf_marking t  \<^bsup>\<sigma>\<^esup>mark \<acute>mark \<^bsup>\<sigma>\<^esup>m \<and>
        (\<forall>p. p \<notin> set_of t \<longrightarrow> \<^bsup>\<sigma>\<^esup>next p = \<acute>next p)
        \<rbrace>"
apply (hoare_rule HoareTotal.ProcRec1
           [where r="measure (\<lambda>(s,p). size (dag \<^bsup>s\<^esup>p \<^bsup>s\<^esup>low \<^bsup>s\<^esup>high))"])
apply vcg
apply (rule conjI)
apply  clarify
apply  (rule conjI)
apply   clarify
apply   (clarsimp simp del: BinDag.set_of.simps split del: if_split)
defer
apply   (rule impI)
apply   (clarsimp simp del: BinDag.set_of.simps split del: if_split)
defer
apply   (clarsimp simp add: wf_levellist_def wf_marking_def) (* p=Null*)
apply (simp only: Levellist_ext_to_all )
proof -
  fix ll var low high mark "next" nexta p levellist m lt rt
  assume pnN: "p \<noteq> Null"
  assume mark_p: "mark p = (\<not> m)"
  assume lt: "Dag (low p) low high lt"
  assume rt: "Dag (high p) low high rt"
  from pnN lt rt have Dag_p: "Dag p low high (Node lt p rt)" by simp
  from Dag_p rt
  have size_rt_dec: "size (dag (high p) low high) < size (dag p low high)"
    by (simp only: Dag_dag) simp
  from Dag_p lt
  have size_lt_dec: "size (dag (low p) low high) < size (dag p low high)"
    by (simp only: Dag_dag) simp
  assume ll: "Levellist levellist next ll"

  assume marked_child_ll:
    "\<forall>n \<in> set_of (Node lt p rt).
        if mark n = m
        then n \<in> set (ll ! var n) \<and>
             (\<forall>nt p. Dag n low high nt \<and> p \<in> set_of nt \<longrightarrow> mark p = m)
        else n \<notin> set (concat ll)"
  with mark_p have p_notin_ll: "p \<notin> set (concat ll)"
    by auto
  assume varsll': "var p < length levellist"
  with ll have varsll: "var p < length ll"
    by (simp add: Levellist_length)
  assume orderedt: "ordered (Node lt p rt) var"
  show "(low p \<noteq> Null \<longrightarrow> var (low p) < length levellist) \<and>
          ordered lt var \<and>
          (\<forall>n \<in> set_of lt.
              if mark n = m
              then n \<in> set (ll ! var n) \<and>
                   (\<forall>nt p. Dag n low high nt \<and> p \<in> set_of nt \<longrightarrow> mark p = m)
              else n \<notin> set (concat ll)) \<and>
          size (dag (low p) low high) < size (dag p low high) \<and>
          (\<forall>marka nexta levellist lla.
              Levellist levellist nexta lla \<and>
              wf_levellist lt ll lla var \<and> wf_marking lt mark marka m \<and>
              (\<forall>p. p \<notin> set_of lt \<longrightarrow> next p = nexta p)\<longrightarrow>
              (high p \<noteq> Null \<longrightarrow> var (high p) < length levellist) \<and>
              ordered rt var \<and>
              (\<exists>lla. Levellist levellist nexta lla \<and>
                     (\<forall>n \<in> set_of rt.
                        if marka n = m
                        then n \<in> set (lla ! var n) \<and>
                             (\<forall>nt p. Dag n low high nt \<and> p \<in> set_of nt \<longrightarrow>
                                    marka p = m)
                        else n \<notin> set (concat lla)) \<and>
                     size (dag (high p) low high) < size (dag p low high) \<and>
                     (\<forall>markb nextb levellist llb.
                         Levellist levellist nextb llb \<and>
                         wf_levellist rt lla llb var \<and>
                         wf_marking rt marka markb m \<and>
                         (\<forall>p. p \<notin> set_of rt \<longrightarrow> nexta p = nextb p) \<longrightarrow>
                         (\<exists>ll'. Levellist (levellist[var p := p])
                                 (nextb(p := levellist ! var p)) ll' \<and>
                                wf_levellist (Node lt p rt) ll ll' var \<and>
                                wf_marking (Node lt p rt) mark (markb(p := m)) m \<and>
                                (\<forall>pa. pa \<notin> set_of (Node lt p rt) \<longrightarrow>
                                      next pa =
                                      (if pa = p then levellist ! var p
                                       else nextb pa))))))"
  proof (cases "lt")
    case Tip
    note lt_Tip = this
    show ?thesis
    proof (cases "rt")
      case Tip
      show ?thesis
        using size_rt_dec Tip lt_Tip Tip lt rt
        apply clarsimp
        subgoal premises prems for marka nexta levellista lla markb nextb levellistb llb
        proof -
          have lla: "Levellist levellista nexta lla" by fact
          have llb: "Levellist levellistb nextb llb" by fact
          have wfll_lt: "wf_levellist Tip ll lla var"
                        "wf_marking Tip mark marka m" by fact+

          then have ll_lla: "ll = lla"
            by (simp add: wf_levellist_def)

          moreover
          with wfll_lt lt_Tip lt have "marka = mark"
            by (simp add: wf_marking_def)
          moreover
          have wfll_rt:"wf_levellist Tip lla llb var"
                       "wf_marking Tip marka markb m" by fact+
          then have lla_llb: "lla = llb"
            by (simp add: wf_levellist_def)
          moreover
          with wfll_rt Tip rt have "markb = marka"
            by (simp add: wf_marking_def)
          moreover
          from varsll llb ll_lla lla_llb
          obtain "var p < length levellistb" "var p < length llb"
            by (simp add: Levellist_length)
          with llb pnN
          have llc: "Levellist (levellistb[var p := p]) (nextb(p := levellistb ! var p))
                      (llb[var p := p # llb ! var p])"
            apply (clarsimp simp add: Levellist_def map_update)
            apply (erule_tac x=i in allE)
            apply clarsimp
            apply (subgoal_tac "p \<notin> set (llb ! i) ")
            prefer 2
            using  p_notin_ll ll_lla lla_llb
            apply  simp
            apply (case_tac "i=var p")
            apply  simp
            apply simp
            done
          ultimately
          show ?thesis
            using lt_Tip Tip varsll
            apply (clarsimp simp add: wf_levellist_def wf_marking_def)
          proof -
            fix i
            assume varsllb: "var p < length llb"
            assume "i \<le> var p"
            show "\<exists>prx. llb[var p := p#llb!var p]!i = prx @ llb!i \<and>
                      (\<forall>pt\<in>set prx. pt = p \<and> var pt = i)"
            proof (cases "i = var p")
              case True
              with pnN lt rt varsllb lt_Tip Tip show ?thesis
                apply -
                apply (rule_tac x="[p]" in exI)
                apply (simp add: subdag_eq_def)
                done
            next
              assume "i \<noteq> var p"
              with varsllb show ?thesis
                apply -
                apply (rule_tac x="[]" in exI)
                apply (simp add: subdag_eq_def)
                done
            qed
          qed
        qed
      done
    next
      case (Node dag1 a dag2)
      have rt_node: "rt = Node dag1 a dag2" by fact
      with rt have high_p: "high p = a"
        by simp
      have s: "\<And>nexta. (\<forall>p. next p = nexta p) = (next = nexta)"
        by auto
      show ?thesis
        using size_rt_dec size_lt_dec rt_node lt_Tip Tip lt rt
        apply (clarsimp simp del: set_of_Node split del: if_split simp add: s)
        subgoal premises prems for marka levellista lla
        proof -
          have lla: "Levellist levellista next lla" by fact
          have wfll_lt:"wf_levellist Tip ll lla var"
                       "wf_marking Tip mark marka m" by fact+
          from this have ll_lla: "ll = lla"
            by (simp add: wf_levellist_def)
          moreover
          from wfll_lt lt_Tip lt have marklrec: "marka = mark"
            by (simp add: wf_marking_def)
          from orderedt varsll lla ll_lla rt_node lt_Tip high_p
          have var_highp_bound: "var (high p) < length levellista"
            by (auto simp add: Levellist_length)
          from orderedt high_p rt_node lt_Tip
          have ordered_rt: "ordered (Node dag1 (high p) dag2) var"
            by simp
          from high_p marklrec marked_child_ll lt rt lt_Tip rt_node ll_lla
          have mark_rt: "(\<forall>n\<in>set_of (Node dag1 (high p) dag2).
                if marka n = m
                then n \<in> set (lla ! var n) \<and>
                     (\<forall>nt p. Dag n low high nt \<and> p \<in> set_of nt \<longrightarrow> marka p = m)
                else n \<notin> set (concat lla))"
            apply (simp only: BinDag.set_of.simps)
            apply clarify
            apply (drule_tac x=n in bspec)
            apply  blast
            apply assumption
            done
          show ?thesis
            apply (rule conjI)
            apply  (rule var_highp_bound)
            apply (rule conjI)
            apply  (rule ordered_rt)
            apply (rule conjI)
            apply  (rule mark_rt)
            apply clarify
            apply clarsimp
            subgoal premises prems for markb nextb levellistb llb
            proof -
              have llb: "Levellist levellistb nextb llb" by fact
              have wfll_rt: "wf_levellist (Node dag1 (high p) dag2) lla llb var" by fact
              have wfmarking_rt: "wf_marking (Node dag1 (high p) dag2) marka markb m" by fact
              from wfll_rt varsll llb ll_lla
              obtain var_p_bounds: "var p < length levellistb" "var p < length llb"
                by (simp add: Levellist_length wf_levellist_def)
              with p_notin_ll ll_lla wfll_rt
              have p_notin_llb: "\<forall>i < length llb. p \<notin> set (llb ! i)"
                apply -
                apply (intro allI impI)
                apply (clarsimp simp add: wf_levellist_def)
                apply (case_tac "i \<le> var (high p)")
                apply  (drule_tac x=i in spec)
                using  orderedt rt_node lt_Tip high_p
                apply  clarsimp
                apply (drule_tac x=i in spec)
                apply (drule_tac x=i in spec)
                apply clarsimp
                done
              with llb pnN var_p_bounds
              have llc: "Levellist (levellistb[var p := p])
                            (nextb(p := levellistb ! var p))
                            (llb[var p := p # llb ! var p])"
                apply (clarsimp simp add: Levellist_def map_update)
                apply (erule_tac x=i in allE)
                apply (erule_tac x=i in allE)
                apply clarsimp
                apply (case_tac "i=var p")
                apply  simp
                apply simp
                done
              then show ?thesis
                apply simp
                using wfll_rt wfmarking_rt
                      lt_Tip rt_node varsll orderedt lt rt pnN ll_lla marklrec
                apply (clarsimp simp add: wf_levellist_def wf_marking_def)
                apply (intro conjI)
                apply  (rule allI)
                apply  (rule conjI)
                apply   (erule_tac x="q" in allE)
                apply   (case_tac "var p = var q")
                apply    fastforce
                apply   fastforce
                apply  (case_tac "var p = var q")
                apply   hypsubst_thin
                apply   fastforce
                apply  fastforce
                apply (rule allI)
                apply (rotate_tac 4)
                apply (erule_tac x="i" in allE)
                apply (case_tac "i=var p")
                apply  simp
                apply (case_tac "var (high p) < i")
                apply  simp
                apply simp
                apply (erule exE)
                apply (rule_tac x="prx" in exI)
                apply (intro conjI)
                apply  simp
                apply clarify
                apply (rotate_tac 15)
                apply (erule_tac x="pt" in ballE)
                apply  fastforce
                apply fastforce
                done
            qed
          done
        qed
      done
    qed
  next
    case (Node llt l rlt)
    have lt_Node: "lt = Node llt l rlt" by fact
    from orderedt lt varsll' lt_Node
    obtain ordered_lt:
      "ordered lt var" "(low p \<noteq> Null \<longrightarrow> var (low p) < length levellist)"
      by (cases rt) auto
    from lt lt_Node marked_child_ll
    have mark_lt: "\<forall>n\<in>set_of lt.
     if mark n = m
     then n \<in> set (ll ! var n) \<and>
          (\<forall>nt p. Dag n low high nt \<and> p \<in> set_of nt \<longrightarrow> mark p = m)
     else n \<notin> set (concat ll)"
      apply (simp only: BinDag.set_of.simps)
      apply clarify
      apply (drule_tac x=n in bspec)
      apply  blast
      apply assumption
      done
    show ?thesis
      apply (intro conjI ordered_lt mark_lt size_lt_dec)
      apply (clarify)
      apply (simp add: size_rt_dec split del: if_split)
      apply (simp only: Levellist_ext_to_all)
      subgoal premises prems for marka nexta levellista lla
      proof -
        have lla: "Levellist levellista nexta lla" by fact
        have wfll_lt: "wf_levellist lt ll lla var"  by fact
        have wfmarking_lt:"wf_marking lt mark marka m" by fact
        from wfll_lt lt_Node
        have lla_eq_ll: "length lla = length ll"
          by (simp add: wf_levellist_def)
        with ll lla have lla_eq_ll': "length levellista = length levellist"
          by (simp add: Levellist_length)
        with orderedt rt lt_Node lt varsll'
        obtain ordered_rt:
          "ordered rt var" "(high p \<noteq> Null \<longrightarrow> var (high p) < length levellista)"
          by (cases rt) auto
        from wfll_lt lt_Node
        have nodes_in_lla: "\<forall> q. q \<in> set_of lt \<longrightarrow> q \<in> set (lla ! (q\<rightarrow>var))"
          by (simp add: wf_levellist_def)
        from wfll_lt lt_Node lt
        have lla_st: "(\<forall>i \<le> (low p)\<rightarrow>var.
                        (\<exists>prx. (lla ! i) = prx@(ll ! i) \<and>
                               (\<forall>pt \<in> set prx. pt \<in> set_of lt \<and> pt\<rightarrow>var = i)))"
          by (simp add: wf_levellist_def)
        from wfll_lt lt_Node lt
        have lla_nc: "\<forall>i. ((low p)\<rightarrow>var) < i \<longrightarrow> (lla ! i) = (ll ! i)"
          by (simp add: wf_levellist_def)
        from wfmarking_lt lt_Node lt
        have mot_nc: "\<forall> n. n \<notin> set_of lt \<longrightarrow> mark n = marka n"
          by (simp add: wf_marking_def)
        from wfmarking_lt lt_Node lt
        have mit_marked: "\<forall>n. n \<in> set_of lt \<longrightarrow> marka n = m"
          by (simp add: wf_marking_def)
        from marked_child_ll nodes_in_lla mot_nc mit_marked lla_st
        have mark_rt: "\<forall>n\<in>set_of rt.
               if marka n = m
               then n \<in> set (lla ! var n) \<and>
                   (\<forall>nt p. Dag n low high nt \<and> p \<in> set_of nt \<longrightarrow> marka p = m)
               else n \<notin> set (concat lla)"
          apply -
          apply (rule ballI)
          apply (drule_tac x="n" in bspec)
          apply (simp)
        proof -
          fix n

          assume nodes_in_lla: "\<forall>q. q \<in> set_of lt \<longrightarrow> q \<in> set (lla ! var q)"
          assume mot_nc: "\<forall>n. n \<notin> set_of lt \<longrightarrow> mark n = marka n"
          assume mit_marked: "\<forall>n. n \<in> set_of lt \<longrightarrow> marka n = m"
          assume marked_child_ll: "if mark n = m
           then n \<in> set (ll ! var n) \<and>
                (\<forall>nt p. Dag n low high nt \<and> p \<in> set_of nt \<longrightarrow> mark p = m)
           else n \<notin> set (concat ll)"

          assume lla_st: "\<forall>i\<le>var (low p).
                               \<exists>prx. lla ! i = prx @ ll ! i \<and>
                               (\<forall>pt\<in>set prx. pt \<in> set_of lt \<and> var pt = i)"

          assume n_in_rt: " n \<in> set_of rt"
          show n_in_lla_marked: "if marka n = m
             then n \<in> set (lla ! var n) \<and>
                  (\<forall>nt p. Dag n low high nt \<and> p \<in> set_of nt \<longrightarrow> marka p = m)
             else n \<notin> set (concat lla)"
          proof (cases "n \<in> set_of lt")
            case True
            from True nodes_in_lla have n_in_ll: "n \<in> set (lla ! var n)"
              by simp
            moreover
            from True wfmarking_lt
            have "marka n = m"
              apply (cases lt)
              apply (auto simp add: wf_marking_def)
              done
            moreover
            {
              fix nt p
              assume "Dag n low high nt"
              with lt True have subset_nt_lt: "set_of nt \<subseteq> set_of lt"
                by (rule dag_setof_subsetD)
              moreover assume " p \<in> set_of nt"
              ultimately have "p \<in> set_of lt"
                by blast
              with mit_marked have " marka p = m"
                by simp
            }
            ultimately show ?thesis
              using n_in_rt
              apply clarsimp
              done
          next
            assume n_notin_lt: "n \<notin> set_of lt"
            show ?thesis
            proof (cases "marka n = m")
              case True
              from n_notin_lt mot_nc have marka_eq_mark: "mark n = marka n"
                by simp
              from marka_eq_mark True have n_marked: "mark n = m"
                by simp
              from rt n_in_rt have nnN: "n \<noteq> Null"
                apply -
                apply (rule set_of_nn [rule_format])
                apply fastforce
                apply assumption
                done
              from marked_child_ll n_in_rt marka_eq_mark nnN n_marked
              have n_in_ll: "n \<in> set (ll ! var n)"
                by fastforce
              from marked_child_ll n_in_rt marka_eq_mark nnN n_marked lt rt
              have nt_mark: "\<forall>nt p. Dag n low high nt \<and> p \<in> set_of nt \<longrightarrow> mark p = m"
                by simp
              from nodes_in_lla n_in_ll lla_st
              have n_in_lla: "n \<in> set (lla ! var n)"
              proof (cases "var (low p) < (var n)")
                case True
                with lla_nc have "(lla ! var n) = (ll ! var n)"
                  by fastforce
                with n_in_ll show ?thesis
                  by fastforce
              next
                assume varnslp: " \<not> var (low p) < var n"
                with lla_st
                have ll_in_lla: "\<exists>prx. lla ! (var n) = prx @ ll ! (var n)"
                  apply -
                  apply (erule_tac x="var n" in allE)
                  apply fastforce
                  done
                with n_in_ll show ?thesis
                  by fastforce
              qed
              {
                fix nt pt
                assume nt_Dag: "Dag n low high nt"
                assume pt_in_nt: "pt \<in> set_of nt"
                have " marka pt = m"
                proof (cases "pt \<in> set_of lt")
                  case True
                  with mit_marked show ?thesis
                    by fastforce
                next
                  assume pt_notin_lt: " pt \<notin> set_of lt"
                  with mot_nc have "mark pt = marka pt"
                    by fastforce
                  with nt_mark nt_Dag pt_in_nt show ?thesis
                    by fastforce
                qed
              }
              then have nt_marka:
                "\<forall>nt pt. Dag n low high nt \<and> pt \<in> set_of nt \<longrightarrow> marka pt = m"
                by fastforce
              with n_in_lla nt_marka True show ?thesis
                by fastforce
            next
              case False
              note n_not_marka = this
              with wfmarking_lt n_notin_lt
              have "mark n \<noteq> m"
                by (simp add: wf_marking_def lt_Node)
              with marked_child_ll
              have n_notin_ll: "n \<notin> set (concat ll)"
                by simp
              show ?thesis
              proof (cases "n \<in> set (concat lla)")
                case False with n_not_marka show ?thesis by simp
              next
                case True
                with wf_levellist_subset [OF wfll_lt] n_notin_ll
                have "n \<in> set_of lt"
                  by blast
                with n_notin_lt have False by simp
                thus ?thesis ..
              qed
            qed
          qed
        qed
        show ?thesis
          apply (intro conjI ordered_rt mark_rt)
          apply clarify
          subgoal premises prems for markb nextb levellistb llb
          proof -
            have llb: "Levellist levellistb nextb llb" by fact
            have wfll_rt: "wf_levellist rt lla llb var" by fact
            have wfmarking_rt: "wf_marking rt marka markb m" by fact
            show ?thesis
            proof (cases rt)
              case Tip
              from wfll_rt Tip have lla_llb: "lla = llb"
                by (simp add: wf_levellist_def)
              moreover
              from wfmarking_rt Tip rt have "markb = marka"
                by (simp add: wf_marking_def)
              moreover
              from wfll_lt varsll llb lla_llb
              obtain var_p_bounds: "var p < length levellistb" "var p < length llb"
                by (simp add: Levellist_length wf_levellist_def lt_Node Tip)
              with p_notin_ll lla_llb wfll_lt
              have p_notin_llb: "\<forall>i < length llb. p \<notin> set (llb ! i)"
                apply -
                apply (intro allI impI)
                apply (clarsimp simp add: wf_levellist_def lt_Node)
                apply (case_tac "i \<le> var l")
                apply  (drule_tac x=i in spec)
                using  orderedt Tip lt_Node
                apply  clarsimp
                apply (drule_tac x=i in spec)
                apply (drule_tac x=i in spec)
                apply clarsimp
                done
              with llb pnN var_p_bounds
              have llc: "Levellist (levellistb[var p := p])
                            (nextb(p := levellistb ! var p))
                            (llb[var p := p # llb ! var p])"
                apply (clarsimp simp add: Levellist_def map_update)
                apply (erule_tac x=i in allE)
                apply (erule_tac x=i in allE)
                apply clarsimp
                apply (case_tac "i=var p")
                apply  simp
                apply simp
                done
              ultimately show ?thesis
                using Tip lt_Node varsll orderedt lt rt pnN wfll_lt wfmarking_lt
                apply (clarsimp simp add: wf_levellist_def wf_marking_def)
                apply (intro conjI)
                apply  (rule allI)
                apply  (rule conjI)
                apply   (erule_tac x="q" in allE)
                apply   (case_tac "var p = var q")
                apply    fastforce
                apply   fastforce
                apply  (case_tac "var p = var q")
                apply   hypsubst_thin
                apply   fastforce
                apply  fastforce
                apply (rule allI)
                apply (rotate_tac 4)
                apply (erule_tac x="i" in allE)
                apply (case_tac "i=var p")
                apply  simp
                apply (case_tac "var (low p) < i")
                apply  simp
                apply simp
                apply (erule exE)
                apply (rule_tac x="prx" in exI)
                apply (intro conjI)
                apply  simp
                apply clarify
                apply (rotate_tac 15)
                apply (erule_tac x="pt" in ballE)
                apply  fastforce
                apply fastforce
                done
            next
              case (Node lrt r rrt)
              have rt_Node: "rt = Node lrt r rrt" by fact
              from wfll_rt rt_Node
              have llb_eq_lla: "length llb = length lla"
                by (simp add: wf_levellist_def)
              with llb lla
              have llb_eq_lla': "length levellistb = length levellista"
                by (simp add: Levellist_length)
              from wfll_rt rt_Node
              have nodes_in_llb: "\<forall>q. q \<in> set_of rt \<longrightarrow> q \<in> set (llb ! (q\<rightarrow>var))"
                by (simp add: wf_levellist_def)
              from wfll_rt rt_Node rt
              have llb_st: "(\<forall> i \<le> (high p)\<rightarrow>var.
                             (\<exists> prx. (llb ! i) = prx@(lla ! i) \<and>
                             (\<forall>pt \<in> set prx. pt \<in> set_of rt \<and> pt\<rightarrow>var = i)))"
                by (simp add: wf_levellist_def)
              from wfll_rt rt_Node rt
              have llb_nc:
                "\<forall>i. ((high p)\<rightarrow>var) < i \<longrightarrow> (llb ! i) = (lla ! i)"
                by (simp add: wf_levellist_def)
              from wfmarking_rt rt_Node rt
              have mort_nc: "\<forall>n. n \<notin> set_of rt \<longrightarrow> marka n = markb n"
                by (simp add: wf_marking_def)
              from wfmarking_rt rt_Node rt
              have mirt_marked: "\<forall>n. n \<in> set_of rt \<longrightarrow> markb n = m"
                by (simp add: wf_marking_def)
              with p_notin_ll wfll_rt wfll_lt
              have p_notin_llb: "\<forall>i < length llb. p \<notin> set (llb ! i)"
                apply -
                apply (intro allI impI)
                apply (clarsimp simp add: wf_levellist_def lt_Node rt_Node)
                apply (case_tac "i \<le> var r")
                apply  (drule_tac x=i in spec)
                using  orderedt rt_Node lt_Node
                apply  clarsimp
                apply  (erule disjE)
                apply   clarsimp
                apply  (case_tac "i \<le> var l")
                apply   (drule_tac x=i in spec)
                apply   clarsimp
                apply  clarsimp
                apply (subgoal_tac "llb ! i = lla ! i")
                prefer 2
                apply  clarsimp
                apply (case_tac "i \<le> var l")
                apply  (drule_tac x=i in spec, erule impE, assumption)
                apply  clarsimp
                using  orderedt rt_Node lt_Node
                apply  clarsimp
                apply clarsimp
                done
              from wfll_lt wfll_rt varsll lla llb
              obtain var_p_bounds: "var p < length levellistb" "var p < length llb"
                by (simp add: Levellist_length wf_levellist_def lt_Node rt_Node)
              with p_notin_llb llb pnN var_p_bounds
              have llc: "Levellist (levellistb[var p := p])
                            (nextb(p := levellistb ! var p))
                            (llb[var p := p # llb ! var p])"
                apply (clarsimp simp add: Levellist_def map_update)
                apply (erule_tac x=i in allE)
                apply (erule_tac x=i in allE)
                apply clarsimp
                apply (case_tac "i=var p")
                apply  simp
                apply simp
                done
              then show ?thesis
              proof (clarsimp)
                show "wf_levellist (Node lt p rt) ll (llb[var p := p#llb ! var p]) var \<and>
                      wf_marking (Node lt p rt) mark (markb(p := m)) m"
                proof -
                  have nodes_in_upllb: "\<forall> q. q \<in> set_of (Node lt p rt)
                    \<longrightarrow> q \<in> set (llb[var p :=p # llb ! var p] ! (var q))"
                    apply -
                    apply (rule allI)
                    apply (rule impI)
                  proof -
                    fix q
                    assume q_in_t: "q \<in> set_of (Node lt p rt)"
                    show q_in_upllb:
                      "q \<in> set (llb[var p :=p # llb ! var p] ! (var q))"
                    proof (cases "q \<in> set_of rt")
                      case True
                      with nodes_in_llb have q_in_llb: "q \<in> set (llb ! (var q))"
                        by fastforce
                      from orderedt rt_Node lt_Node lt rt
                      have ordered_rt: "ordered rt var"
                        by fastforce
                      from True rt ordered_rt rt_Node lt lt_Node have "var q \<le> var r"
                        apply -
                        apply (drule subnodes_ordered)
                        apply fastforce
                        apply fastforce
                        apply fastforce
                        done
                      with orderedt rt lt rt_Node lt_Node have "var q < var p"
                        by fastforce
                      then have
                        "llb[var p :=p#llb ! var p] ! var q =
                         llb ! var q"
                        by fastforce
                      with q_in_llb show ?thesis
                        by fastforce
                    next
                      assume q_notin_rt: "q \<notin> set_of rt"
                      show "q \<in> set (llb[var p :=p # llb ! var p] ! var q)"
                      proof (cases "q \<in> set_of lt")
                        case True
                        assume q_in_lt: "q \<in> set_of lt"
                        with nodes_in_lla have q_in_lla: "q \<in> set (lla ! (var q))"
                          by fastforce
                        from orderedt rt_Node lt_Node lt rt
                        have ordered_lt: "ordered lt var"
                          by fastforce
                        from q_in_lt lt ordered_lt rt_Node rt lt_Node
                        have "var q \<le> var l"
                          apply -
                          apply (drule subnodes_ordered)
                          apply fastforce
                          apply fastforce
                          apply fastforce
                          done
                        with orderedt rt lt rt_Node lt_Node have qsp: "var q < var p"
                          by fastforce
                        then show ?thesis
                        proof (cases "var q \<le> var (high p)")
                          case True
                          with llb_st
                          have "\<exists>prx. (llb ! (var q)) = prx@(lla ! (var q))"
                            by fastforce
                          with nodes_in_lla q_in_lla
                          have q_in_llb: "q \<in> set (llb ! (var q))"
                            by fastforce
                          from qsp
                          have "llb[var p :=p#llb ! var p]!var q =
                                   llb ! (var q)"
                            by fastforce
                          with q_in_llb show ?thesis
                            by fastforce
                        next
                          assume "\<not> var q \<le> var (high p)"
                          with llb_nc have "llb ! (var q) = lla ! (var q)"
                            by fastforce
                          with q_in_lla have q_in_llb: "q \<in> set (llb ! (var q))"
                            by fastforce
                          from qsp have
                            "llb[var p :=p # llb ! var p] ! var q = llb ! (var q)"
                            by fastforce
                          with q_in_llb show ?thesis
                            by fastforce
                        qed
                      next
                        assume q_notin_lt: "q \<notin> set_of lt"
                        with q_notin_rt rt lt rt_Node lt_Node q_in_t have qp: "q = p"
                          by fastforce
                        with varsll lla_eq_ll llb_eq_lla have "var p < length llb"
                          by fastforce
                        with qp show ?thesis
                          by simp
                      qed
                    qed
                  qed
                  have prx_ll_st: "\<forall>i \<le> var p.
                   (\<exists>prx. llb[var p :=p#llb!var p]!i = prx@(ll!i) \<and>
                         (\<forall>pt \<in> set prx. pt \<in> set_of (Node lt p rt) \<and> var pt = i))"
                    apply -
                    apply (rule allI)
                    apply (rule impI)
                  proof -
                    fix i
                    assume isep: "i \<le> var p"
                    show "\<exists>prx. llb[var p :=p#llb!var p]!i = prx@ll!i \<and>
                      (\<forall>pt\<in>set prx. pt \<in> set_of (Node lt p rt) \<and> var pt = i)"
                    proof (cases "i = var p")
                      case True
                      with orderedt lt lt_Node rt rt_Node
                      have lpsp: "var (low p) < var p"
                        by fastforce
                      with orderedt lt lt_Node rt rt_Node
                      have hpsp: "var (high p) < var p"
                        by fastforce
                      with lpsp lla_nc
                      have llall: "lla ! var p = ll ! var p"
                        by fastforce
                      with hpsp llb_nc have "llb ! var p = ll ! var p"
                        by fastforce
                      with llb_eq_lla lla_eq_ll isep True varsll lt rt show ?thesis
                        apply -
                        apply (rule_tac x="[p]" in exI)
                        apply (rule conjI)
                        apply simp
                        apply (rule ballI)
                        apply fastforce
                        done
                    next
                      assume inp: " i \<noteq> var p"
                      show ?thesis
                      proof (cases "var (low p) < i")
                        case True
                        with lla_nc have llall: "lla ! i = ll ! i"
                          by fastforce
                        assume vpsi: "var (low p) < i"
                        show ?thesis
                        proof (cases "var (high p) < i")
                          case True
                          with llall llb_nc have "llb ! i = ll ! i"
                            by fastforce
                          with inp True vpsi varsll lt rt show ?thesis
                            apply -
                            apply (rule_tac x="[]" in exI)
                            apply (rule conjI)
                            apply simp
                            apply (rule ballI)
                            apply fastforce
                            done
                        next
                          assume isehp: " \<not> var (high p) < i"
                          with vpsi lla_nc have lla_ll: "lla ! i = ll ! i"
                            by fastforce
                          with isehp llb_st
                          have prx_lla: "\<exists>prx. llb ! i = prx @ lla ! i \<and>
                            (\<forall>pt\<in>set prx. pt \<in> set_of rt \<and> var pt = i)"
                            apply -
                            apply (erule_tac x="i" in allE)
                            apply simp
                            done
                          with lla_ll inp rt show ?thesis
                            apply -
                            apply (erule exE)
                            apply (rule_tac x="prx" in exI)
                            apply simp
                            done
                        qed
                      next
                        assume iselp: "\<not> var (low p) < i"
                        show ?thesis
                        proof (cases "var (high p) < i")
                          case True
                          with llb_nc have llb_ll: "llb ! i = lla ! i"
                            by fastforce
                          with iselp lla_st
                          have prx_ll: "\<exists>prx. lla ! i = prx @ ll ! i \<and>
                            (\<forall>pt\<in>set prx. pt \<in> set_of lt \<and> var pt = i)"
                            apply -
                            apply (erule_tac x="i" in allE)
                            apply simp
                            done
                          with llb_ll inp lt show ?thesis
                            apply -
                            apply (erule exE)
                            apply (rule_tac x="prx" in exI)
                            apply simp
                            done
                        next
                          assume isehp: " \<not> var (high p) < i"
                          from iselp lla_st
                          have prxl: "\<exists>prx. lla ! i = prx @ ll ! i \<and>
                            (\<forall>pt\<in>set prx. pt \<in> set_of lt \<and> var pt = i)"
                            by fastforce
                          from isehp llb_st
                          have prxh: "\<exists>prx. llb ! i = prx @ lla ! i \<and>
                            (\<forall>pt\<in>set prx. pt \<in> set_of rt \<and> var pt = i)"
                            by fastforce
                          with prxl inp lt pnN rt show ?thesis
                            apply -
                            apply (elim exE)
                            apply (rule_tac x="prxa @ prx" in exI)
                            apply simp
                            apply (elim conjE)
                            apply fastforce
                            done
                        qed
                      qed
                    qed
                  qed
                  have big_Nodes_nc: "\<forall>i. (p->var) < i
                    \<longrightarrow> (llb[var p :=p # llb ! var p]) ! i = ll ! i"
                    apply -
                    apply (rule allI)
                    apply (rule impI)
                  proof -
                    fix i
                    assume psi: "var p < i"
                    with orderedt lt rt lt_Node rt_Node have lpsi: "var (low p) < i"
                      by fastforce
                    with lla_nc have lla_ll: "lla ! i = ll ! i"
                      by fastforce
                    from psi orderedt lt rt lt_Node rt_Node have hpsi: "var (high p) < i"
                      by fastforce
                    with llb_nc have llb_lla: "llb ! i = lla ! i"
                      by fastforce
                    from psi
                    have upllb_llb: "llb[var p :=p#llb!var p]!i = llb!i"
                      by fastforce
                    from upllb_llb llb_lla lla_ll
                    show "llb[var p :=p # llb ! var p] ! i = ll ! i"
                      by fastforce
                  qed
                  from lla_eq_ll llb_eq_lla
                  have length_eq: "length (llb[var p :=p # llb ! var p]) = length ll"
                    by fastforce
                  from length_eq big_Nodes_nc prx_ll_st nodes_in_upllb
                  have wf_ll_upllb:
                    "wf_levellist (Node lt p rt) ll (llb[var p :=p # llb ! var p]) var"
                    by (simp add: wf_levellist_def)
                  have mark_nc:
                    "\<forall> n. n \<notin> set_of (Node lt p rt) \<longrightarrow> (markb(p:=m)) n = mark n"
                    apply -
                    apply (rule allI)
                    apply (rule impI)
                  proof -
                    fix n
                    assume nnit: "n \<notin> set_of (Node lt p rt)"
                    with lt rt have nnilt: " n \<notin> set_of lt"
                      by fastforce
                    from nnit lt rt have nnirt: " n \<notin> set_of rt"
                      by fastforce
                    with nnilt mot_nc mort_nc have mb_eq_m: "markb n = mark n"
                      by fastforce
                    from nnit have "n\<noteq>p"
                      by fastforce
                    then have upmarkb_markb: "(markb(p :=m)) n = markb n"
                      by fastforce
                    with mb_eq_m show "(markb(p :=m)) n = mark n"
                      by fastforce
                  qed
                  have mark_c: "\<forall> n. n \<in> set_of (Node lt p rt) \<longrightarrow> (markb(p :=m)) n = m"
                    apply -
                    apply (intro allI)
                    apply (rule impI)
                  proof -
                    fix n
                    assume nint: " n \<in> set_of (Node lt p rt)"
                    show "(markb(p :=m)) n = m"
                    proof (cases "n=p")
                      case True
                      then show ?thesis
                        by fastforce
                    next
                      assume nnp: " n \<noteq> p"
                      show ?thesis
                      proof (cases "n \<in> set_of rt")
                        case True
                        with mirt_marked have "markb n = m"
                          by fastforce
                        with nnp show ?thesis
                          by fastforce
                      next
                        assume nninrt: " n \<notin> set_of rt"
                        with nint nnp have ninlt: "n \<in> set_of lt"
                          by fastforce
                        with mit_marked have marka_m: "marka n = m"
                          by fastforce
                        from mort_nc nninrt have "marka n = markb n"
                          by fastforce
                        with marka_m have "markb n = m"
                          by fastforce
                        with nnp show ?thesis
                          by fastforce
                      qed
                    qed
                  qed
                  from mark_c mark_nc
                  have wf_mark: "wf_marking (Node lt p rt) mark (markb(p :=m)) m"
                    by (simp add: wf_marking_def)
                  with wf_ll_upllb show ?thesis
                    by fastforce
                qed
              qed
            qed
          qed
        done
      qed
    done
  qed
next
  fix var low high p lt rt and levellist and
    ll::"ref list list" and mark::"ref \<Rightarrow> bool" and "next"
  assume pnN: "p \<noteq> Null"
  assume ll: "Levellist levellist next ll"
  assume vpsll: "var p < length levellist"
  assume orderedt: "ordered (Node lt p rt) var"
  assume marked_child_ll: "\<forall>n\<in>set_of (Node lt p rt).
           if mark n = mark p
           then n \<in> set (ll ! var n) \<and>
                (\<forall>nt pa. Dag n low high nt \<and> pa \<in> set_of nt \<longrightarrow> mark pa = mark p)
           else n \<notin> set (concat ll)"
  assume lt: "Dag (low p) low high lt"
  assume rt: "Dag (high p) low high rt"
  show "wf_levellist (Node lt p rt) ll ll var \<and>
        wf_marking (Node lt p rt) mark mark (mark p)"
  proof -
    from marked_child_ll pnN lt rt have marked_st:
      "(\<forall>pa. pa \<in> set_of (Node lt p rt) \<longrightarrow> mark pa = mark p)"
      apply -
      apply (drule_tac x="p" in bspec)
      apply  simp
      apply (clarsimp)
      apply (erule_tac x="(Node lt p rt)" in allE)
      apply simp
      done
    have nodest_in_ll:
      "\<forall>q. q \<in> set_of (Node lt p rt) \<longrightarrow> q \<in> set (ll ! var q)"
    proof -
      from marked_child_ll pnN have pinll: "p \<in> set (ll ! var p)"
        apply -
        apply (drule_tac x="p" in bspec)
        apply  simp
        apply fastforce
        done
      from marked_st marked_child_ll lt rt show ?thesis
        apply -
        apply (rule allI)
        apply (erule_tac x="q" in allE)
        apply (rule impI)
        apply (erule impE)
        apply  assumption
        apply (drule_tac x="q" in bspec)
        apply  simp
        apply fastforce
        done
    qed
    have levellist_nc: "\<forall> i \<le> var p. (\<exists> prx. ll ! i = prx@(ll ! i) \<and>
      (\<forall> pt \<in> set prx. pt \<in> set_of (Node lt p rt) \<and> var pt = i))"
      apply -
      apply (rule allI)
      apply (rule impI)
      apply (rule_tac x="[]" in exI)
      apply fastforce
      done
    have ll_nc: "\<forall> i. (var p) < i \<longrightarrow> ll ! i = ll ! i"
      by fastforce
    have length_ll: "length ll = length ll"
      by fastforce
    with ll_nc levellist_nc nodest_in_ll
    have wf: "wf_levellist (Node lt p rt) ll ll var"
      by (simp add: wf_levellist_def)
    have m_nc: "\<forall> n. n \<notin> set_of (Node lt p rt) \<longrightarrow> mark n = mark n"
      by fastforce
    from marked_st have "\<forall> n. n \<in> set_of (Node lt p rt) \<longrightarrow> mark n = mark p"
      by fastforce
    with m_nc have " wf_marking (Node lt p rt) mark mark (mark p)"
      by (simp add: wf_marking_def)
    with wf show ?thesis
      by fastforce
  qed
qed

lemma allD: "\<forall>ll. P ll \<Longrightarrow> P ll"
  by blast

lemma replicate_spec: "\<lbrakk>\<forall>i < n. xs ! i = x; n=length xs\<rbrakk>
  \<Longrightarrow> replicate (length xs) x = xs"
apply hypsubst_thin
apply (induct xs)
apply  simp
apply force
done

lemma (in Levellist_impl) Levellist_spec_total:
shows "\<forall>\<sigma> t. \<Gamma>,\<Theta>\<turnstile>\<^sub>t
        \<lbrace>\<sigma>. Dag \<acute>p \<acute>low \<acute>high t \<and> (\<forall>i < length \<acute>levellist. \<acute>levellist ! i = Null) \<and>
             length \<acute>levellist  = \<acute>p \<rightarrow> \<acute>var + 1 \<and>
             ordered t \<acute>var \<and> (\<forall>n \<in> set_of t. \<acute>mark n = (\<not> \<acute>m) )\<rbrace>
          \<acute>levellist :== PROC Levellist (\<acute>p, \<acute>m, \<acute>levellist)
       \<lbrace>\<exists>ll. Levellist \<acute>levellist \<acute>next ll \<and> wf_ll t ll \<^bsup>\<sigma>\<^esup>var  \<and>
         length \<acute>levellist = \<^bsup>\<sigma>\<^esup>p \<rightarrow> \<^bsup>\<sigma>\<^esup>var + 1 \<and>
         wf_marking t \<^bsup>\<sigma>\<^esup>mark \<acute>mark \<^bsup>\<sigma>\<^esup>m \<and>
         (\<forall>p. p \<notin> set_of t \<longrightarrow> \<^bsup>\<sigma>\<^esup>next p = \<acute>next p)\<rbrace>"
apply (hoare_rule HoareTotal.conseq)
apply  (rule_tac ll="replicate (\<^bsup>\<sigma>\<^esup>p\<rightarrow>\<^bsup>\<sigma>\<^esup>var + 1) []" in allD [OF Levellist_spec_total'])
apply (intro allI impI)
apply (rule_tac x=\<sigma> in exI)
apply (rule_tac x=t in exI)
apply (rule conjI)
apply  (clarsimp split:if_split_asm simp del: concat_replicate_trivial)
apply  (frule replicate_spec [symmetric])
apply   (simp)
apply  (clarsimp simp add: Levellist_def )
apply  (case_tac i)
apply   simp
apply  simp
apply (simp add: Collect_conv_if split:if_split_asm)
apply vcg_step
apply (elim exE conjE)
apply (rule_tac x=ll' in exI)
apply simp
apply (thin_tac "\<forall>p. p \<notin> set_of t \<longrightarrow> next p = nexta p")
apply (simp add: wf_levellist_def wf_ll_def)
apply (case_tac "t = Tip")
apply  simp
apply  (rule conjI)
apply   clarsimp
apply   (case_tac k)
apply    simp
apply   simp
apply  (subgoal_tac "length ll'=Suc (var Null)")
apply   (simp add: Levellist_length)
apply  fastforce
apply (split dag.splits)
apply  simp
apply (elim conjE)
apply (intro conjI)
apply   (rule allI)
apply   (erule_tac x="pa" in allE)
apply   clarify
prefer 2
apply  (simp add: Levellist_length)
apply (rule allI)
apply (rule impI)
apply (rule ballI)
apply (rotate_tac 11)
apply (erule_tac x="k" in allE)
apply (rename_tac dag1 ref dag2 k pa)
apply (subgoal_tac "k <= var ref")
prefer 2
apply  (subgoal_tac "ref = p")
apply   simp
apply  clarify
apply  (erule_tac ?P = "Dag p low high (Node dag1 ref dag2)" in rev_mp)
apply  (simp (no_asm))
apply (rotate_tac 14)
apply (erule_tac x=k in allE)
apply clarify
apply (erule_tac x=k in allE)
apply clarify
apply (case_tac k)
apply  simp
apply simp
done

end
