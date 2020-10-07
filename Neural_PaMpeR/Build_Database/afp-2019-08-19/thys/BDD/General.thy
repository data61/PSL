(*  Title:       BDD
    Author:      Veronika Ortner and Norbert Schirmer, 2004
    Maintainer:  Norbert Schirmer,  norbert.schirmer at web de
    License:     LGPL
*)

(*  
General.thy

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

section \<open>General Lemmas on BDD Abstractions\<close>

theory General imports BinDag begin

definition subdag_eq:: "dag \<Rightarrow> dag \<Rightarrow> bool" where
"subdag_eq t\<^sub>1 t\<^sub>2 = (t\<^sub>1 = t\<^sub>2 \<or> subdag t\<^sub>1 t\<^sub>2)"
(*"subtree_eq Tip t = (if t = Tip then True else False)"
"subtree_eq (Node l a r) t = (t=(Node l a r) \<or> subtree_eq l t \<or> subtree_eq r t)"*)

primrec root :: "dag \<Rightarrow> ref"
where
"root Tip = Null" |
"root (Node l a r) = a"

fun isLeaf :: "dag \<Rightarrow> bool" where
"isLeaf Tip = False"
| "isLeaf (Node Tip v Tip) = True"
| "isLeaf (Node (Node l v\<^sub>1 r) v\<^sub>2 Tip) = False"
| "isLeaf (Node Tip v\<^sub>1 (Node l v\<^sub>2 r)) = False"

datatype bdt = Zero | One | Bdt_Node bdt nat bdt

fun bdt_fn :: "dag \<Rightarrow> (ref \<Rightarrow> nat) \<Rightarrow> bdt option" where
"bdt_fn Tip = (\<lambda>bdtvar . None)"
| "bdt_fn (Node Tip vref Tip) = 
    (\<lambda>bdtvar . 
          (if (bdtvar vref = 0) 
           then Some Zero 
           else (if (bdtvar vref = 1) 
                 then Some One
                 else None)))"  
| "bdt_fn (Node Tip vref (Node l vref1 r)) = (\<lambda>bdtvar . None)"
| "bdt_fn (Node (Node l vref1 r) vref Tip) = (\<lambda>bdtvar . None)"
| "bdt_fn (Node (Node l1 vref1 r1) vref (Node l2 vref2 r2)) = 
  (\<lambda>bdtvar .
    (if (bdtvar vref = 0 \<or> bdtvar vref = 1) 
     then None 
     else  
      (case (bdt_fn (Node l1 vref1 r1) bdtvar) of 
       None \<Rightarrow> None
       |(Some b1) \<Rightarrow>
         (case (bdt_fn (Node l2 vref2 r2) bdtvar) of 
          None \<Rightarrow> None
         |(Some b2) \<Rightarrow> Some (Bdt_Node b1 (bdtvar vref) b2)))))"

(*
Kongruenzregeln sind das Feintuning für den Simplifier (siehe Kapitel 9 im Isabelle
Tutorial). Im Fall von case wird standardmäßig nur die case bedingung nicht
aber die einzelnen Fälle simplifiziert, analog dazu beim if. Dies simuliert die
Auswertungsstrategie einer Programmiersprache, da wird auch zunächst nur die
Bedingung vereinfacht. Will man mehr so kann man die entsprechenden Kongruenz 
regeln dazunehmen.
*)
abbreviation "bdt == bdt_fn"

primrec eval :: "bdt \<Rightarrow> bool list \<Rightarrow> bool"
where
"eval Zero env = False" |
"eval One env  = True" |
"eval (Bdt_Node l v r) env  = (if (env ! v) then eval r env else eval l env)"
 
(*A given bdt is ordered if it is a One or Zero or its value is smaller than
its parents value*)
fun ordered_bdt:: "bdt \<Rightarrow> bool" where
"ordered_bdt Zero = True"
| "ordered_bdt One = True"
| "ordered_bdt (Bdt_Node (Bdt_Node l1 v1 r1) v (Bdt_Node l2 v2 r2)) = 
    ((v1 < v) \<and> (v2 < v) \<and> 
     (ordered_bdt (Bdt_Node l1 v1 r1)) \<and> (ordered_bdt (Bdt_Node l2 v2 r2)))"
| "ordered_bdt (Bdt_Node (Bdt_Node l1 v1 r1) v r) = 
    ((v1 < v) \<and> (ordered_bdt (Bdt_Node l1 v1 r1)))"
| "ordered_bdt (Bdt_Node l v (Bdt_Node l2 v2 r2)) = 
    ((v2 < v) \<and> (ordered_bdt (Bdt_Node l2 v2 r2)))"
| "ordered_bdt (Bdt_Node l v r) = True"

(*In case t = (Node Tip v Tip) v should have the values 0 or 1. This is not checked by this function*)
fun ordered:: "dag \<Rightarrow> (ref\<Rightarrow>nat) \<Rightarrow> bool" where
"ordered Tip = (\<lambda> var. True)"
| "ordered (Node (Node l\<^sub>1 v\<^sub>1 r\<^sub>1) v (Node l\<^sub>2 v\<^sub>2 r\<^sub>2)) = 
    (\<lambda> var. (var v\<^sub>1 < var v \<and> var v\<^sub>2 < var v) \<and> 
        (ordered (Node l\<^sub>1 v\<^sub>1 r\<^sub>1) var) \<and> (ordered (Node l\<^sub>2 v\<^sub>2 r\<^sub>2) var))"
| "ordered (Node Tip v Tip) = (\<lambda> var. (True))"
| "ordered (Node Tip v r) = 
     (\<lambda> var. (var (root r) < var v) \<and> (ordered r var))"
| "ordered (Node l v Tip) = 
     (\<lambda> var. (var (root l) < var v) \<and> (ordered l var))"
 

(*Calculates maximal value in a non ordered bdt. Does not test parents of the 
given bdt*)
primrec max_var :: "bdt \<Rightarrow> nat"
where
"max_var Zero = 0" |
"max_var One = 1" |
"max_var (Bdt_Node l v r) = max v (max (max_var l) (max_var r))"

lemma eval_zero: "\<lbrakk>bdt (Node l v r) var = Some x; 
var (root (Node l v r)) = (0::nat)\<rbrakk> \<Longrightarrow> x = Zero"
apply (cases l)
apply (cases r)
apply simp
apply simp
apply (cases r)
apply simp
apply simp
done

lemma bdt_Some_One_iff [simp]: 
  "(bdt t var = Some One) = (\<exists> p. t = Node Tip p Tip \<and> var p = 1)"
apply (induct t rule: bdt_fn.induct)
apply (auto split: option.splits) (*in order to split the cases Zero and One*)
done

lemma bdt_Some_Zero_iff [simp]: 
  "(bdt t var = Some Zero) = (\<exists> p. t = Node Tip p Tip \<and> var p = 0)"
apply (induct t rule: bdt_fn.induct)
apply (auto split: option.splits)
done


lemma bdt_Some_Node_iff [simp]: 
 "(bdt t var = Some (Bdt_Node bdt1 v bdt2)) = 
    (\<exists> p l r. t = Node l p r \<and> bdt l var = Some bdt1 \<and> bdt r var = Some bdt2 \<and> 
               1 < v \<and> var p = v )"
apply (induct t rule: bdt_fn.induct)
prefer 5
apply (fastforce split: if_splits option.splits)
apply auto
done

lemma balanced_bdt: 
"\<And> p bdt1. \<lbrakk> Dag p low high t; bdt t var = Some bdt1; no \<in> set_of t\<rbrakk> 
 \<Longrightarrow> (low no = Null) = (high no = Null)"
proof (induct t)
  case Tip
  then show ?case by simp
next
  case (Node lt a rt)
  note NN= this
  have bdt1: "bdt (Node lt a rt) var = Some bdt1" by fact
  have no_in_t: " no \<in> set_of (Node lt a rt)" by fact
  have p_tree: "Dag p low high (Node lt a rt)" by fact
  from Node.prems obtain 
    lt: "Dag (low p) low high lt" and 
    rt: "Dag (high p) low high rt" 
    by auto
  show ?case  
  proof (cases lt)
    case (Node llt l rlt)
    note Nlt=this
    show ?thesis
    proof (cases rt)
      case (Node lrt r rrt)
      note Nrt=this
      from Nlt Nrt bdt1 obtain lbdt rbdt where 
        lbdt_def: "bdt lt var = Some lbdt" and 
        rbdt_def: "bdt rt var = Some rbdt" and 
        bdt1_def: "bdt1 = Bdt_Node lbdt (var a) rbdt"
        by (auto split: if_split_asm option.splits)
      from no_in_t show ?thesis
      proof (simp, elim disjE)
        assume " no = a"
        with p_tree Nlt Nrt show ?thesis
          by auto
      next
        assume "no \<in> set_of lt"
        with Node.hyps lbdt_def lt show ?thesis
          by simp
      next
        assume "no \<in> set_of rt"
        with Node.hyps rbdt_def rt show ?thesis
          by simp
      qed
    next
      case Tip
      with Nlt bdt1 show ?thesis
        by simp
    qed
  next
    case Tip
    note ltTip=this
    show ?thesis
    proof (cases rt)
      case Tip
      with ltTip bdt1 no_in_t p_tree show ?thesis
        by auto
    next
      case (Node rlt r rrt)
      with bdt1 ltTip show ?thesis
        by simp
    qed
  qed
qed

primrec dag_map :: "(ref \<Rightarrow> ref) \<Rightarrow> dag \<Rightarrow> dag"
where
"dag_map f Tip = Tip" |
"dag_map f (Node l a r) = (Node (dag_map f l) (f a) (dag_map f r))"


definition wf_marking :: "dag \<Rightarrow> (ref \<Rightarrow> bool) \<Rightarrow> (ref \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> bool"
where
"wf_marking t mark_old mark_new marked =
(case t of Tip \<Rightarrow> mark_new = mark_old
| (Node lt p rt) \<Rightarrow>
  (\<forall> n. n \<notin> set_of t \<longrightarrow> mark_new n = mark_old n) \<and>
  (\<forall> n. n \<in> set_of t \<longrightarrow> mark_new n = marked))"

definition dag_in_levellist:: "dag \<Rightarrow> (ref list list) \<Rightarrow> (ref \<Rightarrow> nat) \<Rightarrow> bool"
where "dag_in_levellist t levellist var = (t \<noteq> Tip \<longrightarrow>
       (\<forall> st. subdag_eq t st \<longrightarrow> root st \<in> set (levellist ! (var (root st)))))"

lemma set_of_nn: "\<lbrakk> Dag p low high t; n \<in> set_of t\<rbrakk> \<Longrightarrow> n \<noteq> Null"
apply (induct t)
apply simp
apply auto
done

lemma subnodes_ordered [rule_format]: 
"\<forall>p. n \<in> set_of t \<longrightarrow> Dag p low high t \<longrightarrow> ordered t var \<longrightarrow> var n <= var p"
apply (induct t)
apply simp
apply (intro allI)
apply (erule_tac x="low p" in allE)
apply (erule_tac x="high p" in allE)
apply clarsimp
apply (case_tac t1)
apply (case_tac t2)
apply simp
apply fastforce
apply (case_tac t2)
apply fastforce
apply fastforce
done


lemma ordered_set_of: 
"\<And> x. \<lbrakk>ordered t var; x \<in> set_of t\<rbrakk> \<Longrightarrow> var x <= var (root t)"
apply (induct t)
apply simp
apply simp
apply (elim disjE)
apply simp
apply (case_tac t1)
apply simp
apply (case_tac t2)
apply fastforce
apply fastforce
apply (case_tac t2)
apply simp
apply (case_tac t1)
apply fastforce
apply fastforce
done

lemma dag_setofD: "\<And> p low high n. \<lbrakk> Dag p low high t; n \<in> set_of t \<rbrakk> \<Longrightarrow> 
  (\<exists> nt. Dag n low high nt) \<and> (\<forall> nt. Dag n low high nt \<longrightarrow> set_of nt \<subseteq> set_of t)"
apply (induct t)
apply simp
apply auto
apply fastforce
apply (fastforce dest: Dag_unique)
apply (fastforce dest: Dag_unique)
apply blast
apply blast
done

lemma dag_setof_exD: "\<lbrakk>Dag p low high t; n \<in> set_of t\<rbrakk> \<Longrightarrow> \<exists> nt. Dag n low high nt"
apply (simp add: dag_setofD)
done

lemma dag_setof_subsetD: "\<lbrakk>Dag p low high t; n \<in> set_of t; Dag n low high nt\<rbrakk> \<Longrightarrow> set_of nt \<subseteq> set_of t"
apply (simp add: dag_setofD)
done  

lemma subdag_parentdag_low: "not <= lt \<Longrightarrow> not <= (Node lt p rt)"
apply (cases "not = lt")
apply (cases lt)
apply simp
apply (cases rt)
apply simp
apply (simp add: le_dag_def less_dag_def)
apply (simp add: le_dag_def less_dag_def)
apply (simp add: le_dag_def less_dag_def)
apply (simp add: le_dag_def less_dag_def)
done

lemma subdag_parentdag_high: "not <= rt \<Longrightarrow> not <= (Node lt p rt)"
apply (cases "not = rt")
apply (cases lt)
apply simp
apply (cases rt)
apply simp
apply (simp add: le_dag_def less_dag_def)
apply (simp add: le_dag_def less_dag_def)
apply (simp add: le_dag_def less_dag_def)
apply (simp add: le_dag_def less_dag_def)
done

lemma set_of_subdag: "\<And> p not no. 
\<lbrakk>Dag p low high t; Dag no low high not; no \<in> set_of t\<rbrakk> \<Longrightarrow> not <= t"
proof (induct t)
  case Tip
  then show ?case by simp
next
  case (Node lt po rt)
  note rtNode=this
  from Node.prems have ppo: "p=po" 
    by simp
  show ?case
  proof (cases "no = p")
    case True
    with ppo Node.prems have "not = (Node lt po rt)"
      by (simp add: Dag_unique del: Dag_Ref)
    with Node.prems ppo show ?thesis by (simp add: subdag_eq_def)
  next
    assume " no \<noteq> p"
    with Node.prems have no_in_ltorrt: "no \<in> set_of lt \<or> no \<in> set_of rt"
      by simp
    show ?thesis
    proof (cases "no \<in> set_of lt")
      case True
      from Node.prems ppo have "Dag (low po) low high lt"
        by simp
      with Node.prems ppo True have "not <= lt"
        apply -
        apply (rule Node.hyps)
        apply assumption+
        done
      with Node.prems no_in_ltorrt show ?thesis
        apply -
        apply (rule subdag_parentdag_low)
        apply simp
        done
    next
      assume "no \<notin> set_of lt"
      with no_in_ltorrt have no_in_rt: "no \<in> set_of rt"
        by simp
      from Node.prems ppo have "Dag (high po) low high rt"
        by simp
      with Node.prems ppo no_in_rt have "not <= rt"
        apply -
        apply (rule Node.hyps)
        apply assumption+
        done
      with Node.prems no_in_rt show ?thesis
        apply -
        apply (rule subdag_parentdag_high)
        apply simp
        done
    qed
  qed
qed

lemma children_ordered: "\<lbrakk>ordered (Node lt p rt) var\<rbrakk> \<Longrightarrow> 
ordered lt var \<and> ordered rt var"
proof (cases lt)
  case Tip
  note ltTip=this
  assume  orderedNode: "ordered (Node lt p rt) var"
  show ?thesis
  proof (cases rt)
    case Tip
    note rtTip = this
    with ltTip show ?thesis
      by simp
  next
    case (Node lrt r rrt)
    with orderedNode ltTip show ?thesis
      by simp
  qed
next
  case (Node llt l rlt)
  note ltNode=this
  assume orderedNode: "ordered (Node lt p rt) var"
  show ?thesis
  proof (cases rt)
    case Tip
    note rtTip = this
    with orderedNode ltNode show ?thesis by simp
  next
    case (Node lrt r rrt)
    note rtNode = this
    with orderedNode ltNode show ?thesis by simp
  qed
qed
    
lemma ordered_subdag: "\<lbrakk>ordered t var; not <= t\<rbrakk> \<Longrightarrow> ordered not var"
proof (induct t)
  case Tip
  then show ?thesis by (simp add: less_dag_def le_dag_def)
next
  case (Node lt p rt)
  show ?case 
  proof (cases "not = Node lt p rt")
    case True
    with Node.prems show ?thesis by simp
  next
    assume notnt: "not \<noteq> Node lt p rt"
    with Node.prems have notstltorrt: "not <= lt \<or> not <= rt"
      apply -
      apply (simp add: less_dag_def le_dag_def)
      apply fastforce
      done
    from Node.prems have ord_lt: "ordered lt var"
      apply -
      apply (drule children_ordered)
      apply simp
      done
    from Node.prems have ord_rt: "ordered rt var"
      apply -
      apply (drule children_ordered)
      apply simp
      done
    show ?thesis 
    proof (cases "not <= lt")
      case True
      with ord_lt show ?thesis
        apply -
        apply (rule Node.hyps)
        apply assumption+
        done
    next
      assume "\<not> not \<le> lt"
      with notstltorrt have notinrt: "not <= rt"
        by simp
      from Node.hyps have hyprt: "\<lbrakk>ordered rt var; not \<le> rt\<rbrakk> \<Longrightarrow> ordered not var" by simp
      from notinrt ord_rt show ?thesis
        apply -
        apply (rule hyprt)
        apply assumption+
        done
    qed
  qed
qed


lemma subdag_ordered: 
"\<And> not no p. \<lbrakk>ordered t var; Dag p low high t; Dag no low high not; 
              no \<in> set_of t\<rbrakk> \<Longrightarrow> ordered not var"
proof (induct t) 
  case Tip
  from Tip.prems show ?case by simp
next
  case (Node lt po rt)
  note nN=this
  show ?case 
  proof (cases lt)
    case Tip
    note ltTip=this
    show ?thesis
    proof (cases rt)
      case Tip
      from Node.prems have ppo: "p=po"
        by simp
      from Tip ltTip Node.prems have "no=p"
        by simp
      with ppo Node.prems have "not=(Node lt po rt)"
        by (simp del: Dag_Ref add: Dag_unique)
      with Node.prems show ?thesis by simp
    next
      case (Node lrnot rn rrnot)
      from Node.prems ltTip Node have ord_rt: "ordered rt var"
        by simp
      from Node.prems have ppo: "p=po"
        by simp
      from Node.prems have ponN: "po \<noteq> Null"
        by auto
      with ppo ponN ltTip Node.prems have *: "Dag (high po) low high rt"
        by auto
      show ?thesis
      proof (cases "no=po")
        case True
        with ppo Node.prems have "not = Node lt po rt"
          by (simp del: Dag_Ref add: Dag_unique)
        with Node.prems show ?thesis
          by simp
      next
        case False
        with Node.prems ltTip have "no \<in> set_of rt" 
          by simp
        with ord_rt * \<open>Dag no low high not\<close> show ?thesis
          by (rule Node.hyps)
      qed
    qed
  next
    case (Node llt l rlt)
    note ltNode=this
    show ?thesis
    proof (cases rt)
      case Tip
      from Node.prems Tip ltNode have ord_lt: "ordered lt var"
        by simp
      from Node.prems have ppo: "p=po"
        by simp
      from Node.prems have ponN: "po \<noteq> Null"
        by auto
      with ppo ponN Tip Node.prems ltNode have *: "Dag (low po) low high lt"
        by auto
      show ?thesis
      proof (cases "no=po")
        case True
        with ppo Node.prems have "not = (Node lt po rt)"
          by (simp del: Dag_Ref add: Dag_unique)
        with Node.prems show ?thesis by simp
      next
        case False
        with Node.prems Tip have "no \<in> set_of lt" 
          by simp
        with ord_lt * \<open>Dag no low high not\<close> show ?thesis
          by (rule Node.hyps)
      qed   
    next
      case (Node lrt r rrt)
      from Node.prems have ppo: "p=po"
        by simp
      from Node.prems Node ltNode have ord_lt: "ordered lt var"
        by simp
      from Node.prems Node ltNode have ord_rt: "ordered rt var"
        by simp
      from Node.prems have ponN: "po \<noteq> Null"
        by auto
      with ppo ponN Node Node.prems ltNode have lt_Dag: "Dag (low po) low high lt"
        by auto
      with ppo ponN Node Node.prems ltNode have rt_Dag: "Dag (high po) low high rt"
        by auto
      show ?thesis
      proof (cases "no = po")
       case True
        with ppo Node.prems have "not = (Node lt po rt)"
          by (simp del: Dag_Ref add: Dag_unique)
        with Node.prems show ?thesis by simp
      next
        assume "no \<noteq> po"
        with Node.prems have no_in_lt_or_rt: "no \<in> set_of lt \<or> no \<in> set_of rt"
          by simp
        show ?thesis 
        proof (cases "no \<in> set_of lt")
          case True
          with ord_lt lt_Dag Node.prems show ?thesis
            apply -
            apply (rule Node.hyps)
            apply assumption+
            done
        next
          assume " no \<notin> set_of lt"
          with no_in_lt_or_rt have no_in_rt: "no \<in> set_of rt"
            by simp
          from Node.hyps have hyp2: 
            "\<And>p no not. \<lbrakk>ordered rt var; Dag p low high rt; Dag no low high not; no \<in> set_of rt\<rbrakk> 
            \<Longrightarrow> ordered not var"
            apply -
            apply assumption
            done
          from no_in_rt ord_rt rt_Dag Node.prems show ?thesis
            apply -
            apply (rule hyp2)
            apply assumption+
            done
        qed
      qed
    qed
  qed
qed

lemma elem_set_of: "\<And> x st. \<lbrakk>x \<in> set_of st; set_of st \<subseteq> set_of t\<rbrakk> \<Longrightarrow> x \<in> set_of t"
by blast


(*procedure Levellist converts a dag with root p in a ref list list (levellist) with nodes of var = i in 
levellist ! i. 
In order to convert the two datastructures a dag traversal is required using a mark on nodes. m indicates
the value which is assumed for a node to be marked. 
(\<exists> nt. Dag n \<^bsup>\<sigma>\<^esup>low \<^bsup>\<sigma>\<^esup>high nt \<and> 
                        {\<^bsup>\<sigma>\<^esup>m} = set_of (dag_map \<^bsup>\<sigma>\<^esup>mark nt))*)

definition wf_ll :: "dag \<Rightarrow> ref list list \<Rightarrow> (ref \<Rightarrow> nat) \<Rightarrow> bool"
where
"wf_ll t levellist var =
  ((\<forall>p. p \<in> set_of t \<longrightarrow> p \<in> set (levellist ! var p)) \<and>
   (\<forall>k < length levellist. \<forall>p \<in> set (levellist ! k). p \<in> set_of t \<and> var p = k))"

definition cong_eval :: "bdt \<Rightarrow> bdt \<Rightarrow> bool" (infix "\<sim>" 60)
  where "cong_eval bdt\<^sub>1 bdt\<^sub>2 = (eval bdt\<^sub>1 = eval bdt\<^sub>2)"

lemma cong_eval_sym: "l \<sim> r = r \<sim> l"
  by (auto simp add: cong_eval_def)

lemma cong_eval_trans: "\<lbrakk> l \<sim> r; r \<sim> t\<rbrakk> \<Longrightarrow> l \<sim> t"
  by (simp add: cong_eval_def)

lemma cong_eval_child_high: " l \<sim> r \<Longrightarrow> r \<sim> (Bdt_Node l v r)"
  apply (simp add: cong_eval_def )
  apply (rule ext)
  apply auto
  done

lemma cong_eval_child_low: " l \<sim> r \<Longrightarrow> l \<sim> (Bdt_Node l v r)"
  apply (simp add: cong_eval_def )
  apply (rule ext)
  apply auto
  done




definition null_comp :: "(ref \<Rightarrow> ref) \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> (ref \<Rightarrow> ref)" (infix "\<propto>" 60)
  where "null_comp a b = (\<lambda> p. (if (b p) = Null then Null else ((a \<circ> b) p)))"

lemma null_comp_not_Null [simp]: "h q \<noteq> Null \<Longrightarrow> (g \<propto> h) q = g (h q)"
  by (simp add: null_comp_def)

lemma id_trans: "(a \<propto> id) (b (c p)) = (a \<propto> b) (c p)"
  by (simp add: null_comp_def)

definition Nodes :: "nat \<Rightarrow> ref list list \<Rightarrow> ref set"
  where "Nodes i levellist = (\<Union>k\<in>{k. k < i} . set (levellist ! k))"


inductive_set Dags :: "ref set \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> dag set"
  for "nodes" "low" "high"
where
  DagsI: "\<lbrakk> set_of t \<subseteq>  nodes; Dag p low high t; t \<noteq> Tip\<rbrakk> 
           \<Longrightarrow> t \<in> Dags nodes low high"

lemma empty_Dags [simp]: "Dags {} low high = {}"
  apply rule
  apply rule
  apply (erule Dags.cases)
  apply (case_tac t)
  apply simp
  apply simp
  apply rule
  done

definition isLeaf_pt :: "ref \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> bool"
  where "isLeaf_pt p low high = (low p = Null \<and> high p = Null)"

definition repNodes_eq :: "ref \<Rightarrow> ref \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> (ref \<Rightarrow> ref) \<Rightarrow> bool"
where
 "repNodes_eq p q low high rep == 
      (rep \<propto> high) p = (rep \<propto> high) q \<and> (rep \<propto> low) p = (rep \<propto> low) q"

definition isomorphic_dags_eq :: "dag \<Rightarrow> dag \<Rightarrow> (ref \<Rightarrow> nat) \<Rightarrow> bool"
where
"isomorphic_dags_eq st\<^sub>1 st\<^sub>2 var =
    (\<forall>bdt\<^sub>1 bdt\<^sub>2. (bdt st\<^sub>1 var = Some bdt\<^sub>1 \<and> bdt st\<^sub>2 var = Some bdt\<^sub>2 \<and> (bdt\<^sub>1 = bdt\<^sub>2))
                 \<longrightarrow> st\<^sub>1 = st\<^sub>2)"

lemma isomorphic_dags_eq_sym: "isomorphic_dags_eq st\<^sub>1 st\<^sub>2 var = isomorphic_dags_eq st\<^sub>2 st\<^sub>1  var"
  by (auto simp add: isomorphic_dags_eq_def)


(*consts subdags_shared :: "dag \<Rightarrow> dag \<Rightarrow> (ref \<Rightarrow> nat) \<Rightarrow> bool"
defs subdags_shared_def : "subdags_shared t1 t2 var == \<forall> st1 st2. (st1 <= t1 \<and> st2 <= t2) \<longrightarrow> shared_prop st1 st2 var"

consts shared :: " dag \<Rightarrow> dag \<Rightarrow> (ref \<Rightarrow> nat) \<Rightarrow> bool"
defs shared_def: "shared t1 t2 var == subdags_shared t1 t1 var \<and> subdags_shared t2 t2 var \<and> subdags_shared t1 t2 var"*)

definition shared :: "dag \<Rightarrow> (ref \<Rightarrow> nat) \<Rightarrow> bool"
  where "shared t var = (\<forall>st\<^sub>1 st\<^sub>2. (st\<^sub>1 <= t \<and> st\<^sub>2 <= t) \<longrightarrow> isomorphic_dags_eq st\<^sub>1 st\<^sub>2 var)"

(* shared returns True if the Dag has no different subdags which represent the same 
bdts. 
Note: The two subdags can have different references and code the same bdt nevertheless!
consts shared :: "dag \<Rightarrow> (ref \<Rightarrow> nat) \<Rightarrow> bool"
defs shared_def: "shared t bdtvar \<equiv> \<forall> st1 st2. (subdag t st1 \<and> subdag t st2 \<and> 
                       (bdt st1 bdtvar = bdt st2 bdtvar \<longrightarrow> st1 = st2))"

consts shared_lower_levels :: "dag \<Rightarrow> nat \<Rightarrow> (ref \<Rightarrow> nat) \<Rightarrow> bool"
defs shared_lower_levels_def : "shared_lower_levels t i bdtvar == \<forall> st1 st2. (st1 < t \<and> st2 < t \<and> bdtvar (root st1) < i \<and> bdtvar (root st2) < i \<and>
                                    (bdt st1 bdtvar = bdt st2 bdtvar \<longrightarrow> st1 = st2))"
*)


fun reduced :: "dag \<Rightarrow> bool" where
  "reduced Tip = True"
| "reduced (Node Tip v Tip) = True"
| "reduced (Node l v r) = (l \<noteq> r \<and> reduced l \<and> reduced r)"  

primrec reduced_bdt :: "bdt \<Rightarrow> bool"
where
  "reduced_bdt Zero = True"
| "reduced_bdt One = True"
| "reduced_bdt (Bdt_Node lbdt v rbdt) =
    (if lbdt = rbdt then False 
     else (reduced_bdt lbdt \<and> reduced_bdt rbdt))"


lemma replicate_elem: "i < n ==>  (replicate n x !i) = x"
apply (induct n)
apply simp
apply (cases i)
apply auto
done

lemma no_in_one_ll: 
 "\<lbrakk>wf_ll pret levellista var; i<length levellista; j < length levellista; 
   no \<in> set (levellista ! i); i\<noteq>j\<rbrakk> 
  \<Longrightarrow> no \<notin> set (levellista ! j) "
apply (unfold wf_ll_def)
apply (erule conjE)
apply (rotate_tac 5)
apply (frule_tac x = i and ?R= "no \<in> set_of pret \<and> var no = i" in allE)
apply (erule impE)
apply simp
apply (rotate_tac 6)
apply (erule_tac x=no in ballE)
apply assumption
apply simp
apply (cases "no \<notin> set (levellista ! j)")
apply assumption
apply (erule_tac x=j in allE)
apply (erule impE)
apply assumption
apply (rotate_tac 7)
apply (erule_tac x=no in ballE)
prefer 2
apply assumption
apply (elim conjE)
apply (thin_tac "\<forall>q. q \<in> set_of pret \<longrightarrow> q \<in> set (levellista ! var q)")
apply fastforce
done

lemma nodes_in_wf_ll: 
"\<lbrakk>wf_ll pret levellista var; i < length levellista;  no \<in> set (levellista ! i)\<rbrakk> 
 \<Longrightarrow> var no = i \<and> no \<in> set_of pret"
apply (simp add: wf_ll_def)
done

lemma subelem_set_of_low: 
"\<And> p. \<lbrakk> x \<in> set_of t; x \<noteq> Null; low x \<noteq> Null; Dag p low high t \<rbrakk> 
 \<Longrightarrow> (low x) \<in> set_of t"
proof (induct t)
  case Tip
  then show ?case by simp
next
  case (Node lt po rt)
  note tNode=this
  then have ppo: "p=po" by simp
  show ?case
  proof (cases "x=p")
    case True
    with Node.prems have lxrootlt: "low x = root lt"
    proof (cases lt)
      case Tip
      with True Node.prems show ?thesis
        by auto
    next
      case (Node llt l rlt)
      with Node.prems True show ?thesis
        by auto
    qed
    with True Node.prems have "low x \<in> set_of (Node lt p rt)"
    proof (cases lt)
      case Tip
      with lxrootlt Node.prems show ?thesis 
        by simp
    next
      case (Node llt l rlt)
      with lxrootlt Node.prems show ?thesis
        by simp
    qed
    with ppo show ?thesis
      by simp
  next
    assume xnp: " x \<noteq> p"  
    with Node.prems have "x \<in> set_of lt \<or> x \<in> set_of rt" 
      by simp
    show ?thesis
    proof (cases "x \<in> set_of lt")
      case True
      note xinlt=this
      from Node.prems have "Dag (low p) low high lt" 
        by fastforce
      with Node.prems True have "low x \<in> set_of lt"
        apply -
        apply (rule Node.hyps)
        apply assumption+
        done
      with Node.prems show ?thesis
        by auto
    next
      assume xnotinlt: " x \<notin> set_of lt"
      with xnp Node.prems have xinrt: "x \<in> set_of rt"
        by simp
      from Node.prems have "Dag (high p) low high rt" 
        by fastforce
      with Node.prems xinrt have "low x \<in> set_of rt"
        apply -
        apply (rule Node.hyps)
        apply assumption+
        done
      with Node.prems show ?thesis
        by auto
    qed
  qed
qed
      
lemma subelem_set_of_high: 
"\<And> p. \<lbrakk> x \<in> set_of t; x \<noteq> Null; high x \<noteq> Null; Dag p low high t \<rbrakk> 
 \<Longrightarrow> (high x) \<in> set_of t"
proof (induct t)
  case Tip
  then show ?case by simp
next
  case (Node lt po rt)
  note tNode=this
  then have ppo: "p=po" by simp
  show ?case
  proof (cases "x=p")
    case True
    with Node.prems have lxrootlt: "high x = root rt"
    proof (cases rt)
      case Tip
      with True Node.prems show ?thesis
        by auto
    next
      case (Node lrt l rrt)
      with Node.prems True show ?thesis
        by auto
    qed
    with True Node.prems have "high x \<in> set_of (Node lt p rt)"
    proof (cases rt)
      case Tip
      with lxrootlt Node.prems show ?thesis 
        by simp
    next
      case (Node lrt l rrt)
      with lxrootlt Node.prems show ?thesis
        by simp
    qed
    with ppo show ?thesis
      by simp
  next
    assume xnp: " x \<noteq> p"  
    with Node.prems have "x \<in> set_of lt \<or> x \<in> set_of rt" 
      by simp
    show ?thesis
    proof (cases "x \<in> set_of lt")
      case True
      note xinlt=this
      from Node.prems have "Dag (low p) low high lt" 
        by fastforce
      with Node.prems True have "high x \<in> set_of lt"
        apply -
        apply (rule Node.hyps)
        apply assumption+
        done
      with Node.prems show ?thesis
        by auto
    next
      assume xnotinlt: " x \<notin> set_of lt"
      with xnp Node.prems have xinrt: "x \<in> set_of rt"
        by simp
      from Node.prems have "Dag (high p) low high rt" 
        by fastforce
      with Node.prems xinrt have "high x \<in> set_of rt"
        apply -
        apply (rule Node.hyps)
        apply assumption+
        done
      with Node.prems show ?thesis
        by auto
    qed
  qed
qed        

lemma set_split: "{k. k<(Suc n)} = {k. k<n} \<union> {n}"
apply auto
done


lemma Nodes_levellist_subset_t: 
"\<lbrakk>wf_ll t levellist var; i<= length levellist\<rbrakk> \<Longrightarrow> Nodes i levellist \<subseteq> set_of t"
proof (induct i)
  case 0
  show ?case by (simp add: Nodes_def)
next
  case (Suc n)
  from Suc.prems Suc.hyps have Nodesn_in_t: "Nodes n levellist \<subseteq> set_of t"
    by simp
  from Suc.prems have "\<forall> x \<in> set (levellist ! n). x \<in> set_of t"
    apply -
    apply (rule ballI)
    apply (simp add: wf_ll_def)
    apply (erule conjE)
    apply (thin_tac " \<forall>q. q \<in> set_of t \<longrightarrow> q \<in> set (levellist ! var q)")
    apply (erule_tac x=n in allE)
    apply (erule impE)
    apply simp
    apply fastforce
    done
  with Suc.prems have "set (levellist ! n) \<subseteq> set_of t"
    apply blast
    done
  with Suc.prems Nodesn_in_t show ?case 
    apply (simp add: Nodes_def)
    apply (simp add: set_split)
    done
qed

lemma bdt_child: 
"\<lbrakk> bdt (Node (Node llt l rlt) p (Node lrt r rrt)) var = Some bdt1\<rbrakk> 
 \<Longrightarrow> \<exists> lbdt rbdt.  bdt (Node llt l rlt) var = Some lbdt \<and> 
                   bdt (Node lrt r rrt) var = Some rbdt"
  by (simp split: option.splits)


lemma subbdt_ex_dag_def: 
"\<And> bdt1 p. \<lbrakk>Dag p low high t; bdt t var = Some bdt1; Dag no low high not; 
no \<in> set_of t\<rbrakk> \<Longrightarrow> \<exists> bdt2.  bdt not var = Some bdt2"
proof (induct t)
  case Tip
  then show ?case by simp
next
  case (Node lt po rt)
  note pNode=this
  with Node.prems have p_po: "p=po" by simp
  show ?case 
  proof (cases "no = po")
    case True
    note no_eq_po=this
    from p_po Node.prems no_eq_po have "not = (Node lt po rt)" by (simp add: Dag_unique del: Dag_Ref)
    with Node.prems have "bdt not var = Some bdt1" by (simp add: le_dag_def)
    then show ?thesis by simp
  next
    assume "no \<noteq> po"
    with Node.prems have no_in_lt_or_rt: "no \<in> set_of lt \<or> no \<in> set_of rt" by simp
    show ?thesis
    proof (cases "no \<in> set_of lt")
      case True
      note no_in_lt=this
      from Node.prems p_po have lt_dag: "Dag (low po) low high lt" by simp
      from Node.prems have lbdt_def: "\<exists> lbdt. bdt lt var = Some lbdt"
      proof (cases lt)
        case Tip
        with Node.prems no_in_lt show ?thesis by (simp add: le_dag_def)
      next
        case (Node llt l rlt)
        note lNode=this
        show ?thesis
        proof (cases rt)
          case Tip
          note rNode=this
          with lNode Node.prems show ?thesis by simp
        next 
          case (Node lrt r rrt)
          note rNode=this
          with lNode Node.prems show ?thesis by (simp split: option.splits)
        qed
      qed
      then obtain lbdt where "bdt lt var = Some lbdt"..
      with Node.prems lt_dag no_in_lt show ?thesis
        apply -
        apply (rule Node.hyps)
        apply assumption+
        done
    next
      assume "no \<notin> set_of lt"
      with no_in_lt_or_rt have no_in_rt: "no \<in> set_of rt" by simp
      from Node.prems p_po have rt_dag: "Dag (high po) low high rt" by simp
      from Node.hyps have hyp2: "\<And> rbdt. \<lbrakk>Dag (high po) low high rt; bdt rt var = Some rbdt; Dag no low high not; no \<in> set_of rt\<rbrakk> \<Longrightarrow> \<exists>bdt2. bdt not var = Some bdt2"
        by simp
      from Node.prems have lbdt_def: "\<exists> rbdt. bdt rt var = Some rbdt"
      proof (cases rt)
        case Tip
        with Node.prems no_in_rt show ?thesis by (simp add: le_dag_def)
      next
        case (Node lrt l rrt)
        note rNode=this
        show ?thesis
        proof (cases lt)
          case Tip
          note lTip=this
          with rNode Node.prems show ?thesis by simp
        next 
          case (Node llt r rlt)
          note lNode=this
          with rNode Node.prems show ?thesis by (simp split: option.splits)
        qed
      qed
      then obtain rbdt where "bdt rt var = Some rbdt"..
      with Node.prems rt_dag no_in_rt show ?thesis
        apply -
        apply (rule hyp2)
        apply assumption+
        done
    qed
  qed
qed
      
lemma subbdt_ex: 
"\<And> bdt1. \<lbrakk> (Node lst stp rst) <= t; bdt t var = Some bdt1\<rbrakk> 
 \<Longrightarrow> \<exists> bdt2.  bdt (Node lst stp rst) var = Some bdt2"
proof (induct t)
  case Tip
  then show ?case by (simp add: le_dag_def)
next 
  case (Node lt p rt)
  note pNode=this
  show ?case
  proof (cases "Node lst stp rst = Node lt p rt")
    case True
    with Node.prems show ?thesis by simp
  next
    assume " Node lst stp rst \<noteq> Node lt p rt"
    with Node.prems have "Node lst stp rst < Node lt p rt" apply (simp add: le_dag_def) apply auto done
    then have in_ltrt: "Node lst stp rst <= lt \<or> Node lst stp rst <= rt" 
      by (simp add: less_dag_Node)
    show ?thesis
    proof (cases "Node lst stp rst <= lt")
      case True 
      note in_lt=this
      from Node.prems have lbdt_def: "\<exists> lbdt. bdt lt var = Some lbdt"
      proof (cases lt)
        case Tip
        with Node.prems in_lt show ?thesis by (simp add: le_dag_def)
      next
        case (Node llt l rlt)
        note lNode=this
        show ?thesis
        proof (cases rt)
          case Tip
          note rNode=this
          with lNode Node.prems show ?thesis by simp
        next 
          case (Node lrt r rrt)
          note rNode=this
          with lNode Node.prems show ?thesis by (simp split: option.splits)
        qed
      qed
      then obtain lbdt where "bdt lt var = Some lbdt"..
      with Node.prems in_lt show ?thesis
        apply -
        apply (rule Node.hyps)
        apply assumption+
        done
    next
      assume " \<not> Node lst stp rst \<le> lt"
      with in_ltrt have in_rt: "Node lst stp rst <= rt" by simp
      from Node.hyps have hyp2: "\<And> rbdt. \<lbrakk>Node lst stp rst <= rt; bdt rt var = Some rbdt\<rbrakk> \<Longrightarrow> \<exists>bdt2. bdt (Node lst stp rst) var = Some bdt2"
        by simp
      from Node.prems have rbdt_def: "\<exists> rbdt. bdt rt var = Some rbdt"
      proof (cases rt)
        case Tip
        with Node.prems in_rt show ?thesis by (simp add: le_dag_def)
      next
        case (Node lrt l rrt)
        note rNode=this
        show ?thesis
        proof (cases lt)
          case Tip
          note lNode=this
          with rNode Node.prems show ?thesis by simp
        next 
          case (Node lrt r rrt)
          note lNode=this
          with rNode Node.prems show ?thesis by (simp split: option.splits)
        qed
      qed
      then obtain rbdt where "bdt rt var = Some rbdt"..
      with Node.prems in_rt show ?thesis
        apply -
        apply (rule hyp2)
        apply assumption+
        done
    qed
  qed
qed


lemma var_ordered_children: 
"\<And> p. \<lbrakk> Dag p low high t; ordered t var; no \<in> set_of t; 
        low no \<noteq> Null; high no \<noteq> Null\<rbrakk> 
       \<Longrightarrow> var (low no) < var no \<and> var (high no) < var no"
proof (induct t)
  case Tip
  then show ?case by simp
next
  case (Node lt po rt)
  then have ppo: "p=po" by simp
  show ?case
  proof (cases "no = po")
    case True
    note no_po=this
    from Node.prems have "var (low po) < var po \<and> var (high po) < var po" 
    proof (cases lt)
      case Tip
      note ltTip=this
      with Node.prems no_po ppo show ?thesis by simp
    next
      case (Node llt l rlt)
      note lNode=this
      show ?thesis
      proof (cases rt)
        case Tip
        note rTip=this
        with Node.prems no_po ppo show ?thesis by simp
      next
        case (Node lrt r rrt)
        note rNode=this
        with Node.prems ppo no_po lNode  show ?thesis by (simp del: Dag_Ref) 
      qed
    qed
    with no_po show ?thesis by simp
  next
    assume " no \<noteq> po"
    with Node.prems have no_in_ltrt: "no \<in> set_of lt \<or> no \<in> set_of rt"
      by simp
    show ?thesis
    proof (cases "no \<in> set_of lt")
      case True
      note no_in_lt=this
      from Node.prems ppo have lt_dag: "Dag (low po) low high lt" 
        by simp
      from Node.prems have ord_lt: "ordered lt var"
        apply -
        apply (drule children_ordered)
        apply simp
        done
      from no_in_lt lt_dag ord_lt Node.prems show ?thesis
        apply -
        apply (rule Node.hyps)
        apply assumption+
        done
    next
      assume " no \<notin> set_of lt"
      with no_in_ltrt have no_in_rt: "no \<in> set_of rt" by simp
      from Node.prems ppo have rt_dag: "Dag (high po) low high rt" by simp
      from Node.hyps have hyp2: " \<lbrakk>Dag (high po) low high rt; ordered rt var; no \<in> set_of rt; low no \<noteq> Null; high no \<noteq> Null\<rbrakk>
                                  \<Longrightarrow> var (low no) < var no \<and> var (high no) < var no"
        by simp
      from Node.prems have ord_rt: "ordered rt var"
        apply -
        apply (drule children_ordered)
        apply simp
        done
      from rt_dag ord_rt no_in_rt Node.prems show ?thesis
        apply -
        apply (rule hyp2)
        apply assumption+
        done
    qed
  qed
qed

lemma nort_null_comp:
assumes pret_dag: "Dag p low high pret" and
        prebdt_pret: "bdt pret var = Some prebdt" and
        nort_dag: "Dag (repc no) (repb \<propto> low) (repb \<propto> high) nort" and
        ord_pret: "ordered pret var" and
        wf_llb: "wf_ll pret levellistb var" and
        nbsll: "nb < length levellistb" and
        repbc_nc: "\<forall> nt. nt \<notin> set (levellistb ! nb) \<longrightarrow> repb nt = repc nt" and
        xsnb_in_pret: "\<forall> x \<in> set_of nort. var x < nb \<and> x \<in> set_of pret"
shows "\<forall> x \<in> set_of nort. ((repc \<propto> low) x = (repb \<propto> low) x \<and> 
                           (repc \<propto> high) x = (repb \<propto> high) x)" 
proof (rule ballI)
  fix x
  assume x_in_nort: "x \<in> set_of nort"
  with nort_dag have xnN: "x \<noteq> Null"
    apply -
    apply (rule set_of_nn [rule_format])
    apply auto
    done
  from x_in_nort xsnb_in_pret have xsnb: "var x <nb"
    by simp
  from x_in_nort xsnb_in_pret have x_in_pret: "x \<in> set_of pret"
    by blast
  show " (repc \<propto> low) x = (repb \<propto> low) x \<and> (repc \<propto> high) x = (repb \<propto> high) x"
  proof (cases "(low x) \<noteq> Null")
    case True
    with pret_dag prebdt_pret x_in_pret have highnN: "(high x) \<noteq> Null"
      apply -
      apply (drule balanced_bdt)
      apply assumption+
      apply simp
      done
    from x_in_pret ord_pret highnN True have children_var_smaller: "var (low x) < var x \<and> var (high x) < var x"
      apply -
      apply (rule var_ordered_children)
      apply (rule pret_dag)
      apply (rule ord_pret)
      apply (rule x_in_pret)
      apply (rule True)
      apply (rule highnN)
      done
    with xsnb have lowxsnb: "var (low x) < nb"
      by arith
    from children_var_smaller xsnb have highxsnb: "var (high x) < nb"
      by arith
    from x_in_pret xnN True pret_dag have lowxinpret: "(low x) \<in> set_of pret"
      apply -
      apply (drule subelem_set_of_low)
      apply assumption
      apply (thin_tac "x \<noteq> Null")
      apply assumption+
      done
    with wf_llb have "low x \<in> set (levellistb ! (var (low x)))" 
      by (simp add: wf_ll_def)
    with wf_llb nbsll lowxsnb have "low x \<notin> set (levellistb ! nb)"
      apply -
      apply (rule_tac ?i="(var (low x))" and ?j=nb in no_in_one_ll)
      apply auto
      done
    with repbc_nc have repclow: "repc (low x) = repb (low x)"
      by auto
    from x_in_pret xnN highnN pret_dag have highxinpret: "(high x) \<in> set_of pret"
      apply -
      apply (drule subelem_set_of_high)
      apply assumption
      apply (thin_tac "x \<noteq> Null")
      apply assumption+
      done
    with wf_llb have "high x \<in> set (levellistb ! (var (high x)))" 
      by (simp add: wf_ll_def)
    with wf_llb nbsll highxsnb have "high x \<notin> set (levellistb ! nb)"
      apply -
      apply (rule_tac ?i="(var (high x))" and ?j=nb in no_in_one_ll)
      apply auto
      done
    with repbc_nc have repchigh: "repc (high x) = repb (high x)"
      by auto
    with repclow show ?thesis 
      by (simp add: null_comp_def)
  next
    assume " \<not> low x \<noteq> Null"
    then have lowxNull: "low x = Null" by simp
    with pret_dag x_in_pret prebdt_pret have highxNull: "high x =Null" 
      apply -
      apply (drule balanced_bdt)
      apply simp
      apply simp
      apply simp
      done
    from lowxNull have repclowNull: "(repc \<propto> low) x = Null"
      by (simp add: null_comp_def)
    from lowxNull have repblowNull: "(repb \<propto> low) x = Null"
      by (simp add: null_comp_def)
    with repclowNull have lowxrepbc: "(repc \<propto> low) x = (repb \<propto> low) x"
      by simp
    from highxNull have repchighNull: "(repc \<propto> high) x = Null"
      by (simp add: null_comp_def)
    from highxNull have "(repb \<propto> high) x = Null"
      by (simp add: null_comp_def)
    with repchighNull have highxrepbc: "(repc \<propto> high) x = (repb \<propto> high) x"
      by simp
    with lowxrepbc show ?thesis
      by simp
  qed
qed         

lemma wf_ll_Nodes_pret: 
"\<lbrakk>wf_ll pret levellista var; nb < length levellista; x \<in> Nodes nb levellista\<rbrakk> 
 \<Longrightarrow> x \<in> set_of pret \<and> var x < nb"
  apply (simp add: wf_ll_def Nodes_def)
  apply (erule conjE)
  apply (thin_tac " \<forall>q. q \<in> set_of pret \<longrightarrow> q \<in> set (levellista ! var q)")
  apply (erule exE)
  apply (elim conjE)
  apply (erule_tac x=xa in allE)
  apply (erule impE)
  apply arith
  apply (erule_tac x=x in ballE)
  apply auto
  done

lemma bdt_Some_var1_One: 
"\<And> x. \<lbrakk> bdt t var = Some x; var (root t) = 1\<rbrakk> 
 \<Longrightarrow> x = One \<and> t = (Node Tip (root t) Tip)"
proof (induct t)
  case Tip
  then show  ?case by simp
next
  case (Node lt p rt)
  note tNode = this
  show ?case 
  proof (cases lt)
    case Tip
    note ltTip=this
    show ?thesis
    proof (cases rt)
      case Tip
      note rtTip = this
      with ltTip Node.prems show ?thesis by auto
    next
      case (Node lrt r rrt)
      note rtNode=this
      with Node.prems ltTip show ?thesis by auto
    qed
  next
    case (Node llt l rlt)
    note ltNode=this
    show ?thesis
    proof (cases rt)
      case Tip
      with ltNode Node.prems show ?thesis by auto
    next
      case (Node lrt r rrt)
      note rtNode=this
      with ltNode Node.prems show ?thesis by auto
    qed
  qed
qed

lemma bdt_Some_var0_Zero: 
"\<And> x. \<lbrakk> bdt t var = Some x; var (root t) = 0\<rbrakk> 
\<Longrightarrow> x = Zero \<and> t = (Node Tip (root t) Tip)"
proof (induct t)
  case Tip
  then show  ?case by simp
next
  case (Node lt p rt)
  note tNode = this
  show ?case 
  proof (cases lt)
    case Tip
    note ltTip=this
    show ?thesis
    proof (cases rt)
      case Tip
      note rtTip = this
      with ltTip Node.prems show ?thesis by auto
    next
      case (Node lrt r rrt)
      note rtNode=this
      with Node.prems ltTip show ?thesis by auto
    qed
  next
    case (Node llt l rlt)
    note ltNode=this
    show ?thesis
    proof (cases rt)
      case Tip
      with ltNode Node.prems show ?thesis by auto
    next
      case (Node lrt r rrt)
      note rtNode=this
      with ltNode Node.prems show ?thesis by auto
    qed
  qed
qed

lemma reduced_children_parent: 
"\<lbrakk> reduced l; l= (Node llt lp rlt); reduced r; r=(Node lrt rp rrt); 
  lp \<noteq> rp \<rbrakk> 
 \<Longrightarrow> reduced (Node l p r)"
  by simp

(*Die allgemeine Form mit i <=j \<Longrightarrow> Nodes i levellista \<subseteq> Nodes j levellista wäre schöner, aber wie beweist man das? *)
lemma Nodes_subset: "Nodes i levellista \<subseteq> Nodes (Suc i) levellista"
  apply (simp add: Nodes_def)
  apply (simp add: set_split)
  done

lemma Nodes_levellist: 
"\<lbrakk> wf_ll pret levellista var; nb < length levellista; p \<in> Nodes nb levellista\<rbrakk> 
 \<Longrightarrow> p \<notin> set (levellista ! nb)"
  apply (simp add: Nodes_def) 
  apply (erule exE)
  apply (rule_tac i=x and j=nb in no_in_one_ll)
  apply auto
  done

lemma Nodes_var_pret: 
 "\<lbrakk>wf_ll pret levellista var; nb < length levellista; p \<in> Nodes nb levellista\<rbrakk> 
  \<Longrightarrow> var p < nb \<and> p \<in> set_of pret"
  apply (simp add: Nodes_def wf_ll_def)
  apply (erule conjE)
  apply (thin_tac "\<forall>q. q \<in> set_of pret \<longrightarrow> q \<in> set (levellista ! var q)")
  apply (erule exE)
  apply (erule_tac x=x in allE)
  apply (erule impE)
  apply arith
  apply (erule_tac x=p in ballE)
  apply arith
  apply simp
  done

lemma Dags_root_in_Nodes:
assumes t_in_DagsSucnb: "t \<in> Dags (Nodes (Suc nb) levellista) low high" 
shows "\<exists> p . Dag p low high t  \<and> p \<in> Nodes (Suc nb) levellista"
proof -
  from t_in_DagsSucnb obtain p where t_dag: "Dag p low high t" and t_subset_Nodes: "set_of t \<subseteq> Nodes (Suc nb) levellista" and t_nTip: "t\<noteq> Tip"
    by (fastforce elim: Dags.cases)
  from t_dag t_nTip have "p\<noteq>Null" by (cases t) auto
  with t_subset_Nodes t_dag have "p \<in> Nodes (Suc nb) levellista" 
    by (cases t) auto
  with t_dag show ?thesis
    by auto
qed

  


lemma subdag_dag: 
"\<And> p. \<lbrakk>Dag p low high t; st <= t\<rbrakk> \<Longrightarrow> \<exists> stp. Dag stp low high st"
proof (induct t)
  case Tip
  then show ?case
    by (simp add: less_dag_def le_dag_def)
next
  case (Node lt po rt)
  note t_Node=this
  with Node.prems have p_po: "p=po"
    by simp
  show ?case
  proof (cases "st = Node lt po rt")
    case True
    note st_t=this
    with Node.prems show ?thesis
      by auto
  next
    assume st_nt: "st \<noteq> Node lt po rt"
    with Node.prems p_po have st_subdag_lt_rt: "st<=lt \<or> st <=rt"
      by (auto simp add:le_dag_def less_dag_def)
    from Node.prems p_po obtain lp rp where lt_dag: "Dag lp low high lt" and rt_dag: "Dag rp low high rt"
      by auto
    show ?thesis
    proof (cases "st<=lt")
      case True
      note st_lt=this
      with lt_dag show ?thesis
        apply-
        apply (rule Node.hyps)
        apply auto
        done
    next
      assume "\<not> st \<le> lt"
      with st_subdag_lt_rt have st_rt: "st <= rt"
        by simp
      from Node.hyps have rhyp: "\<lbrakk>Dag rp low high rt; st \<le> rt\<rbrakk> \<Longrightarrow> \<exists>stp. Dag stp low high st"
        by simp
      from st_rt rt_dag show ?thesis
        apply -
        apply (rule rhyp)
        apply auto
        done
    qed
  qed
qed

lemma Dags_subdags: 
assumes t_in_Dags: "t \<in> Dags nodes low high" and
  st_t: "st <= t" and 
  st_nTip: "st \<noteq> Tip"
shows "st \<in> Dags nodes low high"
proof -
  from t_in_Dags obtain p where t_dag: "Dag p low high t" and t_subset_Nodes: "set_of t \<subseteq> nodes" and t_nTip: "t\<noteq> Tip"
    by (fastforce elim: Dags.cases)
  from st_t have "set_of st \<subseteq> set_of t"
    by (simp add: le_dag_set_of)
  with t_subset_Nodes have st_subset_fnctNodes: "set_of st \<subseteq> nodes"
    by blast
  from st_t t_dag obtain stp where "Dag stp low high st"
    apply -
    apply (drule subdag_dag)
    apply auto
    done
  with st_subset_fnctNodes st_nTip show ?thesis
    apply -
    apply (rule DagsI)
    apply auto
    done
qed


lemma Dags_Nodes_cases: 
assumes P_sym: "\<And> t1 t2. P t1 t2 var = P t2 t1 var" and
  dags_in_lower_levels: 
  "\<And> t1 t2. \<lbrakk>t1 \<in> Dags (fnct `(Nodes n levellista)) low high; 
              t2  \<in> Dags (fnct `(Nodes n levellista)) low high\<rbrakk> 
             \<Longrightarrow> P t1 t2 var" and
  dags_in_mixed_levels: 
  "\<And> t1 t2. \<lbrakk>t1 \<in> Dags (fnct `(Nodes n levellista)) low high; 
              t2  \<in> Dags (fnct `(Nodes (Suc n) levellista)) low high; 
              t2 \<notin>  Dags (fnct `(Nodes n levellista)) low high\<rbrakk> 
             \<Longrightarrow> P t1 t2 var" and
  dags_in_high_level: 
   "\<And> t1 t2. \<lbrakk>t1 \<in> Dags (fnct `(Nodes (Suc n) levellista)) low high; 
               t1 \<notin>  Dags (fnct `(Nodes n levellista)) low high; 
               t2 \<in> Dags (fnct `(Nodes (Suc n) levellista)) low high; 
               t2 \<notin>  Dags (fnct `(Nodes n levellista)) low high\<rbrakk> 
              \<Longrightarrow> P t1 t2 var"
shows "\<forall> t1 t2.  t1 \<in> Dags (fnct `(Nodes (Suc n) levellista)) low high \<and> 
                 t2 \<in> Dags (fnct `(Nodes (Suc n) levellista)) low high 
                 \<longrightarrow> P t1 t2 var"
proof (intro allI impI , elim conjE)
  fix t1 t2
  assume t1_in_higher_levels: "t1 \<in> Dags (fnct ` Nodes (Suc n) levellista) low high"
  assume t2_in_higher_levels: "t2 \<in> Dags (fnct ` Nodes (Suc n) levellista) low high"
  show  "P t1 t2 var"
  proof (cases "t1 \<in> Dags (fnct ` Nodes n levellista) low high")
    case True 
    note t1_in_ll = this
    show ?thesis
    proof (cases "t2 \<in> Dags (fnct ` Nodes n levellista) low high")
      case True
      note t2_in_ll=this
      with t1_in_ll dags_in_lower_levels show ?thesis
        by simp
    next
      assume t2_notin_ll: "t2 \<notin> Dags (fnct ` Nodes n levellista) low high"
      with t1_in_ll t2_in_higher_levels dags_in_mixed_levels show ?thesis
        by simp
    qed
  next
    assume t1_notin_ll: "t1 \<notin> Dags (fnct ` Nodes n levellista) low high"
    show ?thesis
    proof (cases "t2 \<in> Dags (fnct ` Nodes n levellista) low high")
      case True
      note t2_in_ll=this
      with dags_in_mixed_levels t1_in_higher_levels t1_notin_ll P_sym show ?thesis
        by auto
    next
      assume t2_notin_ll: "t2 \<notin> Dags (fnct ` Nodes n levellista) low high"
      with t1_notin_ll t1_in_higher_levels t2_in_higher_levels dags_in_high_level show ?thesis
        by simp
    qed
  qed
qed

lemma Null_notin_Nodes: "\<lbrakk>Dag p low high t; nb <= length levellista; wf_ll t levellista var\<rbrakk> \<Longrightarrow> Null \<notin> Nodes nb levellista" 
  apply (simp add: Nodes_def wf_ll_def del: Dag_Ref)
  apply (rule allI)
  apply (rule impI)
  apply (elim conjE)
  apply (thin_tac "\<forall>q. P q" for P)
  apply (erule_tac x=x in allE)
  apply (erule impE)
  apply simp
  apply (erule_tac x=Null in ballE)
  apply (erule conjE)
  apply (drule set_of_nn [rule_format])
  apply auto
  done


lemma Nodes_in_pret: "\<lbrakk>wf_ll t levellista var; nb <= length levellista\<rbrakk> \<Longrightarrow> Nodes nb levellista \<subseteq> set_of t"
    apply -
    apply rule
    apply (simp add: wf_ll_def Nodes_def)
    apply (erule exE)
    apply (elim conjE)
    apply (thin_tac "\<forall>q. q \<in> set_of t \<longrightarrow> q \<in> set (levellista ! var q)")
    apply (erule_tac x=xa in allE)
    apply (erule impE)
    apply simp
    apply (erule_tac x=x in ballE)
    apply auto
    done



lemma restrict_root_Node: 
  "\<lbrakk>t \<in> Dags (repc `Nodes (Suc nb) levellista) (repc \<propto> low) (repc \<propto> high); t \<notin>  Dags (repc `Nodes nb levellista) (repc \<propto> low) (repc \<propto> high); 
  ordered t var; \<forall> no \<in> Nodes (Suc nb) levellista. var (repc no) <= var no \<and> repc (repc no) = repc no; wf_ll pret levellista var; nb < length levellista;repc `Nodes (Suc nb) levellista \<subseteq> Nodes (Suc nb) levellista\<rbrakk>
  \<Longrightarrow> \<exists> q. Dag (repc q) (repc \<propto> low) (repc \<propto> high) t \<and> q \<in> set (levellista ! nb)"
proof (elim Dags.cases)
  fix p and ta :: "dag"
  assume t_notin_DagsNodesnb: "t \<notin> Dags (repc ` Nodes nb levellista) (repc \<propto> low) (repc \<propto> high)"
  assume t_ta: "t = ta"
  assume ta_in_repc_NodesSucnb: "set_of ta \<subseteq> repc ` Nodes (Suc nb) levellista"
  assume ta_dag: "Dag p (repc \<propto> low) (repc \<propto> high) ta"
  assume ta_nTip: "ta \<noteq> Tip"
  assume ord_t: "ordered t var"
  assume varrep_prop: "\<forall> no \<in> Nodes (Suc nb) levellista. var (repc no) <= var no \<and> repc (repc no) = repc no"
  assume wf_lla: "wf_ll pret levellista var"
  assume nbslla: "nb < length levellista"
  assume repcNodes_in_Nodes: "repc `Nodes (Suc nb) levellista \<subseteq> Nodes (Suc nb) levellista"
  from ta_nTip ta_dag have p_nNull: "p\<noteq> Null"
    by auto
  with ta_nTip ta_dag obtain lt rt where ta_Node: " ta = Node lt p rt"
    by auto
  with ta_nTip ta_dag have p_in_ta: "p \<in> set_of ta"
    by auto
  with ta_in_repc_NodesSucnb have p_in_repcNodes_Sucnb: "p \<in> repc `Nodes (Suc nb) levellista"
    by auto
  show ?thesis
    proof (cases "p \<in> repc `(set (levellista ! nb))")
      case True
      then obtain q where 
        p_repca: "p=repc q" and
        a_in_llanb: "q \<in> set (levellista ! nb)"
        by auto
      with ta_dag t_ta show ?thesis
        apply -
        apply (rule_tac x=q in exI)
        apply simp
        done
    next
      assume p_notin_repc_llanb: "p \<notin> repc ` set (levellista ! nb)"
      with p_in_repcNodes_Sucnb have p_in_repc_Nodesnb: "p \<in> repc `Nodes nb levellista"
        apply -
        apply (erule imageE)
        apply rule
        apply (simp add: Nodes_def)
        apply (simp add: Nodes_def)
        apply (erule exE conjE)
        apply (case_tac "xa=nb")
        apply simp
        apply (rule_tac x=xa in exI)
        apply auto
        done
      have "t \<in> Dags (repc `Nodes nb levellista) (repc \<propto> low) (repc \<propto> high)"
      proof -
        have "set_of t \<subseteq> repc `Nodes nb levellista"
        proof (rule)
          fix x :: ref
          assume x_in_t: "x \<in> set_of t"
          with ord_t have "var x <= var (root t)"
            apply -
            apply (rule ordered_set_of)
            apply auto
            done
          with t_ta ta_Node have varx_varp: "var x <= var p"
            by auto
          from p_in_repc_Nodesnb obtain k where ksnb: "k < nb" and p_in_repc_llak:  "p \<in> repc `(set (levellista ! k))"
            by (auto simp add: Nodes_def ImageE)
          then obtain q where p_repcq: "p=repc q" and q_in_llak: "q \<in> set (levellista ! k)"
            by auto
          from q_in_llak wf_lla nbslla ksnb have varqk: "var q = k"
            by (simp add: wf_ll_def)
          have Nodesnb_in_NodesSucnb: "Nodes nb levellista \<subseteq> Nodes (Suc nb) levellista"
            by (rule Nodes_subset)
          from q_in_llak ksnb have "q \<in> Nodes nb levellista"
            by (auto simp add: Nodes_def)
          with varrep_prop Nodesnb_in_NodesSucnb have "var (repc q) <= var q"
            by auto
          with varqk ksnb p_repcq have "var p < nb"
            by auto
          with varx_varp have varx_snb: "var x < nb"
            by auto
          from x_in_t t_ta ta_in_repc_NodesSucnb obtain a where 
            x_repca: "x= repc a" and
            a_in_NodesSucnb: "a \<in> Nodes (Suc nb) levellista"
            by auto
          with varrep_prop have rx_x: "repc x = x" 
            by auto
          have "x \<in> set_of pret"
          proof -
            from wf_lla nbslla have "Nodes (Suc nb) levellista \<subseteq> set_of pret"
              apply -
              apply (rule Nodes_in_pret)
              apply auto
              done
            with x_in_t t_ta ta_in_repc_NodesSucnb repcNodes_in_Nodes show ?thesis
              by auto 
          qed 
          with wf_lla have "x \<in> set (levellista ! (var x))" 
            by (auto simp add: wf_ll_def) 
          with varx_snb have "x \<in> Nodes nb levellista" 
            by (auto simp add: Nodes_def) 
          with rx_x show "x \<in> repc `Nodes nb levellista"
            apply -
            apply rule
            apply (subgoal_tac "x=repc x")
            apply auto
            done
        qed 
        with ta_nTip ta_dag t_ta show ?thesis
          apply -
          apply (rule DagsI)
          apply auto
          done
      qed
      with t_notin_DagsNodesnb show ?thesis
        by auto
    qed
  qed
          




lemma same_bdt_var: "\<lbrakk>bdt (Node lt1 p1 rt1) var = Some bdt1; bdt (Node lt2 p2 rt2) var = Some bdt1\<rbrakk>
  \<Longrightarrow> var p1 = var p2"
proof (induct bdt1)
  case Zero
  then obtain var_p1: "var p1 = 0" and var_p2: "var p2 = 0"
    by simp
  then show ?case
    by simp
next
  case One
  then obtain var_p1: "var p1 = 1" and var_p2: "var p2 = 1"
    by simp
  then show ?case
    by simp
next
  case (Bdt_Node lbdt v rbdt)
  then obtain var_p1: "var p1 = v" and var_p2: "var p2 = v"
    by simp
  then show ?case by simp
qed

lemma bdt_Some_Leaf_var_le_1: 
"\<lbrakk>Dag p low high t; bdt t var = Some x; isLeaf_pt p low high\<rbrakk> 
  \<Longrightarrow> var p <= 1"
proof (induct t)
  case Tip
  thus ?case by simp
next
  case (Node lt p rt)
  note tNode=this
  from Node.prems tNode show ?case
    apply (simp add: isLeaf_pt_def)
    apply (case_tac "var p = 0")
    apply simp
    apply (case_tac "var p = Suc 0")
    apply simp
    apply simp
    done
qed

lemma subnode_dag_cons: 
"\<And> p. \<lbrakk>Dag p low high t; no \<in> set_of t\<rbrakk> \<Longrightarrow> \<exists> not. Dag no low high not"
proof (induct t)
  case Tip
  thus ?case by simp
next
  case (Node lt q rt)
  with Node.prems have q_p: "p = q"
    by simp
  from Node.prems have lt_dag: "Dag (low p) low high lt"
    by auto
  from Node.prems have rt_dag: "Dag (high p) low high rt"
    by auto
  show ?case
  proof (cases "no \<in> set_of lt")
    case True
    with Node.hyps lt_dag show ?thesis
      by simp
  next
    assume no_notin_lt: "no \<notin> set_of lt"
    show ?thesis
    proof (cases "no=p")
      case True
      with Node.prems q_p show ?thesis
        by auto
    next
      assume no_neq_p: "no \<noteq> p"
      with Node.prems no_notin_lt have no_in_rt: "no \<in> set_of rt"
        by simp
      with rt_dag Node.hyps show ?thesis
        by auto
    qed
  qed
qed






(*theorems for the proof of share_reduce_rep_list*)




lemma nodes_in_taken_in_takeSucn: "no \<in> set (take n nodeslist) \<Longrightarrow> no \<in> set (take (Suc n) nodeslist) "
proof -
  assume no_in_taken: "no \<in> set (take n nodeslist)"
  have "set (take n nodeslist) \<subseteq> set (take (Suc n) nodeslist)"
    apply -
    apply (rule set_take_subset_set_take)
    apply simp
    done
  with no_in_taken show ?thesis
    by blast
qed


lemma ind_in_higher_take: "\<And>n k. \<lbrakk>n < k;  n < length xs\<rbrakk> 
  \<Longrightarrow> xs ! n \<in> set (take k xs)"
apply (induct xs)
apply simp
apply simp
apply (case_tac n)
apply simp
apply (case_tac k)
apply simp
apply simp
apply simp
apply (case_tac k)
apply simp
apply simp
done

lemma take_length_set: "\<And>n. n=length xs \<Longrightarrow> set (take n xs) = set xs"
apply (induct xs)
apply (auto simp add: take_Cons split: nat.splits)
done


lemma repNodes_eq_ext_rep: "\<lbrakk>low no \<noteq> nodeslist! n; high no \<noteq> nodeslist ! n; 
  low sn \<noteq> nodeslist ! n; high sn \<noteq> nodeslist ! n\<rbrakk>
  \<Longrightarrow> repNodes_eq sn no low high repa = repNodes_eq sn no low high (repa(nodeslist ! n := repa (low (nodeslist ! n))))"
  by (simp add: repNodes_eq_def null_comp_def)


lemma filter_not_empty: "\<lbrakk>x \<in> set xs; P x\<rbrakk> \<Longrightarrow> filter P xs \<noteq> []"
  by (induct xs) auto

lemma "x \<in> set (filter P xs) \<Longrightarrow> P x"
  by auto

lemma hd_filter_in_list: "filter P xs \<noteq> [] \<Longrightarrow> hd (filter P xs) \<in> set xs"
  by (induct xs) auto

lemma hd_filter_in_filter: "filter P xs \<noteq> [] \<Longrightarrow> hd (filter P xs) \<in> set (filter P xs)"
  by (induct xs) auto

lemma hd_filter_prop: 
  assumes non_empty: "filter P xs \<noteq> []" 
  shows "P (hd (filter P xs))"
proof -
  from non_empty have "hd (filter P xs) \<in> set (filter P xs)"
    by (rule hd_filter_in_filter)
  thus ?thesis
    by auto
qed

lemma index_elem: "x \<in> set xs \<Longrightarrow> \<exists>i<length xs. x = xs ! i"
  apply (induct xs) 
  apply simp
  apply (case_tac "x=a")
  apply  auto
  done

lemma filter_hd_P_rep_indep:     
"\<lbrakk>\<forall>x. P x x; \<forall>a b. P x a \<longrightarrow> P a b \<longrightarrow> P x b; filter (P x) xs \<noteq> []\<rbrakk>  \<Longrightarrow> 
  hd (filter (P (hd (filter (P x) xs))) xs) =  hd (filter (P x) xs)"
apply (induct xs)
apply simp
apply (case_tac "P x a")
using [[simp_depth_limit=2]]
apply  (simp)
apply clarsimp
apply (fastforce dest: hd_filter_prop)
done

lemma take_Suc_not_last:
"\<And>n. \<lbrakk>x \<in> set (take (Suc n) xs); x\<noteq>xs!n; n < length xs\<rbrakk> \<Longrightarrow> x \<in> set (take n xs)"     
apply (induct xs)
apply  simp
apply (case_tac n)
apply  simp
using [[simp_depth_limit=2]]
apply fastforce
done

lemma P_eq_list_filter: "\<forall>x \<in> set xs. P x = Q x \<Longrightarrow> filter P xs = filter Q xs"
  apply (induct xs)
  apply auto
  done

lemma hd_filter_take_more: "\<And>n m.\<lbrakk>filter P (take n xs) \<noteq> []; n \<le> m\<rbrakk> \<Longrightarrow> 
       hd (filter P (take n xs)) =  hd (filter P (take m xs))"
apply (induct xs)
apply  simp
apply (case_tac n)
apply  simp
apply (case_tac m)
apply  simp
apply clarsimp
done

(*
consts wf_levellist :: "dag \<Rightarrow> ref list list \<Rightarrow> ref list list \<Rightarrow>
                       (ref \<Rightarrow> nat) \<Rightarrow> bool"
defs wf_levellist_def: "wf_levellist t levellist_old levellist_new var  \<equiv> 
case t of Tip \<Rightarrow> levellist_old = levellist_new
| (Node lt p rt) \<Rightarrow>
  (\<forall> q. q \<in> set_of t \<longrightarrow> q \<in> set (levellist_new ! (var q))) \<and>
  (\<forall> i \<le> var p. (\<exists> prx. (levellist_new ! i) = prx@(levellist_old ! i) 
                       \<and> (\<forall> pt \<in> set prx. pt \<in> set_of t \<and> var pt = i))) \<and>
  (\<forall> i. (var p) < i \<longrightarrow> (levellist_new ! i) = (levellist_old ! i)) \<and>
  (length levellist_new = length levellist_old)" 
*)


end
