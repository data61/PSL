(*  Title:      JinjaThreads/Framework/FWInterrupt.thy
    Author:     Andreas Lochbihler
*)

section \<open>Semantics of the thread actions for interruption\<close>

theory FWInterrupt
imports
  FWState
begin

primrec redT_updI :: "'t interrupts \<Rightarrow> 't interrupt_action \<Rightarrow> 't interrupts"
where
  "redT_updI is (Interrupt t) = insert t is"
| "redT_updI is (ClearInterrupt t) = is - {t}"
| "redT_updI is (IsInterrupted t b) = is"

fun redT_updIs :: "'t interrupts \<Rightarrow> 't interrupt_action list \<Rightarrow> 't interrupts"
where
  "redT_updIs is [] = is"
| "redT_updIs is (ia # ias) = redT_updIs (redT_updI is ia) ias"

primrec interrupt_action_ok :: "'t interrupts \<Rightarrow> 't interrupt_action \<Rightarrow> bool"
where
  "interrupt_action_ok is (Interrupt t) = True"
| "interrupt_action_ok is (ClearInterrupt t) = True"
| "interrupt_action_ok is (IsInterrupted t b) = (b = (t \<in> is))"

fun interrupt_actions_ok :: "'t interrupts \<Rightarrow> 't interrupt_action list \<Rightarrow> bool"
where
  "interrupt_actions_ok is [] = True"
| "interrupt_actions_ok is (ia # ias) \<longleftrightarrow> interrupt_action_ok is ia \<and> interrupt_actions_ok (redT_updI is ia) ias"

primrec interrupt_action_ok' :: "'t interrupts \<Rightarrow> 't interrupt_action \<Rightarrow> bool"
where
  "interrupt_action_ok' is (Interrupt t) = True"
| "interrupt_action_ok' is (ClearInterrupt t) = True"
| "interrupt_action_ok' is (IsInterrupted t b) = (b \<or> t \<notin> is)"

fun interrupt_actions_ok' :: "'t interrupts \<Rightarrow> 't interrupt_action list \<Rightarrow> bool"
where
  "interrupt_actions_ok' is [] = True"
| "interrupt_actions_ok' is (ia # ias) \<longleftrightarrow> interrupt_action_ok' is ia \<and> interrupt_actions_ok' (redT_updI is ia) ias"

fun collect_interrupt :: "'t interrupt_action \<Rightarrow> 't set \<Rightarrow> 't set"
where
  "collect_interrupt (IsInterrupted t True) Ts = insert t Ts"
| "collect_interrupt (Interrupt t) Ts = Ts - {t}"
| "collect_interrupt _ Ts = Ts"

definition collect_interrupts :: "'t interrupt_action list \<Rightarrow> 't set"
where "collect_interrupts ias = foldr collect_interrupt ias {}"

lemma collect_interrupts_interrupted:
  "\<lbrakk> interrupt_actions_ok is ias; t' \<in> collect_interrupts ias \<rbrakk> \<Longrightarrow> t' \<in> is"
unfolding collect_interrupts_def
proof(induct ias arbitrary: "is")
  case Nil thus ?case by simp
next
  case (Cons ia ias) thus ?case
    by(cases "(ia, foldr collect_interrupt ias {})" rule: collect_interrupt.cases) auto
qed

lemma interrupt_actions_ok_append [simp]:
  "interrupt_actions_ok is (ias @ ias') \<longleftrightarrow> interrupt_actions_ok is ias \<and> interrupt_actions_ok (redT_updIs is ias) ias'"
by(induct ias arbitrary: "is") auto

lemma collect_interrupt_subset: "Ts \<subseteq> Ts' \<Longrightarrow> collect_interrupt ia Ts \<subseteq> collect_interrupt ia Ts'"
by(cases "(ia, Ts)" rule: collect_interrupt.cases) auto

lemma foldr_collect_interrupt_subset:
  "Ts \<subseteq> Ts' \<Longrightarrow> foldr collect_interrupt ias Ts \<subseteq> foldr collect_interrupt ias Ts'"
by(induct ias)(simp_all add: collect_interrupt_subset)

lemma interrupt_actions_ok_all_nthI:
  assumes "\<And>n. n < length ias \<Longrightarrow> interrupt_action_ok (redT_updIs is (take n ias)) (ias ! n)"
  shows "interrupt_actions_ok is ias"
using assms
proof(induct ias arbitrary: "is")
  case Nil thus ?case by simp
next
  case (Cons ia ias)
  from Cons.prems[of 0] have "interrupt_action_ok is ia" by simp
  moreover
  { fix n
    assume "n < length ias"
    hence "interrupt_action_ok (redT_updIs (redT_updI is ia) (take n ias)) (ias ! n)"
      using Cons.prems[of "Suc n"] by simp }
  hence "interrupt_actions_ok (redT_updI is ia) ias" by(rule Cons.hyps)
  ultimately show ?case by simp
qed

lemma interrupt_actions_ok_nthD:
  assumes "interrupt_actions_ok is ias"
  and "n < length ias"
  shows "interrupt_action_ok (redT_updIs is (take n ias)) (ias ! n)"
using assms
by(induct n arbitrary: "is" ias)(case_tac [!] ias, auto)

lemma interrupt_actions_ok'_all_nthI:
  assumes "\<And>n. n < length ias \<Longrightarrow> interrupt_action_ok' (redT_updIs is (take n ias)) (ias ! n)"
  shows "interrupt_actions_ok' is ias"
using assms
proof(induct ias arbitrary: "is")
  case Nil thus ?case by simp
next
  case (Cons ia ias)
  from Cons.prems[of 0] have "interrupt_action_ok' is ia" by simp
  moreover
  { fix n
    assume "n < length ias"
    hence "interrupt_action_ok' (redT_updIs (redT_updI is ia) (take n ias)) (ias ! n)"
      using Cons.prems[of "Suc n"] by simp }
  hence "interrupt_actions_ok' (redT_updI is ia) ias" by(rule Cons.hyps)
  ultimately show ?case by simp
qed

lemma interrupt_actions_ok'_nthD:
  assumes "interrupt_actions_ok' is ias"
  and "n < length ias"
  shows "interrupt_action_ok' (redT_updIs is (take n ias)) (ias ! n)"
using assms
by(induct n arbitrary: "is" ias)(case_tac [!] ias, auto)

lemma interrupt_action_ok_imp_interrupt_action_ok' [simp]:
  "interrupt_action_ok is ia \<Longrightarrow> interrupt_action_ok' is ia"
by(cases ia) simp_all

lemma interrupt_actions_ok_imp_interrupt_actions_ok' [simp]:
  "interrupt_actions_ok is ias \<Longrightarrow> interrupt_actions_ok' is ias"
by(induct ias arbitrary: "is")(simp_all)

lemma collect_interruptsE:
  assumes "t' \<in> collect_interrupts ias'"
  obtains n' where "n' < length ias'" "ias' ! n' = IsInterrupted t' True"
  and "Interrupt t' \<notin> set (take n' ias')"
proof(atomize_elim)
  from assms show "\<exists>n'<length ias'. ias' ! n' = IsInterrupted t' True \<and> Interrupt t' \<notin> set (take n' ias')"
    unfolding collect_interrupts_def
  proof(induct ias' arbitrary: t')
    case Nil thus ?case by simp
  next
    case (Cons ia ias) thus ?case
      by(cases "(ia, foldr collect_interrupt ias {})" rule: collect_interrupt.cases) fastforce+
  qed
qed

lemma collect_interrupts_prefix:
  "collect_interrupts ias \<subseteq> collect_interrupts (ias @ ias')"
by (metis Un_empty collect_interrupts_def foldr_append foldr_collect_interrupt_subset inf_sup_ord(1) inf_sup_ord(2) subset_Un_eq)

lemma redT_updI_insert_Interrupt:
  "\<lbrakk> t \<in> redT_updI is ia; t \<notin> is \<rbrakk> \<Longrightarrow> ia = Interrupt t"
by(cases ia) simp_all

lemma redT_updIs_insert_Interrupt:
  "\<lbrakk> t \<in> redT_updIs is ias; t \<notin> is \<rbrakk> \<Longrightarrow> Interrupt t \<in> set ias"
proof(induct ias arbitrary: "is")
  case Nil thus ?case by simp
next
  case (Cons ia ias) thus ?case
    by(cases "t \<in> redT_updI is ia")(auto dest: redT_updI_insert_Interrupt)
qed

lemma interrupt_actions_ok_takeI:
  "interrupt_actions_ok is ias \<Longrightarrow> interrupt_actions_ok is (take n ias)"
by(subst (asm) append_take_drop_id[symmetric, where n=n])(simp del: append_take_drop_id)

lemma interrupt_actions_ok'_collect_interrupts_imp_interrupt_actions_ok:
  assumes int: "interrupt_actions_ok' is ias"
  and ci: "collect_interrupts ias \<subseteq> is"
  and int': "interrupt_actions_ok is' ias"
  shows "interrupt_actions_ok is ias"
proof(rule interrupt_actions_ok_all_nthI)
  fix n
  assume n: "n < length ias"
  show "interrupt_action_ok (redT_updIs is (take n ias)) (ias ! n)"
  proof(cases "\<exists>t. ias ! n = IsInterrupted t True")
    case False
    with interrupt_actions_ok'_nthD[OF int n] show ?thesis by(cases "ias ! n") simp_all
  next
    case True
    then obtain t where ia: "ias ! n = IsInterrupted t True" ..
    from int' n have "interrupt_action_ok (redT_updIs is' (take n ias)) (ias ! n)" by(rule interrupt_actions_ok_nthD)
    with ia have "t \<in> redT_updIs is' (take n ias)" by simp
    moreover have "ias = take (Suc n) ias @ drop (Suc n) ias" by simp
    with ci have "collect_interrupts (take (Suc n) ias) \<subseteq> is"
      by (metis collect_interrupts_prefix subset_trans)
    ultimately have "t \<in> redT_updIs is (take n ias)" using n ia int int'
    proof(induct n arbitrary: "is" is' ias)
      case 0 thus ?case by(clarsimp simp add: neq_Nil_conv collect_interrupts_def)
    next
      case (Suc n)
      from \<open>Suc n < length ias\<close> obtain ia ias'
        where ias [simp]: "ias = ia # ias'" by(cases ias) auto
      from \<open>interrupt_actions_ok is' ias\<close>
      have ia_ok: "interrupt_action_ok is' ia" by simp
        
      from \<open>t \<in> redT_updIs is' (take (Suc n) ias)\<close>
      have "t \<in> redT_updIs (redT_updI is' ia) (take n ias')" by simp
      moreover from \<open>collect_interrupts (take (Suc (Suc n)) ias) \<subseteq> is\<close> ia_ok
      have "collect_interrupts (take (Suc n) ias') \<subseteq> redT_updI is ia"
      proof(cases "(ia, is)" rule: collect_interrupt.cases)
        case ("3_2" t' Ts)
        hence [simp]: "ia = ClearInterrupt t'" "Ts = is" by simp_all
        have "t' \<notin> collect_interrupts (take (Suc n) ias')"
        proof
          assume "t' \<in> collect_interrupts (take (Suc n) ias')"
          then obtain n' where "n' < length (take (Suc n) ias')" "take (Suc n) ias' ! n' = IsInterrupted t' True"
            "Interrupt t' \<notin> set (take n' (take (Suc n) ias'))" by(rule collect_interruptsE)
          hence "n' \<le> n" "ias' ! n' = IsInterrupted t' True" "Interrupt t' \<notin> set (take n' ias')"
            using \<open>Suc n < length ias\<close> by(simp_all add: min_def split: if_split_asm)
          hence "Suc n' < length ias" using \<open>Suc n < length ias\<close> by(simp add: min_def)
          with \<open>interrupt_actions_ok is' ias\<close> 
          have "interrupt_action_ok (redT_updIs is' (take (Suc n') ias)) (ias ! Suc n')"
            by(rule interrupt_actions_ok_nthD)
          with \<open>Suc n < length ias\<close> \<open>ias' ! n' = IsInterrupted t' True\<close>
          have "t' \<in> redT_updIs (is' - {t'}) (take n' ias')" by simp
          hence "Interrupt t' \<in> set (take n' ias')"
            by(rule redT_updIs_insert_Interrupt) simp
          with \<open>Interrupt t' \<notin> set (take n' ias')\<close> show False by contradiction
        qed
        thus ?thesis using \<open>collect_interrupts (take (Suc (Suc n)) ias) \<subseteq> is\<close>
          by(auto simp add: collect_interrupts_def)
      qed(auto simp add: collect_interrupts_def)
      moreover from \<open>Suc n < length ias\<close> have "n < length ias'" by simp
      moreover from \<open>ias ! Suc n = IsInterrupted t True\<close> have "ias' ! n = IsInterrupted t True" by simp
      moreover from \<open>interrupt_actions_ok' is ias\<close> have "interrupt_actions_ok' (redT_updI is ia) ias'"
        unfolding ias by simp
      moreover from \<open>interrupt_actions_ok is' ias\<close> have "interrupt_actions_ok (redT_updI is' ia) ias'" by simp
      ultimately have "t \<in> redT_updIs (redT_updI is ia) (take n ias')" by(rule Suc)
      thus ?case by simp
    qed
    thus ?thesis unfolding ia by simp
  qed
qed

end
