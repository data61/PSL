section "Simplifiying the definition"

theory Evaluate_Clock
imports Evaluate_Termination
begin

hide_const (open) sem_env.v

lemma fix_clock:
  "fix_clock s1 (s2, x) = (s, x) \<Longrightarrow> clock s \<le> clock s1"
  "fix_clock s1 (s2, x) = (s, x) \<Longrightarrow> clock s \<le> clock s2"
unfolding fix_clock_alt_def by auto

lemma dec_clock[simp]: "clock (dec_clock st) = clock st - 1"
unfolding dec_clock_def by auto

context begin

private lemma fun_evaluate_clock0:
  "clock (fst (fun_evaluate_match s1 env v p v')) \<le> clock s1"
  "clock (fst (fun_evaluate s1 env e)) \<le> clock s1"
proof (induction rule: fun_evaluate_match_fun_evaluate.induct)
  case (2 st env e1 e2 es)

  obtain st' r where *[simp]: "fix_clock st (fun_evaluate st env [e1]) = (st', r)"
    by force

  show ?case
    apply (auto split: prod.splits result.splits)
    subgoal
      using 2(2)[OF *[symmetric]]
      by (smt "*" fix_clock(1) fix_clock.simps fst_conv le_trans prod.collapse)
    subgoal
      using 2(2)[OF *[symmetric]]
      by (smt "*" fix_clock(1) fix_clock.simps fst_conv le_trans prod.collapse)
    subgoal
      by (metis "*" fix_clock(1) fix_clock.simps prod.collapse prod.sel(2))
    done
next
  case (5 st env e pes)

  obtain st' r where *[simp]: "fix_clock st (fun_evaluate st env [e]) = (st', r)"
    by force

  show ?case
    apply (auto split: prod.splits result.splits)
    subgoal
      by (metis "*" fix_clock(1) fix_clock.simps prod.collapse prod.sel(2))
    subgoal
      using 5(2)[OF *[symmetric]]
      by (smt "*" "5.IH"(1) dual_order.trans eq_fst_iff error_result.exhaust error_result.simps(5) error_result.simps(6) fix_clock(2) fix_clock.simps)
    done
next
  case (9 st env op1 es)

  obtain st' r where *[simp]: "fix_clock st (fun_evaluate st env (rev es)) = (st', r)"
    by force

  note do_app.simps[simp del]

  show ?case
    apply (auto split: prod.splits result.splits option.splits if_splits)
    subgoal
      by (metis "*" fix_clock(1) fix_clock.simps prod.collapse prod.sel(2))
    subgoal
      by (metis "*" fix_clock(1) fix_clock.simps prod.collapse prod.sel(2))
    subgoal
      by (smt "*" "9.IH"(2) One_nat_def Suc_pred dec_clock dual_order.trans fix_clock(1) fix_clock.simps fst_conv le_imp_less_Suc nat_less_le prod.collapse)
    subgoal
      by (metis "*" fix_clock(1) fix_clock.simps fst_conv prod.collapse)
    subgoal
      using 9(2)[OF *[symmetric], simplified]
      by (smt "*" Suc_pred dual_order.trans fix_clock(1) fix_clock.simps le_imp_less_Suc less_irrefl_nat nat_le_linear prod.collapse prod.sel(2))
    subgoal
      by (metis "*" fix_clock(1) fix_clock.simps prod.collapse prod.sel(2))
    subgoal
      using 9(2)[OF *[symmetric], simplified]
      by (smt "*" Suc_pred dual_order.trans fix_clock(1) fix_clock.simps le_imp_less_Suc less_irrefl_nat nat_le_linear prod.collapse prod.sel(2))
    done
next
  case (10 st env lop e1 e2)

  obtain st' r where *[simp]: "fix_clock st (fun_evaluate st env [e1]) = (st', r)"
    by force

  show ?case
    apply (auto split: prod.splits result.splits option.splits exp_or_val.splits)
    subgoal
      by (metis "*" fix_clock(1) fix_clock.simps fst_conv prod.collapse)
    subgoal
      using 10(2)[OF *[symmetric]]
      by (metis (no_types, lifting) "*" dual_order.trans fix_clock(1) fix_clock.simps fstI prod.collapse)
    subgoal
      by (metis "*" fix_clock(1) fix_clock.simps prod.collapse snd_conv)
    subgoal
      by (metis "*" fix_clock(1) fix_clock.simps fst_conv prod.exhaust_sel)
    done
next
  case (11 st env e1 e2 e3)

  obtain st' r where *[simp]: "fix_clock st (fun_evaluate st env [e1]) = (st', r)"
    by force

  show ?case
    apply (auto split: prod.splits result.splits option.splits)
    subgoal
      by (metis "*" fix_clock(1) fix_clock.simps fst_conv prod.collapse)
    subgoal
      using 11(2)[OF *[symmetric]]
      by (metis (no_types, lifting) "*" dual_order.trans eq_fst_iff fix_clock(1) fix_clock.simps)
    subgoal
      by (metis "*" fix_clock(1) fix_clock.simps fst_conv prod.exhaust_sel)
    done
next
  case (12 st env e pes)

  obtain st' r where *[simp]: "fix_clock st (fun_evaluate st env [e]) = (st', r)"
    by force

  show ?case
    apply (auto split: prod.splits result.splits option.splits)
    subgoal
      using 12(2)[OF *[symmetric]]
      by (metis (no_types, lifting) "*" dual_order.trans eq_fst_iff fix_clock(1) fix_clock.simps)
    subgoal
      by (metis "*" fix_clock(1) fix_clock.simps fst_conv prod.exhaust_sel)
    done
next
  case (13 st env xo e1 e2)

  obtain st' r where *[simp]: "fix_clock st (fun_evaluate st env [e1]) = (st', r)"
    by force

  show ?case
    apply (auto split: prod.splits result.splits option.splits)
    subgoal
      using 13(2)[OF *[symmetric]]
      by (metis (no_types, lifting) "*" dual_order.trans eq_fst_iff fix_clock(1) fix_clock.simps)
    subgoal
      by (metis "*" fix_clock(1) fix_clock.simps fst_conv prod.exhaust_sel)
    done
qed (auto split: prod.splits result.splits option.splits match_result.splits)

lemma fun_evaluate_clock:
  "fun_evaluate_match s1 env v p v' = (s2, r) \<Longrightarrow> clock s2 \<le> clock s1"
  "fun_evaluate s1 env e = (s2, r) \<Longrightarrow> clock s2 \<le> clock s1"
using fun_evaluate_clock0 by (metis fst_conv)+

end

lemma fix_clock_evaluate[simp]:
  "fix_clock s1 (fun_evaluate s1 env e) = fun_evaluate s1 env e"
unfolding fix_clock_alt_def
using fun_evaluate_clock by (fastforce split: prod.splits)

declare fun_evaluate.simps[simp del]
declare fun_evaluate_match.simps[simp del]

lemmas fun_evaluate_simps[simp] =
  fun_evaluate.simps[unfolded fix_clock_evaluate]
  fun_evaluate_match.simps[unfolded fix_clock_evaluate]

lemmas fun_evaluate_induct =
  fun_evaluate_match_fun_evaluate.induct[unfolded fix_clock_evaluate]

lemma fun_evaluate_length:
  "fun_evaluate_match s env v pes err_v = (s', res) \<Longrightarrow> (case res of Rval vs \<Rightarrow> length vs = 1 | _ \<Rightarrow> True)"
  "fun_evaluate s env es = (s', res) \<Longrightarrow> (case res of Rval vs \<Rightarrow> length vs = length es | _ \<Rightarrow> True)"
proof (induction arbitrary: s' res and s' res rule: fun_evaluate_match_fun_evaluate.induct)
  case (9 st env op1 es)
  then show ?case
    supply do_app.simps[simp del]
    apply (fastforce
        split: if_splits prod.splits result.splits option.splits exp_or_val.splits match_result.splits error_result.splits
        simp: list_result_alt_def)
    done
qed (fastforce
      split: if_splits prod.splits result.splits option.splits exp_or_val.splits
             match_result.splits error_result.splits)+

lemma fun_evaluate_matchE:
  assumes "fun_evaluate_match s env v pes err_v = (s', Rval vs)"
  obtains v where "vs = [v]"
using fun_evaluate_length(1)[OF assms]
by (cases vs) auto

end