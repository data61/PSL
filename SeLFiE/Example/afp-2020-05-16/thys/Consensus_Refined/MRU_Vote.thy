section \<open>The MRU Vote Model\<close>

theory MRU_Vote
imports Same_Vote
begin

context quorum_process
begin

text \<open>This model is identical to Same Vote, except that it replaces
  the @{term safe} guard with the following one, which says that \<open>v\<close> is the
  most recently used (MRU) vote of a quorum:
\<close>

definition mru_guard :: "v_state \<Rightarrow> process set \<Rightarrow> val \<Rightarrow> bool" where
  "mru_guard s Q v \<equiv> Q \<in> Quorum \<and> (let mru = mru_of_set (votes s) Q in 
    mru = None \<or> (\<exists>r. mru = Some (r, v)))"

text \<open>The concrete algorithms will not refine the MRU Voting model directly, but its optimized
  version instead. For simplicity, we thus do not create the model explicitly, but just prove guard
  strengthening. We will show later that the optimized model refines the Same Vote model.\<close>

lemma mru_vote_implies_safe:
  assumes 
    inv4: "s \<in> SV_inv4"
    and inv1: "s \<in> Vinv1"
    and mru_vote: "mru_guard s Q v"
    and is_Quorum: "Q \<in> Quorum"
  shows "safe s (v_state.next_round s) v" using mru_vote
proof(clarsimp simp add: mru_guard_def mru_of_set_def option_Max_by_def)
  \<comment> \<open>The first case: some votes have been cast. We prove that the most recently used one is 
    safe.\<close>
  fix r
  assume
    nempty: "vote_set (votes s) Q \<noteq> {}" 
    and max: "Max_by fst (vote_set (votes s) Q) = (r, v)"

  from Max_by_in[OF Vinv1_finite_vote_set[OF inv1] nempty] max
  have in_votes: "(r, v) \<in> vote_set (votes s) Q" by metis

  have no_larger: "\<forall>a'\<in>Q. \<forall>r'>r. votes s r' a' = None"
  proof(safe, rule ccontr, clarsimp)
    fix a' r' w
    assume "a' \<in> Q"  "votes s r' a' = Some w" and gt: "r' > r"
    hence "(r', w) \<in> vote_set (votes s) Q"
      by(auto simp add: vote_set_def)
    thus False 
      using Max_by_ge[where f=fst, OF Vinv1_finite_vote_set[where Q=Q, OF inv1]] max gt
      by(clarsimp simp add: not_le[symmetric])
  qed

  have "safe s (Suc r) v" using inv4 in_votes and SV_inv4_def      
    by(clarsimp simp add: vote_set_def)

  thus "safe s (v_state.next_round s) v" using no_larger is_Quorum[THEN qintersect]
    apply(clarsimp simp add: safe_def quorum_for_def)
    by (metis IntE all_not_in_conv not_less_eq option.distinct(1))

next
  assume "vote_set (votes s) Q = {}"
  thus "safe s (v_state.next_round s) v" using is_Quorum[THEN qintersect]
    by(force simp add: vote_set_def safe_def quorum_for_def)
qed

end (* context quorum_process *)

end
