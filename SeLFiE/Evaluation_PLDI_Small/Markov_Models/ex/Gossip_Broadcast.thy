(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section \<open>Formalization of the Gossip-Broadcast\<close>

theory Gossip_Broadcast
  imports "../Discrete_Time_Markov_Chain"
begin

lemma inj_on_upd_PiE:
  assumes "i \<notin> I" shows "inj_on (\<lambda>(x,f). f(i := x)) (M \<times> (\<Pi>\<^sub>E i\<in>I. A i))"
  unfolding PiE_def
proof (safe intro!: inj_onI ext)
  fix f g :: "'a \<Rightarrow> 'b" and x y :: 'b
  assume *: "f(i := x) = g(i := y)" "f \<in> extensional I" "g \<in> extensional I"
  then show "x = y" by (auto simp: fun_eq_iff split: if_split_asm)
  fix i' from * \<open>i \<notin> I\<close> show "f i' = g i'"
    by (cases "i' = i") (auto simp: fun_eq_iff extensional_def split: if_split_asm)
qed

lemma sum_folded_product:
  fixes I :: "'i set" and f :: "'s \<Rightarrow> 'i \<Rightarrow> 'a::{semiring_0, comm_monoid_mult}"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> finite (S i)"
  shows "(\<Sum>x\<in>Pi\<^sub>E I S. \<Prod>i\<in>I. f (x i) i) = (\<Prod>i\<in>I. \<Sum>s\<in>S i. f s i)"
using assms proof (induct I)
  case empty then show ?case by simp
next
  case (insert i I)
  have *: "Pi\<^sub>E (insert i I) S = (\<lambda>(x, f). f(i := x)) ` (S i \<times> Pi\<^sub>E I S)"
    by (auto simp: PiE_def intro!: image_eqI ext dest: extensional_arb)
  have "(\<Sum>x\<in>Pi\<^sub>E (insert i I) S. \<Prod>i\<in>insert i I. f (x i) i) =
    sum ((\<lambda>x. \<Prod>i\<in>insert i I. f (x i) i) \<circ> ((\<lambda>(x, f). f(i := x)))) (S i \<times> Pi\<^sub>E I S)"
    unfolding * using insert by (intro sum.reindex) (auto intro!: inj_on_upd_PiE)
  also have "\<dots> = (\<Sum>(a, x)\<in>(S i \<times> Pi\<^sub>E I S). f a i * (\<Prod>i\<in>I. f (x i) i))"
    using insert by (force intro!: sum.cong prod.cong arg_cong2[where f="(*)"])
  also have "\<dots> = (\<Sum>a\<in>S i. f a i * (\<Sum>x\<in>Pi\<^sub>E I S. \<Prod>i\<in>I. f (x i) i))"
    by (simp add: sum.cartesian_product sum_distrib_left)
  finally show ?case
    using insert by (simp add: sum_distrib_right)
qed

subsection \<open>Definition of the Gossip-Broadcast\<close>

datatype state = listening | sending | sleeping

type_synonym sys_state = "(nat \<times> nat) \<Rightarrow> state"

lemma state_UNIV: "UNIV = {listening, sending, sleeping}"
  by (auto intro: state.exhaust)

locale gossip_broadcast =
  fixes size :: nat and p :: real
  assumes size: "0 < size"
  assumes p: "0 < p" "p < 1"
begin

interpretation pmf_as_function .

definition states :: "sys_state set" where
  "states = ({..< size} \<times> {..< size}) \<rightarrow>\<^sub>E {listening, sending, sleeping}"

definition start :: sys_state where
  "start = (\<lambda>x\<in>{..< size}\<times>{..< size}. listening)((0, 0) := sending)"

definition neighbour_sending where
  "neighbour_sending s = (\<lambda>(x,y).
    (x > 0 \<and> s (x - 1, y) = sending) \<or>
    (x < size \<and> s (x + 1, y) = sending) \<or>
    (y > 0 \<and> s (x, y - 1) = sending) \<or>
    (y < size \<and> s (x, y + 1) = sending))"

definition node_trans :: "sys_state \<Rightarrow> (nat \<times> nat) \<Rightarrow> state \<Rightarrow> state \<Rightarrow> real" where
"node_trans g x s = (case s of
  listening \<Rightarrow> (if neighbour_sending g x
    then (\<lambda>_.0) (sending := p, sleeping := 1 - p)
    else (\<lambda>_.0) (listening := 1))
| sending   \<Rightarrow> (\<lambda>_.0) (sleeping := 1)
| sleeping  \<Rightarrow> (\<lambda>_.0) (sleeping := 1))"

lemma node_trans_sum_eq_1[simp]:
  "node_trans g x s' listening + (node_trans g x s' sending + node_trans g x s' sleeping) = 1"
  by (simp add: node_trans_def split: state.split)

lemma node_trans_nonneg[simp]: "0 \<le> node_trans s x i j"
  using p by (auto simp: node_trans_def split: state.split)

lift_definition proto_trans :: "sys_state \<Rightarrow> sys_state pmf" is
  "\<lambda>s s'. if s' \<in> states then (\<Prod>x\<in>{..< size}\<times>{..< size}. node_trans s x (s x) (s' x)) else 0"
proof
  let ?f = "\<lambda>s s'. if s' \<in> states then (\<Prod>x\<in>{..< size}\<times>{..< size}. node_trans s x (s x) (s' x)) else 0"
  fix s show "\<forall>t. 0 \<le> ?f s t"
    using p by (auto intro!: prod_nonneg simp: node_trans_def split: state.split)
  show "(\<integral>\<^sup>+t. ?f s t \<partial>count_space UNIV) = 1"
    apply (subst nn_integral_count_space'[of states])
    apply (simp_all add: prod_nonneg)
  proof -
    show "(\<Sum>x\<in>states. \<Prod>xa\<in>{..<size} \<times> {..<size}. node_trans s xa (s xa) (x xa)) = 1"
      unfolding states_def by (subst sum_folded_product) simp_all
    show "finite states"
      by (auto simp: states_def intro!: finite_PiE)
  qed
qed

end

subsection \<open>The Gossip-Broadcast forms a DTMC\<close>

sublocale gossip_broadcast \<subseteq> MC_syntax proto_trans .

end
