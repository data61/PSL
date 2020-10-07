(* Author: Tobias Nipkow *)

section "Deterministic Online and Offline Algorithms"

theory On_Off
imports Complex_Main
begin

type_synonym ('s,'r,'a) alg_off = "'s \<Rightarrow> 'r list \<Rightarrow> 'a list"
type_synonym ('s,'is,'r,'a) alg_on = "('s \<Rightarrow> 'is) * ('s * 'is \<Rightarrow> 'r \<Rightarrow> 'a * 'is)"

locale On_Off =
fixes step :: "'state \<Rightarrow> 'request \<Rightarrow> 'answer \<Rightarrow> 'state"
fixes t :: "'state \<Rightarrow> 'request \<Rightarrow> 'answer \<Rightarrow> nat"
fixes wf :: "'state \<Rightarrow> 'request list \<Rightarrow> bool"
begin

fun T :: "'state \<Rightarrow> 'request list \<Rightarrow> 'answer list \<Rightarrow> nat" where
"T s [] [] = 0" |
"T s (r#rs) (a#as) = t s r a + T (step s r a) rs as"

definition Step ::
  "('state , 'istate, 'request, 'answer)alg_on
   \<Rightarrow> 'state * 'istate \<Rightarrow> 'request \<Rightarrow> 'state * 'istate"
where
"Step A s r = (let (a,is') = snd A s r in (step (fst s) r a, is'))"

fun config' :: "('state,'is,'request,'answer) alg_on  \<Rightarrow> ('state*'is) \<Rightarrow> 'request list  
    \<Rightarrow> ('state * 'is)" where
"config' A s []  = s" |
"config' A s (r#rs) = config' A (Step A s r) rs"

lemma config'_snoc: "config' A s (rs@[r]) = Step A (config' A s rs) r"
apply(induct rs arbitrary: s) by simp_all

lemma config'_append2: "config' A s (xs@ys) = config' A (config' A s xs) ys"
apply(induct xs arbitrary: s) by simp_all

lemma config'_induct: "P (fst init) \<Longrightarrow> (\<And>s q a. P s \<Longrightarrow> P (step s q a))
     \<Longrightarrow> P (fst (config' A init rs))"
apply (induct rs arbitrary: init) by(simp_all add: Step_def split: prod.split)

abbreviation config where
"config A s0 rs == config' A (s0, fst A s0) rs" 
 

lemma config_snoc: "config A s (rs@[r]) = Step A (config A s rs) r"
using config'_snoc by metis

lemma config_append: "config A s (xs@ys) = config' A (config A s xs) ys"
using config'_append2 by metis

lemma config_induct: "P s0 \<Longrightarrow> (\<And>s q a. P s \<Longrightarrow> P (step s q a)) \<Longrightarrow> P (fst (config A s0 qs))"
using config'_induct[of P "(s0, fst A s0)" ] by auto

fun T_on' :: "('state,'is,'request,'answer) alg_on \<Rightarrow> ('state*'is) \<Rightarrow> 'request list \<Rightarrow>  nat" where
"T_on' A s [] = 0" |
"T_on' A s (r#rs) = (t (fst s) r (fst (snd A s r))) + T_on' A (Step A s r) rs"

lemma T_on'_append: "T_on' A s (xs@ys) = T_on' A s xs + T_on' A (config' A s xs) ys"
apply(induct xs arbitrary: s) by simp_all   

abbreviation T_on'' :: "('state,'is,'request,'answer) alg_on \<Rightarrow> 'state \<Rightarrow> 'request list \<Rightarrow> nat" where
  "T_on'' A s rs == T_on' A (s,fst A s) rs" 

lemma T_on_append: "T_on'' A s (xs@ys) = T_on'' A s xs + T_on' A (config A s xs) ys"
by(rule T_on'_append)  

abbreviation "T_on_n A s0 xs n == T_on' A (config A s0 (take n xs)) [xs!n]" 

lemma T_on__as_sum: "T_on'' A s0 rs = sum (T_on_n A s0 rs) {..<length rs} "
apply(induct rs rule: rev_induct)
  by(simp_all add: T_on'_append  nth_append)



fun off2 :: "('state,'is,'request,'answer) alg_on \<Rightarrow> ('state * 'is,'request,'answer) alg_off" where
"off2 A s [] = []" |
"off2 A s (r#rs) = fst (snd A s r) # off2 A (Step A s r) rs"


abbreviation off :: "('state,'is,'request,'answer) alg_on \<Rightarrow> ('state,'request,'answer) alg_off" where
"off A s0 \<equiv> off2 A (s0, fst A s0)"


abbreviation T_off :: "('state,'request,'answer) alg_off \<Rightarrow> 'state \<Rightarrow> 'request list \<Rightarrow> nat" where
"T_off A s0 rs == T s0 rs (A s0 rs)"



abbreviation T_on :: "('state,'is,'request,'answer) alg_on \<Rightarrow> 'state \<Rightarrow> 'request list \<Rightarrow> nat" where
"T_on A == T_off (off A)"



lemma T_on_on': "T_off (\<lambda>s0. (off2 A (s0, x))) s0 qs = T_on' A (s0,x) qs"
apply(induct qs arbitrary: s0 x) 
  by(simp_all add: Step_def split: prod.split)

lemma T_on_on'': "T_on A s0 qs = T_on'' A s0 qs"
using T_on_on'[where x="fst A s0", of s0 qs A] by(auto)

lemma T_on_as_sum: "T_on A s0 rs = sum (T_on_n A s0 rs) {..<length rs} "
using T_on__as_sum T_on_on'' by metis



definition T_opt :: "'state \<Rightarrow> 'request list \<Rightarrow> nat" where
"T_opt s rs = Inf {T s rs as | as. size as = size rs}"

definition compet :: "('state,'is,'request,'answer) alg_on \<Rightarrow> real \<Rightarrow> 'state set \<Rightarrow> bool" where
"compet A c S = (\<forall>s\<in>S. \<exists>b \<ge> 0. \<forall>rs. wf s rs \<longrightarrow> real(T_on A s rs) \<le> c * T_opt s rs + b)"

lemma length_off[simp]: "length(off2 A s rs) = length rs"
by (induction rs arbitrary: s) (auto split: prod.split)

lemma compet_mono: assumes "compet A c S0" and "c \<le> c'"
shows "compet A c' S0"
proof (unfold compet_def, auto)
  let ?compt = "\<lambda>s0 rs b (c::real). T_on A s0 rs \<le> c * T_opt s0 rs + b"
  fix s0 assume "s0 \<in> S0"
  with assms(1) obtain b where "b \<ge> 0" and 1: "\<forall>rs. wf s0 rs \<longrightarrow> ?compt s0 rs b c"
    by(auto simp: compet_def)
  have "\<forall>rs.  wf s0 rs \<longrightarrow> ?compt s0 rs b c'"
  proof safe
    fix rs
    assume wf: "wf s0 rs"
    from 1 wf have "?compt s0 rs b c" by blast
    thus "?compt s0 rs b c'"
      using 1 mult_right_mono[OF assms(2) of_nat_0_le_iff[of "T_opt s0 rs"]]
      by arith
  qed
  thus "\<exists>b\<ge>0. \<forall>rs.  wf s0 rs \<longrightarrow> ?compt s0 rs b c'" using \<open>b\<ge>0\<close> by(auto)
qed

lemma competE: fixes c :: real
assumes "compet A c S0" "c \<ge> 0" "\<forall>s0 rs. size(aoff s0 rs) = length rs" "s0\<in>S0"
shows "\<exists>b\<ge>0. \<forall>rs. wf s0 rs \<longrightarrow> T_on A s0 rs \<le> c * T_off aoff s0 rs + b"
proof -
  from assms(1,4) obtain b where "b\<ge>0" and
    1: "\<forall>rs.  wf s0 rs \<longrightarrow> T_on A s0 rs \<le> c * T_opt s0 rs + b"
    by(auto simp add: compet_def)
  { fix rs
    assume "wf s0 rs"
    then have 2: "real(T_on A s0 rs) \<le> c * Inf {T s0 rs as | as. size as = size rs} + b"
      (is "_ \<le> _ * real(Inf ?T) + _")
      using 1 by(auto simp add: T_opt_def)
    have "Inf ?T \<le> T_off aoff s0 rs"
      using assms(3) by (intro cInf_lower) auto
    from mult_left_mono[OF of_nat_le_iff[THEN iffD2, OF this] assms(2)]
    have "T_on A s0 rs \<le> c * T_off aoff s0 rs + b" using 2 by arith
  }
  thus ?thesis using \<open>b\<ge>0\<close> by(auto simp: compet_def)
qed

end

end
