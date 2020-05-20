theory EtaExpansionSafe
imports EtaExpansion Sestoft
begin

theorem eta_expansion_safe:
  assumes "set T \<subseteq> range Arg"
  shows "(\<Gamma>, eta_expand (length T) e, T@S) \<Rightarrow>\<^sup>* (\<Gamma>, e, T@S)"
using assms
proof(induction T arbitrary: e)
  case Nil show ?case by simp
next
  case (Cons se T)
  from Cons(2) obtain x where "se = Arg x" by auto

  from Cons have prem: "set T \<subseteq> range Arg" by simp
  
  have "(\<Gamma>, eta_expand (Suc (length T)) e, Arg x # T @ S) = (\<Gamma>, Lam [fresh_var e]. eta_expand (length T) (App e (fresh_var e)), Arg x # T @ S)" by simp
  also have "\<dots> \<Rightarrow> (\<Gamma>, (eta_expand (length T) (App e (fresh_var e)))[fresh_var e ::= x], T @ S)" by (rule app\<^sub>2)
  also have "\<dots> = (\<Gamma>, (eta_expand (length T) (App e x)), T @ S)" unfolding subst_eta_expand by simp
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Gamma>, App e x, T @ S)" by (rule Cons.IH[OF prem])
  also have "\<dots> \<Rightarrow> (\<Gamma>, e, Arg x # T @ S)"  by (rule app\<^sub>1)
  finally show ?case using \<open>se = _\<close> by simp
qed

fun arg_prefix :: "stack \<Rightarrow> nat" where
  "arg_prefix [] = 0"
| "arg_prefix (Arg x # S) = Suc (arg_prefix S)"
| "arg_prefix (Alts e1 e2 # S) = 0"
| "arg_prefix (Upd x # S) = 0"
| "arg_prefix (Dummy x # S) = 0"

theorem eta_expansion_safe':
  assumes "n \<le> arg_prefix S"
  shows "(\<Gamma>, eta_expand n e, S) \<Rightarrow>\<^sup>* (\<Gamma>, e, S)"
proof-
  from assms
  have "set (take n S) \<subseteq> range Arg" and "length (take n S) = n"
    apply (induction S arbitrary: n rule: arg_prefix.induct)
    apply auto
    apply (case_tac n, auto)+
    done
  hence "S = take n S @ drop n S" by (metis append_take_drop_id)
  with eta_expansion_safe[OF \<open>_ \<subseteq> _\<close>] \<open>length _ = _\<close>
  show ?thesis by metis
qed

end
