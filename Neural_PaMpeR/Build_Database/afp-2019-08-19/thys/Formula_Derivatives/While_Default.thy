theory While_Default
imports "HOL-Library.While_Combinator"
begin

context
  fixes d :: "'a"
  and b :: "'a \<Rightarrow> bool"
  and c :: "'a \<Rightarrow> 'a"
begin

definition while_default :: "'a \<Rightarrow> 'a" where
  "while_default s =
     (if \<forall>k. b ((c^^k) s) then d else the (while_option b c s))"

lemma while_default_code[code]:
   "while_default s = (if b s then while_default (c s) else s)"
proof (cases "\<forall>k. b ((c^^k) s)")
  case True
  moreover
  from spec[OF True, of "0"] have "b s" by simp_all
  moreover
  from spec[OF True, of "Suc m" for m] have "\<forall>k. b ((c^^k) (c s))"
    by (simp add: funpow_Suc_right del: funpow.simps(2))
  ultimately show ?thesis unfolding while_default_def by simp
next
  case False
  define k where "k = (LEAST k. \<not> b ((c ^^ k) s))"
  with False have k: "\<not> b ((c ^^ k) s)"
    "\<And>l. \<not> b ((c ^^ l) s) \<Longrightarrow> k \<le> l"
    by (auto intro!: LeastI_ex[of "\<lambda>k. \<not> b ((c ^^ k) s)"] Least_le)
  show ?thesis
  proof (cases k)
    case 0
    with k(1) have "\<not> b s" by auto
    with False show ?thesis by (auto simp add: while_default_def while_option_unfold)
  next
    case (Suc k)
    with k(2) have "b ((c ^^ 0) s)" by blast
    then have "b s" by simp
    with k(1) Suc False show ?thesis unfolding while_default_def
      by (subst while_option_unfold) (auto simp add: funpow_Suc_right simp del: funpow.simps(2))
  qed
qed

lemma while_default_rule:
  assumes c: "\<And>s. P s \<Longrightarrow> b s \<Longrightarrow> P (c s)"
  and t: "\<And>s. P s \<Longrightarrow> \<not> b s \<Longrightarrow> Q s"
  and s: "P s" and d: "Q d"
  shows "Q (while_default s)"
proof (cases "\<forall>k. b ((c^^k) s)")
  case False
  then obtain t where "while_option b c s = Some t" unfolding while_option_def by auto
  with False show ?thesis using while_option_rule[of P b c s t] while_option_stop[of b c s t] s c t
    by (auto simp add: while_default_def)
qed (simp add: while_default_def d t)

end

end
