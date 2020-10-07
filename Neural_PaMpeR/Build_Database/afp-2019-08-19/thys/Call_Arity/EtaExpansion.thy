theory EtaExpansion
imports Launchbury.Terms Launchbury.Substitution
begin

definition fresh_var :: "exp \<Rightarrow> var" where
  "fresh_var e = (SOME v. v \<notin> fv e)"

lemma fresh_var_not_free:
  "fresh_var e \<notin> fv e"
proof-
  obtain v :: var where "atom v \<sharp> e" by (rule obtain_fresh)
  hence "v \<notin> fv e" by (metis fv_not_fresh)
  thus ?thesis unfolding fresh_var_def by (rule someI)
qed

lemma fresh_var_fresh[simp]:
  "atom (fresh_var e) \<sharp> e"
  by (metis fresh_var_not_free fv_not_fresh)

lemma fresh_var_subst[simp]:
  "e[fresh_var e::=x] = e"
  by (metis fresh_var_fresh subst_fresh_noop)

fun eta_expand :: "nat \<Rightarrow> exp \<Rightarrow> exp" where
   "eta_expand 0 e = e"
|  "eta_expand (Suc n) e = (Lam [fresh_var e]. eta_expand n (App e (fresh_var e)))"

lemma eta_expand_eqvt[eqvt]:
  "\<pi> \<bullet> (eta_expand n e) = eta_expand (\<pi> \<bullet> n) (\<pi> \<bullet> e)"
  apply (induction n arbitrary: e \<pi>)
  apply (auto simp add: fresh_Pair permute_pure)
  apply (metis fresh_at_base_permI fresh_at_base_permute_iff fresh_var_fresh subst_fresh_noop subst_swap_same)
  done

lemma fresh_eta_expand[simp]: "a \<sharp> eta_expand n e \<longleftrightarrow> a \<sharp> e"
  apply (induction n arbitrary: e)
  apply  (simp add: fresh_Pair)
  apply  (clarsimp simp add: fresh_Pair fresh_at_base)
  by (metis fresh_var_fresh)

lemma subst_eta_expand: "(eta_expand n e)[x ::= y] = eta_expand n (e[x ::= y])"
proof (induction n arbitrary: e)
case 0 thus ?case by simp
next
case (Suc n)
  obtain z :: var where "atom z \<sharp> (e, fresh_var e, x, y)" by (rule obtain_fresh)
  
  have "(eta_expand (Suc n) e)[x::=y] = (Lam [fresh_var e]. eta_expand n (App e (fresh_var e)))[x::=y]" by simp
  also have "\<dots> = (Lam [z]. eta_expand n (App e z))[x::=y]"
    apply (subst change_Lam_Variable[where y' = z])
    using \<open>atom z \<sharp> _\<close>
    by (auto simp add: fresh_Pair eta_expand_eqvt pure_fresh permute_pure flip_fresh_fresh intro!: eqvt_fresh_cong2[where f = eta_expand, OF eta_expand_eqvt])
  also have "\<dots> = Lam [z]. (eta_expand n (App e z))[x::=y]"
    using \<open>atom z \<sharp> _\<close> by simp
  also have "\<dots> = Lam [z]. eta_expand n (App e z)[x::=y]" unfolding Suc.IH..
  also have "\<dots> = Lam [z]. eta_expand n (App e[x::=y] z)"
    using \<open>atom z \<sharp> _\<close> by simp
  also have "\<dots> = Lam [fresh_var (e[x::=y])]. eta_expand n (App e[x::=y] (fresh_var (e[x::=y])))"
    apply (subst change_Lam_Variable[where y' = "fresh_var (e[x::=y])"])
    using \<open>atom z \<sharp> _\<close>
    by (auto simp add: fresh_Pair eqvt_fresh_cong2[where f = eta_expand, OF eta_expand_eqvt] pure_fresh eta_expand_eqvt  flip_fresh_fresh subst_pres_fresh simp del: exp_assn.eq_iff)
  also have "\<dots> = eta_expand (Suc n) e[x::=y]" by simp
  finally show ?case.
qed

lemma isLam_eta_expand:
  "isLam e \<Longrightarrow> isLam (eta_expand n e)" and "n > 0 \<Longrightarrow> isLam (eta_expand n e)"
by (induction n) auto

lemma isVal_eta_expand:
  "isVal e \<Longrightarrow> isVal (eta_expand n e)" and "n > 0 \<Longrightarrow> isVal (eta_expand n e)"
by (induction n) auto


end
