(* Author: Matthias Brun,   ETH Zürich, 2019 *)
(* Author: Dmitriy Traytel, ETH Zürich, 2019 *)

section \<open>Agreement Relation\<close>

(*<*)
theory Agreement
  imports Semantics
begin
(*>*)

inductive agree :: "tyenv \<Rightarrow> term \<Rightarrow> term \<Rightarrow> term \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _, _, _ : _" [150,0,0,0,150] 149) where
  a_Unit: "\<Gamma> \<turnstile> Unit, Unit, Unit : One" |
  a_Var: "\<Gamma> $$ x = Some \<tau>
    \<Longrightarrow> \<Gamma> \<turnstile> Var x, Var x, Var x : \<tau>" |
  a_Lam: "\<lbrakk> atom x \<sharp> \<Gamma>; \<Gamma>(x $$:= \<tau>\<^sub>1) \<turnstile> e, eP, eV : \<tau>\<^sub>2 \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Lam x e, Lam x eP, Lam x eV : Fun \<tau>\<^sub>1 \<tau>\<^sub>2" |
  a_App: "\<lbrakk> \<Gamma> \<turnstile> e\<^sub>1, eP\<^sub>1, eV\<^sub>1 : Fun \<tau>\<^sub>1 \<tau>\<^sub>2; \<Gamma> \<turnstile> e\<^sub>2, eP\<^sub>2, eV\<^sub>2 : \<tau>\<^sub>1 \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> App e\<^sub>1 e\<^sub>2, App eP\<^sub>1 eP\<^sub>2, App eV\<^sub>1 eV\<^sub>2 : \<tau>\<^sub>2" |
  a_Let: "\<lbrakk> atom x \<sharp> (\<Gamma>, e\<^sub>1, eP\<^sub>1, eV\<^sub>1); \<Gamma> \<turnstile> e\<^sub>1, eP\<^sub>1, eV\<^sub>1 : \<tau>\<^sub>1; \<Gamma>(x $$:= \<tau>\<^sub>1) \<turnstile> e\<^sub>2, eP\<^sub>2, eV\<^sub>2 : \<tau>\<^sub>2 \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Let e\<^sub>1 x e\<^sub>2, Let eP\<^sub>1 x eP\<^sub>2, Let eV\<^sub>1 x eV\<^sub>2 : \<tau>\<^sub>2" |
  a_Rec: "\<lbrakk> atom x \<sharp> \<Gamma>; atom y \<sharp> (\<Gamma>,x); \<Gamma>(x $$:= Fun \<tau>\<^sub>1 \<tau>\<^sub>2) \<turnstile> Lam y e, Lam y eP, Lam y eV : Fun \<tau>\<^sub>1 \<tau>\<^sub>2 \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Rec x (Lam y e), Rec x (Lam y eP), Rec x (Lam y eV) : Fun \<tau>\<^sub>1 \<tau>\<^sub>2" |
  a_Inj1: "\<lbrakk> \<Gamma> \<turnstile> e, eP, eV : \<tau>\<^sub>1 \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Inj1 e, Inj1 eP, Inj1 eV : Sum \<tau>\<^sub>1 \<tau>\<^sub>2" |
  a_Inj2: "\<lbrakk> \<Gamma> \<turnstile> e, eP, eV : \<tau>\<^sub>2 \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Inj2 e, Inj2 eP, Inj2 eV : Sum \<tau>\<^sub>1 \<tau>\<^sub>2" |
  a_Case: "\<lbrakk> \<Gamma> \<turnstile> e, eP, eV : Sum \<tau>\<^sub>1 \<tau>\<^sub>2; \<Gamma> \<turnstile> e\<^sub>1, eP\<^sub>1, eV\<^sub>1 : Fun \<tau>\<^sub>1 \<tau>; \<Gamma> \<turnstile> e\<^sub>2, eP\<^sub>2, eV\<^sub>2 : Fun \<tau>\<^sub>2 \<tau> \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Case e e\<^sub>1 e\<^sub>2, Case eP eP\<^sub>1 eP\<^sub>2, Case eV eV\<^sub>1 eV\<^sub>2 : \<tau>" |
  a_Pair: "\<lbrakk> \<Gamma> \<turnstile> e\<^sub>1, eP\<^sub>1, eV\<^sub>1 : \<tau>\<^sub>1; \<Gamma> \<turnstile> e\<^sub>2, eP\<^sub>2, eV\<^sub>2 : \<tau>\<^sub>2 \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Pair e\<^sub>1 e\<^sub>2, Pair eP\<^sub>1 eP\<^sub>2, Pair eV\<^sub>1 eV\<^sub>2 : Prod \<tau>\<^sub>1 \<tau>\<^sub>2" |
  a_Prj1: "\<lbrakk> \<Gamma> \<turnstile> e, eP, eV : Prod \<tau>\<^sub>1 \<tau>\<^sub>2 \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Prj1 e, Prj1 eP, Prj1 eV : \<tau>\<^sub>1" |
  a_Prj2: "\<lbrakk> \<Gamma> \<turnstile> e, eP, eV : Prod \<tau>\<^sub>1 \<tau>\<^sub>2 \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Prj2 e, Prj2 eP, Prj2 eV : \<tau>\<^sub>2" |
  a_Roll: "\<lbrakk> atom \<alpha> \<sharp> \<Gamma>; \<Gamma> \<turnstile> e, eP, eV : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha> \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Roll e, Roll eP, Roll eV : Mu \<alpha> \<tau>" |
  a_Unroll: "\<lbrakk> atom \<alpha> \<sharp> \<Gamma>; \<Gamma> \<turnstile> e, eP, eV : Mu \<alpha> \<tau> \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Unroll e, Unroll eP, Unroll eV : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha>" |
  a_Auth: "\<lbrakk> \<Gamma> \<turnstile> e, eP, eV : \<tau> \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Auth e, Auth eP, Auth eV : AuthT \<tau>" |
  a_Unauth: "\<lbrakk> \<Gamma> \<turnstile> e, eP, eV : AuthT \<tau> \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> Unauth e, Unauth eP, Unauth eV : \<tau>" |
  a_HashI: "\<lbrakk> {$$} \<turnstile> v, vP, \<lparr>vP\<rparr> : \<tau>; hash \<lparr>vP\<rparr> = h; value v; value vP \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> v, Hashed h vP, Hash h : AuthT \<tau>"

declare agree.intros[intro]

equivariance agree
nominal_inductive agree
  avoids a_Lam: x
       | a_Rec: x and y
       | a_Let: x
       | a_Roll: \<alpha>
       | a_Unroll: \<alpha>
  by (auto simp: fresh_Pair fresh_subst_type)

lemma Abs_lst_eq_3tuple:
  fixes x x' :: var
  fixes e eP eV e' eP' eV' :: "term"
  assumes "[[atom x]]lst. e = [[atom x']]lst. e'"
  and     "[[atom x]]lst. eP = [[atom x']]lst. eP'"
  and     "[[atom x]]lst. eV = [[atom x']]lst. eV'"
  shows   "[[atom x]]lst. (e, eP, eV) = [[atom x']]lst. (e', eP', eV')"
  using assms by (simp add: fresh_Pair)

lemma agree_fresh_env_fresh_term:
  fixes a :: var
  assumes "\<Gamma> \<turnstile> e, eP, eV : \<tau>" "atom a \<sharp> \<Gamma>"
  shows   "atom a \<sharp> (e, eP, eV)"
  using assms proof (nominal_induct \<Gamma> e eP eV \<tau> avoiding: a rule: agree.strong_induct)
  case (a_Var \<Gamma> x \<tau>)
  then show ?case
    by (cases "a = x") (auto simp: fresh_tyenv_None)
qed (simp_all add: fresh_Cons fresh_fmap_update fresh_Pair)

lemma agree_empty_fresh[dest]:
  fixes a :: var
  assumes "{$$} \<turnstile> e, eP, eV : \<tau>"
  shows   "{atom a} \<sharp>* {e, eP, eV}"
  using assms by (auto simp: fresh_Pair dest: agree_fresh_env_fresh_term)

text \<open>Inversion rules for agreement.\<close>

declare [[simproc del: alpha_lst]]

lemma a_Lam_inv_I[elim]:
  assumes "\<Gamma> \<turnstile> (Lam x e'), eP, eV : (Fun \<tau>\<^sub>1 \<tau>\<^sub>2)"
  and     "atom x \<sharp> \<Gamma>"
  obtains eP' eV' where "eP = Lam x eP'" "eV = Lam x eV'" "\<Gamma>(x $$:= \<tau>\<^sub>1) \<turnstile> e', eP', eV' : \<tau>\<^sub>2"
  using assms
proof (atomize_elim, nominal_induct \<Gamma> "Lam x e'" eP eV "Fun \<tau>\<^sub>1 \<tau>\<^sub>2" avoiding: x e' \<tau>\<^sub>1 \<tau>\<^sub>2 rule: agree.strong_induct)
  case (a_Lam x \<Gamma> \<tau>\<^sub>1 e eP eV \<tau>\<^sub>2 y e')
  show ?case
  proof (intro exI conjI)
    from a_Lam show "Lam x eP = Lam y ((x \<leftrightarrow> y) \<bullet> eP)"
      by (auto intro!: Abs_lst_eq_flipI  dest!: agree_fresh_env_fresh_term
        simp: fresh_fmap_update fresh_Pair)
    from a_Lam show "Lam x eV = Lam y ((x \<leftrightarrow> y) \<bullet> eV)"
      by (auto intro!: Abs_lst_eq_flipI  dest!: agree_fresh_env_fresh_term
        simp: fresh_fmap_update fresh_Pair)
    from a_Lam(1-6,8,10) show "\<Gamma>(y $$:= \<tau>\<^sub>1) \<turnstile> e', (x \<leftrightarrow> y) \<bullet> eP, (x \<leftrightarrow> y) \<bullet> eV : \<tau>\<^sub>2"
      by (auto simp: perm_supp_eq Abs1_eq_iff(3)
        dest!: agree.eqvt[where p = "(x \<leftrightarrow> y)", of "\<Gamma>(x $$:= \<tau>\<^sub>1)"])
  qed
qed

lemma a_Lam_inv_P[elim]:
  assumes "{$$} \<turnstile> v, (Lam x vP'), vV : (Fun \<tau>\<^sub>1 \<tau>\<^sub>2)"
  obtains v' vV' where "v = Lam x v'" "vV = Lam x vV'" "{$$}(x $$:= \<tau>\<^sub>1) \<turnstile> v', vP', vV' : \<tau>\<^sub>2"
  using assms
proof (atomize_elim, nominal_induct "{$$}::tyenv" v "Lam x vP'" vV "Fun \<tau>\<^sub>1 \<tau>\<^sub>2" avoiding: x vP' rule: agree.strong_induct)
  case (a_Lam x' e eP eV)
  show ?case
  proof (intro exI conjI)
    from a_Lam show "Lam x' e = Lam x ((x' \<leftrightarrow> x) \<bullet> e)"
      by (auto intro!: Abs_lst_eq_flipI  dest!: agree_fresh_env_fresh_term
        simp: fresh_fmap_update fresh_Pair)
    from a_Lam show "Lam x' eV = Lam x ((x' \<leftrightarrow> x) \<bullet> eV)"
      by (auto intro!: Abs_lst_eq_flipI  dest!: agree_fresh_env_fresh_term
        simp: fresh_fmap_update fresh_Pair)
    from a_Lam(1-4,6) show "{$$}(x $$:= \<tau>\<^sub>1) \<turnstile> (x' \<leftrightarrow> x) \<bullet> e, vP', (x' \<leftrightarrow> x) \<bullet> eV : \<tau>\<^sub>2"
      by (auto simp: perm_supp_eq Abs1_eq_iff(3)
        dest!: agree.eqvt[where p = "(x' \<leftrightarrow> x)", of "{$$}(x' $$:= \<tau>\<^sub>1)"])
  qed
qed

lemma a_Lam_inv_V[elim]:
  assumes "{$$} \<turnstile> v, vP, (Lam x vV') : (Fun \<tau>\<^sub>1 \<tau>\<^sub>2)"
  obtains v' vP' where "v = Lam x v'" "vP = Lam x vP'" "{$$}(x $$:= \<tau>\<^sub>1) \<turnstile> v', vP', vV' : \<tau>\<^sub>2"
  using assms
proof (atomize_elim, nominal_induct "{$$}::tyenv" v vP "Lam x vV'" "Fun \<tau>\<^sub>1 \<tau>\<^sub>2" avoiding: x vV' rule: agree.strong_induct)
  case (a_Lam x' e eP eV)
  show ?case
  proof (intro exI conjI)
    from a_Lam show "Lam x' e = Lam x ((x' \<leftrightarrow> x) \<bullet> e)"
      by (auto intro!: Abs_lst_eq_flipI  dest!: agree_fresh_env_fresh_term
        simp: fresh_fmap_update fresh_Pair)
    from a_Lam show "Lam x' eP = Lam x ((x' \<leftrightarrow> x) \<bullet> eP)"
      by (auto intro!: Abs_lst_eq_flipI  dest!: agree_fresh_env_fresh_term
        simp: fresh_fmap_update fresh_Pair)
    from a_Lam(1-4,6) show "{$$}(x $$:= \<tau>\<^sub>1) \<turnstile> (x' \<leftrightarrow> x) \<bullet> e, (x' \<leftrightarrow> x) \<bullet> eP, vV' : \<tau>\<^sub>2"
      by (auto simp: perm_supp_eq Abs1_eq_iff(3)
        dest!: agree.eqvt[where p = "(x' \<leftrightarrow> x)", of "{$$}(x' $$:= \<tau>\<^sub>1)"])
  qed
qed

lemma a_Rec_inv_I[elim]:
  assumes "\<Gamma> \<turnstile> Rec x e, eP, eV : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
  and     "atom x \<sharp> \<Gamma>"
  obtains y e' eP' eV'
  where "e = Lam y e'" "eP = Rec x (Lam y eP')" "eV = Rec x (Lam y eV')" "atom y \<sharp> (\<Gamma>,x)"
        "\<Gamma>(x $$:= Fun \<tau>\<^sub>1 \<tau>\<^sub>2) \<turnstile> Lam y e', Lam y eP', Lam y eV' : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
  using assms
proof (atomize_elim, nominal_induct \<Gamma> "Rec x e" eP eV "Fun \<tau>\<^sub>1 \<tau>\<^sub>2" avoiding: x e rule: agree.strong_induct)
  case (a_Rec x' \<Gamma> y e' eP eV)
  then show ?case
  proof (nominal_induct e avoiding: x x' y rule: term.strong_induct)
    case Unit
    from Unit(9) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Var x)
    from Var(9) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Lam z ee)
    show ?case
    proof (intro conjI exI)
      from Lam(1-3,5-13,15) show "Lam z ee = Lam y ((z \<leftrightarrow> y) \<bullet> ee)"
        by (auto intro: Abs_lst_eq_flipI simp: fresh_fmap_update fresh_Pair)
      from Lam(1-3,5-13,15) show "Rec x' (Lam y eP) = Rec x (Lam y ((x' \<leftrightarrow> x) \<bullet> eP))"
        using Abs_lst_eq_flipI[of x "Lam y eP" x']
        by (elim agree_fresh_env_fresh_term[where a = x, elim_format])
          (simp_all add: fresh_fmap_update fresh_Pair)
      from Lam(1-3,5-13,15) show "Rec x' (Lam y eV) = Rec x (Lam y ((x' \<leftrightarrow> x) \<bullet> eV))"
        using Abs_lst_eq_flipI[of x "Lam y eV" x']
        by (elim agree_fresh_env_fresh_term[where a = x, elim_format])
          (simp_all add: fresh_fmap_update fresh_Pair)
      from Lam(7,10) show "atom y \<sharp> (\<Gamma>, x)"
        by simp
      from Lam(1-3,5-11,13) have "(x' \<leftrightarrow> x) \<bullet> e' = (z \<leftrightarrow> y) \<bullet> ee"
        by (simp add: Abs1_eq_iff flip_commute swap_permute_swap fresh_perm fresh_at_base)
      with Lam(1-2,7,9,11-12,15) show "\<Gamma>(x $$:= Fun \<tau>\<^sub>1 \<tau>\<^sub>2) \<turnstile>
        Lam y ((z \<leftrightarrow> y) \<bullet> ee), Lam y ((x' \<leftrightarrow> x) \<bullet> eP), Lam y ((x' \<leftrightarrow> x) \<bullet> eV) : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
        by (elim agree.eqvt[of _ "Lam y e'" _ _ _ "(x' \<leftrightarrow> x)", elim_format]) (simp add:  perm_supp_eq)
    qed
  next
    case (Rec x1 x2a)
    from Rec(13) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Inj1 x)
    from Inj1(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Inj2 x)
    from Inj2(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Pair x1 x2a)
    from Pair(11) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Roll x)
    from Roll(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Let x1 x2a x3)
    from Let(14) show ?case by (simp add: Abs1_eq_iff)
  next
    case (App x1 x2a)
    from App(11) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Case x1 x2a x3)
    from Case(12) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Prj1 x)
    from Prj1(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Prj2 x)
    from Prj2(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Unroll x)
    from Unroll(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Auth x)
    from Auth(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Unauth x)
    from Unauth(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Hash x)
    from Hash(9) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Hashed x1 x2a)
    from Hashed(10) show ?case by (simp add: Abs1_eq_iff)
  qed
qed

lemma a_Rec_inv_P[elim]:
  assumes "\<Gamma> \<turnstile> e, Rec x eP, eV : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
  and     "atom x \<sharp> \<Gamma>"
  obtains y e' eP' eV'
  where "e = Rec x (Lam y e')" "eP = Lam y eP'" "eV = Rec x (Lam y eV')" "atom y \<sharp> (\<Gamma>,x)"
        "\<Gamma>(x $$:= Fun \<tau>\<^sub>1 \<tau>\<^sub>2) \<turnstile> Lam y e', Lam y eP', Lam y eV' : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
  using assms
proof (atomize_elim,nominal_induct \<Gamma> e "Rec x eP" eV "Fun \<tau>\<^sub>1 \<tau>\<^sub>2" avoiding: x eP rule: agree.strong_induct)
  case (a_Rec x \<Gamma> y e eP eV x' eP')
  then show ?case
  proof (nominal_induct eP' avoiding: x' x y rule: term.strong_induct)
    case Unit
    from Unit(9) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Var x)
    from Var(9) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Lam ya eP')
    show ?case
    proof (intro conjI exI)
      from Lam(1-3,5-13,15) show "Rec x (Lam y e) = Rec x' (Lam y ((x \<leftrightarrow> x') \<bullet> e))"
        using Abs_lst_eq_flipI[of x' "Lam y e" x]
        by (elim agree_fresh_env_fresh_term[where a = x', elim_format])
          (simp_all add: fresh_fmap_update fresh_Pair)
      from Lam(1-3,5-13,15) show "Lam ya eP' = Lam y ((x \<leftrightarrow> x') \<bullet> eP)"
        unfolding trans[OF eq_sym_conv Abs1_eq_iff(3)]
        by (simp add: flip_commute fresh_at_base)
      from Lam(1-3,5-13,15) show "Rec x (Lam y eV) = Rec x' (Lam y ((x \<leftrightarrow> x') \<bullet> eV))"
        using Abs_lst_eq_flipI[of x' "Lam y eV" x]
        by (elim agree_fresh_env_fresh_term[where a = x', elim_format])
          (simp_all add: fresh_fmap_update fresh_Pair)
      from Lam(7,10) show "atom y \<sharp> (\<Gamma>, x')"
        by simp
      with Lam(1-2,7,9,11-12,15) show "\<Gamma>(x' $$:= Fun \<tau>\<^sub>1 \<tau>\<^sub>2) \<turnstile>
        Lam y ((x \<leftrightarrow> x') \<bullet> e), Lam y ((x \<leftrightarrow> x') \<bullet> eP), Lam y ((x \<leftrightarrow> x') \<bullet> eV) : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
        by (elim agree.eqvt[of _ "Lam y _" _ _ _ "(x' \<leftrightarrow> x)", elim_format])
          (simp add:  perm_supp_eq flip_commute)
    qed
  next
    case (Rec x1 x2a)
    from Rec(13) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Inj1 x)
    from Inj1(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Inj2 x)
    from Inj2(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Pair x1 x2a)
    from Pair(11) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Roll x)
    from Roll(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Let x1 x2a x3)
    from Let(14) show ?case by (simp add: Abs1_eq_iff)
  next
    case (App x1 x2a)
    from App(11) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Case x1 x2a x3)
    from Case(12) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Prj1 x)
    from Prj1(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Prj2 x)
    from Prj2(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Unroll x)
    from Unroll(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Auth x)
    from Auth(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Unauth x)
    from Unauth(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Hash x)
    from Hash(9) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Hashed x1 x2a)
    from Hashed(10) show ?case by (simp add: Abs1_eq_iff)
  qed
qed

lemma a_Rec_inv_V[elim]:
  assumes "\<Gamma> \<turnstile> e, eP, Rec x eV : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
    and     "atom x \<sharp> \<Gamma>"
  obtains y e' eP' eV'
  where "e = Rec x (Lam y e')" "eP = Rec x (Lam y eP')" "eV = Lam y eV'" "atom y \<sharp> (\<Gamma>,x)"
    "\<Gamma>(x $$:= Fun \<tau>\<^sub>1 \<tau>\<^sub>2) \<turnstile> Lam y e', Lam y eP', Lam y eV' : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
  using assms
proof (atomize_elim, nominal_induct \<Gamma> e eP "Rec x eV" "Fun \<tau>\<^sub>1 \<tau>\<^sub>2" avoiding: x eV rule: agree.strong_induct)
  case (a_Rec x \<Gamma> y e eP eV x' eV')
  then show ?case
  proof (nominal_induct eV' avoiding: x' x y rule: term.strong_induct)
    case Unit
    from Unit(9) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Var x)
    from Var(9) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Lam ya eV')
    show ?case
    proof (intro conjI exI)
      from Lam(1-3,5-13,15) show "Rec x (Lam y e) = Rec x' (Lam y ((x \<leftrightarrow> x') \<bullet> e))"
        using Abs_lst_eq_flipI[of x' "Lam y e" x]
        by (elim agree_fresh_env_fresh_term[where a = x', elim_format])
          (simp_all add: fresh_fmap_update fresh_Pair)
      from Lam(1-3,5-13,15) show "Lam ya eV' = Lam y ((x \<leftrightarrow> x') \<bullet> eV)"
        unfolding trans[OF eq_sym_conv Abs1_eq_iff(3)]
        by (simp add: flip_commute fresh_at_base)
      from Lam(1-3,5-13,15) show "Rec x (Lam y eP) = Rec x' (Lam y ((x \<leftrightarrow> x') \<bullet> eP))"
        using Abs_lst_eq_flipI[of x' "Lam y eP" x]
        by (elim agree_fresh_env_fresh_term[where a = x', elim_format])
          (simp_all add: fresh_fmap_update fresh_Pair)
      from Lam(7,10) show "atom y \<sharp> (\<Gamma>, x')"
        by simp
      with Lam(1-2,7,9,11-12,15) show "\<Gamma>(x' $$:= Fun \<tau>\<^sub>1 \<tau>\<^sub>2) \<turnstile>
        Lam y ((x \<leftrightarrow> x') \<bullet> e), Lam y ((x \<leftrightarrow> x') \<bullet> eP), Lam y ((x \<leftrightarrow> x') \<bullet> eV) : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
        by (elim agree.eqvt[of _ "Lam y _" _ _ _ "(x' \<leftrightarrow> x)", elim_format])
          (simp add:  perm_supp_eq flip_commute)
    qed
  next
    case (Rec x1 x2a)
    from Rec(13) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Inj1 x)
    from Inj1(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Inj2 x)
    from Inj2(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Pair x1 x2a)
    from Pair(11) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Roll x)
    from Roll(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Let x1 x2a x3)
    from Let(14) show ?case by (simp add: Abs1_eq_iff)
  next
    case (App x1 x2a)
    from App(11) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Case x1 x2a x3)
    from Case(12) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Prj1 x)
    from Prj1(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Prj2 x)
    from Prj2(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Unroll x)
    from Unroll(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Auth x)
    from Auth(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Unauth x)
    from Unauth(10) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Hash x)
    from Hash(9) show ?case by (simp add: Abs1_eq_iff)
  next
    case (Hashed x1 x2a)
    from Hashed(10) show ?case by (simp add: Abs1_eq_iff)
  qed
qed

inductive_cases a_Inj1_inv_I[elim]: "\<Gamma> \<turnstile> Inj1 e, eP, eV : Sum \<tau>\<^sub>1 \<tau>\<^sub>2"
inductive_cases a_Inj1_inv_P[elim]: "\<Gamma> \<turnstile> e, Inj1 eP, eV : Sum \<tau>\<^sub>1 \<tau>\<^sub>2"
inductive_cases a_Inj1_inv_V[elim]: "\<Gamma> \<turnstile> e, eP, Inj1 eV : Sum \<tau>\<^sub>1 \<tau>\<^sub>2"

inductive_cases a_Inj2_inv_I[elim]: "\<Gamma> \<turnstile> Inj2 e, eP, eV : Sum \<tau>\<^sub>1 \<tau>\<^sub>2"
inductive_cases a_Inj2_inv_P[elim]: "\<Gamma> \<turnstile> e, Inj2 eP, eV : Sum \<tau>\<^sub>1 \<tau>\<^sub>2"
inductive_cases a_Inj2_inv_V[elim]: "\<Gamma> \<turnstile> e, eP, Inj2 eV : Sum \<tau>\<^sub>1 \<tau>\<^sub>2"

inductive_cases a_Pair_inv_I[elim]: "\<Gamma> \<turnstile> Pair e\<^sub>1 e\<^sub>2, eP, eV : Prod \<tau>\<^sub>1 \<tau>\<^sub>2"
inductive_cases a_Pair_inv_P[elim]: "\<Gamma> \<turnstile> e, Pair eP\<^sub>1 eP\<^sub>2, eV : Prod \<tau>\<^sub>1 \<tau>\<^sub>2"

lemma a_Roll_inv_I[elim]:
  assumes "\<Gamma> \<turnstile> Roll e', eP, eV : Mu \<alpha> \<tau>"
  obtains eP' eV'
  where "eP = Roll eP'" "eV = Roll eV'" "\<Gamma> \<turnstile> e', eP', eV' : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha>"
  using assms
  by (nominal_induct \<Gamma> "Roll e'" eP eV "Mu \<alpha> \<tau>" avoiding: \<alpha> \<tau> rule: agree.strong_induct)
     (simp add: Abs1_eq(3) Abs_lst_eq_flipI subst_type_perm_eq)

lemma a_Roll_inv_P[elim]:
  assumes "\<Gamma> \<turnstile> e, Roll eP', eV : Mu \<alpha> \<tau>"
  obtains e' eV'
  where "e = Roll e'" "eV = Roll eV'" "\<Gamma> \<turnstile> e', eP', eV' : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha>"
  using assms
  by (nominal_induct \<Gamma> e "Roll eP'" eV "Mu \<alpha> \<tau>" avoiding: \<alpha> \<tau> rule: agree.strong_induct)
     (simp add: Abs1_eq(3) Abs_lst_eq_flipI subst_type_perm_eq)

lemma a_Roll_inv_V[elim]:
  assumes "\<Gamma> \<turnstile> e, eP, Roll eV' : Mu \<alpha> \<tau>"
  obtains e' eP'
  where "e = Roll e'" "eP = Roll eP'" "\<Gamma> \<turnstile> e', eP', eV' : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha>"
  using assms
  by (nominal_induct \<Gamma> e eP "Roll eV'" "Mu \<alpha> \<tau>" avoiding: \<alpha> \<tau> rule: agree.strong_induct)
     (simp add: Abs1_eq(3) Abs_lst_eq_flipI subst_type_perm_eq)

inductive_cases a_HashI_inv[elim]: "\<Gamma> \<turnstile> v, Hashed (hash \<lparr>vP\<rparr>) vP, Hash (hash \<lparr>vP\<rparr>) : AuthT \<tau>"

text \<open>Inversion on types for agreement.\<close>

lemma a_AuthT_value_inv:
  assumes "{$$} \<turnstile> v, vP, vV : AuthT \<tau>"
  and     "value v" "value vP" "value vV"
  obtains vP' where "vP = Hashed (hash \<lparr>vP'\<rparr>) vP'" "vV = Hash (hash \<lparr>vP'\<rparr>)" "value vP'"
  using assms by (atomize_elim, induct "{$$}::tyenv" v vP vV "AuthT \<tau>" rule: agree.induct) simp_all

inductive_cases a_Mu_inv[elim]: "\<Gamma> \<turnstile> e, eP, eV : Mu \<alpha> \<tau>"
inductive_cases a_Sum_inv[elim]: "\<Gamma> \<turnstile> e, eP, eV : Sum \<tau>\<^sub>1 \<tau>\<^sub>2"
inductive_cases a_Prod_inv[elim]: "\<Gamma> \<turnstile> e, eP, eV : Prod \<tau>\<^sub>1 \<tau>\<^sub>2"
inductive_cases a_Fun_inv[elim]: "\<Gamma> \<turnstile> e, eP, eV : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"

declare [[simproc add: alpha_lst]]

lemma agree_weakening_1:
  assumes "\<Gamma> \<turnstile> e, eP, eV : \<tau>" "atom y \<sharp> e" "atom y \<sharp> eP" "atom y \<sharp> eV"
  shows   "\<Gamma>(y $$:= \<tau>') \<turnstile> e, eP, eV : \<tau>"
using assms proof (nominal_induct \<Gamma> e eP eV \<tau> avoiding: y \<tau>' rule: agree.strong_induct)
  case (a_Lam x \<Gamma> \<tau>\<^sub>1 e eP eV \<tau>\<^sub>2)
  then show ?case
    by (force simp add: fresh_at_base fresh_fmap_update fmupd_reorder_neq)
next
  case (a_App v\<^sub>1 v\<^sub>2 vP\<^sub>1 vP\<^sub>2 vV\<^sub>1 vV\<^sub>2 \<Gamma> \<tau>\<^sub>1 \<tau>\<^sub>2)
  then show ?case
    using term.fresh(9) by blast
next
  case (a_Let x \<Gamma> e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau>\<^sub>1 e\<^sub>2 eP\<^sub>2 eV\<^sub>2 \<tau>\<^sub>2)
  then show ?case
    by (auto simp add: fresh_at_base fresh_Pair fresh_fmap_update fmupd_reorder_neq[of x y]
      intro!: a_Let(10) agree.a_Let[of x])
next
  case (a_Rec x \<Gamma> z \<tau>\<^sub>1 \<tau>\<^sub>2 e eP eV)
  then show ?case
    by (auto simp add: fresh_at_base fresh_Pair fresh_fmap_update fmupd_reorder_neq[of x y]
      intro!: a_Rec(9) agree.a_Rec[of x])
next
  case (a_Case v v\<^sub>1 v\<^sub>2 vP vP\<^sub>1 vP\<^sub>2 vV vV\<^sub>1 vV\<^sub>2 \<Gamma> \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau>)
  then show ?case
    by (fastforce simp: fresh_at_base)
next
  case (a_Prj1 v vP vV \<Gamma> \<tau>\<^sub>1 \<tau>\<^sub>2)
  then show ?case
    by (fastforce simp: fresh_at_base)
next
  case (a_Prj2 v vP vV \<Gamma> \<tau>\<^sub>1 \<tau>\<^sub>2)
  then show ?case
    by (fastforce simp: fresh_at_base)
qed (auto simp: fresh_fmap_update)

lemma agree_weakening_2:
  assumes "\<Gamma> \<turnstile> e, eP, eV : \<tau>" "atom y \<sharp> \<Gamma>"
  shows   "\<Gamma>(y $$:= \<tau>') \<turnstile> e, eP, eV : \<tau>"
proof -
  from assms have "{atom y} \<sharp>* {e, eP, eV}" by (auto simp: fresh_Pair dest: agree_fresh_env_fresh_term)
  with assms show "\<Gamma>(y $$:= \<tau>') \<turnstile> e, eP, eV : \<tau>" by (simp add: agree_weakening_1)
qed

lemma agree_weakening_env:
  assumes "{$$} \<turnstile> e, eP, eV : \<tau>"
  shows   "\<Gamma> \<turnstile> e, eP, eV : \<tau>"
using assms proof (induct \<Gamma>)
  case fmempty
  then show ?case by assumption
next
  case (fmupd x y \<Gamma>)
  then show ?case
    by (simp add: fresh_tyenv_None agree_weakening_2)
qed

(*<*)
end
(*>*)