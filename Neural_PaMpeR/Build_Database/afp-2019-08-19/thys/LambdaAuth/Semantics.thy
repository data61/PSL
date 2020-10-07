(* Author: Matthias Brun,   ETH Zürich, 2019 *)
(* Author: Dmitriy Traytel, ETH Zürich, 2019 *)

section \<open>Semantics of $\lambda\bullet$\<close>

(*<*)
theory Semantics
  imports FMap_Lemmas Syntax
begin
(*>*)

text \<open>Avoid clash with substitution notation.\<close>
no_notation inverse_divide (infixl "'/" 70)

text \<open>Help automated provers with smallsteps.\<close>
declare One_nat_def[simp del]

subsection \<open>Equivariant Hash Function\<close>

consts hash_real :: "term \<Rightarrow> hash"

nominal_function map_fixed :: "var \<Rightarrow> var list \<Rightarrow> term \<Rightarrow> term" where
  "map_fixed fp l Unit = Unit" |
  "map_fixed fp l (Var y) = (if y \<in> set l then (Var y) else (Var fp))" |
  "atom y \<sharp> (fp, l) \<Longrightarrow> map_fixed fp l (Lam y t) = (Lam y ((map_fixed fp (y # l) t)))" |
  "atom y \<sharp> (fp, l) \<Longrightarrow> map_fixed fp l (Rec y t) = (Rec y ((map_fixed fp (y # l) t)))" |
  "map_fixed fp l (Inj1 t) = (Inj1 ((map_fixed fp l t)))" |
  "map_fixed fp l (Inj2 t) = (Inj2 ((map_fixed fp l t)))" |
  "map_fixed fp l (Pair t1 t2) = (Pair ((map_fixed fp l t1)) ((map_fixed fp l t2)))" |
  "map_fixed fp l (Roll t) = (Roll ((map_fixed fp l t)))" |
  "atom y \<sharp> (fp, l) \<Longrightarrow> map_fixed fp l (Let t1 y t2) = (Let ((map_fixed fp l t1)) y ((map_fixed fp (y # l) t2)))" |
  "map_fixed fp l (App t1 t2) = (App ((map_fixed fp l t1)) ((map_fixed fp l t2)))" |
  "map_fixed fp l (Case t1 t2 t3) = (Case ((map_fixed fp l t1)) ((map_fixed fp l t2)) ((map_fixed fp l t3)))" |
  "map_fixed fp l (Prj1 t) = (Prj1 ((map_fixed fp l t)))" |
  "map_fixed fp l (Prj2 t) = (Prj2 ((map_fixed fp l t)))" |
  "map_fixed fp l (Unroll t) = (Unroll ((map_fixed fp l t)))" |
  "map_fixed fp l (Auth t) = (Auth ((map_fixed fp l t)))" |
  "map_fixed fp l (Unauth t) = (Unauth ((map_fixed fp l t)))" |
  "map_fixed fp l (Hash h) = (Hash h)" |
  "map_fixed fp l (Hashed h t) = (Hashed h ((map_fixed fp l t)))"
  using [[simproc del: alpha_lst]]
  subgoal by (simp add: eqvt_def map_fixed_graph_aux_def)
  subgoal by (erule map_fixed_graph.induct) (auto simp: fresh_star_def fresh_at_base)
                      apply clarify
  subgoal for P fp l t
    by (rule term.strong_exhaust[of t P "(fp, l)"]) (auto simp: fresh_star_def fresh_Pair)
                      apply (simp_all add: fresh_star_def fresh_at_base)
  subgoal for y fp l t ya fpa la ta
    apply (erule conjE)+
    apply (erule Abs_lst1_fcb2'[where c = "(fp, l)"])
       apply (simp_all add: eqvt_at_def)
       apply (simp_all add: perm_supp_eq Abs_fresh_iff fresh_Pair)
    done
  subgoal for y fp l t ya fpa la ta
    apply (erule conjE)+
    apply (erule Abs_lst1_fcb2'[where c = "(fp, l)"])
       apply (simp_all add: eqvt_at_def)
       apply (simp_all add: perm_supp_eq Abs_fresh_iff fresh_Pair)
    done
  subgoal for y fp l t ya fpa la ta
    apply (erule conjE)+
    apply (erule Abs_lst1_fcb2'[where c = "(fp, l)"])
       apply (simp_all add: eqvt_at_def)
       apply (simp_all add: perm_supp_eq Abs_fresh_iff fresh_Pair)
    done
  done
nominal_termination (eqvt)
  by lexicographic_order

definition hash where
  "hash t = hash_real (map_fixed undefined [] t)"

lemma permute_map_list: "p \<bullet> l = map (\<lambda>x. p \<bullet> x) l"
  by (induct l) auto

lemma map_fixed_eqvt: "p \<bullet> l = l \<Longrightarrow> map_fixed v l (p \<bullet> t) = map_fixed v l t"
proof (nominal_induct t avoiding: v l p rule: term.strong_induct)
  case (Var x)
  then show ?case
    by (auto simp: term.supp supp_at_base permute_map_list list_eq_iff_nth_eq in_set_conv_nth)
next
  case (Lam y e)
  from Lam(1,2,3,5) Lam(4)[of p "y # l" v] show ?case
    by (auto simp: fresh_perm)
next
  case (Rec y e)
  from Rec(1,2,3,5) Rec(4)[of p "y # l" v] show ?case
    by (auto simp: fresh_perm)
next
  case (Let e' y e)
  from Let(1,2,3,6) Let(4)[of p l v] Let(5)[of p "y # l" v] show ?case
    by (auto simp: fresh_perm)
qed (auto simp: permute_pure)

lemma hash_eqvt[eqvt]: "p \<bullet> hash t = hash (p \<bullet> t)"
  unfolding permute_pure hash_def by (auto simp: map_fixed_eqvt)

lemma map_fixed_idle: "{x. \<not> atom x \<sharp> t} \<subseteq> set l \<Longrightarrow> map_fixed v l t = t"
proof (nominal_induct t avoiding: v l rule: term.strong_induct)
  case (Var x)
  then show ?case
    by (auto simp: subset_iff fresh_at_base)
next
  case (Lam y e)
  from Lam(1,2,4) Lam(3)[of "y # l" v] show ?case
    by (auto simp: fresh_Pair Abs1_eq)
next
  case (Rec y e)
  from Rec(1,2,4) Rec(3)[of "y # l" v] show ?case
    by (auto simp: fresh_Pair Abs1_eq)
next
  case (Let e' y e)
  from Let(1,2,5) Let(3)[of l v] Let(4)[of "y # l" v] show ?case
    by (auto simp: fresh_Pair Abs1_eq)
qed (auto simp: subset_iff)

lemma map_fixed_inj_closed:
  "closed t \<Longrightarrow> closed u \<Longrightarrow> map_fixed undefined [] t = map_fixed undefined [] u \<Longrightarrow> t = u"
  by (erule box_equals[OF _ map_fixed_idle map_fixed_idle]) auto

subsection \<open>Substitution\<close>

nominal_function subst_term :: "term \<Rightarrow> term \<Rightarrow> var \<Rightarrow> term" ("_[_ '/ _]" [250, 200, 200] 250) where
  "Unit[t' / x] = Unit" |
  "(Var y)[t' / x] = (if x = y then t' else Var y)" |
  "atom y \<sharp> (x, t') \<Longrightarrow> (Lam y t)[t' / x] = Lam y (t[t' / x])" |
  "atom y \<sharp> (x, t') \<Longrightarrow> (Rec y t)[t' / x] = Rec y (t[t' / x])" |
  "(Inj1 t)[t' / x] = Inj1 (t[t' / x])" |
  "(Inj2 t)[t' / x] = Inj2 (t[t' / x])" |
  "(Pair t1 t2)[t' / x] = Pair (t1[t' / x]) (t2[t' / x]) " |
  "(Roll t)[t' / x] = Roll (t[t' / x])" |
  "atom y \<sharp> (x, t') \<Longrightarrow> (Let t1 y t2)[t' / x] = Let (t1[t' / x]) y (t2[t' / x])" |
  "(App t1 t2)[t' / x] = App (t1[t' / x]) (t2[t' / x])" |
  "(Case t1 t2 t3)[t' / x] = Case (t1[t' / x]) (t2[t' / x]) (t3[t' / x])" |
  "(Prj1 t)[t' / x] = Prj1 (t[t' / x])" |
  "(Prj2 t)[t' / x] = Prj2 (t[t' / x])" |
  "(Unroll t)[t' / x] = Unroll (t[t' / x])" |
  "(Auth t)[t' / x] = Auth (t[t' / x])" |
  "(Unauth t)[t' / x] = Unauth (t[t' / x])" |
  "(Hash h)[t' / x] = Hash h" |
  "(Hashed h t)[t' / x] = Hashed h (t[t' / x])"
  using [[simproc del: alpha_lst]]
  subgoal by (simp add: eqvt_def subst_term_graph_aux_def)
  subgoal by (erule subst_term_graph.induct) (auto simp: fresh_star_def fresh_at_base)
                      apply clarify
  subgoal for P a b t
    by (rule term.strong_exhaust[of a P "(b, t)"]) (auto simp: fresh_star_def fresh_Pair)
                      apply (simp_all add: fresh_star_def fresh_at_base)
  subgoal
    apply (erule conjE)
    apply (erule Abs_lst1_fcb2')
       apply (simp_all add: eqvt_at_def)
       apply (simp_all add: perm_supp_eq Abs_fresh_iff fresh_Pair)
    done
  subgoal
    apply (erule conjE)
    apply (erule Abs_lst1_fcb2')
       apply (simp_all add: eqvt_at_def)
       apply (simp_all add: perm_supp_eq Abs_fresh_iff fresh_Pair)
    done
  subgoal
    apply (erule conjE)
    apply (erule Abs_lst1_fcb2')
       apply (simp_all add: eqvt_at_def)
       apply (simp_all add: perm_supp_eq Abs_fresh_iff fresh_Pair)
    done
  done
nominal_termination (eqvt)
  by lexicographic_order

type_synonym tenv = "(var, term) fmap"

nominal_function psubst_term :: "term \<Rightarrow> tenv \<Rightarrow> term" where
  "psubst_term Unit f = Unit" |
  "psubst_term (Var y) f = (case f $$ y of Some t \<Rightarrow> t | None \<Rightarrow> Var y)" |
  "atom y \<sharp> f \<Longrightarrow> psubst_term (Lam y t) f = Lam y (psubst_term t f)" |
  "atom y \<sharp> f \<Longrightarrow> psubst_term (Rec y t) f = Rec y (psubst_term t f)" |
  "psubst_term (Inj1 t) f = Inj1 (psubst_term t f)" |
  "psubst_term (Inj2 t) f = Inj2 (psubst_term t f)" |
  "psubst_term (Pair t1 t2) f = Pair (psubst_term t1 f) (psubst_term t2 f) " |
  "psubst_term (Roll t) f = Roll (psubst_term t f)" |
  "atom y \<sharp> f \<Longrightarrow> psubst_term (Let t1 y t2) f = Let (psubst_term t1 f) y (psubst_term t2 f)" |
  "psubst_term (App t1 t2) f = App (psubst_term t1 f) (psubst_term t2 f)" |
  "psubst_term (Case t1 t2 t3) f = Case (psubst_term t1 f) (psubst_term t2 f) (psubst_term t3 f)" |
  "psubst_term (Prj1 t) f = Prj1 (psubst_term t f)" |
  "psubst_term (Prj2 t) f = Prj2 (psubst_term t f)" |
  "psubst_term (Unroll t) f = Unroll (psubst_term t f)" |
  "psubst_term (Auth t) f = Auth (psubst_term t f)" |
  "psubst_term (Unauth t) f = Unauth (psubst_term t f)" |
  "psubst_term (Hash h) f = Hash h" |
  "psubst_term (Hashed h t) f = Hashed h (psubst_term t f)"
  using [[simproc del: alpha_lst]]
  subgoal by (simp add: eqvt_def psubst_term_graph_aux_def)
  subgoal by (erule psubst_term_graph.induct) (auto simp: fresh_star_def fresh_at_base)
  apply clarify
  subgoal for P a b
    by (rule term.strong_exhaust[of a P b]) (auto simp: fresh_star_def fresh_Pair)
                      apply (simp_all add: fresh_star_def fresh_at_base)
  subgoal by clarify
  subgoal
    apply (erule conjE)
    apply (erule Abs_lst1_fcb2')
       apply (simp_all add: eqvt_at_def)
      apply (simp_all add: perm_supp_eq Abs_fresh_iff)
    done
  subgoal
    apply (erule conjE)
    apply (erule Abs_lst1_fcb2')
       apply (simp_all add: eqvt_at_def)
      apply (simp_all add: perm_supp_eq Abs_fresh_iff)
    done
  subgoal
    apply (erule conjE)
    apply (erule Abs_lst1_fcb2')
       apply (simp_all add: eqvt_at_def)
      apply (simp_all add: perm_supp_eq Abs_fresh_iff)
    done
  done
nominal_termination (eqvt)
  by lexicographic_order

nominal_function subst_type :: "ty \<Rightarrow> ty \<Rightarrow> tvar \<Rightarrow> ty" where
  "subst_type One t' x = One" |
  "subst_type (Fun t1 t2) t' x = Fun (subst_type t1 t' x) (subst_type t2 t' x)" |
  "subst_type (Sum t1 t2) t' x = Sum (subst_type t1 t' x) (subst_type t2 t' x)" |
  "subst_type (Prod t1 t2) t' x = Prod (subst_type t1 t' x) (subst_type t2 t' x)" |
  "atom y \<sharp> (t', x) \<Longrightarrow> subst_type (Mu y t) t' x = Mu y (subst_type t t' x)" |
  "subst_type (Alpha y) t' x = (if y = x then t' else Alpha y)" |
  "subst_type (AuthT t) t' x = AuthT (subst_type t t' x)"
  using [[simproc del: alpha_lst]]
  subgoal by (simp add: eqvt_def subst_type_graph_aux_def)
  subgoal by (erule subst_type_graph.induct) (auto simp: fresh_star_def fresh_at_base)
  apply clarify
  subgoal for P a
    by (rule ty.strong_exhaust[of a P]) (auto simp: fresh_star_def)
                      apply (simp_all add: fresh_star_def fresh_at_base)
  subgoal
    apply (erule conjE)
    apply (erule Abs_lst1_fcb2')
       apply (simp_all add: eqvt_at_def)
      apply (simp_all add: perm_supp_eq Abs_fresh_iff fresh_Pair)
    done
  done
nominal_termination (eqvt)
  by lexicographic_order

lemma fresh_subst_term: "atom x \<sharp> t[t' / x'] \<longleftrightarrow> (x = x' \<or> atom x \<sharp> t) \<and> (atom x' \<sharp> t \<or> atom x \<sharp> t')"
  by (nominal_induct t avoiding: t' x x' rule: term.strong_induct) (auto simp add: fresh_at_base)

lemma term_fresh_subst[simp]: "atom x \<sharp> t \<Longrightarrow> atom x \<sharp> s \<Longrightarrow> (atom (x::var)) \<sharp> t[s / y]"
  by (nominal_induct t avoiding: s y rule: term.strong_induct) (auto)

lemma term_subst_idle[simp]: "atom y \<sharp> t \<Longrightarrow> t[s / y] = t"
  by (nominal_induct t avoiding: s y rule: term.strong_induct) (auto simp: fresh_Pair fresh_at_base)

lemma term_subst_subst: "atom y1 \<noteq> atom y2 \<Longrightarrow> atom y1 \<sharp> s2 \<Longrightarrow> t[s1 / y1][s2 / y2] = t[s2 / y2][s1[s2 / y2] / y1]"
  by (nominal_induct t avoiding: y1 y2 s1 s2 rule: term.strong_induct) auto

lemma fresh_psubst:
  fixes x :: var
  assumes "atom x \<sharp> e" "atom x \<sharp> vs"
  shows   "atom x \<sharp> psubst_term e vs"
  using assms
  by (induct e vs rule: psubst_term.induct)
    (auto simp: fresh_at_base elim: fresh_fmap_fresh_Some split: option.splits)

lemma fresh_subst_type:
  "atom \<alpha> \<sharp> subst_type \<tau> \<tau>' \<alpha>' \<longleftrightarrow> ((\<alpha> = \<alpha>' \<or> atom \<alpha> \<sharp> \<tau>) \<and> (atom \<alpha>' \<sharp> \<tau> \<or> atom \<alpha> \<sharp> \<tau>'))"
  by (nominal_induct \<tau> avoiding: \<alpha> \<alpha>' \<tau>' rule: ty.strong_induct) (auto simp add: fresh_at_base)

lemma type_fresh_subst[simp]: "atom x \<sharp> t \<Longrightarrow> atom x \<sharp> s \<Longrightarrow> (atom (x::tvar)) \<sharp> subst_type t s y"
  by (nominal_induct t avoiding: s y rule: ty.strong_induct) (auto)

lemma type_subst_idle[simp]: "atom y \<sharp> t \<Longrightarrow> subst_type t s y = t"
  by (nominal_induct t avoiding: s y rule: ty.strong_induct) (auto simp: fresh_Pair fresh_at_base)

lemma type_subst_subst: "atom y1 \<noteq> atom y2 \<Longrightarrow> atom y1 \<sharp> s2 \<Longrightarrow> 
  subst_type (subst_type t s1 y1) s2 y2 = subst_type (subst_type t s2 y2) (subst_type s1 s2 y2) y1"
  by (nominal_induct t avoiding: y1 y2 s1 s2 rule: ty.strong_induct) auto

subsection \<open>Weak Typing Judgement\<close>

type_synonym tyenv = "(var, ty) fmap"

inductive judge_weak :: "tyenv \<Rightarrow> term \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile>\<^sub>W _ : _" [150,0,150] 149) where
  jw_Unit:   "\<Gamma> \<turnstile>\<^sub>W Unit : One" |
  jw_Var:    "\<lbrakk> \<Gamma> $$ x = Some \<tau> \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Var x : \<tau>" |
  jw_Lam:    "\<lbrakk> atom x \<sharp> \<Gamma>; \<Gamma>(x $$:= \<tau>\<^sub>1) \<turnstile>\<^sub>W e : \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Lam x e : Fun \<tau>\<^sub>1 \<tau>\<^sub>2" |
  jw_App:    "\<lbrakk> \<Gamma> \<turnstile>\<^sub>W e : Fun \<tau>\<^sub>1 \<tau>\<^sub>2; \<Gamma> \<turnstile>\<^sub>W e' : \<tau>\<^sub>1 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W App e e' : \<tau>\<^sub>2" |
  jw_Let:    "\<lbrakk> atom x \<sharp> (\<Gamma>, e\<^sub>1); \<Gamma> \<turnstile>\<^sub>W e\<^sub>1 : \<tau>\<^sub>1; \<Gamma>(x $$:= \<tau>\<^sub>1) \<turnstile>\<^sub>W e\<^sub>2 : \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Let e\<^sub>1 x e\<^sub>2 : \<tau>\<^sub>2" |
  jw_Rec:    "\<lbrakk> atom x \<sharp> \<Gamma>; atom y \<sharp> (\<Gamma>,x); \<Gamma>(x $$:= Fun \<tau>\<^sub>1 \<tau>\<^sub>2) \<turnstile>\<^sub>W Lam y e : Fun \<tau>\<^sub>1 \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Rec x (Lam y e) : Fun \<tau>\<^sub>1 \<tau>\<^sub>2" |
  jw_Inj1:   "\<lbrakk> \<Gamma> \<turnstile>\<^sub>W e : \<tau>\<^sub>1 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Inj1 e : Sum \<tau>\<^sub>1 \<tau>\<^sub>2" |
  jw_Inj2:   "\<lbrakk> \<Gamma> \<turnstile>\<^sub>W e : \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Inj2 e : Sum \<tau>\<^sub>1 \<tau>\<^sub>2" |
  jw_Case:   "\<lbrakk> \<Gamma> \<turnstile>\<^sub>W e : Sum \<tau>\<^sub>1 \<tau>\<^sub>2; \<Gamma> \<turnstile>\<^sub>W e\<^sub>1 : Fun \<tau>\<^sub>1 \<tau>; \<Gamma> \<turnstile>\<^sub>W e\<^sub>2 : Fun \<tau>\<^sub>2 \<tau> \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Case e e\<^sub>1 e\<^sub>2 : \<tau>" |
  jw_Pair:   "\<lbrakk> \<Gamma> \<turnstile>\<^sub>W e\<^sub>1 : \<tau>\<^sub>1; \<Gamma> \<turnstile>\<^sub>W e\<^sub>2 : \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Pair e\<^sub>1 e\<^sub>2 : Prod \<tau>\<^sub>1 \<tau>\<^sub>2" |
  jw_Prj1:   "\<lbrakk> \<Gamma> \<turnstile>\<^sub>W e : Prod \<tau>\<^sub>1 \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Prj1 e : \<tau>\<^sub>1" |
  jw_Prj2:   "\<lbrakk> \<Gamma> \<turnstile>\<^sub>W e : Prod \<tau>\<^sub>1 \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Prj2 e : \<tau>\<^sub>2" |
  jw_Roll:   "\<lbrakk> atom \<alpha> \<sharp> \<Gamma>; \<Gamma> \<turnstile>\<^sub>W e : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha> \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Roll e : Mu \<alpha> \<tau>" |
  jw_Unroll: "\<lbrakk> atom \<alpha> \<sharp> \<Gamma>; \<Gamma> \<turnstile>\<^sub>W e : Mu \<alpha> \<tau> \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Unroll e : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha>" |
  jw_Auth:   "\<lbrakk> \<Gamma> \<turnstile>\<^sub>W e : \<tau> \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Auth e : \<tau>" |
  jw_Unauth: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>W e : \<tau> \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>W Unauth e : \<tau>"

declare judge_weak.intros[simp]
declare judge_weak.intros[intro]

equivariance judge_weak
nominal_inductive judge_weak
  avoids jw_Lam: x
       | jw_Rec: x and y
       | jw_Let: x
       | jw_Roll: \<alpha>
       | jw_Unroll: \<alpha>
  by (auto simp: fresh_subst_type fresh_Pair)

text \<open>Inversion rules for typing judgment.\<close>

inductive_cases jw_Unit_inv[elim]: "\<Gamma> \<turnstile>\<^sub>W Unit : \<tau>"
inductive_cases jw_Var_inv[elim]: "\<Gamma> \<turnstile>\<^sub>W Var x : \<tau>"

lemma jw_Lam_inv[elim]:
  assumes "\<Gamma> \<turnstile>\<^sub>W Lam x e : \<tau>"
  and     "atom x \<sharp> \<Gamma>"
  obtains \<tau>\<^sub>1 \<tau>\<^sub>2 where "\<tau> = Fun \<tau>\<^sub>1 \<tau>\<^sub>2" "(\<Gamma>(x $$:= \<tau>\<^sub>1)) \<turnstile>\<^sub>W e : \<tau>\<^sub>2"
  using assms proof (atomize_elim, nominal_induct \<Gamma> "Lam x e" \<tau> avoiding: x e rule: judge_weak.strong_induct)
  case (jw_Lam x \<Gamma> \<tau>\<^sub>1 t \<tau>\<^sub>2 y u)
  then show ?case
    by (auto simp: perm_supp_eq elim!:
        iffD1[OF Abs_lst1_fcb2'[where f = "\<lambda>x t (\<Gamma>, \<tau>\<^sub>1, \<tau>\<^sub>2). (\<Gamma>(x $$:= \<tau>\<^sub>1)) \<turnstile>\<^sub>W t : \<tau>\<^sub>2"
        and c = "(\<Gamma>, \<tau>\<^sub>1, \<tau>\<^sub>2)" and a = x and b = y and x = t and y = u, unfolded prod.case],
        rotated -1])
qed

lemma swap_permute_swap: "atom x \<sharp> \<pi> \<Longrightarrow> atom y \<sharp> \<pi> \<Longrightarrow> (x \<leftrightarrow> y) \<bullet> \<pi> \<bullet> (x \<leftrightarrow> y) \<bullet> t = \<pi> \<bullet> t"
  by (subst permute_eqvt) (auto simp: flip_fresh_fresh)

lemma jw_Rec_inv[elim]:
  assumes "\<Gamma> \<turnstile>\<^sub>W Rec x t : \<tau>"
  and     "atom x \<sharp> \<Gamma>"
  obtains y e \<tau>\<^sub>1 \<tau>\<^sub>2 where "atom y \<sharp> (\<Gamma>,x)" "t = Lam y e" "\<tau> = Fun \<tau>\<^sub>1 \<tau>\<^sub>2" "\<Gamma>(x $$:= Fun \<tau>\<^sub>1 \<tau>\<^sub>2) \<turnstile>\<^sub>W Lam y e : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
  using [[simproc del: alpha_lst]] assms
proof (atomize_elim, nominal_induct \<Gamma> "Rec x t" \<tau> avoiding: x t rule: judge_weak.strong_induct)
  case (jw_Rec x \<Gamma> y \<tau>\<^sub>1 \<tau>\<^sub>2 e z t)
  then show ?case
  proof (nominal_induct t avoiding: y x z rule: term.strong_induct)
    case (Lam y' e')
    show ?case
    proof (intro exI conjI)
      from Lam.prems show "atom y \<sharp> (\<Gamma>, z)" by simp
      from Lam.hyps(1-3) Lam.prems show "Lam y' e' = Lam y ((y' \<leftrightarrow> y) \<bullet> e')"
        by (subst term.eq_iff(3), intro Abs_lst_eq_flipI) (simp add: fresh_at_base)
      from Lam.hyps(1-3) Lam.prems show "\<Gamma>(z $$:= Fun \<tau>\<^sub>1 \<tau>\<^sub>2) \<turnstile>\<^sub>W Lam y ((y' \<leftrightarrow> y) \<bullet> e') : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
        by (elim judge_weak.eqvt[of "\<Gamma>(x $$:= Fun \<tau>\<^sub>1 \<tau>\<^sub>2)" "Lam y e" "Fun \<tau>\<^sub>1 \<tau>\<^sub>2" "(x \<leftrightarrow> z)", elim_format])
          (simp add: perm_supp_eq Abs1_eq_iff fresh_at_base swap_permute_swap fresh_perm flip_commute)
    qed simp
  qed (simp_all add: Abs1_eq_iff)
qed

inductive_cases jw_Inj1_inv[elim]: "\<Gamma> \<turnstile>\<^sub>W Inj1 e : \<tau>"
inductive_cases jw_Inj2_inv[elim]: "\<Gamma> \<turnstile>\<^sub>W Inj2 e : \<tau>"
inductive_cases jw_Pair_inv[elim]: "\<Gamma> \<turnstile>\<^sub>W Pair e\<^sub>1 e\<^sub>2 : \<tau>"

lemma jw_Let_inv[elim]:
  assumes "\<Gamma> \<turnstile>\<^sub>W Let e\<^sub>1 x e\<^sub>2 : \<tau>\<^sub>2"
  and     "atom x \<sharp> (e\<^sub>1, \<Gamma>)"
  obtains \<tau>\<^sub>1 where "\<Gamma> \<turnstile>\<^sub>W e\<^sub>1 : \<tau>\<^sub>1" "\<Gamma>(x $$:= \<tau>\<^sub>1) \<turnstile>\<^sub>W e\<^sub>2 : \<tau>\<^sub>2"
using assms proof (atomize_elim, nominal_induct \<Gamma> "Let e\<^sub>1 x e\<^sub>2" \<tau>\<^sub>2 avoiding: e\<^sub>1 x e\<^sub>2 rule: judge_weak.strong_induct)
  case (jw_Let x \<Gamma> e\<^sub>1 \<tau>\<^sub>1 e\<^sub>2 \<tau>\<^sub>2 x' e\<^sub>2')
  then show ?case
    by (auto simp: fresh_Pair perm_supp_eq elim!:
        iffD1[OF Abs_lst1_fcb2'[where f = "\<lambda>x t (\<Gamma>, \<tau>\<^sub>1, \<tau>\<^sub>2). \<Gamma>(x $$:= \<tau>\<^sub>1) \<turnstile>\<^sub>W t : \<tau>\<^sub>2"
        and c = "(\<Gamma>, \<tau>\<^sub>1, \<tau>\<^sub>2)" and a = x and b = x' and x = e\<^sub>2 and y = e\<^sub>2', unfolded prod.case],
        rotated -1])
qed

inductive_cases jw_Prj1_inv[elim]: "\<Gamma> \<turnstile>\<^sub>W Prj1 e : \<tau>\<^sub>1"
inductive_cases jw_Prj2_inv[elim]: "\<Gamma> \<turnstile>\<^sub>W Prj2 e : \<tau>\<^sub>2"
inductive_cases jw_App_inv[elim]: "\<Gamma> \<turnstile>\<^sub>W App e e' : \<tau>\<^sub>2"
inductive_cases jw_Case_inv[elim]: "\<Gamma> \<turnstile>\<^sub>W Case e e\<^sub>1 e\<^sub>2 : \<tau>"
inductive_cases jw_Auth_inv[elim]: "\<Gamma> \<turnstile>\<^sub>W Auth e : \<tau>"
inductive_cases jw_Unauth_inv[elim]: "\<Gamma> \<turnstile>\<^sub>W Unauth e : \<tau>"

lemma subst_type_perm_eq:
  assumes "atom b \<sharp> t"
  shows   "subst_type t (Mu a t) a = subst_type ((a \<leftrightarrow> b) \<bullet> t) (Mu b ((a \<leftrightarrow> b) \<bullet> t)) b"
  using assms proof -
  have f: "atom a \<sharp> subst_type t (Mu a t) a" by (rule iffD2[OF fresh_subst_type]) simp
  have    "atom b \<sharp> subst_type t (Mu a t) a" by (auto simp: assms)
  with f have "subst_type t (Mu a t) a = (a \<leftrightarrow> b) \<bullet> subst_type t (Mu a t) a"
    by (simp add: flip_fresh_fresh)
  then show "subst_type t (Mu a t) a  = subst_type ((a \<leftrightarrow> b) \<bullet> t) (Mu b ((a \<leftrightarrow> b) \<bullet> t)) b"
    by simp
qed

lemma jw_Roll_inv[elim]:
  assumes "\<Gamma> \<turnstile>\<^sub>W Roll e : \<tau>"
  and     "atom \<alpha> \<sharp> (\<Gamma>, \<tau>)"
  obtains \<tau>' where "\<tau> = Mu \<alpha> \<tau>'" "\<Gamma> \<turnstile>\<^sub>W e : subst_type \<tau>' (Mu \<alpha> \<tau>') \<alpha>"
  using assms [[simproc del: alpha_lst]]
  proof (atomize_elim, nominal_induct \<Gamma> "Roll e" \<tau> avoiding: e \<alpha> rule: judge_weak.strong_induct)
  case (jw_Roll \<alpha> \<Gamma> e \<tau> \<alpha>')
  then show ?case
    by (auto simp: perm_supp_eq fresh_Pair fresh_at_base subst_type.eqvt
      intro!: exI[of _ "(\<alpha> \<leftrightarrow> \<alpha>') \<bullet> \<tau>"] Abs_lst_eq_flipI dest: judge_weak.eqvt[of _ _ _ "(\<alpha> \<leftrightarrow> \<alpha>')"])
qed

lemma jw_Unroll_inv[elim]:
  assumes "\<Gamma> \<turnstile>\<^sub>W Unroll e : \<tau>"
  and     "atom \<alpha> \<sharp> (\<Gamma>, \<tau>)"
  obtains \<tau>' where "\<tau> = subst_type \<tau>' (Mu \<alpha> \<tau>') \<alpha>" "\<Gamma> \<turnstile>\<^sub>W e : Mu \<alpha> \<tau>'"
  using assms proof (atomize_elim, nominal_induct \<Gamma> "Unroll e" \<tau> avoiding: e \<alpha> rule: judge_weak.strong_induct)
  case (jw_Unroll \<alpha> \<Gamma> e \<tau> \<alpha>')
  then show ?case
    by (auto simp: perm_supp_eq fresh_Pair subst_type_perm_eq fresh_subst_type
      intro!: exI[of _ "(\<alpha> \<leftrightarrow> \<alpha>') \<bullet> \<tau>"] dest: judge_weak.eqvt[of _ _ _ "(\<alpha> \<leftrightarrow> \<alpha>')"])
qed

text \<open>Additional inversion rules based on type rather than term.\<close>

inductive_cases jw_Prod_inv[elim]: "{$$} \<turnstile>\<^sub>W e : Prod \<tau>\<^sub>1 \<tau>\<^sub>2"
inductive_cases jw_Sum_inv[elim]: "{$$} \<turnstile>\<^sub>W e : Sum \<tau>\<^sub>1 \<tau>\<^sub>2"

lemma jw_Fun_inv[elim]:
  assumes "{$$} \<turnstile>\<^sub>W v : Fun \<tau>\<^sub>1 \<tau>\<^sub>2" "value v"
  obtains e x where "v = Lam x e \<or> v = Rec x e" "atom x \<sharp> (c::term)"
  using assms [[simproc del: alpha_lst]]
proof (atomize_elim, nominal_induct "{$$} :: tyenv" v "Fun \<tau>\<^sub>1 \<tau>\<^sub>2" avoiding: \<tau>\<^sub>1 \<tau>\<^sub>2 rule: judge_weak.strong_induct)
  case (jw_Lam x \<tau>\<^sub>1 e \<tau>\<^sub>2)
  then obtain x' where "atom (x'::var) \<sharp> (c, e)" using finite_supp obtain_fresh' by blast
  then have "[[atom x]]lst. e = [[atom x']]lst. (x \<leftrightarrow> x') \<bullet> e \<and> atom x' \<sharp> c"
    by (simp add: Abs_lst_eq_flipI fresh_Pair)
  then show ?case
    by auto
next
  case (jw_Rec x y \<tau>\<^sub>1 \<tau>\<^sub>2 e')
  obtain x' where "atom (x'::var) \<sharp> (c, Lam y e')" using finite_supp obtain_fresh by blast
  then have "[[atom x]]lst. Lam y e' = [[atom x']]lst. (x \<leftrightarrow> x') \<bullet> (Lam y e') \<and> atom x' \<sharp> c"
    using Abs_lst_eq_flipI fresh_Pair by blast
  then show ?case
    by auto
qed simp_all

lemma jw_Mu_inv[elim]:
  assumes "{$$} \<turnstile>\<^sub>W v : Mu \<alpha> \<tau>" "value v"
  obtains v' where "v = Roll v'"
  using assms by (atomize_elim, nominal_induct "{$$} :: tyenv" v "Mu \<alpha> \<tau>" rule: judge_weak.strong_induct) simp_all


subsection \<open>Erasure of Authenticated Types\<close>

nominal_function erase :: "ty \<Rightarrow> ty" where
  "erase One = One" |
  "erase (Fun \<tau>\<^sub>1 \<tau>\<^sub>2) = Fun (erase \<tau>\<^sub>1) (erase \<tau>\<^sub>2)" |
  "erase (Sum \<tau>\<^sub>1 \<tau>\<^sub>2) = Sum (erase \<tau>\<^sub>1) (erase \<tau>\<^sub>2)" |
  "erase (Prod \<tau>\<^sub>1 \<tau>\<^sub>2) = Prod (erase \<tau>\<^sub>1) (erase \<tau>\<^sub>2)" |
  "erase (Mu \<alpha> \<tau>) = Mu \<alpha> (erase \<tau>)" |
  "erase (Alpha \<alpha>) = Alpha \<alpha>" |
  "erase (AuthT \<tau>) = erase \<tau>"
  using [[simproc del: alpha_lst]]
  subgoal by (simp add: eqvt_def erase_graph_aux_def)
  subgoal by (erule erase_graph.induct) (auto simp: fresh_star_def fresh_at_base)
  subgoal for P x
    by (rule ty.strong_exhaust[of x P x]) (auto simp: fresh_star_def)
                      apply (simp_all add: fresh_star_def fresh_at_base)
  subgoal
    apply (erule Abs_lst1_fcb2')
       apply (simp_all add: eqvt_at_def)
      apply (simp_all add: perm_supp_eq Abs_fresh_iff)
    done
  done
nominal_termination (eqvt)
  by lexicographic_order

lemma fresh_erase_fresh:
  assumes "atom x \<sharp> \<tau>"
  shows   "atom x \<sharp> erase \<tau>"
  using assms by (induct \<tau> rule: ty.induct) auto

lemma fresh_fmmap_erase_fresh:
  assumes "atom x \<sharp> \<Gamma>"
  shows   "atom x \<sharp> fmmap erase \<Gamma>"
  using assms by transfer simp

lemma erase_subst_type_shift[simp]:
  "erase (subst_type \<tau> \<tau>' \<alpha>) = subst_type (erase \<tau>) (erase \<tau>') \<alpha>"
  by (induct \<tau> \<tau>' \<alpha> rule: subst_type.induct) (auto simp: fresh_Pair fresh_erase_fresh)

definition erase_env :: "tyenv \<Rightarrow> tyenv" where
  "erase_env = fmmap erase"

subsection \<open>Strong Typing Judgement\<close>

inductive judge :: "tyenv \<Rightarrow> term \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ : _" [150,0,150] 149) where
  j_Unit:   "\<Gamma> \<turnstile> Unit : One" |
  j_Var:    "\<lbrakk> \<Gamma> $$ x = Some \<tau> \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Var x : \<tau>" |
  j_Lam:    "\<lbrakk> atom x \<sharp> \<Gamma>; \<Gamma>(x $$:= \<tau>\<^sub>1) \<turnstile> e : \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Lam x e : Fun \<tau>\<^sub>1 \<tau>\<^sub>2" |
  j_App:    "\<lbrakk> \<Gamma> \<turnstile> e : Fun \<tau>\<^sub>1 \<tau>\<^sub>2; \<Gamma> \<turnstile> e' : \<tau>\<^sub>1 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> App e e' : \<tau>\<^sub>2" |
  j_Let:    "\<lbrakk> atom x \<sharp> (\<Gamma>, e\<^sub>1); \<Gamma> \<turnstile> e\<^sub>1 : \<tau>\<^sub>1; \<Gamma>(x $$:= \<tau>\<^sub>1) \<turnstile> e\<^sub>2 : \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Let e\<^sub>1 x e\<^sub>2 : \<tau>\<^sub>2" |
  j_Rec:    "\<lbrakk> atom x \<sharp> \<Gamma>; atom y \<sharp> (\<Gamma>,x); \<Gamma>(x $$:= Fun \<tau>\<^sub>1 \<tau>\<^sub>2) \<turnstile> Lam y e' : Fun \<tau>\<^sub>1 \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Rec x (Lam y e') : Fun \<tau>\<^sub>1 \<tau>\<^sub>2" |
  j_Inj1:   "\<lbrakk> \<Gamma> \<turnstile> e : \<tau>\<^sub>1 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Inj1 e : Sum \<tau>\<^sub>1 \<tau>\<^sub>2" |
  j_Inj2:   "\<lbrakk> \<Gamma> \<turnstile> e : \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Inj2 e : Sum \<tau>\<^sub>1 \<tau>\<^sub>2" |
  j_Case:   "\<lbrakk> \<Gamma> \<turnstile> e : Sum \<tau>\<^sub>1 \<tau>\<^sub>2; \<Gamma> \<turnstile> e\<^sub>1 : Fun \<tau>\<^sub>1 \<tau>; \<Gamma> \<turnstile> e\<^sub>2 : Fun \<tau>\<^sub>2 \<tau> \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Case e e\<^sub>1 e\<^sub>2 : \<tau>" |
  j_Pair:   "\<lbrakk> \<Gamma> \<turnstile> e\<^sub>1 : \<tau>\<^sub>1; \<Gamma> \<turnstile> e\<^sub>2 : \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Pair e\<^sub>1 e\<^sub>2 : Prod \<tau>\<^sub>1 \<tau>\<^sub>2" |
  j_Prj1:   "\<lbrakk> \<Gamma> \<turnstile> e : Prod \<tau>\<^sub>1 \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Prj1 e : \<tau>\<^sub>1" |
  j_Prj2:   "\<lbrakk> \<Gamma> \<turnstile> e : Prod \<tau>\<^sub>1 \<tau>\<^sub>2 \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Prj2 e : \<tau>\<^sub>2" |
  j_Roll:   "\<lbrakk> atom \<alpha> \<sharp> \<Gamma>; \<Gamma> \<turnstile> e : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha> \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Roll e : Mu \<alpha> \<tau>" |
  j_Unroll: "\<lbrakk> atom \<alpha> \<sharp> \<Gamma>; \<Gamma> \<turnstile> e : Mu \<alpha> \<tau> \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Unroll e : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha>" |
  j_Auth:   "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Auth e : AuthT \<tau>" |
  j_Unauth: "\<lbrakk> \<Gamma> \<turnstile> e : AuthT \<tau> \<rbrakk>
           \<Longrightarrow> \<Gamma> \<turnstile> Unauth e : \<tau>"

declare judge.intros[intro]

equivariance judge
nominal_inductive judge
  avoids j_Lam: x
       | j_Rec: x and y
       | j_Let: x
       | j_Roll: \<alpha>
       | j_Unroll: \<alpha>
  by (auto simp: fresh_subst_type fresh_Pair)

lemma judge_imp_judge_weak:
  assumes "\<Gamma> \<turnstile> e : \<tau>"
  shows   "erase_env \<Gamma> \<turnstile>\<^sub>W e : erase \<tau>"
  using assms unfolding erase_env_def
  by (induct \<Gamma> e \<tau> rule: judge.induct) (simp_all add: fresh_Pair fresh_fmmap_erase_fresh fmmap_fmupd)

subsection \<open>Shallow Projection\<close>

nominal_function shallow :: "term \<Rightarrow> term" ("\<lparr>_\<rparr>") where
  "\<lparr>Unit\<rparr>  = Unit" |
  "\<lparr>Var v\<rparr> = Var v" |
  "\<lparr>Lam x e\<rparr> = Lam x \<lparr>e\<rparr>" |
  "\<lparr>Rec x e\<rparr> = Rec x \<lparr>e\<rparr>" |
  "\<lparr>Inj1 e\<rparr> = Inj1 \<lparr>e\<rparr>" |
  "\<lparr>Inj2 e\<rparr> = Inj2 \<lparr>e\<rparr>" |
  "\<lparr>Pair e\<^sub>1 e\<^sub>2\<rparr> = Pair \<lparr>e\<^sub>1\<rparr> \<lparr>e\<^sub>2\<rparr>" |
  "\<lparr>Roll e\<rparr> = Roll \<lparr>e\<rparr>" |
  "\<lparr>Let e\<^sub>1 x e\<^sub>2\<rparr> = Let \<lparr>e\<^sub>1\<rparr> x \<lparr>e\<^sub>2\<rparr>" |
  "\<lparr>App e\<^sub>1 e\<^sub>2\<rparr> = App \<lparr>e\<^sub>1\<rparr> \<lparr>e\<^sub>2\<rparr>" |
  "\<lparr>Case e e\<^sub>1 e\<^sub>2\<rparr> = Case \<lparr>e\<rparr> \<lparr>e\<^sub>1\<rparr> \<lparr>e\<^sub>2\<rparr>" |
  "\<lparr>Prj1 e\<rparr> = Prj1 \<lparr>e\<rparr>" |
  "\<lparr>Prj2 e\<rparr> = Prj2 \<lparr>e\<rparr>" |
  "\<lparr>Unroll e\<rparr> = Unroll \<lparr>e\<rparr>" |
  "\<lparr>Auth e\<rparr> = Auth \<lparr>e\<rparr>" |
  "\<lparr>Unauth e\<rparr> = Unauth \<lparr>e\<rparr>" |
  \<comment> \<open>No rule is defined for Hash, but: "[..] preserving that structure in every case but that of <h, v> [..]"\<close>
  "\<lparr>Hash h\<rparr> = Hash h" |
  "\<lparr>Hashed h e\<rparr> = Hash h"
  using [[simproc del: alpha_lst]]
  subgoal by (simp add: eqvt_def shallow_graph_aux_def)
  subgoal by (erule shallow_graph.induct) (auto simp: fresh_star_def fresh_at_base)
  subgoal for P a
    by (rule term.strong_exhaust[of a P a]) (auto simp: fresh_star_def)
                      apply (simp_all add: fresh_star_def fresh_at_base)
  subgoal
    apply (erule Abs_lst1_fcb2')
       apply (simp_all add: eqvt_at_def)
      apply (simp_all add: perm_supp_eq Abs_fresh_iff)
    done
  subgoal
    apply (erule Abs_lst1_fcb2')
       apply (simp_all add: eqvt_at_def)
      apply (simp_all add: perm_supp_eq Abs_fresh_iff)
    done
  subgoal
    apply (erule conjE)
    apply (erule Abs_lst1_fcb2')
       apply (simp_all add: eqvt_at_def)
      apply (simp_all add: perm_supp_eq Abs_fresh_iff)
    done
  done
nominal_termination (eqvt)
  by lexicographic_order

lemma fresh_shallow: "atom x \<sharp> e \<Longrightarrow> atom x \<sharp> \<lparr>e\<rparr>"
  by (induct e rule: term.induct) auto

subsection \<open>Small-step Semantics\<close>

datatype mode = I | P | V \<comment> \<open>Ideal, Prover and Verifier modes\<close>

instantiation mode :: pure
begin
definition permute_mode :: "perm \<Rightarrow> mode \<Rightarrow> mode" where
  "permute_mode \<pi> h = h"
instance proof qed (auto simp: permute_mode_def)
end

type_synonym proofstream = "term list"

inductive smallstep :: "proofstream \<Rightarrow> term \<Rightarrow> mode \<Rightarrow> proofstream \<Rightarrow> term \<Rightarrow> bool" ("\<lless>_, _\<ggreater> _\<rightarrow> \<lless>_, _\<ggreater>") where
  s_App1:      "\<lbrakk> \<lless> \<pi>, e\<^sub>1 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e\<^sub>1' \<ggreater> \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, App e\<^sub>1 e\<^sub>2 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', App e\<^sub>1' e\<^sub>2 \<ggreater>" |
  s_App2:      "\<lbrakk> value v\<^sub>1; \<lless> \<pi>, e\<^sub>2 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e\<^sub>2' \<ggreater> \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, App v\<^sub>1 e\<^sub>2 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', App v\<^sub>1 e\<^sub>2' \<ggreater>" |
  s_AppLam:    "\<lbrakk> value v; atom x \<sharp> (v,\<pi>) \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, App (Lam x e) v \<ggreater>  _\<rightarrow>  \<lless> \<pi>, e[v / x] \<ggreater>" |
  s_AppRec:    "\<lbrakk> value v; atom x \<sharp> (v,\<pi>) \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, App (Rec x e) v \<ggreater>  _\<rightarrow>  \<lless> \<pi>, App (e[(Rec x e) / x]) v \<ggreater>" |
  s_Let1:      "\<lbrakk> atom x \<sharp> (e\<^sub>1,e\<^sub>1',\<pi>,\<pi>'); \<lless> \<pi>, e\<^sub>1 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e\<^sub>1' \<ggreater> \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Let e\<^sub>1 x e\<^sub>2 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', Let e\<^sub>1' x e\<^sub>2 \<ggreater>" |
  s_Let2:      "\<lbrakk> value v; atom x \<sharp> (v,\<pi>) \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Let v x e \<ggreater>  _\<rightarrow>  \<lless> \<pi>, e[v / x] \<ggreater>" |
  s_Inj1:      "\<lbrakk> \<lless> \<pi>, e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e' \<ggreater> \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Inj1 e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', Inj1 e' \<ggreater>" |
  s_Inj2:      "\<lbrakk> \<lless> \<pi>, e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e' \<ggreater> \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Inj2 e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', Inj2 e' \<ggreater>" |
  s_Case:      "\<lbrakk> \<lless> \<pi>, e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e' \<ggreater> \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Case e e\<^sub>1 e\<^sub>2 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', Case e' e\<^sub>1 e\<^sub>2 \<ggreater>" |
  \<comment> \<open>Case rules are different from paper to account for recursive functions.\<close>
  s_CaseInj1:  "\<lbrakk> value v \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Case (Inj1 v) e\<^sub>1 e\<^sub>2 \<ggreater>  _\<rightarrow>  \<lless> \<pi>, App e\<^sub>1 v \<ggreater>" |
  s_CaseInj2:  "\<lbrakk> value v \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Case (Inj2 v) e\<^sub>1 e\<^sub>2 \<ggreater>  _\<rightarrow>  \<lless> \<pi>, App e\<^sub>2 v \<ggreater>" |
  s_Pair1:     "\<lbrakk> \<lless> \<pi>, e\<^sub>1 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e\<^sub>1' \<ggreater> \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Pair e\<^sub>1 e\<^sub>2 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', Pair e\<^sub>1' e\<^sub>2 \<ggreater>" |
  s_Pair2:     "\<lbrakk> value v\<^sub>1; \<lless> \<pi>, e\<^sub>2 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e\<^sub>2' \<ggreater> \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Pair v\<^sub>1 e\<^sub>2 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', Pair v\<^sub>1 e\<^sub>2' \<ggreater>" |
  s_Prj1:      "\<lbrakk> \<lless> \<pi>, e \<ggreater> m\<rightarrow> \<lless> \<pi>', e' \<ggreater> \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Prj1 e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', Prj1 e' \<ggreater>" |
  s_Prj2:      "\<lbrakk> \<lless> \<pi>, e \<ggreater> m\<rightarrow> \<lless> \<pi>', e' \<ggreater> \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Prj2 e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', Prj2 e' \<ggreater>" |
  s_PrjPair1:  "\<lbrakk> value v\<^sub>1; value v\<^sub>2 \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Prj1 (Pair v\<^sub>1 v\<^sub>2) \<ggreater>  _\<rightarrow>  \<lless> \<pi>, v\<^sub>1 \<ggreater>" |
  s_PrjPair2:  "\<lbrakk> value v\<^sub>1; value v\<^sub>2 \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Prj2 (Pair v\<^sub>1 v\<^sub>2) \<ggreater>  _\<rightarrow>  \<lless> \<pi>, v\<^sub>2 \<ggreater>" |
  s_Unroll:    "\<lless> \<pi>, e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e' \<ggreater>
              \<Longrightarrow> \<lless> \<pi>, Unroll e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', Unroll e' \<ggreater>" |
  s_Roll:      "\<lless> \<pi>, e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e' \<ggreater>
              \<Longrightarrow> \<lless> \<pi>, Roll e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', Roll e' \<ggreater>" |
  s_UnrollRoll:"\<lbrakk> value v \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Unroll (Roll v) \<ggreater>  _\<rightarrow>  \<lless> \<pi>, v \<ggreater>" |
  \<comment> \<open>Mode-specific rules\<close>
  s_Auth:      "\<lless> \<pi>, e \<ggreater> m\<rightarrow> \<lless> \<pi>', e' \<ggreater>
              \<Longrightarrow> \<lless> \<pi>, Auth e \<ggreater> m\<rightarrow> \<lless> \<pi>', Auth e' \<ggreater>" |
  s_Unauth:    "\<lless> \<pi>, e \<ggreater> m\<rightarrow> \<lless> \<pi>', e' \<ggreater>
              \<Longrightarrow> \<lless> \<pi>, Unauth e \<ggreater> m\<rightarrow> \<lless> \<pi>', Unauth e' \<ggreater>" |
  s_AuthI:     "\<lbrakk> value v \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Auth v \<ggreater> I\<rightarrow> \<lless> \<pi>, v \<ggreater>" |
  s_UnauthI:   "\<lbrakk> value v \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Unauth v \<ggreater> I\<rightarrow> \<lless> \<pi>, v \<ggreater>" |
  s_AuthP:     "\<lbrakk> closed \<lparr>v\<rparr>; value v \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Auth v \<ggreater> P\<rightarrow> \<lless> \<pi>, Hashed (hash \<lparr>v\<rparr>) v \<ggreater>" |
  s_UnauthP:   "\<lbrakk> value v \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Unauth (Hashed h v) \<ggreater> P\<rightarrow> \<lless> \<pi> @ [\<lparr>v\<rparr>], v \<ggreater>" |
  s_AuthV:     "\<lbrakk> closed v; value v \<rbrakk>
              \<Longrightarrow> \<lless> \<pi>, Auth v \<ggreater> V\<rightarrow> \<lless> \<pi>, Hash (hash v) \<ggreater>" |
  s_UnauthV:   "\<lbrakk> closed s\<^sub>0; hash s\<^sub>0 = h \<rbrakk>
              \<Longrightarrow> \<lless> s\<^sub>0#\<pi>, Unauth (Hash h) \<ggreater> V\<rightarrow> \<lless> \<pi>, s\<^sub>0 \<ggreater>"

declare smallstep.intros[simp]
declare smallstep.intros[intro]

equivariance smallstep
nominal_inductive smallstep
  avoids s_AppLam: x
       | s_AppRec: x
       | s_Let1:   x
       | s_Let2:   x
  by (auto simp add: fresh_Pair fresh_subst_term)

inductive smallsteps :: "proofstream \<Rightarrow> term \<Rightarrow> mode \<Rightarrow> nat \<Rightarrow> proofstream \<Rightarrow> term \<Rightarrow> bool" ("\<lless>_, _\<ggreater> _\<rightarrow>_ \<lless>_, _\<ggreater>") where
  s_Id: "\<lless> \<pi>, e \<ggreater> _\<rightarrow>0 \<lless> \<pi>, e \<ggreater>" |
  s_Tr: "\<lbrakk> \<lless> \<pi>\<^sub>1, e\<^sub>1 \<ggreater> m\<rightarrow>i \<lless> \<pi>\<^sub>2, e\<^sub>2 \<ggreater>; \<lless> \<pi>\<^sub>2, e\<^sub>2 \<ggreater> m\<rightarrow> \<lless> \<pi>\<^sub>3, e\<^sub>3 \<ggreater> \<rbrakk>
       \<Longrightarrow> \<lless> \<pi>\<^sub>1, e\<^sub>1 \<ggreater> m\<rightarrow>(i+1) \<lless> \<pi>\<^sub>3, e\<^sub>3 \<ggreater>"

declare smallsteps.intros[simp]
declare smallsteps.intros[intro]

equivariance smallsteps
nominal_inductive smallsteps .

lemma steps_1_step[simp]: "\<lless> \<pi>, e \<ggreater> m\<rightarrow>1 \<lless> \<pi>', e' \<ggreater> = \<lless> \<pi>, e \<ggreater> m\<rightarrow> \<lless> \<pi>', e' \<ggreater>" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then show ?R
  proof (induct \<pi> e m "1::nat" \<pi>' e' rule: smallsteps.induct)
    case (s_Tr \<pi>\<^sub>1 e\<^sub>1 m i \<pi>\<^sub>2 e\<^sub>2 \<pi>\<^sub>3 e\<^sub>3)
    then show ?case
      by (induct \<pi>\<^sub>1 e\<^sub>1 m i \<pi>\<^sub>2 e\<^sub>2 rule: smallsteps.induct) auto
  qed simp
qed (auto intro: s_Tr[where i=0, simplified])

text \<open>Inversion rules for smallstep(s) predicates.\<close>

lemma value_no_step[intro]:
  assumes "\<lless> \<pi>\<^sub>1, v \<ggreater> m\<rightarrow> \<lless> \<pi>\<^sub>2, t \<ggreater>" "value v"
  shows   "False"
  using assms by (induct \<pi>\<^sub>1 v m \<pi>\<^sub>2 t rule: smallstep.induct) auto

lemma subst_term_perm:
  assumes "atom x' \<sharp> (x, e)"
  shows "e[v / x] = ((x \<leftrightarrow> x') \<bullet> e)[v / x']"
  using assms [[simproc del: alpha_lst]]
  by (nominal_induct e avoiding: x x' v rule: term.strong_induct)
     (auto simp: fresh_Pair fresh_at_base(2) permute_hash_def)

inductive_cases s_Unit_inv[elim]: "\<lless> \<pi>\<^sub>1, Unit \<ggreater>  m\<rightarrow>  \<lless> \<pi>\<^sub>2, v \<ggreater>"

inductive_cases s_App_inv[consumes 1, case_names App1 App2 AppLam AppRec, elim]: "\<lless> \<pi>, App v\<^sub>1 v\<^sub>2 \<ggreater> m\<rightarrow> \<lless> \<pi>', e \<ggreater>"

lemma s_Let_inv':
  assumes "\<lless> \<pi>, Let e\<^sub>1 x e\<^sub>2 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e' \<ggreater>"
  and     "atom x \<sharp> (e\<^sub>1,\<pi>)"
  obtains e\<^sub>1' where "(e' = e\<^sub>2[e\<^sub>1 / x] \<and> value e\<^sub>1 \<and> \<pi> = \<pi>') \<or> (\<lless> \<pi>, e\<^sub>1 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e\<^sub>1' \<ggreater> \<and> e' = Let e\<^sub>1' x e\<^sub>2 \<and> \<not> value e\<^sub>1)"
  using assms [[simproc del: alpha_lst]]
  by (atomize_elim, induct \<pi> "Let e\<^sub>1 x e\<^sub>2" m \<pi>' e' rule: smallstep.induct)
     (auto simp: fresh_Pair fresh_subst_term perm_supp_eq elim: Abs_lst1_fcb2')

lemma s_Let_inv[consumes 2, case_names Let1 Let2, elim]:
  assumes "\<lless> \<pi>, Let e\<^sub>1 x e\<^sub>2 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e' \<ggreater>"
  and     "atom x \<sharp> (e\<^sub>1,\<pi>)"
  and     "e' = e\<^sub>2[e\<^sub>1 / x] \<and> value e\<^sub>1 \<and> \<pi> = \<pi>' \<Longrightarrow> Q"
  and     "\<And>e\<^sub>1'. \<lless> \<pi>, e\<^sub>1 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e\<^sub>1' \<ggreater> \<and> e' = Let e\<^sub>1' x e\<^sub>2 \<and> \<not> value e\<^sub>1 \<Longrightarrow> Q"
  shows   "Q"
  using assms by (auto elim: s_Let_inv')

inductive_cases s_Case_inv[consumes 1, case_names Case Inj1 Inj2, elim]:
  "\<lless> \<pi>, Case e e\<^sub>1 e\<^sub>2 \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e' \<ggreater>"
inductive_cases s_Prj1_inv[consumes 1, case_names Prj1 PrjPair1, elim]:
  "\<lless> \<pi>, Prj1 e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', v \<ggreater>"
inductive_cases s_Prj2_inv[consumes 1, case_names Prj2 PrjPair2, elim]:
  "\<lless> \<pi>, Prj2 e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', v \<ggreater>"
inductive_cases s_Pair_inv[consumes 1, case_names Pair1 Pair2, elim]:
  "\<lless> \<pi>, Pair e\<^sub>1 e\<^sub>2 \<ggreater> m\<rightarrow> \<lless> \<pi>', e' \<ggreater>"
inductive_cases s_Inj1_inv[consumes 1, case_names Inj1, elim]:
  "\<lless> \<pi>, Inj1 e \<ggreater> m\<rightarrow> \<lless> \<pi>', e' \<ggreater>"
inductive_cases s_Inj2_inv[consumes 1, case_names Inj2, elim]:
  "\<lless> \<pi>, Inj2 e \<ggreater> m\<rightarrow> \<lless> \<pi>', e' \<ggreater>"
inductive_cases s_Roll_inv[consumes 1, case_names Roll, elim]:
  "\<lless> \<pi>, Roll e \<ggreater> m\<rightarrow> \<lless> \<pi>', e' \<ggreater>"
inductive_cases s_Unroll_inv[consumes 1, case_names Unroll UnrollRoll, elim]:
  "\<lless> \<pi>, Unroll e \<ggreater>  m\<rightarrow>  \<lless> \<pi>', e' \<ggreater>"
inductive_cases s_AuthI_inv[consumes 1, case_names Auth AuthI, elim]:
  "\<lless> \<pi>, Auth e \<ggreater>  I\<rightarrow>  \<lless> \<pi>', e' \<ggreater>"
inductive_cases s_UnauthI_inv[consumes 1, case_names Unauth UnauthI, elim]:
  "\<lless> \<pi>, Unauth e \<ggreater>  I\<rightarrow>  \<lless> \<pi>', e' \<ggreater>"
inductive_cases s_AuthP_inv[consumes 1, case_names Auth AuthP, elim]:
  "\<lless> \<pi>, Auth e \<ggreater>  P\<rightarrow>  \<lless> \<pi>', e' \<ggreater>"
inductive_cases s_UnauthP_inv[consumes 1, case_names Unauth UnauthP, elim]:
  "\<lless> \<pi>, Unauth e \<ggreater>  P\<rightarrow>  \<lless> \<pi>', e' \<ggreater>"
inductive_cases s_AuthV_inv[consumes 1, case_names Auth AuthV, elim]:
  "\<lless> \<pi>, Auth e \<ggreater>  V\<rightarrow>  \<lless> \<pi>', e' \<ggreater>"
inductive_cases s_UnauthV_inv[consumes 1, case_names Unauth UnauthV, elim]:
  "\<lless> \<pi>, Unauth e \<ggreater>  V\<rightarrow>  \<lless> \<pi>', e' \<ggreater>"

inductive_cases s_Id_inv[elim]: "\<lless> \<pi>\<^sub>1, e\<^sub>1 \<ggreater> m\<rightarrow>0 \<lless> \<pi>\<^sub>2, e\<^sub>2 \<ggreater>"
inductive_cases s_Tr_inv[elim]: "\<lless> \<pi>\<^sub>1, e\<^sub>1 \<ggreater> m\<rightarrow>i \<lless> \<pi>\<^sub>3, e\<^sub>3 \<ggreater>"

text \<open>Freshness with smallstep.\<close>

lemma fresh_smallstep_I:
  fixes x :: var
  assumes "\<lless> \<pi>, e \<ggreater> I\<rightarrow> \<lless> \<pi>', e' \<ggreater>" "atom x \<sharp> e"
  shows   "atom x \<sharp> e'"
  using assms by (induct \<pi> e I \<pi>' e' rule: smallstep.induct) (auto simp: fresh_subst_term)

lemma fresh_smallstep_P:
  fixes x :: var
  assumes "\<lless> \<pi>, e \<ggreater> P\<rightarrow> \<lless> \<pi>', e' \<ggreater>" "atom x \<sharp> e"
  shows   "atom x \<sharp> e'"
  using assms by (induct \<pi> e P \<pi>' e' rule: smallstep.induct) (auto simp: fresh_subst_term)

lemma fresh_smallsteps_I:
  fixes x :: var
  assumes "\<lless> \<pi>, e \<ggreater> I\<rightarrow>i \<lless> \<pi>', e' \<ggreater>" "atom x \<sharp> e"
  shows   "atom x \<sharp> e'"
  using assms by (induct \<pi> e I i \<pi>' e' rule: smallsteps.induct) (simp_all add: fresh_smallstep_I)

lemma fresh_ps_smallstep_P:
  fixes x :: var
  assumes "\<lless> \<pi>, e \<ggreater> P\<rightarrow> \<lless> \<pi>', e' \<ggreater>" "atom x \<sharp> e" "atom x \<sharp> \<pi>"
  shows   "atom x \<sharp> \<pi>'"
  using assms proof (induct \<pi> e P \<pi>' e' rule: smallstep.induct)
  case (s_UnauthP v \<pi> h)
  then show ?case
    by (simp add: fresh_Cons fresh_append fresh_shallow)
  qed auto

text \<open>Proofstream lemmas.\<close>

lemma smallstepI_ps_eq:
  assumes "\<lless> \<pi>, e \<ggreater> I\<rightarrow> \<lless> \<pi>', e' \<ggreater>"
  shows   "\<pi> = \<pi>'"
  using assms by (induct \<pi> e I \<pi>' e' rule: smallstep.induct) auto

lemma smallstepI_ps_emptyD:
  "\<lless>\<pi>, e\<ggreater> I\<rightarrow> \<lless>[], e'\<ggreater> \<Longrightarrow> \<lless>[], e\<ggreater> I\<rightarrow> \<lless>[], e'\<ggreater>"
  "\<lless>[], e\<ggreater> I\<rightarrow> \<lless>\<pi>, e'\<ggreater> \<Longrightarrow> \<lless>[], e\<ggreater> I\<rightarrow> \<lless>[], e'\<ggreater>"
  using smallstepI_ps_eq by force+

lemma smallstepsI_ps_eq:
  assumes "\<lless>\<pi>, e\<ggreater> I\<rightarrow>i \<lless>\<pi>', e'\<ggreater>"
  shows   "\<pi> = \<pi>'"
  using assms by (induct \<pi> e I i \<pi>' e' rule: smallsteps.induct) (auto dest: smallstepI_ps_eq)

lemma smallstepsI_ps_emptyD:
  "\<lless>\<pi>, e\<ggreater> I\<rightarrow>i \<lless>[], e'\<ggreater> \<Longrightarrow> \<lless>[], e\<ggreater> I\<rightarrow>i \<lless>[], e'\<ggreater>"
  "\<lless>[], e\<ggreater> I\<rightarrow>i \<lless>\<pi>, e'\<ggreater> \<Longrightarrow> \<lless>[], e\<ggreater> I\<rightarrow>i \<lless>[], e'\<ggreater>"
  using smallstepsI_ps_eq by force+

lemma smallstepV_consumes_proofstream:
  assumes "\<lless> \<pi>\<^sub>1, eV \<ggreater> V\<rightarrow> \<lless> \<pi>\<^sub>2, eV' \<ggreater>"
  obtains \<pi> where "\<pi>\<^sub>1 = \<pi> @ \<pi>\<^sub>2"
  using assms by (induct \<pi>\<^sub>1 eV V \<pi>\<^sub>2 eV' rule: smallstep.induct) auto

lemma smallstepsV_consumes_proofstream:
  assumes "\<lless> \<pi>\<^sub>1, eV \<ggreater> V\<rightarrow>i \<lless> \<pi>\<^sub>2, eV' \<ggreater>"
  obtains \<pi> where "\<pi>\<^sub>1 = \<pi> @ \<pi>\<^sub>2"
  using assms by (induct \<pi>\<^sub>1 eV V i \<pi>\<^sub>2 eV' rule: smallsteps.induct)
                 (auto elim: smallstepV_consumes_proofstream)

lemma smallstepP_generates_proofstream:
  assumes "\<lless> \<pi>\<^sub>1, eP \<ggreater> P\<rightarrow> \<lless> \<pi>\<^sub>2, eP' \<ggreater>"
  obtains \<pi> where "\<pi>\<^sub>2 = \<pi>\<^sub>1 @ \<pi>"
  using assms by (induct \<pi>\<^sub>1 eP P \<pi>\<^sub>2 eP' rule: smallstep.induct) auto

lemma smallstepsP_generates_proofstream:
  assumes "\<lless> \<pi>\<^sub>1, eP \<ggreater> P\<rightarrow>i \<lless> \<pi>\<^sub>2, eP' \<ggreater>"
  obtains \<pi> where "\<pi>\<^sub>2 = \<pi>\<^sub>1 @ \<pi>"
  using assms by (induct \<pi>\<^sub>1 eP P i \<pi>\<^sub>2 eP' rule: smallsteps.induct)
                 (auto elim: smallstepP_generates_proofstream)

lemma smallstepV_ps_append:
  "\<lless> \<pi>, eV \<ggreater> V\<rightarrow> \<lless> \<pi>', eV' \<ggreater> \<longleftrightarrow> \<lless> \<pi> @ X, eV \<ggreater> V\<rightarrow> \<lless> \<pi>' @ X, eV' \<ggreater>" (is "?L \<longleftrightarrow> ?R")
proof (rule iffI)
  assume ?L then show ?R
    by (nominal_induct \<pi> eV V \<pi>' eV' avoiding: X rule: smallstep.strong_induct)
       (auto simp: fresh_append fresh_Pair)
next
  assume ?R then show ?L
    by (nominal_induct "\<pi> @ X" eV V "\<pi>' @ X" eV' avoiding: X rule: smallstep.strong_induct)
       (auto simp: fresh_append fresh_Pair)
qed

lemma smallstepV_ps_to_suffix:
  assumes "\<lless>\<pi>, e\<ggreater> V\<rightarrow> \<lless>\<pi>' @ X, e'\<ggreater>"
  obtains \<pi>'' where "\<pi> = \<pi>'' @ X"
  using assms
  by (induct \<pi> e V "\<pi>' @ X" e' rule: smallstep.induct) auto

lemma smallstepsV_ps_append:
  "\<lless> \<pi>, eV \<ggreater> V\<rightarrow>i \<lless> \<pi>', eV' \<ggreater> \<longleftrightarrow> \<lless> \<pi> @ X, eV \<ggreater> V\<rightarrow>i \<lless> \<pi>' @ X, eV' \<ggreater>" (is "?L \<longleftrightarrow> ?R")
proof (rule iffI)
  assume ?L then show ?R
  proof (induct \<pi> eV V i \<pi>' eV' rule: smallsteps.induct)
    case (s_Tr \<pi>\<^sub>1 e\<^sub>1 i \<pi>\<^sub>2 e\<^sub>2 \<pi>\<^sub>3 e\<^sub>3)
    then show ?case
      by (auto simp: iffD1[OF smallstepV_ps_append])
  qed simp
next
  assume ?R then show ?L
  proof (induct "\<pi> @ X" eV V i "\<pi>' @ X" eV' arbitrary: \<pi>' rule: smallsteps.induct)
    case (s_Tr e\<^sub>1 i \<pi>\<^sub>2 e\<^sub>2 e\<^sub>3)
    from s_Tr(3) obtain \<pi>''' where "\<pi>\<^sub>2 = \<pi>''' @ X"
      by (auto elim: smallstepV_ps_to_suffix)
    with s_Tr show ?case
      by (auto dest: iffD2[OF smallstepV_ps_append])
  qed simp
qed

lemma smallstepP_ps_prepend:
  "\<lless> \<pi>, eP \<ggreater> P\<rightarrow> \<lless> \<pi>', eP' \<ggreater> \<longleftrightarrow> \<lless> X @ \<pi>, eP \<ggreater> P\<rightarrow> \<lless> X @ \<pi>', eP' \<ggreater>" (is "?L \<longleftrightarrow> ?R")
proof (rule iffI)
  assume ?L then show ?R
  proof (nominal_induct \<pi> eP P \<pi>' eP' avoiding: X rule: smallstep.strong_induct)
    case (s_UnauthP v \<pi> h)
    then show ?case
      by (subst append_assoc[symmetric, of X \<pi> "[\<lparr>v\<rparr>]"]) (erule smallstep.s_UnauthP)
  qed (auto simp: fresh_append fresh_Pair)
next
  assume ?R then show ?L
    by (nominal_induct "X @ \<pi>" eP P "X @ \<pi>'" eP' avoiding: X rule: smallstep.strong_induct)
       (auto simp: fresh_append fresh_Pair)
qed

lemma smallstepsP_ps_prepend:
  "\<lless> \<pi>, eP \<ggreater> P\<rightarrow>i \<lless> \<pi>', eP' \<ggreater> \<longleftrightarrow> \<lless> X @ \<pi>, eP \<ggreater> P\<rightarrow>i \<lless> X @ \<pi>', eP' \<ggreater>" (is "?L \<longleftrightarrow> ?R")
proof (rule iffI)
  assume ?L then show ?R
  proof (induct \<pi> eP P i \<pi>' eP' rule: smallsteps.induct)
    case (s_Tr \<pi>\<^sub>1 e\<^sub>1 i \<pi>\<^sub>2 e\<^sub>2 \<pi>\<^sub>3 e\<^sub>3)
    then show ?case
      by (auto simp: iffD1[OF smallstepP_ps_prepend])
  qed simp
next
  assume ?R then show ?L
  proof (induct "X @ \<pi>" eP P i "X @ \<pi>'" eP' arbitrary: \<pi>' rule: smallsteps.induct)
    case (s_Tr e\<^sub>1 i \<pi>\<^sub>2 e\<^sub>2 e\<^sub>3)
    then obtain \<pi>'' where \<pi>'': "\<pi>\<^sub>2 = X @ \<pi> @ \<pi>''"
      by (auto elim: smallstepsP_generates_proofstream)
    then have "\<lless>\<pi>, e\<^sub>1\<ggreater> P\<rightarrow>i \<lless>\<pi> @ \<pi>'', e\<^sub>2\<ggreater>"
      by (auto dest: s_Tr(2))
    with \<pi>'' s_Tr(1,3) show ?case
      by (auto dest: iffD2[OF smallstepP_ps_prepend])
  qed simp
qed

subsection \<open>Type Progress\<close>

lemma type_progress:
  assumes "{$$} \<turnstile>\<^sub>W e : \<tau>"
  shows   "value e \<or> (\<exists>e'. \<lless> [], e \<ggreater> I\<rightarrow> \<lless> [], e' \<ggreater>)"
using assms proof (nominal_induct "{$$} :: tyenv" e \<tau> rule: judge_weak.strong_induct)
  case (jw_Let x e\<^sub>1 \<tau>\<^sub>1 e\<^sub>2 \<tau>\<^sub>2)
  then show ?case
    by (auto 0 3 simp: fresh_smallstep_I elim!: s_Let2[of e\<^sub>2]
      intro: exI[where P="\<lambda>e. \<lless>_, _\<ggreater> _\<rightarrow> \<lless>_, e\<ggreater>", OF s_Let1, rotated])
next
  case (jw_Prj1 v \<tau>\<^sub>1 \<tau>\<^sub>2)
  then show ?case
    by (auto elim!: jw_Prod_inv[of v \<tau>\<^sub>1 \<tau>\<^sub>2])
next
  case (jw_Prj2 v \<tau>\<^sub>1 \<tau>\<^sub>2)
  then show ?case
    by (auto elim!: jw_Prod_inv[of v \<tau>\<^sub>1 \<tau>\<^sub>2])
next
  case (jw_App e \<tau>\<^sub>1 \<tau>\<^sub>2 e')
  then show ?case
    by (auto 0 4 elim: jw_Fun_inv[of _ _ _ e'])
next
  case (jw_Case v v\<^sub>1 v\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau>)
  then show ?case
    by (auto 0 4 elim: jw_Sum_inv[of _ v\<^sub>1 v\<^sub>2])
qed fast+

subsection \<open>Weak Type Preservation\<close>

lemma fresh_tyenv_None:
  fixes \<Gamma> :: tyenv
  shows "atom x \<sharp> \<Gamma> \<longleftrightarrow> \<Gamma> $$ x = None" (is "?L \<longleftrightarrow> ?R")
proof
  assume assm: ?L show ?R
  proof (rule ccontr)
    assume "\<Gamma> $$ x \<noteq> None"
    then obtain \<tau> where "\<Gamma> $$ x = Some \<tau>" by blast
    with assm have "\<forall>a :: var. atom a \<sharp> \<Gamma> \<longrightarrow> \<Gamma> $$ a = Some \<tau>"
      using fmap_freshness_lemma_unique[OF exI, of x \<Gamma>]
      by (simp add: fresh_Pair fresh_Some) metis
    then have "{a :: var. atom a \<sharp> \<Gamma>} \<subseteq> fmdom' \<Gamma>"
      by (auto simp: image_iff Ball_def fmlookup_dom'_iff)
    moreover
    { assume "infinite {a :: var. \<not> atom a \<sharp> \<Gamma>}"
      then have "infinite {a :: var. atom a \<in> supp \<Gamma>}"
        unfolding fresh_def by auto
      then have "infinite (supp \<Gamma>)"
        by (rule contrapos_nn)
          (auto simp: image_iff inv_f_f[of atom] inj_on_def
            elim!: finite_surj[of _ _ "inv atom"] bexI[rotated])
      then have False
        using finite_supp[of \<Gamma>] by blast
    }
    then have "infinite {a :: var. atom a \<sharp> \<Gamma>}"
      by auto
    ultimately show False
      using finite_subset[of "{a. atom a \<sharp> \<Gamma>}" "fmdom' \<Gamma>"] unfolding fmdom'_alt_def
      by auto
  qed
next
  assume ?R then show ?L
  proof (induct \<Gamma> arbitrary: x)
    case (fmupd y z \<Gamma>)
    then show ?case
      by (cases "y = x") (auto intro: fresh_fmap_update)
  qed simp
qed

lemma judge_weak_fresh_env_fresh_term[dest]:
  fixes a :: var
  assumes "\<Gamma> \<turnstile>\<^sub>W e : \<tau>" "atom a \<sharp> \<Gamma>"
  shows   "atom a \<sharp> e"
  using assms proof (nominal_induct \<Gamma> e \<tau> avoiding: a rule: judge_weak.strong_induct)
  case (jw_Var \<Gamma> x \<tau>)
  then show ?case
    by (cases "a = x") (auto simp: fresh_tyenv_None)
qed (simp_all add: fresh_Cons fresh_fmap_update)

lemma judge_weak_weakening_1:
  assumes "\<Gamma> \<turnstile>\<^sub>W e : \<tau>" "atom y \<sharp> e"
  shows   "\<Gamma>(y $$:= \<tau>') \<turnstile>\<^sub>W e : \<tau>"
  using assms proof (nominal_induct \<Gamma> e \<tau> avoiding: y \<tau>' rule: judge_weak.strong_induct)
  case (jw_Lam x \<Gamma> \<tau>\<^sub>1 e \<tau>\<^sub>2)
  from jw_Lam(5)[of y \<tau>'] jw_Lam(1-4,6) show ?case
    by (auto simp add: fresh_at_base fmap_reorder_neq_updates fresh_fmap_update)
next
  case (jw_App v v' \<Gamma> \<tau>\<^sub>1 \<tau>\<^sub>2)
  then show ?case
    by (force simp add: fresh_at_base fmap_reorder_neq_updates fresh_fmap_update)
next
  case (jw_Let x \<Gamma> e\<^sub>1 \<tau>\<^sub>1 e\<^sub>2 \<tau>\<^sub>2)
  from jw_Let(6)[of y \<tau>'] jw_Let(8)[of y \<tau>'] jw_Let(1-5,7,9) show ?case
    by (auto simp add: fresh_at_base fmap_reorder_neq_updates fresh_fmap_update)
next
  case (jw_Rec x \<Gamma> z \<tau>\<^sub>1 \<tau>\<^sub>2 e')
  from jw_Rec(9)[of y \<tau>'] jw_Rec(1-8,10) show ?case
    by (auto simp add: fresh_at_base fmap_reorder_neq_updates fresh_fmap_update fresh_Pair)
next
  case (jw_Case v v\<^sub>1 v\<^sub>2 \<Gamma> \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau>)
  then show ?case
    by (fastforce simp add: fresh_at_base fmap_reorder_neq_updates fresh_fmap_update)
next
  case (jw_Roll \<alpha> \<Gamma> v \<tau>)
  then show ?case
    by (simp add: fresh_fmap_update)
next
  case (jw_Unroll \<alpha> \<Gamma> v \<tau>)
  then show ?case
    by (simp add: fresh_fmap_update)
qed auto

lemma judge_weak_weakening_2:
  assumes "\<Gamma> \<turnstile>\<^sub>W e : \<tau>" "atom y \<sharp> \<Gamma>"
  shows   "\<Gamma>(y $$:= \<tau>') \<turnstile>\<^sub>W e : \<tau>"
  proof -
    from assms have "atom y \<sharp> e"
      by (rule judge_weak_fresh_env_fresh_term)
    with assms show "\<Gamma>(y $$:= \<tau>') \<turnstile>\<^sub>W e : \<tau>" by (simp add: judge_weak_weakening_1)
  qed

lemma judge_weak_weakening_env:
  assumes "{$$} \<turnstile>\<^sub>W e : \<tau>"
  shows   "\<Gamma> \<turnstile>\<^sub>W e : \<tau>"
using assms proof (induct \<Gamma>)
  case fmempty
  then show ?case by assumption
next
  case (fmupd x y \<Gamma>)
  then show ?case
    by (simp add: fresh_tyenv_None judge_weak_weakening_2)
qed

lemma value_subst_value:
  assumes "value e" "value e'"
  shows   "value (e[e' / x])"
  using assms by (induct e  e'  x rule: subst_term.induct) auto

lemma judge_weak_subst[intro]:
  assumes "\<Gamma>(a $$:= \<tau>') \<turnstile>\<^sub>W e : \<tau>" "{$$} \<turnstile>\<^sub>W e' : \<tau>'"
  shows   "\<Gamma> \<turnstile>\<^sub>W e[e' / a] : \<tau>"
  using assms proof (nominal_induct "\<Gamma>(a $$:= \<tau>')" e \<tau> avoiding: a e' \<Gamma> rule: judge_weak.strong_induct)
  case (jw_Var x \<tau>)
  then show ?case
    by (auto simp: judge_weak_weakening_env)
next
  case (jw_Lam x \<tau>\<^sub>1 e \<tau>\<^sub>2)
  then show ?case
    by (fastforce simp: fmap_reorder_neq_updates)
next
  case (jw_Rec x y \<tau>\<^sub>1 \<tau>\<^sub>2 e)
  then show ?case
    by (fastforce simp: fmap_reorder_neq_updates)
next
  case (jw_Let x e\<^sub>1 \<tau>\<^sub>1 e\<^sub>2 \<tau>\<^sub>2)
  then show ?case
    by (fastforce simp: fmap_reorder_neq_updates)
qed fastforce+

lemma type_preservation:
  assumes "\<lless> [], e \<ggreater> I\<rightarrow> \<lless> [], e' \<ggreater>" "{$$} \<turnstile>\<^sub>W e : \<tau>"
  shows   "{$$} \<turnstile>\<^sub>W e' : \<tau>"
  using assms [[simproc del: alpha_lst]]
proof (nominal_induct "[]::proofstream" e I "[]::proofstream" e' arbitrary: \<tau> rule: smallstep.strong_induct)
case (s_AppLam v x e)
  then show ?case by force
next
  case (s_AppRec v x e)
  then show ?case
    by (elim jw_App_inv jw_Rec_inv) (auto 0 3 simp del: subst_term.simps)
next
  case (s_Let1 x e\<^sub>1 e\<^sub>1' e\<^sub>2)
  from s_Let1(1,2,7) show ?case
    by (auto intro: s_Let1(6) del: jw_Let_inv elim!: jw_Let_inv)
next
  case (s_Unroll e e')
  then obtain \<alpha>::tvar where "atom \<alpha> \<sharp> \<tau>"
    using obtain_fresh by blast
  with s_Unroll show ?case
    by (auto elim: jw_Unroll_inv[where \<alpha> = \<alpha>])
next
  case (s_Roll e e')
  then obtain \<alpha>::tvar where "atom \<alpha> \<sharp> \<tau>"
    using obtain_fresh by blast
  with s_Roll show ?case
    by (auto elim: jw_Roll_inv[where \<alpha> = \<alpha>])
next
  case (s_UnrollRoll v)
  then obtain \<alpha>::tvar where "atom \<alpha> \<sharp> \<tau>"
    using obtain_fresh by blast
  with s_UnrollRoll show ?case
    by (fastforce simp: Abs1_eq(3) elim: jw_Roll_inv[where \<alpha> = \<alpha>] jw_Unroll_inv[where \<alpha> = \<alpha>])
qed fastforce+

subsection \<open>Corrected Lemma 1 from Miller et al.~\cite{adsg}: Weak Type Soundness\<close>

lemma type_soundness:
  assumes "{$$} \<turnstile>\<^sub>W e : \<tau>"
  shows   "value e \<or> (\<exists>e'. \<lless> [], e \<ggreater> I\<rightarrow> \<lless> [], e' \<ggreater> \<and> {$$} \<turnstile>\<^sub>W e' : \<tau>)"
proof (cases "value e")
  case True
  then show ?thesis by simp
next
  case False
  with assms obtain e' where "\<lless>[], e\<ggreater> I\<rightarrow> \<lless>[], e'\<ggreater>" by (auto dest: type_progress)
  with assms show ?thesis
    by (auto simp: type_preservation)
qed

(*<*)
end
(*>*)
