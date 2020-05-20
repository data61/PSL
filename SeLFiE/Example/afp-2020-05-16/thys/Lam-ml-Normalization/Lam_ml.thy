section \<open>Introduction\<close>
(*<*) 
theory Lam_ml
imports "HOL-Nominal.Nominal" "HOL-Library.LaTeXsugar"
begin (*>*)
text_raw \<open>\label{chap:formal}\<close>

text \<open>This article contains a formalization of the strong normalization
theorem for the $\lambda_{ml}$-calculus. The formalization is based on a proof
by Lindley and Stark \cite{TT-lifting}. An informal description of the
formalization can be found in \cite{Doczkal:09}.

This formalization extends the example proof of strong normalization for the
simply-typed $\lambda$-calculus, which is included in the Isabelle distribution
\cite{SN.thy}. The parts of the original proof which have been left unchanged
are not displayed in this document.

The next section deals with the formalization of syntax, typing, and
substitution. Section~\ref{sec:reduction} contains the formalization of the
reduction relation. Section~\ref{sec:stacks} defines stacks which are used to
define the reducibility relation in Section~\ref{sec:reducibility-formal}. The
following sections contain proofs about the reducibility relation, ending with
the normalization theorem in Section~\ref{sec:FTLR}.\<close>

section \<open>The Calculus\<close>
text_raw \<open>\label{sec:calc}\<close>

atom_decl name

nominal_datatype trm = 
    Var "name" 
  | App "trm" "trm"
  | Lam "\<guillemotleft>name\<guillemotright>trm"      ("\<Lambda> _ . _" [0,120] 120)
  | To "trm" "\<guillemotleft>name\<guillemotright>trm" ("_ to _ in _" [141,0,140] 140) 
  | Ret "trm" ("[_]")


declare trm.inject[simp]
lemmas name_swap_bij = pt_swap_bij''[OF pt_name_inst at_name_inst]
lemmas ex_fresh = exists_fresh'[OF fin_supp]

lemma alpha'' :
  fixes x y :: name and t::trm
  assumes a: "x \<sharp> t"
  shows "[y].t = [x].([(y,x)] \<bullet> t)"
proof -
  from a have aux: "y \<sharp> [(y, x)] \<bullet> t"
    by (subst fresh_bij[THEN sym, of _ _ "[(x,y)]"]) 
        (auto simp add: perm_swap calc_atm)
  thus ?thesis  
    by(auto simp add: alpha perm_swap name_swap_bij fresh_bij)
qed

text \<open>Even though our types do not involve binders, we still need to formalize
them as nominal datatypes to obtain a permutation action. This is required to
establish equivariance of the typing relation.\<close>

nominal_datatype ty =
    TBase
  | TFun "ty" "ty" (infix "\<rightarrow>" 200)
  | T "ty" 

text\<open>Since we cannot use typed variables, we have to formalize typing
contexts. Typing contexts are formalized as lists. A context is \textit{valid}
if no name occurs twice.\<close>

inductive 
  valid :: "(name\<times>ty) list \<Rightarrow> bool"
where
  v1[intro]: "valid []"
| v2[intro]: "\<lbrakk>valid \<Gamma>;x\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((x,\<sigma>)#\<Gamma>)"
equivariance valid 

lemma fresh_ty: 
  fixes x :: name and \<tau>::ty
  shows "x \<sharp> \<tau>"
by (induct \<tau> rule: ty.induct) (auto)

lemma fresh_context: 
  fixes  \<Gamma> :: "(name\<times>ty)list"
  assumes a: "x \<sharp> \<Gamma>"
  shows "\<not>(\<exists> \<tau> . (x,\<tau>)\<in>set \<Gamma>)"
using a
by (induct \<Gamma>) (auto simp add: fresh_prod fresh_list_cons fresh_atm)

inductive 
  typing :: "(name\<times>ty) list\<Rightarrow>trm\<Rightarrow>ty\<Rightarrow>bool" ("_ \<turnstile> _ : _" [60,60,60] 60)
where
  t1[intro]: "\<lbrakk>valid \<Gamma>; (x,\<tau>)\<in>set \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x : \<tau>"
| t2[intro]: "\<lbrakk>\<Gamma> \<turnstile> s : \<tau>\<rightarrow>\<sigma>; \<Gamma> \<turnstile> t : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App s t : \<sigma>"
| t3[intro]: "\<lbrakk>x \<sharp> \<Gamma>; ((x,\<tau>)#\<Gamma>) \<turnstile> t : \<sigma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<Lambda> x . t : \<tau>\<rightarrow>\<sigma>" 
| t4[intro]: "\<lbrakk> \<Gamma> \<turnstile> s : \<sigma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> [s] : T \<sigma>" 
| t5[intro]: "\<lbrakk>x \<sharp> (\<Gamma>,s); \<Gamma> \<turnstile> s : T \<sigma> ; ((x,\<sigma>)#\<Gamma>) \<turnstile> t : T \<tau> \<rbrakk> 
                \<Longrightarrow> \<Gamma> \<turnstile> s to x in t : T \<tau>" 
equivariance typing
nominal_inductive typing 
  by(simp_all add: abs_fresh fresh_ty)

text \<open>Except for the explicit requirement that contexts be valid in the
variable case and the freshness requirements in \isa{t3} and \isa{t5}, this
typing
relation is a direct translation of the original typing relation in
\cite{TT-lifting} to Curry-style typing.\<close>

fun
  lookup :: "(name\<times>trm) list \<Rightarrow> name \<Rightarrow> trm"   
where
  "lookup [] x        = Var x"
| "lookup ((y,e)#\<theta>) x = (if x=y then e else lookup \<theta> x)"

lemma lookup_eqvt[eqvt]:
  fixes pi::"name prm"
  and   \<theta>::"(name\<times>trm) list"
  and   x::"name"
  shows "pi \<bullet> (lookup \<theta> x) = lookup (pi \<bullet> \<theta>) (pi \<bullet> x)"
by (induct \<theta>) (auto simp add: eqvts)

nominal_primrec
  psubst :: "(name\<times>trm) list \<Rightarrow> trm \<Rightarrow> trm"  ("_<_>" [95,95] 205)
where 
    "\<theta><Var x> = lookup \<theta> x"
  | "\<theta><App s t> = App (\<theta><s>) (\<theta><t>)"
  | "x \<sharp> \<theta> \<Longrightarrow> \<theta><\<Lambda> x .s> = \<Lambda> x . (\<theta><s>)"
  | "\<theta><[t]> = [\<theta><t>]"
  | "\<lbrakk> x \<sharp> \<theta> ; x \<sharp> t \<rbrakk> \<Longrightarrow> \<theta><t to x in s> = (\<theta><t>) to x in (\<theta><s>)"
by(finite_guess+ , (simp add: abs_fresh)+ , fresh_guess+)

lemma psubst_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi \<bullet> (\<theta><t>) = (pi \<bullet> \<theta>)<(pi \<bullet> t)>"
by(nominal_induct t avoiding: \<theta> rule:trm.strong_induct)
  (auto simp add: eqvts fresh_bij)

abbreviation 
  subst :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm" ("_[_::=_]" [200,100,100] 200)
where 
  "t[x::=t']  \<equiv> ([(x,t')])<t>"

lemma subst[simp]:
shows "(Var x)[y::=v] = (if x = y then v else Var x)"
  and "(App s t)[y::=v] = App (s[y::=v]) (t[y::=v])"
  and "x \<sharp> (y,v) \<Longrightarrow> (\<Lambda> x . t)[y::=v] = \<Lambda> x .t[y::=v]"
  and "x \<sharp> (s,y,v) \<Longrightarrow> (s to x in t)[y::=v] = s[y::=v] to x in t[y::=v]"
  and "([s])[y::=v] = [s[y::=v]]"
by(simp_all add: fresh_list_cons fresh_list_nil)

lemma subst_rename: 
  assumes a: "y \<sharp> t"
  shows "([(y,x)]\<bullet>t)[y::=v] = t[x::=v]"
using a
by(nominal_induct t avoiding: x y v rule: trm.strong_induct)
    (auto simp add: calc_atm fresh_atm abs_fresh fresh_prod fresh_aux)
lemmas subst_rename' = subst_rename[THEN sym]

lemma forget: "x \<sharp> t \<Longrightarrow> t[x::=v] = t"
by(nominal_induct t avoiding: x v rule: trm.strong_induct)
    (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact: 
  fixes x::"name"
  assumes x: "x \<sharp> v"   "x \<sharp> t"
  shows "x \<sharp> t[y::=v]"
using x
by(nominal_induct t avoiding: x y v rule: trm.strong_induct)
    (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact': 
  fixes x::"name"
  assumes x: "x \<sharp> v"
  shows "x \<sharp> t[x::=v]"
using x
by(nominal_induct t avoiding: x v rule: trm.strong_induct)
    (auto simp add: abs_fresh fresh_atm)

lemma subst_lemma:  
  assumes a: "x\<noteq>y"
  and     b: "x \<sharp> u"
  shows "s[x::=v][y::=u] = s[y::=u][x::=v[y::=u]]"
using a b
by(nominal_induct s avoiding: x y u v rule: trm.strong_induct)
    (auto simp add: fresh_fact forget)

lemma id_subs: 
  shows "t[x::=Var x] = t"
by(nominal_induct t avoiding: x rule:trm.strong_induct) auto

text \<open>In addition to the facts on simple substitution we also need some facts
on parallel substitution. In particular we want to be able to extend a parallel
substitution with a simple one.\<close>

lemma lookup_fresh:
  fixes z::"name"
  assumes "z\<sharp>\<theta>"   "z\<sharp>x"
  shows "z\<sharp> lookup \<theta> x"
using assms 
by(induct rule: lookup.induct) 
  (auto simp add: fresh_list_cons)

lemma lookup_fresh':
  assumes a: "z\<sharp>\<theta>"
  shows "lookup \<theta> z = Var z"
using a
by (induct rule: lookup.induct)
   (auto simp add: fresh_list_cons fresh_prod fresh_atm)

lemma psubst_fresh_fact:
  fixes x :: name
  assumes a: "x \<sharp> t" and b: "x \<sharp> \<theta>" 
  shows "x \<sharp> \<theta><t>"
using a b
by(nominal_induct t avoiding: \<theta> x rule:trm.strong_induct) 
    (auto simp add: lookup_fresh abs_fresh)

lemma psubst_subst:
  assumes a: "x \<sharp> \<theta>"
  shows "\<theta><t>[x::=s] = ((x,s)#\<theta>)<t>"
  using a
by(nominal_induct t avoiding: \<theta> x s rule: trm.strong_induct)
    (auto simp add: fresh_list_cons fresh_atm forget 
      lookup_fresh lookup_fresh' fresh_prod psubst_fresh_fact)

section \<open>The Reduction Relation\<close>
text_raw \<open>\label{sec:reduction}\<close>

text \<open>With substitution in place, we can now define the reduction relation on
$\lambda_{ml}$-terms. To derive strong induction and case rules, all the rules
must be vc-compatible (cf. \cite{nominal-techniques}). This requires some
additional freshness conditions. Note that in this particular case the
additional freshness conditions only serve the technical purpose of
automatically deriving strong reasoning principles. To show that the version
with freshness conditions defines the same relation as the one without the
freshness conditions, we also state this version and prove equality of the two
relations. 

This requires quite some effort and is something that is certainly undesirable
in nominal reasoning. Unfortunately, handling the reduction rule \isa{r10} which
rearranges the binding structure, appeared to be impossible without going
through this.\<close>


inductive std_reduction :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<leadsto> _" [80,80] 80)
where
  std_r1[intro!]:"s \<leadsto> s' \<Longrightarrow> App s t \<leadsto> App s' t"
| std_r2[intro!]:"t \<leadsto> t' \<Longrightarrow> App s t \<leadsto> App s t'"
| std_r3[intro!]:"App (\<Lambda> x . t) s \<leadsto> t[x::=s]"

| std_r4[intro!]:"t \<leadsto> t' \<Longrightarrow> \<Lambda> x . t \<leadsto> \<Lambda> x . t'"
| std_r5[intro!]:"x \<sharp> t \<Longrightarrow> \<Lambda> x . App t (Var x) \<leadsto> t"

| std_r6[intro!]:"\<lbrakk> s \<leadsto> s' \<rbrakk> \<Longrightarrow> s to x in t \<leadsto> s' to x in t"
| std_r7[intro!]:"\<lbrakk> t \<leadsto> t' \<rbrakk> \<Longrightarrow> s to x in t \<leadsto> s  to x in t'"
| std_r8[intro!]:"[s] to x in t \<leadsto> t[x::=s]"
| std_r9[intro!]:"x \<sharp> s \<Longrightarrow> s to x in [Var x] \<leadsto> s"
| std_r10[intro!]: "\<lbrakk> x \<sharp> y; x \<sharp> u\<rbrakk> 
                     \<Longrightarrow> (s to x in t) to y in u \<leadsto> s to x in (t to y in u)"
| std_r11[intro!]: "s \<leadsto> s' \<Longrightarrow> [s] \<leadsto> [s']"

inductive 
  reduction :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<mapsto> _" [80,80] 80)
where
  r1[intro!]:"s \<mapsto> s' \<Longrightarrow> App s t \<mapsto> App s' t"
| r2[intro!]:"t \<mapsto> t' \<Longrightarrow> App s t \<mapsto> App s t'"
| r3[intro!]:"x \<sharp> s \<Longrightarrow> App (\<Lambda> x . t) s \<mapsto> t[x::=s]"

| r4[intro!]:"t \<mapsto> t' \<Longrightarrow> \<Lambda> x . t \<mapsto> \<Lambda> x . t'"
| r5[intro!]:"x \<sharp> t \<Longrightarrow> \<Lambda> x . App t (Var x) \<mapsto> t"

| r6[intro!]:"\<lbrakk> x \<sharp> (s,s') ; s \<mapsto> s' \<rbrakk> \<Longrightarrow> s to x in t \<mapsto> s' to x in t"
| r7[intro!]:"\<lbrakk> x \<sharp> s ; t \<mapsto> t' \<rbrakk> \<Longrightarrow> s to x in t \<mapsto> s  to x in t'"
| r8[intro!]:"x \<sharp> s \<Longrightarrow> [s] to x in t \<mapsto> t[x::=s]"
| r9[intro!]:"x \<sharp> s \<Longrightarrow> s to x in [Var x] \<mapsto> s"
| r10[intro!]: "\<lbrakk> x \<sharp> (y,s,u) ; y \<sharp> (s,t) \<rbrakk> 
                  \<Longrightarrow> (s to x in t) to y in u \<mapsto> s to x in (t to y in u)"
| r11[intro!]: "s \<mapsto> s' \<Longrightarrow> [s] \<mapsto> [s']" 
equivariance reduction
nominal_inductive reduction
  by(auto simp add: abs_fresh fresh_fact' fresh_prod fresh_atm)


text \<open>In order to show adequacy, the extra freshness conditions in the rules
\isa{r3}, \isa{r6}, \isa{r7}, \isa{r8}, \isa{r9}, and \isa{r10} need to be
discharged.\<close>

text_raw \<open>\label{pg:alpha-begin}\<close>

lemma r3'[intro!]: "App (\<Lambda> x . t) s \<mapsto> t[x::=s]"
proof -
  obtain x'::name where s: "x' \<sharp> s" and t: "x' \<sharp> t"
    using ex_fresh[of "(s,t)"] by (auto simp add: fresh_prod)
  from t have "App (\<Lambda> x . t) s = App (\<Lambda> x' . ([(x,x')] \<bullet> t)) s" 
    by (simp add: alpha'')
  also from s have "\<dots> \<mapsto> ([(x, x')] \<bullet> t)[x'::=s]" ..
  also have "\<dots> = t[x::=s]" using t 
    by (auto simp add: subst_rename') (metis perm_swap)
  finally show ?thesis .
qed 
declare r3[rule del]


lemma r6'[intro]:
  fixes s :: trm 
  assumes r: "s \<mapsto> s'"
  shows "s to x in t \<mapsto> s' to x in t"
using assms
proof -
  obtain x'::name where s: "x' \<sharp> (s, s')" and t: "x' \<sharp> t"
    using ex_fresh[of "(s,s',t)"] by (auto simp add: fresh_prod)
  from t have "s to x in t = s to x' in ([(x,x')] \<bullet> t)"
    by (simp add: alpha'')
  also from s r have "\<dots> \<mapsto> s' to x' in ([(x, x')] \<bullet> t)" ..
  also from t have "\<dots> = s' to x in t"
    by (simp add: alpha'')
  finally show ?thesis .
qed
declare r6[rule del]

lemma r7'[intro]: 
  fixes t :: trm
  assumes "t \<mapsto> t'"
  shows "s to x in t \<mapsto> s to x in t'"
using assms
proof -
  obtain x'::name where f: "x' \<sharp> t"   "x' \<sharp> t'"   "x' \<sharp> s"   "x' \<sharp> x" 
    using ex_fresh[of "(t,t',s,x)"] by(auto simp add:fresh_prod)
  hence a: "s to x in t = s to x' in ([(x,x')] \<bullet> t)" 
    by (auto simp add: alpha'')
  from assms have "([(x,x')] \<bullet> t) \<mapsto> [(x,x')] \<bullet> t'" 
    by (simp add: eqvts)
  hence r: "s to x' in ([(x,x')] \<bullet> t) \<mapsto> s to x' in ([(x,x')] \<bullet> t')" 
    using f by auto 
  from f have "s to x in t' = s to x' in ([(x,x')] \<bullet> t')" 
    by (auto simp add: alpha'')
  with a r show ?thesis by (simp del: trm.inject)
qed
declare r7[rule del]

lemma r8'[intro!]: "[s] to x in t \<mapsto> t[x::=s]"
proof - 
  obtain x'::name where s: "x' \<sharp> s" and t: "x' \<sharp> t"
    using ex_fresh[of "(s,t)"] by (auto simp add: fresh_prod)
  from t have "[s] to x in t = [s] to x' in ([(x,x')] \<bullet> t)" 
    by (simp add: alpha'')
  also from s have "\<dots> \<mapsto> ([(x, x')] \<bullet> t)[x'::=s]" ..
  also have "\<dots> = t[x::=s]" using t 
    by (auto simp add: subst_rename') (metis perm_swap)
  finally show ?thesis .
qed
declare r8[rule del]

lemma r9'[intro!]: "s to x in [Var x] \<mapsto> s"
proof - 
  obtain x'::name where f: "x' \<sharp> s"   "x' \<sharp> x" 
    using ex_fresh[of "(s,x)"] by(auto simp add:fresh_prod)
  hence "s to x' in [Var x'] \<mapsto> s" by auto
  moreover have "s to x' in ([Var x']) = s to x in ([Var x])"
    by (auto simp add: alpha fresh_atm swap_simps)
  ultimately show ?thesis by simp
qed
declare r9[rule del]

text \<open>While discharging these freshness conditions is easy for rules involving
only one binder it unfortunately becomes quite tedious for the assoc rule
\isa{r10}. This is due to the complex binding structure of this rule which
includes \textit{four} binding occurrences of two different names. Furthermore,
the binding structure changes from the left to the right: On the left hand
side, $x$ is only bound in $t$, whereas on the right hand side the scope of $x$
extends over the whole term @{term "(t to y in u)"}.\<close>

lemma r10'[intro!]: 
  assumes xf: "x \<sharp> y"   "x \<sharp> u"
  shows "(s to x in t) to y in u \<mapsto> s to x in (t to y in u)"
proof -
  obtain y'::name \<comment> \<open>suitably fresh\<close>
    where y: "y' \<sharp> s"   "y' \<sharp> x"   "y' \<sharp> t"   "y' \<sharp> u" 
    using ex_fresh[of "(s,x,t,u,[(x, x')] \<bullet> t)"] 
    by (auto simp add: fresh_prod)
  obtain x'::name 
    where x: "x' \<sharp> s"   "x' \<sharp> y'"   "x' \<sharp> y"  "x' \<sharp> t"   "x' \<sharp> u"   
             "x' \<sharp> ([(y,y')] \<bullet> u)"
    using ex_fresh[of "(s,y',y,t,u,([(y,y')] \<bullet> u))"] 
    by (auto simp add: fresh_prod)
  from x y have yaux: "y' \<sharp> [(x, x')] \<bullet> t"
    by(simp add: fresh_left perm_fresh_fresh fresh_atm)
   have "(s to x in t) to y in u = (s to x in t) to y' in ([(y,y')] \<bullet> u)"
    using \<open>y' \<sharp> u\<close> by (simp add: alpha'')
  also have "\<dots> = (s to x' in ([(x,x')] \<bullet> t)) to y' in ([(y,y')] \<bullet> u)"
    using \<open>x' \<sharp> t\<close> by (simp add: alpha'')
  also have "\<dots> \<mapsto> s to x' in (([(x,x')] \<bullet> t) to y' in ([(y,y')] \<bullet> u))"
    using x y yaux by (auto simp add: fresh_prod) 
  also have " \<dots> = s to x' in (([(x,x')] \<bullet> t) to y in u)"
    using \<open>y' \<sharp> u\<close> by (simp add: abs_fun_eq1 alpha'')
  also have "\<dots> = s to x in (t to y in u)"
  proof (subst trm.inject)
    from xf x have swap: "[(x,x')] \<bullet> y = y"   "[(x,x')] \<bullet> u = u " 
      by(auto simp add: fresh_atm perm_fresh_fresh )
    with x show "s = s \<and> [x'].([(x, x')] \<bullet> t) to y in u = [x].t to y in u"
      by (auto simp add: alpha''[of x' _ x] abs_fresh abs_fun_eq1 swap)
  qed
  finally show ?thesis .
qed
declare r10[rule del]

text_raw \<open>\label{pg:alpha-end}\<close>

text \<open>Since now all the introduction rules of the vc-compatible reduction
relation exactly match their standard counterparts, both directions of the
adequacy proof are trivial inductions.\<close>

theorem adequacy: "s \<mapsto> t = s \<leadsto> t"
by (auto elim:reduction.induct std_reduction.induct)

text \<open>Next we show that the reduction relation preserves freshness and is in
turn preserved under substitution.\<close>

lemma reduction_fresh: 
  fixes x::"name"
  assumes r: "t \<mapsto> t'"
  shows "x \<sharp> t \<Longrightarrow> x \<sharp> t'"
using r
by(nominal_induct t t' avoiding: x rule: reduction.strong_induct)
    (auto simp add: abs_fresh fresh_fact fresh_atm)

lemma reduction_subst:
  assumes a: " t \<mapsto> t' "
  shows "t[x::=v] \<mapsto> t'[x::=v]"
using a
by(nominal_induct t t' avoiding: x v rule: reduction.strong_induct)
  (auto simp add: fresh_atm fresh_fact subst_lemma fresh_prod abs_fresh)


(*section {* Strong Normalization *}
text_raw {* \label{sec:SN-formal} *} *)

text \<open>Following \cite{SN.thy}, we use an inductive variant of strong
normalization, as it allows for inductive proofs on terms being strongly
normalizing, without establishing that
the reduction relation is finitely branching.\<close>   


inductive 
  SN :: "trm \<Rightarrow> bool"
where
  SN_intro: "(\<And> t' . t \<mapsto> t' \<Longrightarrow> SN t') \<Longrightarrow> SN t" 

(*
text {* It remains to be shown that this definition actually excludes infinite
sequences of reductions. We define a term $t$ to be diverging, written @{term
"DIV t"}, if there is some infinite sequence $S$ of reductions beginning at
$t$. *}

definition DIV :: "trm \<Rightarrow> bool"
where
  "DIV t \<equiv> \<exists> (S::nat \<Rightarrow> trm) .  t = S 0 \<and> (\<forall> n . S n \<mapsto> S (n + 1))"

theorem "SN t \<Longrightarrow> \<not> DIV t"
proof (induct rule:SN.induct)
  case (SN_intro t)
  have ih: "\<And>t'. t \<mapsto> t' \<Longrightarrow> \<not> DIV t'" by fact
  moreover have "DIV t \<Longrightarrow> \<exists> t' . t \<mapsto> t' \<and> DIV t'"
  proof -
    assume "DIV t" from this obtain S::"nat\<Rightarrow>trm" 
      where S: "t = S 0 \<and> (\<forall> n . S n \<mapsto> S (n + 1))"
      unfolding DIV_def .. 
    let ?t = "S 1" let ?S = "\<lambda> n . S (n + 1)"
    from S have " t \<mapsto> ?t" by auto
    moreover { 
      from S have "?t = ?S 0 \<and> (\<forall> n . ?S n \<mapsto> ?S (n + 1))" by auto
      hence "DIV ?t" unfolding DIV_def by auto}
    ultimately show ?thesis by blast
  qed
  ultimately show "\<not> DIV t" using ih by blast
qed


theorem "\<not> SN t \<Longrightarrow> DIV t"
proof -
  fix t assume t: "\<not> SN t"
  let ?NSN = "{ t . \<not> SN t }"
  have "\<forall> t \<in> ?NSN .  \<exists> t' . t \<mapsto> t' \<and> \<not> SN t'"
    by (auto intro: SN_intro)
  hence " \<exists> f . \<forall> t \<in> ?NSN . t \<mapsto> f t \<and> \<not> SN (f t)"
    by (rule bchoice)
  from this obtain f where f: "\<forall> t \<in> ?NSN . t \<mapsto> f t \<and> \<not> SN (f t)" ..
  let ?S = "\<lambda> n . (f^^n) t"
  { fix n from t f have  "?S n \<mapsto> ?S (n + 1) \<and> \<not> SN (?S (n + 1))"
      by (induct n) auto }
  hence "t = ?S 0 \<and> (\<forall> n . ?S n \<mapsto> ?S (n + 1))" by auto
  thus "DIV t" unfolding DIV_def  by(rule exI[where x="?S"])
qed

text{* For the normalization theorem, we merely need that strong normalization
is preserved under reduction and some lemmas on normal terms. *}
*)

lemma SN_preserved[intro]: 
  assumes a: "SN t"   "t \<mapsto> t'"
  shows "SN t'"
using a by (cases) (auto)

definition "NORMAL" :: "trm \<Rightarrow> bool"
where
  "NORMAL t \<equiv> \<not>(\<exists>t'. t \<mapsto> t')"

lemma normal_var: "NORMAL (Var x)"
unfolding NORMAL_def by (auto elim: reduction.cases)

lemma normal_implies_sn : "NORMAL s \<Longrightarrow> SN s"
unfolding NORMAL_def by(auto intro: SN_intro)

section \<open>Stacks\<close>
text_raw \<open>\label{sec:stacks}\<close>

text\<open>As explained in \cite{TT-lifting}, the monadic type structure of
the $\lambda_{ml}$-calculus does not lend itself to an easy definition of a
logical relation along the type structure of the calculus. Therefore, we need to
introduce stacks as an auxiliary notion to handle the monadic type constructor
$T$. Stacks can be thought of as lists of term abstractions @{term "[x].t"}. The
notation for stacks is chosen with this resemblance in mind.\<close>

nominal_datatype stack = Id | St "\<guillemotleft>name\<guillemotright>trm" "stack" ("[_]_\<ggreater>_")

lemma stack_exhaust :
  fixes c :: "'a::fs_name"
  shows "k = Id \<or> (\<exists> y n l  . y \<sharp> l \<and> y \<sharp> c \<and> k = [y]n\<ggreater>l)"
by(nominal_induct k avoiding: c rule: stack.strong_induct) (auto)

nominal_primrec 
  length :: "stack \<Rightarrow> nat" ( "|_|")
where
  "|Id| = 0" 
| "y \<sharp> L \<Longrightarrow> length ([y]n\<ggreater>L) = 1 + |L|"
by(finite_guess+,auto simp add: fresh_nat,fresh_guess)


text\<open>Together with the stack datatype, we introduce the notion of dismantling
a term onto a stack. Unfortunately, the dismantling operation has no easy
primitive recursive formulation. The Nominal package, however, only provides a
recursion combinator for primitive recursion. This means that for dismantling
one has to prove pattern completeness, right uniqueness, and termination
explicitly.\<close>

function
  dismantle :: "trm \<Rightarrow> stack \<Rightarrow> trm" ("_ \<star> _" [160,160] 160)
where
  "t \<star> Id = t" |
  "x \<sharp> (K,t) \<Longrightarrow> t \<star> ([x]s\<ggreater>K) = (t to x in s) \<star> K"
proof -    \<comment> \<open>pattern completeness\<close>
  fix P :: bool and arg::"trm \<times> stack"
  assume id: "\<And>t. arg = (t, stack.Id) \<Longrightarrow> P"
    and st: "\<And>x K t s. \<lbrakk>x \<sharp> (K, t); arg = (t, [x]s\<ggreater>K)\<rbrakk> \<Longrightarrow> P"
  { assume "snd arg = Id"
    hence P by (metis id[where t="fst arg"] surjective_pairing) }
  moreover 
  { fix y n L assume "snd arg = [y]n\<ggreater>L"   "y \<sharp> (L, fst arg)"
    hence P by (metis st[where t="fst arg"] surjective_pairing) }
  ultimately show P using stack_exhaust[of   "snd arg"   "fst arg"] by auto
next
    \<comment> \<open>right uniqueness\<close>
    \<comment> \<open>only the case of the second equation matching both args needs to be
shown.\<close>
  fix t t' :: trm and x x' :: name and s s' :: trm and K K' :: stack
  let ?g = dismantle_sumC \<comment> \<open>graph of dismantle\<close>
  assume "x \<sharp> (K, t)"   "x' \<sharp> (K', t')" 
    and  "(t, [x]s\<ggreater>K) = (t', [x']s'\<ggreater>K')"
  thus "?g (t to x in s, K) = ?g (t' to x' in s', K')" 
    by (auto intro!: arg_cong[where f="?g"] simp add: stack.inject)
qed (simp_all add: stack.inject) \<comment> \<open>all other cases are trivial\<close>

termination dismantle
by(relation "measure (\<lambda>(t,K). |K| )")(auto)

text\<open>Like all our constructions, dismantling is equivariant. Also, freshness
can be pushed over dismantling, and the freshness requirement in the second
defining equation is not needed\<close>

lemma dismantle_eqvt[eqvt]:
  fixes pi :: "(name \<times> name) list"
  shows "pi \<bullet> (t \<star> K) =  (pi \<bullet> t) \<star> (pi \<bullet> K)"
by(nominal_induct K avoiding: pi t rule:stack.strong_induct)
  (auto simp add: eqvts fresh_bij)

lemma dismantle_fresh[iff]:
  fixes  x :: name
  shows "(x \<sharp> (t \<star> k)) = (x \<sharp> t \<and> x \<sharp> k)"
by(nominal_induct k avoiding: t x rule: stack.strong_induct) 
  (simp_all)

lemma dismantle_simp[simp]: "s \<star> [y]n\<ggreater>L = (s to y in n) \<star> L"
proof - 
  obtain x::name where f: "x \<sharp> s"   "x \<sharp> L"   "x \<sharp> n"  
    using ex_fresh[of "(s,L,n)"] by(auto simp add:fresh_prod)
  hence t: "s to y in n = s to x in ([(y,x)] \<bullet> n)" 
    by(auto simp add: alpha'')
  from f have "[y]n\<ggreater>L = [x]([(y,x)] \<bullet> n)\<ggreater>L" 
    by (auto simp add: stack.inject alpha'')
  hence "s \<star> [y]n\<ggreater>L = s \<star> [x]([(y,x)] \<bullet> n)\<ggreater>L" by simp
  also have " \<dots> = (s to y in n) \<star> L" using f t by(simp del:trm.inject)
  finally show ?thesis .
qed


text \<open>We also need a notion of reduction on stacks. This reduction relation
allows us to define strong normalization not only for terms but also for stacks
and is needed to prove the properties of the logical relation later on.\<close>

definition stack_reduction :: "stack \<Rightarrow> stack \<Rightarrow> bool" (" _ \<mapsto> _ ")
where
  "k \<mapsto> k' \<equiv> \<forall> (t::trm) . (t \<star> k)  \<mapsto> (t \<star> k')" 


lemma stack_reduction_fresh:
  fixes k :: stack  and x :: name
  assumes r : "k \<mapsto> k'" and f :"x \<sharp> k"
  shows "x \<sharp> k'"
proof -
  from ex_fresh[of x] obtain z::name where f': "z \<sharp> x" ..
  from r have "Var z \<star> k \<mapsto> Var z \<star> k'" unfolding stack_reduction_def ..
  moreover from f f' have "x \<sharp> Var z \<star> k" by(auto simp add: fresh_atm)
  ultimately have "x \<sharp> Var z \<star> k'" by(rule reduction_fresh)
  thus "x \<sharp> k'" by simp
qed

lemma dismantle_red[intro]:
  fixes m :: trm
  assumes r: " m \<mapsto> m'"
  shows "m \<star> k \<mapsto> m' \<star> k"
using r
by (nominal_induct k avoiding: m m' rule:stack.strong_induct) auto


text \<open>Next we define a substitution operation for stacks. The main purpose of
this is to distribute substitution over dismantling.\<close>

nominal_primrec
  ssubst :: "name \<Rightarrow> trm \<Rightarrow> stack \<Rightarrow> stack" 
where
    "ssubst x v Id = Id"
  | " y \<sharp> (k,x,v)  \<Longrightarrow> ssubst x v ([y]n\<ggreater>k) = [y](n[x::=v])\<ggreater>(ssubst x v k)"
by(finite_guess+ , (simp add: abs_fresh)+ , fresh_guess+)

lemma ssubst_fresh:
  fixes y :: name
  assumes " y \<sharp> (x,v,k) "
  shows  "y \<sharp> ssubst x v k"
using assms
by(nominal_induct k avoiding: y x v rule: stack.strong_induct)
  (auto simp add: fresh_prod fresh_atm abs_fresh fresh_fact)

lemma ssubst_forget: 
  fixes x :: name
  assumes "x \<sharp> k"
  shows "ssubst x v k = k"
using assms
by(nominal_induct k avoiding: x v rule: stack.strong_induct)
  (auto simp add: abs_fresh fresh_atm forget)

lemma subst_dismantle[simp]: "(t \<star> k)[x ::= v] = (t[x::=v]) \<star> ssubst x v k"
by(nominal_induct k avoiding: t x v  rule: stack.strong_induct)
  (auto simp add: ssubst_fresh fresh_prod fresh_fact)

section \<open>Reducibility for Terms and Stacks\<close>
text_raw \<open>\label{sec:reducibility-formal}\<close>

text \<open>Following \cite{SN.thy}, we formalize the logical relation as a function
@{term "RED"} of type @{typ "ty \<Rightarrow> trm set"} for the term part and accordingly
@{term SRED} of type @{typ "ty \<Rightarrow> stack set"} for the stack part of the logical
relation.\<close>

lemma ty_exhaust: "ty = TBase \<or> (\<exists> \<sigma> \<tau> . ty = \<sigma> \<rightarrow> \<tau>) \<or> (\<exists> \<sigma> . ty = T \<sigma>)"
by(induct ty rule:ty.induct) (auto)

function RED :: "ty \<Rightarrow> trm set"
and     SRED :: "ty \<Rightarrow> stack set"
where
  "RED (TBase) = {t. SN(t)}"
| "RED (\<tau>\<rightarrow>\<sigma>) = {t. \<forall> u \<in> RED \<tau> . (App t u) \<in> RED \<sigma> }"
| "RED (T \<sigma>) = {t. \<forall> k \<in> SRED \<sigma> . SN(t \<star> k) }" 
| "SRED \<tau> = {k. \<forall> t \<in> RED \<tau> . SN ([t] \<star> k) }"
by(auto simp add: ty.inject, case_tac x rule: sum.exhaust,insert ty_exhaust)
  (blast)+

text \<open>This is the second non-primitive function in the formalization. Since
types do not involve binders, pattern completeness and right uniqueness are
mostly trivial. The termination argument is not as simple as for the dismantling
function, because the definiton of @{term "SRED \<tau>"} involves a recursive call to
@{term "RED \<tau>"} without reducing the size of @{term "\<tau>"}.\<close>

nominal_primrec
  tsize :: "ty \<Rightarrow> nat"
where
    "tsize TBase = 1"
  | "tsize (\<sigma>\<rightarrow>\<tau>) = 1 + tsize \<sigma> + tsize \<tau>"
  | "tsize (T \<tau>) = 1 + tsize \<tau>"
by (rule TrueI)+

text \<open>In the termination argument below, @{term "Inl \<tau>"} corresponds to the
call @{term "RED \<tau>"}, whereas @{term "Inr \<tau>"}  corresponds to @{term "SRED \<tau>"}
\<close>

termination RED
by(relation "measure 
    (\<lambda> x . case x of Inl \<tau> \<Rightarrow> 2 * tsize \<tau> 
                      | Inr \<tau> \<Rightarrow> 2 * tsize \<tau> + 1)") (auto)

section \<open>Properties of the Reducibility Relation\<close>

text \<open>After defining the logical relations we need to prove that the relation
implies strong normalization, is preserved under reduction, and satisfies the
head expansion property.\<close>

definition NEUT :: "trm \<Rightarrow> bool"
where
  "NEUT t \<equiv> (\<exists>a. t = Var a) \<or> (\<exists>t1 t2. t = App t1 t2)" 

definition "CR1" :: "ty \<Rightarrow> bool"
where
  "CR1 \<tau> \<equiv> \<forall>t. (t\<in>RED \<tau> \<longrightarrow> SN t)"

definition "CR2" :: "ty \<Rightarrow> bool"
where
  "CR2 \<tau> \<equiv> \<forall>t t'. (t\<in>RED \<tau> \<and> t \<mapsto> t') \<longrightarrow> t'\<in>RED \<tau>"

definition "CR3_RED" :: "trm \<Rightarrow> ty \<Rightarrow> bool"
where
  "CR3_RED t \<tau> \<equiv> \<forall>t'. t \<mapsto> t' \<longrightarrow>  t'\<in>RED \<tau>" 

definition "CR3" :: "ty \<Rightarrow> bool"
where
  "CR3 \<tau> \<equiv> \<forall>t. (NEUT t \<and> CR3_RED t \<tau>) \<longrightarrow> t\<in>RED \<tau>"
   
definition "CR4" :: "ty \<Rightarrow> bool"
where
  "CR4 \<tau> \<equiv> \<forall>t. (NEUT t \<and> NORMAL t) \<longrightarrow>t\<in>RED \<tau>"

lemma CR3_implies_CR4[intro]: "CR3 \<tau> \<Longrightarrow> CR4 \<tau>"
by (auto simp add: CR3_def CR3_RED_def CR4_def NORMAL_def)

lemma%invisible sub_induction: 
  assumes a: "SN(u)"
  and     b: "u\<in>RED \<tau>"
  and     c1: "NEUT t"
  and     c2: "CR2 \<tau>"
  and     c3: "CR3 \<sigma>"
  and     c4: "CR3_RED t (\<tau>\<rightarrow>\<sigma>)"
  shows "(App t u)\<in>RED \<sigma>"
using a b
proof(induct)
  fix u
  assume as: "u\<in>RED \<tau>"
  assume ih: " \<And>u'. \<lbrakk>u \<mapsto> u'; u' \<in> RED \<tau>\<rbrakk> \<Longrightarrow> App t u' \<in> RED \<sigma>"
  have "NEUT (App t u)" using c1 by (auto simp add: NEUT_def)
  moreover
  have "CR3_RED (App t u) \<sigma>" unfolding CR3_RED_def
  proof (intro strip)
    fix r
    assume red: "App t u \<mapsto> r"
    moreover
    { assume "\<exists>t'. t \<mapsto> t' \<and> r = App t' u"
      then obtain t' where a1: "t \<mapsto> t'" and a2: "r = App t' u" by blast
      have "t'\<in>RED (\<tau>\<rightarrow>\<sigma>)" using c4 a1 by (simp add: CR3_RED_def)
      then have "App t' u\<in>RED \<sigma>" using as by simp
      then have "r\<in>RED \<sigma>" using a2 by simp
    }
    moreover
    { assume "\<exists>u'. u \<mapsto> u' \<and> r = App t u'"
      then obtain u' where b1: "u \<mapsto> u'" and b2: "r = App t u'" by blast
      have "u'\<in>RED \<tau>" using as b1 c2 by (auto simp add: CR2_def)
      with ih have "App t u' \<in> RED \<sigma>" using b1 by simp
      then have "r\<in>RED \<sigma>" using b2 by simp
    }
    moreover
    { assume "\<exists>x t'. t = \<Lambda> x .t'"
      then obtain x t' where "t = \<Lambda> x .t'" by blast
      then have "NEUT (\<Lambda> x .t')" using c1 by simp
      then have "False" by (simp add: NEUT_def)
      then have "r\<in>RED \<sigma>" by simp
    }
    ultimately show "r \<in> RED \<sigma>" by (cases) (auto)
  qed
  ultimately show "App t u \<in> RED \<sigma>" using c3 by (simp add: CR3_def)
qed


inductive 
  FST :: "trm\<Rightarrow>trm\<Rightarrow>bool" (" _ \<guillemotright> _" [80,80] 80)
where
  fst[intro!]:  "(App t s) \<guillemotright> t"

lemma SN_of_FST_of_App: 
  assumes a: "SN (App t s)"
  shows "SN t"
proof - 
  from a have "\<forall>z. (App t s \<guillemotright> z) \<longrightarrow> SN z"
    by (induct rule: SN.induct)
       (blast elim: FST.cases intro: SN_intro)
  then show "SN t" by blast
qed

text \<open>The lemma above is a simplified version of the one used in
\cite{SN.thy}. Since we have generalized our notion of reduction from terms to
stacks, we can also generalize the notion of strong normalization. The new
induction principle will be used to prove the @{term "T"} case of the
properties of the reducibility relation.\<close>

inductive 
  SSN :: "stack \<Rightarrow> bool"
where
  SSN_intro: "(\<And> k' . k \<mapsto> k' \<Longrightarrow> SSN k') \<Longrightarrow> SSN k"

text \<open>Furthermore, the approach for deriving strong normalization of
subterms from above can be generalized to terms of the form @{term "t \<star> k"}. In
contrast to the case of applications, @{term "t \<star> k"} does \textit{not} uniquely
determine @{term t} and @{term k}. Thus, the extraction is a proper relation in
this case.\<close>

inductive
  SND_DIS :: "trm \<Rightarrow> stack \<Rightarrow> bool" ("_ \<rhd> _")
where
  snd_dis[intro!]: "t \<star> k \<rhd> k"

lemma SN_SSN:
  assumes a: "SN (t \<star> k)"
  shows " SSN k"
proof - 
  from a have "\<forall>z. (t \<star> k \<rhd> z) \<longrightarrow> SSN z"  by (induct rule: SN.induct)
       (metis SND_DIS.cases SSN_intro snd_dis stack_reduction_def)
  thus "SSN k" by blast
qed

text \<open>To prove CR1-3, the authors of
\cite{TT-lifting} use a case distinction on the reducts of @{term "t \<star> k"},
where $t$ is a neutral term and therefore no interaction occurs between $t$ and
$k$.

%auto generated stuff
\begin{isamarkuptext}%
\renewcommand\isacharquery{}
$$\inferrule{
    \isa{{\isacharquery}t\ {\isasymstar}\ {\isacharquery}k\ {\isasymmapsto}\
{\isacharquery}r}\\
    \isa{{\isasymAnd}t{\isacharprime}{\isachardot}\
{\isasymlbrakk}{\isacharquery}t\ {\isasymmapsto}\
t{\isacharprime}{\isacharsemicolon}\ {\isacharquery}r\ {\isacharequal}\
t{\isacharprime}\ {\isasymstar}\ {\isacharquery}k{\isasymrbrakk}\
{\isasymLongrightarrow}\ {\isacharquery}P}\\
    \isa{NEUT\ {\isacharquery}t}\\
    \isa{{\isasymAnd}k{\isacharprime}{\isachardot}\ {\isasymlbrakk}\
{\isacharquery}k\ {\isasymmapsto}\ k{\isacharprime}\ {\isacharsemicolon}\
{\isacharquery}r\ {\isacharequal}\ {\isacharquery}t\ {\isasymstar}\
k{\isacharprime}{\isasymrbrakk}\ {\isasymLongrightarrow}\ {\isacharquery}P}\\
    }{
    \isa{{\isacharquery}P}}$$%
\end{isamarkuptext}%\<close>

text \<open>We strive for a proof of this rule by structural induction on $k$. The
general idea of the case where @{term "k = [y]n\<ggreater>l"} is to move the first stack
frame into the term $t$ and then apply the induction hypothesis as a case
rule. Unfortunately, this term is no longer neutral, so, for the induction to go
through, we need to generalize the claim to also include the possible
interactions of non-neutral terms and stacks.\<close>


lemma dismantle_cases:
  fixes t :: trm
  assumes r: "t \<star> k \<mapsto> r"
  and T: "\<And> t' . \<lbrakk> t \<mapsto> t' ; r = t' \<star> k \<rbrakk> \<Longrightarrow> P"
  and K: "\<And> k' . \<lbrakk> k \<mapsto> k' ; r = t \<star> k' \<rbrakk> \<Longrightarrow> P" 
  and B: "\<And> s y n l .\<lbrakk> t = [s] ; k = [y]n\<ggreater>l ; r = (n[y::=s]) \<star> l \<rbrakk> \<Longrightarrow> P"
  and A: "\<And> u x v y n l.\<lbrakk> x \<sharp> y; x \<sharp> n ; t = u to x in v ; 
             k = [y]n\<ggreater>l ; r = (u to x in (v to y in n)) \<star> l \<rbrakk> \<Longrightarrow> P "
  shows "P"
using assms
proof (nominal_induct k avoiding: t r rule:stack.strong_induct)
  case (St y n L) note  yfresh = \<open>y \<sharp> t\<close> \<open>y \<sharp> r\<close> \<open>y \<sharp> L\<close> 
  note IH = St(4) 
    and T = St(6) and K = St(7) and B = St(8) and A = St(9) 
  thus "P" proof (cases rule:IH[where b="t to y in n" and ba="r"])
    case (2 r') have red: "t to y in n \<mapsto> r'" and r: " r = r' \<star> L" by fact+
txt \<open>If @{term "m to y in n"} makes a step we reason by case distinction      
on the successors of @{term "m to y in n"}. We want to use the strong inversion
principle for the reduction relation. For this we need that $y$ is fresh for
@{term "t to y in n"} and $r'$.\<close>
    from yfresh r have y: "y \<sharp>  t to y in n"   "y \<sharp> r'" 
      by (auto simp add: abs_fresh)
    obtain z where z: "z \<noteq> y"   "z \<sharp> r'"   "z \<sharp> t to y in n" 
      using ex_fresh[of "(y,r',t to y in n)"] 
      by(auto simp add:fresh_prod fresh_atm)
    from red  r show "P" 
    proof (cases rule:reduction.strong_cases
        [ where x="y"and xa="y" and xb="y" and xc="y" and xd="y" 
          and xe="y" and xf="y" and xg="z" and y="y"])
      case (r6 s t' u) \<comment> \<open>if $t$ makes a step we use assumption T\<close>
      with y have m: "t \<mapsto> t'"   "r' = t' to y in n" by auto
      thus "P" using T[of t'] r by auto
    next
      case (r7 _ _ n') with y have n: "n \<mapsto> n'" and r': "r' = t to y in n'"
        by (auto simp add: alpha)
      txt \<open>Since @{term "k = [y]n\<ggreater>L"}, the reduction @{thm n} occurs within
        the stack $k$. Hence, we need to establish this stack reduction.\<close>
      have "[y]n\<ggreater>L \<mapsto> [y]n'\<ggreater>L" unfolding stack_reduction_def
      proof 
        fix u have "u to y in n \<mapsto> u to y in n'" using n .. 
        hence "(u to y in n) \<star> L \<mapsto> (u to y in n') \<star> L" ..
        thus " u \<star> [y]n\<ggreater>L \<mapsto> u \<star> [y]n'\<ggreater>L" 
          by simp
      qed
      moreover have "r = t \<star> [y]n'\<ggreater>L" using r r' by simp
      ultimately show "P" by (rule K)
    next 
      case (r8 s _) \<comment> \<open>the case of a $\beta$-reduction is exactly B\<close>
      with y have "t = [s]"   "r' = n[y::=s]" by(auto simp add: alpha) 
      thus "P" using B[of "s" "y" "n" "L"] r by auto 
    next 
      case (r9 _) \<comment> \<open>The case of an $\eta$-reduction is a stack
reduction as well.\<close>
      with y have n: "n = [Var y]" and r': "r' = t" 
        by(auto simp add: alpha)
      { fix u have "u to y in n \<mapsto> u" unfolding n ..
        hence "(u to y in n) \<star> L \<mapsto> u \<star> L " ..
        hence "u \<star> [y]n\<ggreater>L \<mapsto> u \<star> L" by simp
      } hence "[y]n\<ggreater>L \<mapsto> L" unfolding stack_reduction_def ..
      moreover have "r = t \<star> L" using r r' by simp
      ultimately show "P" by (rule K)
    next
      case (r10 u _ v) \<comment> \<open>The assoc case holds by A.\<close>
      with y z have 
        "t = (u to z in v)" 
        "r' = u to z in (v to y in n)" 
        "z \<sharp> (y,n)" by (auto simp add: fresh_prod alpha)
      thus "P" using A[of z y n] r by auto
    qed (insert y, auto)  \<comment> \<open>No other reductions are possible.\<close>
  next 
    txt \<open>Next we have to solve the case where a reduction occurs deep within
$L$. We get a reduction of the stack $k$ by moving the first stack frame
``[y]n'' back to the right hand side of the dismantling operator.\<close>
    case (3 L')
    hence L: "L \<mapsto> L'" and  r: "r = (t to y in n) \<star> L'" by auto
    { fix s from L have  "(s to y in n) \<star> L \<mapsto> (s to y in n) \<star> L'" 
        unfolding stack_reduction_def ..
      hence "s \<star> [y]n\<ggreater>L \<mapsto> s \<star> [y]n\<ggreater>L'" by simp
    } hence "[y]n\<ggreater>L \<mapsto> [y]n\<ggreater>L'" unfolding stack_reduction_def by auto
    moreover from r have "r = t \<star> [y]n\<ggreater>L'" by simp
    ultimately show "P" by (rule K) 
  next
    case (5 x z n' s v K) \<comment> \<open>The ``assoc'' case is again a stack reduction\<close>
    have xf: "x \<sharp> z"   "x \<sharp> n'" 
      \<comment> \<open>We get the following equalities\<close>
    and red: "t to y in n = s to x in v"
             "L = [z]n'\<ggreater>K"
             "r = (s to x in v to z in n') \<star> K" by fact+
    { fix u from red have "u \<star> [y]n\<ggreater>L = ((u to x in v) to z in n') \<star> K "
        by(auto intro: arg_cong[where f="\<lambda> x . x \<star> K"])
      moreover 
      { from xf have "(u to x in v) to z in n' \<mapsto> u to x in (v to z in n')" ..
        hence "((u to x in v) to z in n') \<star> K \<mapsto> (u to x in (v to z in n')) \<star> K"
          by rule 
      } ultimately  have "u \<star> [y]n\<ggreater>L \<mapsto> (u to x in (v to z in n')) \<star> K" 
        by (simp (no_asm_simp) del:dismantle_simp)
      hence "u \<star> [y]n\<ggreater>L \<mapsto> u \<star> [x](v to z in n')\<ggreater>K" by simp
    } hence "[y]n\<ggreater>L \<mapsto>  [x](v to z in n')\<ggreater> K" 
      unfolding stack_reduction_def by simp
    moreover have "r = t \<star> ([x](v to z in n')\<ggreater>K)" using red 
      by (auto)
    ultimately show "P" by (rule K)
  qed (insert St, auto )
qed auto

text \<open>Now that we have established the general claim, we can restrict $t$ to
neutral terms only and drop the cases dealing with possible interactions.\<close>

lemma dismantle_cases'[consumes 2, case_names T K]:
  fixes m :: trm
  assumes r: "t \<star> k \<mapsto> r"
  and "NEUT t"
  and "\<And> t' . \<lbrakk> t \<mapsto> t' ; r = t' \<star> k \<rbrakk> \<Longrightarrow> P"
  and "\<And> k' . \<lbrakk> k \<mapsto> k' ; r = t \<star> k' \<rbrakk> \<Longrightarrow> P" 
  shows "P"  
using assms unfolding NEUT_def
by (cases rule: dismantle_cases[of t k r]) (auto) 

lemma red_Ret:
  fixes t :: trm
  assumes "[s] \<mapsto> t"
  shows " \<exists> s' . t = [s'] \<and> s  \<mapsto> s'"
using assms by cases (auto)

lemma SN_Ret: "SN u \<Longrightarrow> SN [u]"
by(induct rule:SN.induct) (metis SN.intros red_Ret)

text \<open>All the properties of reducibility are shown simultaneously by induction
on the type. Lindley and Stark \cite{TT-lifting} only spell out the cases
dealing with the monadic type constructor $T$. We do the same by reusing the
proofs from \cite{SN.thy} for the other cases. To shorten the presentation,
these proofs are omitted\<close>
    
lemma RED_props: 
  shows "CR1 \<tau>" and "CR2 \<tau>" and "CR3 \<tau>"
proof (nominal_induct \<tau> rule: ty.strong_induct)
  case TBase {%invisible case 1 show "CR1 TBase" 
      by (simp add: CR1_def)
  next
    case 2 show "CR2 TBase" 
      by (auto intro: SN_preserved simp add: CR2_def)
  next
    case 3 show "CR3 TBase" 
      by (auto intro: SN_intro simp add: CR3_def CR3_RED_def)
  }
next
  case (TFun \<tau>1 \<tau>2) {%invisible case 1
    have ih_CR3_\<tau>1: "CR3 \<tau>1" by fact
    have ih_CR1_\<tau>2: "CR1 \<tau>2" by fact
    have "\<And>t. t \<in> RED (\<tau>1 \<rightarrow> \<tau>2) \<Longrightarrow> SN t" 
    proof - 
      fix t
      assume "t \<in> RED (\<tau>1 \<rightarrow> \<tau>2)"
      then have a: "\<forall>u. u \<in> RED \<tau>1 \<longrightarrow> App t u \<in> RED \<tau>2" by simp
      from ih_CR3_\<tau>1 have "CR4 \<tau>1" by (simp add: CR3_implies_CR4) 
      moreover
      fix a have "NEUT (Var a)" by (force simp add: NEUT_def)
      moreover
      have "NORMAL (Var a)" by (rule normal_var)
      ultimately have "(Var a)\<in> RED \<tau>1" by (simp add: CR4_def)
      with a have "App t (Var a) \<in> RED \<tau>2" by simp
      hence "SN (App t (Var a))" using ih_CR1_\<tau>2 by (simp add: CR1_def)
      thus "SN t" by (auto dest: SN_of_FST_of_App)
    qed
    then show "CR1 (\<tau>1 \<rightarrow> \<tau>2)" unfolding CR1_def by simp
  next
    case 2
    have ih_CR2_\<tau>2: "CR2 \<tau>2" by fact
    then show "CR2 (\<tau>1 \<rightarrow> \<tau>2)" unfolding CR2_def by auto 
  next
    case 3
    have ih_CR1_\<tau>1: "CR1 \<tau>1" by fact
    have ih_CR2_\<tau>1: "CR2 \<tau>1" by fact
    have ih_CR3_\<tau>2: "CR3 \<tau>2" by fact
    show "CR3 (\<tau>1 \<rightarrow> \<tau>2)" unfolding CR3_def
    proof (simp, intro strip)
      fix t u
      assume a1: "u \<in> RED \<tau>1"
      assume a2: "NEUT t \<and> CR3_RED t (\<tau>1 \<rightarrow> \<tau>2)"
      have "SN(u)" using a1 ih_CR1_\<tau>1 by (simp add: CR1_def)
      then show "(App t u)\<in>RED \<tau>2" 
        using ih_CR2_\<tau>1 ih_CR3_\<tau>2 a1 a2 by (blast intro: sub_induction)
    qed
  }
next
  case (T \<sigma>)
  { case 1 \<comment> \<open>follows from the fact that @{term "Id \<in> SRED \<sigma>"}\<close>
    have ih_CR1_\<sigma>: "CR1 \<sigma>" by fact
    { fix t assume t_red: "t \<in> RED (T \<sigma>)"
      { fix s assume "s \<in> RED \<sigma>" 
        hence "SN s" using ih_CR1_\<sigma> by (auto simp add: CR1_def)
        hence "SN ([s])" by (rule SN_Ret)
        hence "SN ([s] \<star> Id)" by simp
      } hence "Id \<in> SRED \<sigma>" by simp
      with t_red have "SN (t)" by (auto simp del: SRED.simps)
    } thus "CR1 (T \<sigma>)" unfolding CR1_def by blast
  next
    case 2 \<comment> \<open>follows since \isa{SN} is preserved under redcution\<close>
    { fix t t'::trm  assume t_red: "t \<in> RED (T \<sigma>)" and t_t': "t \<mapsto> t'" 
      { fix k assume k: "k \<in> SRED \<sigma>"
        with t_red have "SN(t \<star> k)" by simp
        moreover from t_t' have "t \<star> k \<mapsto> t' \<star> k" ..
        ultimately have "SN(t' \<star> k)" by (rule SN_preserved) 
      } hence "t' \<in> RED (T \<sigma>)"  by (simp del: SRED.simps)
    } thus "CR2 (T \<sigma>)"unfolding CR2_def by blast
  next
    case 3 from \<open>CR3 \<sigma>\<close> have ih_CR4_\<sigma> : "CR4 \<sigma>" ..
    { fix t assume t'_red: "\<And> t' . t \<mapsto> t' \<Longrightarrow> t' \<in> RED (T \<sigma>)" 
      and neut_t: "NEUT t"
      { fix k assume k_red: "k \<in> SRED \<sigma>" 
        fix x have "NEUT (Var x)" unfolding NEUT_def by simp 
        hence "Var x \<in> RED \<sigma>" using normal_var ih_CR4_\<sigma> 
          by (simp add: CR4_def)
        hence "SN ([Var x] \<star> k)" using k_red by simp
        hence "SSN k" by (rule SN_SSN)
        then have "SN (t \<star> k)" using k_red
        proof (induct k rule:SSN.induct)
          case (SSN_intro k)
          have ih : "\<And>k'. \<lbrakk> k \<mapsto> k' ; k' \<in> SRED \<sigma> \<rbrakk>  \<Longrightarrow> SN (t \<star> k')"
            and k_red: "k \<in> SRED \<sigma>" by fact+
          { fix r assume r: "t \<star> k \<mapsto> r"
            hence "SN r" using neut_t
            proof (cases rule:dismantle_cases')
              case (T t') hence t_t': "t \<mapsto> t'" and r_def: "r = t' \<star> k" . 
              from t_t' have "t' \<in> RED (T \<sigma>)" by (rule t'_red)
              thus "SN r" using k_red r_def by simp
            next
              case (K k') hence k_k': "k \<mapsto> k'" and r_def: "r = t \<star> k'" .
              { fix s assume "s \<in> RED \<sigma>" 
                hence "SN ([s] \<star> k)" using k_red
                  by simp
                moreover have "[s] \<star> k \<mapsto> [s] \<star> k'"
                  using k_k' unfolding stack_reduction_def ..   
                ultimately have "SN ([s] \<star> k')" ..
              } hence "k' \<in> SRED \<sigma>" by simp
              with k_k' show "SN r" unfolding r_def by (rule ih)
            qed } thus "SN (t \<star> k)" .. 
        qed } hence "t \<in> RED (T \<sigma>)" by simp
    } thus "CR3 (T \<sigma>)" unfolding CR3_def CR3_RED_def by blast
  }
qed

text \<open>The last case above shows that, once all the reasoning principles have
been established, some proofs have a formalization which is amazingly close to
the informal version. For a direct comparison, the informal proof is presented
in Figure~\ref{fig:cr3}.\<close>

text_raw \<open>\input{figureCR3}\<close>

text \<open>Now that we have established the properties of the reducibility
relation, we need to show that reducibility is preserved by the various term
constructors. The only nontrivial cases are abstraction and sequencing.\<close>

section \<open>Abstraction Preserves Reducibility\<close>    

text \<open>Once again we could reuse the proofs from \cite{SN.thy}. The proof uses
the \isa{double-SN} rule and the lemma \isa{red-Lam} below. Unfortunately, this
time the proofs are not fully identical to the proofs in \cite{SN.thy} because
we consider $\beta\eta$-reduction rather than $\beta$-reduction only. However,
the differences are only minor.\<close>
    
lemma%invisible double_SN_aux:
  assumes a: "SN a"
  and b: "SN b"
  and hyp: "\<And>x z.
    \<lbrakk>\<And>y. x \<mapsto> y \<Longrightarrow> SN y; \<And>y. x \<mapsto> y \<Longrightarrow> P y z;
     \<And>u. z \<mapsto> u \<Longrightarrow> SN u; \<And>u. z \<mapsto> u \<Longrightarrow> P x u\<rbrakk> \<Longrightarrow> P x z"
  shows "P a b"
proof -
  from a
  have r: "\<And>b. SN b \<Longrightarrow> P a b"
  proof (induct a rule: SN.induct)
    case (SN_intro x)
    note SNI' = SN_intro
    have "SN b" by fact
    thus ?case
    proof (induct b rule: SN.induct)
      case (SN_intro y)
      show ?case
        apply (rule hyp)
        apply (erule SNI')
        apply (erule SNI')
        apply (rule SN.SN_intro)
        apply (erule SN_intro)+
        done
    qed
  qed
  from b show ?thesis by (rule r)
qed

lemma double_SN[consumes 2]:
  assumes a: "SN a"
  and     b: "SN b" 
  and     c: "\<And>(x::trm) (z::trm). 
             \<lbrakk>\<And>y. x \<mapsto> y \<Longrightarrow> P y z; \<And>u. z \<mapsto> u \<Longrightarrow> P x u\<rbrakk> \<Longrightarrow> P x z"
  shows "P a b"
using a b c
by%invisible (blast intro: double_SN_aux)

lemma red_Lam:
  assumes a: "\<Lambda> x . t \<mapsto> r" 
  shows " (\<exists>t'. r = \<Lambda> x . t' \<and> t \<mapsto> t') \<or> (t = App r (Var x) \<and> x \<sharp> r ) "
proof -
  obtain z::name where z: "z \<sharp> x"   "z \<sharp> t"   "z \<sharp> r" 
    using ex_fresh[of "(x,t,r)"] by (auto simp add: fresh_prod)
  have "x \<sharp> \<Lambda> x . t" by (simp add: abs_fresh)
  with a have "x \<sharp> r" by (simp add: reduction_fresh)
  with a show ?thesis using z
    by(cases rule: reduction.strong_cases
       [where x ="x" and xa="x" and xb="x" and xc="x" and 
              xd="x" and xe="x" and xf="x" and xg="x" and y="z"])
        (auto simp add: abs_fresh alpha fresh_atm)
qed

lemma abs_RED: 
  assumes asm: "\<forall>s\<in>RED \<tau>. t[x::=s]\<in>RED \<sigma>"
  shows "\<Lambda> x . t \<in>RED (\<tau>\<rightarrow>\<sigma>)"
proof %invisible -
  have b1: "SN t" 
  proof -
    have "Var x\<in>RED \<tau>"
    proof -
      have "CR4 \<tau>" by (simp add: RED_props CR3_implies_CR4)
      moreover
      have "NEUT (Var x)" by (auto simp add: NEUT_def)
      moreover
      have "NORMAL (Var x)" by (rule normal_var) 
      ultimately show "Var x\<in>RED \<tau>" by (simp add: CR4_def)
    qed
    then have "t[x::=Var x]\<in>RED \<sigma>" using asm by simp
    then have "t\<in>RED \<sigma>" by (simp add: id_subs)
    moreover 
    have "CR1 \<sigma>" by (simp add: RED_props)
    ultimately show "SN t" by (simp add: CR1_def)
  qed
  show "\<Lambda> x .t\<in>RED (\<tau>\<rightarrow>\<sigma>)"
  proof (simp, intro strip)
    fix u
    assume b2: "u\<in>RED \<tau>"
    then have b3: "SN u" using RED_props by (auto simp add: CR1_def)
    show "App (\<Lambda> x .t) u \<in> RED \<sigma>" using b1 b3 b2 asm
    proof(induct t u rule: double_SN)
      fix t u
      assume ih1: "\<And>t'.  \<lbrakk>t \<mapsto> t'; u\<in>RED \<tau>; \<forall>s\<in>RED \<tau>. t'[x::=s]\<in>RED \<sigma>\<rbrakk> \<Longrightarrow> App (\<Lambda> x
.t') u \<in>
RED \<sigma>" 
      assume ih2: "\<And>u'.  \<lbrakk>u \<mapsto> u'; u'\<in>RED \<tau>; \<forall>s\<in>RED \<tau>. t[x::=s]\<in>RED \<sigma>\<rbrakk> \<Longrightarrow> App (\<Lambda> x
.t) u' \<in>
RED \<sigma>"
      assume as1: "u \<in> RED \<tau>"
      assume as2: "\<forall>s\<in>RED \<tau>. t[x::=s]\<in>RED \<sigma>"
      have "CR3_RED (App (\<Lambda> x. t) u) \<sigma>" unfolding CR3_RED_def
      proof(intro strip)
        fix r
        assume red: "App (\<Lambda> x .t) u \<mapsto> r"
        moreover
        { assume "\<exists>t'. t \<mapsto> t' \<and> r = App (\<Lambda> x . t') u"
          then obtain t' where a1: "t \<mapsto> t'" and a2: "r = App (\<Lambda> x .t') u" by
blast
          have "App (\<Lambda> x .t') u\<in>RED \<sigma>" using ih1 a1 as1 as2
            apply(auto)
            apply(drule_tac x="t'" in meta_spec)
            apply(simp)
            apply(drule meta_mp)
            prefer 2
            apply(auto)[1]
            apply(rule ballI)
            apply(drule_tac x="s" in bspec)
            apply(simp)
            apply(subgoal_tac "CR2 \<sigma>")(*A*)
            apply(unfold CR2_def)[1]
            apply(drule_tac x="t[x::=s]" in spec)
            apply(drule_tac x="t'[x::=s]" in spec)
            apply(simp add: reduction_subst)
            (*A*)
            apply(simp add: RED_props)
            done
          then have "r\<in>RED \<sigma>" using a2 by simp
        } note rt = this
        moreover
        { assume "\<exists>u'. u \<mapsto> u' \<and> r = App (\<Lambda> x . t) u'"
          then obtain u' where b1: "u \<mapsto> u'" and b2: "r = App (\<Lambda> x .t) u'" by
blast
          have "App (\<Lambda> x .t) u'\<in>RED \<sigma>" using ih2 b1 as1 as2
            apply(auto)
            apply(drule_tac x="u'" in meta_spec)
            apply(simp)
            apply(drule meta_mp)
            apply(subgoal_tac "CR2 \<tau>")
            apply(unfold CR2_def)[1]
            apply(drule_tac x="u" in spec)
            apply(drule_tac x="u'" in spec)
            apply(simp)
            apply(simp add: RED_props)
            apply(simp)
            done
          then have "r\<in>RED \<sigma>" using b2 by simp
        } note ru= this
        moreover
        { assume "r = t[x::=u]"
          then have "r\<in>RED \<sigma>" using as1 as2 by auto
        } note r = this
        
        ultimately show "r \<in> RED \<sigma>" 
          (* one wants to use the strong elimination principle; for this one 
             has to know that x\<sharp>u *)
        apply(cases) 
        apply(auto)
        apply(drule red_Lam)
        apply(drule disjE)prefer 3 apply simp
        apply(auto)[1]
        prefer 2
        apply(auto simp add: alpha subst_rename')[1]
        apply(subgoal_tac "App s' u = t[x::=u]")
        apply(auto)
        apply(auto simp add: forget)
        done
    qed
    moreover 
    have "NEUT (App (\<Lambda> x . t) u)" unfolding NEUT_def by (auto)
    ultimately show "App (\<Lambda> x . t) u \<in> RED \<sigma>"  using RED_props by (simp add:
CR3_def)
  qed
qed
qed


section \<open>Sequencing Preserves Reducibility\<close>

text \<open>This section corresponds to the main part of the paper being formalized
and as such deserves special attention. In the lambda case one has to formalize
doing induction on $\max(s) + max(t)$ for two strongly normalizing terms $s$ and
$t$ (cf. \cite[Section 6.3]{proofs+types}). Above, this was done through a
\isa{double-SN}
rule. The central Lemma 7 of Lindley and Stark's paper uses an even more
complicated induction scheme. They assume terms $p$ and $n$ as well as a stack
$K$ such that @{term "SN(p)"} and @{term "SN(n[x::=p] \<star> K)"}. The induction is
then done on $|K| + max(n \star K) + max(p)$. See Figure~\ref{fig:lemma7} in
for details.\<close>

text_raw \<open>\input{figureLemma7}\<close>


text \<open>Since we have settled for a different characterization of strong
normalization, we have to derive an induction principle similar in spirit to the
\isa{double-SN} rule. 

Furthermore, it turns out that it is not necessary to formalize the fact that
stack reductions do not increase the length of the stack.\footnote{This
possibility was only discovered \textit{after} having formalized $ K \mapsto K'
\Rightarrow |K| \geq |K'|$. The proof of this seemingly simple fact
was about 90 lines of Isar code.} Doing induction on the sum above, this is
necessary to handle the case of a reduction occurring in $K$. We differ
from \cite{TT-lifting} and establish an induction principle which to some extent
resembles the lexicographic order on $$(\SN,\mapsto) \times (\SN,\mapsto) \times
(\N,>)\,.$$\<close>

lemma triple_induct[consumes 2]: 
  assumes a: "SN (p)"
  and b: "SN (q)"
  and hyp: "\<And> (p::trm) (q::trm) (k::stack) . 
  \<lbrakk> \<And> p' . p \<mapsto> p' \<Longrightarrow> P p' q k ; 
    \<And> q' k . q \<mapsto> q' \<Longrightarrow> P p q' k; 
    \<And> k' .  |k'| < |k| \<Longrightarrow> P p q k' \<rbrakk> \<Longrightarrow> P p q k "
  shows "P p q k"
proof -
  from a have "\<And>q K . SN q \<Longrightarrow> P p q K"
  proof (induct p)
    case (SN_intro p) 
    have sn1: "\<And> p' q K . \<lbrakk>p \<mapsto> p'; SN q\<rbrakk> \<Longrightarrow> P p' q K" by fact
    have sn_q: "SN q"   "SN q" by fact+
    thus "P p q K"
    proof (induct q arbitrary: K) 
      case (SN_intro q K)
      have sn2: "\<And> q' K . \<lbrakk>q \<mapsto> q'; SN q'\<rbrakk> \<Longrightarrow> P p q' K" by fact
      show "P p q K"
      proof (induct K rule: measure_induct_rule[where f="length"])
        case (less k)
        have le: "\<And> k' . |k'| < |k| \<Longrightarrow> P p q k'" by fact
        { fix p' assume "p \<mapsto> p'"
          moreover have "SN q" by fact
          ultimately have "P p' q k" using sn1 by auto }
        moreover
        { fix q' K  assume r: "q \<mapsto> q'" 
          have "SN q" by fact
          hence "SN q'" using r by (rule SN_preserved)
          with r have "P p q' K" using sn2 by auto }
        ultimately show ?case using le
          by (auto intro:hyp)
      qed
    qed
  qed 
  with b show ?thesis by blast
qed


text \<open>Here we strengthen the case rule for terms of the form @{term "t \<star> k \<mapsto>
r"}. The freshness requirements on $x$,$y$, and $z$
correspond to those for the rule \isa{reduction.strong-cases}, the strong
inversion principle for the reduction relation.\<close>


lemma dismantle_strong_cases:
  fixes t :: trm
  assumes r: "t \<star> k \<mapsto> r"
  and f: "y \<sharp> (t,k,r)"   "x \<sharp> (z,t,k,r)"   "z \<sharp> (t,k,r)"
  and T: "\<And> t' . \<lbrakk> t \<mapsto> t' ; r = t' \<star> k \<rbrakk> \<Longrightarrow> P"
  and K: "\<And> k' . \<lbrakk> k \<mapsto> k' ; r = t \<star> k' \<rbrakk> \<Longrightarrow> P" 
  and B: "\<And> s n l . \<lbrakk> t = [s] ; 
                       k = [y]n\<ggreater>l ; r = (n[y::=s]) \<star> l \<rbrakk> \<Longrightarrow> P "
  and A: "\<And> u v n l . 
           \<lbrakk> x \<sharp> (z,n); t = u to x in v ; k = [z]n\<ggreater>l ; 
             r = (u to x in (v to z in n)) \<star> l \<rbrakk> \<Longrightarrow> P "
  shows "P"
proof (cases rule:dismantle_cases[of t k r P])
  case (4 s y' n L) have ch:
    "t = [s]"
    "k = [y']n\<ggreater>L"
    "r = n[y'::=s] \<star> L" by fact+
  txt \<open>The equations we get look almost like those we need to instantiate the
hypothesis \isa{B}. The only difference is that \isa{B} only applies to $y$, and
since we want $y$ to become an instantiation variable of the strengthened rule,
we only know that $y$ satisfies \isa{f} and nothing else. But the condition
\isa{f} is just strong enough to rename $y'$ to $y$ and apply \isa{B}.\<close>
  with f have "y = y' \<or> y \<sharp> n" 
    by (auto simp add: fresh_prod abs_fresh)
  hence "n[y'::=s] = ([(y,y')] \<bullet> n)[y::=s]" 
    and "[y']n\<ggreater>L = [y]([(y,y')] \<bullet> n)\<ggreater>L"
    by(auto simp add: name_swap_bij subst_rename' stack.inject alpha' )
  with ch have "t = [s]" 
    "k = [y]([(y,y')] \<bullet> n)\<ggreater>L" 
    "r = ([(y,y')] \<bullet> n)[y::=s] \<star> L"
    by (auto)
  thus "P" by (rule B) 
next 
  case (5 u x' v z' n L) have ch:
    "x' \<sharp> z'"   "x' \<sharp> n"
    "t = u to x' in v"
    "k = [z']n\<ggreater>L"
    "r = (u to x' in v to z' in n) \<star> L" by fact+ 
  txt \<open>We want to do the same trick as above but at this point we have to take
care of the possibility that $x$ might coincide with $x'$ or $z'$. Similarly,
$z$
might coincide with $z'$.\<close>
  with f have x: "x = x' \<or> x \<sharp> v to z' in n" 
    and z: "z = z' \<or> z \<sharp> n"
    by (auto simp add: fresh_prod abs_fresh)
  from f ch have x': "x' \<sharp> n"   " x' \<sharp> z'" 
    and xz': "x = z' \<or> x \<sharp> n" 
    by (auto simp add:name_swap_bij alpha fresh_prod fresh_atm abs_fresh)
  from f ch have "x \<sharp> z" "x \<sharp> [z'].n" by (auto simp add:  fresh_prod)
  with xz' z have  " x \<sharp> (z , ([(z, z')] \<bullet> n))" 
    by (auto simp add: fresh_atm fresh_bij name_swap_bij 
          fresh_prod abs_fresh calc_atm fresh_aux fresh_left)
  moreover from x ch have "t = u to x in ([(x,x')] \<bullet> v)" 
    by (auto simp add:name_swap_bij alpha')
  moreover from z ch have "k = [z]([(z,z')] \<bullet> n)\<ggreater>L"
    by (auto simp add:name_swap_bij stack.inject alpha')
  txt \<open>The first two $\alpha$-renamings are simple, but here we have to handle
the nested binding structure of the assoc rule. Since $x$ scopes over the whole
term @{term "(v to z' in n)" }, we have to push the swapping over $z'$\<close>
  moreover { from x have 
    "u to x' in (v to z' in n) = u to x in ([(x,x')] \<bullet> (v to z' in n))"
      by (auto simp add:name_swap_bij alpha' simp del: trm.perm)
    also from xz' x' have "\<dots> = u to x in (([(x,x')] \<bullet> v) to z' in n)"
      by (auto simp add: abs_fun_eq1 swap_simps alpha'') 
           (metis alpha'' fresh_atm perm_fresh_fresh swap_simps(1) x')
    also from z have " \<dots> = u to x in (([(x,x')] \<bullet> v) to z in ([(z,z')] \<bullet> n))"
      by (auto simp add: abs_fun_eq1 alpha' name_swap_bij )
    finally 
      have "r =  (u to x in (([(x, x')] \<bullet> v) to z in ([(z, z')] \<bullet> n))) \<star> L" 
        using ch by (simp del: trm.inject) }
  ultimately show "P" 
    by (rule A[where n="[(z, z')] \<bullet> n" and v="([(x, x')] \<bullet> v)"]) 
qed (insert r T K, auto)


text \<open>The lemma in Figure~\ref{fig:lemma7} assumes @{term "SN(n[x::=p] \<star> K)"}
but the actual induction in done on @{term "SN(n \<star> K)"}. The stronger
assumption @{term "SN (n[x::=p] \<star> K)"} is needed to handle the $\beta$ and
$\eta$ cases.\<close>

lemma sn_forget:
  assumes a: "SN(t[x::=v])"
  shows "SN t"
proof -
  define q where "q = t[x::=v]"
  from a have "SN q" unfolding q_def .
  thus "SN t" using q_def
  proof (induct q arbitrary: t)
    case (SN_intro t)
    hence ih: "\<And> t'. \<lbrakk>t[x::=v] \<mapsto> t'[x::=v]\<rbrakk> \<Longrightarrow> SN t'" by auto
    { fix t' assume "t \<mapsto> t'"
      hence "t[x::=v] \<mapsto> t'[x::=v]" by (rule reduction_subst)
      hence "SN t'" by (rule ih) }
    thus "SN t" ..
  qed
qed

          
lemma sn_forget': 
  assumes sn: "SN (t[x::=p] \<star> k)" 
  and x: "x \<sharp> k"
  shows "SN (t \<star> k)"
proof -
  from x have "t[x::=p] \<star> k = (t \<star> k)[x::=p]" by (simp add: ssubst_forget)
  with sn have "SN( (t \<star> k)[x::=p] )" by simp
  thus ?thesis by (rule sn_forget)
qed

abbreviation
redrtrans :: "trm \<Rightarrow> trm \<Rightarrow> bool" (" _ \<mapsto>\<^sup>* _ " )
where "redrtrans \<equiv> reduction^**" 

text \<open>To be able to handle the case where $p$ makes a step, we need to
establish @{term "p \<mapsto> p' \<Longrightarrow> (m[x::=p]) \<mapsto>\<^sup>* (m[x::=p'])"} as well as the
fact that strong normalization is preserved for an arbitrary number of reduction
steps. The first claim involves a number of simple transitivity lemmas. Here we
can benefit from having removed the freshness conditions from the reduction
relation as this allows all the cases to be proven automatically. Similarly, in
the \isa{red-subst} lemma, only those cases where substitution is pushed to two
subterms needs to be proven explicitly.\<close>

lemma red_trans:
  shows r1_trans: " s \<mapsto>\<^sup>* s' \<Longrightarrow> App s t \<mapsto>\<^sup>* App s' t"
  and r2_trans: " t \<mapsto>\<^sup>* t' \<Longrightarrow> App s t \<mapsto>\<^sup>* App s t'"
  and r4_trans: "t \<mapsto>\<^sup>* t' \<Longrightarrow> \<Lambda> x . t \<mapsto>\<^sup>* \<Lambda> x . t' "
  and r6_trans: " s \<mapsto>\<^sup>* s'  \<Longrightarrow> s to x in t \<mapsto>\<^sup>* s' to x in t"
  and r7_trans: "\<lbrakk> t \<mapsto>\<^sup>* t'  \<rbrakk> \<Longrightarrow> s to x in t \<mapsto>\<^sup>* s  to x in t'"
  and r11_trans: "s \<mapsto>\<^sup>* s' \<Longrightarrow> [s] \<mapsto>\<^sup>* ([s'])"
by - (induct rule: rtranclp_induct , (auto intro:
transitive_closurep_trans')[2])+

lemma red_subst: "p \<mapsto> p' \<Longrightarrow> (m[x::=p]) \<mapsto>\<^sup>* (m[x::=p'])"
proof(nominal_induct m avoiding: x p p' rule:trm.strong_induct)
  case (App s t) 
  hence "App (s[x::=p]) (t[x::=p]) \<mapsto>\<^sup>* App (s[x::=p']) (t[x::=p])" 
    by (auto intro: r1_trans)
  also from App have "\<dots> \<mapsto>\<^sup>* App (s[x::=p']) ( t[x::=p'])"
    by (auto intro: r2_trans)
  finally show ?case by auto
next
  case (To s y n) hence 
    "(s[x::=p]) to y in (n[x::=p]) \<mapsto>\<^sup>* (s[x::=p']) to y in (n[x::=p])" 
    by (auto intro: r6_trans)
  also from To have " \<dots> \<mapsto>\<^sup>* (s[x::=p']) to y in (n[x::=p']) "
    by (auto intro: r7_trans)
  finally show ?case using To by auto
qed (auto intro:red_trans)

lemma SN_trans : "\<lbrakk>  p \<mapsto>\<^sup>* p' ; SN p \<rbrakk> \<Longrightarrow> SN p' "
by (induct rule: rtranclp_induct) (auto intro: SN_preserved)

subsection \<open>Central lemma\<close>
text_raw \<open>\label{sec:central}\<close>

text \<open>Now we have everything in place we need to tackle the central ``Lemma
7'' of \cite{TT-lifting} (cf. Figure~\ref{fig:lemma7}). The proof is quite long,
but for the most part, the reasoning is that of \cite{TT-lifting}.\<close>

lemma to_RED_aux: 
  assumes p: "SN p"
  and x: "x \<sharp> p"   "x \<sharp> k"
  and npk: " SN (n[x::=p] \<star> k)"
  shows "SN (([p] to x in n) \<star> k)"
proof -
  { fix q assume "SN q" with p 
    have  "\<And> m . \<lbrakk> q = m \<star> k ; SN(m[x::=p] \<star> k) \<rbrakk> 
               \<Longrightarrow> SN (([p] to x in m) \<star> k)"
      using x
    proof (induct p q rule:triple_induct[where k="k"]) 
      case (1 p q k) \<comment> \<open>We obtain an induction hypothesis for $p$, $q$, and
$k$.\<close>
      have ih_p: 
        "\<And> p' m . \<lbrakk>p \<mapsto> p'; q = m \<star> k; SN (m[x::=p'] \<star> k); x \<sharp> p'; x \<sharp> k\<rbrakk>
            \<Longrightarrow> SN (([p'] to x in m) \<star> k)" by fact
      have ih_q: 
        "\<And> q' m k . \<lbrakk>q \<mapsto> q'; q' = m \<star> k; SN (m[x::=p] \<star> k); x \<sharp> p; x \<sharp> k\<rbrakk>
            \<Longrightarrow> SN (([p] to x in m) \<star> k)" by fact
      have ih_k: 
        "\<And> k' m . \<lbrakk> |k'| < |k|; q = m \<star> k'; SN (m[x::=p] \<star> k'); x \<sharp> p; x \<sharp> k'\<rbrakk>
            \<Longrightarrow> SN (([p] to x in m) \<star> k')" by fact
      have q: "q = m \<star> k" and sn: "SN (m[x::=p] \<star> k)" by fact+
      have xp: "x \<sharp> p" and xk: "x \<sharp> k" by fact+

txt \<open>Once again we want to reason via case distinction on the successors of a
term including a dismantling operator. Since this time we also need to handle
the cases where interactions occur, we want to use the strengthened case
rule. We already require $x$ to be suitably fresh. To instantiate the rule, we
need another fresh name.\<close>

      { fix r assume red: "([p] to x in m) \<star> k \<mapsto> r"
        from xp xk have x1 : "x \<sharp> ([p] to x in m) \<star> k "  
          by (simp add: abs_fresh)
        with red have x2: "x \<sharp> r" by (rule reduction_fresh)
        obtain z::name where z: "z \<sharp> (x,p,m,k,r)" 
          using ex_fresh[of "(x,p,m,k,r)"] by (auto simp add: fresh_prod)
        have "SN r"
        proof (cases rule:dismantle_strong_cases
            [of   "[p] to x in m"   k r x x z ])
          case (5 r') have r: "r = r' \<star> k" and r': "[p] to x in m \<mapsto> r'" by fact+
          txt \<open>To handle the case of a reduction occurring somewhere in @{term
"[p] to x in m" }, we need to contract the freshness conditions to this subterm.
This allows the use of the strong inversion rule for the reduction relation.\<close>
          from x1 x2 r 
          have xl:"(x \<sharp> [p] to x in m)" and xr:"x \<sharp> r'" by auto
          from z have zl: "z \<sharp> ([p] to x in m)"   "x \<noteq> z" 
            by (auto simp add: abs_fresh fresh_prod fresh_atm)
          with r' have zr: "z \<sharp> r'"  by (blast intro:reduction_fresh)
          \<comment> \<open>handle all reductions of @{term "[p] to x in m"}\<close>
          from r' show "SN r" proof (cases rule:reduction.strong_cases
              [where x="x" and xa="x" and xb="x" and xc="x" and xd="x" 
                and xe="x" and xf="x"and xg="x" and y="z"])
txt \<open>The case where @{term "p \<mapsto> p'"} is interesting, because it requires
reasioning about the reflexive transitive closure of the reduction relation.\<close>
            case (r6 s s' t)  hence ch: "[p] \<mapsto> s'"   "r' = s' to x in m" 
              using xl xr by (auto)
            from this obtain p' where s: "s' = [p']" and  p : "p \<mapsto> p'" 
              by (blast dest:red_Ret)
            from p have "((m\<star>k)[x::=p]) \<mapsto>\<^sup>* ((m\<star>k)[x::=p'])" 
              by (rule red_subst)
            with xk have "((m[x::=p]) \<star> k) \<mapsto>\<^sup>* ((m[x::=p']) \<star> k)" 
              by (simp add: ssubst_forget)
            hence sn: "SN ((m[x::=p']) \<star> k)" using sn by (rule SN_trans)
            from p xp have xp' : "x \<sharp> p'" by (rule reduction_fresh)
            from ch s have rr: "r' = [p'] to x in m" by simp
            from p q  sn xp' xk
            show "SN r" unfolding r rr by (rule ih_p)
          next

            case(r7 s t m') hence "r' = [p] to x in m'" and "m \<mapsto> m'" 
              using xl xr by (auto simp add: alpha)
            hence rr: "r' = [p] to x in m'" by simp
            from q \<open>m \<mapsto> m'\<close> have  "q \<mapsto> m' \<star> k" by(simp add: dismantle_red)
            moreover have "m' \<star> k = m' \<star> k" .. \<comment> \<open>a triviality\<close>
            moreover { from \<open>m \<mapsto> m'\<close> have "(m[x::=p]) \<star> k \<mapsto> (m'[x::=p]) \<star> k"
                by (simp add: dismantle_red reduction_subst)
              with sn have "SN(m'[x::=p] \<star> k)" .. }
            ultimately show "SN r" using xp xk unfolding r rr by (rule ih_q)
          next  
              
            case (r8 s t) \<comment> \<open>the $\beta$-case is handled by assumption\<close>
            hence "r' = m[x::=p]" using xl xr by(auto simp add: alpha)
            thus "SN r" unfolding r using sn by simp
          next 

            case (r9 s) \<comment> \<open>the $\eta$-case is handled by assumption as well\<close> 
            hence "m = [Var x]" and "r' = [p]" using xl xr 
              by(auto simp add: alpha)
            hence "r' = m[x::=p]" by simp
            thus "SN r" unfolding r using sn by simp
          qed (simp_all only: xr xl zl zr abs_fresh , auto)
          \<comment> \<open>There are no other possible reductions of @{term "[p] to x in
m"}.\<close>
        next

          case (6 k') 
          have k: "k \<mapsto> k'" and r: "r = ([p] to x in m) \<star> k'" by fact+
          from q k have "q \<mapsto> m \<star> k'" unfolding stack_reduction_def by blast
          moreover have "m \<star> k' = m \<star> k'" ..
          moreover { have "SN (m[x::=p] \<star> k)" by fact
            moreover have "(m[x::=p]) \<star> k \<mapsto> (m[x::=p]) \<star> k'" 
              using k unfolding stack_reduction_def .. 
            ultimately have "SN (m[x::=p] \<star> k')" .. }
          moreover note xp 
          moreover from k xk  have "x \<sharp> k'"
            by (rule stack_reduction_fresh)
          ultimately show "SN r" unfolding r by (rule ih_q)
        next
txt \<open>The case of an assoc interaction between @{term "[p] to x in m" } and
@{term "k"} is easily handled by the induction hypothesis, since @{term
"(m[x::=p]) \<star> k"} remains fixed under assoc.\<close>
          case (8 s t u L)
          hence k: "k = [z]u\<ggreater>L"
            and r: "r = ([p] to x in (m to z in u)) \<star> L" 
            and u: "x \<sharp> u" 
            by(auto simp add: alpha fresh_prod)
          let ?k = L and ?m = "m to z in u"
          from k z have "|?k| < |k|" by (simp add: fresh_prod)
          moreover have "q =  ?m \<star> ?k" using k q by simp
          moreover { from k u z xp have "(?m[x::=p] \<star> ?k) = (m[x::=p]) \<star> k" 
            by(simp add: fresh_prod forget)
          hence "SN (?m[x::=p] \<star> ?k)" using sn by simp }
          moreover from xp xk k have "x \<sharp> p" and "x \<sharp> ?k" by auto
          ultimately show "SN r" unfolding r by (rule ih_k)
        qed (insert red z x1 x2 xp xk ,
            auto simp add: fresh_prod fresh_atm abs_fresh)
      } thus "SN (([p] to x in m) \<star> k)" ..
    qed } 
  moreover have "SN ((n[x::=p]) \<star> k)" by fact
  moreover hence "SN (n \<star> k)" using \<open>x \<sharp> k\<close> by (rule sn_forget') 
  ultimately show ?thesis by blast
qed

text \<open>Having established the claim above, we use it show that
\textsf{to}-bindings preserve reducibility.\<close>

lemma to_RED:
  assumes s: "s \<in> RED (T \<sigma>)"
  and t : " \<forall> p \<in> RED \<sigma> . t[x::=p] \<in> RED (T \<tau>)"
  shows "s to x in t \<in> RED (T \<tau>)"
proof -
  { fix K assume k: "K \<in> SRED \<tau>" 
    { fix p assume p: "p \<in> RED \<sigma>"
      hence snp: "SN p" using RED_props by(simp add: CR1_def)
      obtain x'::name where x: "x' \<sharp> (t, p, K)" 
        using ex_fresh[of "(t,p,K)"] by (auto)
      from p t k have "SN((t[x::=p]) \<star> K)" by auto
      with x have "SN ((([(x',x)] \<bullet> t )[x'::=p]) \<star> K)" 
        by (simp add: fresh_prod subst_rename)
      with snp x  have snx': "SN (([p] to x' in ([(x',x)] \<bullet> t )) \<star> K)" 
        by (auto intro: to_RED_aux)
      from x have "[p] to x' in ([(x',x)] \<bullet> t ) = [p] to x in t" 
        by simp (metis alpha' fresh_prod name_swap_bij x)
      moreover have "([p] to x in t) \<star> K  = [p] \<star> [x]t\<ggreater>K" by simp
      ultimately have snx: "SN([p] \<star> [x]t\<ggreater>K)" using snx' 
        by (simp del: trm.inject)
    } hence "[x]t\<ggreater>K \<in> SRED \<sigma>" by simp
    with s have "SN((s to x in t) \<star> K)" by(auto simp del: SRED.simps) 
  } thus "s to x in t \<in> RED (T \<tau>)" by simp
qed


section \<open>Fundamental Theorem\<close>
text_raw \<open>\label{sec:FTLR}\<close>

text \<open>The remainder of this section follows \cite{SN.thy} very closely.  We
first establish that all well typed terms are reducible if we substitute
reducible terms for the free variables.\<close>

abbreviation 
 mapsto :: "(name\<times>trm) list \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> bool" ("_ maps _ to _" [55,55,55] 55)
where
 "\<theta> maps x to e \<equiv> (lookup \<theta> x) = e"

abbreviation 
  closes :: "(name\<times>trm) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" ("_ closes _" [55,55] 55) 
where
  "\<theta> closes \<Gamma> \<equiv> \<forall>x \<tau>. ((x,\<tau>) \<in> set \<Gamma> \<longrightarrow> (\<exists>t. \<theta> maps x to t \<and> t \<in> RED \<tau>))"

theorem fundamental_theorem: 
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"   and   b: "\<theta> closes \<Gamma>"
  shows "\<theta><t> \<in> RED \<tau>"
using a b
proof(nominal_induct  avoiding: \<theta> rule: typing.strong_induct)
  case (t3 a \<Gamma> \<sigma> t \<tau> \<theta>) \<comment> \<open>lambda case\<close> 
  {%invisible 
  have ih: "\<And>\<theta>. \<theta> closes ((a,\<sigma>)#\<Gamma>) \<Longrightarrow> \<theta><t> \<in> RED \<tau>" by fact
  have \<theta>_cond: "\<theta> closes \<Gamma>" by fact
  have fresh: "a\<sharp>\<Gamma>"   "a\<sharp>\<theta>" by fact+
  from ih have "\<forall>s\<in>RED \<sigma>. ((a,s)#\<theta>)<t> \<in> RED \<tau>" 
    using fresh \<theta>_cond fresh_context by simp
  then have "\<forall>s\<in>RED \<sigma>. \<theta><t>[a::=s] \<in> RED \<tau>" 
    using fresh by (simp add: psubst_subst)
  then have "\<Lambda> a . (\<theta><t>) \<in> RED (\<sigma> \<rightarrow> \<tau>)" by (simp only: abs_RED)
  then show "\<theta><(\<Lambda> a . t)> \<in> RED (\<sigma> \<rightarrow> \<tau>)" using fresh by simp }
next
  case (t5 x \<Gamma> s \<sigma> t \<tau> \<theta>) \<comment> \<open>to case\<close>
  have ihs : "\<And> \<theta> . \<theta> closes \<Gamma> \<Longrightarrow> \<theta><s> \<in> RED (T \<sigma>)" by fact
  have iht : "\<And> \<theta> . \<theta> closes ((x, \<sigma>) # \<Gamma>) \<Longrightarrow> \<theta><t> \<in> RED (T \<tau>)" by fact
  have \<theta>_cond: "\<theta> closes \<Gamma>" by fact
  have fresh: "x \<sharp> \<theta>"  "x \<sharp> \<Gamma>"   "x \<sharp> s" by fact+
  from ihs have "\<theta><s> \<in> RED (T \<sigma>)" using \<theta>_cond by simp
  moreover 
  { from iht have "\<forall>s\<in>RED \<sigma>. ((x,s)#\<theta>)<t> \<in> RED (T \<tau>)" 
      using fresh \<theta>_cond fresh_context by simp
    hence "\<forall>s\<in>RED \<sigma>. \<theta><t>[x::=s] \<in> RED (T \<tau>)" 
      using fresh by (simp add: psubst_subst) }
  ultimately have "(\<theta><s>) to x in (\<theta><t>) \<in> RED (T \<tau>)" by (simp only: to_RED)
  thus "\<theta><s to x in t> \<in> RED (T \<tau>)" using fresh by simp
qed auto \<comment> \<open>all other cases are trivial\<close>

text \<open>The final result then follows using the identity substitution, which is
$\Gamma$-closing since all variables are reducible at any type.\<close>

fun
  "id" :: "(name\<times>ty) list \<Rightarrow> (name\<times>trm) list"
where
  "id []    = []"
| "id ((x,\<tau>)#\<Gamma>) = (x,Var x)#(id \<Gamma>)"

lemma id_maps: 
  shows "(id \<Gamma>) maps a to (Var a)"
by (induct \<Gamma>) (auto)

lemma id_fresh:
  fixes x::"name"
  assumes x: "x \<sharp> \<Gamma>"
  shows "x \<sharp> (id \<Gamma>)"
using x
by (induct \<Gamma>) (auto simp add: fresh_list_nil fresh_list_cons)

lemma id_apply: 
  shows "(id \<Gamma>)<t> = t"
by (nominal_induct t avoiding: \<Gamma> rule: trm.strong_induct)
   (auto simp add: id_maps id_fresh)

lemma id_closes:
  shows "(id \<Gamma>) closes \<Gamma>"
proof - 
  { fix x \<tau> assume "(x,\<tau>) \<in> set \<Gamma>"
    have "CR4 \<tau>" by(simp add: RED_props CR3_implies_CR4)
    hence "Var x \<in> RED \<tau>" 
      by(auto simp add: NEUT_def normal_var CR4_def)
    hence "(id \<Gamma>) maps x to Var x \<and> Var x \<in> RED \<tau>"
      by (simp add: id_maps) 
  } thus ?thesis by blast
qed

subsection \<open>Strong normalization theorem\<close>

lemma typing_implies_RED:  
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  shows "t \<in> RED \<tau>"
proof -
  have "(id \<Gamma>)<t>\<in>RED \<tau>" 
  proof -
    have "(id \<Gamma>) closes \<Gamma>" by (rule id_closes)
    with a show ?thesis by (rule fundamental_theorem)
  qed
  thus"t \<in> RED \<tau>" by (simp add: id_apply)
qed

theorem strong_normalization: 
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  shows "SN(t)"
proof -
  from a have "t \<in> RED \<tau>" by (rule typing_implies_RED)
  moreover have "CR1 \<tau>" by (rule RED_props)
  ultimately show "SN(t)" by (simp add: CR1_def)
qed

text \<open>This finishes our formalization effort. This article is generated
from the Isabelle theory file, which consists of roughly 1500 lines of proof
code. The reader is invited to replay some of the more technical proofs using
the theory file provided.\<close>

(*<*)end(*>*)


