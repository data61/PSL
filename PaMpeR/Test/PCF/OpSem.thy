(*  Title:      OpSem.thy
    Author:     Peter Gammie
*)

section {* Logical relations for computational adequacy *}
(*<*)

theory OpSem
imports
  Basis
  PCF
begin

(*>*)
text{*

\label{sec:opsem}

We relate the denotational semantics for PCF of \S\ref{sec:densem} to
a \emph{big-step} (or \emph{natural}) operational semantics. This
follows \citet{DBLP:conf/mfps/Pitts93}.

*}

subsection{* Direct semantics using de Bruijn notation *}

text{*

\label{sec:directsem_db}

In contrast to \S\ref{sec:directsem} we must be more careful in our
treatment of @{text "\<alpha>"}-equivalent terms, as we would like our
operational semantics to identify of all these. To that end we adopt
de Bruijn notation, adapting the work of
\citet{DBLP:journals/jar/Nipkow01}, and show that it is suitably
equivalent to our original syntactic story.

*}

datatype db =
    DBVar var
  | DBApp db db
  | DBAbsN db
  | DBAbsV db
  | DBDiverge
  | DBFix db
  | DBtt
  | DBff
  | DBCond db db db
  | DBNum nat
  | DBSucc db
  | DBPred db
  | DBIsZero db

text{*

Nipkow et al's substitution operation is defined for arbitrary open
terms. In our case we only substitute closed terms into terms where
only the variable @{term "0"} may be free, and while we could develop
a simpler account, we retain the traditional one.

*}

fun
  lift :: "db \<Rightarrow> nat \<Rightarrow> db"
where
  "lift (DBVar i) k = DBVar (if i < k then i else (i + 1))"
| "lift (DBAbsN s) k = DBAbsN (lift s (k + 1))"
| "lift (DBAbsV s) k = DBAbsV (lift s (k + 1))"
| "lift (DBApp s t) k = DBApp (lift s k) (lift t k)"
| "lift (DBFix e) k = DBFix (lift e (k + 1))"
| "lift (DBCond c t e) k = DBCond (lift c k) (lift t k) (lift e k)"
| "lift (DBSucc e) k = DBSucc (lift e k)"
| "lift (DBPred e) k = DBPred (lift e k)"
| "lift (DBIsZero e) k = DBIsZero (lift e k)"
| "lift x k = x"

fun
  subst :: "db \<Rightarrow> db \<Rightarrow> var \<Rightarrow> db"  ("_<_'/_>" [300, 0, 0] 300)
where
  subst_Var: "(DBVar i)<s/k> =
      (if k < i then DBVar (i - 1) else if i = k then s else DBVar i)"
| subst_AbsN: "(DBAbsN t)<s/k> = DBAbsN (t<lift s 0 / k+1>)"
| subst_AbsV: "(DBAbsV t)<s/k> = DBAbsV (t<lift s 0 / k+1>)"
| subst_App: "(DBApp t u)<s/k> = DBApp (t<s/k>) (u<s/k>)"
| "(DBFix e)<s/k> = DBFix (e<lift s 0 / k+1>)"
| "(DBCond c t e)<s/k> = DBCond (c<s/k>) (t<s/k>) (e<s/k>)"
| "(DBSucc e)<s/k> = DBSucc (e<s/k>)"
| "(DBPred e)<s/k> = DBPred (e<s/k>)"
| "(DBIsZero e)<s/k> = DBIsZero (e<s/k>)"
| subst_Consts: "x<s/k> = x"
(*<*)

declare subst_Var [simp del]

lemma subst_eq: "(DBVar k)<u/k> = u"
  by (simp add: subst_Var)

lemma subst_gt: "i < j \<Longrightarrow> (DBVar j)<u/i> = DBVar (j - 1)"
  by (simp add: subst_Var)

lemma subst_lt: "j < i \<Longrightarrow> (DBVar j)<u/i> = DBVar j"
  by (simp add: subst_Var)

lemma lift_lift:
    "i < k + 1 \<Longrightarrow> lift (lift t i) (Suc k) = lift (lift t k) i"
  by (induct t arbitrary: i k) auto

lemma lift_subst:
    "j < i + 1 \<Longrightarrow> lift (t<s/j>) i = (lift t (i + 1))<lift s i / j>"
  by (induct t arbitrary: i j s)
     (simp_all add: diff_Suc subst_Var lift_lift split: nat.split)

lemma lift_subst_lt:
    "i < j + 1 \<Longrightarrow> lift (t<s/j>) i = (lift t i)<lift s i / j + 1>"
  by (induct t arbitrary: i j s) (auto simp: subst_Var lift_lift)

lemma subst_lift:
    "(lift t k)<s/k> = t"
  by (induct t arbitrary: k s) (simp_all add: subst_eq subst_gt subst_lt)

lemmas subst_simps [simp] =
  subst_eq
  subst_gt
  subst_lt
  lift_subst
  subst_lift

lemma subst_subst:
    "i < j + 1 \<Longrightarrow> t<lift v i/Suc j><u<v/j>/i> = t<u/i><v/j>"
  by (induct t arbitrary: i j u v)
     (simp_all add: diff_Suc subst_Var lift_lift [symmetric] lift_subst_lt
             split: nat.split)

(*>*)
text{*

We elide the standard lemmas about these operations.

A variable is free in a de Bruijn term in the standard way.

*}

fun
  freedb :: "db \<Rightarrow> var \<Rightarrow> bool"
where
  "freedb (DBVar j) k = (j = k)"
| "freedb (DBAbsN s) k = freedb s (k + 1)"
| "freedb (DBAbsV s) k = freedb s (k + 1)"
| "freedb (DBApp s t) k = (freedb s k \<or> freedb t k)"
| "freedb (DBFix e) k = freedb e (Suc k)"
| "freedb (DBCond c t e) k = (freedb c k \<or> freedb t k \<or> freedb e k)"
| "freedb (DBSucc e) k = freedb e k"
| "freedb (DBPred e) k = freedb e k "
| "freedb (DBIsZero e) k = freedb e k"
| "freedb _ _ = False"
(*<*)

lemma subst_not_free [simp]: "\<not> freedb s i \<Longrightarrow> s<t/i> = s<u/i>"
  by (induct s arbitrary: i t u) (simp_all add: subst_Var)

lemma free_lift [simp]:
  "freedb (lift t k) i \<longleftrightarrow> (i < k \<and> freedb t i \<or> k < i \<and> freedb t (i - 1))"
  by (induct t arbitrary: i k) (auto cong: conj_cong)

lemma free_subst [simp]:
    "freedb (s<t/k>) i \<longleftrightarrow> (freedb s k \<and> freedb t i \<or> freedb s (if i < k then i else i + 1))"
  apply (induct s arbitrary: i k t)
    prefer 2
    apply simp
    apply blast
   prefer 2
   apply simp
  apply (simp add: diff_Suc subst_Var split: nat.split)
  apply auto
  done

theorem lift_subst_dummy: "\<not> freedb s i \<Longrightarrow> lift (s<dummy/i>) i = s"
  by (induct s arbitrary: i dummy) (simp_all add: not_less_eq if_not_P)

lemma closed_lift:
  "\<forall>v. freedb e v \<longrightarrow> v < k \<Longrightarrow> lift e k = e"
  apply (induct e arbitrary: k)
  apply simp_all
  apply (metis less_Suc_eq_0_disj nat.exhaust)+
  done

(* FIXME this is terrible *)

lemma closed_subst:
  "\<forall>v. freedb e v \<longrightarrow> v < k \<Longrightarrow> e<s/k> = e"
  apply (induct e arbitrary: s k)
  apply simp_all

  apply (drule_tac x="lift s 0" in meta_spec)
  apply (drule_tac x="Suc k" in meta_spec)
  apply (subgoal_tac "\<forall>v. freedb e v \<longrightarrow> v < Suc k")
   apply blast
  apply clarsimp
  apply (case_tac v)
   apply simp
  apply simp

  apply (drule_tac x="lift s 0" in meta_spec)
  apply (drule_tac x="Suc k" in meta_spec)
  apply (subgoal_tac "\<forall>v. freedb e v \<longrightarrow> v < Suc k")
   apply blast
  apply clarsimp
  apply (case_tac v)
   apply simp
  apply simp

  apply (drule_tac x="lift s 0" in meta_spec)
  apply (drule_tac x="Suc k" in meta_spec)
  apply (subgoal_tac "\<forall>v. freedb e v \<longrightarrow> v < Suc k")
   apply blast
  apply clarsimp
  apply (case_tac v)
   apply simp
  apply simp
  done

(*>*)
text{* Programs are closed expressions. *}

definition closed :: "db \<Rightarrow> bool" where
  "closed e \<equiv> \<forall>i. \<not> freedb e i"
(*<*)

lemma closed_inv:
  "closed (DBApp f x) \<longleftrightarrow> closed f \<and> closed x"
  "closed DBDiverge"
  "closed DBtt"
  "closed DBff"
  "closed (DBCond c t e) \<longleftrightarrow> closed c \<and> closed t \<and> closed e"
  "closed (DBNum n)"
  "closed (DBSucc e) \<longleftrightarrow> closed e"
  "closed (DBPred e) \<longleftrightarrow> closed e"
  "closed (DBIsZero e) \<longleftrightarrow> closed e"
  unfolding closed_def by auto

lemma closed_binders:
  "closed (DBAbsN e) \<longleftrightarrow> (\<forall>i. freedb e i \<longrightarrow> i = 0)"
  "closed (DBAbsV e) \<longleftrightarrow> (\<forall>i. freedb e i \<longrightarrow> i = 0)"
  "closed (DBFix e) \<longleftrightarrow> (\<forall>i. freedb e i \<longrightarrow> i = 0)"
  unfolding closed_def
  apply auto
  apply (case_tac i, auto)+
  done

lemmas closed_invs [iff] =
  closed_inv
  closed_binders

(*>*)
text{*

The direct denotational semantics is almost identical to that given in
\S\ref{sec:densem}, apart from this change in the representation of
environments.

*}

definition env_empty_db :: "'a Env" where
  "env_empty_db \<equiv> \<bottom>"

definition env_ext_db :: "'a \<rightarrow> 'a Env \<rightarrow> 'a Env" where
  "env_ext_db \<equiv> \<Lambda> x \<rho> v. (case v of 0 \<Rightarrow> x | Suc v' \<Rightarrow> \<rho>\<cdot>v')"
(*<*)

lemma env_ext_same_db: "env_ext_db\<cdot>x\<cdot>\<rho>\<cdot>0 = x"
  by (simp add: env_ext_db_def)

lemma env_ext_neq_db: "env_ext_db\<cdot>x\<cdot>\<rho>\<cdot>(Suc v) = \<rho>\<cdot>v"
  by (simp add: env_ext_db_def)

lemmas env_ext_db_simps [simp] =
  env_ext_same_db
  env_ext_neq_db
(*>*)
text{**}

primrec
  evalDdb :: "db \<Rightarrow> ValD Env \<rightarrow> ValD"
where
  "evalDdb (DBVar i) = (\<Lambda> \<rho>. \<rho>\<cdot>i)"
| "evalDdb (DBApp f x) = (\<Lambda> \<rho>. appF\<cdot>(evalDdb f\<cdot>\<rho>)\<cdot>(evalDdb x\<cdot>\<rho>))"
| "evalDdb (DBAbsN e) = (\<Lambda> \<rho>. ValF\<cdot>(\<Lambda> x. evalDdb e\<cdot>(env_ext_db\<cdot>x\<cdot>\<rho>)))"
| "evalDdb (DBAbsV e) = (\<Lambda> \<rho>. ValF\<cdot>(strictify\<cdot>(\<Lambda> x. evalDdb e\<cdot>(env_ext_db\<cdot>x\<cdot>\<rho>))))"
| "evalDdb (DBDiverge) = (\<Lambda> \<rho>. \<bottom>)"
| "evalDdb (DBFix e) = (\<Lambda> \<rho>. \<mu> x. evalDdb e\<cdot>(env_ext_db\<cdot>x\<cdot>\<rho>))"
| "evalDdb (DBtt) = (\<Lambda> \<rho>. ValTT)"
| "evalDdb (DBff) = (\<Lambda> \<rho>. ValFF)"
| "evalDdb (DBCond c t e) = (\<Lambda> \<rho>. cond\<cdot>(evalDdb c\<cdot>\<rho>)\<cdot>(evalDdb t\<cdot>\<rho>)\<cdot>(evalDdb e\<cdot>\<rho>))"
| "evalDdb (DBNum n) = (\<Lambda> \<rho>. ValN\<cdot>n)"
| "evalDdb (DBSucc e) = (\<Lambda> \<rho>. succ\<cdot>(evalDdb e\<cdot>\<rho>))"
| "evalDdb (DBPred e) = (\<Lambda> \<rho>. pred\<cdot>(evalDdb e\<cdot>\<rho>))"
| "evalDdb (DBIsZero e) = (\<Lambda> \<rho>. isZero\<cdot>(evalDdb e\<cdot>\<rho>))"
(*<*)

(* This proof is trivial but Isabelle doesn't seem keen enough to
apply the induction hypothesises in the obvious ways. *)
lemma evalDdb_env_cong:
  assumes "\<forall>v. freedb e v \<longrightarrow> \<rho>\<cdot>v = \<rho>'\<cdot>v"
  shows "evalDdb e\<cdot>\<rho> = evalDdb e\<cdot>\<rho>'"
using assms
proof(induct e arbitrary: \<rho> \<rho>')
  case (DBApp e1 e2 \<rho> \<rho>')
  from DBApp.hyps[where \<rho>=\<rho> and \<rho>'=\<rho>'] DBApp.prems show ?case by simp
next
  case (DBAbsN e \<rho> \<rho>')
  { fix x
    from DBAbsN.hyps[where \<rho>="env_ext_db\<cdot>x\<cdot>\<rho>" and \<rho>'="env_ext_db\<cdot>x\<cdot>\<rho>'"] DBAbsN.prems
    have "evalDdb e\<cdot>(env_ext_db\<cdot>x\<cdot>\<rho>) = evalDdb e\<cdot>(env_ext_db\<cdot>x\<cdot>\<rho>')"
      by (simp add: env_ext_db_def split: nat.splits) }
  thus ?case by simp
next
  case (DBAbsV e \<rho> \<rho>')
  { fix x
    from DBAbsV.hyps[where \<rho>="env_ext_db\<cdot>x\<cdot>\<rho>" and \<rho>'="env_ext_db\<cdot>x\<cdot>\<rho>'"] DBAbsV.prems
    have "evalDdb e\<cdot>(env_ext_db\<cdot>x\<cdot>\<rho>) = evalDdb e\<cdot>(env_ext_db\<cdot>x\<cdot>\<rho>')"
      by (simp add: env_ext_db_def split: nat.splits) }
  thus ?case by simp
next
  case (DBFix e \<rho> \<rho>') thus ?case
    by simp (rule parallel_fix_ind, simp_all add: env_ext_db_def split: nat.splits)
next
  case (DBCond i t e \<rho> \<rho>')
  from DBCond.hyps[where \<rho>=\<rho> and \<rho>'=\<rho>'] DBCond.prems show ?case by simp
next
  case (DBSucc e \<rho> \<rho>')
  from DBSucc.hyps[where \<rho>=\<rho> and \<rho>'=\<rho>'] DBSucc.prems show ?case by simp
next
  case (DBPred e \<rho> \<rho>')
  from DBPred.hyps[where \<rho>=\<rho> and \<rho>'=\<rho>'] DBPred.prems show ?case by simp
next
  case (DBIsZero e \<rho> \<rho>')
  from DBIsZero.hyps[where \<rho>=\<rho> and \<rho>'=\<rho>'] DBIsZero.prems show ?case by simp
qed (auto simp: cfun_eq_iff)

lemma evalDdb_env_closed:
  assumes "closed e"
  shows "evalDdb e\<cdot>\<rho> = evalDdb e\<cdot>\<rho>'"
by (rule evalDdb_env_cong) (simp add: assms[unfolded closed_def])

(*>*)
text{*

We show that our direct semantics using de Bruijn notation coincides
with the evaluator of \S\ref{sec:directsem} by translating between the
syntaxes and showing that the evaluators yield identical results.

Firstly we show how to translate an expression using names into a
nameless term. The following function finds the first mention of a
variable in a list of variables.

*}

primrec index :: "var list \<Rightarrow> var \<Rightarrow> nat \<Rightarrow> nat" where
  "index [] v n = n"
| "index (h # t) v n = (if v = h then n else index t v (Suc n))"

primrec
  transdb :: "expr \<Rightarrow> var list \<Rightarrow> db"
where
  "transdb (Var i) \<Gamma> = DBVar (index \<Gamma> i 0)"
| "transdb (App t1 t2) \<Gamma> = DBApp (transdb t1 \<Gamma>) (transdb t2 \<Gamma>)"
| "transdb (AbsN v t) \<Gamma> = DBAbsN (transdb t (v # \<Gamma>))"
| "transdb (AbsV v t) \<Gamma> = DBAbsV (transdb t (v # \<Gamma>))"
| "transdb (Diverge) \<Gamma> = DBDiverge"
| "transdb (Fix v e) \<Gamma> = DBFix (transdb e (v # \<Gamma>))"
| "transdb (tt) \<Gamma> = DBtt"
| "transdb (ff) \<Gamma> = DBff"
| "transdb (Cond c t e) \<Gamma> = DBCond (transdb c \<Gamma>) (transdb t \<Gamma>) (transdb e \<Gamma>)"
| "transdb (Num n) \<Gamma> = (DBNum n)"
| "transdb (Succ e) \<Gamma> = DBSucc (transdb e \<Gamma>)"
| "transdb (Pred e) \<Gamma> = DBPred (transdb e \<Gamma>)"
| "transdb (IsZero e) \<Gamma> = DBIsZero (transdb e \<Gamma>)"

text{*

This semantics corresponds with the direct semantics for named
expressions.

*}
(*<*)
text{* The free variables of an expression using names. *}

fun
  free :: "expr \<Rightarrow> var list"
where
  "free (Var v) = [v]"
| "free (App f x) = free f @ free x"
| "free (AbsN v e) = removeAll v (free e)"
| "free (AbsV v e) = removeAll v (free e)"
| "free (Fix v e) = removeAll v (free e)"
| "free (Cond c t e) = free c @ free t @ free e"
| "free (Succ e) = free e"
| "free (Pred e) = free e"
| "free (IsZero e) = free e"
| "free _ = []"

lemma index_Suc:
  "index \<Gamma> v (Suc i) = Suc (index \<Gamma> v i)"
  by (induct \<Gamma> arbitrary: i) simp_all

lemma evalD_evalDdb_open:
  assumes "set (free e) \<subseteq> set \<Gamma>"
  assumes "\<forall>v \<in> set \<Gamma>. \<rho>'\<cdot>(index \<Gamma> v 0) = \<rho>\<cdot>v"
  shows "\<lbrakk>e\<rbrakk>\<rho> = evalDdb (transdb e \<Gamma>)\<cdot>\<rho>'"
using assms
proof(induct e arbitrary: \<Gamma> \<rho> \<rho>')
  case AbsN thus ?case
    apply (clarsimp simp: cfun_eq_iff)
    apply (subst AbsN.hyps)
    apply (auto simp: cfun_eq_iff env_ext_db_def index_Suc)
    done
next
  case AbsV thus ?case
    apply (clarsimp simp: cfun_eq_iff)
    apply (case_tac "x=\<bottom>")
     apply simp
    apply simp
    apply (subst AbsV.hyps)
    apply (auto simp: cfun_eq_iff env_ext_db_def index_Suc)
    done
next
  case Fix thus ?case
    apply (clarsimp simp: cfun_eq_iff)
    apply (rule parallel_fix_ind)
      apply simp
     apply simp
    apply simp
    apply (subst Fix.hyps)
    apply (auto simp: cfun_eq_iff env_ext_db_def index_Suc)
    done
qed auto

(*>*)
lemma evalD_evalDdb:
  assumes "free e = []"
  shows "\<lbrakk>e\<rbrakk>\<rho> = evalDdb (transdb e [])\<cdot>\<rho>"
  using assms by (simp add: evalD_evalDdb_open)

text{*

Conversely, all de Bruijn expressions have named equivalents.

*}

primrec
  transdb_inv :: "db \<Rightarrow> (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var \<Rightarrow> expr"
where
  "transdb_inv (DBVar i) \<Gamma> c k = Var (\<Gamma> i)"
| "transdb_inv (DBApp t1 t2) \<Gamma> c k = App (transdb_inv t1 \<Gamma> c k) (transdb_inv t2 \<Gamma> c k)"
| "transdb_inv (DBAbsN e) \<Gamma> c k = AbsN (c + k) (transdb_inv e (case_nat (c + k) \<Gamma>) c (k + 1))"
| "transdb_inv (DBAbsV e) \<Gamma> c k = AbsV (c + k) (transdb_inv e (case_nat (c + k) \<Gamma>) c (k + 1))"
| "transdb_inv (DBDiverge) \<Gamma> c k = Diverge"
| "transdb_inv (DBFix e) \<Gamma> c k = Fix (c + k) (transdb_inv e (case_nat (c + k) \<Gamma>) c (k + 1))"
| "transdb_inv (DBtt) \<Gamma> c k = tt"
| "transdb_inv (DBff) \<Gamma> c k = ff"
| "transdb_inv (DBCond i t e) \<Gamma> c k =
                     Cond (transdb_inv i \<Gamma> c k) (transdb_inv t \<Gamma> c k) (transdb_inv e \<Gamma> c k)"
| "transdb_inv (DBNum n) \<Gamma> c k = (Num n)"
| "transdb_inv (DBSucc e) \<Gamma> c k = Succ (transdb_inv e \<Gamma> c k)"
| "transdb_inv (DBPred e) \<Gamma> c k = Pred (transdb_inv e \<Gamma> c k)"
| "transdb_inv (DBIsZero e) \<Gamma> c k = IsZero (transdb_inv e \<Gamma> c k)"
(*<*)

(* FIXME These proofs are ghastly. Is there a better way to do this? *)

lemma transdb_inv_open:
  assumes "\<forall>v. freedb e v \<longrightarrow> v < c + k"
  assumes "\<forall>v. freedb e v \<longrightarrow> \<Gamma> v = (if k \<le> v then v - k else c + k - v - 1)"
  assumes "\<forall>v. freedb e v \<longrightarrow> (if k \<le> v then index \<Gamma>' (v - k) 0 = v else index \<Gamma>' (c + k - v - 1) 0 = v)"
  shows "transdb (transdb_inv e \<Gamma> c k) \<Gamma>' = e"
using assms
proof(induct e arbitrary: \<Gamma> \<Gamma>' k)
  case DBVar thus ?case by (simp split: if_splits)
next
  case (DBApp e1 e2 \<Gamma> \<Gamma>') thus ?case
    apply -
    apply (drule_tac x=k in meta_spec)+
    apply (drule_tac x=\<Gamma> in meta_spec, drule_tac x=\<Gamma>' in meta_spec)+
    apply auto
    done
next
  case (DBAbsN e \<Gamma> \<Gamma>' k) show ?case
    apply simp
    apply (rule DBAbsN.hyps)

    using DBAbsN
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp

    using DBAbsN
    apply (clarsimp split: nat.split)

    using DBAbsN
    apply clarsimp
    apply (case_tac v)
    apply (auto simp: index_Suc)
    done
next
  case (DBAbsV e \<Gamma> \<Gamma>' k) show ?case
    apply simp
    apply (rule DBAbsV.hyps)

    using DBAbsV
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp

    using DBAbsV
    apply (clarsimp split: nat.split)

    using DBAbsV
    apply clarsimp
    apply (case_tac v)
    apply (auto simp: index_Suc)
    done
next
  case (DBFix e \<Gamma> \<Gamma>' k) show ?case
    apply simp
    apply (rule DBFix.hyps)

    using DBFix
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp

    using DBFix
    apply (clarsimp split: nat.split)

    using DBFix
    apply clarsimp
    apply (case_tac v)
    apply (auto simp: index_Suc)
    done
next
  case (DBCond i t e \<Gamma> \<Gamma>' k) thus ?case
    apply -
    apply (drule_tac x=k in meta_spec)+
    apply (drule_tac x=\<Gamma> in meta_spec, drule_tac x=\<Gamma>' in meta_spec)+
    apply auto
    done
qed simp_all

(*>*)
text{**}

lemma transdb_inv:
  assumes "closed e"
  shows "transdb (transdb_inv e \<Gamma> c k) \<Gamma>' = e"
(*<*)
  using transdb_inv_open assms
  unfolding closed_def by simp

lemma closed_transdb_inv_aux:
  assumes "\<forall>v. freedb e v \<longrightarrow> v < k"
  assumes "\<forall>v. freedb e v \<longrightarrow> \<Gamma> v = k - v - 1"
  shows "i \<in> set (free (transdb_inv e \<Gamma> 0 k)) \<longleftrightarrow> (i < k \<and> freedb e (k - i - 1))"
using assms
proof(induct e arbitrary: \<Gamma> k)
  case (DBAbsN e \<Gamma> k) thus ?case
    apply -
    apply (drule_tac x="Suc k" in meta_spec)
    apply (drule_tac x="case_nat k \<Gamma>" in meta_spec)
    apply simp
    apply (subgoal_tac "\<forall>v. freedb e v \<longrightarrow> v < Suc k")
     apply (subgoal_tac "\<forall>v. freedb e v \<longrightarrow> case_nat k \<Gamma> v = k - v")
      apply rule
       apply (subgoal_tac "Suc (k - Suc i) = k - i")
        apply simp
       apply auto[1]
      apply (subgoal_tac "Suc (k - Suc i) = k - i")
       apply auto[1]
      apply auto[1]
     apply (auto split: nat.splits)[1]
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp
    done
next
  case (DBAbsV e \<Gamma> k) thus ?case
    apply -
    apply (drule_tac x="Suc k" in meta_spec)
    apply (drule_tac x="case_nat k \<Gamma>" in meta_spec)
    apply simp
    apply (subgoal_tac "\<forall>v. freedb e v \<longrightarrow> v < Suc k")
     apply (subgoal_tac "\<forall>v. freedb e v \<longrightarrow> case_nat k \<Gamma> v = k - v")
      apply rule
       apply (subgoal_tac "Suc (k - Suc i) = k - i")
        apply simp
       apply auto[1]
      apply (subgoal_tac "Suc (k - Suc i) = k - i")
       apply auto[1]
      apply auto[1]
     apply (auto split: nat.splits)[1]
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp
    done
next
  case (DBFix e \<Gamma> k) thus ?case
    apply -
    apply (drule_tac x="Suc k" in meta_spec)
    apply (drule_tac x="case_nat k \<Gamma>" in meta_spec)
    apply simp
    apply (subgoal_tac "\<forall>v. freedb e v \<longrightarrow> v < Suc k")
     apply (subgoal_tac "\<forall>v. freedb e v \<longrightarrow> case_nat k \<Gamma> v = k - v")
      apply rule
       apply (subgoal_tac "Suc (k - Suc i) = k - i")
        apply simp
       apply auto[1]
      apply (subgoal_tac "Suc (k - Suc i) = k - i")
       apply auto[1]
      apply auto[1]
     apply (auto split: nat.splits)[1]
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp
    done
qed auto

lemma closed_transdb_inv:
  assumes "closed e"
  shows "free (transdb_inv e \<Gamma> 0 0) = []"
  using assms closed_transdb_inv_aux[where e=e and k=0 and \<Gamma>=\<Gamma>]
  unfolding closed_def by fastforce

(*>*)


subsection{* Operational Semantics *}

text {*

The evaluation relation (big-step, or natural operational
semantics). This is similar to \citet[\S6.2]{Gunter:1992},
\citet{DBLP:conf/mfps/Pitts93} and \citet[Chapter~11]{Winskel:1993}.

We firstly define the \emph{values} that expressions can evaluate to:
these are either constants or closed abstractions.

*}

inductive
  val :: "db \<Rightarrow> bool"
where
  v_Num[intro]: "val (DBNum n)"
| v_FF[intro]:  "val DBff"
| v_TT[intro]:  "val DBtt"
| v_AbsN[intro]: "closed (DBAbsN e) \<Longrightarrow> val (DBAbsN e)"
| v_AbsV[intro]: "closed (DBAbsV e) \<Longrightarrow> val (DBAbsV e)"

inductive
  evalOP :: "db \<Rightarrow> db \<Rightarrow> bool" ("_ \<Down> _" [50,50] 50)
where
  evalOP_AppN[intro]:  "\<lbrakk> P \<Down> DBAbsN M; M<Q/0> \<Down> V \<rbrakk> \<Longrightarrow> DBApp P Q \<Down> V" (* Lazy application *)
| evalOP_AppV[intro]:  "\<lbrakk> P \<Down> DBAbsV M; Q \<Down> q; M<q/0> \<Down> V \<rbrakk> \<Longrightarrow> DBApp P Q \<Down> V" (* Strict application *)
| evalOP_AbsN[intro]:  "val (DBAbsN e) \<Longrightarrow> DBAbsN e \<Down> DBAbsN e"
| evalOP_AbsV[intro]:  "val (DBAbsV e) \<Longrightarrow> DBAbsV e \<Down> DBAbsV e"
| evalOP_Fix[intro]: "P<DBFix P/0> \<Down> V \<Longrightarrow> DBFix P \<Down> V" (* Lazy fix *)
| evalOP_tt[intro]:  "DBtt \<Down> DBtt"
| evalOP_ff[intro]:  "DBff \<Down> DBff"
| evalOP_CondTT[intro]: "\<lbrakk> C \<Down> DBtt; T \<Down> V \<rbrakk> \<Longrightarrow> DBCond C T E \<Down> V"
| evalOP_CondFF[intro]: "\<lbrakk> C \<Down> DBff; E \<Down> V \<rbrakk> \<Longrightarrow> DBCond C T E  \<Down> V"
| evalOP_Num[intro]:  "DBNum n \<Down> DBNum n"
| evalOP_Succ[intro]: "P \<Down> DBNum n \<Longrightarrow> DBSucc P \<Down> DBNum (Suc n)"
| evalOP_Pred[intro]: "P \<Down> DBNum (Suc n) \<Longrightarrow> DBPred P \<Down> DBNum n"
| evalOP_IsZeroTT[intro]: "\<lbrakk> E \<Down> DBNum 0 \<rbrakk> \<Longrightarrow> DBIsZero E \<Down> DBtt"
| evalOP_IsZeroFF[intro]: "\<lbrakk> E \<Down> DBNum n; 0 < n \<rbrakk> \<Longrightarrow> DBIsZero E \<Down> DBff"

text{*

It is straightforward to show that this relation is deterministic and
sound with respect to the denotational semantics.

*}
(*<*)

lemma closed_val [iff]:
  "val e \<Longrightarrow> closed e"
  by (cases e rule: val.cases) auto

inductive_cases evalOP_inv [elim]:
  "DBApp P Q \<Down> v"
  "DBAbs e \<Down> v"
  "DBFix P \<Down> v"
  "DBtt \<Down> v"
  "DBff \<Down> v"
  "DBCond C T E \<Down> v"
  "DBNum n \<Down> v"
  "DBSucc E \<Down> v"
  "DBPred E \<Down> v"
  "DBIsZero E \<Down> v"

lemma eval_val:
  assumes a: "val t"
  shows "t \<Down> t"
  using a by (induct) blast+

lemma eval_to [iff]:
  assumes a: "t \<Down> t'"
  shows "val t'"
  using a by (induct) blast+

lemma evalOP_deterministic:
  "\<lbrakk> P \<Down> V; P \<Down> V' \<rbrakk> \<Longrightarrow> V = V'"
  apply (induct arbitrary: V' rule: evalOP.induct)
  prefer 2 (* FIXME weird *)
  apply (erule evalOP_inv, blast)
  apply blast+
  done

text{* The denotational semantics respects substitution. *}

lemma evalDdb_lift [simp]:
  "evalDdb (lift s k)\<cdot>\<rho> = evalDdb s\<cdot>(\<Lambda> i. if i < k then \<rho>\<cdot>i else \<rho>\<cdot>(Suc i))"
proof(induct s arbitrary: k \<rho> \<rho>')
  case DBAbsN thus ?case
    apply (clarsimp simp: cfun_eq_iff env_ext_db_def)
    apply (rule cfun_arg_cong)
    apply (auto split: nat.split simp: cfun_eq_iff)
    done
next
  case DBAbsV thus ?case
    apply (clarsimp simp: cfun_eq_iff env_ext_db_def)
    apply (case_tac "x=\<bottom>")
     apply simp
    apply (intro cfun_cong)
    apply (auto split: nat.split simp: cfun_eq_iff cong: cfun_cong)
    apply (intro cfun_cong) (* FIXME weird *)
    apply (auto split: nat.split simp: cfun_eq_iff cong: cfun_cong)
    done
next
  case (DBFix s k \<rho>) thus ?case
    apply (clarsimp simp: cfun_eq_iff env_ext_db_def)
    apply (rule parallel_fix_ind)
      apply simp
     apply simp
    apply simp
    apply (rule cfun_arg_cong)
    apply (auto split: nat.split simp: cfun_eq_iff)
    done
qed simp_all

lemma evalDdb_subst:
  "evalDdb (e<s/x>)\<cdot>\<rho> = evalDdb e\<cdot>(\<Lambda> i. if x < i then \<rho>\<cdot>(i - 1) else if i = x then evalDdb s\<cdot>\<rho> else \<rho>\<cdot>i)"
proof(induct e arbitrary: s x \<rho>)
  case DBAbsN thus ?case
    apply simp
    apply (clarsimp simp: cfun_eq_iff)
    apply (rule cfun_arg_cong)
    apply (clarsimp simp: cfun_eq_iff)
    apply (auto simp: eta_cfun env_ext_db_def split: nat.split)
    done
next
  case DBAbsV thus ?case
    apply simp
    apply (clarsimp simp: cfun_eq_iff)
    apply (intro cfun_cong)
    apply (clarsimp simp: cfun_eq_iff)
    apply (auto simp: cfun_eq_iff eta_cfun env_ext_db_def split: nat.split)
    apply (intro cfun_cong) (* FIXME weird *)
    apply (auto simp: cfun_eq_iff eta_cfun env_ext_db_def split: nat.split)
    done
next
  case (DBFix e s x \<rho>) thus ?case
    apply simp
    apply (rule parallel_fix_ind)
      apply simp
     apply simp
    apply (clarsimp simp: cfun_eq_iff)
    apply (rule cfun_arg_cong)
    apply (clarsimp simp: cfun_eq_iff)
    apply (auto simp: eta_cfun env_ext_db_def split: nat.split)
    done
qed simp_all

lemma evalDdb_subst_env_ext_db:
  "evalDdb (e<s/0>)\<cdot>\<rho> = evalDdb e\<cdot>(env_ext_db\<cdot>(evalDdb s\<cdot>\<rho>)\<cdot>\<rho>)"
  apply (subst evalDdb_subst)
  apply (rule cfun_arg_cong)
  apply (auto simp: env_ext_db_def cfun_eq_iff split: nat.split)
  done

lemma eval_val_not_bot:
  "P \<Down> V \<Longrightarrow> evalDdb V\<cdot>\<rho> \<noteq> \<bottom>"
  apply (drule eval_to)
  apply (cases rule: val.induct)
  apply simp_all
  done

(*>*)
lemma evalOP_sound:
  assumes "P \<Down> V"
  shows "evalDdb P\<cdot>\<rho> = evalDdb V\<cdot>\<rho>"
(*<*)
using assms
proof(induct arbitrary: \<rho>)
  case evalOP_AppN thus ?case
    by (simp add: evalOP_AppN(4)[symmetric] evalDdb_subst_env_ext_db)
next
  case (evalOP_AppV P M Q q V \<rho>) thus ?case
    apply simp
    apply (subst evalOP_AppV(4)[symmetric])
    apply (simp add: eval_val_not_bot strictify_cancel evalDdb_subst_env_ext_db)
    done
next
  case (evalOP_Fix P V \<rho>)
  have "evalDdb V\<cdot>\<rho> = evalDdb (P<DBFix P/0>)\<cdot>\<rho>"
    using evalOP_Fix by simp
  also have "... = evalDdb P\<cdot>(\<Lambda> i. if 0 < i then \<rho>\<cdot>(i - 1) else if i = 0 then (\<mu> x. evalDdb P\<cdot>(env_ext_db\<cdot>x\<cdot>\<rho>)) else \<rho>\<cdot>i)"
    apply (simp add: evalDdb_subst)
    apply (rule cfun_arg_cong)
    apply (simp add: cfun_eq_iff)
    done
  also have "... = evalDdb (DBFix P)\<cdot>\<rho>"
    apply simp
    apply (subst fix_eq) back
    apply (simp add: env_ext_db_def)
    apply (rule cfun_arg_cong)
    apply (auto simp: cfun_eq_iff env_ext_db_def split: nat.split)
    done
  finally show ?case by simp
qed (simp_all add: cond_def isZero_def pred_def succ_def)

(*>*)
text{*

We can use soundness to conclude that POR is not definable
operationally either. We rely on @{thm [source] "transdb_inv"} to map
our de Bruijn term into the syntactic universe of
\S\ref{sec:directsem} and appeal to the results of
\S\ref{sec:por}. This takes some effort as @{typ "ValD"} contains
irrelevant junk that makes it hard to draw obvious conclusions; we use
@{text "DBCond"} to restrict the arguments to the putative witness.

*}

definition
  "isPORdb e \<equiv> closed e
    \<and> DBApp (DBApp e DBtt) DBDiverge \<Down> DBtt
    \<and> DBApp (DBApp e DBDiverge) DBtt \<Down> DBtt
    \<and> DBApp (DBApp e DBff) DBff \<Down> DBff"

(*<*)
lemma ValD_strict:
  "\<lbrakk> f\<cdot>a\<cdot>b = ValTT; f\<cdot>x\<cdot>y = ValFF \<rbrakk> \<Longrightarrow> f\<cdot>\<bottom>\<cdot>\<bottom> = \<bottom>"
using monofun_cfun[OF monofun_cfun_arg[where f=f and x="\<bottom>" and y=x], where x="\<bottom>" and y=y, simplified]
      monofun_cfun[OF monofun_cfun_arg[where f=f and x="\<bottom>" and y=a], where x="\<bottom>" and y=b, simplified]
apply (cases "f\<cdot>\<bottom>\<cdot>\<bottom>")
apply simp_all
done

lemma ValD_ValTT:
  "\<lbrakk> f\<cdot>\<bottom>\<cdot>ValTT = ValTT; f\<cdot>ValTT\<cdot>\<bottom> = ValTT \<rbrakk> \<Longrightarrow> f\<cdot>ValTT\<cdot>ValTT = ValTT"
using monofun_cfun[OF monofun_cfun_arg[where f=f and x="\<bottom>"], where x="ValTT" and y="ValTT"]
apply (cases "f\<cdot>ValTT\<cdot>ValTT")
apply simp_all
done
(*>*)

lemma POR_is_not_operationally_definable: "\<not>isPORdb e"
(*<*)
proof
  assume P: "isPORdb e"
  let ?porV = "ValF\<cdot>(\<Lambda> x. ValF\<cdot>(\<Lambda> y. x por y))"
  { fix \<rho>
    from P have "closed e
       \<and> evalDdb (DBApp (DBApp e DBtt) DBDiverge)\<cdot>\<rho> = ValTT
       \<and> evalDdb (DBApp (DBApp e DBDiverge) DBtt)\<cdot>\<rho> = ValTT
       \<and> evalDdb (DBApp (DBApp e DBff) DBff)\<cdot>\<rho> = ValFF"
      unfolding isPORdb_def
      apply -
      apply (elim conjE)
      apply (drule evalOP_sound[where \<rho>=\<rho>])+
      apply simp
      done
    hence "closed e
      \<and> \<lbrakk>transdb_inv (DBApp (DBApp e DBtt) DBDiverge) id 0 0\<rbrakk>\<rho> = ValTT
      \<and> \<lbrakk>transdb_inv (DBApp (DBApp e DBDiverge) DBtt) id 0 0\<rbrakk>\<rho> = ValTT
      \<and> \<lbrakk>transdb_inv (DBApp (DBApp e DBff) DBff) id 0 0\<rbrakk>\<rho> = ValFF"
      (* id is arbitrary here *)
      by (simp add: evalD_evalDdb transdb_inv closed_transdb_inv) }
  note F = this
  { fix \<rho>
    from F have "appF\<cdot>(appF\<cdot>(\<lbrakk>transdb_inv e id 0 0\<rbrakk>\<rho>)\<cdot>\<bottom>)\<cdot>\<bottom> = \<bottom>"
      by (auto intro: ValD_strict[where f="\<Lambda> x y. appF\<cdot>(appF\<cdot>(\<lbrakk>transdb_inv e id 0 0\<rbrakk>\<rho>)\<cdot>x)\<cdot>y", simplified]) }
  note G = this
  { fix \<rho>
    from F have "appF\<cdot>(appF\<cdot>(\<lbrakk>transdb_inv e id 0 0\<rbrakk>\<rho>)\<cdot>ValTT)\<cdot>ValTT = ValTT"
      using ValD_ValTT[where f="\<Lambda> x y. appF\<cdot>(appF\<cdot>(\<lbrakk>transdb_inv e id 0 0\<rbrakk>\<rho>)\<cdot>x)\<cdot>y"]
      by simp }
  note H = this
  let ?f = "AbsN 0 (AbsN 1 (App (App (transdb_inv e id 0 0)
                                     (Cond (Var 0) (Var 0) (Cond (Var 1) (Var 1) (Var 1))) )
                                     (Cond (Var 1) (Var 1) (Cond (Var 0) (Var 0) (Var 0))) ))"
  from F G H have "\<lbrakk>?f\<rbrakk>env_empty = ?porV"
    apply (clarsimp simp: cfun_eq_iff cond_def)
    apply (case_tac x, simp_all)
     apply (case_tac xa, simp_all)+
    done
  with POR_sat have "definable ?porV \<and> appFLv ?porV [POR_arg1_rel, POR_arg2_rel] = POR_result_rel"
    unfolding definable_def by blast
  with POR_is_not_definable show False by blast
qed
(*>*)


subsection{* Computational Adequacy *}

text{*

\label{sec:compad}

The lemma @{thm [source] "evalOP_sound"} tells us that the operational
semantics preserves the denotational semantics. We might also hope
that the two are somehow equivalent, but due to the junk in the
domain-theoretic model (see \S\ref{sec:pcfdefinability}) we cannot
expect this to be entirely straightforward. Here we show that the
denotational semantics is \emph{computationally adequate}, which means
that it can be used to soundly reason about contextual equivalence.

We follow \citet{DBLP:conf/mfps/Pitts93,PittsAM:relpod} by defining a
suitable logical relation between our @{typ "ValD"} domain and the set
of programs (closed terms). These are termed "formal approximation
relations" by Plotkin. The machinery of \S\ref{sec:synlr} requires us
to define a unique bottom element, which in this case is @{term "{\<bottom>} \<times>
{ P . closed P}"}. To that end we define the type of programs.

*}

typedef Prog = "{ P. closed P }"
  morphisms unProg mkProg by fastforce

definition
  ca_lf_rep :: "(ValD, Prog) synlf_rep"
where
  "ca_lf_rep \<equiv> \<lambda>(rm, rp).
     ({\<bottom>} \<times> UNIV)
     \<union> { (d, P) |d P.
        (\<exists>n. d = ValN\<cdot>n \<and> unProg P \<Down> DBNum n)
      \<or> (d = ValTT \<and> unProg P \<Down> DBtt)
      \<or> (d = ValFF \<and> unProg P \<Down> DBff)
      \<or> (\<exists>f M. d = ValF\<cdot>f \<and> unProg P \<Down> DBAbsN M
              \<and> (\<forall>(x, X) \<in> unsynlr (undual rm). (f\<cdot>x, mkProg (M<unProg X/0>)) \<in> unsynlr rp))
      \<or> (\<exists>f M. d = ValF\<cdot>f \<and> unProg P \<Down> DBAbsV M \<and> f\<cdot>\<bottom> = \<bottom>
              \<and> (\<forall>(x, X) \<in> unsynlr (undual rm). \<forall>V. unProg X \<Down> V
                     \<longrightarrow> (f\<cdot>x, mkProg (M<V/0>)) \<in> unsynlr rp)) }"

abbreviation ca_lr :: "(ValD, Prog) synlf" where
  "ca_lr \<equiv> \<lambda>r. mksynlr (ca_lf_rep r)"

text{*

Intuitively we relate domain-theoretic values to all programs that
converge to the corresponding syntatic values. If a program has a
non-@{term "\<bottom>"} denotation then we can use this relation to conclude
something about the value it (operationally) converges to.

*}
(*<*)

lemmas Prog_simps [iff] =
  unProg_inverse
  mkProg_inverse[simplified]

lemma bot_ca_lf_rep [intro, simp]:
  "(\<bottom>, P) \<in> ca_lf_rep r"
  unfolding ca_lf_rep_def by (simp add: split_def)

lemma synlr_cal_lr_rep [intro, simp]:
  "ca_lf_rep r \<in> synlr"
  unfolding ca_lf_rep_def
  apply rule
  by (auto intro!: adm_conj adm_disj adm_below_monic_exists
             simp: split_def
             dest: evalOP_deterministic)

lemma mono_ca_lr:
  shows "mono ca_lr"
  apply (rule monoI)
  apply simp
  apply (simp add: ca_lf_rep_def unsynlr_leq[symmetric] undual_leq[symmetric] split_def)
  apply (fastforce simp: unsynlr_leq[symmetric] undual_leq[symmetric])+
  done

lemma min_inv_ca_lr:
  assumes "e\<cdot>\<bottom> = \<bottom>"
  assumes "eRSS e R' S'"
  shows "eRSS (ValD_copy_rec\<cdot>e) (dual (ca_lr (dual S', undual R'))) (ca_lr (R', S'))"
  apply simp
  unfolding ca_lf_rep_def using assms
  apply simp
  apply (rule ballI)
  apply (simp add: split_def)
  apply (elim disjE)
  apply fastforce
  apply fastforce
  apply fastforce
  apply fastforce

  (* FIXME fastforce gets lost ?? AbsN *)
  apply clarsimp
  apply (rule_tac x=M in exI)
  apply clarsimp
  apply (frule (1) bspec)
  apply simp
  apply (frule (1) bspec) back
  apply simp
  apply (frule (1) bspec) back
  apply simp

  (* FIXME fastforce gets lost ?? AbsV *)
  apply (intro disjI2)
  apply clarsimp
  apply (rule_tac x=M in exI)
  apply clarsimp
  apply (frule (1) bspec)
  apply simp
  apply (frule (1) bspec) back
  apply simp
  apply (frule (1) bspec) back
  apply bestsimp
  done

(*>*)
text{**}

interpretation ca: DomSolSyn ValD_copy_rec ca_lr
  apply standard
     apply (rule ValD_copy_ID)
    apply simp
   apply (rule mono_ca_lr)
  apply (erule (1) min_inv_ca_lr)
  done

definition ca_lr_syn :: "ValD \<Rightarrow> db \<Rightarrow> bool" ("_ \<triangleleft> _" [80,80] 80) where
  "d \<triangleleft> P \<equiv> (d, P) \<in> { (x, unProg Y) |x Y. (x, Y) \<in> unsynlr ca.delta }"
(*<*)

lemma adm_ca_lr [intro, simp]:
  "closed P \<Longrightarrow> adm (\<lambda>x. x \<triangleleft> P)"
  unfolding ca_lr_syn_def
  by (auto simp: unProg_inject)

lemma closed_ca_lr [intro]:
  "d \<triangleleft> P \<Longrightarrow> closed P"
  apply (subst (asm) ca_lr_syn_def)
  apply (subst (asm) ca.delta_sol)
  apply simp
  apply (clarsimp simp: ca_lf_rep_def)
  apply (case_tac Y)
  apply simp
  done

lemma ca_lrI [intro, simp]:
  "closed P \<Longrightarrow> \<bottom> \<triangleleft> P"
  "\<lbrakk> P \<Down> DBtt; closed P \<rbrakk> \<Longrightarrow> ValTT \<triangleleft> P"
  "\<lbrakk> P \<Down> DBff; closed P \<rbrakk> \<Longrightarrow> ValFF \<triangleleft> P"
  "\<lbrakk> P \<Down> DBNum n; closed P \<rbrakk> \<Longrightarrow> ValN\<cdot>n \<triangleleft> P"
  apply (simp_all add: ca_lr_syn_def)
  apply (simp add: exI[where x="mkProg P"])
  apply ((subst ca.delta_sol, simp, subst ca_lf_rep_def, simp add: exI[where x="mkProg P"])+)
  done

lemma ca_lr_DBAbsNI:
  "\<lbrakk> P \<Down> DBAbsN M; closed P; \<And>x X. x \<triangleleft> X \<Longrightarrow> f\<cdot>x \<triangleleft> M<X/0> \<rbrakk> \<Longrightarrow> ValF\<cdot>f \<triangleleft> P"
  apply (simp add: ca_lr_syn_def)
  apply (subst ca.delta_sol)
  apply simp
  apply (rule exI[where x="mkProg P"])
  apply (subst ca_lf_rep_def)
  apply simp
  apply (rule disjI1)
  apply (rule exI[where x=M])
  apply force
  done

lemma ca_lr_DBAbsVI:
  "\<lbrakk> P \<Down> DBAbsV M; closed P; f\<cdot>\<bottom> = \<bottom>; \<And>x X V. \<lbrakk> x \<triangleleft> X; X \<Down> V \<rbrakk> \<Longrightarrow> f\<cdot>x \<triangleleft> M<V/0> \<rbrakk> \<Longrightarrow> ValF\<cdot>f \<triangleleft> P"
  apply (simp add: ca_lr_syn_def)
  apply (subst ca.delta_sol)
  apply simp
  apply (rule exI[where x="mkProg P"])
  apply (subst ca_lf_rep_def)
  apply simp
  apply force
  done

lemma ca_lrE:
  "\<lbrakk> d \<triangleleft> P;
     \<lbrakk> d = \<bottom>; closed P \<rbrakk> \<Longrightarrow> Q;
     \<lbrakk> d = ValTT; closed P; P \<Down> DBtt \<rbrakk> \<Longrightarrow> Q;
     \<lbrakk> d = ValFF; closed P; P \<Down> DBff \<rbrakk> \<Longrightarrow> Q;
     \<And>n. \<lbrakk> d = ValN\<cdot>n; closed P; P \<Down> DBNum n \<rbrakk> \<Longrightarrow> Q;
     \<And>f M. \<lbrakk> d = ValF\<cdot>f; closed P; P \<Down> DBAbsN M; \<And>x X. x \<triangleleft> X \<Longrightarrow> f\<cdot>x \<triangleleft> M<X/0> \<rbrakk> \<Longrightarrow> Q;
     \<And>f M. \<lbrakk> d = ValF\<cdot>f; f\<cdot>\<bottom> = \<bottom>; closed P; P \<Down> DBAbsV M; \<And>x X V. \<lbrakk> x \<triangleleft> X; X \<Down> V \<rbrakk> \<Longrightarrow> f\<cdot>x \<triangleleft> M<V/0> \<rbrakk> \<Longrightarrow> Q
   \<rbrakk> \<Longrightarrow> Q"
  apply (simp add: ca_lr_syn_def)
  apply (subst (asm) ca.delta_sol)
  apply simp
  apply (subst (asm) ca_lf_rep_def)
  apply clarsimp
  apply (case_tac Y)
  apply (elim disjE)
  apply auto

  apply (drule_tac x=f in meta_spec)
  apply (drule_tac x=M in meta_spec)
  apply simp
  apply (subgoal_tac "(\<And>x X. \<exists>Y. X = unProg Y \<and> (x, Y) \<in> unsynlr (DomSolSyn.delta ca_lr) \<Longrightarrow> \<exists>Y. M<X/0> = unProg Y \<and> (f\<cdot>x, Y) \<in> unsynlr (DomSolSyn.delta ca_lr))")
   apply blast
  apply clarsimp
  apply (rule_tac x="mkProg (M<unProg Y/0>)" in exI)
  apply auto[1]
  apply (subst mkProg_inverse)
   apply simp
  apply (drule eval_to)
  apply (drule closed_val)
  apply (subst (asm) closed_binders)
  apply (auto simp: closed_def
             split: nat.splits)[2]
  apply (case_tac Y)
  apply (auto simp: closed_def)[1]

  apply (drule_tac x=f in meta_spec) back
  apply (drule_tac x=M in meta_spec)
  apply simp
  apply (subgoal_tac "(\<And>x X V. \<lbrakk>\<exists>Y. X = unProg Y \<and> (x, Y) \<in> unsynlr (DomSolSyn.delta ca_lr); X \<Down> V\<rbrakk>
                      \<Longrightarrow> \<exists>Y. M<V/0> = unProg Y \<and> (f\<cdot>x, Y) \<in> unsynlr (DomSolSyn.delta ca_lr))")
   apply blast
  apply clarsimp
  apply (drule (1) bspec)
  apply clarsimp
  apply (rule_tac x="mkProg (M<V/0>)" in exI)
  apply clarsimp
  apply (subst mkProg_inverse)
   defer
   apply simp
  apply simp
  apply (drule eval_to)+
  apply (drule closed_val)+
  apply (simp add: closed_binders closed_def split: nat.splits)
  done

(*>*)
text{*

To establish this result we need a ``closing substitution'' operation.
It seems easier to define it directly in this simple-minded way than
reusing the standard substitution operation.

This is quite similar to a context-plugging (non-capturing)
substitution operation, where the ``holes'' are free variables, and
indeed we use it as such below.

*}

fun
  closing_subst :: "db \<Rightarrow> (var \<Rightarrow> db) \<Rightarrow> var \<Rightarrow> db"
where
  "closing_subst (DBVar i) \<Gamma> k = (if k \<le> i then \<Gamma> (i - k) else DBVar i)"
| "closing_subst (DBApp t u) \<Gamma> k = DBApp (closing_subst t \<Gamma> k) (closing_subst u \<Gamma> k)"
| "closing_subst (DBAbsN t) \<Gamma> k = DBAbsN (closing_subst t \<Gamma> (k + 1))"
| "closing_subst (DBAbsV t) \<Gamma> k = DBAbsV (closing_subst t \<Gamma> (k + 1))"
| "closing_subst (DBFix e) \<Gamma> k = DBFix (closing_subst e \<Gamma> (k + 1))"
| "closing_subst (DBCond c t e) \<Gamma> k =
            DBCond (closing_subst c \<Gamma> k) (closing_subst t \<Gamma> k) (closing_subst e \<Gamma> k)"
| "closing_subst (DBSucc e) \<Gamma> k = DBSucc (closing_subst e \<Gamma> k)"
| "closing_subst (DBPred e) \<Gamma> k = DBPred (closing_subst e \<Gamma> k)"
| "closing_subst (DBIsZero e) \<Gamma> k = DBIsZero (closing_subst e \<Gamma> k)"
| "closing_subst x \<Gamma> k = x"

text{*

We can show it has the expected properties when all terms in @{term
"\<Gamma>"} are closed.

*}

(*<*)
lemma freedb_closing_subst [iff]:
  assumes "\<forall>v. freedb e v \<and> k \<le> v \<longrightarrow> closed (\<Gamma> (v - k))"
  shows "freedb (closing_subst e \<Gamma> k) i \<longleftrightarrow> (freedb e i \<and> i < k)"
  using assms
  apply (induct e arbitrary: i k)
  apply (auto simp: closed_def not_less_eq diff_Suc split: nat.split)

    apply (drule_tac x="Suc i" in meta_spec)
    apply (drule_tac x="Suc k" in meta_spec)
    apply simp
    apply (subgoal_tac "\<forall>v. freedb e v \<and> Suc k \<le> v \<longrightarrow> (\<forall>j. \<not> freedb (\<Gamma> (v - Suc k)) j)")
     apply simp
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp

    apply (drule_tac x="Suc i" in meta_spec)
    apply (drule_tac x="Suc k" in meta_spec)
    apply simp
    apply (subgoal_tac "\<forall>v. freedb e v \<and> Suc k \<le> v \<longrightarrow> (\<forall>j. \<not> freedb (\<Gamma> (v - Suc k)) j)")
     apply simp
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp

    apply (drule_tac x="Suc i" in meta_spec)
    apply (drule_tac x="Suc k" in meta_spec)
    apply simp
    apply (subgoal_tac "\<forall>v. freedb e v \<and> Suc k \<le> v \<longrightarrow> (\<forall>j. \<not> freedb (\<Gamma> (v - Suc k)) j)")
     apply simp
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp

    apply (drule_tac x="Suc i" in meta_spec)
    apply (drule_tac x="Suc k" in meta_spec)
    apply simp
    apply (subgoal_tac "\<forall>v. freedb e v \<and> Suc k \<le> v \<longrightarrow> (\<forall>j. \<not> freedb (\<Gamma> (v - Suc k)) j)")
     apply simp
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp

    apply (drule_tac x="Suc i" in meta_spec)
    apply (drule_tac x="Suc k" in meta_spec)
    apply simp
    apply (subgoal_tac "\<forall>v. freedb e v \<and> Suc k \<le> v \<longrightarrow> (\<forall>j. \<not> freedb (\<Gamma> (v - Suc k)) j)")
     apply simp
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp

    apply (drule_tac x="Suc i" in meta_spec)
    apply (drule_tac x="Suc k" in meta_spec)
    apply simp
    apply (subgoal_tac "\<forall>v. freedb e v \<and> Suc k \<le> v \<longrightarrow> (\<forall>j. \<not> freedb (\<Gamma> (v - Suc k)) j)")
     apply simp
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp

    apply (drule_tac x="Suc i" in meta_spec)
    apply (drule_tac x="Suc k" in meta_spec)
    apply simp
    apply (subgoal_tac "\<forall>v. freedb e v \<and> Suc k \<le> v \<longrightarrow> (\<forall>j. \<not> freedb (\<Gamma> (v - Suc k)) j)")
     apply simp
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp

    apply (drule_tac x="Suc i" in meta_spec)
    apply (drule_tac x="Suc k" in meta_spec)
    apply simp
    apply (subgoal_tac "\<forall>v. freedb e v \<and> Suc k \<le> v \<longrightarrow> (\<forall>j. \<not> freedb (\<Gamma> (v - Suc k)) j)")
     apply simp
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp

    apply (drule_tac x="Suc i" in meta_spec)
    apply (drule_tac x="Suc k" in meta_spec)
    apply simp
    apply (subgoal_tac "\<forall>v. freedb e v \<and> Suc k \<le> v \<longrightarrow> (\<forall>j. \<not> freedb (\<Gamma> (v - Suc k)) j)")
     apply simp
    apply clarsimp
    apply (case_tac v)
     apply simp
    apply simp

    done

lemma closed_closing_subst [intro, simp]:
  assumes "\<forall>v. freedb e v \<longrightarrow> closed (\<Gamma> v)"
  shows "closed (closing_subst e \<Gamma> 0)"
  using assms freedb_closing_subst[where e=e and k=0]
  unfolding closed_def
  by fastforce

lemma subst_closing_subst:
  assumes "\<forall>v. freedb e v \<and> k < v \<longrightarrow> closed (\<Gamma> (v - Suc k))"
  assumes "closed X"
  shows "(closing_subst e \<Gamma> (Suc k))<X/k> = closing_subst e (case_nat X \<Gamma>) k"
  using assms
  apply (induct e arbitrary: i k)
  apply (auto simp: not_less_eq split: nat.split)

  apply (subst diff_Suc)
  apply simp
  apply (subst closed_subst)
   apply (clarsimp simp: closed_def)
   apply (metis Suc_lessE diff_Suc_Suc diff_diff_cancel diff_less_Suc order_le_less)
  apply simp

  apply (subst closed_lift)
   apply (simp add: closed_def)
  apply (drule_tac x="Suc k" in meta_spec)
  apply (subgoal_tac "\<forall>v. freedb e v \<and> Suc k < v \<longrightarrow> closed (\<Gamma> (v - Suc (Suc k)))")
   apply blast
  apply (clarsimp simp: closed_def)
  apply (case_tac v)
  apply auto
  done

lemma closing_subst_closed [intro, simp]:
  assumes "\<forall>v. freedb e v \<longrightarrow> v < k"
  shows "closing_subst e \<Gamma> k = e"
  using assms
  apply (induct e arbitrary: i k)
  apply (auto simp: closed_def)
  apply (metis gr_implies_not0 nat.exhaust not_less_eq)+
  done

lemma closing_subst_evalDdb_cong:
  assumes 1: "\<forall>v. closed (\<Gamma> v) \<and> closed (\<Gamma>' v)"
  assumes 2: "\<forall>v. evalDdb (\<Gamma> v)\<cdot>env_empty_db = evalDdb (\<Gamma>' v)\<cdot>env_empty_db"
  shows "evalDdb (closing_subst e \<Gamma> k)\<cdot>\<rho> = evalDdb (closing_subst e \<Gamma>' k)\<cdot>\<rho>"
  apply (induct e arbitrary: i k \<rho>)
  apply simp
  apply (subst evalDdb_env_closed[where \<rho>'=env_empty_db])
   defer
  apply (subst evalDdb_env_closed[where \<rho>'=env_empty_db]) back
   defer
  apply (simp add: 2)
  using 1
  apply auto
  done

(*>*)
text{*

The key lemma is shown by induction over @{term "e"} for arbitrary
environments (@{term "\<Gamma>"} and @{term "\<rho>"}):

*}

lemma ca_open:
  assumes "\<forall>v. freedb e v \<longrightarrow> \<rho>\<cdot>v \<triangleleft> \<Gamma> v \<and> closed (\<Gamma> v)"
  shows "evalDdb e\<cdot>\<rho> \<triangleleft> closing_subst e \<Gamma> 0"
(*<*)
using assms
proof(induct e arbitrary: \<Gamma> \<rho>)
  case (DBApp e1 e2 \<Gamma> \<rho>) thus ?case
    apply simp
    apply (drule_tac x=\<rho> in meta_spec)+
    apply (drule_tac x=\<Gamma> in meta_spec)+
    apply simp
    apply (erule ca_lrE)
     apply simp_all

    apply (drule_tac x="evalDdb e2\<cdot>\<rho>" in meta_spec)
    apply (drule_tac x="closing_subst e2 \<Gamma> 0" in meta_spec)
    apply simp
    apply (erule ca_lrE) back
     apply (auto intro: ca_lr_DBAbsNI ca_lr_DBAbsVI)[6]

    apply (case_tac "evalDdb e2\<cdot>\<rho> = \<bottom>")
     apply simp
    apply (subgoal_tac "\<exists>V. closing_subst e2 \<Gamma> 0 \<Down> V")
     apply clarsimp
     apply (drule_tac x="evalDdb e2\<cdot>\<rho>" in meta_spec)
      apply (drule_tac x="closing_subst e2 \<Gamma> 0" in meta_spec)
      apply (drule_tac x="V" in meta_spec)
      apply simp
      apply (erule ca_lrE) back
       apply (auto intro: ca_lr_DBAbsNI ca_lr_DBAbsVI)[6]
    apply (erule ca_lrE)
    apply auto
    done
next
  case (DBAbsN e \<Gamma> \<rho>) thus ?case
    apply simp
    apply (rule ca_lr_DBAbsNI)
      apply (rule eval_val)
      apply (rule v_AbsN)
      apply (clarsimp simp: closed_def split: nat.split)
     apply clarsimp
    apply simp
    apply (subst subst_closing_subst)
      apply simp
     apply blast
    apply (drule_tac x="env_ext_db\<cdot>x\<cdot>\<rho>" in meta_spec)
    apply (drule_tac x="case_nat X \<Gamma>" in meta_spec)
    apply (subgoal_tac "\<forall>v. freedb e v \<longrightarrow> env_ext_db\<cdot>x\<cdot>\<rho>\<cdot>v \<triangleleft> case_nat X \<Gamma> v \<and> closed (case_nat X \<Gamma> v)")
     apply blast
    apply (auto simp: env_ext_db_def split: nat.splits)
    done
next
  case (DBAbsV e \<Gamma> \<rho>) thus ?case
    apply simp
    apply (rule ca_lr_DBAbsVI)
       apply (rule eval_val)
       apply (rule v_AbsV)
       apply (clarsimp simp: closed_def split: nat.split)
     apply clarsimp
    apply simp
    apply (case_tac "x=\<bottom>")
     apply simp
     apply (rule ca_lrI)
     apply (subst subst_closing_subst)
       apply simp
      apply (simp add: eval_to)
     apply (metis closed_closing_subst closed_def closed_val eval_to nat.case not0_implies_Suc)
    apply simp
    apply (subst subst_closing_subst)
      apply simp
     apply blast
    apply (drule_tac x="env_ext_db\<cdot>x\<cdot>\<rho>" in meta_spec)
    apply (drule_tac x="case_nat V \<Gamma>" in meta_spec)
    apply (subgoal_tac "\<forall>v. freedb e v \<longrightarrow> env_ext_db\<cdot>x\<cdot>\<rho>\<cdot>v \<triangleleft> case_nat V \<Gamma> v \<and> closed (case_nat V \<Gamma> v)")
     apply blast
    apply (auto simp: env_ext_db_def split: nat.splits)
    apply (erule ca_lrE)
      apply (auto dest: evalOP_deterministic)[4]
     apply clarsimp
     apply (subgoal_tac "V = DBAbsN M")
      apply clarsimp
      apply (rule ca_lr_DBAbsNI)
      apply (rule eval_val)
      apply (auto dest: eval_to closed_val evalOP_deterministic)[4]
    apply (subgoal_tac "V = DBAbsV M")
     apply clarsimp
     apply (rule ca_lr_DBAbsVI)
     apply (rule eval_val)
     apply (auto dest: eval_to closed_val evalOP_deterministic)[4]
    apply (auto dest: evalOP_deterministic)
    done
next
  case (DBFix e \<Gamma> \<rho>) thus ?case
    apply simp
    apply (rule fix_ind)
      apply simp_all
    apply (drule_tac x="env_ext_db\<cdot>x\<cdot>\<rho>" in meta_spec)
    apply (drule_tac x="case_nat (closing_subst (DBFix e) \<Gamma> 0) \<Gamma>" in meta_spec)
    apply (subgoal_tac "\<forall>v. freedb e v \<longrightarrow> env_ext_db\<cdot>x\<cdot>\<rho>\<cdot>v \<triangleleft> case_nat (closing_subst (DBFix e) \<Gamma> 0) \<Gamma> v \<and> closed (case_nat (closing_subst (DBFix e) \<Gamma> 0) \<Gamma> v)")
     apply clarsimp
     apply (erule ca_lrE) back
      apply auto[1]

      apply simp
      apply (rule ca_lrI)
       apply (auto simp: subst_closing_subst freedb_closing_subst)[2]

      apply simp
      apply (rule ca_lrI)
       apply (auto simp: subst_closing_subst freedb_closing_subst)[2]

      apply simp
      apply (rule ca_lrI)
       apply (auto simp: subst_closing_subst freedb_closing_subst)[2]

      apply simp
      apply (rule ca_lr_DBAbsNI)
       apply (auto simp: subst_closing_subst freedb_closing_subst)[3]

      apply simp
      apply (rule ca_lr_DBAbsVI)
       apply (auto simp: subst_closing_subst freedb_closing_subst)[3]
       apply force

      apply (clarsimp simp: env_ext_db_def split: nat.split)
    done
next
  case (DBCond c t e \<Gamma> \<rho>) thus ?case
    apply (simp add: cond_def)
    apply (drule_tac x=\<rho> in meta_spec, drule_tac x=\<Gamma> in meta_spec)+
    apply simp
    apply (erule ca_lrE, auto intro: ca_lr_DBAbsNI ca_lr_DBAbsVI)+
    done
next
  case (DBSucc e \<Gamma> \<rho>) thus ?case
    apply (simp add: succ_def)
    apply (drule_tac x=\<rho> in meta_spec, drule_tac x=\<Gamma> in meta_spec)
    apply simp
    apply (erule ca_lrE, auto intro: ca_lr_DBAbsNI ca_lr_DBAbsVI)+
    done
next
  case (DBPred e \<Gamma> \<rho>) thus ?case
    apply (simp add: pred_def)
    apply (drule_tac x=\<rho> in meta_spec, drule_tac x=\<Gamma> in meta_spec)
    apply simp
    apply (erule ca_lrE, auto intro: ca_lr_DBAbsNI ca_lr_DBAbsVI split: nat.split)+
    done
next
  case (DBIsZero e \<Gamma> \<rho>) thus ?case
    apply (simp add: isZero_def)
    apply (drule_tac x=\<rho> in meta_spec, drule_tac x=\<Gamma> in meta_spec)
    apply simp
    apply (erule ca_lrE, auto intro: ca_lr_DBAbsNI ca_lr_DBAbsVI)+
    done
qed auto

(*>*)
text{**}

lemma ca_closed:
  assumes "closed e"
  shows "evalDdb e\<cdot>env_empty_db \<triangleleft> e"
  using ca_open[where e=e and \<rho>=env_empty_db] assms
  by (simp add: closed_def)

theorem ca:
  assumes nb: "evalDdb e\<cdot>env_empty_db \<noteq> \<bottom>"
  assumes "closed e"
  shows "\<exists>V. e \<Down> V"
  using ca_closed[OF `closed e`] nb
  by (auto elim!: ca_lrE)

text{*

This last result justifies reasoning about contextual equivalence
using the denotational semantics, as we now show.

*}


subsubsection{* Contextual Equivalence *}

text{*

As we are using an un(i)typed language, we take a context @{term "C"}
to be an arbitrary term, where the free variables are the
``holes''. We substitute a closed expression @{term "e"} uniformly for
all of the free variables in @{term "C"}. If open, the term @{term
"e"} can be closed using enough @{term "AbsN"}s. This seems to be a
standard trick now, see e.g. \citet{DBLP:conf/popl/KoutavasW06}. If we
didn't have CBN (only CBV) then it might be worth showing that this is
an adequate treatment.

*}

definition ctxt_sub :: "db \<Rightarrow> db \<Rightarrow> db" ("(_<_>)" [300, 0] 300) where
  "C<e> \<equiv> closing_subst C (\<lambda>_. e) 0"
(*<*)

lemma ctxt_sub_closed [iff]:
  "closed e \<Longrightarrow> closed (C<e>)"
  unfolding ctxt_sub_def by simp

lemma ctxt_sub_cong:
  assumes "closed e1"
  assumes "closed e2"
  assumes "evalDdb e1\<cdot>env_empty_db = evalDdb e2\<cdot>env_empty_db"
  shows "evalDdb (C<e1>)\<cdot>env_empty_db = evalDdb (C<e2>)\<cdot>env_empty_db"
  unfolding ctxt_sub_def
  apply (rule closing_subst_evalDdb_cong)
  using assms
  apply simp_all
  done

(*>*)
text{*

Following \citet{PittsAM:relpod} we define a relation between values
that ``have the same form''. This is weak at functional values. We
don't distinguish between strict and non-strict abstractions.

*}

inductive
  have_the_same_form :: "db \<Rightarrow> db \<Rightarrow> bool" ("_ \<sim> _" [50,50] 50)
where
  "DBAbsN e \<sim> DBAbsN e'"
| "DBAbsN e \<sim> DBAbsV e'"
| "DBAbsV e \<sim> DBAbsN e'"
| "DBAbsV e \<sim> DBAbsV e'"
| "DBFix e \<sim> DBFix e'"
| "DBtt \<sim> DBtt"
| "DBff \<sim> DBff"
| "DBNum n \<sim> DBNum n"
(*<*)

declare have_the_same_form.intros [intro, simp]

lemma have_the_same_form_sound:
  assumes D: "evalDdb v1\<cdot>\<rho> = evalDdb v2\<cdot>\<rho>"
  assumes "val v1"
  assumes "val v2"
  shows "v1 \<sim> v2"
  using `val v1` D
  apply (induct rule: val.induct)
  apply simp_all
  using `val v2`
  apply (induct rule: val.induct)
  apply simp_all
  using `val v2`
  apply (induct rule: val.induct)
  apply simp_all
  using `val v2`
  apply (induct rule: val.induct)
  apply simp_all
  using `val v2`
  apply (induct rule: val.induct)
  apply simp_all
  using `val v2`
  apply (induct rule: val.induct)
  apply simp_all
  done

(* FIXME could also show compatability, i.e. that the
contextually_equivalent relation is compatible with the language. *)

(*>*)
text{*

A program @{term "e2"} \emph{refines} the program @{term "e1"} if it
converges in context at least as often. This is a preorder on
programs.

*}

definition
  refines :: "db \<Rightarrow> db \<Rightarrow> bool" ("_ \<unlhd> _" [50,50] 50)
where
  "e1 \<unlhd> e2 \<equiv> \<forall>C. \<exists>V1. C<e1> \<Down> V1 \<longrightarrow> (\<exists>V2. C<e2> \<Down> V2 \<and> V1 \<sim> V2)"

text{*

Contextually-equivalent programs refine each other.

*}

definition
  contextually_equivalent :: "db \<Rightarrow> db \<Rightarrow> bool" ("_ \<approx> _")
where
  "e1 \<approx> e2 \<equiv> e1 \<unlhd> e2 \<and> e2 \<unlhd> e1"
(*<*)

lemma refinesI:
  "(\<And>C V1. C<e1> \<Down> V1 \<Longrightarrow> (\<exists>V2. C<e2> \<Down> V2 \<and> V1 \<sim> V2))
     \<Longrightarrow> e1 \<unlhd> e2"
  unfolding refines_def by blast

lemma computational_adequacy_refines:
  assumes "closed e1"
  assumes "closed e2"
  assumes e: "evalDdb e1\<cdot>env_empty_db = evalDdb e2\<cdot>env_empty_db"
  shows "e1 \<unlhd> e2"
proof(rule refinesI)
  fix C V1 assume V1: "C<e1> \<Down> V1"
  from assms have D: "evalDdb (C<e2>)\<cdot>env_empty_db = evalDdb (C<e1>)\<cdot>env_empty_db"
    by (metis ctxt_sub_cong)
  from D `closed e2` obtain V2 where V2: "C<e2> \<Down> V2"
    using evalOP_sound[OF V1]
    using ca[where e="C<e2>"]
    using eval_val_not_bot[OF V1]
    apply auto
    done
  from D V1 V2 have V1V2: "evalDdb V1\<cdot>env_empty_db = evalDdb V2\<cdot>env_empty_db"
    by (simp add: evalOP_sound)
  from V1 V2 V1V2
  show "\<exists>V2. C<e2> \<Down> V2 \<and> V1 \<sim> V2"
    by (auto simp: have_the_same_form_sound)
qed

(*>*)
text{*

Our ultimate theorem states that if two programs have the same
denotation then they are contextually equivalent.

*}

theorem computational_adequacy:
  assumes 1: "closed e1"
  assumes 2: "closed e2"
  assumes D: "evalDdb e1\<cdot>env_empty_db = evalDdb e2\<cdot>env_empty_db"
  shows "e1 \<approx> e2"
(*<*)
  using assms
  unfolding contextually_equivalent_def
  by (simp add: computational_adequacy_refines)
(*>*)

text{*

This gives us a sound but incomplete method for demonstrating
contextual equivalence. We expect this result is useful for showing
contextual equivalence for \emph{typed} programs as well, but leave it
to future work to demonstrate this.

See \citet[\S6.2]{Gunter:1992} for further discussion of computational
adequacy at higher types.

The reader may wonder why we did not use Nominal syntax to define our
operational semantics, following
\citet{DBLP:journals/entcs/UrbanN09}. The reason is that Nominal2 does
not support the definition of continuous functions over Nominal
syntax, which is required by the evaluators of \S\ref{sec:directsem}
and \S\ref{sec:directsem_db}. As observed above, in the setting of
traditional programming language semantics one can get by with a much
simpler notion of substitution than is needed for investigations into
@{text "\<lambda>"}-calculi. Clearly this does not hold of languages that
reduce ``under binders''.

The ``fast and loose reasoning is morally correct'' work of
\citet{DBLP:conf/popl/DanielssonHJG06} can be seen as a kind of
adequacy result.

\citet{DBLP:conf/tphol/BentonKV09} demonstrate a similar computational
adequacy result in Coq. However their system is only geared up for
this kind of metatheory, and not reasoning about particular programs;
its term language is combinatory.

\citet{DBLP:conf/ppdp/BentonKBH07,DBLP:conf/ppdp/BentonKBH09} have
shown that it is difficult to scale this domain-theoretic approach up
to richer languages, such as those with dynamic allocation of mutable
references, especially if these references can contain (arbitrary)
functional values.

*}

(*<*)

end
(*>*)
