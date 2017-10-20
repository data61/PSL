(*  Title:      PCF.thy
    Author:     Peter Gammie
*)

section {* Logical relations for definability in PCF *}
(*<*)

theory PCF
imports
  Basis
  Logical_Relations
begin

(*>*)
text{*

\label{sec:directsem}

Using this machinery we can demonstrate some classical results about
PCF \citep{Plotkin77}. We diverge from the traditional treatment by
considering PCF as an untyped language and including both call-by-name
(CBN) and call-by-value (CBV) abstractions following
\citet{DBLP:conf/icalp/Reynolds74}. We also adopt some of the
presentation of \citet[Chapter~11]{Winskel:1993}, in particular by
making the fixed point operator a binding construct.

We model the syntax of PCF as a HOL datatype, where variables have
names drawn from the naturals:

*}

type_synonym var = nat

datatype expr =
    Var var
  | App expr expr
  | AbsN var expr (* non-strict fns *)
  | AbsV var expr (* strict fns *)
  | Diverge ("\<Omega>")
  | Fix var expr
  | tt
  | ff
  | Cond expr expr expr
  | Num nat
  | Succ expr
  | Pred expr
  | IsZero expr

subsection{* Direct denotational semantics *}

text{*

\label{sec:densem}

We give this language a direct denotational semantics by interpreting
it into a domain of values.

*}

domain ValD =
   ValF (lazy appF :: "ValD \<rightarrow> ValD")
 | ValTT | ValFF
 | ValN (lazy "nat")

text{*

The \textbf{lazy} keyword means that the @{term "ValF"} constructor is
lifted, i.e. @{term "ValF\<cdot>\<bottom> \<noteq> \<bottom>"}, which further means that @{term
"ValF\<cdot>(\<Lambda> x. \<bottom>) \<noteq> \<bottom>"}.

The naturals are discretely ordered.

*}
(*<*)

lemma ValD_case_ID [simp]:
  "ValD_case\<cdot>ValF\<cdot>ValTT\<cdot>ValFF\<cdot>ValN = ID"
  apply (rule cfun_eqI)
  apply (case_tac x)
  apply simp_all
  done

lemma below_monic_ValF [iff]:
  "below_monic_cfun ValF"
  by (rule below_monicI) simp

lemma below_monic_ValN [iff]:
  "below_monic_cfun ValN"
  by (rule below_monicI) simp

(*>*)
text{*

The minimal invariant for @{typ "ValD"} is straightforward; the
function @{term "cfun_map\<cdot>f\<cdot>g\<cdot>h"} denotes @{term "g oo h oo f"}.

*}

fixrec
  ValD_copy_rec :: "(ValD \<rightarrow> ValD) \<rightarrow> (ValD \<rightarrow> ValD)"
where
  "ValD_copy_rec\<cdot>r\<cdot>(ValF\<cdot>f) = ValF\<cdot>(cfun_map\<cdot>r\<cdot>r\<cdot>f)"
| "ValD_copy_rec\<cdot>r\<cdot>(ValTT) = ValTT"
| "ValD_copy_rec\<cdot>r\<cdot>(ValFF) = ValFF"
| "ValD_copy_rec\<cdot>r\<cdot>(ValN\<cdot>n) = ValN\<cdot>n"
(*<*)

lemma ValD_copy_rec_strict [simp]:
  "ValD_copy_rec\<cdot>r\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

abbreviation
  "ValD_copy \<equiv> fix\<cdot>ValD_copy_rec"

lemma ValD_copy_strict [simp]:
  "ValD_copy\<cdot>\<bottom> = \<bottom>"
  by (subst fix_eq) simp

lemma ValD_copy_ID [simp]:
  "ValD_copy = ID"
proof -
  { fix x :: ValD
    fix i :: nat
    have "ValD_take i\<cdot>(ValD_copy\<cdot>(ValD_take i\<cdot>x)) = ValD_take i\<cdot>x"
    proof (induct i arbitrary: x)
      case (Suc n) thus ?case
        by (cases x) (subst fix_eq, simp add: cfun_map_def)+
    qed simp }
  hence "\<And>x :: ValD. (\<Squnion>i. ValD_take i\<cdot>(ValD_copy\<cdot>(ValD_take i\<cdot>x))) = (\<Squnion>i. ValD_take i\<cdot>x)"
    by (blast intro: lub_eq)
  thus ?thesis by (simp add: lub_distribs ValD.lub_take cfun_eq_iff)
qed

(*>*)
text{*

We interpret the PCF constants in the obvious ways. ``Ill-typed'' uses
of these combinators are mapped to @{term "\<bottom>"}.

*}

definition cond :: "ValD \<rightarrow> ValD \<rightarrow> ValD \<rightarrow> ValD" where
  "cond \<equiv> \<Lambda> i t e. case i of ValF\<cdot>f \<Rightarrow> \<bottom> | ValTT \<Rightarrow> t | ValFF \<Rightarrow> e | ValN\<cdot>n \<Rightarrow> \<bottom>"

definition succ :: "ValD \<rightarrow> ValD" where
  "succ \<equiv> \<Lambda> (ValN\<cdot>n). ValN\<cdot>(n + 1)"

definition pred :: "ValD \<rightarrow> ValD" where
  "pred \<equiv> \<Lambda> (ValN\<cdot>n). case n of 0 \<Rightarrow> \<bottom> | Suc n \<Rightarrow> ValN\<cdot>n"

definition isZero :: "ValD \<rightarrow> ValD" where
  "isZero \<equiv> \<Lambda> (ValN\<cdot>n). if n = 0 then ValTT else ValFF"

text{*

We model environments simply as continuous functions from variable
names to values.

*}

type_synonym Var = "var"
type_synonym 'a Env = "Var \<rightarrow> 'a"

definition env_empty :: "'a Env" where
  "env_empty \<equiv> \<bottom>"

definition env_ext :: "Var \<rightarrow> 'a \<rightarrow> 'a Env \<rightarrow> 'a Env" where
  "env_ext \<equiv> \<Lambda> v x \<rho> v'. if v = v' then x else \<rho>\<cdot>v'"
(*<*)

lemma env_ext_same: "env_ext\<cdot>v\<cdot>x\<cdot>\<rho>\<cdot>v = x"
  by (simp add: env_ext_def)

lemma env_ext_neq: "v \<noteq> v' \<Longrightarrow> env_ext\<cdot>v\<cdot>x\<cdot>\<rho>\<cdot>v' = \<rho>\<cdot>v'"
  by (simp add: env_ext_def)

lemmas env_ext_simps[simp] = env_ext_same env_ext_neq

(*>*)
text{*

The semantics is given by a function defined by primitive recursion
over the syntax.

*}

type_synonym EnvD = "ValD Env"

primrec
  evalD :: "expr \<Rightarrow> EnvD \<rightarrow> ValD"
where
  "evalD (Var v) = (\<Lambda> \<rho>. \<rho>\<cdot>v)"
| "evalD (App f x) = (\<Lambda> \<rho>. appF\<cdot>(evalD f\<cdot>\<rho>)\<cdot>(evalD x\<cdot>\<rho>))"
| "evalD (AbsN v e) = (\<Lambda> \<rho>. ValF\<cdot>(\<Lambda> x. evalD e\<cdot>(env_ext\<cdot>v\<cdot>x\<cdot>\<rho>)))"
| "evalD (AbsV v e) = (\<Lambda> \<rho>. ValF\<cdot>(strictify\<cdot>(\<Lambda> x. evalD e\<cdot>(env_ext\<cdot>v\<cdot>x\<cdot>\<rho>))))"
| "evalD (Diverge) = (\<Lambda> \<rho>. \<bottom>)"
| "evalD (Fix v e) = (\<Lambda> \<rho>. \<mu> x. evalD e\<cdot>(env_ext\<cdot>v\<cdot>x\<cdot>\<rho>))"
| "evalD (tt) = (\<Lambda> \<rho>. ValTT)"
| "evalD (ff) = (\<Lambda> \<rho>. ValFF)"
| "evalD (Cond i t e) = (\<Lambda> \<rho>. cond\<cdot>(evalD i\<cdot>\<rho>)\<cdot>(evalD t\<cdot>\<rho>)\<cdot>(evalD e\<cdot>\<rho>))"
| "evalD (Num n) = (\<Lambda> \<rho>. ValN\<cdot>n)"
| "evalD (Succ e) = (\<Lambda> \<rho>. succ\<cdot>(evalD e\<cdot>\<rho>))"
| "evalD (Pred e) = (\<Lambda> \<rho>. pred\<cdot>(evalD e\<cdot>\<rho>))"
| "evalD (IsZero e) = (\<Lambda> \<rho>. isZero\<cdot>(evalD e\<cdot>\<rho>))"

abbreviation eval' :: "expr \<Rightarrow> ValD Env \<Rightarrow> ValD" ("\<lbrakk>_\<rbrakk>_" [0,1000] 60) where
  "eval' M \<rho> \<equiv> evalD M\<cdot>\<rho>"


subsection{* The Y Combinator *}

text{*

We can shown the Y combinator is the least fixed point operator Using
just the minimal invariant.  In other words, @{term "fix"} is
definable in untyped PCF minus the @{term "Fix"} construct.

This is Example~3.6 from \citet{PittsAM:relpod}. He attributes the
proof to Plotkin.

These two functions are @{text "\<Delta> \<equiv> \<lambda>f x. f (x x)"} and @{text "Y \<equiv>
\<lambda>f. (\<Delta> f) (\<Delta> f)"}.

Note the numbers here are names, not de Bruijn indices.

*}

definition Y_delta :: expr where
  "Y_delta \<equiv> AbsN 0 (AbsN 1 (App (Var 0) (App (Var 1) (Var 1))))"

definition Ycomb :: expr where
  "Ycomb \<equiv> AbsN 0 (App (App Y_delta (Var 0)) (App Y_delta (Var 0)))"

definition fixD :: "ValD \<rightarrow> ValD" where
  "fixD \<equiv> \<Lambda> (ValF\<cdot>f). fix\<cdot>f"

lemma Y: "\<lbrakk>Ycomb\<rbrakk>\<rho> = ValF\<cdot>fixD"
(*<*)
proof(rule below_antisym)
  show "ValF\<cdot>fixD \<sqsubseteq> \<lbrakk>Ycomb\<rbrakk>\<rho>"
    unfolding fixD_def Ycomb_def
    apply (clarsimp simp: cfun_below_iff eta_cfun)
    apply (case_tac x)
     apply simp_all
    apply (rule fix_least)
    by (subst Y_delta_def, simp)
next
  { fix f \<rho>
    let ?P = "\<lambda>x. x \<sqsubseteq> ID \<and> appF\<cdot>(x\<cdot>(appF\<cdot>(\<lbrakk>Y_delta\<rbrakk>\<rho>)\<cdot>(ValF\<cdot>f)))\<cdot>(appF\<cdot>(\<lbrakk>Y_delta\<rbrakk>\<rho>)\<cdot>(ValF\<cdot>f)) \<sqsubseteq> fixD\<cdot>(ValF\<cdot>f)"
    have "?P ValD_copy"
      apply (rule fix_ind)
        apply simp
       apply simp
      apply clarsimp
      apply (rule conjI)
       apply (rule cfun_belowI)
       apply (case_tac xa)
        apply simp_all
       apply (drule cfun_map_below_ID)
       apply (simp add: cfun_below_iff)
      apply (simp add: fixD_def eta_cfun)
      apply (subst Y_delta_def)
      apply (subst fix_eq)
      apply simp
      apply (rule cfun_below_ID, assumption)
      apply (rule monofun_cfun_arg)
      apply (subgoal_tac "appF\<cdot>(x\<cdot>(appF\<cdot>(\<lbrakk>Y_delta\<rbrakk>\<rho>)\<cdot>(ValF\<cdot>f)))\<cdot>(x\<cdot>(appF\<cdot>(\<lbrakk>Y_delta\<rbrakk>\<rho>)\<cdot>(ValF\<cdot>f)))
                        \<sqsubseteq> appF\<cdot>(x\<cdot>(appF\<cdot>(\<lbrakk>Y_delta\<rbrakk>\<rho>)\<cdot>(ValF\<cdot>f)))\<cdot>(appF\<cdot>(\<lbrakk>Y_delta\<rbrakk>\<rho>)\<cdot>(ValF\<cdot>f))")
       apply (erule (1) below_trans)
      apply (simp add: monofun_cfun_arg cfun_below_iff)
      done }
  thus "\<lbrakk>Ycomb\<rbrakk>\<rho> \<sqsubseteq> ValF\<cdot>fixD"
    unfolding Ycomb_def fixD_def
    apply (clarsimp simp: cfun_below_iff)
    apply (case_tac x)
    apply (subst Y_delta_def, simp)
    apply simp
    apply (subst Y_delta_def, simp)+
    done
qed

(* FIXME could also try to show uniformity, cf Gunter, Plotkin "3 Inadequate Models". *)

(*>*)

subsection{* Logical relations for definability *}

text{*

\label{sec:pcfdefinability}

An element of @{typ "ValD"} is definable if there is an expression
that denotes it.

*}

definition definable :: "ValD \<Rightarrow> bool" where
  "definable d \<equiv> \<exists>M. \<lbrakk>M\<rbrakk>env_empty = d"

text{*

A classical result about PCF is that while the denotational semantics
is \emph{adequate}, as we show in \S\ref{sec:opsem}, it is not
\emph{fully abstract}, i.e. it contains undefinable values (junk).

One way of showing this is to reason operationally; see, for instance,
\citet[\S4]{Plotkin77} and \citet[\S6.1]{Gunter:1992}.

Another is to use \emph{logical relations}, following
\citet{Plotkin:1973}, and also
\citet{Mitchell:1996,Sieber:1992,DBLP:conf/mfps/Stoughton93}.

For this purpose we define a logical relation to be a set of vectors
over @{typ "ValD"} that is closed under continuous functions of type
@{typ "ValD \<rightarrow> ValD"}. This is complicated by the @{term "ValF"} tag
and having strict function abstraction.

*}

definition
  logical_relation :: "('i::type \<Rightarrow> ValD) set \<Rightarrow> bool"
where
  "logical_relation R \<equiv>
     (\<forall>fs \<in> R. \<forall>xs \<in> R. (\<lambda>j. appF\<cdot>(fs j)\<cdot>(xs j)) \<in> R)
   \<and> (\<forall>fs \<in> R. \<forall>xs \<in> R. (\<lambda>j. strictify\<cdot>(appF\<cdot>(fs j))\<cdot>(xs j)) \<in> R)
   \<and> (\<forall>fs. (\<forall>xs \<in> R. (\<lambda>j. (fs j)\<cdot>(xs j)) \<in> R) \<longrightarrow> (\<lambda>j. ValF\<cdot>(fs j)) \<in> R)
   \<and> (\<forall>fs. (\<forall>xs \<in> R. (\<lambda>j. strictify\<cdot>(fs j)\<cdot>(xs j)) \<in> R) \<longrightarrow> (\<lambda>j. ValF\<cdot>(strictify\<cdot>(fs j))) \<in> R)
   \<and> (\<forall>xs \<in> R. (\<lambda>j. fixD\<cdot>(xs j)) \<in> R)
   \<and> (\<forall>cs \<in> R. \<forall>ts \<in> R. \<forall>es \<in> R. (\<lambda>j. cond\<cdot>(cs j)\<cdot>(ts j)\<cdot>(es j)) \<in> R)
   \<and> (\<forall>xs \<in> R. (\<lambda>j. succ\<cdot>(xs j)) \<in> R)
   \<and> (\<forall>xs \<in> R. (\<lambda>j. pred\<cdot>(xs j)) \<in> R)
   \<and> (\<forall>xs \<in> R. (\<lambda>j. isZero\<cdot>(xs j)) \<in> R)"
(*<*)

lemma logical_relationI:
  "\<lbrakk> \<And>fs xs. \<lbrakk> fs \<in> R; xs \<in> R \<rbrakk> \<Longrightarrow> (\<lambda>j. appF\<cdot>(fs j)\<cdot>(xs j)) \<in> R;
     \<And>fs xs. \<lbrakk> fs \<in> R; xs \<in> R \<rbrakk> \<Longrightarrow> (\<lambda>j. strictify\<cdot>(appF\<cdot>(fs j))\<cdot>(xs j)) \<in> R;
     \<And>fs. (\<And>xs. xs \<in> R \<Longrightarrow> (\<lambda>j. (fs j)\<cdot>(xs j)) \<in> R) \<Longrightarrow> (\<lambda>j. ValF\<cdot>(fs j)) \<in> R;
     \<And>fs. (\<And>xs. xs \<in> R \<Longrightarrow> (\<lambda>j. strictify\<cdot>(fs j)\<cdot>(xs j)) \<in> R) \<Longrightarrow> (\<lambda>j. ValF\<cdot>(strictify\<cdot>(fs j))) \<in> R;
     \<And>xs. xs \<in> R \<Longrightarrow> (\<lambda>j. fixD\<cdot>(xs j)) \<in> R;
     \<And>cs ts es. \<lbrakk> cs \<in> R; ts \<in> R; es \<in> R \<rbrakk> \<Longrightarrow> (\<lambda>j. cond\<cdot>(cs j)\<cdot>(ts j)\<cdot>(es j)) \<in> R;
     \<And>xs. xs \<in> R \<Longrightarrow> (\<lambda>j. succ\<cdot>(xs j)) \<in> R;
     \<And>xs. xs \<in> R \<Longrightarrow> (\<lambda>j. pred\<cdot>(xs j)) \<in> R;
     \<And>xs. xs \<in> R \<Longrightarrow> (\<lambda>j. isZero\<cdot>(xs j)) \<in> R \<rbrakk> \<Longrightarrow> logical_relation R"
  unfolding logical_relation_def by (simp add: cfcomp1)

lemma lr_l2r:
  "\<lbrakk> fs \<in> R; xs \<in> R; logical_relation R \<rbrakk> \<Longrightarrow> (\<lambda>j. appF\<cdot>(fs j)\<cdot>(xs j)) \<in> R"
  "\<lbrakk> fs \<in> R; xs \<in> R; logical_relation R \<rbrakk> \<Longrightarrow> (\<lambda>j. strictify\<cdot>(appF\<cdot>(fs j))\<cdot>(xs j)) \<in> R"
  "\<lbrakk> xs \<in> R; logical_relation R \<rbrakk> \<Longrightarrow> (\<lambda>j. fixD\<cdot>(xs j)) \<in> R"
  "\<lbrakk> cs \<in> R; ts \<in> R; es \<in> R; logical_relation R \<rbrakk> \<Longrightarrow> (\<lambda>j. cond\<cdot>(cs j)\<cdot>(ts j)\<cdot>(es j)) \<in> R"
  "\<lbrakk> xs \<in> R; logical_relation R \<rbrakk> \<Longrightarrow> (\<lambda>j. succ\<cdot>(xs j)) \<in> R"
  "\<lbrakk> xs \<in> R; logical_relation R \<rbrakk> \<Longrightarrow> (\<lambda>j. pred\<cdot>(xs j)) \<in> R"
  "\<lbrakk> xs \<in> R; logical_relation R \<rbrakk> \<Longrightarrow> (\<lambda>j. isZero\<cdot>(xs j)) \<in> R"
  unfolding logical_relation_def by blast+

lemma lr_r2l:
  "\<lbrakk> logical_relation R; \<forall>xs \<in> R. (\<lambda>j. (fs j)\<cdot>(xs j)) \<in> R \<rbrakk> \<Longrightarrow> (\<lambda>i. ValF\<cdot>(fs i)) \<in> R"
  unfolding logical_relation_def by (simp add: cfcomp1)

lemma lr_r2l_strict:
  "\<lbrakk> logical_relation R; \<forall>xs \<in> R. (\<lambda>j. strictify\<cdot>(fs j)\<cdot>(xs j)) \<in> R \<rbrakk> \<Longrightarrow> (\<lambda>i. ValF\<cdot>(strictify\<cdot>(fs i))) \<in> R"
  unfolding logical_relation_def by (simp add: cfcomp1)

(*>*)
text{*

In the context of PCF these relations also need to respect the
constants.

*}

definition
  PCF_consts_rel :: "('i::type \<Rightarrow> ValD) set \<Rightarrow> bool"
where
  "PCF_consts_rel R \<equiv>
       \<bottom> \<in> R
     \<and> (\<lambda>i. ValTT) \<in> R
     \<and> (\<lambda>i. ValFF) \<in> R
     \<and> (\<forall>n. (\<lambda>i. ValN\<cdot>n) \<in> R)"
(*<*)

lemma PCF_consts_rel_simps [simp, elim]:
  "PCF_consts_rel R \<Longrightarrow> \<bottom> \<in> R"
  "PCF_consts_rel R \<Longrightarrow> (\<lambda>i. ValTT) \<in> R"
  "PCF_consts_rel R \<Longrightarrow> (\<lambda>i. ValFF) \<in> R"
  "PCF_consts_rel R \<Longrightarrow> (\<lambda>i. ValN\<cdot>n) \<in> R"
unfolding PCF_consts_rel_def by simp_all

lemma PCF_consts_relI:
  "\<lbrakk> \<bottom> \<in> R;
     (\<lambda>i. ValTT) \<in> R;
     (\<lambda>i. ValFF) \<in> R;
     \<And>n. (\<lambda>i. ValN\<cdot>n) \<in> R \<rbrakk> \<Longrightarrow> PCF_consts_rel R"
unfolding PCF_consts_rel_def by blast

(*>*)
text{**}

abbreviation
  "PCF_lr R \<equiv> adm (\<lambda>x. x \<in> R) \<and> logical_relation R \<and> PCF_consts_rel R"

text{*

The fundamental property of logical relations states that all PCF
expressions satisfy all PCF logical relations. This result is
essentially due to \citet{Plotkin:1973}.  The proof is by a
straightforward induction on the expression @{term "M"}.

*}

lemma lr_fundamental:
  assumes lr: "PCF_lr R"
  assumes \<rho>: "\<forall>v. (\<lambda>i. \<rho> i\<cdot>v) \<in> R"
  shows "(\<lambda>i. \<lbrakk>M\<rbrakk>(\<rho> i)) \<in> R"
(*<*)
using \<rho>
proof(induct M arbitrary: \<rho>)
  case (Var v \<rho>) thus ?case by simp
next
  case (App e1 e2 \<rho>)
  with lr lr_l2r(1)[where fs="\<lambda>j. \<lbrakk>e1\<rbrakk>(\<rho> j)" and xs="\<lambda>j. \<lbrakk>e2\<rbrakk>(\<rho> j)"]
  show ?case by simp
next
  case (AbsN v e)
  with lr show ?case
    apply clarsimp
    apply (erule lr_r2l[where fs="\<lambda>i. \<Lambda> x. \<lbrakk>e\<rbrakk>(env_ext\<cdot>v\<cdot>x\<cdot>(\<rho> i))" and R=R, simplified])
    apply clarsimp
    apply (cut_tac \<rho>="\<lambda>j. env_ext\<cdot>v\<cdot>(xs j)\<cdot>(\<rho> j)" in AbsN.hyps)
     apply (simp add: env_ext_def)
     using AbsN(2)
     apply clarsimp
     apply (case_tac "v=va")
      apply (simp add: eta_cfun)
     apply simp
    apply simp
    done
next
  case (AbsV v e)
  with lr show ?case
    apply clarsimp
    apply (rule lr_r2l_strict[where fs="\<lambda>i. \<Lambda> x. \<lbrakk>e\<rbrakk>(env_ext\<cdot>v\<cdot>x\<cdot>(\<rho> i))", simplified])
     apply simp
    apply clarsimp
    apply (cut_tac fs="\<lambda>i. ValF\<cdot>(\<Lambda> x. \<lbrakk>e\<rbrakk>(env_ext\<cdot>v\<cdot>x\<cdot>(\<rho> i)))" and xs=xs and R=R in lr_l2r(2))
     apply simp_all
    apply (erule lr_r2l[where fs="\<lambda>i. \<Lambda> x. \<lbrakk>e\<rbrakk>(env_ext\<cdot>v\<cdot>x\<cdot>(\<rho> i))" and R=R, simplified])
    apply clarsimp
    apply (cut_tac \<rho>="\<lambda>j. env_ext\<cdot>v\<cdot>(xsa j)\<cdot>(\<rho> j)" in AbsV.hyps)
     apply (simp add: env_ext_def)
     using AbsV(2)
     apply clarsimp
     apply (case_tac "v=va")
      apply (simp add: eta_cfun)
     apply simp
    apply simp
    done
next
  case (Fix v e \<rho>) show ?case
    apply simp
    apply (subst fix_argument_promote_fun)
    apply (rule fix_ind[where F="\<Lambda> f. (\<lambda>x. (\<Lambda> xa. \<lbrakk>e\<rbrakk>(env_ext\<cdot>v\<cdot>xa\<cdot>(\<rho> x)))\<cdot>(f x))"])
      apply (simp add: lr)
     apply (simp add: lr inst_fun_pcpo[symmetric])
    apply simp
    apply (cut_tac \<rho>="\<lambda>i. env_ext\<cdot>v\<cdot>(x i)\<cdot>(\<rho> i)" in Fix.hyps)
     unfolding env_ext_def
     using Fix(2)
     apply clarsimp
     apply (case_tac "v=va")
      apply (simp add: eta_cfun)
     apply simp
    apply (simp add: cont_fun)
    done
next
  case (Cond i t e \<rho>)
  with lr lr_l2r(4)[where cs="\<lambda>j. \<lbrakk>i\<rbrakk>(\<rho> j)" and ts="\<lambda>j. \<lbrakk>t\<rbrakk>(\<rho> j)" and es="\<lambda>j. \<lbrakk>e\<rbrakk>(\<rho> j)"]
  show ?case by simp
next
  case (Succ e \<rho>)
  with lr lr_l2r(5)[where xs="\<lambda>j. \<lbrakk>e\<rbrakk>(\<rho> j)"]
  show ?case by simp
next
  case (Pred e \<rho>)
  with lr lr_l2r(6)[where xs="\<lambda>j. \<lbrakk>e\<rbrakk>(\<rho> j)"]
  show ?case by simp
next
  case (IsZero e \<rho>)
  with lr lr_l2r(7)[where xs="\<lambda>j. \<lbrakk>e\<rbrakk>(\<rho> j)"]
  show ?case by simp

(* FIXME weirdness *)
next
  case Diverge with lr show ?case
    apply simp
    apply (simp add: inst_fun_pcpo[symmetric])
    done
qed (insert lr, simp_all)
(*>*)

text{*

We can use this result to show that there is no PCF term that maps the
vector @{term "args \<in> R"} to @{term "result \<notin> R"} for some logical
relation @{term "R"}. If we further show that there is a function
@{term "f"} in @{term "ValD"} such that @{term "f args = result"} then
we can conclude that @{term "f"} is not definable.

*}

abbreviation
  appFLv :: "ValD \<Rightarrow> ('i::type \<Rightarrow> ValD) list \<Rightarrow> ('i \<Rightarrow> ValD)"
where
  "appFLv f args \<equiv> (\<lambda>i. foldl (\<lambda>f x. appF\<cdot>f\<cdot>(x i)) f args)"

lemma lr_appFLv:
  assumes lr: "logical_relation R"
  assumes f: "(\<lambda>i::'i::type. f) \<in> R"
  assumes args: "set args \<subseteq> R"
  shows "appFLv f args \<in> R"
(*<*)
using args
proof(induct args rule: rev_induct)
  case Nil with f show ?case by simp
next
  case (snoc x xs) thus ?case
    apply simp
    using lr_l2r(1)[OF _ _ lr, where fs="\<lambda>i. (foldl (\<lambda>f x. appF\<cdot>f\<cdot>(x i)) f xs)" and xs=x]
    apply simp
    done
qed

(*>*)
text{**}

corollary not_definable:
  fixes R :: "('i::type \<Rightarrow> ValD) set"
  fixes args :: "('i \<Rightarrow> ValD) list"
  fixes result :: "'i \<Rightarrow> ValD"
  assumes lr: "PCF_lr R"
  assumes args: "set args \<subseteq> R"
  assumes result: "result \<notin> R"
  shows "\<not>(\<exists>(f::ValD). definable f \<and> appFLv f args = result)"
(*<*)
proof
  assume "\<exists>f. definable f \<and> appFLv f args = result"
  then obtain f
    where df: "definable f"
      and f: "appFLv f args = result" by blast
  from df obtain M
    where Mf: "\<lbrakk>M\<rbrakk>env_empty = f"
    unfolding definable_def by blast
  with lr lr_fundamental[OF lr, where M=M and \<rho>="\<lambda>i. env_empty"]
       f args lr_appFLv[where f=f and R=R and args=args]
  have "result \<in> R" unfolding env_empty_def by (simp add: inst_fun_pcpo[symmetric])
  with result show False ..
qed
(*>*)

subsection{* Parallel OR is not definable *}

text {*

\label{sec:por}

We show that parallel-or is not @{text "\<lambda>"}-definable following
\citet{Sieber:1992} and \citet{DBLP:conf/mfps/Stoughton93}.

Parallel-or is similar to lazy-or except that if the first argument is
@{term "\<bottom>"} and the second one is @{term "ValTT"}, we get @{term
"ValTT"} (and not @{term "\<bottom>"}). It is continuous and hence included in
the @{typ "ValD"} domain.

*}

definition por :: "ValD \<Rightarrow> ValD \<Rightarrow> ValD" ("_ por _" [31,30] 30) where
  "x por y \<equiv>
     if x = ValTT then ValTT
       else if y = ValTT then ValTT
              else if (x = ValFF \<and> y = ValFF) then ValFF else \<bottom>"

text{* The defining properties of parallel-or. *}

lemma POR_simps [simp]:
  "(ValTT por y) = ValTT"
  "(x por ValTT) = ValTT"
  "(ValFF por ValFF) = ValFF"
  "(ValFF por \<bottom>) = \<bottom>"
  "(ValFF por ValN\<cdot>n) = \<bottom>"
  "(ValFF por ValF\<cdot>f) = \<bottom>"
  "(\<bottom> por ValFF) = \<bottom>"
  "(ValN\<cdot>n por ValFF) = \<bottom>"
  "(ValF\<cdot>f por ValFF) = \<bottom>"
  "(\<bottom> por \<bottom>) = \<bottom>"
  "(\<bottom> por ValN\<cdot>n) = \<bottom>"
  "(\<bottom> por ValF\<cdot>f) = \<bottom>"
  "(ValN\<cdot>n por \<bottom>) = \<bottom>"
  "(ValF\<cdot>f por \<bottom>) = \<bottom>"
  "(ValN\<cdot>m por ValN\<cdot>n) = \<bottom>"
  "(ValN\<cdot>n por ValF\<cdot>f) = \<bottom>"
  "(ValF\<cdot>f por ValN\<cdot>n) = \<bottom>"
  "(ValF\<cdot>f por ValF\<cdot>g) = \<bottom>"
  unfolding por_def by simp_all
(*<*)

text{*

We show that parallel-or is a continuous function.

*}

lemma POR_sym: "(x por y) = (y por x)"
  unfolding por_def by simp

lemma ValTT_below_iff [simp]: "ValTT \<sqsubseteq> x \<longleftrightarrow> x = ValTT"
  by (cases x) simp_all

lemma ValFF_below_iff [simp]: "ValFF \<sqsubseteq> x \<longleftrightarrow> x = ValFF"
  by (cases x) simp_all

lemma monofun_por: "monofun (\<lambda>x. x por y)"
  unfolding por_def
  by (rule monofunI) auto

lemma mic2mic: "max_in_chain i Y \<Longrightarrow> max_in_chain i (\<lambda>i. f (Y i))"
  unfolding max_in_chain_def by simp

lemma cont_por1: "cont (\<lambda>x. x por y)"
  apply (rule contI2[OF monofun_por])
  apply (case_tac "Lub Y")
   apply simp_all
   apply (cases y)
   apply simp_all
   apply (cases y)
   apply simp_all

   apply (frule compact_imp_max_in_chain)
    apply simp
   apply clarsimp
   apply (frule mic2mic[where f="\<lambda>x. x por y"])
   apply (subst iffD1[OF maxinch_is_thelub])
   apply simp_all
   apply (simp_all add: maxinch_is_thelub)

   apply (frule compact_imp_max_in_chain)
    apply simp
   apply clarsimp
   apply (frule mic2mic[where f="\<lambda>x. x por y"])
   apply (subst iffD1[OF maxinch_is_thelub])
   apply simp_all
   apply (simp_all add: maxinch_is_thelub)

   apply (cases y)
   apply simp_all
   done

lemma cont_por[cont2cont, simp]:
  assumes f: "cont (\<lambda>x. f x)" and g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. f x por g x)"
proof -
  have A: "\<And>f y. cont f \<Longrightarrow> cont (\<lambda>x. f x por y)"
    by (rule cont_apply) (simp_all add: cont_por1)
  from A[OF f] A[OF g] show ?thesis
    apply -
    apply (subst (asm) POR_sym) back
    apply (rule cont_apply[OF f])
    apply (simp_all add: cont_por1)
    done
qed

(*>*)
text{*

We need three-element vectors.

*}

datatype Three = One | Two | Three

text{*

The standard logical relation @{term "R"} that demonstrates POR is not
definable is:
\[
  (x, y, z) \in R\ \mbox{iff}\ x = y = z \lor (x = \bot \lor y = \bot)
\]
That POR satisfies this relation can be seen from its truth table (see
below).

Note we restrict the @{text "x = y = z"} clause to non-function
values. Adding functions breaks the ``logical relations'' property.

*}

definition
  POR_base_lf_rep :: "(Three \<Rightarrow> ValD) lf_rep"
where
  "POR_base_lf_rep \<equiv> \<lambda>(mR, pR).
     { (\<lambda>i. ValTT) } \<union> { (\<lambda>i. ValFF) } (* x = y = z for bools *)
   \<union> (\<Union>n. { (\<lambda>i. ValN\<cdot>n) }) (* x = y = z for numerals *)
   \<union> { f . f One = \<bottom> } (* x = \<bottom> *)
   \<union> { f . f Two = \<bottom> } (* y = \<bottom> *)"

text{*

We close this relation with respect to continuous functions. This
functor yields an admissible relation for all @{term "r"} and is
monotonic.

*}

definition
  fn_lf_rep :: "('i::type \<Rightarrow> ValD) lf_rep"
where
  "fn_lf_rep \<equiv> \<lambda>(mR, pR). { \<lambda>i. ValF\<cdot>(fs i) |fs. \<forall>xs \<in> unlr (undual mR). (\<lambda>j. (fs j)\<cdot>(xs j)) \<in> unlr pR }"
(*<*)

lemma adm_POR_base_lf_rep:
  "adm (\<lambda>x. x \<in> POR_base_lf_rep r)"
unfolding POR_base_lf_rep_def
using adm_below_monic_exists[OF _ below_monic_fun_K[where f="ValN"], where P="\<lambda>_. True", simplified]
by (auto intro!: adm_disj simp: cont_fun)

lemma mono_POR_base_lf_rep:
  "mono POR_base_lf_rep"
unfolding POR_base_lf_rep_def by (blast intro!: monoI)

lemma adm_fn:
  "adm (\<lambda>x. x \<in> fn_lf_rep r)"
unfolding fn_lf_rep_def
using adm_below_monic_exists[OF _ below_monic_fun_K[where f="ValF"], where P="\<lambda>_. True", simplified]
apply (clarsimp simp: split_def)
apply (rule adm_below_monic_exists)
apply (auto simp: cont_fun)

(* FIXME lemma *)
apply (rule below_monicI)
apply (rule fun_belowI)
apply (subst (asm) fun_below_iff)
apply auto
done

(*
  by (fastforce simp: split_def intro: adm_below_monic_exists)
*)

lemma mono_fn_lf_rep:
  "mono fn_lf_rep"
  by (rule monoI) (fastforce simp: fn_lf_rep_def unlr_leq[symmetric] undual_leq[symmetric])

(*>*)
text{**}

definition POR_lf_rep :: "(Three \<Rightarrow> ValD) lf_rep" where
  "POR_lf_rep R \<equiv> POR_base_lf_rep R \<union> fn_lf_rep R"

abbreviation "POR_lf \<equiv> \<lambda>r. mklr (POR_lf_rep r)"
(*<*)

lemma admS_POR_lf [intro, simp]:
  "POR_lf_rep r \<in> admS"
proof
  show "\<bottom> \<in> POR_lf_rep r"
    unfolding POR_lf_rep_def POR_base_lf_rep_def
    by simp
next
  show "adm (\<lambda>x. x \<in> POR_lf_rep r)"
    unfolding POR_lf_rep_def
    using adm_POR_base_lf_rep[of r] adm_fn[of r] by simp
qed

lemma mono_POR_lf:
  "mono POR_lf"
  apply (rule monoI)
  apply simp
  unfolding POR_lf_rep_def
  using mono_fn_lf_rep mono_POR_base_lf_rep
  apply (blast dest: monoD)
  done

(*>*)
text{*

Again it yields an admissible relation and is monotonic.

We need to show the functor respects the minimal invariant.

*}

lemma min_inv_POR_lf:
  assumes "eRSV e R' S'"
  shows "eRSV (ValD_copy_rec\<cdot>e) (dual (POR_lf (dual S', undual R'))) (POR_lf (R', S'))"
(*<*)
  apply clarsimp
  apply (simp add: POR_lf_rep_def)
  apply (elim disjE)
   apply (rule disjI1)
   apply (auto simp: POR_base_lf_rep_def eta_cfun cfcomp1 cfun_eq_iff)[1]
  apply (rule disjI2)
  using assms
  apply (clarsimp simp: fn_lf_rep_def eta_cfun)
  apply (simp add: cfcomp1 cfun_map_def)
  apply (rule_tac x="\<lambda>i. \<Lambda> xa. e\<cdot>(fs i\<cdot>(e\<cdot>xa))" in exI)
  apply force
  done

interpretation POR: DomSolV ValD_copy_rec POR_lf
  apply standard
    apply (rule ValD_copy_ID)
   apply (rule mono_POR_lf)
  apply (erule min_inv_POR_lf)
  done

lemma PORI [intro, simp]:
  "(\<lambda>i. ValTT) \<in> unlr POR.delta"
  "(\<lambda>i. ValFF) \<in> unlr POR.delta"
  "(\<lambda>i. ValN\<cdot>n) \<in> unlr POR.delta"
  "f One = \<bottom> \<Longrightarrow> f \<in> unlr POR.delta"
  "f Two = \<bottom> \<Longrightarrow> f \<in> unlr POR.delta"
  "\<lbrakk> \<And>xs. xs \<in> unlr POR.delta \<Longrightarrow> (\<lambda>j. (fs j)\<cdot>(xs j)) \<in> unlr POR.delta \<rbrakk> \<Longrightarrow> (\<lambda>i. ValF\<cdot>(fs i)) \<in> unlr POR.delta"
  by (subst POR.delta_sol, simp, subst POR_lf_rep_def,
      fastforce simp: POR_base_lf_rep_def fn_lf_rep_def eta_cfun cfcomp1)+

lemma POR_fun_constI:
  "\<lbrakk> \<And>xs. xs \<in> unlr POR.delta \<Longrightarrow> (\<lambda>j. f\<cdot>(xs j)) \<in> unlr POR.delta \<rbrakk> \<Longrightarrow> (\<lambda>i. ValF\<cdot>f) \<in> unlr POR.delta"
  using PORI(6)[where fs="\<lambda>_. f"] by simp

lemma PORE:
  "\<lbrakk> a \<in> unlr POR.delta;
     (a = (\<lambda>i. ValTT) \<Longrightarrow> P);
     (a = (\<lambda>i. ValFF) \<Longrightarrow> P);
     (\<And>n. a = (\<lambda>i. ValN\<cdot>n) \<Longrightarrow> P);
     (a One = \<bottom> \<Longrightarrow> P);
     (a Two = \<bottom> \<Longrightarrow> P);
     (\<And>fs. \<lbrakk> a = (\<lambda>i. ValF\<cdot>(fs i)); \<And>xs. xs \<in> unlr POR.delta \<Longrightarrow> (\<lambda>j. (fs j)\<cdot>(xs j)) \<in> unlr POR.delta \<rbrakk> \<Longrightarrow> P)
   \<rbrakk> \<Longrightarrow> P"
  apply (subst (asm) POR.delta_sol)
  apply simp
  apply (subst (asm) POR_lf_rep_def)
  apply (fastforce simp: POR_base_lf_rep_def fn_lf_rep_def eta_cfun)
  done

lemma POR_strict_appI:
  assumes "xs \<in> unlr POR.delta"
  assumes "\<And>xs. xs \<in> unlr POR.delta \<Longrightarrow> (\<lambda>j. fs j\<cdot>(xs j)) \<in> unlr POR.delta"
  shows "(\<lambda>j. strictify\<cdot>(fs j)\<cdot>(xs j)) \<in> unlr POR.delta"
using assms
apply -
apply (erule PORE)
apply simp_all
done

lemma logical_relation_POR:
  "logical_relation (unlr POR.delta)"
  apply (rule logical_relationI)

  (* Strict application *)
  prefer 2
  apply (cut_tac fs="\<lambda>i. appF\<cdot>(fs i)" and xs=xs in POR_strict_appI)
   apply simp_all
  apply (auto elim: PORE)[1]

  (* FIXME fixD *)
  prefer 2
  apply (erule PORE)
  apply (simp_all add: fixD_def)
  apply (subst fix_argument_promote_fun)
  apply (rule_tac F="\<Lambda> f. (\<lambda>x. fs x\<cdot>(f x))" in fix_ind)
  apply (simp_all split: nat.split add: cont_fun)

  apply (auto elim: PORE simp: cond_def isZero_def pred_def succ_def eta_cfun split: nat.split)
  done

lemma PCF_consts_rel_POR:
  "PCF_consts_rel (unlr POR.delta)"
  by (rule PCF_consts_relI) simp_all

(*>*)
text{*

We can show that the solution satisfies the expectations of the
fundamental theorem @{thm [source] "lr_fundamental"}.

*}

lemma PCF_lr_POR_delta: "PCF_lr (unlr POR.delta)"
(*<*)
  using logical_relation_POR PCF_consts_rel_POR by fastforce
(*>*)
text{*

This is the truth-table for POR rendered as a vector: we seek a
function that simultaneously maps the two argument vectors to the
result.

*}

definition POR_arg1_rel where
  "POR_arg1_rel \<equiv> \<lambda>i. case i of One \<Rightarrow> ValTT | Two \<Rightarrow> \<bottom> | Three \<Rightarrow> ValFF"

definition POR_arg2_rel where
  "POR_arg2_rel \<equiv> \<lambda>i. case i of One \<Rightarrow> \<bottom> | Two \<Rightarrow> ValTT | Three \<Rightarrow> ValFF"

definition POR_result_rel where
  "POR_result_rel \<equiv> \<lambda>i. case i of One \<Rightarrow> ValTT | Two \<Rightarrow> ValTT | Three \<Rightarrow> ValFF"

lemma lr_POR_arg1_rel: "POR_arg1_rel \<in> unlr POR.delta"
  unfolding POR_arg1_rel_def by auto

lemma lr_POR_arg2_rel: "POR_arg2_rel \<in> unlr POR.delta"
  unfolding POR_arg2_rel_def by auto

lemma lr_POR_result_rel: "POR_result_rel \<notin> unlr POR.delta"
(*<*)
  unfolding POR_result_rel_def
  apply clarify
  apply (erule PORE)
  apply (auto iff: fun_eq_iff split: Three.splits)
  done

(*>*)
text{*

Parallel-or satisfies these tests:

*}

theorem POR_sat:
  "appFLv (ValF\<cdot>(\<Lambda> x. ValF\<cdot>(\<Lambda> y. x por y))) [POR_arg1_rel, POR_arg2_rel] = POR_result_rel"
  unfolding POR_arg1_rel_def POR_arg2_rel_def POR_result_rel_def
  by (simp add: fun_eq_iff split: Three.splits)

text{*

... but is not PCF-definable:

*}

theorem POR_is_not_definable:
  shows "\<not>(\<exists>f. definable f \<and> appFLv f [POR_arg1_rel, POR_arg2_rel] = POR_result_rel)"
  apply (rule not_definable[where R="unlr POR.delta"])
    using lr_POR_arg1_rel lr_POR_arg2_rel lr_POR_result_rel PCF_lr_POR_delta
    apply simp_all
  done


subsection{* Plotkin's existential quantifier *}

text{*

We can also show that the existential quantifier of
\citet[\S5]{Plotkin77} is not PCF-definable using logical relations.

Our definition is quite loose; if the argument function @{term "f"}
maps any value to @{term "ValTT"} then @{term "plotkin_exists"} yields
@{term "ValTT"}. It may be more plausible to test @{term "f"} on
numerals only.

*}

definition plotkin_exists :: "ValD \<Rightarrow> ValD" where
  "plotkin_exists f \<equiv>
     if (appF\<cdot>f\<cdot>\<bottom> = ValFF)
       then ValFF
       else if (\<exists>n. appF\<cdot>f\<cdot>n = ValTT) then ValTT else \<bottom>"
(*<*)

lemma plotkin_exists_simps [simp]:
  "plotkin_exists \<bottom> = \<bottom>"
  "plotkin_exists (ValF\<cdot>\<bottom>) = \<bottom>"
  "plotkin_exists (ValF\<cdot>(\<Lambda> _. ValFF)) = ValFF"
  unfolding plotkin_exists_def by simp_all

lemma plotkin_exists_tt [simp]:
  "appF\<cdot>f\<cdot>(ValN\<cdot>n) = ValTT \<Longrightarrow> plotkin_exists f = ValTT"
  unfolding plotkin_exists_def
  using monofun_cfun_arg[where f="appF\<cdot>f" and x="\<bottom>"]
  by auto

lemma monofun_pe:
  "monofun plotkin_exists"
proof(rule monofunI)
  fix f g assume fg: "(f::ValD) \<sqsubseteq> g"
  let ?goal = "plotkin_exists f \<sqsubseteq> plotkin_exists g"
  {
    assume fbot: "appF\<cdot>f\<cdot>\<bottom> = ValFF"
    with fg have "appF\<cdot>g\<cdot>\<bottom> = ValFF"
      using monofun_cfun[where f="appF\<cdot>f" and g="appF\<cdot>g" and x="\<bottom>"]
      by (simp add: monofun_cfun_arg)
    with fbot have ?goal by (simp add: plotkin_exists_def)
  }
  moreover
  {
    assume efn: "\<exists>n. appF\<cdot>f\<cdot>n = ValTT"
    then obtain n where fn: "appF\<cdot>f\<cdot>n = ValTT" by blast
    hence fbot: "appF\<cdot>f\<cdot>\<bottom> \<noteq> ValFF"
      using monofun_cfun_arg[where f="appF\<cdot>f" and x="\<bottom>" and y="n"] by fastforce
    from fg have "appF\<cdot>f\<cdot>n \<sqsubseteq> appF\<cdot>g\<cdot>n"
      using monofun_cfun_arg[OF fg, where f=appF]
      by (simp only: cfun_below_iff)
    with fn have gn: "appF\<cdot>g\<cdot>n = ValTT"
      using ValD.nchotomy[where y="appF\<cdot>g\<cdot>\<bottom>"] by simp
    hence gbot: "appF\<cdot>g\<cdot>\<bottom> \<noteq> ValFF"
      using monofun_cfun_arg[where f="appF\<cdot>g" and x="\<bottom>" and y="n"] by fastforce
    from fn gn fbot gbot have ?goal apply (unfold plotkin_exists_def) by fastforce
  }
  moreover
  {
    assume fbot: "appF\<cdot>f\<cdot>\<bottom> \<noteq> ValFF" and efn: "\<not>(\<exists>n. appF\<cdot>f\<cdot>n = ValTT)"
    hence ?goal by (simp add: plotkin_exists_def)
  }
  ultimately show ?goal unfolding plotkin_exists_def by blast
qed

(*>*)
text{*

We can show this function is continuous.

*}

lemma cont_pe [cont2cont, simp]: "cont plotkin_exists"
(*<*)
proof (rule contI2[OF monofun_pe])
  fix Y assume Y: "chain (Y :: nat \<Rightarrow> ValD)"
  let ?goal = "plotkin_exists (\<Squnion> i. Y i) \<sqsubseteq> (\<Squnion> i. plotkin_exists (Y i))"
  have peY: "chain (\<lambda>i. plotkin_exists (Y i))"
    by (rule chainI, simp add: monofunE[OF monofun_pe] chainE[OF Y])
  {
    assume "\<exists>i. appF\<cdot>(Y i)\<cdot>\<bottom> = ValFF"
    then obtain i where Yi: "appF\<cdot>(Y i)\<cdot>\<bottom> = ValFF" by blast
    have "Y i \<sqsubseteq> (\<Squnion> i. Y i)"
      using is_ub_thelub[OF Y, where x=i] by simp
    hence "appF\<cdot>(Y i)\<cdot>\<bottom> \<sqsubseteq> appF\<cdot>(\<Squnion> i. Y i)\<cdot>\<bottom>" by (fastforce intro: monofun_cfun)
    with Yi have "ValFF \<sqsubseteq> appF\<cdot>(\<Squnion> i. Y i)\<cdot>\<bottom>" by simp
    hence "appF\<cdot>(\<Squnion> i. Y i)\<cdot>\<bottom> = ValFF" using ValD.nchotomy[where y="appF\<cdot>(\<Squnion> i. Y i)\<cdot>\<bottom>"] by simp
    moreover
    from Yi have "plotkin_exists (Y i) = ValFF" by (simp add: plotkin_exists_def)
    hence "ValFF \<sqsubseteq> (\<Squnion> i. plotkin_exists (Y i))" using is_ub_thelub[OF peY, where x=i] by simp
    hence "ValFF = (\<Squnion> i. plotkin_exists (Y i))" using ValD.nchotomy[where y="\<Squnion> i. plotkin_exists (Y i)"] by simp
    ultimately have ?goal by (simp add: plotkin_exists_def)
  }
  moreover
  {
    assume "\<exists>i j. appF\<cdot>(Y i)\<cdot>j = ValTT"
    then obtain i j where Yij: "appF\<cdot>(Y i)\<cdot>j = ValTT" by blast
    from Yij have Yib: "appF\<cdot>(Y i)\<cdot>\<bottom> \<noteq> ValFF"
      using monofun_cfun_arg[where f="appF\<cdot>(Y i)" and x="\<bottom>" and y=j] by clarsimp
    moreover
    from Yij have "appF\<cdot>(Y i)\<cdot>j \<sqsubseteq> appF\<cdot>(\<Squnion> i. Y i)\<cdot>j"
      using is_ub_thelub[OF Y, where x=i] by (fastforce intro: monofun_cfun)
    with Yij have Yjlub: "appF\<cdot>(\<Squnion> i. Y i)\<cdot>j = ValTT"
      using ValD.nchotomy[where y="appF\<cdot>(\<Squnion> i. Y i)\<cdot>j"] by simp
    moreover
    from Yjlub have "appF\<cdot>(\<Squnion> i. Y i)\<cdot>\<bottom> \<noteq> ValFF"
      using monofun_cfun_arg[where f="appF\<cdot>(\<Squnion> i. Y i)" and x="\<bottom>" and y=j] by auto
    moreover
    from Yib Yij have "plotkin_exists (Y i) = ValTT" by (auto simp add: plotkin_exists_def)
    hence "ValTT \<sqsubseteq> (\<Squnion> i. plotkin_exists (Y i))" using is_ub_thelub[OF peY, where x=i] by simp
    hence "ValTT = (\<Squnion> i. plotkin_exists (Y i))" using ValD.nchotomy[where y="\<Squnion> i. plotkin_exists (Y i)"] by simp
    ultimately have ?goal by (simp add: plotkin_exists_def)
  }
  moreover
  {
    assume nFF: "\<not>(\<exists>i. appF\<cdot>(Y i)\<cdot>\<bottom> = ValFF)" and nTT: "\<not>(\<exists>i j. appF\<cdot>(Y i)\<cdot>j = ValTT)"
    with Y have ?goal
      unfolding plotkin_exists_def
      apply (simp add: contlub_cfun_arg contlub_cfun_fun)
      using compact_below_lub_iff[OF ValD.compacts(2)]
            compact_below_lub_iff[OF ValD.compacts(3)]
      apply auto
      done
  }
  ultimately show ?goal by blast
qed

lemma cont_pe2[cont2cont, simp]: "cont f \<Longrightarrow> cont (\<lambda>x. plotkin_exists (f x))"
  by (rule cont_apply) simp_all

(*>*)
text{*

Again we construct argument and result test vectors such that @{term
"plotkin_exists"} satisfies these tests but no PCF-definable term
does.

*}

definition PE_arg_rel where
  "PE_arg_rel \<equiv> \<lambda>i. ValF\<cdot>(case i of
        0 \<Rightarrow> (\<Lambda> _. ValFF)
      | Suc n \<Rightarrow> (\<Lambda> (ValN\<cdot>x). if x = Suc n then ValTT else \<bottom>))"

definition PE_result_rel where
  "PE_result_rel \<equiv> \<lambda>i. case i of 0 \<Rightarrow> ValFF | Suc n \<Rightarrow> ValTT"

text{*

Note that unlike the POR case the argument relation does not
characterise PE: we don't treat functions that return @{term "ValTT"}s
and @{term "ValFF"}s.

The Plotkin existential satisfies these tests:

*}

theorem pe_sat:
  "appFLv (ValF\<cdot>(\<Lambda> x. plotkin_exists x)) [PE_arg_rel] = PE_result_rel"
  unfolding PE_arg_rel_def PE_result_rel_def
  by (clarsimp simp: fun_eq_iff split: nat.splits)

text{*

As for POR, the difference between the two vectors is that the
argument can diverge but not the result.

*}

definition PE_base_lf_rep :: "(nat \<Rightarrow> ValD) lf_rep" where
  "PE_base_lf_rep \<equiv> \<lambda>(mR, pR).
     { \<bottom> }
   \<union> { (\<lambda>i. ValTT) } \<union> { (\<lambda>i. ValFF) } (* x = y = z for bools *)
   \<union> (\<Union>n. { (\<lambda>i. ValN\<cdot>n) }) (* x = y = z for numerals *)
   \<union> { f . f 1 = \<bottom> \<or> f 2 = \<bottom> } (* Vectors that diverge on one or two. *)"
(*<*)

lemma adm_PE_base_lf_rep:
  "adm (\<lambda>x. x \<in> PE_base_lf_rep r)"
unfolding PE_base_lf_rep_def
using adm_below_monic_exists[OF _ below_monic_fun_K[where f=ValN], where P="\<lambda>_. True"]
by (auto intro!: adm_disj simp: cont_fun)

lemma mono_PE_base_lf_rep:
  "mono PE_base_lf_rep"
unfolding PE_base_lf_rep_def
by (blast intro!: monoI)

(*>*)
text{*

Again we close this under the function space, and show that it is
admissible, monotonic and respects the minimal invariant.

*}

definition PE_lf_rep :: "(nat \<Rightarrow> ValD) lf_rep" where
  "PE_lf_rep R \<equiv> PE_base_lf_rep R \<union> fn_lf_rep R"

abbreviation "PE_lf \<equiv> \<lambda>r. mklr (PE_lf_rep r)"
(*<*)

lemma admS_PE_lf [intro, simp]:
  "PE_lf_rep r \<in> admS"
proof
  show "\<bottom> \<in> PE_lf_rep r"
    unfolding PE_lf_rep_def PE_base_lf_rep_def
    by simp
next
  show "adm (\<lambda>x. x \<in> PE_lf_rep r)"
    unfolding PE_lf_rep_def
    using adm_PE_base_lf_rep[of r] adm_fn[of r] by simp
qed

lemma mono_PE_lf:
  "mono PE_lf"
  apply (rule monoI)
  apply simp
  unfolding PE_lf_rep_def
  using mono_fn_lf_rep mono_PE_base_lf_rep
  apply (blast dest: monoD)
  done

lemma min_inv_PE_lf:
  assumes "eRSV e R' S'"
  shows "eRSV (ValD_copy_rec\<cdot>e) (dual (PE_lf (dual S', undual R'))) (PE_lf (R', S'))"
  apply clarsimp
  apply (simp add: PE_lf_rep_def)
  apply (elim disjE)
   apply (rule disjI1)
   apply (auto simp: PE_base_lf_rep_def eta_cfun cfcomp1 cfun_eq_iff)[1]
  apply (rule disjI2)
  using assms
  apply (clarsimp simp: fn_lf_rep_def eta_cfun)
  apply (simp add: cfcomp1 cfun_map_def)
  apply (rule_tac x="\<lambda>x. \<Lambda> xa. e\<cdot>(fs x\<cdot>(e\<cdot>xa))" in exI)
  apply force
  done

interpretation PE: DomSolV ValD_copy_rec PE_lf
  apply standard
    apply (rule ValD_copy_ID)
   apply (rule mono_PE_lf)
  apply (erule min_inv_PE_lf)
  done

lemma PEI [intro, simp]:
  "\<bottom> \<in> unlr PE.delta"
  "(\<lambda>i. ValTT) \<in> unlr PE.delta"
  "(\<lambda>i. ValFF) \<in> unlr PE.delta"
  "(\<lambda>i. ValN\<cdot>n) \<in> unlr PE.delta"
  "f 1 = \<bottom> \<Longrightarrow> f \<in> unlr PE.delta"
  "f 2 = \<bottom> \<Longrightarrow> f \<in> unlr PE.delta"
  "\<lbrakk> \<And>xs. xs \<in> unlr PE.delta \<Longrightarrow> (\<lambda>j. (fs j)\<cdot>(xs j)) \<in> unlr PE.delta \<rbrakk> \<Longrightarrow> (\<lambda>i. ValF\<cdot>(fs i)) \<in> unlr PE.delta"
  by (subst PE.delta_sol, simp, subst PE_lf_rep_def,
      fastforce simp: PE_base_lf_rep_def fn_lf_rep_def eta_cfun cfcomp1)+

lemma PE_fun_constI:
  "\<lbrakk> \<And>xs. xs \<in> unlr PE.delta \<Longrightarrow> (\<lambda>j. f\<cdot>(xs j)) \<in> unlr PE.delta \<rbrakk> \<Longrightarrow> (\<lambda>i. ValF\<cdot>f) \<in> unlr PE.delta"
  using PEI(7)[where fs="\<lambda>_. f"] by simp

lemma PEE:
  "\<lbrakk> a \<in> unlr PE.delta;
     (a = \<bottom> \<Longrightarrow> P);
     (a = (\<lambda>i. ValTT) \<Longrightarrow> P);
     (a = (\<lambda>i. ValFF) \<Longrightarrow> P);
     (\<And>n. a = (\<lambda>i. ValN\<cdot>n) \<Longrightarrow> P);
     (a 1 = \<bottom> \<Longrightarrow> P);
     (a 2 = \<bottom> \<Longrightarrow> P);
     (\<And>fs. \<lbrakk> a = (\<lambda>j. ValF\<cdot>(fs j)); \<And>xs. xs \<in> unlr PE.delta \<Longrightarrow> (\<lambda>j. (fs j)\<cdot>(xs j)) \<in> unlr PE.delta \<rbrakk> \<Longrightarrow> P)
   \<rbrakk> \<Longrightarrow> P"
  apply (subst (asm) PE.delta_sol)
  apply simp
  apply (subst (asm) PE_lf_rep_def)
  apply (fastforce simp: PE_base_lf_rep_def fn_lf_rep_def eta_cfun)
  done

lemma PEE_strict_appI:
  assumes "xs \<in> unlr PE.delta"
  assumes "\<And>xs. xs \<in> unlr PE.delta \<Longrightarrow> (\<lambda>j. fs j\<cdot>(xs j)) \<in> unlr PE.delta"
  shows "(\<lambda>j. strictify\<cdot>(fs j)\<cdot>(xs j)) \<in> unlr PE.delta"
  using assms
  apply -
  apply (erule PEE)
  apply simp_all
  done

lemma logical_relation_PE:
  "logical_relation (unlr PE.delta)"
apply (rule logical_relationI)

  (* Strict application *)
  prefer 2
  apply (cut_tac fs="\<lambda>i. appF\<cdot>(fs i)" and xs=xs in PEE_strict_appI)
   apply simp_all
  apply (auto elim: PEE)[1]

  (* FIXME fixD *)
  prefer 2
  apply (erule PEE)
  apply (simp_all add: fixD_def)
  apply (subst fix_argument_promote_fun)
  apply (rule_tac F="\<Lambda> f. (\<lambda>x. fs x\<cdot>(f x))" in fix_ind)
  apply (simp_all split: nat.split add: cont_fun)

  apply (auto elim: PEE simp: cond_def isZero_def pred_def succ_def eta_cfun split: nat.split)
  done

lemma PCF_consts_rel_PE:
  "PCF_consts_rel (unlr PE.delta)"
  by (rule PCF_consts_relI) simp_all
(*>*)
text{*

The solution satisfies the expectations of the fundamental theorem:

*}

lemma PCF_lr_PE_delta: "PCF_lr (unlr PE.delta)"
(*<*)
  using logical_relation_PE PCF_consts_rel_PE by fastforce
(*>*)

lemma lr_PE_arg_rel: "PE_arg_rel \<in> unlr PE.delta"
(*<*)
  unfolding PE_arg_rel_def
  apply (rule PEI(7))
  apply (erule PEE)
   apply simp_all
  apply (case_tac n)
   apply simp
  apply (case_tac nat)
   apply simp_all
  done
(*>*)

lemma lr_PE_result_rel: "PE_result_rel \<notin> unlr PE.delta"
(*<*)
unfolding PE_result_rel_def
apply clarify
apply (erule PEE)
apply (auto iff: fun_eq_iff split: nat.splits)
done
(*>*)

theorem PE_is_not_definable: "\<not>(\<exists>f. definable f \<and> appFLv f [PE_arg_rel] = PE_result_rel)"
(*<*)
apply (rule not_definable[where R="unlr PE.delta"])
  using lr_PE_arg_rel lr_PE_result_rel PCF_lr_PE_delta
  apply simp_all
done
(*>*)

subsection{* Concluding remarks *}

text{*

These techniques could be used to show that Haskell's @{text "seq"}
operation is not PCF-definable. (It is definable for each base
``type'' separately, and requires some care on function values.) If we
added an (unlifted) product type then it should be provable that
parallel evaluation is required to support @{text "seq"} on these
objects (given @{text "seq"} on all other objects). (See
\citet[\S5.4]{DBLP:conf/hopl/HudakHJW07} and sundry posts to the
internet by Lennart Augustsson.) This may be difficult to do plausibly
without adding a type system.

*}

(*<*)

end
(*>*)
