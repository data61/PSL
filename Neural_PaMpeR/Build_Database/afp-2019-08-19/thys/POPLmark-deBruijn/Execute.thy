(*  Author:     Stefan Berghofer, TU Muenchen, 2005; Lukas Bulwahn, TU Muenchen, 2009
*)

theory Execute
imports POPLmarkRecord "HOL-Library.Code_Target_Numeral"
begin

section \<open>Executing the specification\<close>

text \<open>
\label{sec:exec}
An important criterion that a solution to the {\sc PoplMark} Challenge should
fulfill is the possibility to {\it animate} the specification. For example,
it should be possible to apply the reduction relation for the calculus to
example terms. Since the reduction relations are defined inductively, they can
be interpreted as a logic program in the style of {\sc Prolog}.
The definition of the single-step evaluation relation presented in \secref{sec:evaluation}
and \secref{sec:evaluation-rcd} is directly executable.

In order to compute the normal form of a term using the one-step evaluation
relation \<open>\<longmapsto>\<close>, we introduce the inductive predicate \<open>t \<Down> u\<close>,
denoting that \<open>u\<close> is a normal form of \<open>t\<close>.
\<close>

inductive norm :: "trm \<Rightarrow> trm \<Rightarrow> bool"  (infixl "\<Down>" 50)
where
  "t \<in> value \<Longrightarrow> t \<Down> t"
| "t \<longmapsto> s \<Longrightarrow> s \<Down> u \<Longrightarrow> t \<Down> u"

definition normal_forms where
  "normal_forms t \<equiv> {u. t \<Down> u}"

lemma [code_pred_intro Rcd_Nil]: "valuep (Rcd [])"
by (auto intro: valuep.intros)

lemma [code_pred_intro Rcd_Cons]: "valuep t \<Longrightarrow> valuep (Rcd fs) \<Longrightarrow> valuep (Rcd ((l, t) # fs))" 
by (auto intro!: valuep.intros elim!: valuep.cases)

lemmas valuep.intros(1)[code_pred_intro Abs'] valuep.intros(2)[code_pred_intro TAbs']

code_pred (modes: i => bool) valuep
proof -
  case valuep
  from valuep.prems show thesis
  proof (cases rule: valuep.cases)
    case (Rcd fs)
    from this valuep.Rcd_Nil valuep.Rcd_Cons show thesis
      by (cases fs) (auto intro: valuep.intros)
  next
    case Abs
    with valuep.Abs' show thesis .
  next
    case TAbs
    with valuep.TAbs' show thesis .
  qed
qed

thm valuep.equation

code_pred (modes: i => i => bool, i => o => bool as normalize) norm .

thm norm.equation

lemma [code]:
  "normal_forms = set_of_pred o normalize"
unfolding set_of_pred_def o_def normal_forms_def [abs_def]
by (auto intro: set_eqI normalizeI elim: normalizeE)

lemma [code_unfold]: "x \<in> value \<longleftrightarrow> valuep x"
  by (simp add: value_def)

definition
  natT :: type where
  "natT \<equiv> \<forall><:Top. (\<forall><:TVar 0. (\<forall><:TVar 1. (TVar 2 \<rightarrow> TVar 1) \<rightarrow> TVar 0 \<rightarrow> TVar 1))"

definition
  fact2 :: trm where
  "fact2 \<equiv>
   LET PVar natT =
     (\<lambda><:Top. \<lambda><:TVar 0. \<lambda><:TVar 1. \<lambda>:TVar 2 \<rightarrow> TVar 1. \<lambda>: TVar 1. Var 1 \<bullet> Var 0)
   IN
   LET PRcd
     [(''pluspp'', PVar (natT \<rightarrow> natT \<rightarrow> natT)),
      (''multpp'', PVar (natT \<rightarrow> natT \<rightarrow> natT))] = Rcd
     [(''multpp'', \<lambda>:natT. \<lambda>:natT. \<lambda><:Top. \<lambda><:TVar 0. \<lambda><:TVar 1. \<lambda>:TVar 2 \<rightarrow> TVar 1.
        Var 5 \<bullet>\<^sub>\<tau> TVar 3 \<bullet>\<^sub>\<tau> TVar 2 \<bullet>\<^sub>\<tau> TVar 1 \<bullet> (Var 4 \<bullet>\<^sub>\<tau> TVar 3 \<bullet>\<^sub>\<tau> TVar 2 \<bullet>\<^sub>\<tau> TVar 1) \<bullet> Var 0),
      (''pluspp'', \<lambda>:natT. \<lambda>:natT. \<lambda><:Top. \<lambda><:TVar 0. \<lambda><:TVar 1. \<lambda>:TVar 2 \<rightarrow> TVar 1. \<lambda>:TVar 1.
        Var 6 \<bullet>\<^sub>\<tau> TVar 4 \<bullet>\<^sub>\<tau> TVar 3 \<bullet>\<^sub>\<tau> TVar 3 \<bullet> Var 1 \<bullet>
          (Var 5 \<bullet>\<^sub>\<tau> TVar 4 \<bullet>\<^sub>\<tau> TVar 3 \<bullet>\<^sub>\<tau> TVar 2 \<bullet> Var 1 \<bullet> Var 0))]
   IN
     Var 0 \<bullet> (Var 1 \<bullet> Var 2 \<bullet> Var 2) \<bullet> Var 2"

value "normal_forms fact2"

text \<open>
Unfortunately, the definition based
on evaluation contexts from \secref{sec:evaluation-ctxt} is not directly executable.
The reason is that from the definition of evaluation contexts, the code generator
cannot immediately read off an algorithm that, given a term \<open>t\<close>, computes a context
\<open>E\<close> and a term \<open>t\<^sub>0\<close> such that \<open>t = E t\<^sub>0\<close>. In order to do this, one
would have to extract the algorithm contained in the proof of the {\it decomposition lemma}
from \secref{sec:evaluation-ctxt}.
\<close>

values "{u. norm fact2 u}"

end
