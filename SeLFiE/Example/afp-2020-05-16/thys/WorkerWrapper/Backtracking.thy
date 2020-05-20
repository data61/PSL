(*<*)
(*
 * The worker/wrapper transformation, following Gill and Hutton.
 * (C)opyright 2009-2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory Backtracking
imports
  HOLCF
  Nats
  WorkerWrapperNew
begin

(*>*)
section\<open>Backtracking using lazy lists and continuations\<close>

text\<open>
\label{sec:ww-backtracking}

To illustrate the utility of worker/wrapper fusion to programming
language semantics, we consider here the first-order part of a
higher-order backtracking language by \citet{DBLP:conf/icfp/WandV04};
see also \citet{DBLP:journals/ngc/DanvyGR01}. We refer the reader to
these papers for a broader motivation for these languages.

As syntax is typically considered to be inductively generated, with
each syntactic object taken to be finite and completely defined, we
define the syntax for our language using a HOL datatype:

\<close>

datatype expr = const nat | add expr expr | disj expr expr | fail
(*<*)

lemma case_expr_cont[cont2cont]:
  assumes f1: "\<And>y. cont (\<lambda>x. f1 x y)"
  assumes f2: "\<And>y z. cont (\<lambda>x. f2 x y z)"
  assumes f3: "\<And>y z. cont (\<lambda>x. f3 x y z)"
  assumes f4: "cont (\<lambda>x. f4 x)"
  shows "cont (\<lambda>x. case_expr (f1 x) (f2 x) (f3 x) (f4 x) expr)"
  using assms by (cases expr) simp_all

(* Presumably obsolete in the HG version, not so in Isabelle2011. *)

fun
  expr_encode :: "expr \<Rightarrow> nat"
where
  "expr_encode (const n) = prod_encode (0, n)"
| "expr_encode (add e1 e2) = prod_encode (1, (prod_encode (expr_encode e1, expr_encode e2)))"
| "expr_encode (disj e1 e2) = prod_encode (2, (prod_encode (expr_encode e1, expr_encode e2)))"
| "expr_encode fail = prod_encode (3, 0)"

lemma expr_encode_inj:
  "expr_encode x = expr_encode y \<Longrightarrow> x = y"
  by (induct x arbitrary: y) ((case_tac y, auto dest!: inj_onD[OF inj_prod_encode, where A=UNIV])[1])+

instance expr :: countable
  by (rule countable_classI[OF expr_encode_inj])

(*>*)
text\<open>

The language consists of constants, an addition function, a
disjunctive choice between expressions, and failure. We give it a
direct semantics using the monad of lazy lists of natural numbers,
with the goal of deriving an an extensionally-equivalent evaluator
that uses double-barrelled continuations.

Our theory of lazy lists is entirely standard.

\<close>

default_sort predomain

domain 'a llist =
    lnil
  | lcons (lazy "'a") (lazy "'a llist")

text\<open>

By relaxing the default sort of type variables to \<open>predomain\<close>,
our polymorphic definitions can be used at concrete types that do not
contain @{term "\<bottom>"}. These include those constructed from HOL types
using the discrete ordering type constructor @{typ "'a discr"}, and in
particular our interpretation @{typ "nat discr"} of the natural
numbers.

The following standard list functions underpin the monadic
infrastructure:

\<close>

fixrec lappend :: "'a llist \<rightarrow> 'a llist \<rightarrow> 'a llist" where
  "lappend\<cdot>lnil\<cdot>ys = ys"
| "lappend\<cdot>(lcons\<cdot>x\<cdot>xs)\<cdot>ys = lcons\<cdot>x\<cdot>(lappend\<cdot>xs\<cdot>ys)"

fixrec lconcat :: "'a llist llist \<rightarrow> 'a llist" where
  "lconcat\<cdot>lnil = lnil"
| "lconcat\<cdot>(lcons\<cdot>x\<cdot>xs) = lappend\<cdot>x\<cdot>(lconcat\<cdot>xs)"

fixrec lmap :: "('a \<rightarrow> 'b) \<rightarrow> 'a llist \<rightarrow> 'b llist" where
  "lmap\<cdot>f\<cdot>lnil = lnil"
| "lmap\<cdot>f\<cdot>(lcons\<cdot>x\<cdot>xs) = lcons\<cdot>(f\<cdot>x)\<cdot>(lmap\<cdot>f\<cdot>xs)"
(*<*)

lemma lappend_strict'[simp]: "lappend\<cdot>\<bottom> = (\<Lambda> a. \<bottom>)"
  by fixrec_simp

lemma lconcat_strict[simp]: "lconcat\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma lmap_strict[simp]: "lmap\<cdot>f\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

(*>*)
text\<open>

We define the lazy list monad \<open>S\<close> in the traditional fashion:

\<close>

type_synonym S = "nat discr llist"

definition returnS :: "nat discr \<rightarrow> S" where
  "returnS = (\<Lambda> x. lcons\<cdot>x\<cdot>lnil)"

definition bindS :: "S \<rightarrow> (nat discr \<rightarrow> S) \<rightarrow> S" where
  "bindS = (\<Lambda> x g. lconcat\<cdot>(lmap\<cdot>g\<cdot>x))"

text\<open>

Unfortunately the lack of higher-order polymorphism in HOL prevents us
from providing the general typing one would expect a monad to have in
Haskell.

The evaluator uses the following extra constants:

\<close>

definition addS :: "S \<rightarrow> S \<rightarrow> S" where
  "addS \<equiv> (\<Lambda> x y. bindS\<cdot>x\<cdot>(\<Lambda> xv. bindS\<cdot>y\<cdot>(\<Lambda> yv. returnS\<cdot>(xv + yv))))"

definition disjS :: "S \<rightarrow> S \<rightarrow> S" where
  "disjS \<equiv> lappend"

definition failS :: "S" where
  "failS \<equiv> lnil"

text\<open>

We interpret our language using these combinators in the obvious
way. The only complication is that, even though our evaluator is
primitive recursive, we must explicitly use the fixed point operator
as the worker/wrapper technique requires us to talk about the body of
the recursive definition.

\<close>

definition
  evalS_body :: "(expr discr \<rightarrow> nat discr llist)
              \<rightarrow> (expr discr \<rightarrow> nat discr llist)"
where
  "evalS_body \<equiv> \<Lambda> r e. case undiscr e of
     const n \<Rightarrow> returnS\<cdot>(Discr n)
   | add e1 e2 \<Rightarrow> addS\<cdot>(r\<cdot>(Discr e1))\<cdot>(r\<cdot>(Discr e2))
   | disj e1 e2 \<Rightarrow> disjS\<cdot>(r\<cdot>(Discr e1))\<cdot>(r\<cdot>(Discr e2))
   | fail \<Rightarrow> failS"

abbreviation evalS :: "expr discr \<rightarrow> nat discr llist" where
  "evalS \<equiv> fix\<cdot>evalS_body"

text\<open>

We aim to transform this evaluator into one using double-barrelled
continuations; one will serve as a "success" context, taking a natural
number into "the rest of the computation", and the other outright
failure.

In general we could work with an arbitrary observation type ala
\citet{DBLP:conf/icalp/Reynolds74}, but for convenience we use the
clearly adequate concrete type @{typ "nat discr llist"}.

\<close>

type_synonym Obs = "nat discr llist"
type_synonym Failure = "Obs"
type_synonym Success = "nat discr \<rightarrow> Failure \<rightarrow> Obs"
type_synonym K = "Success \<rightarrow> Failure \<rightarrow> Obs"

text\<open>

To ease our development we adopt what
\citet[\S5]{DBLP:conf/icfp/WandV04} call a "failure computation"
instead of a failure continuation, which would have the type @{typ
"unit \<rightarrow> Obs"}.

The monad over the continuation type @{typ "K"} is as follows:

\<close>

definition returnK :: "nat discr \<rightarrow> K" where
  "returnK \<equiv> (\<Lambda> x. \<Lambda> s f. s\<cdot>x\<cdot>f)"

definition bindK :: "K \<rightarrow> (nat discr \<rightarrow> K) \<rightarrow> K" where
  "bindK \<equiv> \<Lambda> x g. \<Lambda> s f. x\<cdot>(\<Lambda> xv f'. g\<cdot>xv\<cdot>s\<cdot>f')\<cdot>f"

text\<open>

Our extra constants are defined as follows:

\<close>

definition addK :: "K \<rightarrow> K \<rightarrow> K" where
  "addK \<equiv> (\<Lambda> x y. bindK\<cdot>x\<cdot>(\<Lambda> xv. bindK\<cdot>y\<cdot>(\<Lambda> yv. returnK\<cdot>(xv + yv))))"

definition disjK :: "K \<rightarrow> K \<rightarrow> K" where
  "disjK \<equiv> (\<Lambda> g h. \<Lambda> s f. g\<cdot>s\<cdot>(h\<cdot>s\<cdot>f))"

definition failK :: "K" where
  "failK \<equiv> \<Lambda> s f. f"

text\<open>

The continuation semantics is again straightforward:

\<close>

definition
  evalK_body :: "(expr discr \<rightarrow> K) \<rightarrow> (expr discr \<rightarrow> K)"
where
  "evalK_body \<equiv> \<Lambda> r e. case undiscr e of
     const n \<Rightarrow> returnK\<cdot>(Discr n)
   | add e1 e2 \<Rightarrow> addK\<cdot>(r\<cdot>(Discr e1))\<cdot>(r\<cdot>(Discr e2))
   | disj e1 e2 \<Rightarrow> disjK\<cdot>(r\<cdot>(Discr e1))\<cdot>(r\<cdot>(Discr e2))
   | fail \<Rightarrow> failK"

abbreviation evalK :: "expr discr \<rightarrow> K" where
  "evalK \<equiv> fix\<cdot>evalK_body"

text\<open>

We now set up a worker/wrapper relation between these two semantics.

The kernel of @{term "unwrap"} is the following function that converts
a lazy list into an equivalent continuation representation.

\<close>

fixrec SK :: "S \<rightarrow> K" where
  "SK\<cdot>lnil = failK"
| "SK\<cdot>(lcons\<cdot>x\<cdot>xs) = (\<Lambda> s f. s\<cdot>x\<cdot>(SK\<cdot>xs\<cdot>s\<cdot>f))"

definition
  unwrap :: "(expr discr \<rightarrow> nat discr llist) \<rightarrow> (expr discr \<rightarrow> K)"
where
  "unwrap \<equiv> \<Lambda> r e. SK\<cdot>(r\<cdot>e)"
(*<*)

lemma SK_strict[simp]: "SK\<cdot>\<bottom> = \<bottom>"
  by fixrec_simp

lemma unwrap_strict[simp]: "unwrap\<cdot>\<bottom> = \<bottom>"
  unfolding unwrap_def by simp

(*>*)
text\<open>

Symmetrically @{term "wrap"} converts an evaluator using continuations
into one generating lazy lists by passing it the right continuations.

\<close>

definition KS :: "K \<rightarrow> S" where
  "KS \<equiv> (\<Lambda> k. k\<cdot>lcons\<cdot>lnil)"

definition wrap :: "(expr discr \<rightarrow> K) \<rightarrow> (expr discr \<rightarrow> nat discr llist)" where
  "wrap \<equiv> \<Lambda> r e. KS\<cdot>(r\<cdot>e)"
(*<*)

lemma KS_strict[simp]: "KS\<cdot>\<bottom> = \<bottom>"
  unfolding KS_def by simp

lemma wrap_strict[simp]: "wrap\<cdot>\<bottom> = \<bottom>"
  unfolding wrap_def by simp

(*>*)
text\<open>

The worker/wrapper condition follows directly from these definitions.

\<close>

lemma KS_SK_id:
  "KS\<cdot>(SK\<cdot>xs) = xs"
  by (induct xs) (simp_all add: KS_def failK_def)

lemma wrap_unwrap_id:
  "wrap oo unwrap = ID"
  unfolding wrap_def unwrap_def
  by (simp add: KS_SK_id cfun_eq_iff)

text\<open>

The worker/wrapper transformation is only non-trivial if @{term
"wrap"} and @{term "unwrap"} do not witness an isomorphism. In this
case we can show that we do not even have a Galois connection.

\<close>

lemma cfun_not_below:
  "f\<cdot>x \<notsqsubseteq> g\<cdot>x \<Longrightarrow> f \<notsqsubseteq> g"
  by (auto simp: cfun_below_iff)

lemma unwrap_wrap_not_under_id:
  "unwrap oo wrap \<notsqsubseteq> ID"
proof -
  let ?witness = "\<Lambda> e. (\<Lambda> s f. lnil :: K)"
  have "(unwrap oo wrap)\<cdot>?witness\<cdot>(Discr fail)\<cdot>\<bottom>\<cdot>(lcons\<cdot>0\<cdot>lnil)
       \<notsqsubseteq> ?witness\<cdot>(Discr fail)\<cdot>\<bottom>\<cdot>(lcons\<cdot>0\<cdot>lnil)"
    by (simp add: failK_def wrap_def unwrap_def KS_def)
  hence "(unwrap oo wrap)\<cdot>?witness \<notsqsubseteq> ?witness"
    by (fastforce intro!: cfun_not_below)
  thus ?thesis by (simp add: cfun_not_below)
qed

text\<open>

We now apply \texttt{worker\_wrapper\_id}:

\<close>

definition eval_work :: "expr discr \<rightarrow> K" where
  "eval_work \<equiv> fix\<cdot>(unwrap oo evalS_body oo wrap)"

definition eval_ww :: "expr discr \<rightarrow> nat discr llist" where
  "eval_ww \<equiv> wrap\<cdot>eval_work"

lemma "evalS = eval_ww"
  unfolding eval_ww_def eval_work_def
  using worker_wrapper_id[OF wrap_unwrap_id]
  by simp

text\<open>

We now show how the monadic operations correspond by showing that
@{term "SK"} witnesses a \emph{monad morphism}
\citep[\S6]{wadler92:_comprehending_monads}. As required by
\citet[Definition~2.1]{DBLP:journals/ngc/DanvyGR01}, the mapping needs
to hold for our specific operations in addition to the common monadic
scaffolding.

\<close>

lemma SK_returnS_returnK:
  "SK\<cdot>(returnS\<cdot>x) = returnK\<cdot>x"
  by (simp add: returnS_def returnK_def failK_def)

lemma SK_lappend_distrib:
 "SK\<cdot>(lappend\<cdot>xs\<cdot>ys)\<cdot>s\<cdot>f = SK\<cdot>xs\<cdot>s\<cdot>(SK\<cdot>ys\<cdot>s\<cdot>f)"
  by (induct xs) (simp_all add: failK_def)

lemma SK_bindS_bindK:
  "SK\<cdot>(bindS\<cdot>x\<cdot>g) = bindK\<cdot>(SK\<cdot>x)\<cdot>(SK oo g)"
  by (induct x)
     (simp_all add: cfun_eq_iff
                    bindS_def bindK_def failK_def
                    SK_lappend_distrib)

lemma SK_addS_distrib:
  "SK\<cdot>(addS\<cdot>x\<cdot>y) = addK\<cdot>(SK\<cdot>x)\<cdot>(SK\<cdot>y)"
  by (clarsimp simp: cfcomp1
                     addS_def addK_def failK_def
                     SK_bindS_bindK SK_returnS_returnK)

lemma SK_disjS_disjK:
 "SK\<cdot>(disjS\<cdot>xs\<cdot>ys) = disjK\<cdot>(SK\<cdot>xs)\<cdot>(SK\<cdot>ys)"
  by (simp add: cfun_eq_iff disjS_def disjK_def SK_lappend_distrib)

lemma SK_failS_failK:
  "SK\<cdot>failS = failK"
  unfolding failS_def by simp

text\<open>

These lemmas directly establish the precondition for our all-in-one
worker/wrapper and fusion rule:

\<close>

lemma evalS_body_evalK_body:
  "unwrap oo evalS_body oo wrap = evalK_body oo unwrap oo wrap"
proof(intro cfun_eqI)
  fix r e' s f
  obtain e :: "expr"
    where ee': "e' = Discr e" by (cases e')
  have "(unwrap oo evalS_body oo wrap)\<cdot>r\<cdot>(Discr e)\<cdot>s\<cdot>f
      = (evalK_body oo unwrap oo wrap)\<cdot>r\<cdot>(Discr e)\<cdot>s\<cdot>f"
    by (cases e)
       (simp_all add: evalS_body_def evalK_body_def unwrap_def
                      SK_returnS_returnK SK_addS_distrib
                      SK_disjS_disjK SK_failS_failK)
  with ee' show "(unwrap oo evalS_body oo wrap)\<cdot>r\<cdot>e'\<cdot>s\<cdot>f
                = (evalK_body oo unwrap oo wrap)\<cdot>r\<cdot>e'\<cdot>s\<cdot>f"
    by simp
qed

theorem evalS_evalK:
  "evalS = wrap\<cdot>evalK"
  using worker_wrapper_fusion_new[OF wrap_unwrap_id unwrap_strict]
        evalS_body_evalK_body
  by simp

text\<open>

This proof can be considered an instance of the approach of
\citet{DBLP:journals/jfp/HuttonJG10}, which uses the worker/wrapper
machinery to relate two algebras.

This result could be obtained by a structural induction over the
syntax of the language. However our goal here is to show how such a
transformation can be achieved by purely equational means; this has
the advantange that our proof can be locally extended, e.g. to the
full language of \citet{DBLP:journals/ngc/DanvyGR01} simply by proving
extra equations. In contrast the higher-order language of
\citet{DBLP:conf/icfp/WandV04} is beyond the reach of this approach.

\<close>
(*<*)

end
(*>*)
