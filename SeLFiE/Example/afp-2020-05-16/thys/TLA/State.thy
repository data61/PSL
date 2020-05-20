(*  Title:       A Definitional Encoding of TLA in Isabelle/HOL
    Authors:     Gudmund Grov <ggrov at inf.ed.ac.uk>
                 Stephan Merz <Stephan.Merz at loria.fr>
    Year:        2011
    Maintainer:  Gudmund Grov <ggrov at inf.ed.ac.uk>
*)

section \<open>Representing state in TLA*\<close>

theory State 
imports Liveness 
begin

text\<open>
  We adopt the hidden state appraoch, as used in the existing 
  Isabelle/HOL TLA embedding \cite{Merz98}. This approach is also used
  in \cite{Ehmety01}.
  Here, a state space is defined by its projections, and everything else is
  unknown. Thus, a variable is a projection of the state space, and has the same
  type as a state function. Moreover, strong typing is achieved, since the projection
  function may have any result type. To achieve this, the state space is represented
  by an undefined type, which is an instance of the \<open>world\<close> class to enable
  use with the \<open>Intensional\<close> theory.
\<close>

typedecl state

instance state :: world ..

type_synonym 'a statefun = "(state,'a) stfun"
type_synonym statepred  = "bool statefun"
type_synonym 'a tempfun = "(state,'a) formfun"
type_synonym temporal = "state formula"

text \<open>
  Formalizing type state would require formulas to be tagged with
  their underlying state space and would result in a system that is
  much harder to use. (Unlike Hoare logic or Unity, TLA has quantification
  over state variables, and therefore one usually works with different
  state spaces within a single specification.) Instead, state is just
  an anonymous type whose only purpose is to provide Skolem constants.
  Moreover, we do not define a type of state variables separate from that
  of arbitrary state functions, again in order to simplify the definition
  of flexible quantification later on. Nevertheless, we need to distinguish
  state variables, mainly to define the enabledness of actions. The user
  identifies (tuples of) ``base'' state variables in a specification via the
  ``meta predicate'' \<open>basevars\<close>, which is defined here.
\<close>

definition stvars    :: "'a statefun \<Rightarrow> bool"
where basevars_def:  "stvars \<equiv> surj" 

syntax
  "PRED"    :: "lift \<Rightarrow> 'a"                          ("PRED _")
  "_stvars" :: "lift \<Rightarrow> bool"                        ("basevars _")

translations
  "PRED P"   \<rightharpoonup>  "(P::state => _)"
  "_stvars"  \<rightleftharpoons>  "CONST stvars"

text \<open>
  Base variables may be assigned arbitrary (type-correct) values.
  In the following lemma, note that \<open>vs\<close> may be a tuple of variables.
  The correct identification of base variables is up to the user who must
  take care not to introduce an inconsistency. For example, @{term "basevars (x,x)"}
  would definitely be inconsistent.
\<close>

lemma basevars: "basevars vs \<Longrightarrow> \<exists>u. vs u = c"
proof (unfold basevars_def surj_def)
  assume "\<forall>y. \<exists>x. y = vs x"
  then obtain x where "c = vs x" by blast
  thus "\<exists>u. vs u = c" by blast
qed

lemma baseE: 
  assumes H1: "basevars v" and H2:"\<And>x. v x = c \<Longrightarrow> Q"
  shows "Q"
  using H1[THEN basevars] H2 by auto

text \<open>A variant written for sequences rather than single states.\<close>
lemma first_baseE:
  assumes H1: "basevars v" and H2: "\<And>x. v (first x) = c \<Longrightarrow> Q"
  shows "Q"
  using H1[THEN basevars] H2 by (force simp: first_def)

lemma base_pair1: 
  assumes h: "basevars (x,y)"
  shows "basevars x"
proof (auto simp: basevars_def)
  fix c
  from h[THEN basevars] obtain s where "(LIFT (x,y)) s = (c, arbitrary)" by auto
  thus "c \<in> range x" by auto
qed

lemma base_pair2: 
  assumes h: "basevars (x,y)"
  shows "basevars y"
proof (auto simp: basevars_def)
  fix d
  from h[THEN basevars] obtain s where "(LIFT (x,y)) s = (arbitrary, d)" by auto
  thus "d \<in> range y" by auto
qed

lemma base_pair: "basevars (x,y) \<Longrightarrow> basevars x \<and> basevars y"
  by (auto elim: base_pair1 base_pair2)

text \<open>
  Since the @{typ unit} type has just one value, any state function of unit type
  satisfies the predicate \<open>basevars\<close>. The following theorem can sometimes
  be useful because it gives a trivial solution for \<open>basevars\<close> premises.
\<close>

lemma unit_base: "basevars (v::state \<Rightarrow> unit)"
  by (auto simp: basevars_def)

text \<open>
  A pair of the form \<open>(x,x)\<close> will generally not satisfy the predicate
  \<open>basevars\<close> -- except for pathological cases such as \<open>x::unit\<close>.
\<close>
lemma
  fixes x :: "state \<Rightarrow> bool"
  assumes h1: "basevars (x,x)"
  shows "False"
proof -
  from h1 have "\<exists>u. (LIFT (x,x)) u = (False,True)" by (rule basevars)
  thus False by auto
qed

lemma
  fixes x :: "state \<Rightarrow> nat"
  assumes h1: "basevars (x,x)"
  shows "False"
proof -
  from h1 have "\<exists>u. (LIFT (x,x)) u = (0,1)" by (rule basevars)
  thus False by auto
qed

text \<open>
  The following theorem reduces the reasoning about the existence of a
  state sequence satisfiyng an enabledness predicate to finding a suitable
  value \<open>c\<close> at the successor state for the base variables of the 
  specification. This rule is intended for reasoning about standard TLA
  specifications, where \<open>Enabled\<close> is applied to actions, not arbitrary
  pre-formulas.
\<close>
lemma base_enabled:
  assumes h1: "basevars vs"
  and h2: "\<And>u. vs (first u) = c \<Longrightarrow> ((first s) ## u) \<Turnstile> F"
  shows "s \<Turnstile> Enabled F"
using h1 proof (rule first_baseE)
  fix t
  assume "vs (first t) = c"
  hence "((first s) ## t) \<Turnstile> F" by (rule h2)
  thus "s \<Turnstile> Enabled F" unfolding enabled_def by blast
qed


subsection "Temporal Quantifiers"

text\<open>
  In \cite{Lamport94}, Lamport gives a stuttering invariant definition
  of quantification over (flexible) variables. It relies on similarity
  of two sequences (as supported in our @{theory TLA.Sequence} theory), and
  equivalence of two sequences up to a variable (the bound variable).
  However, sequence equaivalence up to a variable, requires state
  equaivalence up to a variable. Our state representation above does not
  support this, hence we cannot encode Lamport's definition in our theory.
  Thus, we need to axiomatise quantification over (flexible) variables.
  Note that with a state representation supporting this, our theory should
  allow such an encoding.
\<close>

consts
  EEx        :: "('a statefun \<Rightarrow> temporal) \<Rightarrow> temporal"       (binder "Eex " 10)
  AAll       :: "('a statefun \<Rightarrow> temporal) \<Rightarrow> temporal"       (binder "Aall " 10)

syntax
  "_EEx"     :: "[idts, lift] => lift"                ("(3\<exists>\<exists> _./ _)" [0,10] 10)
  "_AAll"    :: "[idts, lift] => lift"                ("(3\<forall>\<forall> _./ _)" [0,10] 10)
translations
  "_EEx v A"  ==   "Eex v. A"
  "_AAll v A" ==   "Aall v. A"


axiomatization where
     eexI: "\<turnstile> F x \<longrightarrow> (\<exists>\<exists> x. F x)"
and  eexE: "\<lbrakk>s \<Turnstile> (\<exists>\<exists> x. F x) ; basevars vs; (!! x. \<lbrakk> basevars (x,vs); s \<Turnstile> F x \<rbrakk> \<Longrightarrow> s \<Turnstile> G)\<rbrakk>
            \<Longrightarrow> (s \<Turnstile> G)"
and  all_def: "\<turnstile> (\<forall>\<forall> x. F x) = (\<not>(\<exists>\<exists> x. \<not>(F x)))"
and  eexSTUT: "STUTINV F x \<Longrightarrow> STUTINV (\<exists>\<exists> x. F x)"
and  history: "\<turnstile> (I \<and> \<box>[A]_v) = (\<exists>\<exists> h. ($h = ha) \<and> I \<and> \<box>[A \<and> h$=hb]_(h,v))"

lemmas eexI_unl = eexI[unlift_rule] \<comment> \<open>@{text "w \<Turnstile> F x \<Longrightarrow> w \<Turnstile> (\<exists>\<exists> x. F x)"}\<close>

text \<open>
  \<open>tla_defs\<close> can be used to unfold TLA definitions into lowest predicate level.
  This is particularly useful for reasoning about enabledness of formulas.
\<close>
lemmas tla_defs = unch_def before_def after_def first_def second_def suffix_def 
                  tail_def nexts_def app_def angle_actrans_def actrans_def


end
