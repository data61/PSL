(*  Title:      POPLmark/POPLmark.thy
    Author:     Stefan Berghofer, TU Muenchen, 2005
*)

theory POPLmark
imports Basis
begin


section \<open>Formalization of the basic calculus\<close>

text \<open>
\label{sec:basic-calculus}
In this section, we describe the formalization of the basic calculus
without records. As a main result, we prove {\it type safety}, presented
as two separate theorems, namely {\it preservation} and {\it progress}.
\<close>


subsection \<open>Types and Terms\<close>

text \<open>
The types of System \fsub{} are represented by the following datatype:
\<close>

datatype type =
    TVar nat
  | Top
  | Fun type type    (infixr "\<rightarrow>" 200)
  | TyAll type type  ("(3\<forall><:_./ _)" [0, 10] 10)

text \<open>
The subtyping and typing judgements depend on a {\it context} (or environment) @{term \<Gamma>}
containing bindings for term and type variables. A context is a list of bindings,
where the @{term i}th element @{term "\<Gamma>\<langle>i\<rangle>"} corresponds to the variable
with index @{term i}.
\<close>

datatype binding = VarB type | TVarB type
type_synonym env = "binding list"

text \<open>
In contrast to the usual presentation of type systems often found in textbooks, new
elements are added to the left of a context using the \<open>Cons\<close> operator \<open>\<Colon>\<close> for lists.
We write @{term is_TVarB} for the predicate that returns @{term True} when applied to
a type variable binding, function @{term type_ofB} extracts the type contained in a binding,
and @{term "mapB f"} applies @{term f} to the type contained in a binding.
\<close>

primrec is_TVarB :: "binding \<Rightarrow> bool"
where
  "is_TVarB (VarB T) = False"
| "is_TVarB (TVarB T) = True"

primrec type_ofB :: "binding \<Rightarrow> type"
where
  "type_ofB (VarB T) = T"
| "type_ofB (TVarB T) = T"

primrec mapB :: "(type \<Rightarrow> type) \<Rightarrow> binding \<Rightarrow> binding"
where
  "mapB f (VarB T) = VarB (f T)"
| "mapB f (TVarB T) = TVarB (f T)"

text \<open>
The following datatype represents the terms of System \fsub{}:
\<close>

datatype trm =
    Var nat
  | Abs type trm   ("(3\<lambda>:_./ _)" [0, 10] 10)
  | TAbs type trm  ("(3\<lambda><:_./ _)" [0, 10] 10)
  | App trm trm    (infixl "\<bullet>" 200)
  | TApp trm type  (infixl "\<bullet>\<^sub>\<tau>" 200)


subsection \<open>Lifting and Substitution\<close>

text \<open>
One of the central operations of $\lambda$-calculus is {\it substitution}.
In order to avoid that free variables in a term or type get ``captured''
when substituting it for a variable occurring in the scope of a binder,
we have to increment the indices of its free variables during substitution.
This is done by the lifting functions \<open>\<up>\<^sub>\<tau> n k\<close> and \<open>\<up> n k\<close>
for types and terms, respectively, which increment the indices of all free
variables with indices \<open>\<ge> k\<close> by @{term n}. The lifting functions on
types and terms are defined by
\<close>

primrec liftT :: "nat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type" ("\<up>\<^sub>\<tau>")
where
  "\<up>\<^sub>\<tau> n k (TVar i) = (if i < k then TVar i else TVar (i + n))"
| "\<up>\<^sub>\<tau> n k Top = Top"
| "\<up>\<^sub>\<tau> n k (T \<rightarrow> U) = \<up>\<^sub>\<tau> n k T \<rightarrow> \<up>\<^sub>\<tau> n k U"
| "\<up>\<^sub>\<tau> n k (\<forall><:T. U) = (\<forall><:\<up>\<^sub>\<tau> n k T. \<up>\<^sub>\<tau> n (k + 1) U)"

primrec lift :: "nat \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> trm" ("\<up>")
where
  "\<up> n k (Var i) = (if i < k then Var i else Var (i + n))"
| "\<up> n k (\<lambda>:T. t) = (\<lambda>:\<up>\<^sub>\<tau> n k T. \<up> n (k + 1) t)"
| "\<up> n k (\<lambda><:T. t) = (\<lambda><:\<up>\<^sub>\<tau> n k T. \<up> n (k + 1) t)"
| "\<up> n k (s \<bullet> t) = \<up> n k s \<bullet> \<up> n k t"
| "\<up> n k (t \<bullet>\<^sub>\<tau> T) = \<up> n k t \<bullet>\<^sub>\<tau> \<up>\<^sub>\<tau> n k T"

text \<open>
It is useful to also define an ``unlifting'' function \<open>\<down>\<^sub>\<tau> n k\<close> for
decrementing all free variables with indices \<open>\<ge> k\<close> by @{term n}.
Moreover, we need several substitution functions, denoted by
\mbox{\<open>T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>\<close>}, \mbox{\<open>t[k \<mapsto>\<^sub>\<tau> S]\<close>}, and \mbox{\<open>t[k \<mapsto> s]\<close>},
which substitute type variables in types, type variables in terms,
and term variables in terms, respectively. They are defined as follows:
\<close>

primrec substTT :: "type \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type"  ("_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>\<tau>" [300, 0, 0] 300)
where
  "(TVar i)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> =
     (if k < i then TVar (i - 1) else if i = k then \<up>\<^sub>\<tau> k 0 S else TVar i)"
| "Top[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = Top"
| "(T \<rightarrow> U)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> \<rightarrow> U[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>"
| "(\<forall><:T. U)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = (\<forall><:T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>. U[k+1 \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>)"

primrec decT :: "nat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type"  ("\<down>\<^sub>\<tau>")
where
  "\<down>\<^sub>\<tau> 0 k T = T"
| "\<down>\<^sub>\<tau> (Suc n) k T = \<down>\<^sub>\<tau> n k (T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>)"

primrec subst :: "trm \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> trm"  ("_[_ \<mapsto> _]" [300, 0, 0] 300)
where
  "(Var i)[k \<mapsto> s] = (if k < i then Var (i - 1) else if i = k then \<up> k 0 s else Var i)"
| "(t \<bullet> u)[k \<mapsto> s] = t[k \<mapsto> s] \<bullet> u[k \<mapsto> s]"
| "(t \<bullet>\<^sub>\<tau> T)[k \<mapsto> s] = t[k \<mapsto> s] \<bullet>\<^sub>\<tau> \<down>\<^sub>\<tau> 1 k T"
| "(\<lambda>:T. t)[k \<mapsto> s] = (\<lambda>:\<down>\<^sub>\<tau> 1 k T. t[k+1 \<mapsto> s])"
| "(\<lambda><:T. t)[k \<mapsto> s] = (\<lambda><:\<down>\<^sub>\<tau> 1 k T. t[k+1 \<mapsto> s])"

primrec substT :: "trm \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> trm"    ("_[_ \<mapsto>\<^sub>\<tau> _]" [300, 0, 0] 300)
where
  "(Var i)[k \<mapsto>\<^sub>\<tau> S] = (if k < i then Var (i - 1) else Var i)"
| "(t \<bullet> u)[k \<mapsto>\<^sub>\<tau> S] = t[k \<mapsto>\<^sub>\<tau> S] \<bullet> u[k \<mapsto>\<^sub>\<tau> S]"
| "(t \<bullet>\<^sub>\<tau> T)[k \<mapsto>\<^sub>\<tau> S] = t[k \<mapsto>\<^sub>\<tau> S] \<bullet>\<^sub>\<tau> T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>"
| "(\<lambda>:T. t)[k \<mapsto>\<^sub>\<tau> S] = (\<lambda>:T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>. t[k+1 \<mapsto>\<^sub>\<tau> S])"
| "(\<lambda><:T. t)[k \<mapsto>\<^sub>\<tau> S] = (\<lambda><:T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>. t[k+1 \<mapsto>\<^sub>\<tau> S])"

text \<open>
Lifting and substitution extends to typing contexts as follows:
\<close>

primrec liftE :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> env" ("\<up>\<^sub>e")
where
  "\<up>\<^sub>e n k [] = []"
| "\<up>\<^sub>e n k (B \<Colon> \<Gamma>) = mapB (\<up>\<^sub>\<tau> n (k + \<parallel>\<Gamma>\<parallel>)) B \<Colon> \<up>\<^sub>e n k \<Gamma>"

primrec substE :: "env \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> env"  ("_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>e" [300, 0, 0] 300)
where
  "[][k \<mapsto>\<^sub>\<tau> T]\<^sub>e = []"
| "(B \<Colon> \<Gamma>)[k \<mapsto>\<^sub>\<tau> T]\<^sub>e = mapB (\<lambda>U. U[k + \<parallel>\<Gamma>\<parallel> \<mapsto>\<^sub>\<tau> T]\<^sub>\<tau>) B \<Colon> \<Gamma>[k \<mapsto>\<^sub>\<tau> T]\<^sub>e"

primrec decE :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> env"  ("\<down>\<^sub>e")
where
  "\<down>\<^sub>e 0 k \<Gamma> = \<Gamma>"
| "\<down>\<^sub>e (Suc n) k \<Gamma> = \<down>\<^sub>e n k (\<Gamma>[k \<mapsto>\<^sub>\<tau> Top]\<^sub>e)"

text \<open>
Note that in a context of the form @{term "B \<Colon> \<Gamma>"}, all variables in @{term B} with
indices smaller than the length of @{term \<Gamma>} refer to entries in @{term \<Gamma>} and therefore
must not be affected by substitution and lifting. This is the reason why an
additional offset @{term "\<parallel>\<Gamma>\<parallel>"} needs to be added to the index @{term k}
in the second clauses of the above functions. Some standard properties of lifting
and substitution, which can be proved by structural induction on terms and types,
are proved below. Properties of this kind are
quite standard for encodings using de Bruijn indices and can also be found in
papers by Barras and Werner \cite{Barras-Werner-JAR} and Nipkow \cite{Nipkow-JAR01}.
\<close>

lemma liftE_length [simp]: "\<parallel>\<up>\<^sub>e n k \<Gamma>\<parallel> = \<parallel>\<Gamma>\<parallel>"
  by (induct \<Gamma>) simp_all

lemma substE_length [simp]: "\<parallel>\<Gamma>[k \<mapsto>\<^sub>\<tau> U]\<^sub>e\<parallel> = \<parallel>\<Gamma>\<parallel>"
  by (induct \<Gamma>) simp_all

lemma liftE_nth [simp]:
  "(\<up>\<^sub>e n k \<Gamma>)\<langle>i\<rangle> = map_option (mapB (\<up>\<^sub>\<tau> n (k + \<parallel>\<Gamma>\<parallel> - i - 1))) (\<Gamma>\<langle>i\<rangle>)"
  apply (induct \<Gamma> arbitrary: i)
  apply simp
  apply simp
  apply (case_tac i)
  apply simp
  apply simp
  done

lemma substE_nth [simp]:
  "(\<Gamma>[0 \<mapsto>\<^sub>\<tau> T]\<^sub>e)\<langle>i\<rangle> = map_option (mapB (\<lambda>U. U[\<parallel>\<Gamma>\<parallel> - i - 1 \<mapsto>\<^sub>\<tau> T]\<^sub>\<tau>)) (\<Gamma>\<langle>i\<rangle>)"
  apply (induct \<Gamma> arbitrary: i)
  apply simp
  apply simp
  apply (case_tac i)
  apply simp
  apply simp
  done

lemma liftT_liftT [simp]:
  "i \<le> j \<Longrightarrow> j \<le> i + m \<Longrightarrow> \<up>\<^sub>\<tau> n j (\<up>\<^sub>\<tau> m i T) = \<up>\<^sub>\<tau> (m + n) i T"
  by (induct T arbitrary: i j m n) simp_all

lemma liftT_liftT' [simp]:
  "i + m \<le> j \<Longrightarrow> \<up>\<^sub>\<tau> n j (\<up>\<^sub>\<tau> m i T) = \<up>\<^sub>\<tau> m i (\<up>\<^sub>\<tau> n (j - m) T)"
  apply (induct T arbitrary: i j m n)
  apply simp_all
  apply arith
  apply (subgoal_tac "Suc j - m = Suc (j - m)")
  apply simp
  apply arith
  done

lemma lift_size [simp]: "size (\<up>\<^sub>\<tau> n k T) = size T"
  by (induct T arbitrary: k) simp_all

lemma liftT0 [simp]: "\<up>\<^sub>\<tau> 0 i T = T"
  by (induct T arbitrary: i) simp_all

lemma lift0 [simp]: "\<up> 0 i t = t"
  by (induct t arbitrary: i) simp_all

theorem substT_liftT [simp]:
  "k \<le> k' \<Longrightarrow> k' < k + n \<Longrightarrow> (\<up>\<^sub>\<tau> n k T)[k' \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau> = \<up>\<^sub>\<tau> (n - 1) k T"
  by (induct T arbitrary: k k') simp_all

theorem liftT_substT [simp]:
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>\<tau> n k (T[k' \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>) = \<up>\<^sub>\<tau> n k T[k' + n \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
  apply (induct T arbitrary: k k')
  apply simp_all
  done

theorem liftT_substT' [simp]: "k' < k \<Longrightarrow>
  \<up>\<^sub>\<tau> n k (T[k' \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>) = \<up>\<^sub>\<tau> n (k + 1) T[k' \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n (k - k') U]\<^sub>\<tau>"
  apply (induct T arbitrary: k k')
  apply simp_all
  apply arith
  done

lemma liftT_substT_Top [simp]:
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>\<tau> n k' (T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>) = \<up>\<^sub>\<tau> n (Suc k') T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
  apply (induct T arbitrary: k k')
  apply simp_all
  apply arith
  done

lemma liftT_substT_strange:
  "\<up>\<^sub>\<tau> n k T[n + k \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau> = \<up>\<^sub>\<tau> n (Suc k) T[k \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n 0 U]\<^sub>\<tau>"
  apply (induct T arbitrary: n k)
  apply simp_all
  apply (thin_tac "\<And>x. PROP P x" for P :: "_ \<Rightarrow> prop")
  apply (drule_tac x=n in meta_spec)
  apply (drule_tac x="Suc k" in meta_spec)
  apply simp
  done

lemma lift_lift [simp]:
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up> n' k' (\<up> n k t) = \<up> (n + n') k t"
  by (induct t arbitrary: k k') simp_all

lemma substT_substT:
  "i \<le> j \<Longrightarrow> T[Suc j \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>[i \<mapsto>\<^sub>\<tau> U[j - i \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>]\<^sub>\<tau> = T[i \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>[j \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>"
  apply (induct T arbitrary: i j U V)
  apply (simp_all add: diff_Suc split: nat.split)
  apply (thin_tac "\<And>x. PROP P x" for P :: "_ \<Rightarrow> prop")
  apply (drule_tac x="Suc i" in meta_spec)
  apply (drule_tac x="Suc j" in meta_spec)
  apply simp
  done


subsection \<open>Well-formedness\<close>

text \<open>
\label{sec:wf}
The subtyping and typing judgements to be defined in \secref{sec:subtyping}
and \secref{sec:typing} may only operate on types and contexts that
are well-formed. Intuitively, a type @{term T} is well-formed with respect to a
context @{term \<Gamma>}, if all variables occurring in it are defined in @{term \<Gamma>}.
More precisely, if @{term T} contains a type variable @{term "TVar i"}, then
the @{term i}th element of @{term \<Gamma>} must exist and have the form @{term "TVarB U"}.
\<close>

inductive
  well_formed :: "env \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile>\<^sub>w\<^sub>f _" [50, 50] 50)
where
  wf_TVar: "\<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f TVar i"
| wf_Top: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f Top"
| wf_arrow: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<rightarrow> U"
| wf_all: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> TVarB T \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f (\<forall><:T. U)"

text \<open>
A context @{term "\<Gamma>"} is well-formed, if all types occurring in it only refer to type variables
declared ``further to the right'':
\<close>

inductive
  well_formedE :: "env \<Rightarrow> bool"  ("_ \<turnstile>\<^sub>w\<^sub>f" [50] 50)
  and well_formedB :: "env \<Rightarrow> binding \<Rightarrow> bool"  ("_ \<turnstile>\<^sub>w\<^sub>f\<^sub>B _" [50, 50] 50)
where
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<equiv> \<Gamma> \<turnstile>\<^sub>w\<^sub>f type_ofB B"
| wf_Nil: "[] \<turnstile>\<^sub>w\<^sub>f"
| wf_Cons: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"

text \<open>
The judgement \<open>\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B\<close>, which denotes well-formedness of the binding @{term B}
with respect to context @{term \<Gamma>}, is just an abbreviation for \<open>\<Gamma> \<turnstile>\<^sub>w\<^sub>f type_ofB B\<close>.
We now present a number of properties of the well-formedness judgements that will be used
in the proofs in the following sections.
\<close>

inductive_cases well_formed_cases:
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f TVar i"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f Top"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<rightarrow> U"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f (\<forall><:T. U)"

inductive_cases well_formedE_cases:
  "B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"

lemma wf_TVarB: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> TVarB T \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  by (rule wf_Cons) simp_all

lemma wf_VarB: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> VarB T \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  by (rule wf_Cons) simp_all

lemma map_is_TVarb:
  "map is_TVarB \<Gamma>' = map is_TVarB \<Gamma> \<Longrightarrow>
    \<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor> \<Longrightarrow> \<exists>T. \<Gamma>'\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor>"
  apply (induct \<Gamma> arbitrary: \<Gamma>' T i)
  apply simp
  apply (auto split: nat.split_asm)
  apply (case_tac z)
  apply simp_all
  done

text \<open>
A type that is well-formed in a context @{term \<Gamma>} is also well-formed in another context
@{term \<Gamma>'} that contains type variable bindings at the same positions as @{term \<Gamma>}:
\<close>

lemma wf_equallength:
  assumes H: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T"
  shows "map is_TVarB \<Gamma>' = map is_TVarB \<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>w\<^sub>f T" using H
  by (induct arbitrary: \<Gamma>') (auto intro: well_formed.intros dest: map_is_TVarb)

text \<open>
A well-formed context of the form @{term "\<Delta> @ B \<Colon> \<Gamma>"} remains well-formed if we replace
the binding @{term B} by another well-formed binding @{term B'}:
\<close>

lemma wfE_replace:
  "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B' \<Longrightarrow> is_TVarB B' = is_TVarB B \<Longrightarrow>
    \<Delta> @ B' \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  apply (induct \<Delta>)
  apply simp
  apply (erule wf_Cons)
  apply (erule well_formedE_cases)
  apply assumption
  apply simp
  apply (erule well_formedE_cases)
  apply (rule wf_Cons)
  apply (case_tac a)
  apply simp
  apply (rule wf_equallength)
  apply assumption
  apply simp
  apply simp
  apply (rule wf_equallength)
  apply assumption
  apply simp
  apply simp
  done

text \<open>
The following weakening lemmas can easily be proved by structural induction on
types and contexts:
\<close>

lemma wf_weaken:
  assumes H: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f T"
  shows "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T"
  using H
  apply (induct "\<Delta> @ \<Gamma>" T arbitrary: \<Delta>)
  apply simp_all
  apply (rule conjI)
  apply (rule impI)
  apply (rule wf_TVar)
  apply simp
  apply (rule impI)
  apply (rule wf_TVar)
  apply (subgoal_tac "Suc i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel>)")
  apply simp
  apply arith
  apply (rule wf_Top)
  apply (rule wf_arrow)
  apply simp
  apply simp
  apply (rule wf_all)
  apply simp
  apply (drule_tac x="TVarB T \<Colon> \<Delta>" in meta_spec)
  apply simp
  done

lemma wf_weaken': "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T"
  apply (induct \<Delta>)
  apply simp_all
  apply (drule_tac B=a in wf_weaken [of "[]", simplified])
  apply simp
  done

lemma wfE_weaken: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<Longrightarrow> \<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  apply (induct \<Delta>)
  apply simp
  apply (rule wf_Cons)
  apply assumption+
  apply simp
  apply (rule wf_Cons)
  apply (erule well_formedE_cases)
  apply (case_tac a)
  apply simp
  apply (rule wf_weaken)
  apply assumption
  apply simp
  apply (rule wf_weaken)
  apply assumption
  apply (erule well_formedE_cases)
  apply simp
  done

text \<open>
Intuitively, lemma \<open>wf_weaken\<close> states that a type @{term T} which is well-formed
in a context is still well-formed in a larger context, whereas lemma \<open>wfE_weaken\<close>
states that a well-formed context remains well-formed when extended with a
well-formed binding. Owing to the encoding of variables using de Bruijn
indices, the statements of the above lemmas involve additional lifting functions.
The typing judgement, which will be described in \secref{sec:typing}, involves
the lookup of variables in a context. It has already been pointed out earlier that each
entry in a context may only depend on types declared ``further to the right''. To ensure that
a type @{term T} stored at position @{term i} in an environment @{term \<Gamma>} is valid in the full
environment, as opposed to the smaller environment consisting only of the entries in
@{term \<Gamma>} at positions greater than @{term i}, we need to increment the indices of all
free type variables in @{term T} by @{term "Suc i"}:
\<close>

lemma wf_liftB:
  assumes H: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  shows "\<Gamma>\<langle>i\<rangle> = \<lfloor>VarB T\<rfloor> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> (Suc i) 0 T"
  using H
  apply (induct arbitrary: i)
  apply simp
  apply (simp split: nat.split_asm)
  apply (frule_tac B="VarB T" in wf_weaken [of "[]", simplified])
  apply simp+
  apply (rename_tac nat)
  apply (drule_tac x=nat in meta_spec)
  apply simp
  apply (frule_tac T="\<up>\<^sub>\<tau> (Suc nat) 0 T" in wf_weaken [of "[]", simplified])
  apply simp
  done

text \<open>
We also need lemmas stating that substitution of well-formed types preserves the well-formedness
of types and contexts:
\<close>

theorem wf_subst:
  "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
  apply (induct T arbitrary: \<Delta>)
  apply simp_all
  apply (rule conjI)
  apply (rule impI)
  apply (drule_tac \<Gamma>=\<Gamma> and \<Delta>="\<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e" in wf_weaken')
  apply simp
  apply (rule impI conjI)+
  apply (erule well_formed_cases)
  apply (rule wf_TVar)
  apply (simp split: nat.split_asm)
  apply (rename_tac nat \<Delta> T nata)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> nat - Suc 0")
  apply (subgoal_tac "nat - Suc \<parallel>\<Delta>\<parallel> = nata")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply (rule impI)
  apply (erule well_formed_cases)
  apply (rule wf_TVar)
  apply simp
  apply (rule wf_Top)
  apply (erule well_formed_cases)
  apply (rule wf_arrow)
  apply simp+
  apply (erule well_formed_cases)
  apply (rule wf_all)
  apply simp
  apply (thin_tac "\<And>x. PROP P x" for P :: "_ \<Rightarrow> prop")
  apply (drule_tac x="TVarB T1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  done

theorem wfE_subst: "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  apply (induct \<Delta>)
  apply simp
  apply (erule well_formedE_cases)
  apply assumption
  apply simp
  apply (case_tac a)
  apply (erule well_formedE_cases)
  apply (rule wf_Cons)
  apply simp
  apply (rule wf_subst)
  apply assumption+
  apply simp
  apply (erule well_formedE_cases)
  apply (rule wf_Cons)
  apply simp
  apply (rule wf_subst)
  apply assumption+
  done


subsection \<open>Subtyping\<close>

text \<open>
\label{sec:subtyping}
We now come to the definition of the subtyping judgement \<open>\<Gamma> \<turnstile> T <: U\<close>.
\<close>

inductive
  subtyping :: "env \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile> _ <: _" [50, 50, 50] 50)
where
  SA_Top: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f S \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
| SA_refl_TVar: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f TVar i \<Longrightarrow> \<Gamma> \<turnstile> TVar i <: TVar i"
| SA_trans_TVar: "\<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB U\<rfloor> \<Longrightarrow>
    \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc i) 0 U <: T \<Longrightarrow> \<Gamma> \<turnstile> TVar i <: T"
| SA_arrow: "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1 \<rightarrow> T\<^sub>2"
| SA_all: "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> TVarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow>
    \<Gamma> \<turnstile> (\<forall><:S\<^sub>1. S\<^sub>2) <: (\<forall><:T\<^sub>1. T\<^sub>2)"

text \<open>
The rules \<open>SA_Top\<close> and \<open>SA_refl_TVar\<close>, which appear at the leaves of
the derivation tree for a judgement @{term "\<Gamma> \<turnstile> T <: U"}, contain additional
side conditions ensuring the well-formedness of the contexts and types involved.
In order for the rule \<open>SA_trans_TVar\<close> to be applicable, the context @{term \<Gamma>}
must be of the form \mbox{@{term "\<Gamma>\<^sub>1 @ B \<Colon> \<Gamma>\<^sub>2"}}, where @{term "\<Gamma>\<^sub>1"} has the length @{term i}.
Since the indices of variables in @{term B} can only refer to variables defined in
@{term "\<Gamma>\<^sub>2"}, they have to be incremented by @{term "Suc i"} to ensure that they point
to the right variables in the larger context \<open>\<Gamma>\<close>.
\<close>

lemma wf_subtype_env:
  assumes PQ: "\<Gamma> \<turnstile> P <: Q"
  shows "\<Gamma> \<turnstile>\<^sub>w\<^sub>f" using PQ
  by induct assumption+

lemma wf_subtype:
  assumes PQ: "\<Gamma> \<turnstile> P <: Q"
  shows "\<Gamma> \<turnstile>\<^sub>w\<^sub>f P \<and> \<Gamma> \<turnstile>\<^sub>w\<^sub>f Q" using PQ
  by induct (auto intro: well_formed.intros elim!: wf_equallength)

lemma wf_subtypeE:
  assumes H: "\<Gamma> \<turnstile> T <: U"
  and H': "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> P"
  shows "P"
  apply (rule H')
  apply (rule wf_subtype_env)
  apply (rule H)
  apply (rule wf_subtype [OF H, THEN conjunct1])
  apply (rule wf_subtype [OF H, THEN conjunct2])
  done

text \<open>
By induction on the derivation of @{term "\<Gamma> \<turnstile> T <: U"}, it can easily be shown
that all types and contexts occurring in a subtyping judgement must be well-formed:
\<close>

lemma wf_subtype_conj:
  "\<Gamma> \<turnstile> T <: U \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<and> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<and> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U"
  by (erule wf_subtypeE) iprover

text \<open>
By induction on types, we can prove that the subtyping relation is reflexive:
\<close>

lemma subtype_refl: \<comment> \<open>A.1\<close>
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile> T <: T"
  by (induct T arbitrary: \<Gamma>) (blast intro:
    subtyping.intros wf_Nil wf_TVarB elim: well_formed_cases)+

text \<open>
The weakening lemma for the subtyping relation is proved in two steps:
by induction on the derivation of the subtyping relation, we first prove
that inserting a single type into the context preserves subtyping:
\<close>

lemma subtype_weaken:
  assumes H: "\<Delta> @ \<Gamma> \<turnstile> P <: Q"
  and wf: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B"
  shows "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> P <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> Q" using H
proof (induct "\<Delta> @ \<Gamma>" P Q arbitrary: \<Delta>)
  case SA_Top
  with wf show ?case
    by (auto intro: subtyping.SA_Top wfE_weaken wf_weaken)
next
  case SA_refl_TVar
  with wf show ?case
    by (auto intro!: subtyping.SA_refl_TVar wfE_weaken dest: wf_weaken)
next
  case (SA_trans_TVar i U T)
  thus ?case
  proof (cases "i < \<parallel>\<Delta>\<parallel>")
    case True
    with SA_trans_TVar
    have "(\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma>)\<langle>i\<rangle> = \<lfloor>TVarB (\<up>\<^sub>\<tau> 1 (\<parallel>\<Delta>\<parallel> - Suc i) U)\<rfloor>"
      by simp
    moreover from True SA_trans_TVar
    have "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>
      \<up>\<^sub>\<tau> (Suc i) 0 (\<up>\<^sub>\<tau> 1 (\<parallel>\<Delta>\<parallel> - Suc i) U) <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by simp
    ultimately have "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> TVar i <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by (rule subtyping.SA_trans_TVar)
    with True show ?thesis by simp
  next
    case False
    then have "Suc i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel>)" by arith
    with False SA_trans_TVar have "(\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma>)\<langle>Suc i\<rangle> = \<lfloor>TVarB U\<rfloor>"
      by simp
    moreover from False SA_trans_TVar
    have "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc (Suc i)) 0 U <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by simp
    ultimately have "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> TVar (Suc i) <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by (rule subtyping.SA_trans_TVar)
    with False show ?thesis by simp
  qed
next
  case SA_arrow
  thus ?case by simp (iprover intro: subtyping.SA_arrow)
next
  case (SA_all T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2 \<Delta>)
  with SA_all(4) [of "TVarB T\<^sub>1 \<Colon> \<Delta>"]
  show ?case by simp (iprover intro: subtyping.SA_all)
qed

text \<open>
All cases are trivial, except for the \<open>SA_trans_TVar\<close> case, which
requires a case distinction on whether the index of the variable is smaller
than @{term "\<parallel>\<Delta>\<parallel>"}.
The stronger result that appending a new context @{term \<Delta>} to a context
@{term \<Gamma>} preserves subtyping can be proved by induction on @{term \<Delta>},
using the previous result in the induction step:
\<close>

lemma subtype_weaken': \<comment> \<open>A.2\<close>
  "\<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 P <: \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 Q"
  apply (induct \<Delta>)
  apply simp_all
  apply (erule well_formedE_cases)
  apply simp
  apply (drule_tac B="a" and \<Gamma>="\<Delta> @ \<Gamma>" in subtype_weaken [of "[]", simplified])
  apply simp_all
  done

text \<open>
An unrestricted transitivity rule has the disadvantage that it can
be applied in any situation. In order to make the above definition of the
subtyping relation {\it syntax-directed}, the transitivity rule \<open>SA_trans_TVar\<close>
is restricted to the case where the type on the left-hand side of the \<open><:\<close>
operator is a variable. However, the unrestricted transitivity rule
can be derived from this definition.
In order for the proof to go through, we have to simultaneously prove
another property called {\it narrowing}.
The two properties are proved by nested induction. The outer induction
is on the size of the type @{term Q}, whereas the two inner inductions for
proving transitivity and narrowing are on the derivation of the
subtyping judgements. The transitivity property is needed in the proof of
narrowing, which is by induction on the derivation of \mbox{@{term "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> M <: N"}}.
In the case corresponding to the rule \<open>SA_trans_TVar\<close>, we must prove
\mbox{@{term "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> TVar i <: T"}}. The only interesting case
is the one where @{term "i = \<parallel>\<Delta>\<parallel>"}. By induction hypothesis, we know that
@{term "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (i+1) 0 Q <: T"} and
@{term "(\<Delta> @ TVarB Q \<Colon> \<Gamma>)\<langle>i\<rangle> = \<lfloor>TVarB Q\<rfloor>"}.
By assumption, we have @{term "\<Gamma> \<turnstile> P <: Q"} and hence 
\mbox{@{term "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (i+1) 0 P <: \<up>\<^sub>\<tau> (i+1) 0 Q"}} by weakening.
Since @{term "\<up>\<^sub>\<tau> (i+1) 0 Q"} has the same size as @{term Q}, we can use
the transitivity property, which yields
@{term "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (i+1) 0 P <: T"}. The claim then follows
easily by an application of \<open>SA_trans_TVar\<close>.
\<close>

lemma subtype_trans: \<comment> \<open>A.3\<close>
  "\<Gamma> \<turnstile> S <: Q \<Longrightarrow> \<Gamma> \<turnstile> Q <: T \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
  "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> M <: N \<Longrightarrow> \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
     \<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> M <: N"
  using wf_measure_size
proof (induct Q arbitrary: \<Gamma> S T \<Delta> P M N rule: wf_induct_rule)
  case (less Q)
  {
    fix \<Gamma> S T Q'
    assume "\<Gamma> \<turnstile> S <: Q'"
    then have "\<Gamma> \<turnstile> Q' <: T \<Longrightarrow> size Q = size Q' \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
    proof (induct arbitrary: T)
      case SA_Top
      from SA_Top(3) show ?case
        by cases (auto intro: subtyping.SA_Top SA_Top)
    next
      case SA_refl_TVar show ?case by fact
    next
      case SA_trans_TVar
      thus ?case by (auto intro: subtyping.SA_trans_TVar)
    next
      case (SA_arrow \<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
      note SA_arrow' = SA_arrow
      from SA_arrow(5) show ?case
      proof cases
        case SA_Top
        with SA_arrow show ?thesis
          by (auto intro: subtyping.SA_Top wf_arrow elim: wf_subtypeE)
      next
        case (SA_arrow T\<^sub>1' T\<^sub>2')
        from SA_arrow SA_arrow' have "\<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1' \<rightarrow> T\<^sub>2'"
          by (auto intro!: subtyping.SA_arrow intro: less(1) [of "T\<^sub>1"] less(1) [of "T\<^sub>2"])
        with SA_arrow show ?thesis by simp
      qed
    next
      case (SA_all \<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
      note SA_all' = SA_all
      from SA_all(5) show ?case
      proof cases
        case SA_Top
        with SA_all show ?thesis by (auto intro!:
          subtyping.SA_Top wf_all intro: wf_equallength elim: wf_subtypeE)
      next
        case (SA_all T\<^sub>1' T\<^sub>2')
        from SA_all SA_all' have "\<Gamma> \<turnstile> T\<^sub>1' <: S\<^sub>1"
          by - (rule less(1), simp_all)
        moreover from SA_all SA_all' have "TVarB T\<^sub>1' \<Colon> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2"
          by - (rule less(2) [of _ "[]", simplified], simp_all)
        with SA_all SA_all' have "TVarB T\<^sub>1' \<Colon> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2'"
          by - (rule less(1), simp_all)
        ultimately have "\<Gamma> \<turnstile> (\<forall><:S\<^sub>1. S\<^sub>2) <: (\<forall><:T\<^sub>1'. T\<^sub>2')"
          by (rule subtyping.SA_all)
        with SA_all show ?thesis by simp
      qed
    qed
  }
  note tr = this
  {
    case 1
    thus ?case using refl by (rule tr)
  next
    case 2
    from 2(1) show "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> M <: N"
    proof (induct "\<Delta> @ TVarB Q \<Colon> \<Gamma>" M N arbitrary: \<Delta>)
      case SA_Top
      with 2 show ?case by (auto intro!: subtyping.SA_Top
        intro: wf_equallength wfE_replace elim!: wf_subtypeE)
    next
      case SA_refl_TVar
      with 2 show ?case by (auto intro!: subtyping.SA_refl_TVar
        intro: wf_equallength wfE_replace elim!: wf_subtypeE)
    next
      case (SA_trans_TVar i U T)
      show ?case
      proof (cases "i < \<parallel>\<Delta>\<parallel>")
        case True
        with SA_trans_TVar show ?thesis
          by (auto intro!: subtyping.SA_trans_TVar)
      next
        case False
        note False' = False
        show ?thesis
        proof (cases "i = \<parallel>\<Delta>\<parallel>")
          case True
          from SA_trans_TVar have "(\<Delta> @ [TVarB P]) @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
            by (auto elim!: wf_subtypeE)
          with \<open>\<Gamma> \<turnstile> P <: Q\<close>
          have "(\<Delta> @ [TVarB P]) @ \<Gamma> \<turnstile> \<up>\<^sub>\<tau> \<parallel>\<Delta> @ [TVarB P]\<parallel> 0 P <: \<up>\<^sub>\<tau> \<parallel>\<Delta> @ [TVarB P]\<parallel> 0 Q"
            by (rule subtype_weaken')
          with SA_trans_TVar True False have "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc \<parallel>\<Delta>\<parallel>) 0 P <: T"
            by - (rule tr, simp+)
          with True and False and SA_trans_TVar show ?thesis
            by (auto intro!: subtyping.SA_trans_TVar)
        next
          case False
          with False' have "i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel> - 1)" by arith
          with False False' SA_trans_TVar show ?thesis
            by - (rule subtyping.SA_trans_TVar, simp+)
        qed
      qed
    next
      case SA_arrow
      thus ?case by (auto intro!: subtyping.SA_arrow)
    next
      case (SA_all T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
      thus ?case by (auto intro: subtyping.SA_all
        SA_all(4) [of "TVarB T\<^sub>1 \<Colon> \<Delta>", simplified])
    qed
  }
qed

text \<open>
In the proof of the preservation theorem presented in \secref{sec:evaluation},
we will also need a substitution theorem, which is proved by
induction on the subtyping derivation:
\<close>

lemma substT_subtype: \<comment> \<open>A.10\<close>
  assumes H: "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> S <: T"
  shows "\<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> S[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau> <: T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>"
  using H
  apply (induct "\<Delta> @ TVarB Q \<Colon> \<Gamma>" S T arbitrary: \<Delta>)
  apply simp_all
  apply (rule SA_Top)
  apply (rule wfE_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (rule wf_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (rule impI conjI)+
  apply (rule subtype_refl)
  apply (rule wfE_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (erule wf_subtypeE)
  apply (drule_tac T=P and \<Delta>="\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e" in wf_weaken')
  apply simp
  apply (rule conjI impI)+
  apply (rule SA_refl_TVar)
  apply (rule wfE_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (erule wf_subtypeE)
  apply (drule wf_subst)
  apply assumption
  apply simp
  apply (rule impI)
  apply (rule SA_refl_TVar)
  apply (rule wfE_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (erule wf_subtypeE)
  apply (drule wf_subst)
  apply assumption
  apply simp
  apply (rule conjI impI)+
  apply simp
  apply (drule_tac \<Gamma>=\<Gamma> and \<Delta>="\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e" in subtype_weaken')
  apply (erule wf_subtypeE)+
  apply assumption
  apply simp
  apply (rule subtype_trans(1))
  apply assumption+
  apply (rule conjI impI)+
  apply (rule SA_trans_TVar)
  apply (simp split: nat.split_asm)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> i - Suc 0")
  apply (rename_tac nat)
  apply (subgoal_tac "i - Suc \<parallel>\<Delta>\<parallel> = nat")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply simp
  apply (rule impI)
  apply (rule SA_trans_TVar)
  apply (simp split: nat.split_asm)
  apply (subgoal_tac "Suc (\<parallel>\<Delta>\<parallel> - Suc 0) = \<parallel>\<Delta>\<parallel>")
  apply (simp (no_asm_simp))
  apply arith
  apply (rule SA_arrow)
  apply simp+
  apply (rule SA_all)
  apply simp
  apply (drule_tac x="TVarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  done

lemma subst_subtype:
  assumes H: "\<Delta> @ VarB V \<Colon> \<Gamma> \<turnstile> T <: U"
  shows "\<down>\<^sub>e 1 0 \<Delta> @ \<Gamma> \<turnstile> \<down>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T <: \<down>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> U"
  using H
  apply (induct "\<Delta> @ VarB V \<Colon> \<Gamma>" T U arbitrary: \<Delta>)
  apply simp_all
  apply (rule SA_Top)
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)
  apply (rule wf_subst)
  apply assumption
  apply (rule wf_Top)
  apply (rule impI conjI)+
  apply (rule SA_Top)
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)+
  apply (rule conjI impI)+
  apply (rule SA_refl_TVar)
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)
  apply (drule wf_subst)
  apply (rule wf_Top)
  apply simp
  apply (rule impI)
  apply (rule SA_refl_TVar)
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)
  apply (drule wf_subst)
  apply (rule wf_Top)
  apply simp
  apply (rule conjI impI)+
  apply simp
  apply (rule conjI impI)+
  apply (simp split: nat.split_asm)
  apply (rule SA_trans_TVar)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> i - Suc 0")
  apply (rename_tac nat)
  apply (subgoal_tac "i - Suc \<parallel>\<Delta>\<parallel> = nat")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply simp
  apply (rule impI)
  apply (rule SA_trans_TVar)
  apply simp
  apply (subgoal_tac "0 < \<parallel>\<Delta>\<parallel>")
  apply simp
  apply arith
  apply (rule SA_arrow)
  apply simp+
  apply (rule SA_all)
  apply simp
  apply (drule_tac x="TVarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  done


subsection \<open>Typing\<close>

text \<open>
\label{sec:typing}
We are now ready to give a definition of the typing judgement \<open>\<Gamma> \<turnstile> t : T\<close>.
\<close>

inductive
  typing :: "env \<Rightarrow> trm \<Rightarrow> type \<Rightarrow> bool"    ("_ \<turnstile> _ : _" [50, 50, 50] 50)
where
  T_Var: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma>\<langle>i\<rangle> = \<lfloor>VarB U\<rfloor> \<Longrightarrow> T = \<up>\<^sub>\<tau> (Suc i) 0 U \<Longrightarrow> \<Gamma> \<turnstile> Var i : T"
| T_Abs: "VarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda>:T\<^sub>1. t\<^sub>2) : T\<^sub>1 \<rightarrow> \<down>\<^sub>\<tau> 1 0 T\<^sub>2"
| T_App: "\<Gamma> \<turnstile> t\<^sub>1 : T\<^sub>1\<^sub>1 \<rightarrow> T\<^sub>1\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> t\<^sub>1 \<bullet> t\<^sub>2 : T\<^sub>1\<^sub>2"
| T_TAbs: "TVarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda><:T\<^sub>1. t\<^sub>2) : (\<forall><:T\<^sub>1. T\<^sub>2)"
| T_TApp: "\<Gamma> \<turnstile> t\<^sub>1 : (\<forall><:T\<^sub>1\<^sub>1. T\<^sub>1\<^sub>2) \<Longrightarrow> \<Gamma> \<turnstile> T\<^sub>2 <: T\<^sub>1\<^sub>1 \<Longrightarrow>
    \<Gamma> \<turnstile> t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 : T\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]\<^sub>\<tau>"
| T_Sub: "\<Gamma> \<turnstile> t : S \<Longrightarrow> \<Gamma> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<turnstile> t : T"

text \<open>
Note that in the rule \<open>T_Var\<close>, the indices of the type @{term U} looked up in
the context @{term \<Gamma>} need to be incremented in order for the type to be well-formed
with respect to @{term \<Gamma>}. In the rule \<open>T_Abs\<close>, the type @{term "T\<^sub>2"} of the
abstraction body @{term "t\<^sub>2"} may not contain the variable with index \<open>0\<close>,
since it is a term variable. To compensate for the disappearance of the context
element @{term "VarB T\<^sub>1"} in the conclusion of thy typing rule, the indices of all
free type variables in @{term "T\<^sub>2"} have to be decremented by \<open>1\<close>.
\<close>

theorem wf_typeE1:
  assumes H: "\<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile>\<^sub>w\<^sub>f" using H
  by induct (blast elim: well_formedE_cases)+

theorem wf_typeE2:
  assumes H: "\<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T" using H
  apply induct
  apply simp
  apply (rule wf_liftB)
  apply assumption+
  apply (drule wf_typeE1)+
  apply (erule well_formedE_cases)+
  apply (rule wf_arrow)
  apply simp
  apply simp
  apply (rule wf_subst [of "[]", simplified])
  apply assumption
  apply (rule wf_Top)
  apply (erule well_formed_cases)
  apply assumption
  apply (rule wf_all)
  apply (drule wf_typeE1)
  apply (erule well_formedE_cases)
  apply simp  
  apply assumption
  apply (erule well_formed_cases)
  apply (rule wf_subst [of "[]", simplified])
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  done

text \<open>
Like for the subtyping judgement, we can again prove that all types and contexts
involved in a typing judgement are well-formed:
\<close>
lemma wf_type_conj: "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<and> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T"
  by (frule wf_typeE1, drule wf_typeE2) iprover

text \<open>
The narrowing theorem for the typing judgement states that replacing the type
of a variable in the context by a subtype preserves typability:
\<close>

lemma narrow_type: \<comment> \<open>A.7\<close>
  assumes H: "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> t : T"
  using H
  apply (induct "\<Delta> @ TVarB Q \<Colon> \<Gamma>" t T arbitrary: \<Delta>)
  apply simp_all
  apply (rule T_Var)
  apply (erule wfE_replace)
  apply (erule wf_subtypeE)
  apply simp+
  apply (case_tac "i < \<parallel>\<Delta>\<parallel>")
  apply simp
  apply (case_tac "i = \<parallel>\<Delta>\<parallel>")
  apply simp
  apply (simp split: nat.split nat.split_asm)+
  apply (rule T_Abs [simplified])
  apply (drule_tac x="VarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (rule_tac T\<^sub>1\<^sub>1=T\<^sub>1\<^sub>1 in T_App)
  apply simp+
  apply (rule T_TAbs)
  apply (drule_tac x="TVarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (rule_tac T\<^sub>1\<^sub>1=T\<^sub>1\<^sub>1 in T_TApp)
  apply simp
  apply (rule subtype_trans(2))
  apply assumption+
  apply (rule_tac S=S in T_Sub)
  apply simp
  apply (rule subtype_trans(2))
  apply assumption+
  done

lemma subtype_refl':
  assumes t: "\<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> T <: T"
proof (rule subtype_refl)
  from t show "\<Gamma> \<turnstile>\<^sub>w\<^sub>f" by (rule wf_typeE1)
  from t show "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T" by (rule wf_typeE2)
qed

lemma Abs_type: \<comment> \<open>A.13(1)\<close>
  assumes H: "\<Gamma> \<turnstile> (\<lambda>:S. s) : T"
  shows "\<Gamma> \<turnstile> T <: U \<rightarrow> U' \<Longrightarrow>
    (\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> VarB S \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
      \<Gamma> \<turnstile> \<down>\<^sub>\<tau> 1 0 S' <: U' \<Longrightarrow> P) \<Longrightarrow> P"
  using H
proof (induct \<Gamma> "\<lambda>:S. s" T arbitrary: U U' S s P)
  case (T_Abs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2)
  from \<open>\<Gamma> \<turnstile> T\<^sub>1 \<rightarrow> \<down>\<^sub>\<tau> 1 0 T\<^sub>2 <: U \<rightarrow> U'\<close>
  obtain ty1: "\<Gamma> \<turnstile> U <: T\<^sub>1" and ty2: "\<Gamma> \<turnstile> \<down>\<^sub>\<tau> 1 0 T\<^sub>2 <: U'"
    by cases simp_all
  from ty1 \<open>VarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2\<close> ty2
  show ?case by (rule T_Abs)
next
  case (T_Sub \<Gamma> S' T)
  from \<open>\<Gamma> \<turnstile> S' <: T\<close> and \<open>\<Gamma> \<turnstile> T <: U \<rightarrow> U'\<close>
  have "\<Gamma> \<turnstile> S' <: U \<rightarrow> U'" by (rule subtype_trans(1))
  then show ?case
    by (rule T_Sub) (rule T_Sub(5))
qed

lemma Abs_type':
  assumes H: "\<Gamma> \<turnstile> (\<lambda>:S. s) : U \<rightarrow> U'"
  and R: "\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> VarB S \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
    \<Gamma> \<turnstile> \<down>\<^sub>\<tau> 1 0 S' <: U' \<Longrightarrow> P"
  shows "P" using H subtype_refl' [OF H]
  by (rule Abs_type) (rule R)

lemma TAbs_type: \<comment> \<open>A.13(2)\<close>
  assumes H: "\<Gamma> \<turnstile> (\<lambda><:S. s) : T"
  shows "\<Gamma> \<turnstile> T <: (\<forall><:U. U') \<Longrightarrow>
    (\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> TVarB U \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
      TVarB U \<Colon> \<Gamma> \<turnstile> S' <: U' \<Longrightarrow> P) \<Longrightarrow> P"
  using H
proof (induct \<Gamma> "\<lambda><:S. s" T arbitrary: U U' S s P)
  case (T_TAbs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2)
  from \<open>\<Gamma> \<turnstile> (\<forall><:T\<^sub>1. T\<^sub>2) <: (\<forall><:U. U')\<close>
  obtain ty1: "\<Gamma> \<turnstile> U <: T\<^sub>1" and ty2: "TVarB U \<Colon> \<Gamma> \<turnstile> T\<^sub>2 <: U'"
    by cases simp_all
  from \<open>TVarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2\<close>
  have "TVarB U \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2" using ty1
    by (rule narrow_type [of "[]", simplified])
  with ty1 show ?case using ty2 by (rule T_TAbs)
next
  case (T_Sub \<Gamma> S' T)
  from \<open>\<Gamma> \<turnstile> S' <: T\<close> and \<open>\<Gamma> \<turnstile> T <: (\<forall><:U. U')\<close>
  have "\<Gamma> \<turnstile> S' <: (\<forall><:U. U')" by (rule subtype_trans(1))
  then show ?case
    by (rule T_Sub) (rule T_Sub(5))
qed

lemma TAbs_type':
  assumes H: "\<Gamma> \<turnstile> (\<lambda><:S. s) : (\<forall><:U. U')"
  and R: "\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> TVarB U \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
    TVarB U \<Colon> \<Gamma> \<turnstile> S' <: U' \<Longrightarrow> P"
  shows "P" using H subtype_refl' [OF H]
  by (rule TAbs_type) (rule R)

lemma T_eq: "\<Gamma> \<turnstile> t : T \<Longrightarrow> T = T' \<Longrightarrow> \<Gamma> \<turnstile> t : T'" by simp

text \<open>
The weakening theorem states that inserting a binding @{term B}
does not affect typing:
\<close>

lemma type_weaken:
  assumes H: "\<Delta> @ \<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<Longrightarrow>
    \<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up> 1 \<parallel>\<Delta>\<parallel> t : \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T" using H
  apply (induct "\<Delta> @ \<Gamma>" t T arbitrary: \<Delta>)
  apply simp_all
  apply (rule conjI)
  apply (rule impI)
  apply (rule T_Var)
  apply (erule wfE_weaken)
  apply simp+
  apply (rule impI)
  apply (rule T_Var)
  apply (erule wfE_weaken)
  apply assumption
  apply (subgoal_tac "Suc i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel>)")
  apply simp
  apply arith
  apply (rule refl)
  apply (rule T_Abs [THEN T_eq])
  apply (drule_tac x="VarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply simp
  apply (rule_tac T\<^sub>1\<^sub>1="\<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T\<^sub>1\<^sub>1" in T_App)
  apply simp
  apply simp
  apply (rule T_TAbs)
  apply (drule_tac x="TVarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (erule_tac T_TApp [THEN T_eq])
  apply (drule subtype_weaken)
  apply simp+
  apply (case_tac \<Delta>)
  apply (simp add: liftT_substT_strange [of _ 0, simplified])+
  apply (rule_tac S="\<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> S" in T_Sub)
  apply simp
  apply (drule subtype_weaken)
  apply simp+
  done

text \<open>
We can strengthen this result, so as to mean that concatenating a new context
@{term \<Delta>} to the context @{term \<Gamma>} preserves typing:
\<close>

lemma type_weaken': \<comment> \<open>A.5(6)\<close>
  "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> \<up> \<parallel>\<Delta>\<parallel> 0 t : \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T"
  apply (induct \<Delta>)
  apply simp
  apply simp
  apply (erule well_formedE_cases)
  apply simp
  apply (drule_tac B=a in type_weaken [of "[]", simplified])
  apply simp+
  done

text \<open>
This property is proved by structural induction on the context @{term \<Delta>},
using the previous result in the induction step. In the proof of the preservation
theorem, we will need two substitution theorems for term and type variables,
both of which are proved by induction on the typing derivation.
Since term and type variables are stored in the same context, we again have to
decrement the free type variables in @{term \<Delta>} and @{term T} by \<open>1\<close>
in the substitution rule for term variables in order to compensate for the
disappearance of the variable.
\<close>

theorem subst_type: \<comment> \<open>A.8\<close>
  assumes H: "\<Delta> @ VarB U \<Colon> \<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> u : U \<Longrightarrow>
    \<down>\<^sub>e 1 0 \<Delta> @ \<Gamma> \<turnstile> t[\<parallel>\<Delta>\<parallel> \<mapsto> u] : \<down>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T" using H
  apply (induct "\<Delta> @ VarB U \<Colon> \<Gamma>" t T arbitrary: \<Delta>)
  apply simp
  apply (rule conjI)
  apply (rule impI)
  apply simp
  apply (drule_tac \<Delta>="\<Delta>[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e" in type_weaken')
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)
  apply simp
  apply (rule impI conjI)+
  apply (simp split: nat.split_asm)
  apply (rule T_Var)
  apply (erule wfE_subst)
  apply (rule wf_Top)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> i - Suc 0")
  apply (rename_tac nat)
  apply (subgoal_tac "i - Suc \<parallel>\<Delta>\<parallel> = nat")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply simp
  apply (rule impI)
  apply (rule T_Var)
  apply (erule wfE_subst)
  apply (rule wf_Top)
  apply simp
  apply (subgoal_tac "Suc (\<parallel>\<Delta>\<parallel> - Suc 0) = \<parallel>\<Delta>\<parallel>")
  apply (simp (no_asm_simp))
  apply arith
  apply simp
  apply (drule_tac x="VarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply (rule T_Abs [THEN T_eq])
  apply simp
  apply (simp add: substT_substT [symmetric])
  apply simp
  apply (rule_tac T\<^sub>1\<^sub>1="T\<^sub>1\<^sub>1[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>" in T_App)
  apply simp+
  apply (rule T_TAbs)
  apply (drule_tac x="TVarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply simp
  apply (rule T_TApp [THEN T_eq])
  apply simp
  apply (rule subst_subtype [simplified])
  apply assumption
  apply (simp add: substT_substT [symmetric])
  apply (rule_tac S="S[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>" in T_Sub)
  apply simp
  apply simp
  apply (rule subst_subtype [simplified])
  apply assumption
  done

theorem substT_type: \<comment> \<open>A.11\<close>
  assumes H: "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> P <: Q \<Longrightarrow>
    \<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> t[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P] : T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>" using H
  apply (induct "\<Delta> @ TVarB Q \<Colon> \<Gamma>" t T arbitrary: \<Delta>)
  apply simp_all
  apply (rule impI conjI)+
  apply simp
  apply (rule T_Var)
  apply (erule wfE_subst)
  apply (erule wf_subtypeE)
  apply assumption
  apply (simp split: nat.split_asm)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> i - Suc 0")
  apply (rename_tac nat)
  apply (subgoal_tac "i - Suc \<parallel>\<Delta>\<parallel> = nat")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply simp
  apply (rule impI)
  apply (case_tac "i = \<parallel>\<Delta>\<parallel>")
  apply simp
  apply (rule T_Var)
  apply (erule wfE_subst)
  apply (erule wf_subtypeE)
  apply assumption
  apply simp
  apply (subgoal_tac "i < \<parallel>\<Delta>\<parallel>")
  apply (subgoal_tac "Suc (\<parallel>\<Delta>\<parallel> - Suc 0) = \<parallel>\<Delta>\<parallel>")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply (rule T_Abs [THEN T_eq])
  apply (drule_tac x="VarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (simp add: substT_substT [symmetric])
  apply (rule_tac T\<^sub>1\<^sub>1="T\<^sub>1\<^sub>1[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>" in T_App)
  apply simp+
  apply (rule T_TAbs)
  apply (drule_tac x="TVarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (rule T_TApp [THEN T_eq])
  apply simp
  apply (rule substT_subtype)
  apply assumption
  apply assumption
  apply (simp add: substT_substT [symmetric])
  apply (rule_tac S="S[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>" in T_Sub)
  apply simp
  apply (rule substT_subtype)
  apply assumption
  apply assumption
  done


subsection \<open>Evaluation\<close>

text \<open>
\label{sec:evaluation}
For the formalization of the evaluation strategy, it is useful to first define
a set of {\it canonical values} that are not evaluated any further. The canonical
values of call-by-value \fsub{} are exactly the abstractions over term and type variables:
\<close>

inductive_set
  "value" :: "trm set"
where
  Abs: "(\<lambda>:T. t) \<in> value"
| TAbs: "(\<lambda><:T. t) \<in> value"

text \<open>
The notion of a @{term value} is now used in the defintion of the evaluation
relation \mbox{\<open>t \<longmapsto> t'\<close>}. There are several ways for defining this evaluation
relation: Aydemir et al.\ \cite{PoplMark} advocate the use of {\it evaluation
contexts} that allow to separate the description of the ``immediate'' reduction rules,
i.e.\ $\beta$-reduction, from the description of the context in which these reductions
may occur in. The rationale behind this approach is to keep the formalization more modular.
We will take a closer look at this style of presentation in section
\secref{sec:evaluation-ctxt}. For the rest of this section, we will use a different
approach: both the ``immediate'' reductions and the reduction context are described
within the same inductive definition, where the context is described by additional
congruence rules.
\<close>

inductive
  eval :: "trm \<Rightarrow> trm \<Rightarrow> bool"  (infixl "\<longmapsto>" 50)
where
  E_Abs: "v\<^sub>2 \<in> value \<Longrightarrow> (\<lambda>:T\<^sub>1\<^sub>1. t\<^sub>1\<^sub>2) \<bullet> v\<^sub>2 \<longmapsto> t\<^sub>1\<^sub>2[0 \<mapsto> v\<^sub>2]"
| E_TAbs: "(\<lambda><:T\<^sub>1\<^sub>1. t\<^sub>1\<^sub>2) \<bullet>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]"
| E_App1: "t \<longmapsto> t' \<Longrightarrow> t \<bullet> u \<longmapsto> t' \<bullet> u"
| E_App2: "v \<in> value \<Longrightarrow> t \<longmapsto> t' \<Longrightarrow> v \<bullet> t \<longmapsto> v \<bullet> t'"
| E_TApp: "t \<longmapsto> t' \<Longrightarrow> t \<bullet>\<^sub>\<tau> T \<longmapsto> t' \<bullet>\<^sub>\<tau> T"

text \<open>
Here, the rules \<open>E_Abs\<close> and \<open>E_TAbs\<close> describe the ``immediate'' reductions,
whereas \<open>E_App1\<close>, \<open>E_App2\<close>, and \<open>E_TApp\<close> are additional congruence
rules describing reductions in a context. The most important theorems of this section
are the {\it preservation} theorem, stating that the reduction of a well-typed term
does not change its type, and the {\it progress} theorem, stating that reduction of
a well-typed term does not ``get stuck'' -- in other words, every well-typed, closed
term @{term t} is either a value, or there is a term @{term t'} to which @{term t}
can be reduced. The preservation theorem
is proved by induction on the derivation of @{term "\<Gamma> \<turnstile> t : T"}, followed by a case
distinction on the last rule used in the derivation of @{term "t \<longmapsto> t'"}.
\<close>

theorem preservation: \<comment> \<open>A.20\<close>
  assumes H: "\<Gamma> \<turnstile> t : T"
  shows "t \<longmapsto> t' \<Longrightarrow> \<Gamma> \<turnstile> t' : T" using H
proof (induct arbitrary: t')
  case (T_Var \<Gamma> i U T t')
  from \<open>Var i \<longmapsto> t'\<close>
  show ?case by cases
next
  case (T_Abs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2 t')
  from \<open>(\<lambda>:T\<^sub>1. t\<^sub>2) \<longmapsto> t'\<close>
  show ?case by cases
next
  case (T_App \<Gamma> t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 t\<^sub>2 t')
  from \<open>t\<^sub>1 \<bullet> t\<^sub>2 \<longmapsto> t'\<close>
  show ?case
  proof cases
    case (E_Abs T\<^sub>1\<^sub>1' t\<^sub>1\<^sub>2)
    with T_App have "\<Gamma> \<turnstile> (\<lambda>:T\<^sub>1\<^sub>1'. t\<^sub>1\<^sub>2) : T\<^sub>1\<^sub>1 \<rightarrow> T\<^sub>1\<^sub>2" by simp
    then obtain S'
      where T\<^sub>1\<^sub>1: "\<Gamma> \<turnstile> T\<^sub>1\<^sub>1 <: T\<^sub>1\<^sub>1'"
      and t\<^sub>1\<^sub>2: "VarB T\<^sub>1\<^sub>1' \<Colon> \<Gamma> \<turnstile> t\<^sub>1\<^sub>2 : S'"
      and S': "\<Gamma> \<turnstile> S'[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau> <: T\<^sub>1\<^sub>2" by (rule Abs_type' [simplified]) blast
    from \<open>\<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1\<^sub>1\<close>
    have "\<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1\<^sub>1'" using T\<^sub>1\<^sub>1 by (rule T_Sub)
    with t\<^sub>1\<^sub>2 have "\<Gamma> \<turnstile> t\<^sub>1\<^sub>2[0 \<mapsto> t\<^sub>2] : S'[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
      by (rule subst_type [where \<Delta>="[]", simplified])
    hence "\<Gamma> \<turnstile> t\<^sub>1\<^sub>2[0 \<mapsto> t\<^sub>2] : T\<^sub>1\<^sub>2" using S' by (rule T_Sub)
    with E_Abs show ?thesis by simp
  next
    case (E_App1 t'')
    from \<open>t\<^sub>1 \<longmapsto> t''\<close>
    have "\<Gamma> \<turnstile> t'' : T\<^sub>1\<^sub>1 \<rightarrow> T\<^sub>1\<^sub>2" by (rule T_App)
    hence "\<Gamma> \<turnstile> t'' \<bullet> t\<^sub>2 : T\<^sub>1\<^sub>2" using \<open>\<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1\<^sub>1\<close>
      by (rule typing.T_App)
    with E_App1 show ?thesis by simp
  next
    case (E_App2 t'')
    from \<open>t\<^sub>2 \<longmapsto> t''\<close>
    have "\<Gamma> \<turnstile> t'' : T\<^sub>1\<^sub>1" by (rule T_App)
    with T_App(1) have "\<Gamma> \<turnstile> t\<^sub>1 \<bullet> t'' : T\<^sub>1\<^sub>2"
      by (rule typing.T_App)
    with E_App2 show ?thesis by simp
  qed
next
  case (T_TAbs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2 t')
  from \<open>(\<lambda><:T\<^sub>1. t\<^sub>2) \<longmapsto> t'\<close>
  show ?case by cases
next
  case (T_TApp \<Gamma> t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2 t')
  from \<open>t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t'\<close>
  show ?case
  proof cases
    case (E_TAbs T\<^sub>1\<^sub>1' t\<^sub>1\<^sub>2)
    with T_TApp have "\<Gamma> \<turnstile> (\<lambda><:T\<^sub>1\<^sub>1'. t\<^sub>1\<^sub>2) : (\<forall><:T\<^sub>1\<^sub>1. T\<^sub>1\<^sub>2)" by simp
    then obtain S'
      where "TVarB T\<^sub>1\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>1\<^sub>2 : S'"
      and "TVarB T\<^sub>1\<^sub>1 \<Colon> \<Gamma> \<turnstile> S' <: T\<^sub>1\<^sub>2" by (rule TAbs_type') blast
    hence "TVarB T\<^sub>1\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>1\<^sub>2 : T\<^sub>1\<^sub>2" by (rule T_Sub)
    hence "\<Gamma> \<turnstile> t\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2] : T\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]\<^sub>\<tau>" using T_TApp(3)
      by (rule substT_type [where \<Delta>="[]", simplified])
    with E_TAbs show ?thesis by simp
  next
    case (E_TApp t'')
    from \<open>t\<^sub>1 \<longmapsto> t''\<close>
    have "\<Gamma> \<turnstile> t'' : (\<forall><:T\<^sub>1\<^sub>1. T\<^sub>1\<^sub>2)" by (rule T_TApp)
    hence "\<Gamma> \<turnstile> t'' \<bullet>\<^sub>\<tau> T\<^sub>2 : T\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]\<^sub>\<tau>" using \<open>\<Gamma> \<turnstile> T\<^sub>2 <: T\<^sub>1\<^sub>1\<close>
      by (rule typing.T_TApp)
    with E_TApp show ?thesis by simp
  qed
next
  case (T_Sub \<Gamma> t S T t')
  from \<open>t \<longmapsto> t'\<close>
  have "\<Gamma> \<turnstile> t' : S" by (rule T_Sub)
  then show ?case using \<open>\<Gamma> \<turnstile> S <: T\<close>
    by (rule typing.T_Sub)
qed

text \<open>
The progress theorem is also proved by induction on the derivation of
@{term "[] \<turnstile> t : T"}. In the induction steps, we need the following two lemmas
about {\it canonical forms}
stating that closed values of types @{term "T\<^sub>1 \<rightarrow> T\<^sub>2"} and @{term "\<forall><:T\<^sub>1. T\<^sub>2"}
must be abstractions over term and type variables, respectively.
\<close>

lemma Fun_canonical: \<comment> \<open>A.14(1)\<close>
  assumes ty: "[] \<turnstile> v : T\<^sub>1 \<rightarrow> T\<^sub>2"
  shows "v \<in> value \<Longrightarrow> \<exists>t S. v = (\<lambda>:S. t)" using ty
proof (induct "[]::env" v "T\<^sub>1 \<rightarrow> T\<^sub>2" arbitrary: T\<^sub>1 T\<^sub>2)
  case T_Abs
  show ?case by iprover
next
  case (T_App t\<^sub>1 T\<^sub>1\<^sub>1 t\<^sub>2 T\<^sub>1 T\<^sub>2)
  from \<open>t\<^sub>1 \<bullet> t\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2 T\<^sub>1 T\<^sub>2')
  from \<open>t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case (T_Sub t S T\<^sub>1 T\<^sub>2)
  from \<open>[] \<turnstile> S <: T\<^sub>1 \<rightarrow> T\<^sub>2\<close>
  obtain S\<^sub>1 S\<^sub>2 where S: "S = S\<^sub>1 \<rightarrow> S\<^sub>2"
    by cases (auto simp add: T_Sub)
  show ?case by (rule T_Sub S)+
qed simp

lemma TyAll_canonical: \<comment> \<open>A.14(3)\<close>
  assumes ty: "[] \<turnstile> v : (\<forall><:T\<^sub>1. T\<^sub>2)"
  shows "v \<in> value \<Longrightarrow> \<exists>t S. v = (\<lambda><:S. t)" using ty
proof (induct "[]::env" v "\<forall><:T\<^sub>1. T\<^sub>2" arbitrary: T\<^sub>1 T\<^sub>2)
  case (T_App t\<^sub>1 T\<^sub>1\<^sub>1 t\<^sub>2 T\<^sub>1 T\<^sub>2)
  from \<open>t\<^sub>1 \<bullet> t\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case T_TAbs
  show ?case by iprover
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2 T\<^sub>1 T\<^sub>2')
  from \<open>t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case (T_Sub t S T\<^sub>1 T\<^sub>2)
  from \<open>[] \<turnstile> S <: (\<forall><:T\<^sub>1. T\<^sub>2)\<close>
  obtain S\<^sub>1 S\<^sub>2 where S: "S = (\<forall><:S\<^sub>1. S\<^sub>2)"
    by cases (auto simp add: T_Sub)
  show ?case by (rule T_Sub S)+
qed simp

theorem progress:
  assumes ty: "[] \<turnstile> t : T"
  shows "t \<in> value \<or> (\<exists>t'. t \<longmapsto> t')" using ty
proof (induct "[]::env" t T)
  case T_Var
  thus ?case by simp
next
  case T_Abs
  from value.Abs show ?case ..
next
  case (T_App t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 t\<^sub>2)
  hence "t\<^sub>1 \<in> value \<or> (\<exists>t'. t\<^sub>1 \<longmapsto> t')" by simp
  thus ?case
  proof
    assume t\<^sub>1_val: "t\<^sub>1 \<in> value"
    with T_App obtain t S where t\<^sub>1: "t\<^sub>1 = (\<lambda>:S. t)"
      by (auto dest!: Fun_canonical)
    from T_App have "t\<^sub>2 \<in> value \<or> (\<exists>t'. t\<^sub>2 \<longmapsto> t')" by simp
    thus ?thesis
    proof
      assume "t\<^sub>2 \<in> value"
      with t\<^sub>1 have "t\<^sub>1 \<bullet> t\<^sub>2 \<longmapsto> t[0 \<mapsto> t\<^sub>2]"
        by simp (rule eval.intros)
      thus ?thesis by iprover
    next
      assume "\<exists>t'. t\<^sub>2 \<longmapsto> t'"
      then obtain t' where "t\<^sub>2 \<longmapsto> t'" by iprover
      with t\<^sub>1_val have "t\<^sub>1 \<bullet> t\<^sub>2 \<longmapsto> t\<^sub>1 \<bullet> t'" by (rule eval.intros)
      thus ?thesis by iprover
    qed
  next
    assume "\<exists>t'. t\<^sub>1 \<longmapsto> t'"
    then obtain t' where "t\<^sub>1 \<longmapsto> t'" ..
    hence "t\<^sub>1 \<bullet> t\<^sub>2 \<longmapsto> t' \<bullet> t\<^sub>2" by (rule eval.intros)
    thus ?thesis by iprover
  qed
next
  case T_TAbs
  from value.TAbs show ?case ..
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2)
  hence "t\<^sub>1 \<in> value \<or> (\<exists>t'. t\<^sub>1 \<longmapsto> t')" by simp
  thus ?case
  proof
    assume "t\<^sub>1 \<in> value"
    with T_TApp obtain t S where "t\<^sub>1 = (\<lambda><:S. t)"
      by (auto dest!: TyAll_canonical)
    hence "t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]" by simp (rule eval.intros)
    thus ?thesis by iprover
  next
    assume "\<exists>t'. t\<^sub>1 \<longmapsto> t'"
    then obtain t' where "t\<^sub>1 \<longmapsto> t'" ..
    hence "t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t' \<bullet>\<^sub>\<tau> T\<^sub>2" by (rule eval.intros)
    thus ?thesis by iprover
  qed
next
  case (T_Sub t S T)
  show ?case by (rule T_Sub)
qed

end
