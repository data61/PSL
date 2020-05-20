chapter \<open>Second Example\<close>

theory %invisible Second_Example
imports Main
begin

text \<open>\label{chap:exampleII}\<close>

text \<open>Pop-refinement is illustrated via a simple derivation,
in Isabelle/HOL,
of a non-deterministic program that satisfies a hyperproperty.\<close>


section \<open>Hyperproperties\<close>
text \<open>\label{sec:hyper}\<close>

text \<open>Hyperproperties are predicates over sets of traces~%
\cite{ClarksonSchneiderHyperproperties}.
Hyperproperties capture security policies
like non-interference~\cite{GoguenMeseguerNonInterference},
which applies to deterministic systems,
and generalized non-interference (GNI)~\cite{McCulloughSpecificationsMLS},
which generalizes non-interference to non-deterministic systems.\<close>

text \<open>The formulation of GNI in~\cite{ClarksonSchneiderHyperproperties},
which is derived from~\cite{McLeanPossibilisticProperties},
is based on:
\begin{itemize}
\item
A notion of traces as infinite streams of abstract states.
\item
Functions that map each state to low and high inputs and outputs,
where `low' and `high' have the usual security meaning
(e.g.\ `low' means `unclassified' and `high' means `classified').
These functions are homomorphically extended to map each trace
to infinite streams of low and high inputs and outputs.
\end{itemize}
The following formulation is slightly more general,
because the functions that return low and high inputs and outputs
operate directly on abstract traces.\<close>

text \<open>GNI says that for any two traces @{term \<tau>\<^sub>1} and @{term \<tau>\<^sub>2},
there is always a trace @{term \<tau>\<^sub>3} with
the same high inputs as @{term \<tau>\<^sub>1}
and the same low inputs and low outputs as @{term \<tau>\<^sub>2}.
Intuitively, this means that a low observer
(i.e.\ one that only observes low inputs and low outputs of traces)
cannot gain any information about high inputs
(i.e.\ high inputs cannot interfere with low outputs)
because observing a trace @{term \<tau>\<^sub>2}
is indistinguishable from observing some other trace @{term \<tau>\<^sub>3}
that has the same high inputs as an arbitrary trace @{term \<tau>\<^sub>1}.\<close>

locale generalized_non_interference =
  fixes low_in :: "'\<tau> \<Rightarrow> 'i" \<comment> \<open>low inputs\<close>
  fixes low_out :: "'\<tau> \<Rightarrow> 'o" \<comment> \<open>low outputs\<close>
  fixes high_in :: "'\<tau> \<Rightarrow> 'i" \<comment> \<open>high inputs\<close>
  fixes high_out :: "'\<tau> \<Rightarrow> 'o" \<comment> \<open>high outputs\<close>

definition (in generalized_non_interference) GNI :: "'\<tau> set \<Rightarrow> bool"
where "GNI \<T> \<equiv>
  \<forall>\<tau>\<^sub>1 \<in> \<T>. \<forall>\<tau>\<^sub>2 \<in> \<T>. \<exists>\<tau>\<^sub>3 \<in> \<T>.
    high_in \<tau>\<^sub>3 = high_in \<tau>\<^sub>1 \<and> low_in \<tau>\<^sub>3 = low_in \<tau>\<^sub>2 \<and> low_out \<tau>\<^sub>3 = low_out \<tau>\<^sub>2"


section \<open>Target Programming Language\<close>
text \<open>\label{sec:targetII}\<close>

text \<open>In the target language used in this example,%
\footnote{Even though this language has many similarities
with the language in \secref{sec:targetI},
the two languages are defined separately
to keep \chapref{chap:exampleI} simpler.}
a program consists of
a list of distinct state variables
and a body of statements.
The statements modify the variables
by deterministically assigning results of expressions
and by non-deterministically assigning random values.
Expressions are built out of
non-negative integer constants,
state variables,
and addition operations.
Statements are combined
via conditionals, whose tests compare expressions for equality,
and via sequencing.
Each variable stores a non-negative integer.
Executing the body in a state yields a new state.
Because of non-determinism, different new states are possible,
i.e.\ executing the body in the same state
may yield different new states at different times.\<close>

text \<open>For instance, executing the body of the program
\begin{verbatim}
  prog {
    vars {
      x
      y
    }
    body {
      if (x == y + 1) {
        x = 0;
      } else {
        x = y + 3;
      }
      randomize y;
      y = y + 2;
    }
  }
\end{verbatim}
in the state where \verb|x| contains 4 and \verb|y| contains 7,
yields a new state where
\verb|x| always contains 10
and \verb|y| may contain any number in $\{2,3,\ldots\}$.\<close>


subsection \<open>Syntax\<close>
text \<open>\label{sec:syntaxII}\<close>

text \<open>Variables are identified by names.\<close>

type_synonym name = string

text \<open>Expressions are built out of
constants, variables, and addition operations.\<close>

datatype expr = Const nat | Var name | Add expr expr

text \<open>Statements are built out of
deterministic assignments,
non-deterministic assignments,
conditionals,
and sequencing.\<close>

datatype stmt =
  Assign name expr |
  Random name |
  IfEq expr expr stmt stmt |
  Seq stmt stmt

text \<open>A program consists of
a list of state variables
and a body statement.\<close>

record prog =
  vars :: "name list"
  body :: stmt


subsection \<open>Static Semantics\<close>
text \<open>\label{sec:staticII}\<close>

text \<open>A context is a set of variables.\<close>

type_synonym ctxt = "name set"

text \<open>Given a context,
an expression is well-formed iff\
all its variables are in the context.\<close>

fun wfe :: "ctxt \<Rightarrow> expr \<Rightarrow> bool"
where
  "wfe \<Gamma> (Const c) \<longleftrightarrow> True" |
  "wfe \<Gamma> (Var v) \<longleftrightarrow> v \<in> \<Gamma>" |
  "wfe \<Gamma> (Add e\<^sub>1 e\<^sub>2) \<longleftrightarrow> wfe \<Gamma> e\<^sub>1 \<and> wfe \<Gamma> e\<^sub>2"

text \<open>Given a context,
a statement is well-formed iff\
its deterministic assignments
assign well-formed expressions to variables in the context,
its non-deterministic assignments operate on variables in the context,
and its conditional tests compare well-formed expressions.\<close>

fun wfs :: "ctxt \<Rightarrow> stmt \<Rightarrow> bool"
where
  "wfs \<Gamma> (Assign v e) \<longleftrightarrow> v \<in> \<Gamma> \<and> wfe \<Gamma> e" |
  "wfs \<Gamma> (Random v) \<longleftrightarrow> v \<in> \<Gamma>" |
  "wfs \<Gamma> (IfEq e\<^sub>1 e\<^sub>2 s\<^sub>1 s\<^sub>2) \<longleftrightarrow> wfe \<Gamma> e\<^sub>1 \<and> wfe \<Gamma> e\<^sub>2 \<and> wfs \<Gamma> s\<^sub>1 \<and> wfs \<Gamma> s\<^sub>2" |
  "wfs \<Gamma> (Seq s\<^sub>1 s\<^sub>2) \<longleftrightarrow> wfs \<Gamma> s\<^sub>1 \<and> wfs \<Gamma> s\<^sub>2"

text \<open>The context of a program consists of the state variables.\<close>

definition ctxt :: "prog \<Rightarrow> ctxt"
where "ctxt p \<equiv> set (vars p)"

text \<open>A program is well-formed iff\
the variables are distinct
and the body is well-formed in the context of the program.\<close>

definition wfp :: "prog \<Rightarrow> bool"
where "wfp p \<equiv> distinct (vars p) \<and> wfs (ctxt p) (body p)"


subsection \<open>Dynamic Semantics\<close>
text \<open>\label{sec:dynamicII}\<close>

text \<open>A state associates values (non-negative integers) to variables.\<close>

type_synonym state = "name \<rightharpoonup> nat"

text \<open>A state matches a context iff\
state and context have the same variables.\<close>

definition match :: "state \<Rightarrow> ctxt \<Rightarrow> bool"
where "match \<sigma> \<Gamma> \<equiv> dom \<sigma> = \<Gamma>"

text \<open>Evaluating an expression in a state yields a value,
or an error (@{const None})
if the expression contains a variable not in the state.\<close>

definition add_opt :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option" (infixl "\<oplus>" 65)
\<comment> \<open>Lifting of addition to @{typ "nat option"}.\<close>
where "U\<^sub>1 \<oplus> U\<^sub>2 \<equiv>
  case (U\<^sub>1, U\<^sub>2) of (Some u\<^sub>1, Some u\<^sub>2) \<Rightarrow> Some (u\<^sub>1 + u\<^sub>2) | _ \<Rightarrow> None"

fun eval :: "state \<Rightarrow> expr \<Rightarrow> nat option"
where
 "eval \<sigma> (Const c) = Some c" |
 "eval \<sigma> (Var v) = \<sigma> v" |
 "eval \<sigma> (Add e\<^sub>1 e\<^sub>2) = eval \<sigma> e\<^sub>1 \<oplus> eval \<sigma> e\<^sub>2"

text \<open>Evaluating a well-formed expression never yields an error,
if the state matches the context.\<close>

lemma eval_wfe:
  "wfe \<Gamma> e \<Longrightarrow> match \<sigma> \<Gamma> \<Longrightarrow> eval \<sigma> e \<noteq> None"
by (induct e, auto simp: match_def add_opt_def)

text \<open>Executing a statement in a state yields a new state,
or an error (@{const None})
if the evaluation of an expression yields an error
or if an assignment operates on a variable not in the state.
Non-determinism is modeled via a relation
between old states and results,
where a result is either a new state or an error.\<close>

inductive exec :: "stmt \<Rightarrow> state \<Rightarrow> state option \<Rightarrow> bool"
  ("_ \<rhd> _ \<leadsto> _" [50, 50, 50] 50)
where
  ExecAssignNoVar:
    "v \<notin> dom \<sigma> \<Longrightarrow> Assign v e \<rhd> \<sigma> \<leadsto> None" |
  ExecAssignEvalError:
    "eval \<sigma> e = None \<Longrightarrow> Assign v e \<rhd> \<sigma> \<leadsto> None" |
  ExecAssignOK: "
    v \<in> dom \<sigma> \<Longrightarrow>
    eval \<sigma> e = Some u \<Longrightarrow>
    Assign v e \<rhd> \<sigma> \<leadsto> Some (\<sigma>(v \<mapsto> u))" |
  ExecRandomNoVar:
    "v \<notin> dom \<sigma> \<Longrightarrow> Random v \<rhd> \<sigma> \<leadsto> None" |
  ExecRandomOK:
    "v \<in> dom \<sigma> \<Longrightarrow> Random v \<rhd> \<sigma> \<leadsto> Some (\<sigma>(v \<mapsto> u))" |
  ExecCondEvalError1:
    "eval \<sigma> e\<^sub>1 = None \<Longrightarrow> IfEq e\<^sub>1 e\<^sub>2 s\<^sub>1 s\<^sub>2 \<rhd> \<sigma> \<leadsto> None" |
  ExecCondEvalError2:
    "eval \<sigma> e\<^sub>2 = None \<Longrightarrow> IfEq e\<^sub>1 e\<^sub>2 s\<^sub>1 s\<^sub>2 \<rhd> \<sigma> \<leadsto> None" |
  ExecCondTrue: "
    eval \<sigma> e\<^sub>1 = Some u\<^sub>1 \<Longrightarrow>
    eval \<sigma> e\<^sub>2 = Some u\<^sub>2 \<Longrightarrow>
    u\<^sub>1 = u\<^sub>2 \<Longrightarrow>
    s\<^sub>1 \<rhd> \<sigma> \<leadsto> \<rho> \<Longrightarrow>
    IfEq e\<^sub>1 e\<^sub>2 s\<^sub>1 s\<^sub>2 \<rhd> \<sigma> \<leadsto> \<rho>" |
  ExecCondFalse: "
    eval \<sigma> e\<^sub>1 = Some u\<^sub>1 \<Longrightarrow>
    eval \<sigma> e\<^sub>2 = Some u\<^sub>2 \<Longrightarrow>
    u\<^sub>1 \<noteq> u\<^sub>2 \<Longrightarrow>
    s\<^sub>2 \<rhd> \<sigma> \<leadsto> \<rho> \<Longrightarrow>
    IfEq e\<^sub>1 e\<^sub>2 s\<^sub>1 s\<^sub>2 \<rhd> \<sigma> \<leadsto> \<rho>" |
  ExecSeqError:
    "s\<^sub>1 \<rhd> \<sigma> \<leadsto> None \<Longrightarrow> Seq s\<^sub>1 s\<^sub>2 \<rhd> \<sigma> \<leadsto> None" |
  ExecSeqOK:
    "s\<^sub>1 \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<Longrightarrow> s\<^sub>2 \<rhd> \<sigma>' \<leadsto> \<rho> \<Longrightarrow> Seq s\<^sub>1 s\<^sub>2 \<rhd> \<sigma> \<leadsto> \<rho>"

text \<open>The execution of any statement in any state always yields a result.\<close>

lemma exec_always:
  "\<exists>\<rho>. s \<rhd> \<sigma> \<leadsto> \<rho>"
proof (induct s arbitrary: \<sigma>)
  case Assign
  show ?case
  by (metis
    ExecAssignEvalError ExecAssignNoVar ExecAssignOK option.exhaust)
next
  case Random
  show ?case
  by (metis ExecRandomNoVar ExecRandomOK)
next
  case IfEq
  thus ?case
  by (metis
    ExecCondEvalError1 ExecCondEvalError2 ExecCondFalse ExecCondTrue
    option.exhaust)
next
  case Seq
  thus ?case
  by (metis ExecSeqError ExecSeqOK option.exhaust)
qed

text \<open>Executing a well-formed statement in a state that matches the context
never yields an error and always yields states that match the context.\<close>

lemma exec_wfs_match:
  "wfs \<Gamma> s \<Longrightarrow> match \<sigma> \<Gamma> \<Longrightarrow> s \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<Longrightarrow> match \<sigma>' \<Gamma>"
proof (induct s arbitrary: \<sigma> \<sigma>')
  case (Assign v e)
  then obtain u
  where "eval \<sigma> e = Some u"
  and "\<sigma>' = \<sigma>(v \<mapsto> u)"
  by (auto elim: exec.cases)
  with Assign
  show ?case
  by (metis
    domIff dom_fun_upd fun_upd_triv match_def option.distinct(1) wfs.simps(1))
next
  case (Random v)
  then obtain u
  where "\<sigma>' = \<sigma>(v \<mapsto> u)"
  by (auto elim: exec.cases)
  with Random
  show ?case
  by (metis
    domIff dom_fun_upd fun_upd_triv match_def option.distinct(1) wfs.simps(2))
next
  case (IfEq e\<^sub>1 e\<^sub>2 s\<^sub>1 s\<^sub>2)
  hence "s\<^sub>1 \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<or> s\<^sub>2 \<rhd> \<sigma> \<leadsto> Some \<sigma>'"
  by (blast elim: exec.cases)
  with IfEq
  show ?case
  by (metis wfs.simps(3))
next
  case (Seq s\<^sub>1 s\<^sub>2)
  then obtain \<sigma>\<^sub>i
  where "s\<^sub>1 \<rhd> \<sigma> \<leadsto> Some \<sigma>\<^sub>i"
  and "s\<^sub>2 \<rhd> \<sigma>\<^sub>i \<leadsto> Some \<sigma>'"
  by (blast elim: exec.cases)
  with Seq
  show ?case
  by (metis wfs.simps(4))
qed

lemma exec_wfs_no_error:
  "wfs \<Gamma> s \<Longrightarrow> match \<sigma> \<Gamma> \<Longrightarrow> \<not> (s \<rhd> \<sigma> \<leadsto> None)"
proof (induct s arbitrary: \<sigma>)
  case (Assign v e)
  hence Var: "v \<in> dom \<sigma>"
  by (auto simp: match_def)
  from Assign
  have "eval \<sigma> e \<noteq> None"
  by (metis eval_wfe wfs.simps(1))
  with Var
  show ?case
  by (auto elim: exec.cases)
next
  case (Random v)
  thus ?case
  by (auto simp: match_def elim: exec.cases)
next
  case (IfEq e\<^sub>1 e\<^sub>2 s\<^sub>1 s\<^sub>2)
  then obtain u\<^sub>1 u\<^sub>2
  where "eval \<sigma> e\<^sub>1 = Some u\<^sub>1"
  and "eval \<sigma> e\<^sub>2 = Some u\<^sub>2"
  by (metis eval_wfe not_Some_eq wfs.simps(3))
  with IfEq
  show ?case
  by (auto elim: exec.cases)
next
  case (Seq s\<^sub>1 s\<^sub>2)
  show ?case
  proof
    assume "Seq s\<^sub>1 s\<^sub>2 \<rhd> \<sigma> \<leadsto> None"
    hence "s\<^sub>1 \<rhd> \<sigma> \<leadsto> None \<or> (\<exists>\<sigma>'. s\<^sub>1 \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<and> s\<^sub>2 \<rhd> \<sigma>' \<leadsto> None)"
    by (auto elim: exec.cases)
    with Seq exec_wfs_match
    show False
    by (metis wfs.simps(4))
  qed
qed

lemma exec_wfs_always_match:
  "wfs \<Gamma> s \<Longrightarrow> match \<sigma> \<Gamma> \<Longrightarrow> \<exists>\<sigma>'. s \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<and> match \<sigma>' \<Gamma>"
by (metis exec_always exec_wfs_match exec_wfs_no_error option.exhaust)

text \<open>The states of a program
are the ones that match the context of the program.\<close>

definition states :: "prog \<Rightarrow> state set"
where "states p \<equiv> {\<sigma>. match \<sigma> (ctxt p)}"

text \<open>Executing the body of a well-formed program in a state of the program
always yields some state of the program, and never an error.\<close>

lemma exec_wfp_no_error:
  "wfp p \<Longrightarrow> \<sigma> \<in> states p \<Longrightarrow> \<not> (body p \<rhd> \<sigma> \<leadsto> None)"
by (metis exec_wfs_no_error mem_Collect_eq states_def wfp_def)

lemma exec_wfp_in_states:
  "wfp p \<Longrightarrow> \<sigma> \<in> states p \<Longrightarrow> body p \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<Longrightarrow> \<sigma>' \<in> states p"
by (metis exec_wfs_match mem_Collect_eq states_def wfp_def)

lemma exec_wfp_always_in_states:
  "wfp p \<Longrightarrow> \<sigma> \<in> states p \<Longrightarrow> \<exists>\<sigma>'. body p \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<and> \<sigma>' \<in> states p"
by (metis exec_always exec_wfp_in_states exec_wfp_no_error option.exhaust)

text \<open>Program execution can be described
in terms of the trace formalism in~\cite{ClarksonSchneiderHyperproperties}.
Every possible (non-erroneous) execution of a program
can be described by a trace of two states---initial and final.
In this definition,
erroneous executions do not contribute to the traces of a program;
only well-formed programs are of interest,
which, as proved above, never execute erroneously.
Due to non-determinism, there may be traces
with the same initial state and different final states.\<close>

record trace =
  initial :: state
  final :: state

inductive_set traces :: "prog \<Rightarrow> trace set"
for p::prog
where [intro!]: "
  \<sigma> \<in> states p \<Longrightarrow>
  body p \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<Longrightarrow>
  \<lparr>initial = \<sigma>, final = \<sigma>'\<rparr> \<in> traces p"

text \<open>The finite traces of a program could be turned into infinite traces
by infinitely stuttering the final state,
obtaining the `executions' defined in~\cite{ClarksonSchneiderHyperproperties}.
However, such infinite traces carry no additional information
compared to the finite traces from which they are derived:
for programs in this language,
the infinite executions of~\cite{ClarksonSchneiderHyperproperties}
are modeled as finite traces of type @{typ trace}.\<close>


section \<open>Requirement Specification\<close>
text \<open>\label{sec:specificationII}\<close>

text \<open>The target program
must process low and high inputs to yield low and high outputs,
according to constraints that involve
both non-determinism and under-specification,
with no information flowing from high inputs to low outputs.%
\footnote{As in \secref{sec:hyper},
`low' and `high' have the usual security meaning,
e.g.\ `low' means `unclassified' and `high' means `classified'.}\<close>


subsection \<open>Input/Output Variables\<close>
text \<open>\label{sec:specII:iovars}\<close>

text \<open>Even though the language defined in \secref{sec:targetII}
has no explicit features for input and output,
an external agent could
write values into some variables,
execute the program body,
and read values from some variables.
Thus, variables may be regarded as holding
inputs (in the initial state) and outputs (in the final state).\<close>

text \<open>In the target program, four variables are required:
\begin{itemize}
\item
A variable @{term "''lowIn''"} to hold low inputs.
\item
A variable @{term "''lowOut''"} to hold low outputs.
\item
A variable @{term "''highIn''"} to hold high inputs.
\item
A variable @{term "''highOut''"} to hold high outputs.
\end{itemize}
Other variables are allowed but not required.\<close>

definition io_vars :: "prog \<Rightarrow> bool"
where "io_vars p \<equiv> ctxt p \<supseteq> {''lowIn'', ''lowOut'', ''highIn'', ''highOut''}"


subsection \<open>Low Processing\<close>
text \<open>\label{sec:specII:lowproc}\<close>

text \<open>If the low input is not 0,
the low output must be 1 plus the low input.
That is,
for every possible execution of the program
where the initial state's low input is not 0,
the final state's low output must be 1 plus the low input.
If there are multiple possible final states for the same initial state
due to non-determinism,
all of them must have the same required low output.
Thus, processing of non-0 low inputs must be deterministic.\<close>

definition low_proc_non0 :: "prog \<Rightarrow> bool"
where "low_proc_non0 p \<equiv>
  \<forall>\<sigma> \<in> states p. \<forall>\<sigma>'.
    the (\<sigma> ''lowIn'') \<noteq> 0 \<and>
    body p \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<longrightarrow>
    the (\<sigma>' ''lowOut'') = the (\<sigma> ''lowIn'') + 1"

text \<open>If the low input is 0, the low output must be a random value.
That is,
for every possible initial state of the program whose low input is 0,
and for every possible value,
there must exist an execution of the program
whose final state has that value as low output.
Executions corresponding to all possible values must be possible.
Thus, processing of the 0 low input must be non-deterministic.\<close>

definition low_proc_0 :: "prog \<Rightarrow> bool"
where "low_proc_0 p \<equiv>
  \<forall>\<sigma> \<in> states p. \<forall>u.
    the (\<sigma> ''lowIn'') = 0 \<longrightarrow>
    (\<exists>\<sigma>'. body p \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<and> the (\<sigma>' ''lowOut'') = u)"


subsection \<open>High Processing\<close>
text \<open>\label{sec:specII:highproc}\<close>

text \<open>The high output must be
at least as large as the sum of the low and high inputs.
That is,
for every possible execution of the program,
the final state's high output must satisfy the constraint.
If there are multiple possible final states for the same initial state
due to non-determinism,
all of them must contain a high output that satisfies the constraint.
Since different high outputs may satisfy the constraint given the same inputs,
not all the possible final states from a given initial state
must have the same high output.
Thus, processing of high inputs is under-specified;
it can be realized deterministically or non-deterministically.\<close>

definition high_proc :: "prog \<Rightarrow> bool"
where "high_proc p \<equiv>
  \<forall>\<sigma> \<in> states p. \<forall>\<sigma>'.
    body p \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<longrightarrow>
    the (\<sigma>' ''highOut'') \<ge> the (\<sigma> ''lowIn'') + the (\<sigma> ''highIn'')"


subsection \<open>All Requirements\<close>
text \<open>\label{sec:specII:all}\<close>

text \<open>Besides satisfying the above requirements on
input/output variables, low processing, and high processing,
the target program must be well-formed.\<close>

definition spec\<^sub>0 :: "prog \<Rightarrow> bool"
where "spec\<^sub>0 p \<equiv>
  wfp p \<and> io_vars p \<and> low_proc_non0 p \<and> low_proc_0 p \<and> high_proc p"


subsection \<open>Generalized Non-Interference\<close>
text \<open>\label{sec:specII:GNI}\<close>

text \<open>The parameters of the GNI formulation in \secref{sec:hyper}
are instantiated according to the target program under consideration.
In an execution of the program:
\begin{itemize}
\item
The value of the variable @{term "''lowIn''"} in the initial state
is the low input.
\item
The value of the variable @{term "''lowOut''"} in the final state
is the low output.
\item
The value of the variable @{term "''highIn''"} in the initial state
is the high input.
\item
The value of the variable @{term "''highOut''"} in the final state
is the high output.
\end{itemize}\<close>

definition low_in :: "trace \<Rightarrow> nat"
where "low_in \<tau> \<equiv> the (initial \<tau> ''lowIn'')"

definition low_out :: "trace \<Rightarrow> nat"
where "low_out \<tau> \<equiv> the (final \<tau> ''lowOut'')"

definition high_in :: "trace \<Rightarrow> nat"
where "high_in \<tau> \<equiv> the (initial \<tau> ''highIn'')"

definition high_out :: "trace \<Rightarrow> nat"
where "high_out \<tau> \<equiv> the (final \<tau> ''highOut'')"

interpretation
  Target: generalized_non_interference low_in low_out high_in high_out .

abbreviation GNI :: "trace set \<Rightarrow> bool"
where "GNI \<equiv> Target.GNI"

text \<open>The requirements in @{const spec\<^sub>0} imply that
the set of traces of the target program satisfies GNI.\<close>

lemma spec\<^sub>0_GNI:
  "spec\<^sub>0 p \<Longrightarrow> GNI (traces p)"
proof (auto simp: Target.GNI_def)
  assume Spec: "spec\<^sub>0 p"
  \<comment> \<open>Consider a trace @{text \<tau>\<^sub>1} and its high input:\<close>
  fix \<tau>\<^sub>1::trace
  define highIn where "highIn = high_in \<tau>\<^sub>1"
  \<comment> \<open>Consider a trace @{text \<tau>\<^sub>2},
        its low input and output,
        and its states:\<close>
  fix \<tau>\<^sub>2::trace
  define lowIn lowOut \<sigma>\<^sub>2 \<sigma>\<^sub>2'
    where "lowIn = low_in \<tau>\<^sub>2"
      and "lowOut = low_out \<tau>\<^sub>2"
      and "\<sigma>\<^sub>2 = initial \<tau>\<^sub>2"
      and "\<sigma>\<^sub>2' = final \<tau>\<^sub>2"
  assume "\<tau>\<^sub>2 \<in> traces p"
  hence Exec2: "body p \<rhd> \<sigma>\<^sub>2 \<leadsto> Some \<sigma>\<^sub>2'"
  and State2: "\<sigma>\<^sub>2 \<in> states p"
  by (auto simp: \<sigma>\<^sub>2_def \<sigma>\<^sub>2'_def elim: traces.cases)
  \<comment> \<open>Construct the initial state of the witness trace @{text \<tau>\<^sub>3}:\<close>
  define \<sigma>\<^sub>3 where "\<sigma>\<^sub>3 = \<sigma>\<^sub>2 (''highIn'' \<mapsto> highIn)"
  hence LowIn3: "the (\<sigma>\<^sub>3 ''lowIn'') = lowIn"
  and HighIn3: "the (\<sigma>\<^sub>3 ''highIn'') = highIn"
  by (auto simp: lowIn_def low_in_def \<sigma>\<^sub>2_def)
  from Spec State2
  have State3: "\<sigma>\<^sub>3 \<in> states p"
  by (auto simp: \<sigma>\<^sub>3_def states_def match_def spec\<^sub>0_def io_vars_def)
  \<comment> \<open>Construct the final state of @{text \<tau>\<^sub>3}, and @{text \<tau>\<^sub>3},
        by cases on @{term lowIn}:\<close>
  show
    "\<exists>\<tau>\<^sub>3 \<in> traces p.
      high_in \<tau>\<^sub>3 = high_in \<tau>\<^sub>1 \<and>
      low_in \<tau>\<^sub>3 = low_in \<tau>\<^sub>2 \<and>
      low_out \<tau>\<^sub>3 = low_out \<tau>\<^sub>2"
  proof (cases lowIn)
    case 0
    \<comment> \<open>Use as final state the one required by @{term low_proc_0}:\<close>
    with Spec State3 LowIn3
    obtain \<sigma>\<^sub>3'
    where Exec3: "body p \<rhd> \<sigma>\<^sub>3 \<leadsto> Some \<sigma>\<^sub>3'"
    and LowOut3: "the (\<sigma>\<^sub>3' ''lowOut'') = lowOut"
    by (auto simp: spec\<^sub>0_def low_proc_0_def)
    \<comment> \<open>Construct @{text \<tau>\<^sub>3} from its initial and final states:\<close>
    define \<tau>\<^sub>3 where "\<tau>\<^sub>3 = \<lparr>initial = \<sigma>\<^sub>3, final = \<sigma>\<^sub>3'\<rparr>"
    with Exec3 State3
    have Trace3: "\<tau>\<^sub>3 \<in> traces p"
    by auto
    have "high_in \<tau>\<^sub>3 = high_in \<tau>\<^sub>1"
    and "low_in \<tau>\<^sub>3 = low_in \<tau>\<^sub>2"
    and "low_out \<tau>\<^sub>3 = low_out \<tau>\<^sub>2"
    by (auto simp:
      high_in_def low_in_def low_out_def
      \<tau>\<^sub>3_def \<sigma>\<^sub>2_def \<sigma>\<^sub>2'_def
      highIn_def lowIn_def lowOut_def
      LowIn3 HighIn3 LowOut3)
    with Trace3
    show ?thesis
    by auto
  next
    case Suc
    hence Not0: "lowIn \<noteq> 0"
    by auto
    \<comment> \<open>Derive @{term \<tau>\<^sub>2}'s low output from @{term low_proc_non0}:\<close>
    with Exec2 State2 Spec
    have LowOut2: "lowOut = lowIn + 1"
    by (auto simp:
      spec\<^sub>0_def low_proc_non0_def \<sigma>\<^sub>2_def \<sigma>\<^sub>2'_def
      low_in_def low_out_def lowIn_def lowOut_def)
    \<comment> \<open>Use any final state for @{text \<tau>\<^sub>3}:\<close>
    from Spec
    have "wfp p"
    by (auto simp: spec\<^sub>0_def)
    with State3
    obtain \<sigma>\<^sub>3'
    where Exec3: "body p \<rhd> \<sigma>\<^sub>3 \<leadsto> Some \<sigma>\<^sub>3'"
    by (metis exec_always exec_wfp_no_error not_Some_eq)
    \<comment> \<open>Derive @{text \<tau>\<^sub>3}'s low output from @{term low_proc_non0}:\<close>
    with State3 Spec Not0
    have LowOut3: "the (\<sigma>\<^sub>3' ''lowOut'') = lowIn + 1"
    by (auto simp: spec\<^sub>0_def low_proc_non0_def LowIn3)
    \<comment> \<open>Construct @{text \<tau>\<^sub>3} from its initial and final states:\<close>
    define \<tau>\<^sub>3 where "\<tau>\<^sub>3 = \<lparr>initial = \<sigma>\<^sub>3, final = \<sigma>\<^sub>3'\<rparr>"
    with Exec3 State3
    have Trace3: "\<tau>\<^sub>3 \<in> traces p"
    by auto
    have "high_in \<tau>\<^sub>3 = high_in \<tau>\<^sub>1"
    and "low_in \<tau>\<^sub>3 = low_in \<tau>\<^sub>2"
    and "low_out \<tau>\<^sub>3 = low_out \<tau>\<^sub>2"
    by (auto simp:
      high_in_def low_in_def low_out_def
      \<tau>\<^sub>3_def \<sigma>\<^sub>3_def \<sigma>\<^sub>2_def
      LowOut2 LowOut3
      highIn_def lowOut_def[unfolded low_out_def, symmetric])
    with Trace3
    show ?thesis
    by auto
  qed
qed

text \<open>Since GNI is implied by @{const spec\<^sub>0}
and since every pop-refinement of @{const spec\<^sub>0} implies @{const spec\<^sub>0},
GNI is preserved through every pop-refinement of @{const spec\<^sub>0}.
Pop-refinement differs from the popular notion of refinement
as inclusion of sets of traces (e.g.~\cite{AbadiLamportRefinement}),
which does not preserve GNI~\cite{ClarksonSchneiderHyperproperties}.\<close>


section \<open>Stepwise Refinement\<close>
text \<open>\label{sec:refinementII}\<close>

text \<open>The remark at the beginning of \secref{sec:refinementI}
applies here as well:
the following sequence of refinement steps
may be overkill for obtaining an implementation of @{const spec\<^sub>0},
but illustrates concepts that should apply to more complex cases.\<close>


subsection \<open>Step 1\<close>

text \<open>\label{sec:refII:stepI}\<close>

text \<open>The program needs no other variables
besides those prescribed by @{const io_vars}.
Thus, @{const io_vars} is refined to a stronger condition
that constrains the program to contain exactly those variables,
in a certain order.\<close>

abbreviation vars\<^sub>0 :: "name list"
where "vars\<^sub>0 \<equiv> [''lowIn'', ''lowOut'', ''highIn'', ''highOut'']"
\<comment> \<open>The order of the variables in the list is arbitrary.\<close>

lemma vars\<^sub>0_correct:
  "vars p = vars\<^sub>0 \<Longrightarrow> io_vars p"
by (auto simp: io_vars_def ctxt_def)

text \<open>The refinement of @{const io_vars}
reduces the well-formedness of the program
to the well-formedness of the body.\<close>

abbreviation \<Gamma>\<^sub>0 :: ctxt
where "\<Gamma>\<^sub>0 \<equiv> {''lowIn'', ''lowOut'', ''highIn'', ''highOut''}"

lemma reduce_wf_prog_to_body:
  "vars p = vars\<^sub>0 \<Longrightarrow> wfp p \<longleftrightarrow> wfs \<Gamma>\<^sub>0 (body p)"
by (auto simp: wfp_def ctxt_def)

text \<open>The refinement of @{const io_vars}
induces a simplification of the processing constraints:
since the context of the program is now defined to be @{const \<Gamma>\<^sub>0},
the @{term "\<sigma> \<in> states p"} conditions are replaced
with @{term "match \<sigma> \<Gamma>\<^sub>0"} conditions.\<close>

definition low_proc_non0\<^sub>1 :: "prog \<Rightarrow> bool"
where "low_proc_non0\<^sub>1 p \<equiv>
  \<forall>\<sigma> \<sigma>'.
    match \<sigma> \<Gamma>\<^sub>0 \<and>
    the (\<sigma> ''lowIn'') \<noteq> 0 \<and>
    body p \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<longrightarrow>
    the (\<sigma>' ''lowOut'') = the (\<sigma> ''lowIn'') + 1"

lemma low_proc_non0\<^sub>1_correct:
  "vars p = vars\<^sub>0 \<Longrightarrow> low_proc_non0\<^sub>1 p \<longleftrightarrow> low_proc_non0 p"
by (auto simp: low_proc_non0\<^sub>1_def low_proc_non0_def states_def ctxt_def)

definition low_proc_0\<^sub>1 :: "prog \<Rightarrow> bool"
where "low_proc_0\<^sub>1 p \<equiv>
  \<forall>\<sigma> u.
    match \<sigma> \<Gamma>\<^sub>0 \<and>
    the (\<sigma> ''lowIn'') = 0 \<longrightarrow>
    (\<exists>\<sigma>'. body p \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<and> the (\<sigma>' ''lowOut'') = u)"

lemma low_proc_0\<^sub>1_correct:
  "vars p = vars\<^sub>0 \<Longrightarrow> low_proc_0\<^sub>1 p \<longleftrightarrow> low_proc_0 p"
by (auto simp: low_proc_0\<^sub>1_def low_proc_0_def states_def ctxt_def)

definition high_proc\<^sub>1 :: "prog \<Rightarrow> bool"
where "high_proc\<^sub>1 p \<equiv>
  \<forall>\<sigma> \<sigma>'.
    match \<sigma> \<Gamma>\<^sub>0 \<and>
    body p \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<longrightarrow>
    the (\<sigma>' ''highOut'') \<ge> the (\<sigma> ''lowIn'') + the (\<sigma> ''highIn'')"

lemma high_proc\<^sub>1_correct:
  "vars p = vars\<^sub>0 \<Longrightarrow> high_proc\<^sub>1 p \<longleftrightarrow> high_proc p"
by (auto simp: high_proc\<^sub>1_def high_proc_def states_def ctxt_def)

text \<open>The refinement of @{const spec\<^sub>0} consists of
the refinement of @{const io_vars} and of the simplified constraints.\<close>

definition spec\<^sub>1 :: "prog \<Rightarrow> bool"
where "spec\<^sub>1 p \<equiv>
  vars p = vars\<^sub>0 \<and>
  wfs \<Gamma>\<^sub>0 (body p) \<and>
  low_proc_non0\<^sub>1 p \<and>
  low_proc_0\<^sub>1 p \<and>
  high_proc\<^sub>1 p"

lemma step_1_correct:
  "spec\<^sub>1 p \<Longrightarrow> spec\<^sub>0 p"
by (auto simp:
  spec\<^sub>1_def spec\<^sub>0_def
  vars\<^sub>0_correct
  reduce_wf_prog_to_body
  low_proc_non0\<^sub>1_correct
  low_proc_0\<^sub>1_correct
  high_proc\<^sub>1_correct)


subsection \<open>Step 2\<close>

text \<open>\label{sec:refII:stepII}\<close>

text \<open>The body of the target program is split
into two sequential statements---%
one to compute the low output and one to compute the high output.\<close>

definition body_split :: "prog \<Rightarrow> stmt \<Rightarrow> stmt \<Rightarrow> bool"
where "body_split p s\<^sub>L s\<^sub>H \<equiv> body p = Seq s\<^sub>L s\<^sub>H"
\<comment> \<open>The order of the two statements in the body is arbitrary.\<close>

text \<open>The splitting reduces the well-formedness of the body
to the well-formedness of the two statements.\<close>

lemma reduce_wf_body_to_stmts:
  "body_split p s\<^sub>L s\<^sub>H \<Longrightarrow> wfs \<Gamma>\<^sub>0 (body p) \<longleftrightarrow> wfs \<Gamma>\<^sub>0 s\<^sub>L \<and> wfs \<Gamma>\<^sub>0 s\<^sub>H"
by (auto simp: body_split_def)

text \<open>The processing predicates over programs
are refined to predicates over the statements @{term s\<^sub>L} and @{term s\<^sub>H}.
Since @{term s\<^sub>H} follows @{term s\<^sub>L}:
\begin{itemize}
\item
@{term s\<^sub>H} must not change the low output, which is computed by @{term s\<^sub>L}.
\item
@{term s\<^sub>L} must not change the low and high inputs, which are used by @{term s\<^sub>H}.
\end{itemize}\<close>

definition low_proc_non0\<^sub>2 :: "stmt \<Rightarrow> bool"
where "low_proc_non0\<^sub>2 s\<^sub>L \<equiv>
  \<forall>\<sigma> \<sigma>'.
    match \<sigma> \<Gamma>\<^sub>0 \<and>
    the (\<sigma> ''lowIn'') \<noteq> 0 \<and>
    s\<^sub>L \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<longrightarrow>
    the (\<sigma>' ''lowOut'') = the (\<sigma> ''lowIn'') + 1"

definition low_proc_0\<^sub>2 :: "stmt \<Rightarrow> bool"
where "low_proc_0\<^sub>2 s\<^sub>L \<equiv>
  \<forall>\<sigma> u.
    match \<sigma> \<Gamma>\<^sub>0 \<and>
    the (\<sigma> ''lowIn'') = 0 \<longrightarrow>
    (\<exists>\<sigma>'. s\<^sub>L \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<and> the (\<sigma>' ''lowOut'') = u)"

definition low_proc_no_input_change :: "stmt \<Rightarrow> bool"
where "low_proc_no_input_change s\<^sub>L \<equiv>
  \<forall>\<sigma> \<sigma>'.
    match \<sigma> \<Gamma>\<^sub>0 \<and>
    s\<^sub>L \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<longrightarrow>
    the (\<sigma>' ''lowIn'') = the (\<sigma> ''lowIn'') \<and>
    the (\<sigma>' ''highIn'') = the (\<sigma> ''highIn'')"

definition high_proc\<^sub>2 :: "stmt \<Rightarrow> bool"
where "high_proc\<^sub>2 s\<^sub>H \<equiv>
  \<forall>\<sigma> \<sigma>'.
    match \<sigma> \<Gamma>\<^sub>0 \<and>
    s\<^sub>H \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<longrightarrow>
    the (\<sigma>' ''highOut'') \<ge> the (\<sigma> ''lowIn'') + the (\<sigma> ''highIn'')"

definition high_proc_no_low_output_change :: "stmt \<Rightarrow> bool"
where "high_proc_no_low_output_change s\<^sub>H \<equiv>
  \<forall>\<sigma> \<sigma>'.
    match \<sigma> \<Gamma>\<^sub>0 \<and>
    s\<^sub>H \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<longrightarrow>
    the (\<sigma>' ''lowOut'') = the (\<sigma> ''lowOut'')"

lemma proc\<^sub>2_correct:
  assumes Body: "body_split p s\<^sub>L s\<^sub>H"
  assumes WfLow: "wfs \<Gamma>\<^sub>0 s\<^sub>L"
  assumes WfHigh: "wfs \<Gamma>\<^sub>0 s\<^sub>H"
  assumes LowNon0: "low_proc_non0\<^sub>2 s\<^sub>L"
  assumes Low0: "low_proc_0\<^sub>2 s\<^sub>L"
  assumes LowSame: "low_proc_no_input_change s\<^sub>L"
  assumes High: "high_proc\<^sub>2 s\<^sub>H"
  assumes HighSame: "high_proc_no_low_output_change s\<^sub>H"
  shows "low_proc_non0\<^sub>1 p \<and> low_proc_0\<^sub>1 p \<and> high_proc\<^sub>1 p"
proof (auto, goal_cases)
  \<comment> \<open>Processing of non-0 low input:\<close>
  case 1
  show ?case
  proof (auto simp: low_proc_non0\<^sub>1_def)
    fix \<sigma> \<sigma>'
    assume "body p \<rhd> \<sigma> \<leadsto> Some \<sigma>'"
    with Body
    obtain \<sigma>\<^sub>i
    where ExecLow: "s\<^sub>L \<rhd> \<sigma> \<leadsto> Some \<sigma>\<^sub>i"
    and ExecHigh: "s\<^sub>H \<rhd> \<sigma>\<^sub>i \<leadsto> Some \<sigma>'"
    by (auto simp: body_split_def elim: exec.cases)
    assume Non0: "the (\<sigma> ''lowIn'') > 0"
    assume InitMatch: "match \<sigma> \<Gamma>\<^sub>0"
    with ExecLow WfLow
    have "match \<sigma>\<^sub>i \<Gamma>\<^sub>0"
    by (auto simp: exec_wfs_match)
    with Non0 InitMatch ExecLow ExecHigh HighSame LowNon0
    show "the (\<sigma>' ''lowOut'') = Suc (the (\<sigma> ''lowIn''))"
    unfolding high_proc_no_low_output_change_def low_proc_non0\<^sub>2_def
    by (metis Suc_eq_plus1 gr_implies_not0)
  qed
next
  \<comment> \<open>Processing of 0 low input:\<close>
  case 2
  show ?case
  proof (auto simp: low_proc_0\<^sub>1_def)
    fix \<sigma> u
    assume InitMatch: "match \<sigma> \<Gamma>\<^sub>0"
    and "the (\<sigma> ''lowIn'') = 0"
    with Low0
    obtain \<sigma>\<^sub>i
    where ExecLow: "s\<^sub>L \<rhd> \<sigma> \<leadsto> Some \<sigma>\<^sub>i"
    and LowOut: "the (\<sigma>\<^sub>i ''lowOut'') = u"
    by (auto simp: low_proc_0\<^sub>2_def)
    from InitMatch ExecLow WfLow
    have MidMatch: "match \<sigma>\<^sub>i \<Gamma>\<^sub>0"
    by (auto simp: exec_wfs_match)
    with WfHigh
    obtain \<sigma>'
    where ExecHigh: "s\<^sub>H \<rhd> \<sigma>\<^sub>i \<leadsto> Some \<sigma>'"
    by (metis exec_wfs_always_match)
    with HighSame MidMatch
    have "the (\<sigma>' ''lowOut'') = the (\<sigma>\<^sub>i ''lowOut'')"
    by (auto simp: high_proc_no_low_output_change_def)
    with ExecLow ExecHigh Body LowOut
    show "\<exists>\<sigma>'. body p \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<and> the (\<sigma>' ''lowOut'') = u"
    by (auto simp add: body_split_def dest: ExecSeqOK)
  qed
next
  \<comment> \<open>Processing of high input:\<close>
  case 3
  show ?case
  proof (auto simp: high_proc\<^sub>1_def)
    fix \<sigma> \<sigma>'
    assume "body p \<rhd> \<sigma> \<leadsto> Some \<sigma>'"
    with Body
    obtain \<sigma>\<^sub>i
    where ExecLow: "s\<^sub>L \<rhd> \<sigma> \<leadsto> Some \<sigma>\<^sub>i"
    and ExecHigh: "s\<^sub>H \<rhd> \<sigma>\<^sub>i \<leadsto> Some \<sigma>'"
    by (auto simp: body_split_def elim: exec.cases)
    assume InitMatch: "match \<sigma> \<Gamma>\<^sub>0"
    with ExecLow WfLow
    have "match \<sigma>\<^sub>i \<Gamma>\<^sub>0"
    by (auto simp: exec_wfs_match)
    with InitMatch ExecLow ExecHigh LowSame High
    show "the (\<sigma>' ''highOut'') \<ge> the (\<sigma> ''lowIn'') + the (\<sigma> ''highIn'')"
    unfolding low_proc_no_input_change_def high_proc\<^sub>2_def
    by metis
  qed
qed

text \<open>The refined specification consists of
the splitting of the body into the two sequential statements
and the refined well-formedness and processing constraints.\<close>

definition spec\<^sub>2 :: "prog \<Rightarrow> bool"
where "spec\<^sub>2 p \<equiv>
  vars p = vars\<^sub>0 \<and>
  (\<exists>s\<^sub>L s\<^sub>H.
    body_split p s\<^sub>L s\<^sub>H \<and>
    wfs \<Gamma>\<^sub>0 s\<^sub>L \<and>
    wfs \<Gamma>\<^sub>0 s\<^sub>H \<and>
    low_proc_non0\<^sub>2 s\<^sub>L \<and>
    low_proc_0\<^sub>2 s\<^sub>L \<and>
    low_proc_no_input_change s\<^sub>L \<and>
    high_proc\<^sub>2 s\<^sub>H \<and>
    high_proc_no_low_output_change s\<^sub>H)"

lemma step_2_correct:
  "spec\<^sub>2 p \<Longrightarrow> spec\<^sub>1 p"
by (auto simp: spec\<^sub>2_def spec\<^sub>1_def reduce_wf_body_to_stmts proc\<^sub>2_correct)


subsection \<open>Step 3\<close>

text \<open>\label{sec:refII:stepIII}\<close>

text \<open>The processing constraints
@{const low_proc_non0\<^sub>2} and @{const low_proc_0\<^sub>2} on @{term s\<^sub>L}
suggest the use of a conditional that
randomizes @{term "''lowOut''"} if @{term "''lowIn''"} is 0,
and stores 1 plus @{term "''lowIn''"} into @{term "''lowOut''"} otherwise.\<close>

abbreviation s\<^sub>L\<^sub>0 :: stmt
where "s\<^sub>L\<^sub>0 \<equiv>
  IfEq
    (Var ''lowIn'')
    (Const 0)
    (Random ''lowOut'')
    (Assign ''lowOut'' (Add (Var ''lowIn'') (Const 1)))"

lemma wfs_s\<^sub>L\<^sub>0:
  "wfs \<Gamma>\<^sub>0 s\<^sub>L\<^sub>0"
by auto

lemma low_proc_non0_s\<^sub>L\<^sub>0:
  "low_proc_non0\<^sub>2 s\<^sub>L\<^sub>0"
proof (auto simp only: low_proc_non0\<^sub>2_def)
  fix \<sigma> \<sigma>'
  assume Match: "match \<sigma> \<Gamma>\<^sub>0"
  assume "s\<^sub>L\<^sub>0 \<rhd> \<sigma> \<leadsto> Some \<sigma>'"
  and "the (\<sigma> ''lowIn'') > 0"
  hence "(Assign ''lowOut'' (Add (Var ''lowIn'') (Const 1))) \<rhd> \<sigma> \<leadsto> Some \<sigma>'"
  by (auto elim: exec.cases)
  hence "\<sigma>' = \<sigma> (''lowOut'' \<mapsto> the (eval \<sigma> (Add (Var ''lowIn'') (Const 1))))"
  by (auto elim: exec.cases)
  with Match
  show "the (\<sigma>' ''lowOut'') = the (\<sigma> ''lowIn'') + 1"
  by (auto simp: match_def add_opt_def split: option.split)
qed

lemma low_proc_0_s\<^sub>L\<^sub>0:
  "low_proc_0\<^sub>2 s\<^sub>L\<^sub>0"
proof (auto simp only: low_proc_0\<^sub>2_def)
  fix \<sigma> u
  assume Match: "match \<sigma> \<Gamma>\<^sub>0"
  and "the (\<sigma> ''lowIn'') = 0"
  hence LowIn0: "\<sigma> ''lowIn'' = Some 0"
  by (cases "\<sigma> ''lowIn''", auto simp: match_def)
  from Match
  have "''lowOut'' \<in> dom \<sigma>"
  by (auto simp: match_def)
  then obtain \<sigma>'
  where ExecRand: "Random ''lowOut'' \<rhd> \<sigma> \<leadsto> Some \<sigma>'"
  and "\<sigma>' = \<sigma> (''lowOut'' \<mapsto> u)"
  by (auto intro: ExecRandomOK)
  hence "the (\<sigma>' ''lowOut'') = u"
  by auto
  with ExecRand LowIn0
  show "\<exists>\<sigma>'. s\<^sub>L\<^sub>0 \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<and> the (\<sigma>' ''lowOut'') = u"
  by (metis ExecCondTrue eval.simps(1) eval.simps(2))
qed

lemma low_proc_no_input_change_s\<^sub>L\<^sub>0:
  "low_proc_no_input_change s\<^sub>L\<^sub>0"
proof (unfold low_proc_no_input_change_def, clarify)
  fix \<sigma> \<sigma>'
  assume "s\<^sub>L\<^sub>0 \<rhd> \<sigma> \<leadsto> Some \<sigma>'"
  hence "
    Random ''lowOut'' \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<or>
    Assign ''lowOut'' (Add (Var ''lowIn'') (Const 1)) \<rhd> \<sigma> \<leadsto> Some \<sigma>'"
  by (auto elim: exec.cases)
  thus "
    the (\<sigma>' ''lowIn'') = the (\<sigma> ''lowIn'') \<and>
    the (\<sigma>' ''highIn'') = the (\<sigma> ''highIn'')"
  by (auto elim: exec.cases)
qed

text \<open>The refined specification is obtained
by simplification using the definition of @{term s\<^sub>L}.\<close>

definition spec\<^sub>3 :: "prog \<Rightarrow> bool"
where "spec\<^sub>3 p \<equiv>
  vars p = vars\<^sub>0 \<and>
  (\<exists>s\<^sub>H.
    body_split p s\<^sub>L\<^sub>0 s\<^sub>H \<and>
    wfs \<Gamma>\<^sub>0 s\<^sub>H \<and>
    high_proc\<^sub>2 s\<^sub>H \<and>
    high_proc_no_low_output_change s\<^sub>H)"

lemma step_3_correct:
  "spec\<^sub>3 p \<Longrightarrow> spec\<^sub>2 p"
unfolding spec\<^sub>3_def spec\<^sub>2_def
by (metis
  wfs_s\<^sub>L\<^sub>0 low_proc_non0_s\<^sub>L\<^sub>0 low_proc_0_s\<^sub>L\<^sub>0 low_proc_no_input_change_s\<^sub>L\<^sub>0)

text \<open>The non-determinism required by @{const low_proc_0}
cannot be pop-refined away.
In particular, @{term s\<^sub>L} cannot be defined
to copy the high input to the low output when the low input is 0,
which would lead to a program that does not satisfy GNI.\<close>


subsection \<open>Step 4\<close>

text \<open>\label{sec:refII:stepIV}\<close>

text \<open>The processing constraint @{const high_proc\<^sub>2} on @{term s\<^sub>H}
can be satisfied in different ways.
A simple way is to pick the sum of the low and high inputs:
@{const high_proc\<^sub>2} is refined by replacing the inequality with an equality.\<close>

definition high_proc\<^sub>4 :: "stmt \<Rightarrow> bool"
where "high_proc\<^sub>4 s\<^sub>H \<equiv>
  \<forall>\<sigma> \<sigma>'.
    match \<sigma> \<Gamma>\<^sub>0 \<and>
    s\<^sub>H \<rhd> \<sigma> \<leadsto> Some \<sigma>' \<longrightarrow>
    the (\<sigma>' ''highOut'') = the (\<sigma> ''lowIn'') + the (\<sigma> ''highIn'')"

lemma high_proc\<^sub>4_correct:
  "high_proc\<^sub>4 s\<^sub>H \<Longrightarrow> high_proc\<^sub>2 s\<^sub>H"
by (auto simp: high_proc\<^sub>4_def high_proc\<^sub>2_def)

text \<open>The refined specification is obtained
by substituting the refined processing constraint on @{term s\<^sub>H}.\<close>

definition spec\<^sub>4 :: "prog \<Rightarrow> bool"
where "spec\<^sub>4 p \<equiv>
  vars p = vars\<^sub>0 \<and>
  (\<exists>s\<^sub>H.
    body_split p s\<^sub>L\<^sub>0 s\<^sub>H \<and>
    wfs \<Gamma>\<^sub>0 s\<^sub>H \<and>
    high_proc\<^sub>4 s\<^sub>H \<and>
    high_proc_no_low_output_change s\<^sub>H)"

lemma step_4_correct:
  "spec\<^sub>4 p \<Longrightarrow> spec\<^sub>3 p"
by (auto simp: spec\<^sub>4_def spec\<^sub>3_def high_proc\<^sub>4_correct)


subsection \<open>Step 5\<close>

text \<open>\label{sec:refII:stepV}\<close>

text \<open>The refined processing constraint @{const high_proc\<^sub>4} on @{term s\<^sub>H}
suggest the use of an assignment that
stores the sum of @{term "''lowIn''"} and @{term "''highIn''"}
into @{term "''highOut''"}.\<close>

abbreviation s\<^sub>H\<^sub>0 :: stmt
where "s\<^sub>H\<^sub>0 \<equiv> Assign ''highOut'' (Add (Var ''lowIn'') (Var ''highIn''))"

lemma wfs_s\<^sub>H\<^sub>0:
  "wfs \<Gamma>\<^sub>0 s\<^sub>H\<^sub>0"
by auto

lemma high_proc\<^sub>4_s\<^sub>H\<^sub>0:
  "high_proc\<^sub>4 s\<^sub>H\<^sub>0"
proof (auto simp: high_proc\<^sub>4_def)
  fix \<sigma> \<sigma>'
  assume Match: "match \<sigma> \<Gamma>\<^sub>0"
  assume "s\<^sub>H\<^sub>0 \<rhd> \<sigma> \<leadsto> Some \<sigma>'"
  hence "
    \<sigma>' = \<sigma> (''highOut'' \<mapsto> the (eval \<sigma> (Add (Var ''lowIn'') (Var ''highIn''))))"
  by (auto elim: exec.cases)
  with Match
  show "the (\<sigma>' ''highOut'') = the (\<sigma> ''lowIn'') + the (\<sigma> ''highIn'')"
  by (auto simp: match_def add_opt_def split: option.split)
qed

lemma high_proc_no_low_output_change_s\<^sub>H\<^sub>0:
  "high_proc_no_low_output_change s\<^sub>H\<^sub>0"
by (auto simp: high_proc_no_low_output_change_def elim: exec.cases)

text \<open>The refined specification is obtained
by simplification using the definition of @{term s\<^sub>H}.\<close>

definition spec\<^sub>5 :: "prog \<Rightarrow> bool"
where "spec\<^sub>5 p \<equiv> vars p = vars\<^sub>0 \<and> body_split p s\<^sub>L\<^sub>0 s\<^sub>H\<^sub>0"

lemma step_5_correct:
  "spec\<^sub>5 p \<Longrightarrow> spec\<^sub>4 p"
unfolding spec\<^sub>5_def spec\<^sub>4_def
by (metis wfs_s\<^sub>H\<^sub>0 high_proc\<^sub>4_s\<^sub>H\<^sub>0 high_proc_no_low_output_change_s\<^sub>H\<^sub>0)


subsection \<open>Step 6\<close>

text \<open>\label{sec:refII:stepVI}\<close>

text \<open>@{const spec\<^sub>5}, which defines the variables and the body,
is refined to characterize a unique program in explicit syntactic form.\<close>

abbreviation p\<^sub>0 :: prog
where "p\<^sub>0 \<equiv> \<lparr>vars = vars\<^sub>0, body = Seq s\<^sub>L\<^sub>0 s\<^sub>H\<^sub>0\<rparr>"

definition spec\<^sub>6 :: "prog \<Rightarrow> bool"
where "spec\<^sub>6 p \<equiv> p = p\<^sub>0"

lemma step_6_correct:
  "spec\<^sub>6 p \<Longrightarrow> spec\<^sub>5 p"
by (auto simp: spec\<^sub>6_def spec\<^sub>5_def body_split_def)

text \<open>The program satisfies @{const spec\<^sub>0} by construction.
The program witnesses the consistency of the requirements,
i.e.\ the fact that @{const spec\<^sub>0} is not always false.\<close>

lemma p\<^sub>0_sat_spec\<^sub>0:
  "spec\<^sub>0 p\<^sub>0"
by (metis
 step_1_correct
 step_2_correct
 step_3_correct
 step_4_correct
 step_5_correct
 step_6_correct
 spec\<^sub>6_def)

text \<open>From @{const p\<^sub>0}, the program text
\begin{verbatim}
  prog {
    vars {
      lowIn
      lowOut
      highIn
      highOut
    }
    body {
      if (lowIn == 0) {
        randomize lowOut;
      } else {
        lowOut = lowIn + 1;
      }
      highOut = lowIn + highIn;
    }
  }
\end{verbatim}
is easily obtained.\<close>


end %invisible
