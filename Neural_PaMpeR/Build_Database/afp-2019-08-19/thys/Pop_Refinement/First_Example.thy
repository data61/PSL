chapter \<open>First Example\<close>

theory %invisible First_Example
imports Main
begin

text \<open>\label{chap:exampleI}\<close>

text \<open>Pop-refinement is illustrated via a simple derivation,
in Isabelle/HOL,
of a program that includes non-functional aspects.\<close>


section \<open>Target Programming Language\<close>
text \<open>\label{sec:targetI}\<close>

text \<open>In the target language used in this example,
a program consists of
a list of distinct variables (the parameters of the program)
and an arithmetic expression (the body of the program).
The body is built out of
parameters,
non-negative integer constants,
addition operations,
and doubling (i.e.\ multiplication by 2) operations.
The program is executed
by supplying non-negative integers to the parameters
and evaluating the body to obtain a non-negative integer result.\<close>

text \<open>For instance, executing the program
\begin{verbatim}
  prog (a,b) {3 + 2 * (a + b)}
\end{verbatim}
with 5 and 7 supplied to \verb|a| and \verb|b| yields 27.
The syntax and semantics of this language are formalized as follows.\<close>


subsection \<open>Syntax\<close>
text \<open>\label{sec:syntaxI}\<close>

text \<open>Variables are identified by names.\<close>

type_synonym name = string

text \<open>Expressions are built out of
constants, variables, doubling operations, and addition operations.\<close>

datatype expr = Const nat | Var name | Double expr | Add expr expr

text \<open>A program consists of
a list of parameter variables and a body expression.\<close>

record prog =
 para :: "name list"
 body :: expr


subsection \<open>Static Semantics\<close>
text \<open>\label{sec:staticI}\<close>

text \<open>A context is a set of variables.\<close>

type_synonym ctxt = "name set"

text \<open>Given a context,
an expression is well-formed iff\
all its variables are in the context.\<close>

fun wfe :: "ctxt \<Rightarrow> expr \<Rightarrow> bool"
where
  "wfe \<Gamma> (Const c) \<longleftrightarrow> True" |
  "wfe \<Gamma> (Var v) \<longleftrightarrow> v \<in> \<Gamma>" |
  "wfe \<Gamma> (Double e) \<longleftrightarrow> wfe \<Gamma> e" |
  "wfe \<Gamma> (Add e\<^sub>1 e\<^sub>2) \<longleftrightarrow> wfe \<Gamma> e\<^sub>1 \<and> wfe \<Gamma> e\<^sub>2"

text \<open>The context of a program consists of the parameters.\<close>

definition ctxt :: "prog \<Rightarrow> ctxt"
where "ctxt p \<equiv> set (para p)"

text \<open>A program is well-formed iff\
the parameters are distinct
and the body is well-formed in the context of the program.\<close>

definition wfp :: "prog \<Rightarrow> bool"
where "wfp p \<equiv> distinct (para p) \<and> wfe (ctxt p) (body p)"


subsection \<open>Dynamic Semantics\<close>
text \<open>\label{sec:dynamicI}\<close>

text \<open>An environment associates values (non-negative integers)
to variables.\<close>

type_synonym env = "name \<rightharpoonup> nat"

text \<open>An environment matches a context iff\
environment and context have the same variables.\<close>

definition match :: "env \<Rightarrow> ctxt \<Rightarrow> bool"
where "match \<E> \<Gamma> \<equiv> dom \<E> = \<Gamma>"

text \<open>Evaluating an expression in an environment yields a value,
or an error (@{const None})
if the expression contains a variable not in the environment.\<close>

definition mul_opt :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option" (infixl "\<otimes>" 70)
\<comment> \<open>Lifting of multiplication to @{typ "nat option"}.\<close>
where "U\<^sub>1 \<otimes> U\<^sub>2 \<equiv>
  case (U\<^sub>1, U\<^sub>2) of (Some u\<^sub>1, Some u\<^sub>2) \<Rightarrow> Some (u\<^sub>1 * u\<^sub>2) | _ \<Rightarrow> None"

definition add_opt :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option" (infixl "\<oplus>" 65)
\<comment> \<open>Lifting of addition to @{typ "nat option"}.\<close>
where "U\<^sub>1 \<oplus> U\<^sub>2 \<equiv>
  case (U\<^sub>1, U\<^sub>2) of (Some u\<^sub>1, Some u\<^sub>2) \<Rightarrow> Some (u\<^sub>1 + u\<^sub>2) | _ \<Rightarrow> None"

fun eval :: "env \<Rightarrow> expr \<Rightarrow> nat option"
where
  "eval \<E> (Const c) = Some c" |
  "eval \<E> (Var v) = \<E> v" |
  "eval \<E> (Double e) = Some 2 \<otimes> eval \<E> e" |
  "eval \<E> (Add e\<^sub>1 e\<^sub>2) = eval \<E> e\<^sub>1 \<oplus> eval \<E> e\<^sub>2"

text \<open>Evaluating a well-formed expression never yields an error,
if the environment matches the context.\<close>

lemma eval_wfe:
  "wfe \<Gamma> e \<Longrightarrow> match \<E> \<Gamma> \<Longrightarrow> eval \<E> e \<noteq> None"
by (induct e, auto simp: match_def mul_opt_def add_opt_def)

text \<open>The environments of a program
are the ones that match the context of the program.\<close>

definition envs :: "prog \<Rightarrow> env set"
where "envs p \<equiv> {\<E>. match \<E> (ctxt p)}"

text \<open>Evaluating the body of a well-formed program
in an environment of the program
never yields an error.\<close>

lemma eval_wfp:
  "wfp p \<Longrightarrow> \<E> \<in> envs p \<Longrightarrow> eval \<E> (body p) \<noteq> None"
by (metis envs_def eval_wfe mem_Collect_eq wfp_def)

text \<open>Executing a program with values supplied to the parameters
yields a non-negative integer result,
or an error (@{const None})
if the parameters are not distinct,
the number of supplied values differs from the number of parameters,
or the evaluation of the body yields an error.\<close>

definition "supply" :: "prog \<Rightarrow> nat list \<Rightarrow> env option"
where "supply p us \<equiv>
  let vs = para p in
  if distinct vs \<and> length us = length vs
  then Some (map_of (zip vs us))
  else None"

definition exec :: "prog \<Rightarrow> nat list \<Rightarrow> nat option"
where "exec p us \<equiv>
  case supply p us of Some \<E> \<Rightarrow> eval \<E> (body p) | None \<Rightarrow> None"

text \<open>Executing a well-formed program
with the same number of values as the number of parameters
never yields an error.\<close>

lemma supply_wfp: "
  wfp p \<Longrightarrow>
  length us = length (para p) \<Longrightarrow>
  \<exists>\<E> \<in> envs p. supply p us = Some \<E>"
by (auto
 simp: wfp_def supply_def envs_def ctxt_def match_def split: option.split)

lemma exec_wfp:
  "wfp p \<Longrightarrow> length us = length (para p) \<Longrightarrow> exec p us \<noteq> None"
by (metis eval_wfp exec_def option.simps(5) supply_wfp)


subsection \<open>Performance\<close>
text \<open>\label{sec:nonfunc}\<close>

text \<open>As a non-functional semantic aspect,
the cost (e.g.\ time and power) to execute a program
is modeled as the number of doubling and addition operations.\<close>

fun coste :: "expr \<Rightarrow> nat"
where
  "coste (Const c) = 0" |
  "coste (Var v) = 0" |
  "coste (Double e) = 1 + coste e" |
  "coste (Add e\<^sub>1 e\<^sub>2) = 1 + coste e\<^sub>1 + coste e\<^sub>2"

definition costp :: "prog \<Rightarrow> nat"
where "costp p \<equiv> coste (body p)"


section \<open>Requirement Specification\<close>
text \<open>\label{sec:specificationI}\<close>

text \<open>The target program must:
\begin{enumerate}
\item
Be well-formed.
\item
Have exactly the two parameters @{term "''x''"} and @{term "''y''"},
in this order.
\item
Produce the result @{term "f x y"}
when @{term x} and @{term y}
are supplied to @{term "''x''"} and @{term "''y''"},
where @{term f} is defined below.
\item
Not exceed cost 3.
\end{enumerate}\<close>

definition f :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where "f x y \<equiv> 3 * x + 2 * y"

definition spec\<^sub>0 :: "prog \<Rightarrow> bool"
where "spec\<^sub>0 p \<equiv>
  wfp p \<and>
  para p = [''x'', ''y''] \<and>
  (\<forall>x y. exec p [x, y] = Some (f x y)) \<and>
  costp p \<le> 3"

text \<open>@{const f} is used by @{const spec\<^sub>0}
to express a functional requirement on the execution of the program.
@{const spec\<^sub>0} includes
the non-functional requirement @{term "costp(p) \<le> 3"}
and the syntactic interface requirement @{term "para(p) = [''x'', ''y'']"},
which are not expressed by @{const f} alone
and are expressible only in terms of programs.
@{const f} can be computed by a program
with cost higher than 3
and with more or different parameters;
it can also be computed by programs in different target languages.\<close>


section \<open>Stepwise Refinement\<close>
text \<open>\label{sec:refinementI}\<close>

text \<open>It is not difficult
to write a program that satisfies @{const spec\<^sub>0} and to prove that it does.
But with more complex target languages and requirement specifications,
writing a program and proving that it satisfies the requirements
is notoriously difficult.
Stepwise refinement decomposes the proof into manageable pieces,
constructing the implementation along the way.
The following sequence of refinement steps
may be overkill for obtaining an implementation of @{const spec\<^sub>0},
but illustrates concepts that should apply to more complex cases.\<close>


subsection \<open>Step 1\<close>
text \<open>\label{sec:refI:stepI}\<close>

text \<open>The second conjunct in @{const spec\<^sub>0} determines the parameters,
leaving only the body to be determined.
That conjunct also reduces
the well-formedness of the program to the well-formedness of the body,
and the execution of the program to the evaluation of the body.\<close>

abbreviation \<Gamma>\<^sub>x\<^sub>y :: ctxt
where "\<Gamma>\<^sub>x\<^sub>y \<equiv> {''x'', ''y''}"

abbreviation \<E>\<^sub>x\<^sub>y :: "nat \<Rightarrow> nat \<Rightarrow> env"
where "\<E>\<^sub>x\<^sub>y x y \<equiv> [''x'' \<mapsto> x, ''y'' \<mapsto> y]"

lemma reduce_prog_to_body: "
  para p = [''x'', ''y''] \<Longrightarrow>
  wfp p = wfe \<Gamma>\<^sub>x\<^sub>y (body p) \<and>
  exec p [x, y] = eval (\<E>\<^sub>x\<^sub>y x y) (body p)"
by (auto simp: wfp_def ctxt_def exec_def supply_def fun_upd_twist)

text \<open>Using lemma \<open>reduce_prog_to_body\<close>,
and using the definition of @{const costp}
to reduce the cost of the program to the cost of the body,
@{const spec\<^sub>0} is refined as follows.\<close>

definition spec\<^sub>1 :: "prog \<Rightarrow> bool"
where "spec\<^sub>1 p \<equiv>
  wfe \<Gamma>\<^sub>x\<^sub>y (body p) \<and>
  para p = [''x'', ''y''] \<and>
  (\<forall>x y. eval (\<E>\<^sub>x\<^sub>y x y) (body p) = Some (f x y)) \<and>
  coste (body p) \<le> 3"

lemma step_1_correct:
 "spec\<^sub>1 p \<Longrightarrow> spec\<^sub>0 p"
by (auto simp: spec\<^sub>1_def spec\<^sub>0_def reduce_prog_to_body costp_def)

text \<open>@{const spec\<^sub>1} and @{const spec\<^sub>0} are actually equivalent,
but the definition of @{const spec\<^sub>1} is ``closer'' to the implementation
than the definition of @{const spec\<^sub>0}:
the latter states constraints on the whole program,
while the former states simpler constraints on the body,
given that the parameters are already determined.
The proof of \<open>step_1_correct\<close>
can also be used to prove the equivalence of @{const spec\<^sub>1} and @{const spec\<^sub>0},
but in general proving inclusion is easier than proving equivalence.
Some of the following refinement steps yield non-equivalent predicates.\<close>


subsection \<open>Step 2\<close>
text \<open>\label{sec:refI:stepII}\<close>

text \<open>The third conjunct in @{const spec\<^sub>1} says that
the body computes @{term "f x y"},
which depends on both @{term x} and @{term y},
and which yields an odd result for some values of @{term x} and @{term y}.
Thus the body cannot be a constant, a variable, or a double,
leaving a sum as the only option.
Adding @{term "\<exists>e\<^sub>1 e\<^sub>2. body p = Add e\<^sub>1 e\<^sub>2"} as a conjunct to @{const spec\<^sub>1}
and re-arranging the other conjuncts,
moving some of them under the existential quantification
so that they can be simplified in the next refinement step,
@{const spec\<^sub>1} is refined as follows.\<close>

definition spec\<^sub>2 :: "prog \<Rightarrow> bool"
where "spec\<^sub>2 p \<equiv>
  para p = [''x'', ''y''] \<and>
  (\<exists>e\<^sub>1 e\<^sub>2.
    body p = Add e\<^sub>1 e\<^sub>2 \<and>
    wfe \<Gamma>\<^sub>x\<^sub>y (body p) \<and>
    (\<forall>x y. eval (\<E>\<^sub>x\<^sub>y x y) (body p) = Some (f x y)) \<and>
    coste (body p) \<le> 3)"

lemma step_2_correct:
 "spec\<^sub>2 p \<Longrightarrow> spec\<^sub>1 p"
by (auto simp: spec\<^sub>2_def spec\<^sub>1_def)

text \<open>This refinement step is guided by an analysis
of the constraints in @{const spec\<^sub>1}.\<close>


subsection \<open>Step 3\<close>
text \<open>\label{sec:refI:stepIII}\<close>

text \<open>The fact that the body is a sum
reduces the well-formedness, evaluation, and cost of the body
to the well-formedness, evaluation, and cost of the addends.\<close>

lemma reduce_body_to_addends: "
  body p = Add e\<^sub>1 e\<^sub>2 \<Longrightarrow>
  wfe \<Gamma>\<^sub>x\<^sub>y (body p) = (wfe \<Gamma>\<^sub>x\<^sub>y e\<^sub>1 \<and> wfe \<Gamma>\<^sub>x\<^sub>y e\<^sub>2) \<and>
  eval (\<E>\<^sub>x\<^sub>y x y) (body p) = eval (\<E>\<^sub>x\<^sub>y x y) e\<^sub>1 \<oplus> eval (\<E>\<^sub>x\<^sub>y x y) e\<^sub>2 \<and>
  coste (body p) = 1 + coste e\<^sub>1 + coste e\<^sub>2"
by auto

text \<open>Using \<open>reduce_body_to_addends\<close>
and arithmetic simplification,
@{const spec\<^sub>2} is refined as follows.\<close>

definition spec\<^sub>3 :: "prog \<Rightarrow> bool"
where "spec\<^sub>3 p \<equiv>
  para p = [''x'', ''y''] \<and>
  (\<exists>e\<^sub>1 e\<^sub>2.
    body p = Add e\<^sub>1 e\<^sub>2 \<and>
    wfe \<Gamma>\<^sub>x\<^sub>y e\<^sub>1 \<and>
    wfe \<Gamma>\<^sub>x\<^sub>y e\<^sub>2 \<and>
    (\<forall>x y. eval (\<E>\<^sub>x\<^sub>y x y) e\<^sub>1 \<oplus> eval (\<E>\<^sub>x\<^sub>y x y) e\<^sub>2 = Some (f x y)) \<and>
    coste e\<^sub>1 + coste e\<^sub>2 \<le> 2)"

lemma step_3_correct:
  "spec\<^sub>3 p \<Longrightarrow> spec\<^sub>2 p"
by (auto simp: spec\<^sub>3_def spec\<^sub>2_def)
\<comment> \<open>No need to use @{text reduce_body_to_addends} explicitly,\<close>
\<comment> \<open>as the default rules that @{text auto} uses to prove it apply here too.\<close>

text \<open>This refinement step
defines the top-level structure of the body,
reducing the constraints on the body
to simpler constraints on its components.\<close>


subsection \<open>Step 4\<close>
text \<open>\label{sec:refI:stepIV}\<close>

text \<open>The second-to-last conjunct in @{const spec\<^sub>3}
suggests to split @{term "f x y"} into two addends
to be computed by @{term e\<^sub>1} and @{term e\<^sub>2}.\<close>

text \<open>The addends @{term "(3::nat) * x"} and @{term "(2::nat) * y"}
suggested by the definition of @{const f}
would lead to a blind alley,
where the cost constraints could not be satisfied---%
the resulting @{term spec\<^sub>4} would be always false.
The refinement step would be ``correct'' (by strict inclusion)
but the refinement sequence could never reach an implementation.
It would be necessary to backtrack to @{const spec\<^sub>3}
and split @{term "f x y"} differently.\<close>

text \<open>To avoid the blind alley,
the definition of @{const f} is rephrased as follows.\<close>

lemma f_rephrased:
  "f x y = x + (2 * x + 2 * y)"
by (auto simp: f_def)

text \<open>This rephrased definition of @{const f}
does not use the multiplication by 3 of the original definition,
which is not (directly) supported by the target language;
it only uses operations supported by the language.\<close>

text \<open>Using \<open>f_rephrased\<close>, @{const spec\<^sub>3} is refined as follows.\<close>

definition spec\<^sub>4 :: "prog \<Rightarrow> bool"
where "spec\<^sub>4 p \<equiv>
  para p = [''x'', ''y''] \<and>
  (\<exists>e\<^sub>1 e\<^sub>2.
    body p = Add e\<^sub>1 e\<^sub>2 \<and>
    wfe \<Gamma>\<^sub>x\<^sub>y e\<^sub>1 \<and>
    wfe \<Gamma>\<^sub>x\<^sub>y e\<^sub>2 \<and>
    (\<forall>x y. eval (\<E>\<^sub>x\<^sub>y x y) e\<^sub>1 = Some x) \<and>
    (\<forall>x y. eval (\<E>\<^sub>x\<^sub>y x y) e\<^sub>2 = Some (2 * x + 2 * y)) \<and>
    coste e\<^sub>1 + coste e\<^sub>2 \<le> 2)"

lemma step_4_correct:
  "spec\<^sub>4 p \<Longrightarrow> spec\<^sub>3 p"
by (auto simp: spec\<^sub>4_def spec\<^sub>3_def add_opt_def f_rephrased)

text \<open>This refinement step reduces
the functional constraint on the body
to simpler functional constraints on the addends.
The functional constraint can be decomposed in different ways,
some of which are incompatible with the non-functional cost constraint:
blind alleys are avoided
by taking the non-functional constraint into account.\<close>


subsection \<open>Step 5\<close>
text \<open>\label{sec:refI:stepV}\<close>

text \<open>The term @{term x}
in the third-to-last conjunct in @{const spec\<^sub>4}
is a shallow embedding of the program expression \verb|x|,
whose deep embedding is the term @{term "Var ''x''"}.
Using the latter as @{term e\<^sub>1},
the third-to-last conjunct in @{const spec\<^sub>4} is satisfied;
the expression is well-formed and has cost 0.\<close>

lemma first_addend: "
  e\<^sub>1 = Var ''x'' \<Longrightarrow>
  eval (\<E>\<^sub>x\<^sub>y x y) e\<^sub>1 = Some x \<and>
  wfe \<Gamma>\<^sub>x\<^sub>y e\<^sub>1 \<and>
  coste e\<^sub>1 = 0"
by auto

text \<open>Adding @{term "e\<^sub>1 = Var ''x''"} as a conjunct to @{const spec\<^sub>4}
and simplifying,
@{const spec\<^sub>4} is refined as follows.\<close>

definition spec\<^sub>5 :: "prog \<Rightarrow> bool"
where "spec\<^sub>5 p \<equiv>
  para p = [''x'', ''y''] \<and>
  (\<exists>e\<^sub>2.
    body p = Add (Var ''x'') e\<^sub>2 \<and>
    wfe \<Gamma>\<^sub>x\<^sub>y e\<^sub>2 \<and>
    (\<forall>x y. eval (\<E>\<^sub>x\<^sub>y x y) e\<^sub>2 = Some (2 * x + 2 * y)) \<and>
    coste e\<^sub>2 \<le> 2)"

lemma step_5_correct:
  "spec\<^sub>5 p \<Longrightarrow> spec\<^sub>4 p"
by (auto simp: spec\<^sub>5_def spec\<^sub>4_def)
\<comment> \<open>No need to use @{text first_addend} explicitly,\<close>
\<comment> \<open>as the default rules that @{text auto} uses to prove it apply here too.\<close>

text \<open>This refinement step determines the first addend of the body,
leaving only the second addend to be determined.\<close>


subsection \<open>Step 6\<close>
text \<open>\label{sec:refI:stepVI}\<close>

text \<open>The term @{term "(2::nat) * x + 2 * y"}
in the second-to-last conjunct of @{const spec\<^sub>5}
is a shallow embedding of the program expression \verb|2 * x + 2 * y|,
whose deep embedding is the term
@{term "Add (Double (Var ''x'')) (Double (Var ''y''))"}.
Using the latter as @{term e\<^sub>2},
the second-to-last conjunct in @{const spec\<^sub>5} is satisfied,
but the last conjunct is not.
The following factorization of the shallowly embedded expression
leads to a reduced cost of the corresponding deeply embedded expression.\<close>

lemma factorization:
  "(2::nat) * x + 2 * y = 2 * (x + y)"
by auto

text \<open>The deeply embedded expression
@{term "Double (Add (Var ''x'') (Var ''y''))"},
which corresponds to the shallowly embedded expression
@{term "(2::nat) * (x + y)"},
satisfies the second-to-last conjunct of @{const spec\<^sub>5},
is well-formed,
and has cost 2.\<close>

lemma second_addend: "
  e\<^sub>2 = Double (Add (Var ''x'') (Var ''y'')) \<Longrightarrow>
  eval (\<E>\<^sub>x\<^sub>y x y) e\<^sub>2 = Some (2 * x + 2 * y) \<and>
  wfe \<Gamma>\<^sub>x\<^sub>y e\<^sub>2 \<and>
  coste e\<^sub>2 = 2"
by (auto simp: add_opt_def mul_opt_def)
\<comment> \<open>No need to use @{text factorization} explicitly,\<close>
\<comment> \<open>as the default rules that @{text auto} uses to prove it apply here too.\<close>

text \<open>Adding @{term "e\<^sub>2 = Double (Add (Var ''x'') (Var ''y''))"}
as a conjunct to @{const spec\<^sub>5}
and simplifying,
@{const spec\<^sub>5} is refined as follows.\<close>

definition spec\<^sub>6 :: "prog \<Rightarrow> bool"
where "spec\<^sub>6 p \<equiv>
  para p = [''x'', ''y''] \<and>
  body p = Add (Var ''x'') (Double (Add (Var ''x'') (Var ''y'')))"

lemma step_6_correct:
  "spec\<^sub>6 p \<Longrightarrow> spec\<^sub>5 p"
by (auto simp add: spec\<^sub>6_def spec\<^sub>5_def second_addend simp del: eval.simps)

text \<open>This refinement step determines the second addend of the body,
leaving nothing else to be determined.\<close>

text \<open>This and the previous refinement step
turn semantic constraints on the program components @{term e\<^sub>1} and @{term e\<^sub>2}
into syntactic definitions of such components.\<close>


subsection \<open>Step 7\<close>
text \<open>\label{sec:refI:stepVII}\<close>

text \<open>@{const spec\<^sub>6}, which defines the parameters and body,
is refined to characterize a unique program in explicit syntactic form.\<close>

abbreviation p\<^sub>0 :: prog
where "p\<^sub>0 \<equiv>
  \<lparr>para = [''x'', ''y''],
   body = Add (Var ''x'') (Double (Add (Var ''x'') (Var ''y'')))\<rparr>"

definition spec\<^sub>7 :: "prog \<Rightarrow> bool"
where "spec\<^sub>7 p \<equiv> p = p\<^sub>0"

lemma step_7_correct:
  "spec\<^sub>7 p \<Longrightarrow> spec\<^sub>6 p"
by (auto simp: spec\<^sub>7_def spec\<^sub>6_def)

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
 step_7_correct
 spec\<^sub>7_def)

text \<open>From @{const p\<^sub>0}, the program text
\begin{verbatim}
  prog (x,y) {x + 2 * (x + y)}
\end{verbatim}
is easily obtained.\<close>


end %invisible
