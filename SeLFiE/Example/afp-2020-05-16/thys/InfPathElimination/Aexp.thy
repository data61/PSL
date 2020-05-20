theory Aexp
imports Main
begin

section\<open>Arithmetic Expressions\<close>

text \<open>In this section, we model arithmetic expressions as total functions from valuations of 
program variables to values. This modeling does not take into consideration the syntactic aspects 
of arithmetic expressions. Thus, our modeling holds for any operator. However, some classical 
notions, like the set of variables occurring in a given expression for example, must be rethought 
and defined accordingly.\<close>

subsection\<open>Variables and their domain\<close>

text \<open>\textbf{Note}: in the following theories, we distinguish the set of \emph{program variables} 
and the set 
of \emph{symbolic variables}. A number of types we define are parameterized by a type of variables. 
For example, we make a distinction between expressions (arithmetic or boolean) over program 
variables and expressions over symbolic variables. This distinction eases some parts of the following 
formalization.\<close>

paragraph \<open>Symbolic variables.\<close>

text \<open>A \emph{symbolic variable} is an indexed version of a program variable. In the following 
type-synonym, we consider that the abstract type \<open>'v\<close> represent the set of program 
variables. By set 
of program variables, we do not mean \emph{the set of variables of a given program}, but 
\emph{the set of variables of all possible programs}. This distinction justifies some of the 
modeling choices done later. Within Isabelle/HOL, nothing is known about this set. The set of 
program variables is infinite, though it is not needed to make this assumption. On the other hand, 
the set of symbolic variables is infinite, independently of the fact that the set of program 
variables is finite or not.\<close>


type_synonym 'v symvar = "'v \<times> nat"


lemma
  "\<not> finite (UNIV::'v symvar set)"
by (simp add : finite_prod)

text \<open>The previous lemma has no name and thus cannot be referenced in the following. Indeed, it is 
of no use for proving the properties we are interested in. In the following, we will give other
unnamed lemmas when we think they might help the reader to understand the ideas behind our modeling 
choices.\<close>


paragraph \<open>Domain of variables.\<close>

text \<open>We call @{term "D"} the domain of program and symbolic variables. In the following, we 
suppose that @{term "D"} is the set of integers.\<close>


subsection\<open>Program and symbolic states\<close>

text \<open>A state is a total function giving values in @{term "D"} to variables. The latter are 
represented by elements of type \<open>'v\<close>. Unlike in the \<open>'v symvar\<close> type-synonym, here 
the type \<open>'v\<close> can stand for program variables as well as symbolic variables. States over 
program variables are called \emph{program states}, and states over symbolic variables are called 
\emph{symbolic states}.\<close>
type_synonym ('v,'d) state = "'v \<Rightarrow> 'd"


subsection\<open>The \emph{aexp} type-synonym\<close>

text \<open>Arithmetic (and boolean, see \verb?Bexp.thy?) expressions are represented by their 
semantics, i.e.\ 
total functions giving values in @{term "D"} to states. This way of representing expressions has 
the benefit that it is not necessary to define the syntax of terms (and formulae) appearing 
in program statements and path predicates.\<close>

type_synonym ('v,'d) aexp =  "('v,'d) state \<Rightarrow> 'd"


text \<open>In order to represent expressions over program variables as well as symbolic variables, 
the type synonym @{type "aexp"} is parameterized by the type of variables. Arithmetic and boolean 
expressions over program variables are used to express program statements. Arithmetic and boolean 
expressions over symbolic variables are used to represent the constraints occurring in path 
predicates during symbolic execution.\<close>


subsection\<open>Variables of an arithmetic expression\<close>

text\<open>Expressions being represented by total functions, one can not say that a given variable is 
occurring in a given expression. We define the set of variables of an expression as the set of 
variables that can actually have an influence on the value associated by an expression to a state. 
For example, the set of variables of the expression @{term "\<lambda> \<sigma>. \<sigma> x - \<sigma> y"} is @{term "{x,y}"}, 
provided that @{term "x"} and @{term "y"} are distinct variables, and the empty set otherwise. In 
the second case, this expression would evaluate to $0$ for any state @{term
"\<sigma>"}. Similarly, an expression like
 @{term "\<lambda> \<sigma>.  \<sigma> x * (0::nat)"} is considered as having no
 variable as if a static evaluation of the multiplication had occurred.
\<close>


definition vars :: 
  "('v,'d) aexp \<Rightarrow> 'v set" 
where
  "vars e = {v. \<exists> \<sigma> val. e (\<sigma>(v := val)) \<noteq> e \<sigma>}"


lemma vars_example_1 :
  fixes e::"('v,integer) aexp"
  assumes "e = (\<lambda> \<sigma>. \<sigma> x - \<sigma> y)"
  assumes "x \<noteq> y"
  shows   "vars e = {x,y}"
unfolding set_eq_iff
proof (intro allI iffI)
  fix v assume "v \<in> vars e"

  then obtain \<sigma> val 
  where "e (\<sigma>(v := val)) \<noteq> e \<sigma>"
  unfolding vars_def by blast

  thus "v \<in> {x, y}" 
  using assms by (case_tac "v = x", simp, (case_tac "v = y", simp+))
next
  fix v assume "v \<in> {x,y}"

  thus "v \<in> vars e"
  using assms
  by (auto simp add : vars_def) 
     (rule_tac ?x="\<lambda> v. 0" in exI, rule_tac ?x="1" in exI, simp)+
qed


lemma vars_example_2 :
  fixes e::"('v,integer) aexp"
  assumes "e = (\<lambda> \<sigma>. \<sigma> x - \<sigma> y)"
  assumes "x = y"
  shows   "vars e = {}"
using assms by (auto simp add : vars_def)


subsection\<open>Fresh variables\<close>

text \<open>Our notion of symbolic execution suppose \emph{static single assignment 
form}. In order to symbolically execute an assignment, we require the existence of a fresh 
symbolic variable for the configuration from which symbolic execution is performed. We define here 
the notion of \emph{freshness} of a variable for an arithmetic expression.\<close>

text \<open>A variable is fresh for an expression if does not belong to its set of variables.\<close>


abbreviation fresh ::
  "'v \<Rightarrow> ('v,'d) aexp \<Rightarrow> bool" 
where
  "fresh v e \<equiv> v \<notin> vars e"
 
end
