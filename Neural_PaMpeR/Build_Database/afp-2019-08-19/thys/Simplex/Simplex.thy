(* Authors: F. Maric, M. Spasic, R. Thiemann *)
section \<open>The Simplex Algorithm\<close>

theory Simplex
  imports
    Linear_Poly_Maps
    QDelta
    Rel_Chain
    Simplex_Algebra
    "HOL-Library.RBT_Mapping"
    "HOL-Library.Permutation"
    "HOL-Library.Code_Target_Numeral"
begin

text\<open>Linear constraints are of the form \<open>p \<bowtie> c\<close> or \<open>p\<^sub>1 \<bowtie> p\<^sub>2\<close>, where \<open>p\<close>, \<open>p\<^sub>1\<close>, and \<open>p\<^sub>2\<close>, are
linear polynomials, \<open>c\<close> is a rational constant and \<open>\<bowtie> \<in>
{<, >, \<le>, \<ge>, =}\<close>. Their abstract syntax is given by the \<open>constraint\<close> type, and semantics is given by the relation \<open>\<Turnstile>\<^sub>c\<close>, defined straightforwardly by primitive recursion over the
\<open>constraint\<close> type. A set of constraints is satisfied,
denoted by \<open>\<Turnstile>\<^sub>c\<^sub>s\<close>, if all constraints are. There is also an indexed
version \<open>\<Turnstile>\<^sub>i\<^sub>c\<^sub>s\<close> which takes an explicit set of indices and then only
demands that these constraints are satisfied.\<close>

datatype constraint = LT linear_poly rat
  | GT linear_poly rat
  | LEQ linear_poly rat
  | GEQ linear_poly rat
  | EQ linear_poly rat
  | LTPP linear_poly linear_poly
  | GTPP linear_poly linear_poly
  | LEQPP linear_poly linear_poly
  | GEQPP linear_poly linear_poly
  | EQPP linear_poly linear_poly

text \<open>Indexed constraints are just pairs of indices and constraints. Indices will be used
  to identify constraints, e.g., to easily specify an unsatisfiable core by a list of indices.\<close>

type_synonym 'i i_constraint = "'i \<times> constraint"

abbreviation (input) restrict_to :: "'i set \<Rightarrow> ('i \<times> 'a) set \<Rightarrow> 'a set" where
  "restrict_to I xs \<equiv> snd ` (xs \<inter> (I \<times> UNIV))"

text \<open>The operation @{const restrict_to} is used to select constraints for a given index set.\<close>

abbreviation (input) flat :: "('i \<times> 'a) set \<Rightarrow> 'a set" where
  "flat xs \<equiv> snd ` xs"

text \<open>The operation @{const flat} is used to drop indices from a set of indexed constraints.\<close>

abbreviation (input) flat_list :: "('i \<times> 'a) list \<Rightarrow> 'a list" where
  "flat_list xs \<equiv> map snd xs"

primrec
  satisfies_constraint :: "'a :: lrv valuation \<Rightarrow> constraint \<Rightarrow> bool"  (infixl "\<Turnstile>\<^sub>c" 100) where
  "v \<Turnstile>\<^sub>c (LT l r) \<longleftrightarrow> (l\<lbrace>v\<rbrace>) < r *R 1"
| "v \<Turnstile>\<^sub>c GT l r \<longleftrightarrow> (l\<lbrace>v\<rbrace>) > r *R 1"
| "v \<Turnstile>\<^sub>c LEQ l r \<longleftrightarrow> (l\<lbrace>v\<rbrace>) \<le> r *R 1"
| "v \<Turnstile>\<^sub>c GEQ l r \<longleftrightarrow> (l\<lbrace>v\<rbrace>) \<ge>  r *R 1"
| "v \<Turnstile>\<^sub>c EQ l r \<longleftrightarrow> (l\<lbrace>v\<rbrace>) = r *R 1"
| "v \<Turnstile>\<^sub>c LTPP l1 l2 \<longleftrightarrow> (l1\<lbrace>v\<rbrace>) < (l2\<lbrace>v\<rbrace>)"
| "v \<Turnstile>\<^sub>c GTPP l1 l2 \<longleftrightarrow> (l1\<lbrace>v\<rbrace>) > (l2\<lbrace>v\<rbrace>)"
| "v \<Turnstile>\<^sub>c LEQPP l1 l2 \<longleftrightarrow> (l1\<lbrace>v\<rbrace>) \<le> (l2\<lbrace>v\<rbrace>)"
| "v \<Turnstile>\<^sub>c GEQPP l1 l2 \<longleftrightarrow> (l1\<lbrace>v\<rbrace>) \<ge> (l2\<lbrace>v\<rbrace>)"
| "v \<Turnstile>\<^sub>c EQPP l1 l2 \<longleftrightarrow> (l1\<lbrace>v\<rbrace>) = (l2\<lbrace>v\<rbrace>)"


abbreviation satisfies_constraints :: "rat valuation \<Rightarrow> constraint set \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>c\<^sub>s" 100) where
  "v \<Turnstile>\<^sub>c\<^sub>s cs \<equiv> \<forall> c \<in> cs. v \<Turnstile>\<^sub>c c"

lemma unsat_mono: assumes "\<not> (\<exists> v. v \<Turnstile>\<^sub>c\<^sub>s cs)"
  and "cs \<subseteq> ds"
shows "\<not> (\<exists> v. v \<Turnstile>\<^sub>c\<^sub>s ds)"
  using assms by auto

fun i_satisfies_cs (infixl "\<Turnstile>\<^sub>i\<^sub>c\<^sub>s" 100) where
  "(I,v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s cs \<longleftrightarrow> v \<Turnstile>\<^sub>c\<^sub>s restrict_to I cs"

definition distinct_indices :: "('i \<times> 'c) list \<Rightarrow> bool" where
  "distinct_indices as = (distinct (map fst as))"

lemma distinct_indicesD: "distinct_indices as \<Longrightarrow> (i,x) \<in> set as \<Longrightarrow> (i,y) \<in> set as \<Longrightarrow> x = y"
  unfolding distinct_indices_def by (rule eq_key_imp_eq_value)

text \<open>For the unsat-core predicate we only demand minimality in case that the indices are distinct.
  Otherwise, minimality does in general not hold. For instance, consider the input
  constraints $c_1: x < 0$, $c_2: x > 2$ and $c_2: x < 1$ where the index $c_2$ occurs twice.
  If the simplex-method first encounters constraint $c_1$, then it will detect that there is a conflict
  between $c_1$ and the first $c_2$-constraint. Consequently, the index-set $\{c_1,c_2\}$ will be returned,
  but this set is not minimal since $\{c_2\}$ is already unsatisfiable.\<close>
definition minimal_unsat_core :: "'i set \<Rightarrow> 'i i_constraint list \<Rightarrow> bool" where
  "minimal_unsat_core I ics  = ((I \<subseteq> fst ` set ics) \<and> (\<not> (\<exists> v. (I,v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics))
     \<and> (distinct_indices ics \<longrightarrow> (\<forall> J. J \<subset> I \<longrightarrow> (\<exists> v. (J,v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics))))"

subsection \<open>Procedure Specification\<close>

abbreviation (input) Unsat where "Unsat \<equiv> Inl"
abbreviation (input) Sat where "Sat \<equiv> Inr"


text\<open>The specification for the satisfiability check procedure is given by:\<close>
locale Solve =
  \<comment> \<open>Decide if the given list of constraints is satisfiable. Return either
     an unsat core, or a satisfying valuation.\<close>
  fixes solve :: "'i i_constraint list \<Rightarrow> 'i list + rat valuation"
    \<comment> \<open>If the status @{const Sat} is returned, then returned valuation
      satisfies all constraints.\<close>
  assumes  simplex_sat:  "solve cs = Sat v \<Longrightarrow> v \<Turnstile>\<^sub>c\<^sub>s flat (set cs)"
    \<comment> \<open>If the status @{const Unsat} is returned, then constraints are
     unsatisfiable, i.e., an unsatisfiable core is returned.\<close>
  assumes  simplex_unsat:  "solve cs = Unsat I \<Longrightarrow> minimal_unsat_core (set I) cs"

abbreviation (input) look where "look \<equiv> Mapping.lookup"
abbreviation (input) upd where "upd \<equiv> Mapping.update"

lemma look_upd: "look (upd k v m) = (look m)(k \<mapsto> v)"
  by (transfer, auto)

lemmas look_upd_simps[simp] = look_upd Mapping.lookup_empty

definition map2fun:: "(var, 'a :: zero) mapping \<Rightarrow> var \<Rightarrow> 'a" where
  "map2fun v \<equiv> \<lambda>x. case look v x of None \<Rightarrow> 0 | Some y \<Rightarrow> y"
syntax
  "_map2fun" :: "(var, 'a) mapping \<Rightarrow> var \<Rightarrow> 'a"  ("\<langle>_\<rangle>")
translations
  "\<langle>v\<rangle>" == "CONST map2fun v"

lemma map2fun_def':
  "\<langle>v\<rangle> x \<equiv> case Mapping.lookup v x of None \<Rightarrow> 0 | Some y \<Rightarrow> y"
  by (auto simp add: map2fun_def)


text\<open>Note that the above specification requires returning a
valuation (defined as a HOL function), which is not efficiently
executable. In order to enable more efficient data structures for
representing valuations, a refinement of this specification is needed
and the function \<open>solve\<close> is replaced by the function \<open>solve_exec\<close> returning optional \<open>(var, rat) mapping\<close> instead
of \<open>var \<Rightarrow> rat\<close> function. This way, efficient data structures
for representing mappings can be easily plugged-in during code
generation \cite{florian-refinement}. A conversion from the \<open>mapping\<close> datatype to HOL function is denoted by \<open>\<langle>_\<rangle>\<close> and
given by: @{thm map2fun_def'[no_vars]}.\<close>

locale SolveExec =
  fixes solve_exec :: "'i i_constraint list \<Rightarrow> 'i list + (var, rat) mapping"
  assumes  simplex_sat0:  "solve_exec cs = Sat v \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s flat (set cs)"
  assumes  simplex_unsat0:  "solve_exec cs = Unsat I \<Longrightarrow> minimal_unsat_core (set I) cs"
begin
definition solve where
  "solve cs \<equiv> case solve_exec cs of Sat v \<Rightarrow> Sat \<langle>v\<rangle> | Unsat c \<Rightarrow> Unsat c"
end

sublocale SolveExec < Solve solve
  by (unfold_locales, insert simplex_sat0 simplex_unsat0,
      auto simp: solve_def split: sum.splits)


subsection \<open>Handling Strict Inequalities\<close>

text\<open>The first step of the procedure is removing all equalities and
strict inequalities. Equalities can be easily rewritten to non-strict
inequalities. Removing strict inequalities can be done by replacing
the list of constraints by a new one, formulated over an extension
\<open>\<rat>'\<close> of the space of rationals \<open>\<rat>\<close>. \<open>\<rat>'\<close> must
have a structure of a linearly ordered vector space over \<open>\<rat>\<close>
(represented by the type class \<open>lrv\<close>) and must guarantee that
if some non-strict constraints are satisfied in \<open>\<rat>'\<close>, then
there is a satisfying valuation for the original constraints in \<open>\<rat>\<close>. Our final implementation uses the \<open>\<rat>\<^sub>\<delta>\<close> space, defined in
\cite{simplex-rad} (basic idea is to replace \<open>p < c\<close> by \<open>p \<le> c - \<delta>\<close> and \<open>p > c\<close> by \<open>p \<ge> c + \<delta>\<close> for a symbolic
parameter \<open>\<delta>\<close>). So, all constraints are reduced to the form
\<open>p \<bowtie> b\<close>, where \<open>p\<close> is a linear polynomial (still over
\<open>\<rat>\<close>), \<open>b\<close> is constant from \<open>\<rat>'\<close> and \<open>\<bowtie>
\<in> {\<le>, \<ge>}\<close>. The non-strict constraints are represented by the type
\<open>'a ns_constraint\<close>, and their semantics is denoted by \<open>\<Turnstile>\<^sub>n\<^sub>s\<close> and \<open>\<Turnstile>\<^sub>n\<^sub>s\<^sub>s\<close>. The indexed variant is \<open>\<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s\<close>.\<close>
datatype 'a ns_constraint = LEQ_ns linear_poly 'a    |    GEQ_ns linear_poly 'a

type_synonym ('i,'a) i_ns_constraint = "'i \<times> 'a ns_constraint"

primrec satisfiable_ns_constraint :: "'a::lrv valuation \<Rightarrow> 'a ns_constraint \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>n\<^sub>s" 100) where
  "v \<Turnstile>\<^sub>n\<^sub>s LEQ_ns l r \<longleftrightarrow> l\<lbrace>v\<rbrace> \<le> r"
| "v \<Turnstile>\<^sub>n\<^sub>s GEQ_ns l r \<longleftrightarrow> l\<lbrace>v\<rbrace> \<ge> r"

abbreviation satisfies_ns_constraints :: "'a::lrv valuation \<Rightarrow> 'a ns_constraint set \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>n\<^sub>s\<^sub>s " 100) where
  "v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s cs \<equiv> \<forall> c \<in> cs. v \<Turnstile>\<^sub>n\<^sub>s c"

fun i_satisfies_ns_constraints :: "'i set \<times> 'a::lrv valuation \<Rightarrow> ('i,'a) i_ns_constraint set \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s " 100) where
  "(I,v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s cs \<longleftrightarrow> v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s restrict_to I cs"

lemma i_satisfies_ns_constraints_mono:
  "(I,v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s cs \<Longrightarrow> J \<subseteq> I \<Longrightarrow> (J,v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s cs"
  by auto

primrec poly :: "'a ns_constraint \<Rightarrow> linear_poly" where
  "poly (LEQ_ns p a) = p"
| "poly (GEQ_ns p a) = p"

primrec ns_constraint_const :: "'a ns_constraint \<Rightarrow> 'a" where
  "ns_constraint_const (LEQ_ns p a) = a" 
| "ns_constraint_const (GEQ_ns p a) = a" 

definition distinct_indices_ns :: "('i,'a :: lrv) i_ns_constraint set \<Rightarrow> bool" where 
  "distinct_indices_ns ns = ((\<forall> n1 n2 i. (i,n1) \<in> ns \<longrightarrow> (i,n2) \<in> ns \<longrightarrow> 
     poly n1 = poly n2 \<and> ns_constraint_const n1 = ns_constraint_const n2))" 

definition minimal_unsat_core_ns :: "'i set \<Rightarrow> ('i,'a :: lrv) i_ns_constraint set \<Rightarrow> bool" where
  "minimal_unsat_core_ns I cs = ((I \<subseteq> fst ` cs) \<and> (\<not> (\<exists> v. (I,v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s cs))
     \<and> (distinct_indices_ns cs \<longrightarrow> (\<forall> J \<subset> I. \<exists> v. (J,v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s cs)))"


text\<open>Specification of reduction of constraints to non-strict form is given by:\<close>
locale To_ns =
  \<comment> \<open>Convert a constraint to an equisatisfiable non-strict constraint list.
      The conversion must work for arbitrary subsets of constraints -- selected by some index set I --
      in order to carry over unsat-cores and in order to support incremental simplex solving.\<close>
  fixes to_ns :: "'i i_constraint list \<Rightarrow> ('i,'a::lrv) i_ns_constraint list"
    \<comment> \<open>Convert the valuation that satisfies all non-strict constraints to the valuation that
   satisfies all initial constraints.\<close>
  fixes from_ns :: "(var, 'a) mapping \<Rightarrow> 'a ns_constraint list \<Rightarrow> (var, rat) mapping"
  assumes  to_ns_unsat:  "minimal_unsat_core_ns I (set (to_ns cs)) \<Longrightarrow> minimal_unsat_core I cs"
  assumes  i_to_ns_sat:  "(I,\<langle>v'\<rangle>) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set (to_ns cs) \<Longrightarrow> (I,\<langle>from_ns v' (flat_list (to_ns cs))\<rangle>) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs"
  assumes to_ns_indices: "fst ` set (to_ns cs) = fst ` set cs"
  assumes distinct_cond: "distinct_indices cs \<Longrightarrow> distinct_indices_ns (set (to_ns cs))" 
begin
lemma to_ns_sat: "\<langle>v'\<rangle>  \<Turnstile>\<^sub>n\<^sub>s\<^sub>s flat (set (to_ns cs)) \<Longrightarrow> \<langle>from_ns v' (flat_list (to_ns cs))\<rangle> \<Turnstile>\<^sub>c\<^sub>s flat (set cs)"
  using i_to_ns_sat[of UNIV v' cs] by auto
end


locale Solve_exec_ns =
  fixes solve_exec_ns :: "('i,'a::lrv) i_ns_constraint list \<Rightarrow> 'i list + (var, 'a) mapping"
  assumes simplex_ns_sat:  "solve_exec_ns cs = Sat v \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>n\<^sub>s\<^sub>s flat (set cs)"
  assumes simplex_ns_unsat:  "solve_exec_ns cs = Unsat I \<Longrightarrow> minimal_unsat_core_ns (set I) (set cs)"


text\<open>After the transformation, the procedure is reduced to solving
only the non-strict constraints, implemented in the \<open>solve_exec_ns\<close> function having an analogous specification to the
\<open>solve\<close> function. If \<open>to_ns\<close>, \<open>from_ns\<close> and
\<open>solve_exec_ns\<close> are available, the \<open>solve_exec\<close>
function can be easily defined and it can be easily shown that this
definition satisfies its specification (also analogous to \<open>solve\<close>).
\<close>

locale SolveExec' = To_ns to_ns from_ns + Solve_exec_ns solve_exec_ns for
  to_ns:: "'i i_constraint list \<Rightarrow> ('i,'a::lrv) i_ns_constraint list" and
  from_ns :: "(var, 'a) mapping \<Rightarrow> 'a ns_constraint list \<Rightarrow> (var, rat) mapping" and
  solve_exec_ns :: "('i,'a) i_ns_constraint list \<Rightarrow> 'i list + (var, 'a) mapping"
begin

definition solve_exec where
  "solve_exec cs \<equiv> let cs' = to_ns cs in case solve_exec_ns cs'
            of Sat v \<Rightarrow> Sat (from_ns v (flat_list cs'))
             | Unsat is \<Rightarrow> Unsat is"

end


sublocale SolveExec' < SolveExec solve_exec
  by (unfold_locales, insert simplex_ns_sat simplex_ns_unsat to_ns_sat to_ns_unsat,
      (force simp: solve_exec_def Let_def split: sum.splits)+)


subsection \<open>Preprocessing\<close>

text\<open>The next step in the procedure rewrites a list of non-strict
constraints into an equisatisfiable form consisting of a list of
linear equations (called the \emph{tableau}) and of a list of
\emph{atoms} of the form \<open>x\<^sub>i \<bowtie> b\<^sub>i\<close> where \<open>x\<^sub>i\<close> is a
variable and \<open>b\<^sub>i\<close> is a constant (from the extension field). The
transformation is straightforward and introduces auxiliary variables
for linear polynomials occurring in the initial formula. For example,
\<open>[x\<^sub>1 + x\<^sub>2 \<le> b\<^sub>1, x\<^sub>1 + x\<^sub>2 \<ge> b\<^sub>2, x\<^sub>2 \<ge> b\<^sub>3]\<close> can be transformed to
the tableau \<open>[x\<^sub>3 = x\<^sub>1 + x\<^sub>2]\<close> and atoms \<open>[x\<^sub>3 \<le> b\<^sub>1, x\<^sub>3 \<ge>
b\<^sub>2, x\<^sub>2 \<ge> b\<^sub>3]\<close>.\<close>


type_synonym eq = "var \<times> linear_poly"
primrec lhs :: "eq \<Rightarrow> var" where "lhs (l, r) = l"
primrec rhs :: "eq \<Rightarrow> linear_poly" where "rhs (l, r) = r"
abbreviation rvars_eq :: "eq \<Rightarrow> var set" where
  "rvars_eq eq \<equiv> vars (rhs eq)"


definition satisfies_eq :: "'a::rational_vector valuation \<Rightarrow> eq \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>e" 100) where
  "v \<Turnstile>\<^sub>e eq \<equiv> v (lhs eq) = (rhs eq)\<lbrace>v\<rbrace>"

lemma satisfies_eq_iff: "v \<Turnstile>\<^sub>e (x, p) \<equiv> v x = p\<lbrace>v\<rbrace>"
  by (simp add: satisfies_eq_def)



type_synonym tableau ="eq list"


definition satisfies_tableau ::"'a::rational_vector valuation \<Rightarrow> tableau \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>t" 100) where
  "v \<Turnstile>\<^sub>t t \<equiv> \<forall> e \<in> set t. v \<Turnstile>\<^sub>e e"


definition lvars :: "tableau \<Rightarrow> var set" where
  "lvars t = set (map lhs t)"
definition rvars :: "tableau \<Rightarrow> var set" where
  "rvars t = \<Union> (set (map rvars_eq t))"
abbreviation tvars where "tvars t \<equiv> lvars t \<union> rvars t"

text \<open>The condition that the rhss are non-zero is required to obtain minimal unsatisfiable cores.
To observe the problem with 0 as rhs, consider the tableau $x = 0$ in combination
with atom $(A: x \leq 0)$ where then $(B: x \geq 1)$ is asserted.
In this case, the unsat core would be computed as $\{A,B\}$, although already $\{B\}$ is unsatisfiable.\<close>

definition normalized_tableau :: "tableau \<Rightarrow> bool" ("\<triangle>") where
  "normalized_tableau t \<equiv> distinct (map lhs t) \<and> lvars t \<inter> rvars t = {} \<and> 0 \<notin> rhs ` set t"

text\<open>Equations are of the form \<open>x = p\<close>, where \<open>x\<close> is
a variable and \<open>p\<close> is a polynomial, and are represented by the
type \<open>eq = var \<times> linear_poly\<close>. Semantics of equations is given
by @{thm satisfies_eq_iff[no_vars]}. Tableau is represented as a list
of equations, by the type \<open>tableau = eq list\<close>. Semantics for a
tableau is given by @{thm satisfies_tableau_def[no_vars]}. Functions
\<open>lvars\<close> and \<open>rvars\<close> return sets of variables appearing on
the left hand side (lhs) and the right hand side (rhs) of a
tableau. Lhs variables are called \emph{basic} while rhs variables are
called \emph{non-basic} variables. A tableau \<open>t\<close> is
\emph{normalized} (denoted by @{term "\<triangle> t"}) iff no variable occurs on
the lhs of two equations in a tableau and if sets of lhs and rhs
variables are distinct.\<close>

lemma normalized_tableau_unique_eq_for_lvar:
  assumes "\<triangle> t"
  shows "\<forall> x \<in> lvars t. \<exists>! p. (x, p) \<in> set t"
proof (safe)
  fix x
  assume "x \<in> lvars t"
  then show "\<exists>p. (x, p) \<in> set t"
    unfolding lvars_def
    by auto
next
  fix x p1 p2
  assume *: "(x, p1) \<in> set t" "(x, p2) \<in> set t"
  then show "p1 = p2"
    using \<open>\<triangle> t\<close>
    unfolding normalized_tableau_def
    by (force simp add: distinct_map inj_on_def)
qed

lemma recalc_tableau_lvars:
  assumes "\<triangle> t"
  shows "\<forall> v. \<exists> v'. (\<forall> x \<in> rvars t. v x = v' x) \<and> v' \<Turnstile>\<^sub>t t"
proof
  fix v
  let ?v' = "\<lambda> x. if x \<in> lvars t then (THE p. (x, p) \<in> set t) \<lbrace> v \<rbrace> else v x"
  show "\<exists> v'. (\<forall> x \<in> rvars t. v x = v' x) \<and> v' \<Turnstile>\<^sub>t t"
  proof (rule_tac x="?v'" in exI, rule conjI)
    show "\<forall>x\<in>rvars t. v x = ?v' x"
      using \<open>\<triangle> t\<close>
      unfolding normalized_tableau_def
      by auto
    show "?v' \<Turnstile>\<^sub>t t"
      unfolding satisfies_tableau_def satisfies_eq_def
    proof
      fix e
      assume "e \<in> set t"
      obtain l r where e: "e = (l,r)" by force
      show "?v' (lhs e) = rhs e \<lbrace> ?v' \<rbrace>"
      proof-
        have "(lhs e, rhs e) \<in> set t"
          using \<open>e \<in> set t\<close> e by auto
        have "\<exists>!p. (lhs e, p) \<in> set t"
          using \<open>\<triangle> t\<close> normalized_tableau_unique_eq_for_lvar[of t]
          using \<open>e \<in> set t\<close>
          unfolding lvars_def
          by auto

        let ?p = "THE p. (lhs e, p) \<in> set t"
        have "(lhs e, ?p) \<in> set t"
          apply (rule theI')
          using \<open>\<exists>!p. (lhs e, p) \<in> set t\<close>
          by auto
        then have "?p = rhs e"
          using \<open>(lhs e, rhs e) \<in> set t\<close>
          using \<open>\<exists>!p. (lhs e, p) \<in> set t\<close>
          by auto
        moreover
        have "?v' (lhs e) = ?p \<lbrace> v \<rbrace>"
          using \<open>e \<in> set t\<close>
          unfolding lvars_def
          by simp
        moreover
        have "rhs e \<lbrace> ?v' \<rbrace> = rhs e \<lbrace> v \<rbrace>"
          apply (rule valuate_depend)
          using \<open>\<triangle> t\<close> \<open>e \<in> set t\<close>
          unfolding normalized_tableau_def
          by (auto simp add: lvars_def rvars_def)
        ultimately
        show ?thesis
          by auto
      qed
    qed
  qed
qed

lemma tableau_perm:
  assumes "lvars t1 = lvars t2" "rvars t1 = rvars t2"
    "\<triangle> t1" "\<triangle> t2" "\<And> v::'a::lrv valuation. v \<Turnstile>\<^sub>t t1 \<longleftrightarrow> v \<Turnstile>\<^sub>t t2"
  shows "t1 <~~> t2"
proof-
  {
    fix t1 t2
    assume "lvars t1 = lvars t2" "rvars t1 = rvars t2"
      "\<triangle> t1" "\<And> v::'a::lrv valuation. v \<Turnstile>\<^sub>t t1 \<longleftrightarrow> v \<Turnstile>\<^sub>t t2"
    have "set t1 \<subseteq> set t2"
    proof (safe)
      fix a b
      assume "(a, b) \<in> set t1"
      then have "a \<in> lvars t1"
        unfolding lvars_def
        by force
      then have "a \<in> lvars t2"
        using \<open>lvars t1 = lvars t2\<close>
        by simp
      then obtain b' where "(a, b') \<in> set t2"
        unfolding lvars_def
        by force
      have "\<forall>v::'a valuation. \<exists>v'. (\<forall>x\<in>vars (b - b'). v' x = v x) \<and> (b - b') \<lbrace> v' \<rbrace> = 0"
      proof
        fix v::"'a valuation"
        obtain v' where "v' \<Turnstile>\<^sub>t t1" "\<forall> x \<in> rvars t1. v x = v' x"
          using recalc_tableau_lvars[of t1] \<open>\<triangle> t1\<close>
          by auto
        have "v' \<Turnstile>\<^sub>t t2"
          using \<open>v' \<Turnstile>\<^sub>t t1\<close> \<open>\<And> v. v \<Turnstile>\<^sub>t t1 \<longleftrightarrow> v \<Turnstile>\<^sub>t t2\<close>
          by simp
        have "b \<lbrace>v'\<rbrace> = b' \<lbrace>v'\<rbrace>"
          using \<open>(a, b) \<in> set t1\<close> \<open>v' \<Turnstile>\<^sub>t t1\<close>
          using \<open>(a, b') \<in> set t2\<close> \<open>v' \<Turnstile>\<^sub>t t2\<close>
          unfolding satisfies_tableau_def satisfies_eq_def
          by force
        then have "(b - b') \<lbrace>v'\<rbrace> = 0"
          using valuate_minus[of b b' v']
          by auto
        moreover
        have "vars b \<subseteq> rvars t1" "vars b' \<subseteq> rvars t1"
          using \<open>(a, b) \<in> set t1\<close> \<open>(a, b') \<in> set t2\<close> \<open>rvars t1 = rvars t2\<close>
          unfolding rvars_def
          by force+
        then have "vars (b - b') \<subseteq> rvars t1"
          using vars_minus[of b b']
          by blast
        then have "\<forall>x\<in>vars (b - b'). v' x = v x"
          using \<open>\<forall> x \<in> rvars t1. v x = v' x\<close>
          by auto
        ultimately
        show "\<exists>v'. (\<forall>x\<in>vars (b - b'). v' x = v x) \<and> (b - b') \<lbrace> v' \<rbrace> = 0"
          by auto
      qed
      then have "b = b'"
        using all_val[of "b - b'"]
        by simp
      then show "(a, b) \<in> set t2"
        using \<open>(a, b') \<in> set t2\<close>
        by simp
    qed
  }
  note * = this
  have "set t1 = set t2"
    using *[of t1 t2] *[of t2 t1]
    using assms
    by auto
  moreover
  have "distinct t1" "distinct t2"
    using \<open>\<triangle> t1\<close> \<open>\<triangle> t2\<close>
    unfolding normalized_tableau_def
    by (auto simp add: distinct_map)
  ultimately
  show ?thesis
    by (auto simp add: set_eq_iff_mset_eq_distinct mset_eq_perm)
qed


text\<open>Elementary atoms are represented by the type \<open>'a atom\<close>
and semantics for atoms and sets of atoms is denoted by \<open>\<Turnstile>\<^sub>a\<close> and
\<open>\<Turnstile>\<^sub>a\<^sub>s\<close> and given by:
\<close>

datatype 'a atom  = Leq var 'a    |    Geq var 'a

primrec atom_var::"'a atom \<Rightarrow> var" where
  "atom_var (Leq var a) = var"
| "atom_var (Geq var a) = var"

primrec atom_const::"'a atom \<Rightarrow> 'a" where
  "atom_const (Leq var a) = a"
| "atom_const (Geq var a) = a"

primrec satisfies_atom :: "'a::linorder valuation \<Rightarrow> 'a atom \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>a" 100) where
  "v \<Turnstile>\<^sub>a Leq x c \<longleftrightarrow> v x \<le> c"    |    "v \<Turnstile>\<^sub>a Geq x c \<longleftrightarrow> v x \<ge> c"

definition satisfies_atom_set :: "'a::linorder valuation \<Rightarrow> 'a atom set \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>a\<^sub>s" 100) where
  "v \<Turnstile>\<^sub>a\<^sub>s as \<equiv> \<forall> a \<in> as. v \<Turnstile>\<^sub>a a"

definition satisfies_atom' :: "'a::linorder valuation \<Rightarrow> 'a atom \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>a\<^sub>e" 100) where
  "v \<Turnstile>\<^sub>a\<^sub>e a \<longleftrightarrow> v (atom_var a) = atom_const a"

lemma satisfies_atom'_stronger: "v \<Turnstile>\<^sub>a\<^sub>e a \<Longrightarrow> v \<Turnstile>\<^sub>a a" by (cases a, auto simp: satisfies_atom'_def)

abbreviation satisfies_atom_set' :: "'a::linorder valuation \<Rightarrow> 'a atom set \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>a\<^sub>e\<^sub>s" 100) where
  "v \<Turnstile>\<^sub>a\<^sub>e\<^sub>s as \<equiv> \<forall> a \<in> as. v \<Turnstile>\<^sub>a\<^sub>e a"

lemma satisfies_atom_set'_stronger: "v \<Turnstile>\<^sub>a\<^sub>e\<^sub>s as \<Longrightarrow> v \<Turnstile>\<^sub>a\<^sub>s as" 
  using satisfies_atom'_stronger unfolding satisfies_atom_set_def by auto

text \<open>There is also the indexed variant of an atom\<close>

type_synonym ('i,'a) i_atom = "'i \<times> 'a atom"

fun i_satisfies_atom_set :: "'i set \<times> 'a::linorder valuation \<Rightarrow> ('i,'a) i_atom set \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>i\<^sub>a\<^sub>s" 100) where
  "(I,v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s as \<longleftrightarrow> v \<Turnstile>\<^sub>a\<^sub>s restrict_to I as"

fun i_satisfies_atom_set' :: "'i set \<times> 'a::linorder valuation \<Rightarrow> ('i,'a) i_atom set \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>i\<^sub>a\<^sub>e\<^sub>s" 100) where
  "(I,v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>e\<^sub>s as \<longleftrightarrow> v \<Turnstile>\<^sub>a\<^sub>e\<^sub>s restrict_to I as"

lemma i_satisfies_atom_set'_stronger: "Iv \<Turnstile>\<^sub>i\<^sub>a\<^sub>e\<^sub>s as \<Longrightarrow> Iv \<Turnstile>\<^sub>i\<^sub>a\<^sub>s as" 
  using satisfies_atom_set'_stronger[of _ "snd Iv"] by (cases Iv, auto)

lemma satisifies_atom_restrict_to_Cons: "v \<Turnstile>\<^sub>a\<^sub>s restrict_to I (set as) \<Longrightarrow> (i \<in> I \<Longrightarrow> v \<Turnstile>\<^sub>a a)
  \<Longrightarrow> v \<Turnstile>\<^sub>a\<^sub>s restrict_to I (set ((i,a) # as))"
  unfolding satisfies_atom_set_def by auto

lemma satisfies_tableau_Cons: "v \<Turnstile>\<^sub>t t \<Longrightarrow> v \<Turnstile>\<^sub>e e \<Longrightarrow> v \<Turnstile>\<^sub>t (e # t)"
  unfolding satisfies_tableau_def by auto

definition distinct_indices_atoms :: "('i,'a) i_atom set \<Rightarrow> bool" where
  "distinct_indices_atoms as = (\<forall> i a b. (i,a) \<in> as \<longrightarrow> (i,b) \<in> as \<longrightarrow> atom_var a = atom_var b \<and> atom_const a = atom_const b)" 

text\<open>
The specification of the preprocessing function is given by:\<close>
locale Preprocess = fixes preprocess::"('i,'a::lrv) i_ns_constraint list \<Rightarrow> tableau\<times> ('i,'a) i_atom list
  \<times> ((var,'a) mapping \<Rightarrow> (var,'a) mapping) \<times> 'i list"
  assumes
    \<comment> \<open>The returned tableau is always normalized.\<close>
    preprocess_tableau_normalized: "preprocess cs = (t,as,trans_v,U) \<Longrightarrow> \<triangle> t" and

\<comment> \<open>Tableau and atoms are equisatisfiable with starting non-strict constraints.\<close>
i_preprocess_sat: "\<And> v. preprocess cs = (t,as,trans_v,U) \<Longrightarrow> I \<inter> set U = {} \<Longrightarrow> (I,\<langle>v\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>t t \<Longrightarrow> (I,\<langle>trans_v v\<rangle>) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set cs" and

preprocess_unsat: "preprocess cs = (t, as,trans_v,U) \<Longrightarrow> (I,v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set cs \<Longrightarrow> \<exists> v'. (I,v') \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as \<and> v' \<Turnstile>\<^sub>t t" and

\<comment> \<open>distinct indices on ns-constraints ensures distinct indices in atoms\<close>
preprocess_distinct: "preprocess cs = (t, as,trans_v, U) \<Longrightarrow> distinct_indices_ns (set cs) \<Longrightarrow> distinct_indices_atoms (set as)" and

\<comment> \<open>unsat indices\<close>
preprocess_unsat_indices: "preprocess cs = (t, as,trans_v, U) \<Longrightarrow> i \<in> set U \<Longrightarrow> \<not> (\<exists> v. ({i},v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set cs)" and

\<comment> \<open>preprocessing cannot introduce new indices\<close>
preprocess_index: "preprocess cs = (t,as,trans_v, U) \<Longrightarrow> fst ` set as \<union> set U \<subseteq> fst ` set cs"
begin
lemma preprocess_sat: "preprocess cs = (t,as,trans_v,U) \<Longrightarrow> U = [] \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>a\<^sub>s flat (set as) \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>t t \<Longrightarrow> \<langle>trans_v v\<rangle> \<Turnstile>\<^sub>n\<^sub>s\<^sub>s flat (set cs)"
  using i_preprocess_sat[of cs t as trans_v U UNIV v] by auto

end

definition minimal_unsat_core_tabl_atoms :: "'i set \<Rightarrow> tableau \<Rightarrow> ('i,'a::lrv) i_atom set \<Rightarrow> bool" where
  "minimal_unsat_core_tabl_atoms I t as = ( I \<subseteq> fst ` as \<and> (\<not> (\<exists> v. v \<Turnstile>\<^sub>t t \<and> (I,v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s as)) \<and>
       (distinct_indices_atoms as \<longrightarrow> (\<forall> J \<subset> I. \<exists> v. v \<Turnstile>\<^sub>t t \<and> (J,v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>e\<^sub>s as)))" 

lemma minimal_unsat_core_tabl_atomsD: assumes "minimal_unsat_core_tabl_atoms I t as"
  shows "I \<subseteq> fst ` as" 
    "\<not> (\<exists> v. v \<Turnstile>\<^sub>t t \<and> (I,v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s as)" 
    "distinct_indices_atoms as \<Longrightarrow> J \<subset> I \<Longrightarrow> \<exists> v. v \<Turnstile>\<^sub>t t \<and> (J,v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>e\<^sub>s as" 
  using assms unfolding minimal_unsat_core_tabl_atoms_def by auto

locale AssertAll =
  fixes assert_all :: "tableau \<Rightarrow> ('i,'a::lrv) i_atom list \<Rightarrow> 'i list + (var, 'a)mapping"
  assumes assert_all_sat:  "\<triangle> t \<Longrightarrow> assert_all t as = Sat v \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>t t \<and> \<langle>v\<rangle> \<Turnstile>\<^sub>a\<^sub>s flat (set as)"
  assumes assert_all_unsat:  "\<triangle> t \<Longrightarrow> assert_all t as = Unsat I \<Longrightarrow> minimal_unsat_core_tabl_atoms (set I) t (set as)"


text\<open>Once the preprocessing is done and tableau and atoms are
obtained, their satisfiability is checked by the
\<open>assert_all\<close> function. Its precondition is that the starting
tableau is normalized, and its specification is analogue to the one for the
\<open>solve\<close> function. If \<open>preprocess\<close> and \<open>assert_all\<close>
are available, the  \<open>solve_exec_ns\<close> can be defined, and it
can easily be shown that this definition satisfies the specification.\<close>

locale Solve_exec_ns' = Preprocess preprocess + AssertAll assert_all for
  preprocess:: "('i,'a::lrv) i_ns_constraint list \<Rightarrow> tableau \<times> ('i,'a) i_atom list \<times> ((var,'a)mapping \<Rightarrow> (var,'a)mapping) \<times> 'i list" and
  assert_all :: "tableau \<Rightarrow> ('i,'a::lrv) i_atom list \<Rightarrow> 'i list + (var, 'a) mapping"
begin
definition solve_exec_ns where

"solve_exec_ns s \<equiv>
    case preprocess s of (t,as,trans_v,ui) \<Rightarrow>
      (case ui of i # _ \<Rightarrow> Inl [i] | _ \<Rightarrow>
      (case assert_all t as of Inl I \<Rightarrow> Inl I | Inr v \<Rightarrow> Inr (trans_v v))) "
end

context Preprocess
begin

lemma preprocess_unsat_index: assumes prep: "preprocess cs = (t,as,trans_v,ui)" 
  and i: "i \<in> set ui" 
shows "minimal_unsat_core_ns {i} (set cs)"
proof -
  from preprocess_index[OF prep] have "set ui \<subseteq> fst ` set cs" by auto
  with i have i': "i \<in> fst ` set cs" by auto
  from preprocess_unsat_indices[OF prep i]
  show ?thesis unfolding minimal_unsat_core_ns_def using i' by auto
qed

lemma preprocess_minimal_unsat_core: assumes prep: "preprocess cs = (t,as,trans_v,ui)"
    and unsat: "minimal_unsat_core_tabl_atoms I t (set as)" 
    and inter: "I \<inter> set ui = {}" 
  shows "minimal_unsat_core_ns I (set cs)" 
proof -
  from preprocess_tableau_normalized[OF prep]
  have t: "\<triangle> t" .
  from preprocess_index[OF prep] have index: "fst ` set as \<union> set ui \<subseteq> fst ` set cs" by auto
  from minimal_unsat_core_tabl_atomsD(1,2)[OF unsat] preprocess_unsat[OF prep, of I]
  have 1: "I \<subseteq> fst ` set as" "\<not> (\<exists> v. (I, v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set cs)" by force+
  show "minimal_unsat_core_ns I (set cs)" unfolding minimal_unsat_core_ns_def
  proof (intro conjI impI allI 1(2))
    show "I \<subseteq> fst ` set cs" using 1 index by auto
    fix J
    assume "distinct_indices_ns (set cs)" "J \<subset> I" 
    with preprocess_distinct[OF prep]
    have "distinct_indices_atoms (set as)" "J \<subset> I" by auto
    from minimal_unsat_core_tabl_atomsD(3)[OF unsat this]
    obtain v where model: "v \<Turnstile>\<^sub>t t" "(J, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>e\<^sub>s set as" by auto
    from i_satisfies_atom_set'_stronger[OF model(2)] 
    have model': "(J, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as" . 
    define w where "w = Mapping.Mapping (\<lambda> x. Some (v x))"
    have "v = \<langle>w\<rangle>" unfolding w_def map2fun_def
      by (intro ext, transfer, auto)
    with model model' have "\<langle>w\<rangle> \<Turnstile>\<^sub>t t" "(J, \<langle>w\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as" by auto
    from i_preprocess_sat[OF prep _ this(2,1)] \<open>J \<subset> I\<close> inter
    have "(J, \<langle>trans_v w\<rangle>) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set cs" by auto
    then show "\<exists> w. (J, w) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set cs" by auto
  qed
qed
end

sublocale Solve_exec_ns' < Solve_exec_ns solve_exec_ns
proof
  fix cs
  obtain t as trans_v ui where prep: "preprocess cs = (t,as,trans_v,ui)" by (cases "preprocess cs")
  from preprocess_tableau_normalized[OF prep]
  have t: "\<triangle> t" .
  from preprocess_index[OF prep] have index: "fst ` set as \<union> set ui \<subseteq> fst ` set cs" by auto
  note solve = solve_exec_ns_def[of cs, unfolded prep split]
  {
    fix v
    assume "solve_exec_ns cs = Sat v"
    from this[unfolded solve] t assert_all_sat[OF t] preprocess_sat[OF prep]
    show " \<langle>v\<rangle> \<Turnstile>\<^sub>n\<^sub>s\<^sub>s flat (set cs)" by (auto split: sum.splits list.splits)
  }
  {
    fix I
    assume res: "solve_exec_ns cs = Unsat I"
    show "minimal_unsat_core_ns (set I) (set cs)" 
    proof (cases ui)
      case (Cons i uis)
      hence I: "I = [i]" using res[unfolded solve] by auto
      from preprocess_unsat_index[OF prep, of i] I Cons index show ?thesis by auto
    next
      case Nil
      from res[unfolded solve Nil] have assert: "assert_all t as = Unsat I"
        by (auto split: sum.splits)
      from assert_all_unsat[OF t assert]
      have "minimal_unsat_core_tabl_atoms (set I) t (set as)" .
      from preprocess_minimal_unsat_core[OF prep this] Nil
      show "minimal_unsat_core_ns (set I) (set cs)" by simp
    qed
  }
qed

subsection\<open>Incrementally Asserting Atoms\<close>

text\<open>The function @{term assert_all} can be implemented by
iteratively asserting one by one atom from the given list of atoms.
\<close>

type_synonym 'a bounds = "var \<rightharpoonup> 'a"

text\<open>Asserted atoms will be stored in a form of \emph{bounds} for a
given variable. Bounds are of the form \<open>l\<^sub>i \<le> x\<^sub>i \<le> u\<^sub>i\<close>, where
\<open>l\<^sub>i\<close> and \<open>u\<^sub>i\<close> and are either scalars or $\pm
\infty$. Each time a new atom is asserted, a bound for the
corresponding variable is updated (checking for conflict with the
previous bounds). Since bounds for a variable can be either finite or
$\pm \infty$, they are represented by (partial) maps from variables to
values (\<open>'a bounds = var \<rightharpoonup> 'a\<close>). Upper and lower bounds are
represented separately. Infinite bounds map to @{term None} and this
is reflected in the semantics:

\begin{small}
\<open>c \<ge>\<^sub>u\<^sub>b b \<longleftrightarrow> case b of None \<Rightarrow> False | Some b' \<Rightarrow> c \<ge> b'\<close>

\<open>c \<le>\<^sub>u\<^sub>b b \<longleftrightarrow> case b of None \<Rightarrow> True | Some b' \<Rightarrow> c \<le> b'\<close>
\end{small}

\noindent Strict comparisons, and comparisons with lower bounds are performed similarly.
\<close>

abbreviation (input) le where
  "le lt x y \<equiv> lt x y \<or> x = y"
definition geub ("\<unrhd>\<^sub>u\<^sub>b") where
  "\<unrhd>\<^sub>u\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> False | Some b' \<Rightarrow> le lt b' c"
definition gtub ("\<rhd>\<^sub>u\<^sub>b") where
  "\<rhd>\<^sub>u\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> False | Some b' \<Rightarrow> lt b' c"
definition leub ("\<unlhd>\<^sub>u\<^sub>b") where
  "\<unlhd>\<^sub>u\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> True | Some b' \<Rightarrow> le lt c b'"
definition ltub ("\<lhd>\<^sub>u\<^sub>b") where
  "\<lhd>\<^sub>u\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> True | Some b' \<Rightarrow> lt c b'"
definition lelb ("\<unlhd>\<^sub>l\<^sub>b") where
  "\<unlhd>\<^sub>l\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> False | Some b' \<Rightarrow> le lt c b'"
definition ltlb ("\<lhd>\<^sub>l\<^sub>b") where
  "\<lhd>\<^sub>l\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> False | Some b' \<Rightarrow> lt c b'"
definition gelb ("\<unrhd>\<^sub>l\<^sub>b") where
  "\<unrhd>\<^sub>l\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> True | Some b' \<Rightarrow> le lt b' c"
definition gtlb ("\<rhd>\<^sub>l\<^sub>b") where
  "\<rhd>\<^sub>l\<^sub>b lt c b \<equiv> case b of None \<Rightarrow> True | Some b' \<Rightarrow> lt b' c"


definition ge_ubound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl "\<ge>\<^sub>u\<^sub>b" 100) where
  "c \<ge>\<^sub>u\<^sub>b b = \<unrhd>\<^sub>u\<^sub>b (<) c b"
definition gt_ubound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl ">\<^sub>u\<^sub>b" 100) where
  "c >\<^sub>u\<^sub>b b = \<rhd>\<^sub>u\<^sub>b (<) c b"
definition le_ubound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl "\<le>\<^sub>u\<^sub>b" 100) where
  "c \<le>\<^sub>u\<^sub>b b = \<unlhd>\<^sub>u\<^sub>b (<) c b"
definition lt_ubound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl "<\<^sub>u\<^sub>b" 100) where
  "c <\<^sub>u\<^sub>b b = \<lhd>\<^sub>u\<^sub>b (<) c b"
definition le_lbound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl "\<le>\<^sub>l\<^sub>b" 100) where
  "c \<le>\<^sub>l\<^sub>b b = \<unlhd>\<^sub>l\<^sub>b (<) c b"
definition lt_lbound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl "<\<^sub>l\<^sub>b" 100) where
  "c <\<^sub>l\<^sub>b b = \<lhd>\<^sub>l\<^sub>b (<) c b"
definition ge_lbound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl "\<ge>\<^sub>l\<^sub>b" 100) where
  "c \<ge>\<^sub>l\<^sub>b b = \<unrhd>\<^sub>l\<^sub>b (<) c b"
definition gt_lbound :: "'a::linorder \<Rightarrow> 'a option \<Rightarrow> bool" (infixl ">\<^sub>l\<^sub>b" 100) where
  "c >\<^sub>l\<^sub>b b = \<rhd>\<^sub>l\<^sub>b (<) c b"


lemmas bound_compare'_defs =
  geub_def gtub_def leub_def ltub_def
  gelb_def gtlb_def lelb_def ltlb_def

lemmas bound_compare''_defs =
  ge_ubound_def gt_ubound_def le_ubound_def lt_ubound_def
  le_lbound_def lt_lbound_def ge_lbound_def gt_lbound_def

lemmas bound_compare_defs = bound_compare'_defs bound_compare''_defs


lemma opposite_dir [simp]:
  "\<unlhd>\<^sub>l\<^sub>b (>) a b = \<unrhd>\<^sub>u\<^sub>b (<) a b"
  "\<unlhd>\<^sub>u\<^sub>b (>) a b = \<unrhd>\<^sub>l\<^sub>b (<) a b"
  "\<unrhd>\<^sub>l\<^sub>b (>) a b = \<unlhd>\<^sub>u\<^sub>b (<) a b"
  "\<unrhd>\<^sub>u\<^sub>b (>) a b = \<unlhd>\<^sub>l\<^sub>b (<) a b"
  "\<lhd>\<^sub>l\<^sub>b (>) a b = \<rhd>\<^sub>u\<^sub>b (<) a b"
  "\<lhd>\<^sub>u\<^sub>b (>) a b = \<rhd>\<^sub>l\<^sub>b (<) a b"
  "\<rhd>\<^sub>l\<^sub>b (>) a b = \<lhd>\<^sub>u\<^sub>b (<) a b"
  "\<rhd>\<^sub>u\<^sub>b (>) a b = \<lhd>\<^sub>l\<^sub>b (<) a b"
  by (case_tac[!] b) (auto simp add: bound_compare'_defs)


(* Auxiliary lemmas about bound comparison *)

lemma [simp]: "\<not> c \<ge>\<^sub>u\<^sub>b None " "\<not> c \<le>\<^sub>l\<^sub>b None"
  by (auto simp add: bound_compare_defs)

lemma neg_bounds_compare:
  "(\<not> (c \<ge>\<^sub>u\<^sub>b b)) \<Longrightarrow> c <\<^sub>u\<^sub>b b" "(\<not> (c \<le>\<^sub>u\<^sub>b b)) \<Longrightarrow> c >\<^sub>u\<^sub>b b"
  "(\<not> (c >\<^sub>u\<^sub>b b)) \<Longrightarrow> c \<le>\<^sub>u\<^sub>b b" "(\<not> (c <\<^sub>u\<^sub>b b)) \<Longrightarrow> c \<ge>\<^sub>u\<^sub>b b"
  "(\<not> (c \<le>\<^sub>l\<^sub>b b)) \<Longrightarrow> c >\<^sub>l\<^sub>b b" "(\<not> (c \<ge>\<^sub>l\<^sub>b b)) \<Longrightarrow> c <\<^sub>l\<^sub>b b"
  "(\<not> (c <\<^sub>l\<^sub>b b)) \<Longrightarrow> c \<ge>\<^sub>l\<^sub>b b" "(\<not> (c >\<^sub>l\<^sub>b b)) \<Longrightarrow> c \<le>\<^sub>l\<^sub>b b"
  by (case_tac[!] b) (auto simp add: bound_compare_defs)

lemma bounds_compare_contradictory [simp]:
  "\<lbrakk>c \<ge>\<^sub>u\<^sub>b b; c <\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> False" "\<lbrakk>c \<le>\<^sub>u\<^sub>b b; c >\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> False"
  "\<lbrakk>c >\<^sub>u\<^sub>b b; c \<le>\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> False" "\<lbrakk>c <\<^sub>u\<^sub>b b; c \<ge>\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> False"
  "\<lbrakk>c \<le>\<^sub>l\<^sub>b b; c >\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> False" "\<lbrakk>c \<ge>\<^sub>l\<^sub>b b; c <\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> False"
  "\<lbrakk>c <\<^sub>l\<^sub>b b; c \<ge>\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> False" "\<lbrakk>c >\<^sub>l\<^sub>b b; c \<le>\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> False"
  by (case_tac[!] b) (auto simp add: bound_compare_defs)

lemma compare_strict_nonstrict:
  "x <\<^sub>u\<^sub>b b \<Longrightarrow> x \<le>\<^sub>u\<^sub>b b"
  "x >\<^sub>u\<^sub>b b \<Longrightarrow> x \<ge>\<^sub>u\<^sub>b b"
  "x <\<^sub>l\<^sub>b b \<Longrightarrow> x \<le>\<^sub>l\<^sub>b b"
  "x >\<^sub>l\<^sub>b b \<Longrightarrow> x \<ge>\<^sub>l\<^sub>b b"
  by (case_tac[!] b) (auto simp add: bound_compare_defs)

lemma [simp]:
  "\<lbrakk> x \<le> c; c <\<^sub>u\<^sub>b b \<rbrakk> \<Longrightarrow> x <\<^sub>u\<^sub>b b"
  "\<lbrakk> x < c; c \<le>\<^sub>u\<^sub>b b \<rbrakk> \<Longrightarrow> x <\<^sub>u\<^sub>b b"
  "\<lbrakk> x \<le> c; c \<le>\<^sub>u\<^sub>b b \<rbrakk> \<Longrightarrow> x \<le>\<^sub>u\<^sub>b b"
  "\<lbrakk> x \<ge> c; c >\<^sub>l\<^sub>b b \<rbrakk> \<Longrightarrow> x >\<^sub>l\<^sub>b b"
  "\<lbrakk> x > c; c \<ge>\<^sub>l\<^sub>b b \<rbrakk> \<Longrightarrow> x >\<^sub>l\<^sub>b b"
  "\<lbrakk> x \<ge> c; c \<ge>\<^sub>l\<^sub>b b \<rbrakk> \<Longrightarrow> x \<ge>\<^sub>l\<^sub>b b"
  by (case_tac[!] b) (auto simp add: bound_compare_defs)

lemma bounds_lg [simp]:
  "\<lbrakk> c >\<^sub>u\<^sub>b b; x \<le>\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> x < c"
  "\<lbrakk> c \<ge>\<^sub>u\<^sub>b b; x <\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> x < c"
  "\<lbrakk> c \<ge>\<^sub>u\<^sub>b b; x \<le>\<^sub>u\<^sub>b b\<rbrakk> \<Longrightarrow> x \<le> c"
  "\<lbrakk> c <\<^sub>l\<^sub>b b; x \<ge>\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> x > c"
  "\<lbrakk> c \<le>\<^sub>l\<^sub>b b; x >\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> x > c"
  "\<lbrakk> c \<le>\<^sub>l\<^sub>b b; x \<ge>\<^sub>l\<^sub>b b\<rbrakk> \<Longrightarrow> x \<ge> c"
  by (case_tac[!] b) (auto simp add: bound_compare_defs)

lemma bounds_compare_Some [simp]:
  "x \<le>\<^sub>u\<^sub>b Some c \<longleftrightarrow> x \<le> c" "x \<ge>\<^sub>u\<^sub>b Some c \<longleftrightarrow> x \<ge> c"
  "x <\<^sub>u\<^sub>b Some c \<longleftrightarrow> x < c" "x >\<^sub>u\<^sub>b Some c \<longleftrightarrow> x > c"
  "x \<ge>\<^sub>l\<^sub>b Some c \<longleftrightarrow> x \<ge> c" "x \<le>\<^sub>l\<^sub>b Some c \<longleftrightarrow> x \<le> c"
  "x >\<^sub>l\<^sub>b Some c \<longleftrightarrow> x > c" "x <\<^sub>l\<^sub>b Some c \<longleftrightarrow> x < c"
  by (auto simp add: bound_compare_defs)

fun in_bounds where
  "in_bounds x v (lb, ub) = (v x \<ge>\<^sub>l\<^sub>b lb x \<and> v x \<le>\<^sub>u\<^sub>b ub x)"

fun satisfies_bounds :: "'a::linorder valuation \<Rightarrow> 'a bounds \<times> 'a bounds \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>b" 100) where
  "v \<Turnstile>\<^sub>b b \<longleftrightarrow> (\<forall> x. in_bounds x v b)"
declare satisfies_bounds.simps [simp del]


lemma satisfies_bounds_iff:
  "v \<Turnstile>\<^sub>b (lb, ub) \<longleftrightarrow> (\<forall> x. v x \<ge>\<^sub>l\<^sub>b lb x \<and> v x \<le>\<^sub>u\<^sub>b ub x)"
  by (auto simp add: satisfies_bounds.simps)

lemma not_in_bounds:
  "\<not> (in_bounds x v (lb, ub)) = (v x <\<^sub>l\<^sub>b lb x \<or> v x >\<^sub>u\<^sub>b ub x)"
  using bounds_compare_contradictory(7)
  using bounds_compare_contradictory(2)
  using neg_bounds_compare(7)[of "v x" "lb x"]
  using neg_bounds_compare(2)[of "v x" "ub x"]
  by auto

fun atoms_equiv_bounds :: "'a::linorder atom set \<Rightarrow> 'a bounds \<times> 'a bounds \<Rightarrow> bool" (infixl "\<doteq>" 100) where
  "as \<doteq> (lb, ub) \<longleftrightarrow> (\<forall> v. v \<Turnstile>\<^sub>a\<^sub>s as \<longleftrightarrow> v \<Turnstile>\<^sub>b (lb, ub))"
declare atoms_equiv_bounds.simps [simp del]

lemma atoms_equiv_bounds_simps:
  "as \<doteq> (lb, ub) \<equiv> \<forall> v. v \<Turnstile>\<^sub>a\<^sub>s as \<longleftrightarrow> v \<Turnstile>\<^sub>b (lb, ub)"
  by (simp add: atoms_equiv_bounds.simps)

text\<open>A valuation satisfies bounds iff the value of each variable
respects both its lower and upper bound, i.e, @{thm
satisfies_bounds_iff[no_vars]}. Asserted atoms are precisely encoded
by the current bounds in a state (denoted by \<open>\<doteq>\<close>) if every
valuation satisfies them iff it satisfies the bounds, i.e.,
@{thm atoms_equiv_bounds_simps[no_vars, iff]}.\<close>

text\<open>The procedure also keeps track of a valuation that is a
candidate solution. Whenever a new atom is asserted, it is checked
whether the valuation is still satisfying. If not, the procedure tries
to fix that by changing it and changing the tableau if necessary (but
so that it remains equivalent to the initial tableau).\<close>

text\<open>Therefore, the state of the procedure stores the tableau
(denoted by \<open>\<T>\<close>), lower and upper bounds (denoted by \<open>\<B>\<^sub>l\<close> and \<open>\<B>\<^sub>u\<close>, and ordered pair of lower and upper bounds
denoted by \<open>\<B>\<close>), candidate solution (denoted by \<open>\<V>\<close>)
and a flag (denoted by \<open>\<U>\<close>) indicating if unsatisfiability has
been detected so far:\<close>

text\<open>Since we also need to now about the indices of atoms, actually,
  the bounds are also indexed, and in addition to the flag for unsatisfiability,
  we also store an optional unsat core.\<close>

type_synonym 'i bound_index = "var \<Rightarrow> 'i"

type_synonym ('i,'a) bounds_index = "(var, ('i \<times> 'a))mapping"

datatype ('i,'a) state = State
  (\<T>: "tableau")
  (\<B>\<^sub>i\<^sub>l: "('i,'a) bounds_index")
  (\<B>\<^sub>i\<^sub>u: "('i,'a) bounds_index")
  (\<V>: "(var, 'a) mapping")
  (\<U>: bool)
  (\<U>\<^sub>c: "'i list option")

definition indexl :: "('i,'a) state \<Rightarrow> 'i bound_index" ("\<I>\<^sub>l") where
  "\<I>\<^sub>l s = (fst o the) o look (\<B>\<^sub>i\<^sub>l s)"

definition boundsl :: "('i,'a) state \<Rightarrow> 'a bounds" ("\<B>\<^sub>l") where
  "\<B>\<^sub>l s = map_option snd o look (\<B>\<^sub>i\<^sub>l s)"

definition indexu :: "('i,'a) state \<Rightarrow> 'i bound_index" ("\<I>\<^sub>u") where
  "\<I>\<^sub>u s = (fst o the) o look (\<B>\<^sub>i\<^sub>u s)"

definition boundsu :: "('i,'a) state \<Rightarrow> 'a bounds" ("\<B>\<^sub>u") where
  "\<B>\<^sub>u s = map_option snd o look (\<B>\<^sub>i\<^sub>u s)"

abbreviation BoundsIndicesMap ("\<B>\<^sub>i") where  "\<B>\<^sub>i s \<equiv> (\<B>\<^sub>i\<^sub>l s, \<B>\<^sub>i\<^sub>u s)"
abbreviation Bounds :: "('i,'a) state \<Rightarrow> 'a bounds \<times> 'a bounds" ("\<B>") where  "\<B> s \<equiv> (\<B>\<^sub>l s, \<B>\<^sub>u s)"
abbreviation Indices :: "('i,'a) state \<Rightarrow> 'i bound_index \<times> 'i bound_index" ("\<I>") where  "\<I> s \<equiv> (\<I>\<^sub>l s, \<I>\<^sub>u s)"
abbreviation BoundsIndices :: "('i,'a) state \<Rightarrow> ('a bounds \<times> 'a bounds) \<times> ('i bound_index \<times> 'i bound_index)" ("\<B>\<I>")
  where  "\<B>\<I> s \<equiv> (\<B> s, \<I> s)"

fun satisfies_bounds_index :: "'i set \<times> 'a::lrv valuation \<Rightarrow> ('a bounds \<times> 'a bounds) \<times>
  ('i bound_index \<times> 'i bound_index) \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>i\<^sub>b" 100) where
  "(I,v) \<Turnstile>\<^sub>i\<^sub>b ((BL,BU),(IL,IU)) \<longleftrightarrow> (
     (\<forall> x c. BL x = Some c \<longrightarrow> IL x \<in> I \<longrightarrow> v x \<ge> c)
   \<and> (\<forall> x c. BU x = Some c \<longrightarrow> IU x \<in> I \<longrightarrow> v x \<le> c))"
declare satisfies_bounds_index.simps[simp del]

fun satisfies_bounds_index' :: "'i set \<times> 'a::lrv valuation \<Rightarrow> ('a bounds \<times> 'a bounds) \<times>
  ('i bound_index \<times> 'i bound_index) \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>i\<^sub>b\<^sub>e" 100) where
  "(I,v) \<Turnstile>\<^sub>i\<^sub>b\<^sub>e ((BL,BU),(IL,IU)) \<longleftrightarrow> (
     (\<forall> x c. BL x = Some c \<longrightarrow> IL x \<in> I \<longrightarrow> v x = c)
   \<and> (\<forall> x c. BU x = Some c \<longrightarrow> IU x \<in> I \<longrightarrow> v x = c))"
declare satisfies_bounds_index'.simps[simp del]

fun atoms_imply_bounds_index :: "('i,'a::lrv) i_atom set \<Rightarrow> ('a bounds \<times> 'a bounds) \<times> ('i bound_index \<times> 'i bound_index)
  \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>i" 100) where
  "as \<Turnstile>\<^sub>i bi \<longleftrightarrow> (\<forall> I v. (I,v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s as \<longrightarrow> (I,v) \<Turnstile>\<^sub>i\<^sub>b bi)"
declare atoms_imply_bounds_index.simps[simp del]

lemma i_satisfies_atom_set_mono: "as \<subseteq> as' \<Longrightarrow> v \<Turnstile>\<^sub>i\<^sub>a\<^sub>s as' \<Longrightarrow> v \<Turnstile>\<^sub>i\<^sub>a\<^sub>s as"
  by (cases v, auto simp: satisfies_atom_set_def)

lemma atoms_imply_bounds_index_mono: "as \<subseteq> as' \<Longrightarrow> as \<Turnstile>\<^sub>i bi \<Longrightarrow> as' \<Turnstile>\<^sub>i bi"
  unfolding atoms_imply_bounds_index.simps using i_satisfies_atom_set_mono by blast

definition satisfies_state :: "'a::lrv valuation \<Rightarrow> ('i,'a) state \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>s" 100) where
  "v \<Turnstile>\<^sub>s s \<equiv> v \<Turnstile>\<^sub>b \<B> s \<and> v \<Turnstile>\<^sub>t \<T> s"

definition curr_val_satisfies_state :: "('i,'a::lrv) state \<Rightarrow> bool" ("\<Turnstile>") where
  "\<Turnstile> s \<equiv> \<langle>\<V> s\<rangle> \<Turnstile>\<^sub>s s"

fun satisfies_state_index :: "'i set \<times> 'a::lrv valuation \<Rightarrow> ('i,'a) state \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>i\<^sub>s" 100) where
  "(I,v) \<Turnstile>\<^sub>i\<^sub>s s \<longleftrightarrow> (v \<Turnstile>\<^sub>t \<T> s \<and> (I,v) \<Turnstile>\<^sub>i\<^sub>b \<B>\<I> s)"
declare satisfies_state_index.simps[simp del]

fun satisfies_state_index' :: "'i set \<times> 'a::lrv valuation \<Rightarrow> ('i,'a) state \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>i\<^sub>s\<^sub>e" 100) where
  "(I,v) \<Turnstile>\<^sub>i\<^sub>s\<^sub>e s \<longleftrightarrow> (v \<Turnstile>\<^sub>t \<T> s \<and> (I,v) \<Turnstile>\<^sub>i\<^sub>b\<^sub>e \<B>\<I> s)"
declare satisfies_state_index'.simps[simp del]

definition indices_state :: "('i,'a)state \<Rightarrow> 'i set" where
  "indices_state s = { i. \<exists> x b. look (\<B>\<^sub>i\<^sub>l s) x = Some (i,b) \<or> look (\<B>\<^sub>i\<^sub>u s) x = Some (i,b)}"

text \<open>distinctness requires that for each index $i$, there is at most one variable $x$ and bound
  $b$ such that $x \leq b$ or $x \geq b$ or both are enforced.\<close>
definition distinct_indices_state :: "('i,'a)state \<Rightarrow> bool" where
  "distinct_indices_state s = (\<forall> i x b x' b'. 
    ((look (\<B>\<^sub>i\<^sub>l s) x = Some (i,b) \<or> look (\<B>\<^sub>i\<^sub>u s) x = Some (i,b)) \<longrightarrow>
    (look (\<B>\<^sub>i\<^sub>l s) x' = Some (i,b') \<or> look (\<B>\<^sub>i\<^sub>u s) x' = Some (i,b')) \<longrightarrow>
    (x = x' \<and> b = b')))" 

lemma distinct_indices_stateD: assumes "distinct_indices_state s"
  shows "look (\<B>\<^sub>i\<^sub>l s) x = Some (i,b) \<or> look (\<B>\<^sub>i\<^sub>u s) x = Some (i,b) \<Longrightarrow> look (\<B>\<^sub>i\<^sub>l s) x' = Some (i,b') \<or> look (\<B>\<^sub>i\<^sub>u s) x' = Some (i,b')
    \<Longrightarrow> x = x' \<and> b = b'" 
  using assms unfolding distinct_indices_state_def by blast+

definition unsat_state_core :: "('i,'a::lrv) state \<Rightarrow> bool" where
  "unsat_state_core s = (set (the (\<U>\<^sub>c s)) \<subseteq> indices_state s \<and> (\<not> (\<exists> v. (set (the (\<U>\<^sub>c s)),v) \<Turnstile>\<^sub>i\<^sub>s s)))"

definition subsets_sat_core :: "('i,'a::lrv) state \<Rightarrow> bool" where
  "subsets_sat_core s = ((\<forall> I. I \<subset> set (the (\<U>\<^sub>c s)) \<longrightarrow> (\<exists> v. (I,v) \<Turnstile>\<^sub>i\<^sub>s\<^sub>e s)))" 

definition minimal_unsat_state_core :: "('i,'a::lrv) state \<Rightarrow> bool" where
  "minimal_unsat_state_core s = (unsat_state_core s \<and> (distinct_indices_state s \<longrightarrow> subsets_sat_core s))" 

lemma minimal_unsat_core_tabl_atoms_mono: assumes sub: "as \<subseteq> bs" 
  and unsat: "minimal_unsat_core_tabl_atoms I t as" 
shows "minimal_unsat_core_tabl_atoms I t bs" 
  unfolding minimal_unsat_core_tabl_atoms_def
proof (intro conjI impI allI)
  note min = unsat[unfolded minimal_unsat_core_tabl_atoms_def]
  from min have I: "I \<subseteq> fst ` as" by blast
  with sub show "I \<subseteq> fst ` bs" by blast
  from min have "(\<nexists>v. v \<Turnstile>\<^sub>t t \<and> (I, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s as)" by blast
  with i_satisfies_atom_set_mono[OF sub]
  show "(\<nexists>v. v \<Turnstile>\<^sub>t t \<and> (I, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s bs)" by blast
  fix J
  assume J: "J \<subset> I" and dist_bs: "distinct_indices_atoms bs" 
  hence dist: "distinct_indices_atoms as" 
    using sub unfolding distinct_indices_atoms_def by blast
  from min dist J obtain v where v: "v \<Turnstile>\<^sub>t t" "(J, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>e\<^sub>s as" by blast
  have "(J, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>e\<^sub>s bs"
    unfolding i_satisfies_atom_set'.simps
  proof (intro ballI)
    fix a
    assume "a \<in> snd ` (bs \<inter> J \<times> UNIV)" 
    then obtain i where ia: "(i,a) \<in> bs" and i: "i \<in> J" 
      by force
    with J have "i \<in> I" by auto 
    with I obtain b where ib: "(i,b) \<in> as" by force
    with sub have ib': "(i,b) \<in> bs" by auto
    from dist_bs[unfolded distinct_indices_atoms_def, rule_format, OF ia ib']
    have id: "atom_var a = atom_var b" "atom_const a = atom_const b" by auto
    from v(2)[unfolded i_satisfies_atom_set'.simps] i ib 
    have "v \<Turnstile>\<^sub>a\<^sub>e b" by force
    thus "v \<Turnstile>\<^sub>a\<^sub>e a" using id unfolding satisfies_atom'_def by auto
  qed
  with v show "\<exists>v. v \<Turnstile>\<^sub>t t \<and> (J, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>e\<^sub>s bs" by blast
qed

lemma state_satisfies_index: assumes "v \<Turnstile>\<^sub>s s"
  shows "(I,v) \<Turnstile>\<^sub>i\<^sub>s s"
  unfolding satisfies_state_index.simps satisfies_bounds_index.simps
proof (intro conjI impI allI)
  fix x c
  from assms[unfolded satisfies_state_def satisfies_bounds.simps, simplified]
  have "v \<Turnstile>\<^sub>t \<T> s" and bnd: "v x \<ge>\<^sub>l\<^sub>b \<B>\<^sub>l s x" "v x \<le>\<^sub>u\<^sub>b \<B>\<^sub>u s x" by auto
  show "v \<Turnstile>\<^sub>t \<T> s" by fact
  show "\<B>\<^sub>l s x = Some c \<Longrightarrow> \<I>\<^sub>l s x \<in> I \<Longrightarrow> c \<le> v x"
    using bnd(1) by auto
  show "\<B>\<^sub>u s x = Some c \<Longrightarrow> \<I>\<^sub>u s x \<in> I \<Longrightarrow> v x \<le> c"
    using bnd(2) by auto
qed

lemma unsat_state_core_unsat: "unsat_state_core s \<Longrightarrow> \<not> (\<exists> v. v \<Turnstile>\<^sub>s s)"
  unfolding unsat_state_core_def using state_satisfies_index by blast

definition tableau_valuated ("\<nabla>") where
  "\<nabla> s \<equiv> \<forall> x \<in> tvars (\<T> s). Mapping.lookup (\<V> s) x \<noteq> None"

definition index_valid where
  "index_valid as (s :: ('i,'a) state) = (\<forall> x b i.
      (look (\<B>\<^sub>i\<^sub>l s) x = Some (i,b) \<longrightarrow> ((i, Geq x b) \<in> as))
    \<and> (look (\<B>\<^sub>i\<^sub>u s) x = Some (i,b) \<longrightarrow> ((i, Leq x b) \<in> as)))"

lemma index_valid_indices_state: "index_valid as s \<Longrightarrow> indices_state s \<subseteq> fst ` as"
  unfolding index_valid_def indices_state_def by force

lemma index_valid_mono: "as \<subseteq> bs \<Longrightarrow> index_valid as s \<Longrightarrow> index_valid bs s"
  unfolding index_valid_def by blast

lemma index_valid_distinct_indices: assumes "index_valid as s" 
  and "distinct_indices_atoms as" 
shows "distinct_indices_state s" 
  unfolding distinct_indices_state_def
proof (intro allI impI, goal_cases)
  case (1 i x b y c)
  note valid = assms(1)[unfolded index_valid_def, rule_format]
  from 1(1) valid[of x i b] have "(i, Geq x b) \<in> as \<or> (i, Leq x b) \<in> as" by auto
  then obtain a where a: "(i,a) \<in> as" "atom_var a = x" "atom_const a = b" by auto
  from 1(2) valid[of y i c] have y: "(i, Geq y c) \<in> as \<or> (i, Leq y c) \<in> as" by auto
  then obtain a' where a': "(i,a') \<in> as" "atom_var a' = y" "atom_const a' = c" by auto
  from assms(2)[unfolded distinct_indices_atoms_def, rule_format, OF a(1) a'(1)]
  show ?case using a a' by auto
qed

text\<open>To be a solution of the initial problem, a valuation should
satisfy the initial tableau and list of atoms. Since tableau is
changed only by equivalency preserving transformations and asserted
atoms are encoded in the bounds, a valuation is a solution if it
satisfies both the tableau and the bounds in the final state (when all
atoms have been asserted). So, a valuation \<open>v\<close> satisfies a state
\<open>s\<close> (denoted by \<open>\<Turnstile>\<^sub>s\<close>) if it satisfies the tableau and
the bounds, i.e., @{thm satisfies_state_def [no_vars]}. Since \<open>\<V>\<close> should be a candidate solution, it should satisfy the state
(unless the \<open>\<U>\<close> flag is raised). This is denoted by \<open>\<Turnstile> s\<close>
and defined by @{thm curr_val_satisfies_state_def[no_vars]}. \<open>\<nabla>
s\<close> will denote that all variables of \<open>\<T> s\<close> are explicitly
valuated in \<open>\<V> s\<close>.\<close>

definition update\<B>\<I> where
  [simp]: "update\<B>\<I> field_update i x c s = field_update (upd x (i,c)) s"

fun \<B>\<^sub>i\<^sub>u_update where
  "\<B>\<^sub>i\<^sub>u_update up (State T BIL BIU V U UC) = State T BIL (up BIU) V U UC"

fun \<B>\<^sub>i\<^sub>l_update where
  "\<B>\<^sub>i\<^sub>l_update up (State T BIL BIU V U UC) = State T (up BIL) BIU V U UC"

fun \<V>_update where
  "\<V>_update V (State T BIL BIU V_old U UC) = State T BIL BIU V U UC"

fun \<T>_update where
  "\<T>_update T (State T_old BIL BIU V U UC) = State T BIL BIU V U UC"

lemma update_simps[simp]:
  "\<B>\<^sub>i\<^sub>u (\<B>\<^sub>i\<^sub>u_update up s) = up (\<B>\<^sub>i\<^sub>u s)"
  "\<B>\<^sub>i\<^sub>l (\<B>\<^sub>i\<^sub>u_update up s) = \<B>\<^sub>i\<^sub>l s"
  "\<T> (\<B>\<^sub>i\<^sub>u_update up s) = \<T> s"
  "\<V> (\<B>\<^sub>i\<^sub>u_update up s) = \<V> s"
  "\<U> (\<B>\<^sub>i\<^sub>u_update up s) = \<U> s"
  "\<U>\<^sub>c (\<B>\<^sub>i\<^sub>u_update up s) = \<U>\<^sub>c s"
  "\<B>\<^sub>i\<^sub>l (\<B>\<^sub>i\<^sub>l_update up s) = up (\<B>\<^sub>i\<^sub>l s)"
  "\<B>\<^sub>i\<^sub>u (\<B>\<^sub>i\<^sub>l_update up s) = \<B>\<^sub>i\<^sub>u s"
  "\<T> (\<B>\<^sub>i\<^sub>l_update up s) = \<T> s"
  "\<V> (\<B>\<^sub>i\<^sub>l_update up s) = \<V> s"
  "\<U> (\<B>\<^sub>i\<^sub>l_update up s) = \<U> s"
  "\<U>\<^sub>c (\<B>\<^sub>i\<^sub>l_update up s) = \<U>\<^sub>c s"
  "\<V> (\<V>_update V s) = V"
  "\<B>\<^sub>i\<^sub>l (\<V>_update V s) = \<B>\<^sub>i\<^sub>l s"
  "\<B>\<^sub>i\<^sub>u (\<V>_update V s) = \<B>\<^sub>i\<^sub>u s"
  "\<T> (\<V>_update V s) = \<T> s"
  "\<U> (\<V>_update V s) = \<U> s"
  "\<U>\<^sub>c (\<V>_update V s) = \<U>\<^sub>c s"
  "\<T> (\<T>_update T s) = T"
  "\<B>\<^sub>i\<^sub>l (\<T>_update T s) = \<B>\<^sub>i\<^sub>l s"
  "\<B>\<^sub>i\<^sub>u (\<T>_update T s) = \<B>\<^sub>i\<^sub>u s"
  "\<V> (\<T>_update T s) = \<V> s"
  "\<U> (\<T>_update T s) = \<U> s"
  "\<U>\<^sub>c (\<T>_update T s) = \<U>\<^sub>c s"
  by (atomize(full), cases s, auto)

declare
  \<B>\<^sub>i\<^sub>u_update.simps[simp del]
  \<B>\<^sub>i\<^sub>l_update.simps[simp del]

fun set_unsat :: "'i list \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state" where
  "set_unsat I (State T BIL BIU V U UC) = State T BIL BIU V True (Some (remdups I))"

lemma set_unsat_simps[simp]: "\<B>\<^sub>i\<^sub>l (set_unsat I s) = \<B>\<^sub>i\<^sub>l s"
  "\<B>\<^sub>i\<^sub>u (set_unsat I s) = \<B>\<^sub>i\<^sub>u s"
  "\<T> (set_unsat I s) = \<T> s"
  "\<V> (set_unsat I s) = \<V> s"
  "\<U> (set_unsat I s) = True"
  "\<U>\<^sub>c (set_unsat I s) = Some (remdups I)"
  by (atomize(full), cases s, auto)

datatype ('i,'a) Direction = Direction
  (lt: "'a::linorder \<Rightarrow> 'a \<Rightarrow> bool")
  (LBI: "('i,'a) state \<Rightarrow> ('i,'a) bounds_index")
  (UBI: "('i,'a) state \<Rightarrow> ('i,'a) bounds_index")
  (LB: "('i,'a) state \<Rightarrow> 'a bounds")
  (UB: "('i,'a) state \<Rightarrow> 'a bounds")
  (LI: "('i,'a) state \<Rightarrow> 'i bound_index")
  (UI: "('i,'a) state \<Rightarrow> 'i bound_index")
  (UBI_upd: "(('i,'a) bounds_index \<Rightarrow> ('i,'a) bounds_index) \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state")
  (LE: "var \<Rightarrow> 'a \<Rightarrow> 'a atom")
  (GE: "var \<Rightarrow> 'a \<Rightarrow> 'a atom")
  (le_rat: "rat \<Rightarrow> rat \<Rightarrow> bool")

definition Positive where
  [simp]: "Positive \<equiv> Direction (<) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>l \<B>\<^sub>u \<I>\<^sub>l \<I>\<^sub>u \<B>\<^sub>i\<^sub>u_update Leq Geq (\<le>)"

definition Negative where
  [simp]: "Negative \<equiv> Direction (>) \<B>\<^sub>i\<^sub>u \<B>\<^sub>i\<^sub>l \<B>\<^sub>u \<B>\<^sub>l \<I>\<^sub>u \<I>\<^sub>l \<B>\<^sub>i\<^sub>l_update Geq Leq (\<ge>)"


text\<open>Assuming that the \<open>\<U>\<close> flag and the current valuation
\<open>\<V>\<close> in the final state determine the solution of a problem, the
\<open>assert_all\<close> function can be reduced to the \<open>assert_all_state\<close>
function that operates on the states:
@{text[display] "assert_all t as \<equiv> let s = assert_all_state t as in
   if (\<U> s) then (False, None) else (True, Some (\<V> s))" }
\<close>
text\<open>Specification for the \<open>assert_all_state\<close> can be directly
obtained from the specification of \<open>assert_all\<close>, and it describes
the connection between the valuation in the final state and the
initial tableau and atoms. However, we will make an additional
refinement step and give stronger assumptions about the \<open>assert_all_state\<close> function that describes the connection between
the initial tableau and atoms with the tableau and bounds in the final
state.\<close>

locale AssertAllState = fixes assert_all_state::"tableau \<Rightarrow> ('i,'a::lrv) i_atom list \<Rightarrow> ('i,'a) state"
  assumes
    \<comment> \<open>The final and the initial tableau are equivalent.\<close>
    assert_all_state_tableau_equiv: "\<triangle> t \<Longrightarrow> assert_all_state t as = s' \<Longrightarrow> (v::'a valuation) \<Turnstile>\<^sub>t t \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> s'" and

\<comment> \<open>If @{term \<U>} is not raised, then the valuation in the
final state satisfies its tableau and its bounds (that are, in this
case, equivalent to the set of all asserted bounds).\<close>
assert_all_state_sat: "\<triangle> t \<Longrightarrow> assert_all_state t as = s' \<Longrightarrow> \<not> \<U> s' \<Longrightarrow> \<Turnstile> s'" and

assert_all_state_sat_atoms_equiv_bounds: "\<triangle> t \<Longrightarrow> assert_all_state t as = s' \<Longrightarrow> \<not> \<U> s' \<Longrightarrow> flat (set as) \<doteq> \<B> s'" and

\<comment> \<open>If @{term \<U>} is raised, then there is no valuation
   satisfying the tableau and the bounds in the final state (that are,
   in this case, equivalent to a subset of asserted atoms).\<close>
assert_all_state_unsat: "\<triangle> t \<Longrightarrow> assert_all_state t as = s' \<Longrightarrow> \<U> s' \<Longrightarrow> minimal_unsat_state_core s'"  and

assert_all_state_unsat_atoms_equiv_bounds: "\<triangle> t \<Longrightarrow> assert_all_state t as = s' \<Longrightarrow> \<U> s' \<Longrightarrow> set as \<Turnstile>\<^sub>i \<B>\<I> s'" and

\<comment> \<open>The set of indices is taken from the constraints\<close>
assert_all_state_indices: "\<triangle> t \<Longrightarrow> assert_all_state t as = s \<Longrightarrow> indices_state s \<subseteq> fst ` set as" and

assert_all_index_valid: "\<triangle> t \<Longrightarrow> assert_all_state t as = s \<Longrightarrow> index_valid (set as) s"
begin
definition assert_all where
  "assert_all t as \<equiv> let s = assert_all_state t as in
     if (\<U> s) then Unsat (the (\<U>\<^sub>c s)) else Sat (\<V> s)"
end

text\<open>The \<open>assert_all_state\<close> function can be implemented by first
applying the \<open>init\<close> function that creates an initial state based
on the starting tableau, and then by iteratively applying the \<open>assert\<close> function for each atom in the starting atoms list.\<close>

text\<open>
\begin{small}
  \<open>assert_loop as s \<equiv> foldl (\<lambda> s' a. if (\<U> s') then s' else assert a s') s as\<close>

  \<open>assert_all_state t as \<equiv> assert_loop ats (init t)\<close>
\end{small}
\<close>


locale Init' =
  fixes init :: "tableau \<Rightarrow> ('i,'a::lrv) state"
  assumes init'_tableau_normalized: "\<triangle> t \<Longrightarrow> \<triangle> (\<T> (init t))"
  assumes init'_tableau_equiv: "\<triangle> t \<Longrightarrow> (v::'a valuation) \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t \<T> (init t)"
  assumes init'_sat: "\<triangle> t \<Longrightarrow> \<not> \<U> (init t) \<longrightarrow> \<Turnstile> (init t)"
  assumes init'_unsat: "\<triangle> t \<Longrightarrow> \<U> (init t) \<longrightarrow> minimal_unsat_state_core (init t)"
  assumes init'_atoms_equiv_bounds: "\<triangle> t \<Longrightarrow> {} \<doteq> \<B> (init t)"
  assumes init'_atoms_imply_bounds_index: "\<triangle> t \<Longrightarrow> {} \<Turnstile>\<^sub>i \<B>\<I> (init t)"


text\<open>Specification for \<open>init\<close> can be obtained from the
specification of \<open>asser_all_state\<close> since all its assumptions
must also hold for \<open>init\<close> (when the list of atoms is
empty). Also, since \<open>init\<close> is the first step in the \<open>assert_all_state\<close> implementation, the precondition for \<open>init\<close>
the same as for the \<open>assert_all_state\<close>. However,
unsatisfiability is never going to be detected during initialization
and @{term \<U>} flag is never going to be raised. Also, the tableau in
the initial state can just be initialized with the starting
tableau. The condition @{term "{} \<doteq> \<B> (init t)"} is equivalent to
asking that initial bounds are empty. Therefore, specification for
\<open>init\<close> can be refined to:\<close>

locale Init = fixes init::"tableau \<Rightarrow> ('i,'a::lrv) state"
  assumes
    \<comment> \<open>Tableau in the initial state for @{text t} is @{text t}:\<close> init_tableau_id: "\<T> (init t) = t" and

\<comment> \<open>Since unsatisfiability is not detected, @{text \<U>}
     flag must not be set:\<close> init_unsat_flag: "\<not> \<U> (init t)" and

\<comment> \<open>The current valuation must satisfy the tableau:\<close> init_satisfies_tableau: "\<langle>\<V> (init t)\<rangle> \<Turnstile>\<^sub>t t" and

\<comment> \<open>In an inital state no atoms are yet asserted so the bounds
     must be empty:\<close>
init_bounds: "\<B>\<^sub>i\<^sub>l (init t) = Mapping.empty"   "\<B>\<^sub>i\<^sub>u (init t) = Mapping.empty"  and

\<comment> \<open>All tableau vars are valuated:\<close> init_tableau_valuated: "\<nabla> (init t)"

begin


lemma init_satisfies_bounds:
  "\<langle>\<V> (init t)\<rangle> \<Turnstile>\<^sub>b \<B> (init t)"
  using init_bounds
  unfolding satisfies_bounds.simps in_bounds.simps bound_compare_defs
  by (auto simp: boundsl_def boundsu_def)

lemma init_satisfies:
  "\<Turnstile> (init t)"
  using init_satisfies_tableau init_satisfies_bounds init_tableau_id
  unfolding curr_val_satisfies_state_def satisfies_state_def
  by simp

lemma init_atoms_equiv_bounds:
  "{} \<doteq> \<B> (init t)"
  using init_bounds
  unfolding atoms_equiv_bounds.simps satisfies_bounds.simps in_bounds.simps satisfies_atom_set_def
  unfolding bound_compare_defs
  by (auto simp: indexl_def indexu_def boundsl_def boundsu_def)

lemma init_atoms_imply_bounds_index:
  "{} \<Turnstile>\<^sub>i \<B>\<I> (init t)"
  using init_bounds
  unfolding atoms_imply_bounds_index.simps satisfies_bounds_index.simps in_bounds.simps
    i_satisfies_atom_set.simps satisfies_atom_set_def
  unfolding bound_compare_defs
  by (auto simp: indexl_def indexu_def boundsl_def boundsu_def)


lemma init_tableau_normalized:
  "\<triangle> t \<Longrightarrow> \<triangle> (\<T> (init t))"
  using init_tableau_id
  by simp

lemma init_index_valid: "index_valid as (init t)"
  using init_bounds unfolding index_valid_def by auto

lemma init_indices: "indices_state (init t) = {}"
  unfolding indices_state_def init_bounds by auto
end


sublocale Init < Init' init
  using init_tableau_id init_satisfies init_unsat_flag init_atoms_equiv_bounds init_atoms_imply_bounds_index
  by unfold_locales auto



abbreviation vars_list where
  "vars_list t \<equiv> remdups (map lhs t @ (concat (map (Abstract_Linear_Poly.vars_list \<circ> rhs) t)))"

lemma "tvars t = set (vars_list t)"
  by (auto simp add: set_vars_list lvars_def rvars_def)


text\<open>\smallskip The \<open>assert\<close> function asserts a single
atom. Since the \<open>init\<close> function does not raise the \<open>\<U>\<close>
flag, from the definition of \<open>assert_loop\<close>, it is clear that the
flag is not raised when the \<open>assert\<close> function is
called. Moreover, the assumptions about the \<open>assert_all_state\<close>
imply that the loop invariant must be that if the \<open>\<U>\<close> flag is
not raised, then the current valuation must satisfy the state (i.e.,
\<open>\<Turnstile> s\<close>). The \<open>assert\<close> function will be more easily
implemented if it is always applied to a state with a normalized and
valuated tableau, so we make this another loop invariant. Therefore,
the precondition for the \<open>assert a s\<close> function call is that
\<open>\<not> \<U> s\<close>, \<open>\<Turnstile> s\<close>, \<open>\<triangle> (\<T> s)\<close> and \<open>\<nabla> s\<close>
hold. The specification for \<open>assert\<close> directly follows from the
specification of \<open>assert_all_state\<close> (except that it is
additionally required that bounds reflect asserted atoms also when
unsatisfiability is detected, and that it is required that \<open>assert\<close> keeps the tableau normalized and valuated).\<close>

locale Assert = fixes assert::"('i,'a::lrv) i_atom \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state"
  assumes
    \<comment> \<open>Tableau remains equivalent to the previous one and normalized and valuated.\<close>
    assert_tableau: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> let s' = assert a s in
     ((v::'a valuation) \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> s') \<and> \<triangle> (\<T> s') \<and> \<nabla> s'" and

\<comment> \<open>If the @{term \<U>} flag is not raised, then the current
   valuation is updated so that it satisfies the current tableau and
   the current bounds.\<close>
assert_sat: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<not> \<U> (assert a s) \<Longrightarrow> \<Turnstile> (assert a s)" and

\<comment> \<open>The set of asserted atoms remains equivalent to the bounds
    in the state.\<close>
assert_atoms_equiv_bounds: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> flat ats \<doteq> \<B> s \<Longrightarrow> flat (ats \<union> {a}) \<doteq> \<B> (assert a s)" and

\<comment> \<open>There is a subset of asserted atoms which remains index-equivalent to the bounds
    in the state.\<close>
assert_atoms_imply_bounds_index: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> ats \<Turnstile>\<^sub>i \<B>\<I> s \<Longrightarrow>
  insert a ats \<Turnstile>\<^sub>i \<B>\<I> (assert a s)" and

\<comment> \<open>If the @{term \<U>} flag is raised, then there is no valuation
   that satisfies both the current tableau and the current bounds.\<close>
assert_unsat: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s; index_valid ats s\<rbrakk> \<Longrightarrow> \<U> (assert a s) \<Longrightarrow>  minimal_unsat_state_core (assert a s)" and

assert_index_valid: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> index_valid ats s \<Longrightarrow> index_valid (insert a ats) (assert a s)"

begin
lemma assert_tableau_equiv: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> (v::'a valuation) \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> (assert a s)"
  using assert_tableau
  by (simp add: Let_def)

lemma assert_tableau_normalized: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<triangle> (\<T> (assert a s))"
  using assert_tableau
  by (simp add: Let_def)

lemma assert_tableau_valuated: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<nabla> (assert a s)"
  using assert_tableau
  by (simp add: Let_def)
end



locale AssertAllState' = Init init + Assert assert for
  init :: "tableau \<Rightarrow> ('i,'a::lrv) state" and assert :: "('i,'a) i_atom \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state"
begin

definition assert_loop where
  "assert_loop as s \<equiv> foldl (\<lambda> s' a. if (\<U> s') then s' else assert a s') s as"

definition assert_all_state where [simp]:
  "assert_all_state t as \<equiv> assert_loop as (init t)"


lemma AssertAllState'_precond:
  "\<triangle> t \<Longrightarrow> \<triangle> (\<T> (assert_all_state t as))
    \<and> (\<nabla> (assert_all_state t as))
    \<and> (\<not> \<U> (assert_all_state t as) \<longrightarrow> \<Turnstile> (assert_all_state t as))"
  unfolding assert_all_state_def assert_loop_def
  using init_satisfies init_tableau_normalized init_index_valid
  using assert_sat assert_tableau_normalized init_tableau_valuated assert_tableau_valuated
  by (induct as rule: rev_induct) auto

lemma AssertAllState'Induct:
  assumes
    "\<triangle> t"
    "P {} (init t)"
    "\<And> as bs t. as \<subseteq> bs \<Longrightarrow> P as t \<Longrightarrow> P bs t"
    "\<And> s a as. \<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s; P as s; index_valid as s\<rbrakk> \<Longrightarrow> P (insert a as) (assert a s)"
  shows "P (set as) (assert_all_state t as)"
proof -
  have "P (set as) (assert_all_state t as) \<and> index_valid (set as) (assert_all_state t as)"
  proof (induct as rule: rev_induct)
    case Nil
    then show ?case
      unfolding assert_all_state_def assert_loop_def
      using assms(2) init_index_valid by auto
  next
    case (snoc a as')
    let ?f = "\<lambda>s' a. if \<U> s' then s' else assert a s'"
    let ?s = "foldl ?f (init t) as'"
    show ?case
    proof (cases "\<U> ?s")
      case True
      from snoc index_valid_mono[of _ "set (a # as')" "(assert_all_state t as')"]
      have index: "index_valid (set (a # as')) (assert_all_state t as')"
        by auto
      from snoc assms(3)[of "set as'" "set (a # as')"]
      have P: "P (set (a # as')) (assert_all_state t as')" by auto
      show ?thesis
        using True P index
        unfolding assert_all_state_def assert_loop_def
        by simp
    next
      case False
      then show ?thesis
        using snoc
        using assms(1) assms(4)
        using AssertAllState'_precond assert_index_valid
        unfolding assert_all_state_def assert_loop_def
        by auto
    qed
  qed
  then show ?thesis ..
qed

lemma AssertAllState_index_valid: "\<triangle> t \<Longrightarrow> index_valid (set as) (assert_all_state t as)"
  by (rule AssertAllState'Induct, auto intro: assert_index_valid init_index_valid index_valid_mono)

lemma AssertAllState'_sat_atoms_equiv_bounds:
  "\<triangle> t \<Longrightarrow> \<not> \<U> (assert_all_state t as) \<Longrightarrow> flat (set as) \<doteq> \<B> (assert_all_state t as)"
  using AssertAllState'_precond
  using init_atoms_equiv_bounds assert_atoms_equiv_bounds
  unfolding assert_all_state_def assert_loop_def
  by (induct as rule: rev_induct) auto

lemma AssertAllState'_unsat_atoms_implies_bounds:
  assumes "\<triangle> t"
  shows "set as \<Turnstile>\<^sub>i \<B>\<I> (assert_all_state t as)"
proof (induct as rule: rev_induct)
  case Nil
  then show ?case
    using assms init_atoms_imply_bounds_index
    unfolding assert_all_state_def assert_loop_def
    by simp
next
  case (snoc a as')
  let ?s = "assert_all_state t as'"
  show ?case
  proof (cases "\<U> ?s")
    case True
    then show ?thesis
      using snoc atoms_imply_bounds_index_mono[of "set as'" "set (as' @ [a])"]
      unfolding assert_all_state_def assert_loop_def
      by auto
  next
    case False
    then have id: "assert_all_state t (as' @ [a]) = assert a ?s"
      unfolding assert_all_state_def assert_loop_def by simp
    from snoc have as': "set as' \<Turnstile>\<^sub>i \<B>\<I> ?s" by auto
    from AssertAllState'_precond[of t as'] assms False
    have "\<Turnstile> ?s" "\<triangle> (\<T> ?s)" "\<nabla> ?s" by auto
    from assert_atoms_imply_bounds_index[OF False this as', of a]
    show ?thesis unfolding id by auto
  qed
qed

end

text\<open>Under these assumptions, it can easily be shown (mainly by
induction) that the previously shown implementation of \<open>assert_all_state\<close> satisfies its specification.\<close>

sublocale AssertAllState' < AssertAllState assert_all_state
proof
  fix v::"'a valuation" and t as s'
  assume *: "\<triangle> t" and id: "assert_all_state t as = s'"
  note idsym = id[symmetric]

  show "v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t \<T> s'" unfolding idsym
    using  init_tableau_id[of t] assert_tableau_equiv[of _ v]
    by (induct rule: AssertAllState'Induct) (auto simp add: * )

  show "\<not> \<U> s' \<Longrightarrow> \<Turnstile> s'" unfolding idsym
    using AssertAllState'_precond by (simp add: * )

  show "\<not> \<U> s' \<Longrightarrow> flat (set as) \<doteq> \<B> s'"
    unfolding idsym
    using *
    by (rule AssertAllState'_sat_atoms_equiv_bounds)

  show "\<U> s' \<Longrightarrow> set as \<Turnstile>\<^sub>i \<B>\<I> s'"
    using * unfolding idsym
    by (rule AssertAllState'_unsat_atoms_implies_bounds)

  show "\<U> s' \<Longrightarrow> minimal_unsat_state_core s'"
    using init_unsat_flag assert_unsat assert_index_valid unfolding idsym
    by (induct rule: AssertAllState'Induct) (auto simp add: * )

  show "indices_state s' \<subseteq> fst ` set as" unfolding idsym using *
    by (intro index_valid_indices_state, induct rule: AssertAllState'Induct,
        auto simp: init_index_valid index_valid_mono assert_index_valid)

  show "index_valid (set as) s'" using "*" AssertAllState_index_valid idsym by blast
qed


subsection\<open>Asserting Single Atoms\<close>

text\<open>The @{term assert} function is split in two phases. First,
@{term assert_bound} updates the bounds and checks only for conflicts
cheap to detect. Next, \<open>check\<close> performs the full simplex
algorithm. The \<open>assert\<close> function can be implemented as \<open>assert a s = check (assert_bound a s)\<close>. Note that it is also
possible to do the first phase for several asserted atoms, and only
then to let the expensive second phase work.

\medskip Asserting an atom \<open>x \<bowtie> b\<close> begins with the function
\<open>assert_bound\<close>.  If the atom is subsumed by the current bounds,
then no changes are performed. Otherwise, bounds for \<open>x\<close> are
changed to incorporate the atom. If the atom is inconsistent with the
previous bounds for \<open>x\<close>, the @{term \<U>} flag is raised. If
\<open>x\<close> is not a lhs variable in the current tableau and if the
value for \<open>x\<close> in the current valuation violates the new bound
\<open>b\<close>, the value for \<open>x\<close> can be updated and set to
\<open>b\<close>, meanwhile updating the values for lhs variables of
the tableau so that it remains satisfied. Otherwise, no changes to the
current valuation are performed.\<close>

fun satisfies_bounds_set  :: "'a::linorder valuation \<Rightarrow> 'a bounds \<times> 'a bounds \<Rightarrow> var set \<Rightarrow> bool" where
  "satisfies_bounds_set v (lb, ub) S \<longleftrightarrow> (\<forall> x \<in> S. in_bounds x v (lb, ub))"
declare satisfies_bounds_set.simps [simp del]
syntax
  "_satisfies_bounds_set" :: "(var \<Rightarrow> 'a::linorder) \<Rightarrow> 'a bounds \<times> 'a bounds \<Rightarrow> var set \<Rightarrow> bool"    ("_ \<Turnstile>\<^sub>b _ \<parallel>/ _")
translations
  "v \<Turnstile>\<^sub>b b \<parallel> S" == "CONST satisfies_bounds_set v b S"
lemma satisfies_bounds_set_iff:
  "v \<Turnstile>\<^sub>b (lb, ub) \<parallel> S \<equiv> (\<forall> x \<in> S. v x \<ge>\<^sub>l\<^sub>b lb x \<and> v x \<le>\<^sub>u\<^sub>b ub x)"
  by (simp add: satisfies_bounds_set.simps)


definition curr_val_satisfies_no_lhs ("\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s") where
  "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s \<equiv> \<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t (\<T> s) \<and> (\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>b (\<B> s) \<parallel> (- lvars (\<T> s)))"
lemma satisfies_satisfies_no_lhs:
  "\<Turnstile> s \<Longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"
  by (simp add: curr_val_satisfies_state_def satisfies_state_def curr_val_satisfies_no_lhs_def satisfies_bounds.simps satisfies_bounds_set.simps)


definition bounds_consistent :: "('i,'a::linorder) state \<Rightarrow> bool" ("\<diamond>") where
  "\<diamond> s \<equiv>
   \<forall> x. if \<B>\<^sub>l s x = None \<or> \<B>\<^sub>u s x = None then True else the (\<B>\<^sub>l s x) \<le> the (\<B>\<^sub>u s x)"


text\<open>So, the \<open>assert_bound\<close> function must ensure that the
given atom is included in the bounds, that the tableau remains
satisfied by the valuation and that all variables except the lhs variables
in the tableau are within their
bounds. To formalize this, we introduce the notation \<open>v
\<Turnstile>\<^sub>b (lb, ub) \<parallel> S\<close>, and define @{thm
satisfies_bounds_set_iff[no_vars]}, and @{thm
curr_val_satisfies_no_lhs_def[no_vars]}. The \<open>assert_bound\<close>
function raises the \<open>\<U>\<close> flag if and only if lower and upper
bounds overlap. This is formalized as @{thm
bounds_consistent_def[no_vars]}.\<close>


lemma satisfies_bounds_consistent:
  "(v::'a::linorder valuation) \<Turnstile>\<^sub>b \<B> s \<longrightarrow> \<diamond> s"
  unfolding satisfies_bounds.simps in_bounds.simps bounds_consistent_def bound_compare_defs
  by (auto split: option.split) force

lemma satisfies_consistent:
  "\<Turnstile> s \<longrightarrow> \<diamond> s"
  by (auto simp add: curr_val_satisfies_state_def satisfies_state_def satisfies_bounds_consistent)

lemma bounds_consistent_geq_lb:
  "\<lbrakk>\<diamond> s; \<B>\<^sub>u s x\<^sub>i = Some c\<rbrakk>
    \<Longrightarrow> c \<ge>\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i"
  unfolding bounds_consistent_def
  by (cases "\<B>\<^sub>l s x\<^sub>i", auto simp add: bound_compare_defs split: if_splits)
    (erule_tac x="x\<^sub>i" in allE, auto)

lemma bounds_consistent_leq_ub:
  "\<lbrakk>\<diamond> s; \<B>\<^sub>l s x\<^sub>i = Some c\<rbrakk>
    \<Longrightarrow> c \<le>\<^sub>u\<^sub>b \<B>\<^sub>u s x\<^sub>i"
  unfolding bounds_consistent_def
  by (cases "\<B>\<^sub>u s x\<^sub>i", auto simp add: bound_compare_defs split: if_splits)
    (erule_tac x="x\<^sub>i" in allE, auto)

lemma bounds_consistent_gt_ub:
  "\<lbrakk>\<diamond> s; c <\<^sub>l\<^sub>b \<B>\<^sub>l s x \<rbrakk> \<Longrightarrow> \<not> c >\<^sub>u\<^sub>b \<B>\<^sub>u s x"
  unfolding bounds_consistent_def
  by (case_tac[!] "\<B>\<^sub>l s x", case_tac[!] "\<B>\<^sub>u s x")
    (auto simp add: bound_compare_defs, erule_tac x="x" in allE, simp)

lemma bounds_consistent_lt_lb:
  "\<lbrakk>\<diamond> s; c >\<^sub>u\<^sub>b \<B>\<^sub>u s x \<rbrakk> \<Longrightarrow> \<not> c <\<^sub>l\<^sub>b \<B>\<^sub>l s x"
  unfolding bounds_consistent_def
  by (case_tac[!] "\<B>\<^sub>l s x", case_tac[!] "\<B>\<^sub>u s x")
    (auto simp add: bound_compare_defs, erule_tac x="x" in allE, simp)


text\<open>Since the \<open>assert_bound\<close> is the first step in the \<open>assert\<close> function implementation, the preconditions for \<open>assert_bound\<close> are the same as preconditions for the \<open>assert\<close>
function. The specifiction for the \<open>assert_bound\<close> is:\<close>

locale AssertBound = fixes assert_bound::"('i,'a::lrv) i_atom \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state"
  assumes
    \<comment> \<open>The tableau remains unchanged and valuated.\<close>

assert_bound_tableau: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> assert_bound a s = s' \<Longrightarrow> \<T> s' = \<T> s \<and> \<nabla> s'" and

\<comment> \<open>If the @{term \<U>} flag is not set, all but the
   lhs variables in the tableau remain within their bounds,
   the new valuation satisfies the tableau, and bounds do not overlap.\<close>
assert_bound_sat: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> assert_bound a s = s' \<Longrightarrow> \<not> \<U> s' \<Longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s' \<and> \<diamond> s'" and

\<comment> \<open>The set of asserted atoms remains equivalent to the bounds in the state.\<close>

assert_bound_atoms_equiv_bounds: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow>
  flat ats \<doteq> \<B> s \<Longrightarrow> flat (ats \<union> {a}) \<doteq> \<B> (assert_bound a s)" and

assert_bound_atoms_imply_bounds_index: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow>
  ats \<Turnstile>\<^sub>i \<B>\<I> s \<Longrightarrow> insert a ats \<Turnstile>\<^sub>i \<B>\<I> (assert_bound a s)" and

\<comment> \<open>@{term \<U>} flag is raised, only if the bounds became inconsistent:\<close>

assert_bound_unsat: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> index_valid as s \<Longrightarrow> assert_bound a s = s' \<Longrightarrow> \<U> s' \<Longrightarrow> minimal_unsat_state_core s'" and

assert_bound_index_valid: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> index_valid as s \<Longrightarrow> index_valid (insert a as) (assert_bound a s)"

begin
lemma assert_bound_tableau_id: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<T> (assert_bound a s) = \<T> s"
  using assert_bound_tableau by blast

lemma assert_bound_tableau_valuated: "\<lbrakk>\<not> \<U> s; \<Turnstile> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<nabla> (assert_bound a s)"
  using assert_bound_tableau by blast

end

locale AssertBoundNoLhs =
  fixes assert_bound :: "('i,'a::lrv) i_atom \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state"
  assumes assert_bound_nolhs_tableau_id: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s\<rbrakk> \<Longrightarrow> \<T> (assert_bound a s) = \<T> s"
  assumes assert_bound_nolhs_sat: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s\<rbrakk> \<Longrightarrow>
    \<not> \<U> (assert_bound a s) \<Longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s (assert_bound a s) \<and> \<diamond> (assert_bound a s)"
  assumes assert_bound_nolhs_atoms_equiv_bounds: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s\<rbrakk> \<Longrightarrow>
    flat ats \<doteq> \<B> s \<Longrightarrow> flat (ats \<union> {a}) \<doteq> \<B> (assert_bound a s)"
  assumes assert_bound_nolhs_atoms_imply_bounds_index: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s\<rbrakk> \<Longrightarrow>
    ats \<Turnstile>\<^sub>i \<B>\<I> s \<Longrightarrow> insert a ats \<Turnstile>\<^sub>i \<B>\<I> (assert_bound a s)"
  assumes assert_bound_nolhs_unsat: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s\<rbrakk> \<Longrightarrow>
    index_valid as s \<Longrightarrow> \<U> (assert_bound a s) \<Longrightarrow> minimal_unsat_state_core (assert_bound a s)"
  assumes assert_bound_nolhs_tableau_valuated: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s\<rbrakk> \<Longrightarrow>
   \<nabla> (assert_bound a s)"
  assumes assert_bound_nolhs_index_valid: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s\<rbrakk> \<Longrightarrow>
    index_valid as s \<Longrightarrow> index_valid (insert a as) (assert_bound a s)"

sublocale AssertBoundNoLhs < AssertBound 
  by unfold_locales
    ((metis satisfies_satisfies_no_lhs satisfies_consistent
        assert_bound_nolhs_tableau_id assert_bound_nolhs_sat assert_bound_nolhs_atoms_equiv_bounds
        assert_bound_nolhs_index_valid assert_bound_nolhs_atoms_imply_bounds_index
        assert_bound_nolhs_unsat assert_bound_nolhs_tableau_valuated)+) 


text\<open>The second phase of \<open>assert\<close>, the \<open>check\<close> function,
is the heart of the Simplex algorithm. It is always called after
\<open>assert_bound\<close>, but in two different situations. In the first
case \<open>assert_bound\<close> raised the \<open>\<U>\<close> flag and then
\<open>check\<close> should retain the flag and should not perform any changes.
In the second case \<open>assert_bound\<close> did not raise the
\<open>\<U>\<close> flag, so \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s\<close>, \<open>\<diamond> s\<close>, \<open>\<triangle> (\<T>
s)\<close>, and \<open>\<nabla> s\<close> hold.\<close>

locale Check = fixes check::"('i,'a::lrv) state \<Rightarrow> ('i,'a) state"
  assumes
    \<comment> \<open>If @{text check} is called from an inconsistent state, the state is unchanged.\<close>

check_unsat_id: "\<U> s \<Longrightarrow> check s = s"  and

\<comment> \<open>The tableau remains equivalent to the previous one, normalized and valuated.\<close>

check_tableau:  "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow>
   let s' = check s in ((v::'a valuation) \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> s') \<and> \<triangle> (\<T> s') \<and> \<nabla> s'" and

\<comment> \<open>The bounds remain unchanged.\<close>

check_bounds_id:  "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<B>\<^sub>i (check s) = \<B>\<^sub>i s"  and

\<comment> \<open>If @{term \<U>} flag is not raised, the current valuation
   @{text "\<V>"} satisfies both the tableau and the bounds and if it is
   raised, there is no valuation that satisfies them.\<close>

check_sat: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<not> \<U> (check s) \<Longrightarrow> \<Turnstile> (check s)"  and


check_unsat: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<U> (check s) \<Longrightarrow> minimal_unsat_state_core (check s)"

begin

lemma check_tableau_equiv: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow>
                      (v::'a valuation) \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> (check s)"
  using check_tableau
  by (simp add: Let_def)

lemma check_tableau_index_valid: assumes "\<not> \<U> s" " \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s" "\<triangle> (\<T> s)" "\<nabla> s"
  shows "index_valid as (check s) = index_valid as s"
  unfolding index_valid_def using check_bounds_id[OF assms]
  by (auto simp: indexl_def indexu_def boundsl_def boundsu_def)


lemma check_tableau_normalized: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<triangle> (\<T> (check s))"
  using check_tableau
  by (simp add: Let_def)

lemma check_tableau_valuated: "\<lbrakk>\<not> \<U> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<triangle> (\<T> s); \<nabla> s\<rbrakk> \<Longrightarrow> \<nabla> (check s)"
  using check_tableau
  by (simp add: Let_def)

lemma check_indices_state: assumes "\<not> \<U> s \<Longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<not> \<U> s \<Longrightarrow> \<diamond> s" "\<not> \<U> s \<Longrightarrow> \<triangle> (\<T> s)" "\<not> \<U> s \<Longrightarrow> \<nabla> s"
  shows "indices_state (check s) = indices_state s" 
  using check_bounds_id[OF _ assms] check_unsat_id[of s]
  unfolding indices_state_def by (cases "\<U> s", auto)

lemma check_distinct_indices_state: assumes "\<not> \<U> s \<Longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<not> \<U> s \<Longrightarrow> \<diamond> s" "\<not> \<U> s \<Longrightarrow> \<triangle> (\<T> s)" "\<not> \<U> s \<Longrightarrow> \<nabla> s"
  shows "distinct_indices_state (check s) = distinct_indices_state s" 
  using check_bounds_id[OF _ assms] check_unsat_id[of s]
  unfolding distinct_indices_state_def by (cases "\<U> s", auto)
  
end


locale Assert' = AssertBound assert_bound + Check check for
  assert_bound :: "('i,'a::lrv) i_atom \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state" and
  check :: "('i,'a::lrv) state \<Rightarrow> ('i,'a) state"
begin
definition assert :: "('i,'a) i_atom \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state" where
  "assert a s \<equiv> check (assert_bound a s)"

lemma Assert'Precond:
  assumes "\<not> \<U> s" "\<Turnstile> s" "\<triangle> (\<T> s)" "\<nabla> s"
  shows
    "\<triangle> (\<T> (assert_bound a s))"
    "\<not> \<U> (assert_bound a s) \<Longrightarrow>  \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s (assert_bound a s) \<and> \<diamond> (assert_bound a s)"
    "\<nabla> (assert_bound a s)"
  using assms
  using assert_bound_tableau_id assert_bound_sat assert_bound_tableau_valuated
  by (auto simp add: satisfies_bounds_consistent Let_def)
end


sublocale Assert' < Assert assert
proof
  fix s::"('i,'a) state" and v::"'a valuation" and  a::"('i,'a) i_atom"
  assume *: "\<not> \<U> s" "\<Turnstile> s" "\<triangle> (\<T> s)" "\<nabla> s"
  have "\<triangle> (\<T> (assert a s))"
    using check_tableau_normalized[of "assert_bound a s"] check_unsat_id[of "assert_bound a s"] *
    using assert_bound_sat[of s a] Assert'Precond[of s a]
    by (force simp add: assert_def)
  moreover
  have "v \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t \<T> (assert a s)"
    using check_tableau_equiv[of "assert_bound a s" v] *
    using check_unsat_id[of "assert_bound a s"]
    by (force simp add: assert_def Assert'Precond assert_bound_sat assert_bound_tableau_id)
  moreover
  have "\<nabla> (assert a s)"
    using assert_bound_tableau_valuated[of s a] *
    using check_tableau_valuated[of "assert_bound a s"]
    using check_unsat_id[of "assert_bound a s"]
    by (cases "\<U> (assert_bound a s)") (auto simp add: Assert'Precond assert_def)
  ultimately
  show "let s' = assert a s in (v \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t \<T> s') \<and> \<triangle> (\<T> s') \<and> \<nabla> s'"
    by (simp add: Let_def)
next
  fix s::"('i,'a) state" and a::"('i,'a) i_atom"
  assume "\<not> \<U> s" "\<Turnstile> s" "\<triangle> (\<T> s)" "\<nabla> s"
  then show "\<not> \<U> (assert a s) \<Longrightarrow> \<Turnstile> (assert a s)"
    unfolding assert_def
    using check_unsat_id[of "assert_bound a s"]
    using check_sat[of "assert_bound a s"]
    by (force simp add: Assert'Precond)
next
  fix s::"('i,'a) state" and a::"('i,'a) i_atom" and ats::"('i,'a) i_atom set"
  assume "\<not> \<U> s" "\<Turnstile> s" "\<triangle> (\<T> s)" "\<nabla> s"
  then show "flat ats \<doteq> \<B> s \<Longrightarrow> flat (ats \<union> {a}) \<doteq> \<B> (assert a s)"
    using assert_bound_atoms_equiv_bounds
    using check_unsat_id[of "assert_bound a s"] check_bounds_id
    by (cases "\<U> (assert_bound a s)") (auto simp add: Assert'Precond assert_def
        simp: indexl_def indexu_def boundsl_def boundsu_def)
next
  fix s::"('i,'a) state" and a::"('i,'a) i_atom" and ats
  assume *: "\<not> \<U> s" "\<Turnstile> s" "\<triangle> (\<T> s)" "\<nabla> s" "\<U> (assert a s)" "index_valid ats s"
  show "minimal_unsat_state_core (assert a s)"
  proof (cases "\<U> (assert_bound a s)")
    case True
    then show ?thesis
      unfolding assert_def
      using * assert_bound_unsat check_tableau_equiv[of "assert_bound a s"] check_bounds_id
      using check_unsat_id[of "assert_bound a s"]
      by (auto simp add: Assert'Precond satisfies_state_def Let_def)
  next
    case False
    then show ?thesis
      unfolding assert_def
      using * assert_bound_sat[of s a] check_unsat Assert'Precond
      by (metis assert_def)
  qed
next
  fix ats
  fix s::"('i,'a) state" and a::"('i,'a) i_atom"
  assume *: "index_valid ats s"
    and **: "\<not> \<U> s" "\<Turnstile> s" "\<triangle> (\<T> s)" "\<nabla> s"
  have *: "index_valid (insert a ats) (assert_bound a s)"
    using assert_bound_index_valid[OF ** *] .
  show "index_valid (insert a ats) (assert a s)"
  proof (cases "\<U> (assert_bound a s)")
    case True
    show ?thesis unfolding assert_def check_unsat_id[OF True] using * .
  next
    case False
    show ?thesis unfolding assert_def using Assert'Precond[OF **, of a] False *
      by (subst check_tableau_index_valid[OF False], auto)
  qed
next
  fix s ats a
  let ?s = "assert_bound a s"
  assume *: "\<not> \<U> s" "\<Turnstile> s" "\<triangle> (\<T> s)" "\<nabla> s" "ats \<Turnstile>\<^sub>i \<B>\<I> s"
  from assert_bound_atoms_imply_bounds_index[OF this, of a]
  have as: "insert a ats \<Turnstile>\<^sub>i \<B>\<I> (assert_bound a s)" by auto
  show "insert a ats \<Turnstile>\<^sub>i \<B>\<I> (assert a s)"
  proof (cases "\<U> ?s")
    case True
    from check_unsat_id[OF True] as show ?thesis unfolding assert_def by auto
  next
    case False
    from assert_bound_tableau_id[OF *(1-4)] *
    have t: "\<triangle> (\<T> ?s)" by simp
    from assert_bound_tableau_valuated[OF *(1-4)]
    have v: "\<nabla> ?s" .
    from assert_bound_sat[OF *(1-4) refl False]
    have "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?s" "\<diamond> ?s" by auto
    from check_bounds_id[OF False this t v]  as
    show ?thesis unfolding assert_def
      by (auto simp: indexl_def indexu_def boundsl_def boundsu_def)
  qed
qed

text\<open>Under these assumptions for \<open>assert_bound\<close> and \<open>check\<close>, it can be easily shown that the implementation of \<open>assert\<close> (previously given) satisfies its specification.\<close>

locale AssertAllState'' = Init init + AssertBoundNoLhs assert_bound + Check check for
  init :: "tableau \<Rightarrow> ('i,'a::lrv) state" and
  assert_bound :: "('i,'a::lrv) i_atom \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state" and
  check :: "('i,'a::lrv) state \<Rightarrow> ('i,'a) state"
begin
definition assert_bound_loop where
  "assert_bound_loop ats s \<equiv> foldl (\<lambda> s' a. if (\<U> s') then s' else assert_bound a s') s ats"
definition assert_all_state where [simp]:
  "assert_all_state t ats \<equiv> check (assert_bound_loop ats (init t))"

text\<open>However, for efficiency reasons, we want to allow
implementations that delay the \<open>check\<close> function call and call it
after several \<open>assert_bound\<close> calls. For example:

\smallskip
\begin{small}
@{thm assert_bound_loop_def[no_vars]}

@{thm assert_all_state_def[no_vars]}
\end{small}
\smallskip

Then, the loop consists only of \<open>assert_bound\<close> calls, so \<open>assert_bound\<close> postcondition must imply its precondition. This is not
the case, since variables on the lhs may be out of their
bounds. Therefore, we make a refinement and specify weaker
preconditions (replace \<open>\<Turnstile> s\<close>, by \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s\<close> and \<open>\<diamond> s\<close>) for \<open>assert_bound\<close>, and show that these
preconditions are still good enough to prove the correctnes of this
alternative \<open>assert_all_state\<close> definition.\<close>


lemma AssertAllState''_precond':
  assumes "\<triangle> (\<T> s)" "\<nabla> s" "\<not> \<U> s \<longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s \<and> \<diamond> s"
  shows "let s' = assert_bound_loop ats s in
         \<triangle> (\<T> s') \<and> \<nabla> s' \<and> (\<not> \<U> s' \<longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s' \<and> \<diamond> s')"
  using assms
  using assert_bound_nolhs_tableau_id assert_bound_nolhs_sat assert_bound_nolhs_tableau_valuated
  by (induct ats rule: rev_induct) (auto simp add: assert_bound_loop_def Let_def)

lemma AssertAllState''_precond:
  assumes "\<triangle> t"
  shows "let s' = assert_bound_loop ats (init t) in
         \<triangle> (\<T> s') \<and> \<nabla> s' \<and> (\<not> \<U> s' \<longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s' \<and> \<diamond> s')"
  using assms
  using AssertAllState''_precond'[of "init t" ats]
  by (simp add: Let_def init_tableau_id init_unsat_flag init_satisfies satisfies_consistent
      satisfies_satisfies_no_lhs init_tableau_valuated)

lemma AssertAllState''Induct:
  assumes
    "\<triangle> t"
    "P {} (init t)"
    "\<And> as bs t. as \<subseteq> bs \<Longrightarrow> P as t \<Longrightarrow> P bs t"
    "\<And> s a ats. \<lbrakk>\<not> \<U> s;  \<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<triangle> (\<T> s); \<nabla> s; \<diamond> s; P (set ats) s; index_valid (set ats) s\<rbrakk>
      \<Longrightarrow> P (insert a (set ats)) (assert_bound a s)"
  shows "P (set ats) (assert_bound_loop ats (init t))"
proof -
  have "P (set ats) (assert_bound_loop ats (init t)) \<and> index_valid (set ats) (assert_bound_loop ats (init t))"
  proof (induct ats rule: rev_induct)
    case Nil
    then show ?case
      unfolding assert_bound_loop_def
      using assms(2) init_index_valid
      by simp
  next
    case (snoc a as')
    let ?s = "assert_bound_loop as' (init t)"
    from snoc index_valid_mono[of _ "set (a # as')" "assert_bound_loop as' (init t)"]
    have index: "index_valid (set (a # as')) (assert_bound_loop as' (init t))"
      by auto
    from snoc assms(3)[of "set as'" "set (a # as')"]
    have P: "P (set (a # as')) (assert_bound_loop as' (init t))" by auto
    show ?case
    proof (cases "\<U> ?s")
      case True
      then show ?thesis
        using P index
        unfolding assert_bound_loop_def
        by simp
    next
      case False
      have id': "set (as' @ [a]) = insert a (set as')" by simp
      have id: "assert_bound_loop (as' @ [a]) (init t) =
        assert_bound a (assert_bound_loop as' (init t))"
        using False unfolding assert_bound_loop_def by auto
      from snoc have index: "index_valid (set as') ?s" by simp
      show ?thesis unfolding id unfolding id' using False snoc AssertAllState''_precond[OF assms(1)]
        by (intro conjI assert_bound_nolhs_index_valid index assms(4); (force simp: Let_def curr_val_satisfies_no_lhs_def)?)
    qed
  qed
  then show ?thesis ..
qed

lemma AssertAllState''_tableau_id:
  "\<triangle> t \<Longrightarrow> \<T> (assert_bound_loop ats (init t)) = \<T> (init t)"
  by (rule AssertAllState''Induct) (auto simp add: init_tableau_id assert_bound_nolhs_tableau_id)

lemma AssertAllState''_sat:
  "\<triangle> t \<Longrightarrow>
    \<not> \<U> (assert_bound_loop ats (init t)) \<longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s (assert_bound_loop ats (init t)) \<and> \<diamond> (assert_bound_loop ats (init t))"
  by (rule AssertAllState''Induct) (auto simp add: init_unsat_flag init_satisfies satisfies_consistent satisfies_satisfies_no_lhs assert_bound_nolhs_sat)

lemma AssertAllState''_unsat:
  "\<triangle> t \<Longrightarrow> \<U> (assert_bound_loop ats (init t)) \<longrightarrow> minimal_unsat_state_core (assert_bound_loop ats (init t))"
  by (rule AssertAllState''Induct)
    (auto simp add: init_tableau_id assert_bound_nolhs_unsat init_unsat_flag)

lemma AssertAllState''_sat_atoms_equiv_bounds:
  "\<triangle> t \<Longrightarrow> \<not> \<U> (assert_bound_loop ats (init t)) \<longrightarrow> flat (set ats) \<doteq> \<B> (assert_bound_loop ats (init t))"
  using AssertAllState''_precond
  using assert_bound_nolhs_atoms_equiv_bounds init_atoms_equiv_bounds
  by (induct ats rule: rev_induct) (auto simp add: Let_def assert_bound_loop_def)

lemma AssertAllState''_atoms_imply_bounds_index:
  assumes "\<triangle> t"
  shows "set ats \<Turnstile>\<^sub>i \<B>\<I> (assert_bound_loop ats (init t))"
proof (induct ats rule: rev_induct)
  case Nil
  then show ?case
    unfolding assert_bound_loop_def
    using init_atoms_imply_bounds_index assms
    by simp
next
  case (snoc a ats')
  let ?s = "assert_bound_loop ats' (init t)"
  show ?case
  proof (cases "\<U> ?s")
    case True
    then show ?thesis
      using snoc atoms_imply_bounds_index_mono[of "set ats'" "set (ats' @ [a])"]
      unfolding assert_bound_loop_def
      by auto
  next
    case False
    then have id: "assert_bound_loop (ats' @ [a]) (init t) = assert_bound a ?s"
      unfolding assert_bound_loop_def by auto
    from snoc have ats: "set ats' \<Turnstile>\<^sub>i \<B>\<I> ?s" by auto
    from AssertAllState''_precond[of t ats', OF assms, unfolded Let_def] False
    have *: "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?s" "\<triangle> (\<T> ?s)" "\<nabla> ?s" "\<diamond> ?s" by auto
    show ?thesis unfolding id using assert_bound_nolhs_atoms_imply_bounds_index[OF False * ats, of a] by auto
  qed
qed 

lemma AssertAllState''_index_valid:
  "\<triangle> t \<Longrightarrow> index_valid (set ats) (assert_bound_loop ats (init t))"
  by (rule AssertAllState''Induct, auto simp: init_index_valid index_valid_mono assert_bound_nolhs_index_valid)

end

sublocale AssertAllState'' < AssertAllState assert_all_state
proof
  fix v::"'a valuation" and t ats s'
  assume *: "\<triangle> t" and "assert_all_state t ats = s'"
  then have s': "s' = assert_all_state t ats" by simp
  let ?s' = "assert_bound_loop ats (init t)"
  show "v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t \<T> s'"
    unfolding assert_all_state_def s'
    using * check_tableau_equiv[of ?s' v] AssertAllState''_tableau_id[of t ats] init_tableau_id[of t]
    using AssertAllState''_sat[of t ats] check_unsat_id[of ?s']
    using AssertAllState''_precond[of t ats]
    by force

  show "\<not> \<U> s' \<Longrightarrow> \<Turnstile> s'"
    unfolding assert_all_state_def s'
    using * AssertAllState''_precond[of t ats]
    using check_sat check_unsat_id
    by (force simp add: Let_def)

  show "\<U> s' \<Longrightarrow> minimal_unsat_state_core s'"
    using * check_unsat check_unsat_id[of ?s'] check_bounds_id
    using AssertAllState''_unsat[of t ats] AssertAllState''_precond[of t ats] s'
    by (force simp add: Let_def satisfies_state_def)

  show "\<not> \<U> s' \<Longrightarrow> flat (set ats) \<doteq> \<B> s'"
    unfolding assert_all_state_def s'
    using * AssertAllState''_precond[of t ats]
    using check_bounds_id[of ?s'] check_unsat_id[of ?s']
    using AssertAllState''_sat_atoms_equiv_bounds[of t ats]
    by (force simp add: Let_def simp: indexl_def indexu_def boundsl_def boundsu_def)

  show "\<U> s' \<Longrightarrow> set ats \<Turnstile>\<^sub>i \<B>\<I> s'"
    unfolding assert_all_state_def s'
    using * AssertAllState''_precond[of t ats]
    unfolding Let_def
    using check_bounds_id[of ?s']
    using AssertAllState''_atoms_imply_bounds_index[of t ats]
    using check_unsat_id[of ?s']
    by (cases "\<U> ?s'") (auto simp add: Let_def simp: indexl_def indexu_def boundsl_def boundsu_def)

  show "index_valid (set ats) s'"
    unfolding assert_all_state_def s'
    using * AssertAllState''_precond[of t ats] AssertAllState''_index_valid[OF *, of ats]
    unfolding Let_def
    using check_tableau_index_valid[of ?s']
    using check_unsat_id[of ?s']
    by (cases "\<U> ?s'", auto)

  show "indices_state s' \<subseteq> fst ` set ats"
    by (intro index_valid_indices_state, fact)
qed


subsection\<open>Update and Pivot\<close>

text\<open>Both \<open>assert_bound\<close> and \<open>check\<close> need to update
the valuation so that the tableau remains satisfied. If the value for
a variable not on the lhs of the tableau is changed, this
can be done rather easily (once the value of that variable is changed,
one should recalculate and change the values for all lhs
variables of the tableau). The \<open>update\<close> function does this, and
it is specified by:\<close>

locale Update = fixes update::"var \<Rightarrow> 'a::lrv \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state"
  assumes
    \<comment> \<open>Tableau, bounds, and the unsatisfiability flag are preserved.\<close>

update_id:  "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow>
     let s' = update x c s in \<T> s' = \<T> s \<and> \<B>\<^sub>i s' = \<B>\<^sub>i s \<and> \<U> s' = \<U> s \<and> \<U>\<^sub>c s' = \<U>\<^sub>c s" and

\<comment> \<open>Tableau remains valuated.\<close>

update_tableau_valuated:  "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow> \<nabla> (update x v s)"  and

\<comment> \<open>The given variable @{text "x"} in the updated valuation is
   set to the given value @{text "v"} while all other variables
   (except those on the lhs of the tableau) are
   unchanged.\<close>

update_valuation_nonlhs:  "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow> x' \<notin> lvars (\<T> s) \<longrightarrow>
       look (\<V> (update x v s)) x' = (if x = x' then Some v else look (\<V> s) x')" and

\<comment> \<open>Updated valuation continues to satisfy the tableau.\<close>

update_satisfies_tableau:  "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow>  \<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s \<longrightarrow> \<langle>\<V> (update x c s)\<rangle> \<Turnstile>\<^sub>t \<T> s"

begin
lemma update_bounds_id:
  assumes "\<triangle> (\<T> s)" "\<nabla> s" "x \<notin> lvars (\<T> s)"
  shows "\<B>\<^sub>i (update x c s) = \<B>\<^sub>i s"
    "\<B>\<I> (update x c s) = \<B>\<I> s"
    "\<B>\<^sub>l (update x c s) = \<B>\<^sub>l s"
    "\<B>\<^sub>u (update x c s) = \<B>\<^sub>u s"
  using update_id assms
  by (auto simp add: Let_def simp: indexl_def indexu_def boundsl_def boundsu_def)

lemma update_indices_state_id:
  assumes "\<triangle> (\<T> s)" "\<nabla> s" "x \<notin> lvars (\<T> s)"
  shows "indices_state (update x c s) = indices_state s" 
  using update_bounds_id[OF assms] unfolding indices_state_def by auto

lemma update_tableau_id: "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow> \<T> (update x c s) = \<T> s"
  using update_id
  by (auto simp add: Let_def)

lemma update_unsat_id: "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow> \<U> (update x c s) = \<U> s"
  using update_id
  by (auto simp add: Let_def)

lemma update_unsat_core_id: "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x \<notin> lvars (\<T> s)\<rbrakk> \<Longrightarrow> \<U>\<^sub>c (update x c s) = \<U>\<^sub>c s"
  using update_id
  by (auto simp add: Let_def)

definition assert_bound' where
  [simp]: "assert_bound' dir i x c s \<equiv>
       (if (\<unrhd>\<^sub>u\<^sub>b (lt dir)) c (UB dir s x) then s
          else let s' = update\<B>\<I> (UBI_upd dir) i x c s in
             if (\<lhd>\<^sub>l\<^sub>b (lt dir)) c ((LB dir) s x) then
                  set_unsat [i, ((LI dir) s x)] s'
             else if x \<notin> lvars (\<T> s') \<and> (lt dir) c (\<langle>\<V> s\<rangle> x) then
                  update x c s'
             else
                  s')"

fun assert_bound :: "('i,'a::lrv) i_atom \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state" where
  "assert_bound (i,Leq x c) s = assert_bound' Positive i x c s"
| "assert_bound (i,Geq x c) s = assert_bound' Negative i x c s"

lemma assert_bound'_cases:
  assumes "\<lbrakk>\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)\<rbrakk> \<Longrightarrow> P s"
  assumes "\<lbrakk>\<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)); \<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)\<rbrakk> \<Longrightarrow>
     P (set_unsat [i, ((LI dir) s x)] (update\<B>\<I> (UBI_upd dir) i x c s))"
  assumes "\<lbrakk>x \<notin> lvars (\<T> s); (lt dir) c (\<langle>\<V> s\<rangle> x); \<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)); \<not> (\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x))\<rbrakk> \<Longrightarrow>
     P (update x c (update\<B>\<I> (UBI_upd dir) i x c s))"
  assumes "\<lbrakk>\<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)); \<not> (\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)); x \<in> lvars (\<T> s)\<rbrakk> \<Longrightarrow>
     P (update\<B>\<I> (UBI_upd dir) i x c s)"
  assumes "\<lbrakk>\<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)); \<not> (\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)); \<not> ((lt dir) c (\<langle>\<V> s\<rangle> x))\<rbrakk> \<Longrightarrow>
     P (update\<B>\<I> (UBI_upd dir) i x c s)"
  assumes "dir = Positive \<or> dir = Negative"
  shows "P (assert_bound' dir i x c s)"
proof (cases "\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)")
  case True
  then show ?thesis
    using assms(1)
    by simp
next
  case False
  show ?thesis
  proof (cases "\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)")
    case True
    then show ?thesis
      using \<open>\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)\<close>
      using assms(2)
      by simp
  next
    case False
    let ?s = "update\<B>\<I> (UBI_upd dir) i x c s"
    show ?thesis
    proof (cases "x \<notin> lvars (\<T> ?s) \<and> (lt dir) c (\<langle>\<V> s\<rangle> x)")
      case True
      then show ?thesis
        using \<open>\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)\<close> \<open>\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)\<close>
        using assms(3) assms(6)
        by auto
    next
      case False
      then have "x \<in> lvars (\<T> ?s) \<or> \<not> ((lt dir) c (\<langle>\<V> s\<rangle> x))"
        by simp
      then show ?thesis
      proof
        assume "x \<in> lvars (\<T> ?s)"
        then show ?thesis
          using \<open>\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)\<close> \<open>\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)\<close>
          using assms(4) assms(6)
          by auto
      next
        assume "\<not> (lt dir) c (\<langle>\<V> s\<rangle> x)"
        then show ?thesis
          using \<open>\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)\<close> \<open>\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)\<close>
          using assms(5) assms(6)
          by simp
      qed
    qed
  qed
qed

lemma assert_bound_cases:
  assumes "\<And> c x dir.
     \<lbrakk> dir = Positive \<or> dir = Negative;
       a = LE dir x c;
       \<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)
     \<rbrakk> \<Longrightarrow>
       P' (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir) s"
  assumes "\<And> c x dir.
     \<lbrakk>dir = Positive \<or> dir = Negative;
      a = LE dir x c;
      \<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x); \<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x)
     \<rbrakk> \<Longrightarrow>
        P' (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir)
          (set_unsat [i, ((LI dir) s x)] (update\<B>\<I> (UBI_upd dir) i x c s))"
  assumes "\<And> c x dir.
     \<lbrakk> dir = Positive \<or> dir = Negative;
       a = LE dir x c;
       x \<notin> lvars (\<T> s); (lt dir) c (\<langle>\<V> s\<rangle> x);
      \<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)); \<not> (\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x))
     \<rbrakk> \<Longrightarrow>
        P' (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir)
       (update x c ((update\<B>\<I> (UBI_upd dir) i x c s)))"
  assumes "\<And> c x dir.
     \<lbrakk> dir = Positive \<or> dir = Negative;
       a = LE dir x c;
       x \<in> lvars (\<T> s); \<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x));
       \<not> (\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x))
     \<rbrakk> \<Longrightarrow>
        P' (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir)
          ((update\<B>\<I> (UBI_upd dir) i x c s))"
  assumes "\<And> c x dir.
     \<lbrakk> dir = Positive \<or> dir = Negative;
       a = LE dir x c;
       \<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c ((UB dir) s x)); \<not> (\<lhd>\<^sub>l\<^sub>b (lt dir) c ((LB dir) s x));
       \<not> ((lt dir) c (\<langle>\<V> s\<rangle> x))
     \<rbrakk> \<Longrightarrow>
        P' (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir)
           ((update\<B>\<I> (UBI_upd dir) i x c s))"

assumes "\<And> s. P s = P' (>) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>l \<B>\<^sub>u \<B>\<^sub>i\<^sub>l_update \<I>\<^sub>l \<I>\<^sub>u Geq Leq s"
assumes "\<And> s. P s = P' (<) \<B>\<^sub>i\<^sub>u \<B>\<^sub>i\<^sub>l \<B>\<^sub>u \<B>\<^sub>l \<B>\<^sub>i\<^sub>u_update \<I>\<^sub>u \<I>\<^sub>l Leq Geq s"
shows "P (assert_bound (i,a) s)"
proof (cases a)
  case (Leq x c)
  then show ?thesis
    apply (simp del: assert_bound'_def)
    apply (rule assert_bound'_cases, simp_all)
    using assms(1)[of Positive x c]
    using assms(2)[of Positive x c]
    using assms(3)[of Positive x c]
    using assms(4)[of Positive x c]
    using assms(5)[of Positive x c]
    using assms(7)
    by auto
next
  case (Geq x c)
  then show ?thesis
    apply (simp del: assert_bound'_def)
    apply (rule assert_bound'_cases)
    using assms(1)[of Negative x c]
    using assms(2)[of Negative x c]
    using assms(3)[of Negative x c]
    using assms(4)[of Negative x c]
    using assms(5)[of Negative x c]
    using assms(6)
    by auto
qed
end

lemma set_unsat_bounds_id: "\<B> (set_unsat I s) = \<B> s"
  unfolding boundsl_def boundsu_def by auto


lemma decrease_ub_satisfied_inverse:
  assumes lt: "\<lhd>\<^sub>u\<^sub>b (lt dir) c  (UB dir s x)" and dir: "dir = Positive \<or> dir = Negative"
  assumes v: "v \<Turnstile>\<^sub>b \<B> (update\<B>\<I> (UBI_upd dir) i x c s)"
  shows "v \<Turnstile>\<^sub>b \<B> s"
  unfolding satisfies_bounds.simps
proof
  fix x'
  show "in_bounds x' v (\<B> s)"
  proof (cases "x = x'")
    case False
    then show ?thesis
      using v dir
      unfolding satisfies_bounds.simps
      by (auto split: if_splits simp: boundsl_def boundsu_def)
  next
    case True
    then show ?thesis
      using v dir
      unfolding satisfies_bounds.simps
      using lt
      by (erule_tac x="x'" in allE)
        (auto simp add: lt_ubound_def[THEN sym] gt_lbound_def[THEN sym] compare_strict_nonstrict
          boundsl_def boundsu_def)
  qed
qed

lemma atoms_equiv_bounds_extend:
  fixes x c dir
  assumes "dir = Positive \<or> dir = Negative"  "\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x)"  "ats \<doteq> \<B> s"
  shows "(ats \<union> {LE dir x c}) \<doteq> \<B> (update\<B>\<I> (UBI_upd dir) i x c s)"
  unfolding atoms_equiv_bounds.simps
proof
  fix v
  let ?s = "update\<B>\<I> (UBI_upd dir) i x c s"
  show "v \<Turnstile>\<^sub>a\<^sub>s (ats \<union> {LE dir x c}) = v \<Turnstile>\<^sub>b \<B> ?s"
  proof
    assume "v \<Turnstile>\<^sub>a\<^sub>s (ats \<union> {LE dir x c})"
    then have "v \<Turnstile>\<^sub>a\<^sub>s ats" "le (lt dir) (v x) c"
      using \<open>dir = Positive \<or> dir = Negative\<close>
      unfolding satisfies_atom_set_def
      by auto
    show "v \<Turnstile>\<^sub>b \<B> ?s"
      unfolding satisfies_bounds.simps
    proof
      fix x'
      show "in_bounds x' v (\<B> ?s)"
        using \<open>v \<Turnstile>\<^sub>a\<^sub>s ats\<close> \<open>le (lt dir) (v x) c\<close> \<open>ats \<doteq> \<B> s\<close>
        using \<open>dir = Positive \<or> dir = Negative\<close>
        unfolding atoms_equiv_bounds.simps satisfies_bounds.simps
        by (cases "x = x'") (auto simp: boundsl_def boundsu_def)
    qed
  next
    assume "v \<Turnstile>\<^sub>b \<B> ?s"
    then have "v \<Turnstile>\<^sub>b \<B> s"
      using \<open>\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x)\<close>
      using \<open>dir = Positive \<or> dir = Negative\<close>
      using decrease_ub_satisfied_inverse[of dir c s x v]
      using neg_bounds_compare(1)[of c "\<B>\<^sub>u s x"]
      using neg_bounds_compare(5)[of c "\<B>\<^sub>l s x"]
      by (auto simp add:  lt_ubound_def[THEN sym] ge_ubound_def[THEN sym] le_lbound_def[THEN sym] gt_lbound_def[THEN sym])
    show "v \<Turnstile>\<^sub>a\<^sub>s (ats \<union> {LE dir x c})"
      unfolding satisfies_atom_set_def
    proof
      fix a
      assume "a \<in> ats \<union> {LE dir x c}"
      then show "v \<Turnstile>\<^sub>a a"
      proof
        assume "a \<in> {LE dir x c}"
        then show ?thesis
          using \<open>v \<Turnstile>\<^sub>b \<B> ?s\<close>
          using \<open>dir = Positive \<or> dir = Negative\<close>
          unfolding satisfies_bounds.simps
          by (auto split: if_splits simp: boundsl_def boundsu_def)
      next
        assume "a \<in> ats"
        then show ?thesis
          using \<open>ats \<doteq> \<B> s\<close>
          using \<open>v \<Turnstile>\<^sub>b \<B> s\<close>
          unfolding atoms_equiv_bounds.simps satisfies_atom_set_def
          by auto
      qed
    qed
  qed
qed

lemma bounds_updates: "\<B>\<^sub>l (\<B>\<^sub>i\<^sub>u_update u s) = \<B>\<^sub>l s"
  "\<B>\<^sub>u (\<B>\<^sub>i\<^sub>l_update u s) = \<B>\<^sub>u s"
  "\<B>\<^sub>u (\<B>\<^sub>i\<^sub>u_update (upd x (i,c)) s) = (\<B>\<^sub>u s) (x \<mapsto> c)"
  "\<B>\<^sub>l (\<B>\<^sub>i\<^sub>l_update (upd x (i,c)) s) = (\<B>\<^sub>l s) (x \<mapsto> c)"
  by (auto simp: boundsl_def boundsu_def)

locale EqForLVar =
  fixes eq_idx_for_lvar :: "tableau \<Rightarrow> var \<Rightarrow> nat"
  assumes eq_idx_for_lvar:
    "\<lbrakk>x \<in> lvars t\<rbrakk> \<Longrightarrow> eq_idx_for_lvar t x < length t \<and> lhs (t ! eq_idx_for_lvar t x) = x"
begin
definition eq_for_lvar :: "tableau \<Rightarrow> var \<Rightarrow> eq" where
  "eq_for_lvar t v \<equiv> t ! (eq_idx_for_lvar t v)"
lemma eq_for_lvar:
  "\<lbrakk>x \<in> lvars t\<rbrakk> \<Longrightarrow> eq_for_lvar t x \<in> set t \<and> lhs (eq_for_lvar t x) = x"
  unfolding eq_for_lvar_def
  using eq_idx_for_lvar
  by auto

abbreviation rvars_of_lvar where
  "rvars_of_lvar t x \<equiv> rvars_eq (eq_for_lvar t x)"

lemma rvars_of_lvar_rvars:
  assumes "x \<in> lvars t"
  shows "rvars_of_lvar t x \<subseteq> rvars t"
  using assms eq_for_lvar[of x t]
  unfolding rvars_def
  by auto

end

text \<open>Updating changes the value of \<open>x\<close> and then updates
values of all lhs variables so that the tableau remains
satisfied. This can be based on a function that recalculates rhs
polynomial values in the changed valuation:\<close>

locale RhsEqVal = fixes rhs_eq_val::"(var, 'a::lrv) mapping \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> eq \<Rightarrow> 'a"
  \<comment> \<open>@{text rhs_eq_val} computes the value of the rhs of @{text e} in @{text "\<langle>v\<rangle>(x := c)"}.\<close>
  assumes rhs_eq_val:  "\<langle>v\<rangle> \<Turnstile>\<^sub>e e \<Longrightarrow> rhs_eq_val v x c e = rhs e \<lbrace> \<langle>v\<rangle> (x := c) \<rbrace>"

begin

text\<open>\noindent Then, the next implementation of \<open>update\<close>
satisfies its specification:\<close>

abbreviation update_eq where
  "update_eq v x c v' e \<equiv> upd (lhs e) (rhs_eq_val v x c e) v'"

definition update :: "var \<Rightarrow> 'a \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state" where
  "update x c s \<equiv> \<V>_update (upd x c (foldl (update_eq (\<V> s) x c) (\<V> s) (\<T> s))) s"

lemma update_no_set_none:
  shows "look (\<V> s) y \<noteq> None \<Longrightarrow>
         look (foldl (update_eq (\<V> s) x v) (\<V> s) t) y \<noteq> None"
  by (induct t rule: rev_induct, auto simp: lookup_update')

lemma update_no_left:
  assumes  "y \<notin> lvars t"
  shows "look (\<V> s) y = look (foldl (update_eq (\<V> s) x v) (\<V> s) t) y"
  using assms
  by (induct t rule: rev_induct) (auto simp add: lvars_def lookup_update')

lemma update_left:
  assumes "y \<in> lvars t"
  shows "\<exists> eq \<in> set t. lhs eq = y \<and>
     look (foldl (update_eq (\<V> s) x v) (\<V> s) t) y = Some (rhs_eq_val (\<V> s) x v eq)"
  using assms
  by (induct t rule: rev_induct) (auto simp add: lvars_def lookup_update')

lemma update_valuate_rhs:
  assumes "e \<in> set (\<T> s)" "\<triangle> (\<T> s)"
  shows "rhs e \<lbrace> \<langle>\<V> (update x c s)\<rangle> \<rbrace> = rhs e \<lbrace> \<langle>\<V> s\<rangle> (x := c) \<rbrace>"
proof (rule valuate_depend, safe)
  fix y
  assume "y \<in> rvars_eq e"
  then have "y \<notin> lvars (\<T> s)"
    using \<open>\<triangle> (\<T> s)\<close> \<open>e \<in> set (\<T> s)\<close>
    by (auto simp add: normalized_tableau_def rvars_def)
  then show "\<langle>\<V> (update x c s)\<rangle> y = (\<langle>\<V> s\<rangle>(x := c)) y"
    using update_no_left[of y "\<T> s" s x c]
    by (auto simp add: update_def map2fun_def lookup_update')
qed

end


sublocale RhsEqVal < Update update
proof
  fix s::"('i,'a) state" and x c
  show "let s' = update x c s in \<T> s' = \<T> s \<and> \<B>\<^sub>i s' = \<B>\<^sub>i s \<and> \<U> s' = \<U> s \<and> \<U>\<^sub>c s' = \<U>\<^sub>c s"
    by (simp add: Let_def update_def add: boundsl_def boundsu_def indexl_def indexu_def)
next
  fix s::"('i,'a) state" and x c
  assume "\<triangle> (\<T> s)" "\<nabla> s" "x \<notin> lvars (\<T> s)"
  then show "\<nabla> (update x c s)"
    using update_no_set_none[of s]
    by (simp add: Let_def update_def tableau_valuated_def lookup_update')
next
  fix s::"('i,'a) state" and  x x' c
  assume "\<triangle> (\<T> s)" "\<nabla> s" "x \<notin> lvars (\<T> s)"
  show "x' \<notin> lvars (\<T> s) \<longrightarrow>
          look (\<V> (update x c s)) x' =
          (if x = x' then Some c else look (\<V> s) x')"
    using update_no_left[of x' "\<T> s" s x c]
    unfolding update_def lvars_def Let_def
    by (auto simp: lookup_update')
next
  fix s::"('i,'a) state" and x c
  assume "\<triangle> (\<T> s)" "\<nabla> s" "x \<notin> lvars (\<T> s)"
  have "\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s \<Longrightarrow> \<forall>e \<in> set (\<T> s). \<langle>\<V> (update x c s)\<rangle> \<Turnstile>\<^sub>e e"
  proof
    fix e
    assume "e \<in> set (\<T> s)" "\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s"
    then have "\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>e e"
      by (simp add: satisfies_tableau_def)

    have "x \<noteq> lhs e"
      using \<open>x \<notin> lvars (\<T> s)\<close> \<open>e \<in> set (\<T> s)\<close>
      by (auto simp add: lvars_def)
    then have "\<langle>\<V> (update x c s)\<rangle> (lhs e) = rhs_eq_val (\<V> s) x c e"
      using update_left[of "lhs e" "\<T> s" s x c] \<open>e \<in> set (\<T> s)\<close> \<open>\<triangle> (\<T> s)\<close>
      by (auto simp add: lvars_def lookup_update' update_def Let_def map2fun_def normalized_tableau_def distinct_map inj_on_def)
    then show "\<langle>\<V> (update x c s)\<rangle> \<Turnstile>\<^sub>e e"
      using \<open>\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>e e\<close> \<open>e \<in> set (\<T> s)\<close> \<open>x \<notin> lvars (\<T> s)\<close> \<open>\<triangle> (\<T> s)\<close>
      using rhs_eq_val
      by (simp add: satisfies_eq_def update_valuate_rhs)
  qed
  then show "\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s \<longrightarrow> \<langle>\<V> (update x c s)\<rangle> \<Turnstile>\<^sub>t \<T> s"
    by(simp add: satisfies_tableau_def update_def)
qed


text\<open>To update the valuation for a variable that is on the lhs of
the tableau it should first be swapped with some rhs variable of its
equation, in an operation called \emph{pivoting}. Pivoting has the
precondition that the tableau is normalized and that it is always
called for a lhs variable of the tableau, and a rhs variable in the
equation with that lhs variable. The set of rhs variables for the
given lhs variable is found using the \<open>rvars_of_lvar\<close> function
(specified in a very simple locale \<open>EqForLVar\<close>, that we do not
print).\<close>

locale Pivot = EqForLVar + fixes pivot::"var \<Rightarrow> var \<Rightarrow> ('i,'a::lrv) state \<Rightarrow> ('i,'a) state"
  assumes
    \<comment> \<open>Valuation, bounds, and the unsatisfiability flag are not changed.\<close>

pivot_id:  "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
      let s' = pivot x\<^sub>i x\<^sub>j s in \<V> s' = \<V> s \<and> \<B>\<^sub>i s' = \<B>\<^sub>i s \<and> \<U> s' = \<U> s \<and> \<U>\<^sub>c s' = \<U>\<^sub>c s" and

\<comment> \<open>The tableau remains equivalent to the previous one and normalized.\<close>

pivot_tableau:  "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
      let s' = pivot x\<^sub>i x\<^sub>j s in  ((v::'a valuation) \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> s') \<and> \<triangle> (\<T> s') " and

\<comment> \<open>@{text "x\<^sub>i"} and @{text "x\<^sub>j"} are swapped, while the other variables do not change sides.\<close>

pivot_vars':   "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> let s' = pivot x\<^sub>i x\<^sub>j s in
   rvars(\<T> s') = rvars(\<T> s)-{x\<^sub>j}\<union>{x\<^sub>i}  \<and>  lvars(\<T> s') = lvars(\<T> s)-{x\<^sub>i}\<union>{x\<^sub>j}"

begin
lemma pivot_bounds_id: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
      \<B>\<^sub>i (pivot x\<^sub>i x\<^sub>j s) = \<B>\<^sub>i s"
  using pivot_id
  by (simp add: Let_def)

lemma pivot_bounds_id': assumes "\<triangle> (\<T> s)" "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i"
  shows "\<B>\<I> (pivot x\<^sub>i x\<^sub>j s) = \<B>\<I> s" "\<B> (pivot x\<^sub>i x\<^sub>j s) = \<B> s" "\<I> (pivot x\<^sub>i x\<^sub>j s) = \<I> s"
  using pivot_bounds_id[OF assms]
  by (auto simp: indexl_def indexu_def boundsl_def boundsu_def)

lemma pivot_valuation_id: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> \<V> (pivot x\<^sub>i x\<^sub>j s) = \<V> s"
  using pivot_id
  by (simp add: Let_def)

lemma pivot_unsat_id: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> \<U> (pivot x\<^sub>i x\<^sub>j s) = \<U> s"
  using pivot_id
  by (simp add: Let_def)

lemma pivot_unsat_core_id: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> \<U>\<^sub>c (pivot x\<^sub>i x\<^sub>j s) = \<U>\<^sub>c s"
  using pivot_id
  by (simp add: Let_def)

lemma pivot_tableau_equiv: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
      (v::'a valuation) \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t \<T> (pivot x\<^sub>i x\<^sub>j s)"
  using pivot_tableau
  by (simp add: Let_def)

lemma pivot_tableau_normalized: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> \<triangle> (\<T> (pivot x\<^sub>i x\<^sub>j s))"
  using pivot_tableau
  by (simp add: Let_def)

lemma pivot_rvars: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> rvars (\<T> (pivot x\<^sub>i x\<^sub>j s)) = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
  using pivot_vars'
  by (simp add: Let_def)

lemma pivot_lvars: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> lvars (\<T> (pivot x\<^sub>i x\<^sub>j s)) = lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
  using pivot_vars'
  by (simp add: Let_def)

lemma pivot_vars:
  "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> tvars (\<T> (pivot x\<^sub>i x\<^sub>j s)) = tvars (\<T> s) "
  using pivot_lvars[of s x\<^sub>i x\<^sub>j] pivot_rvars[of s x\<^sub>i x\<^sub>j]
  using rvars_of_lvar_rvars[of x\<^sub>i "\<T> s"]
  by auto

lemma
  pivot_tableau_valuated: "\<lbrakk>\<triangle> (\<T> s); x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i; \<nabla> s\<rbrakk> \<Longrightarrow> \<nabla> (pivot x\<^sub>i x\<^sub>j s)"
  using pivot_valuation_id pivot_vars
  by (auto simp add: tableau_valuated_def)

end


text\<open>Functions \<open>pivot\<close> and \<open>update\<close> can be used to
implement the \<open>check\<close> function. In its context, \<open>pivot\<close>
and \<open>update\<close> functions are always called together, so the
following definition can be used: @{prop "pivot_and_update x\<^sub>i x\<^sub>j c s =
update x\<^sub>i c (pivot x\<^sub>i x\<^sub>j s)"}. It is possible to make a more efficient
implementation of \<open>pivot_and_update\<close> that does not use separate
implementations of \<open>pivot\<close> and \<open>update\<close>. To allow this, a
separate specification for \<open>pivot_and_update\<close> can be given. It can be
easily shown that the \<open>pivot_and_update\<close> definition above
satisfies this specification.\<close>


locale PivotAndUpdate = EqForLVar +
  fixes pivot_and_update :: "var \<Rightarrow> var \<Rightarrow> 'a::lrv \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state"
  assumes  pivotandupdate_unsat_id:   "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
      \<U> (pivot_and_update x\<^sub>i x\<^sub>j c s) = \<U> s"
  assumes pivotandupdate_unsat_core_id: "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
      \<U>\<^sub>c (pivot_and_update x\<^sub>i x\<^sub>j c s) = \<U>\<^sub>c s"
  assumes  pivotandupdate_bounds_id:  "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
      \<B>\<^sub>i (pivot_and_update x\<^sub>i x\<^sub>j c s) = \<B>\<^sub>i s"
  assumes  pivotandupdate_tableau_normalized:  "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
      \<triangle> (\<T> (pivot_and_update x\<^sub>i x\<^sub>j c s))"
  assumes  pivotandupdate_tableau_equiv:  "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
      (v::'a valuation) \<Turnstile>\<^sub>t \<T> s \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> (pivot_and_update x\<^sub>i x\<^sub>j c s)"
  assumes pivotandupdate_satisfies_tableau:  "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
      \<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s \<longrightarrow> \<langle>\<V> (pivot_and_update x\<^sub>i x\<^sub>j c s)\<rangle> \<Turnstile>\<^sub>t \<T> s"
  assumes  pivotandupdate_rvars:   "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
      rvars (\<T> (pivot_and_update x\<^sub>i x\<^sub>j c s)) = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
  assumes  pivotandupdate_lvars:  "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
      lvars (\<T> (pivot_and_update x\<^sub>i x\<^sub>j c s)) = lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
  assumes pivotandupdate_valuation_nonlhs:  "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
      x \<notin> lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j} \<longrightarrow> look (\<V> (pivot_and_update x\<^sub>i x\<^sub>j c s)) x = (if x = x\<^sub>i then Some c else look (\<V> s) x)"
  assumes pivotandupdate_tableau_valuated:  "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow>
 \<nabla> (pivot_and_update x\<^sub>i x\<^sub>j c s)"
begin

lemma pivotandupdate_bounds_id':  assumes "\<triangle> (\<T> s)" "\<nabla> s" "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i"
  shows "\<B>\<I> (pivot_and_update x\<^sub>i x\<^sub>j c s) = \<B>\<I> s"
    "\<B> (pivot_and_update x\<^sub>i x\<^sub>j c s) = \<B> s"
    "\<I> (pivot_and_update x\<^sub>i x\<^sub>j c s) = \<I> s"
  using pivotandupdate_bounds_id[OF assms]
  by (auto simp: indexl_def indexu_def boundsl_def boundsu_def)

lemma  pivotandupdate_valuation_xi: "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i\<rbrakk> \<Longrightarrow> look (\<V> (pivot_and_update x\<^sub>i x\<^sub>j c s)) x\<^sub>i = Some c"
  using pivotandupdate_valuation_nonlhs[of s x\<^sub>i x\<^sub>j x\<^sub>i c]
  using rvars_of_lvar_rvars
  by (auto simp add:  normalized_tableau_def)

lemma  pivotandupdate_valuation_other_nolhs: "\<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i; x \<notin> lvars (\<T> s); x \<noteq> x\<^sub>j\<rbrakk> \<Longrightarrow> look (\<V> (pivot_and_update x\<^sub>i x\<^sub>j c s)) x = look (\<V> s) x"
  using pivotandupdate_valuation_nonlhs[of s x\<^sub>i x\<^sub>j x c]
  by auto

lemma pivotandupdate_nolhs:
  "\<lbrakk> \<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i;
     \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<B>\<^sub>l s x\<^sub>i = Some c \<or> \<B>\<^sub>u s x\<^sub>i = Some c\<rbrakk> \<Longrightarrow>
     \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s (pivot_and_update x\<^sub>i x\<^sub>j c s)"
  using pivotandupdate_satisfies_tableau[of s x\<^sub>i x\<^sub>j c]
  using pivotandupdate_tableau_equiv[of s x\<^sub>i x\<^sub>j _ c]
  using pivotandupdate_valuation_xi[of s x\<^sub>i x\<^sub>j c]
  using pivotandupdate_valuation_other_nolhs[of s x\<^sub>i x\<^sub>j _ c]
  using pivotandupdate_lvars[of s x\<^sub>i x\<^sub>j c]
  by (auto simp add: curr_val_satisfies_no_lhs_def satisfies_bounds.simps satisfies_bounds_set.simps
      bounds_consistent_geq_lb bounds_consistent_leq_ub map2fun_def pivotandupdate_bounds_id')

lemma pivotandupdate_bounds_consistent:
  assumes "\<triangle> (\<T> s)" "\<nabla> s" "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i"
  shows "\<diamond> (pivot_and_update x\<^sub>i x\<^sub>j c s) = \<diamond> s"
  using assms pivotandupdate_bounds_id'[of s x\<^sub>i x\<^sub>j c]
  by (simp add: bounds_consistent_def)
end


locale PivotUpdate = Pivot eq_idx_for_lvar pivot + Update update for
  eq_idx_for_lvar :: "tableau \<Rightarrow> var \<Rightarrow> nat" and
  pivot :: "var \<Rightarrow> var \<Rightarrow> ('i,'a::lrv) state \<Rightarrow> ('i,'a) state" and
  update :: "var \<Rightarrow> 'a \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state"
begin
definition  pivot_and_update :: "var \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state" where [simp]:
  "pivot_and_update x\<^sub>i x\<^sub>j c s \<equiv> update x\<^sub>i c (pivot x\<^sub>i x\<^sub>j s)"

lemma pivot_update_precond:
  assumes "\<triangle> (\<T> s)" "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i"
  shows "\<triangle> (\<T> (pivot x\<^sub>i x\<^sub>j s))" "x\<^sub>i \<notin> lvars (\<T> (pivot x\<^sub>i x\<^sub>j s))"
proof-
  from assms have "x\<^sub>i \<noteq> x\<^sub>j"
    using rvars_of_lvar_rvars[of x\<^sub>i "\<T> s"]
    by (auto simp add: normalized_tableau_def)
  then show "\<triangle> (\<T> (pivot x\<^sub>i x\<^sub>j s))" "x\<^sub>i \<notin> lvars (\<T> (pivot x\<^sub>i x\<^sub>j s))"
    using assms
    using pivot_tableau_normalized[of s x\<^sub>i x\<^sub>j]
    using pivot_lvars[of s x\<^sub>i x\<^sub>j]
    by auto
qed

end


sublocale PivotUpdate < PivotAndUpdate eq_idx_for_lvar pivot_and_update
  using pivot_update_precond
  using update_unsat_id pivot_unsat_id pivot_unsat_core_id update_bounds_id pivot_bounds_id
    update_tableau_id pivot_tableau_normalized pivot_tableau_equiv update_satisfies_tableau
    pivot_valuation_id pivot_lvars pivot_rvars  update_valuation_nonlhs update_valuation_nonlhs
    pivot_tableau_valuated update_tableau_valuated update_unsat_core_id
  by (unfold_locales, auto)

text\<open>Given the @{term update} function, \<open>assert_bound\<close> can be
implemented as follows.
\vspace{-2mm}
@{text[display]
  "assert_bound (Leq x c) s \<equiv>
          if c \<ge>\<^sub>u\<^sub>b \<B>\<^sub>u s x then s
          else let s' = s \<lparr> \<B>\<^sub>u := (\<B>\<^sub>u s) (x := Some c) \<rparr>
               in if c <\<^sub>l\<^sub>b \<B>\<^sub>l s x then s' \<lparr> \<U> := True \<rparr>
               else if x \<notin> lvars (\<T> s') \<and> c < \<langle>\<V> s\<rangle> x then update x c s' else s'"
}
\vspace{-2mm}
\noindent The case of \<open>Geq x c\<close> atoms is analogous (a systematic way to
avoid symmetries is discussed in Section \ref{sec:symmetries}). This
implementation satisfies both its specifications.
\<close>

lemma indices_state_set_unsat: "indices_state (set_unsat I s) = indices_state s" 
  by (cases s, auto simp: indices_state_def)

lemma \<B>\<I>_set_unsat: "\<B>\<I> (set_unsat I s) = \<B>\<I> s" 
  by (cases s, auto simp: boundsl_def boundsu_def indexl_def indexu_def)

lemma satisfies_tableau_cong: assumes "\<And> x. x \<in> tvars t \<Longrightarrow> v x = w x"
  shows "(v \<Turnstile>\<^sub>t t) = (w \<Turnstile>\<^sub>t t)" 
  unfolding satisfies_tableau_def satisfies_eq_def
  by (intro ball_cong[OF refl] arg_cong2[of _ _ _ _ "(=)"] valuate_depend, 
      insert assms, auto simp: lvars_def rvars_def)

lemma satisfying_state_valuation_to_atom_tabl: assumes J: "J \<subseteq> indices_state s" 
  and model: "(J, v) \<Turnstile>\<^sub>i\<^sub>s\<^sub>e s" 
  and ivalid: "index_valid as s" 
  and dist: "distinct_indices_atoms as" 
shows "(J, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>e\<^sub>s as" "v \<Turnstile>\<^sub>t \<T> s" 
  unfolding i_satisfies_atom_set'.simps
proof (intro ballI)
  from model[unfolded satisfies_state_index'.simps]
  have model: "v \<Turnstile>\<^sub>t \<T> s" "(J, v) \<Turnstile>\<^sub>i\<^sub>b\<^sub>e \<B>\<I> s" by auto
  show "v \<Turnstile>\<^sub>t \<T> s" by fact
  fix a 
  assume "a \<in> restrict_to J as" 
  then obtain i where iJ: "i \<in> J" and mem: "(i,a) \<in> as" by auto
  with J have "i \<in> indices_state s" by auto
  from this[unfolded indices_state_def] obtain x c where 
    look: "look (\<B>\<^sub>i\<^sub>l s) x = Some (i, c) \<or> look (\<B>\<^sub>i\<^sub>u s) x = Some (i, c)" by auto
  with ivalid[unfolded index_valid_def] 
  obtain b where "(i,b) \<in> as" "atom_var b = x" "atom_const b = c" by force
  with dist[unfolded distinct_indices_atoms_def, rule_format, OF this(1) mem]
  have a: "atom_var a = x" "atom_const a = c" by auto
  from model(2)[unfolded satisfies_bounds_index'.simps] look iJ have "v x = c" 
    by (auto simp: boundsu_def boundsl_def indexu_def indexl_def)
  thus "v \<Turnstile>\<^sub>a\<^sub>e a" unfolding satisfies_atom'_def a .
qed

text \<open>Note that in order to ensure minimality of the unsat cores, pivoting is required.\<close>

sublocale AssertAllState < AssertAll assert_all
proof
  fix t as v I
  assume D: "\<triangle> t"  
  from D show "assert_all t as = Sat v \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>t t \<and> \<langle>v\<rangle> \<Turnstile>\<^sub>a\<^sub>s flat (set as)"
    unfolding Let_def assert_all_def
    using assert_all_state_tableau_equiv[OF D refl]
    using assert_all_state_sat[OF D refl]
    using assert_all_state_sat_atoms_equiv_bounds[OF D refl, of as]
    unfolding atoms_equiv_bounds.simps curr_val_satisfies_state_def satisfies_state_def satisfies_atom_set_def
    by (auto simp: Let_def split: if_splits)
  let ?s = "assert_all_state t as" 
  assume "assert_all t as = Unsat I"
  then have i: "I = the (\<U>\<^sub>c ?s)" and U: "\<U> ?s"
    unfolding assert_all_def Let_def by (auto split: if_splits)
  from assert_all_index_valid[OF D refl, of as] have ivalid: "index_valid (set as) ?s"  .
  note unsat = assert_all_state_unsat[OF D refl U, unfolded minimal_unsat_state_core_def unsat_state_core_def i[symmetric]]
  from unsat have "set I \<subseteq> indices_state ?s" by auto
  also have "\<dots> \<subseteq> fst ` set as" using assert_all_state_indices[OF D refl] .
  finally have indices: "set I \<subseteq> fst ` set as" .
  show "minimal_unsat_core_tabl_atoms (set I) t (set as)" 
    unfolding minimal_unsat_core_tabl_atoms_def
  proof (intro conjI impI allI indices, clarify)
    fix v
    assume model: "v \<Turnstile>\<^sub>t t" "(set I, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as"
    from unsat have no_model: "\<not> ((set I, v) \<Turnstile>\<^sub>i\<^sub>s ?s)" by auto
    from assert_all_state_unsat_atoms_equiv_bounds[OF D refl U]
    have equiv: "set as \<Turnstile>\<^sub>i \<B>\<I> ?s" by auto
    from assert_all_state_tableau_equiv[OF D refl, of v] model
    have model_t: "v \<Turnstile>\<^sub>t \<T> ?s" by auto
    have model_as': "(set I, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as"
      using model(2) by (auto simp: satisfies_atom_set_def)
    with equiv model_t have "(set I, v) \<Turnstile>\<^sub>i\<^sub>s ?s"
      unfolding satisfies_state_index.simps atoms_imply_bounds_index.simps by simp
    with no_model show False by simp
  next
    fix J
    assume dist: "distinct_indices_atoms (set as)" and J: "J \<subset> set I" 
    from J unsat[unfolded subsets_sat_core_def, folded i] 
    have J': "J \<subseteq> indices_state ?s" by auto
    from index_valid_distinct_indices[OF ivalid dist] J unsat[unfolded subsets_sat_core_def, folded i]
    obtain v where model: "(J, v) \<Turnstile>\<^sub>i\<^sub>s\<^sub>e ?s" by blast
    have "(J, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>e\<^sub>s set as" "v \<Turnstile>\<^sub>t t" 
      using satisfying_state_valuation_to_atom_tabl[OF J' model ivalid dist]
       assert_all_state_tableau_equiv[OF D refl] by auto      
    then show "\<exists> v. v \<Turnstile>\<^sub>t t \<and> (J, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>e\<^sub>s set as" by blast
  qed
qed

lemma (in Update) update_to_assert_bound_no_lhs: assumes pivot: "Pivot eqlvar (pivot :: var \<Rightarrow> var \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state)" 
  shows "AssertBoundNoLhs assert_bound" 
proof
  fix s::"('i,'a) state" and a
  assume "\<not> \<U> s" "\<triangle> (\<T> s)" "\<nabla> s"
  then show "\<T> (assert_bound a s) = \<T> s"
    by (cases a, cases "snd a") (auto simp add: Let_def update_tableau_id tableau_valuated_def)
next
  fix s::"('i,'a) state" and ia and as
  assume *: "\<not> \<U> s" "\<triangle> (\<T> s)" "\<nabla> s" and **: "\<U> (assert_bound ia s)"
    and index: "index_valid as s"
    and consistent: "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s" 
  obtain i a where ia: "ia = (i,a)" by force
  let ?modelU = "\<lambda> lt UB UI s v x c i. UB s x = Some c \<longrightarrow> UI s x = i \<longrightarrow> i \<in> set (the (\<U>\<^sub>c s)) \<longrightarrow> (lt (v x) c \<or> v x = c)"
  let ?modelL = "\<lambda> lt LB LI s v x c i. LB s x = Some c \<longrightarrow> LI s x = i \<longrightarrow> i \<in> set (the (\<U>\<^sub>c s)) \<longrightarrow> (lt c (v x) \<or> c = v x)"
  let ?modelIU = "\<lambda> I lt UB UI s v x c i. UB s x = Some c \<longrightarrow> UI s x = i \<longrightarrow> i \<in> I \<longrightarrow> (v x = c)"
  let ?modelIL = "\<lambda> I lt LB LI s v x c i. LB s x = Some c \<longrightarrow> LI s x = i \<longrightarrow> i \<in> I \<longrightarrow> (v x = c)"
  let ?P' = "\<lambda> lt UBI LBI UB LB UBI_upd UI LI LE GE s.
    \<U> s \<longrightarrow> (set (the (\<U>\<^sub>c s)) \<subseteq> indices_state s \<and> \<not> (\<exists>v. (v \<Turnstile>\<^sub>t \<T> s
      \<and> (\<forall> x c i. ?modelU lt UB UI s v x c i)
      \<and> (\<forall> x c i. ?modelL lt LB LI s v x c i))))
      \<and> (distinct_indices_state s \<longrightarrow> (\<forall> I. I \<subset> set (the (\<U>\<^sub>c s)) \<longrightarrow> (\<exists> v. v \<Turnstile>\<^sub>t \<T> s \<and>
            (\<forall> x c i. ?modelIU I lt UB UI s v x c i) \<and> (\<forall> x c i. ?modelIL I lt LB LI s v x c i))))"
  have "\<U> (assert_bound ia s) \<longrightarrow> (unsat_state_core (assert_bound ia s) \<and> 
    (distinct_indices_state (assert_bound ia s) \<longrightarrow> subsets_sat_core (assert_bound ia s)))" (is "?P (assert_bound ia s)") unfolding ia
  proof (rule assert_bound_cases[of _ _ ?P'])
    fix s' :: "('i,'a) state"
    have id: "((x :: 'a) < y \<or> x = y) \<longleftrightarrow> x \<le> y" "((x :: 'a) > y \<or> x = y) \<longleftrightarrow> x \<ge> y" for x y by auto
    have id': "?P' (>) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>l \<B>\<^sub>u undefined \<I>\<^sub>l \<I>\<^sub>u Geq Leq s' = ?P' (<) \<B>\<^sub>i\<^sub>u \<B>\<^sub>i\<^sub>l \<B>\<^sub>u \<B>\<^sub>l undefined \<I>\<^sub>u \<I>\<^sub>l Leq Geq s'" 
      by (intro arg_cong[of _ _ "\<lambda> y. _ \<longrightarrow> y"] arg_cong[of _ _ "\<lambda> x. _ \<and> x"], 
        intro arg_cong2[of _ _ _ _ "(\<and>)"] arg_cong[of _ _ "\<lambda> y. _ \<longrightarrow> y"] arg_cong[of _ _ "\<lambda> y. \<forall> x \<subset> set (the (\<U>\<^sub>c s')). y x"] ext arg_cong[of _ _ Not],
        unfold id, auto)
    show "?P s' = ?P' (>) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>l \<B>\<^sub>u undefined \<I>\<^sub>l \<I>\<^sub>u Geq Leq s'"
      unfolding satisfies_state_def satisfies_bounds_index.simps satisfies_bounds.simps
        in_bounds.simps unsat_state_core_def satisfies_state_index.simps subsets_sat_core_def
        satisfies_state_index'.simps satisfies_bounds_index'.simps
      unfolding bound_compare''_defs id 
      by ((intro arg_cong[of _ _ "\<lambda> x. _ \<longrightarrow> x"] arg_cong[of _ _ "\<lambda> x. _ \<and> x"], 
        intro arg_cong2[of _ _ _ _ "(\<and>)"] refl arg_cong[of _ _ "\<lambda> x. _ \<longrightarrow> x"] arg_cong[of _ _ Not]
        arg_cong[of _ _ "\<lambda> y. \<forall> x \<subset> set (the (\<U>\<^sub>c s')). y x"] ext; intro arg_cong[of _ _ Ex] ext), auto)
    then show "?P s' = ?P' (<) \<B>\<^sub>i\<^sub>u \<B>\<^sub>i\<^sub>l \<B>\<^sub>u \<B>\<^sub>l undefined \<I>\<^sub>u \<I>\<^sub>l Leq Geq s'" unfolding id' .
  next
    fix c::'a and x::nat and dir
    assume "\<lhd>\<^sub>l\<^sub>b (lt dir) c (LB dir s x)" and dir: "dir = Positive \<or> dir = Negative"
    then obtain d where some: "LB dir s x = Some d" and lt: "lt dir c d"
      by (auto simp: bound_compare'_defs split: option.splits)
    from index[unfolded index_valid_def, rule_format, of x _ d]
      some dir obtain j where ind: "LI dir s x = j" "look (LBI dir s) x = Some (j,d)" and ge: "(j, GE dir x d) \<in> as"
      by (auto simp: indexl_def indexu_def boundsl_def boundsu_def)
    let ?s = "set_unsat [i, ((LI dir) s x)] (update\<B>\<I> (UBI_upd dir) i x c s)"
    let ?ss = "update\<B>\<I> (UBI_upd dir) i x c s" 
    show "?P' (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir) ?s"
    proof (intro conjI impI allI, goal_cases)
      case 1
      thus ?case using dir ind ge lt some by (force simp: indices_state_def split: if_splits)
    next
      case 2
      {
        fix v
        assume vU: "\<forall> x c i. ?modelU (lt dir) (UB dir) (UI dir) ?s v x c i"
        assume vL: "\<forall> x c i. ?modelL (lt dir) (LB dir) (LI dir) ?s v x c i" 
        from dir have "UB dir ?s x = Some c" "UI dir ?s x = i" by (auto simp: boundsl_def boundsu_def indexl_def indexu_def)
        from vU[rule_format, OF this] have vx_le_c: "lt dir (v x) c \<or> v x = c" by auto
        from dir ind some have *: "LB dir ?s x = Some d" "LI dir ?s x = j" by (auto simp: boundsl_def boundsu_def indexl_def indexu_def)
        have d_le_vx: "lt dir d (v x) \<or> d = v x" by (intro vL[rule_format, OF *], insert some ind, auto)
        from dir d_le_vx vx_le_c lt
        have False by auto
      }
      thus ?case by blast
    next
      case (3 I)
      then obtain j where I: "I \<subseteq> {j}" by (auto split: if_splits)
      from 3 have dist: "distinct_indices_state ?ss" unfolding distinct_indices_state_def by auto
      have id1: "UB dir ?s y = UB dir ?ss y" "LB dir ?s y = LB dir ?ss y"
               "UI dir ?s y = UI dir ?ss y" "LI dir ?s y = LI dir ?ss y" 
               "\<T> ?s = \<T> s" 
               "set (the (\<U>\<^sub>c ?s)) = {i,LI dir s x}" for y        
        using dir by (auto simp: boundsu_def boundsl_def indexu_def indexl_def) 
      from I have id: "(\<forall> k. P1 k \<longrightarrow> P2 k \<longrightarrow> k \<in> I \<longrightarrow> Q k) \<longleftrightarrow> (I = {} \<or> (P1 j \<longrightarrow> P2 j \<longrightarrow> Q j))" for P1 P2 Q by auto
      have id2: "(UB dir s xa = Some ca \<longrightarrow> UI dir s xa = j \<longrightarrow> P) = (look (UBI dir s) xa = Some (j,ca) \<longrightarrow> P)"
          "(LB dir s xa = Some ca \<longrightarrow> LI dir s xa = j \<longrightarrow> P) = (look (LBI dir s) xa = Some (j,ca) \<longrightarrow> P)" for xa ca P s
        using dir by (auto simp: boundsu_def indexu_def boundsl_def indexl_def)
      have "\<exists>v. v \<Turnstile>\<^sub>t \<T> s \<and>
             (\<forall>xa ca ia.
                 UB dir ?ss xa = Some ca \<longrightarrow> UI dir ?ss xa = ia \<longrightarrow> ia \<in> I \<longrightarrow> v xa = ca) \<and>
             (\<forall>xa ca ia.
                 LB dir ?ss xa = Some ca \<longrightarrow> LI dir ?ss xa = ia \<longrightarrow> ia \<in> I \<longrightarrow> v xa = ca)" 
      proof (cases "\<exists> xa ca. look (UBI dir ?ss) xa = Some (j,ca) \<or> look (LBI dir ?ss) xa = Some (j,ca)")
        case False
        thus ?thesis unfolding id id2 using consistent unfolding curr_val_satisfies_no_lhs_def 
          by (intro exI[of _ "\<langle>\<V> s\<rangle>"], auto)
      next
        case True
        from consistent have val: " \<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s" unfolding curr_val_satisfies_no_lhs_def by auto
        define ss where ss: "ss = ?ss" 
        from True obtain y b where "look (UBI dir ?ss) y = Some (j,b) \<or> look (LBI dir ?ss) y = Some (j,b)" by force
        then have id3: "(look (LBI dir ss) yy = Some (j,bb) \<or> look (UBI dir ss) yy = Some (j,bb)) \<longleftrightarrow> (yy = y \<and> bb = b)" for yy bb 
          using distinct_indices_stateD(1)[OF dist, of y j b yy bb] using dir
          unfolding ss[symmetric] 
          by (auto simp: boundsu_def boundsl_def indexu_def indexl_def)
        have "\<exists>v. v \<Turnstile>\<^sub>t \<T> s \<and> v y = b" 
        proof (cases "y \<in> lvars (\<T> s)")
          case False
          let ?v = "\<langle>\<V> (update y b s)\<rangle>" 
          show ?thesis
          proof (intro exI[of _ ?v] conjI)
            from update_satisfies_tableau[OF *(2,3) False] val 
            show "?v \<Turnstile>\<^sub>t \<T> s" by simp
            from update_valuation_nonlhs[OF *(2,3) False, of y b] False
            show "?v y = b" by (simp add: map2fun_def')
          qed
        next
          case True            
          from *(2)[unfolded normalized_tableau_def]
          have zero: "0 \<notin> rhs ` set (\<T> s)" by auto
          interpret Pivot eqlvar pivot by fact
          interpret PivotUpdate eqlvar pivot update ..
          let ?eq = "eq_for_lvar (\<T> s) y" 
          from eq_for_lvar[OF True] have "?eq \<in> set (\<T> s)" "lhs ?eq = y" by auto
          with zero have rhs: "rhs ?eq \<noteq> 0" by force
          hence "rvars_eq ?eq \<noteq> {}"
            by (simp add: vars_empty_zero)
          then obtain z where z: "z \<in> rvars_eq ?eq" by auto
          let ?v = "\<V> (pivot_and_update y z b s)" 
          let ?vv = "\<langle>?v\<rangle>" 
          from pivotandupdate_valuation_xi[OF *(2,3) True z]
          have "look ?v y = Some b" .
          hence vv: "?vv y = b" unfolding map2fun_def' by auto
          show ?thesis
          proof (intro exI[of _ ?vv] conjI vv)
            show "?vv \<Turnstile>\<^sub>t \<T> s" using pivotandupdate_satisfies_tableau[OF *(2,3) True z] val by auto
          qed
        qed
        thus ?thesis unfolding id id2 ss[symmetric] using id3 by metis
      qed
      thus ?case unfolding id1 .
    qed
  next
    fix c::'a and x::nat and dir
    assume **: "dir = Positive \<or> dir = Negative" "a = LE dir x c" "x \<notin> lvars (\<T> s)" "lt dir c (\<langle>\<V> s\<rangle> x)" 
      "\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x)" "\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c (LB dir s x)"
    let ?s = "update\<B>\<I> (UBI_upd dir) i x c s"
    show "?P' (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir)
      (update x c ?s)"
      using * **
      by (auto simp add: update_unsat_id tableau_valuated_def)
  qed (auto simp add: * update_unsat_id tableau_valuated_def)
  with ** show "minimal_unsat_state_core (assert_bound ia s)" by (auto simp: minimal_unsat_state_core_def)
next
  fix s::"('i,'a) state" and ia
  assume *: "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s" "\<triangle> (\<T> s)" "\<nabla> s"
    and **: "\<not> \<U> (assert_bound ia s)" (is ?lhs)
  obtain i a where ia: "ia = (i,a)" by force
  have "\<langle>\<V> (assert_bound ia s)\<rangle> \<Turnstile>\<^sub>t \<T> (assert_bound ia s)"
  proof-
    let ?P = "\<lambda> lt UBI LBI UB LB UBI_upd UI LI LE GE s. \<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s"
    show ?thesis unfolding ia
    proof (rule assert_bound_cases[of _ _ ?P])
      fix c x and dir :: "('i,'a) Direction"
      let ?s' = "update\<B>\<I> (UBI_upd dir) i x c s"
      assume "x \<notin> lvars (\<T> s)" "(lt dir) c (\<langle>\<V> s\<rangle> x)"
        "dir = Positive \<or> dir = Negative"
      then show "\<langle>\<V> (update x c ?s')\<rangle> \<Turnstile>\<^sub>t \<T> (update x c ?s')"
        using *
        using update_satisfies_tableau[of ?s' x c] update_tableau_id
        by (auto simp add: curr_val_satisfies_no_lhs_def tableau_valuated_def)
    qed (insert *, auto simp add: curr_val_satisfies_no_lhs_def)
  qed
  moreover
  have "\<not> \<U> (assert_bound ia s) \<longrightarrow> \<langle>\<V> (assert_bound ia s)\<rangle> \<Turnstile>\<^sub>b \<B> (assert_bound ia s) \<parallel> - lvars (\<T> (assert_bound ia s))" (is "?P (assert_bound ia s)")
  proof-
    let ?P' = "\<lambda> lt UBI LBI UB LB UB_upd UI LI LE GE s.
      \<not> \<U> s \<longrightarrow> (\<forall>x\<in>- lvars (\<T> s). \<unrhd>\<^sub>l\<^sub>b lt (\<langle>\<V> s\<rangle> x) (LB s x) \<and> \<unlhd>\<^sub>u\<^sub>b lt (\<langle>\<V> s\<rangle> x) (UB s x))"
    let ?P'' = "\<lambda> dir. ?P' (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir)"

    have x: "\<And> s'. ?P s' = ?P' (<) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>u \<B>\<^sub>l \<B>\<^sub>i\<^sub>u_update \<I>\<^sub>u \<I>\<^sub>l Leq Geq s'"
      and xx: "\<And> s'. ?P s' = ?P' (>) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>l \<B>\<^sub>u \<B>\<^sub>i\<^sub>l_update \<I>\<^sub>l \<I>\<^sub>u Geq Leq s'"
      unfolding satisfies_bounds_set.simps in_bounds.simps bound_compare_defs
      by (auto split: option.split)

    show ?thesis unfolding ia
    proof (rule assert_bound_cases[of _ _ ?P'])
      fix dir :: "('i,'a) Direction"
      assume "dir = Positive \<or> dir = Negative"
      then show "?P'' dir s"
        using  x[of s] xx[of s] \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s\<close>
        by (auto simp add: curr_val_satisfies_no_lhs_def)
    next
      fix x c and dir :: "('i,'a) Direction"
      let ?s' = "update\<B>\<I> (UBI_upd dir) i x c s"
      assume "x \<in> lvars (\<T> s)" "dir = Positive \<or> dir = Negative"
      then have "?P ?s'"
        using \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s\<close>
        by (auto simp add: satisfies_bounds_set.simps curr_val_satisfies_no_lhs_def
            boundsl_def boundsu_def indexl_def indexu_def)
      then show "?P'' dir ?s'"
        using x[of ?s'] xx[of ?s'] \<open>dir = Positive \<or> dir = Negative\<close>
        by auto
    next
      fix c x and dir :: "('i,'a) Direction"
      let ?s' = "update\<B>\<I> (UBI_upd dir) i x c s"
      assume "\<not> lt dir c (\<langle>\<V> s\<rangle> x)" "dir = Positive \<or> dir = Negative"
      then show "?P'' dir ?s'"
        using \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s\<close>
        by (auto simp add: satisfies_bounds_set.simps curr_val_satisfies_no_lhs_def
            simp: boundsl_def boundsu_def indexl_def indexu_def)
          (auto simp add: bound_compare_defs)
    next
      fix c x and dir :: "('i,'a) Direction"
      let ?s' = "update x c (update\<B>\<I> (UBI_upd dir) i x c s)"
      assume "x \<notin> lvars (\<T> s)" "\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c (LB dir s x)"
        "dir = Positive \<or> dir = Negative"
      show "?P'' dir ?s'"
      proof (rule impI, rule ballI)
        fix y
        assume "\<not> \<U> ?s'" "y \<in> - lvars (\<T> ?s')"
        show "\<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> ?s'\<rangle> y) (LB dir ?s' y) \<and> \<unlhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> ?s'\<rangle> y) (UB dir ?s' y)"
        proof (cases "x = y")
          case True
          then show ?thesis
            using \<open>x \<notin> lvars (\<T> s)\<close>
            using \<open>y \<in> - lvars (\<T> ?s')\<close>
            using \<open>\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c (LB dir s x)\<close>
            using \<open>dir = Positive \<or> dir = Negative\<close>
            using neg_bounds_compare(7) neg_bounds_compare(3)
            using *
            by (auto simp add: update_valuation_nonlhs update_tableau_id update_bounds_id bound_compare''_defs map2fun_def tableau_valuated_def bounds_updates) (force simp add: bound_compare'_defs)+
        next
          case False
          then show ?thesis
            using \<open>x \<notin> lvars (\<T> s)\<close> \<open>y \<in> - lvars (\<T> ?s')\<close>
            using \<open>dir = Positive \<or> dir = Negative\<close> *
            by (auto simp add: update_valuation_nonlhs update_tableau_id update_bounds_id  bound_compare''_defs satisfies_bounds_set.simps curr_val_satisfies_no_lhs_def map2fun_def
                tableau_valuated_def bounds_updates)
        qed
      qed
    qed (auto simp add: x xx)
  qed
  moreover
  have "\<not> \<U> (assert_bound ia s) \<longrightarrow> \<diamond> (assert_bound ia s)" (is "?P (assert_bound ia s)")
  proof-
    let ?P' = "\<lambda> lt UBI LBI UB LB UBI_upd UI LI LE GE s.
      \<not> \<U> s \<longrightarrow>
      (\<forall>x. if LB s x = None \<or> UB s x = None then True
           else lt (the (LB s x)) (the (UB s x)) \<or> (the (LB s x) = the (UB s x)))"
    let ?P'' = "\<lambda> dir. ?P' (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir)"

    have x: "\<And> s'. ?P s' = ?P' (<) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>u \<B>\<^sub>l \<B>\<^sub>i\<^sub>u_update \<I>\<^sub>u \<I>\<^sub>l Leq Geq s'" and
      xx: "\<And> s'. ?P s' = ?P' (>) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>l \<B>\<^sub>u \<B>\<^sub>i\<^sub>l_update \<I>\<^sub>l \<I>\<^sub>u Geq Leq s'"
      unfolding bounds_consistent_def
      by auto

    show ?thesis unfolding ia
    proof (rule assert_bound_cases[of _ _ ?P'])
      fix dir :: "('i,'a) Direction"
      assume "dir = Positive \<or> dir = Negative"
      then show "?P'' dir s"
        using \<open>\<diamond> s\<close>
        by (auto simp add: bounds_consistent_def) (erule_tac x=x in allE, auto)+
    next
      fix x c and dir :: "('i,'a) Direction"
      let ?s' = "update x c (update\<B>\<I> (UBI_upd dir) i x c s)"
      assume "dir = Positive \<or> dir = Negative" "x \<notin> lvars (\<T> s)"
        "\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x)" "\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c (LB dir s x)"
      then show "?P'' dir ?s'"
        using \<open>\<diamond> s\<close> *
        unfolding bounds_consistent_def
        by (auto simp add: update_bounds_id tableau_valuated_def bounds_updates split: if_splits)
          (force simp add: bound_compare'_defs, erule_tac x=xa in allE, simp)+
    next
      fix x c and dir :: "('i,'a) Direction"
      let ?s' = "update\<B>\<I> (UBI_upd dir) i x c s"
      assume "\<not> \<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x)" "\<not> \<lhd>\<^sub>l\<^sub>b (lt dir) c (LB dir s x)"
        "dir = Positive \<or> dir = Negative"
      then have "?P'' dir ?s'"
        using \<open>\<diamond> s\<close>
        unfolding bounds_consistent_def
        by (auto split: if_splits simp: bounds_updates)
          (force simp add: bound_compare'_defs, erule_tac x=xa in allE, simp)+
      then show "?P'' dir ?s'" "?P'' dir ?s'"
        by simp_all
    qed (auto simp add: x xx)
  qed

  ultimately

  show "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s (assert_bound ia s) \<and> \<diamond> (assert_bound ia s)"
    using \<open>?lhs\<close>
    unfolding curr_val_satisfies_no_lhs_def
    by simp
next
  fix s :: "('i,'a) state" and ats and ia :: "('i,'a) i_atom"
  assume "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<triangle> (\<T> s)" "\<nabla> s"
  obtain i a where ia: "ia = (i,a)" by force
  {
    fix ats
    let ?P' = "\<lambda> lt UBI LBI UB LB UB_upd UI LI LE GE s'. ats \<doteq> \<B> s \<longrightarrow> (ats \<union> {a}) \<doteq> \<B> s'"
    let ?P'' = "\<lambda> dir. ?P' (lt dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir)"
    have "ats \<doteq> \<B> s \<longrightarrow> (ats \<union> {a}) \<doteq> \<B> (assert_bound ia s)" (is "?P (assert_bound ia s)")
      unfolding ia
    proof (rule assert_bound_cases[of _ _ ?P'])
      fix x c and dir :: "('i,'a) Direction"
      assume "dir = Positive \<or> dir = Negative" "a = LE dir x c" "\<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x)"
      then show "?P s"
        unfolding atoms_equiv_bounds.simps satisfies_atom_set_def satisfies_bounds.simps
        by auto (erule_tac x=x in allE, force simp add: bound_compare_defs)+
    next
      fix x c and dir :: "('i,'a) Direction"
      let ?s' = "set_unsat [i, ((LI dir) s x)] (update\<B>\<I> (UBI_upd dir) i x c s)"

      assume "dir = Positive \<or> dir = Negative" "a = LE dir x c" "\<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x))"
      then show "?P ?s'" unfolding set_unsat_bounds_id
        using atoms_equiv_bounds_extend[of dir c s x ats i]
        by auto
    next
      fix x c and dir :: "('i,'a) Direction"
      let ?s' = "update\<B>\<I> (UBI_upd dir) i x c s"
      assume "dir = Positive \<or> dir = Negative" "a = LE dir x c" "\<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x))"
      then have "?P ?s'"
        using atoms_equiv_bounds_extend[of dir c s x ats i]
        by auto
      then show "?P ?s'" "?P ?s'"
        by simp_all
    next
      fix x c and dir :: "('i,'a) Direction"
      let ?s = "update\<B>\<I> (UBI_upd dir) i x c s"
      let ?s' = "update x c ?s"
      assume *: "dir = Positive \<or> dir = Negative" "a = LE dir x c" "\<not> (\<unrhd>\<^sub>u\<^sub>b (lt dir) c (UB dir s x))" "x \<notin> lvars (\<T> s)"
      then have "\<triangle> (\<T> ?s)" "\<nabla> ?s" "x \<notin> lvars (\<T> ?s)"
        using \<open>\<triangle> (\<T> s)\<close> \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s\<close> \<open>\<nabla> s\<close>
        by (auto simp: tableau_valuated_def)
      from update_bounds_id[OF this, of c]
      have "\<B>\<^sub>i ?s' = \<B>\<^sub>i ?s" by blast
      then have id: "\<B> ?s' = \<B> ?s" unfolding boundsl_def boundsu_def by auto
      show "?P ?s'" unfolding id \<open>a = LE dir x c\<close>
        by (intro impI atoms_equiv_bounds_extend[rule_format] *(1,3))
    qed simp_all
  }
  then show "flat ats \<doteq> \<B> s \<Longrightarrow> flat (ats \<union> {ia}) \<doteq> \<B> (assert_bound ia s)" unfolding ia by auto
next
  fix s :: "('i,'a) state" and ats and ia :: "('i,'a) i_atom"
  obtain i a where ia: "ia = (i,a)" by force
  assume "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<triangle> (\<T> s)" "\<nabla> s"
  have *: "\<And> dir x c s. dir = Positive \<or> dir = Negative \<Longrightarrow>
     \<nabla> (update\<B>\<I> (UBI_upd dir) i x c s) = \<nabla> s"
    "\<And> s y I . \<nabla> (set_unsat I s) = \<nabla> s"
    by (auto simp add: tableau_valuated_def)

  show "\<nabla> (assert_bound ia s)" (is "?P (assert_bound ia s)")
  proof-
    let ?P' = "\<lambda> lt UBI LBI UB LB UB_upd UI LI LE GE s'. \<nabla> s'"
    let ?P'' = "\<lambda> dir. ?P' (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir)"
    show ?thesis unfolding ia
    proof (rule assert_bound_cases[of _ _ ?P'])
      fix x c and dir :: "('i,'a) Direction"
      let ?s' = "update\<B>\<I> (UBI_upd dir) i x c s"
      assume "dir = Positive \<or> dir = Negative"
      then have "\<nabla> ?s'"
        using *(1)[of dir x c s] \<open>\<nabla> s\<close>
        by simp
      then show "\<nabla> (set_unsat [i, ((LI dir) s x)] ?s')"
        using *(2) by auto
    next
      fix x c and dir :: "('i,'a) Direction"
      assume *: "x \<notin> lvars (\<T> s)" "dir = Positive \<or> dir = Negative"
      let ?s = "update\<B>\<I> (UBI_upd dir) i x c s"
      let ?s' = "update x c ?s"
      from * show "\<nabla> ?s'"
        using \<open>\<triangle> (\<T> s)\<close> \<open>\<nabla> s\<close>
        using update_tableau_valuated[of ?s x c]
        by (auto simp add: tableau_valuated_def)
    qed (insert \<open>\<nabla> s\<close> *(1), auto)
  qed
next
  fix s :: "('i,'a) state" and as and ia :: "('i,'a) i_atom"
  obtain i a where ia: "ia = (i,a)" by force
  assume *: "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<triangle> (\<T> s)" "\<nabla> s"
    and valid: "index_valid as s"
  have id: "\<And> dir x c s. dir = Positive \<or> dir = Negative \<Longrightarrow>
     \<nabla> (update\<B>\<I> (UBI_upd dir) i x c s) = \<nabla> s"
    "\<And> s y I. \<nabla> (set_unsat I s) = \<nabla> s"
    by (auto simp add: tableau_valuated_def)
  let ?I = "insert (i,a) as"
  define I where "I = ?I"
  from index_valid_mono[OF _ valid] have valid: "index_valid I s" unfolding I_def by auto
  have I: "(i,a) \<in> I" unfolding I_def by auto
  let ?P = "\<lambda> s. index_valid I s"
  let ?P' = "\<lambda> (lt :: 'a \<Rightarrow> 'a \<Rightarrow> bool)
    (UBI :: ('i,'a) state \<Rightarrow> ('i,'a) bounds_index) (LBI :: ('i,'a) state \<Rightarrow> ('i,'a) bounds_index)
    (UB :: ('i,'a) state \<Rightarrow> 'a bounds) (LB :: ('i,'a) state \<Rightarrow> 'a bounds)
    (UBI_upd :: (('i,'a) bounds_index \<Rightarrow> ('i,'a) bounds_index) \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state)
    (UI :: ('i,'a) state \<Rightarrow> 'i bound_index) (LI :: ('i,'a) state \<Rightarrow> 'i bound_index)
    LE GE s'.
    (\<forall> x c i. look (UBI s') x = Some (i,c) \<longrightarrow> (i,LE (x :: var) c) \<in> I) \<and>
    (\<forall> x c i. look (LBI s') x = Some (i,c) \<longrightarrow> (i,GE (x :: nat) c) \<in> I)"
  define P where "P = ?P'"
  let ?P'' = "\<lambda> (dir :: ('i,'a) Direction).
    P (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir)"
  have x: "\<And> s'. ?P s' = P (<) \<B>\<^sub>i\<^sub>u \<B>\<^sub>i\<^sub>l \<B>\<^sub>u \<B>\<^sub>l \<B>\<^sub>i\<^sub>u_update \<I>\<^sub>u \<I>\<^sub>l Leq Geq s'"
    and xx: "\<And> s'. ?P s' = P (>) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>l \<B>\<^sub>u \<B>\<^sub>i\<^sub>l_update \<I>\<^sub>l \<I>\<^sub>u Geq Leq s'"
    unfolding satisfies_bounds_set.simps in_bounds.simps bound_compare_defs index_valid_def P_def
    by (auto split: option.split simp: indexl_def indexu_def boundsl_def boundsu_def)
  from valid have P'': "dir = Positive \<or> dir = Negative \<Longrightarrow> ?P'' dir s" for dir
    using x[of s] xx[of s] by auto
  have UTrue: "dir = Positive \<or> dir = Negative \<Longrightarrow> ?P'' dir s \<Longrightarrow> ?P'' dir (set_unsat I s)" for dir s I
    unfolding P_def by (auto simp: boundsl_def boundsu_def indexl_def indexu_def)
  have updateIB: "a = LE dir x c \<Longrightarrow> dir = Positive \<or> dir = Negative \<Longrightarrow> ?P'' dir s \<Longrightarrow> ?P'' dir
    (update\<B>\<I> (UBI_upd dir) i x c s)" for dir x c s
    unfolding P_def using I by (auto split: if_splits simp: simp: boundsl_def boundsu_def indexl_def indexu_def)
  show "index_valid (insert ia as) (assert_bound ia s)" unfolding ia I_def[symmetric]
  proof ((rule assert_bound_cases[of _ _ P]; (intro UTrue x xx updateIB P'')?))
    fix x c and dir :: "('i,'a) Direction"
    assume **: "dir = Positive \<or> dir = Negative"
      "a = LE dir x c"
      "x \<notin> lvars (\<T> s)"
    let ?s = "(update\<B>\<I> (UBI_upd dir) i x c s)"
    define s' where "s' = ?s"
    have 1: "\<triangle> (\<T> ?s)" using * ** by auto
    have 2: "\<nabla> ?s" using id(1) ** * \<open>\<nabla> s\<close> by auto
    have 3: "x \<notin> lvars (\<T> ?s)" using id(1) ** * \<open>\<nabla> s\<close> by auto
    have "?P'' dir ?s" using ** by (intro updateIB P'') auto
    with update_id[of ?s x c, OF 1 2 3, unfolded Let_def]  **(1)
    show "P (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir)
        (update x c (update\<B>\<I> (UBI_upd dir) i x c s))"
      unfolding P_def s'_def[symmetric] by auto
  qed auto
next
  fix s and ia :: "('i,'a) i_atom" and ats :: "('i,'a) i_atom set"
  assume *: "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s" and ats: "ats \<Turnstile>\<^sub>i \<B>\<I> s"
  obtain i a where ia: "ia = (i,a)" by force
  have id: "\<And> dir x c s. dir = Positive \<or> dir = Negative \<Longrightarrow>
     \<nabla> (update\<B>\<I> (UBI_upd dir) i x c s) = \<nabla> s"
    "\<And> s I. \<nabla> (set_unsat I s) = \<nabla> s"
    by (auto simp add: tableau_valuated_def)
  have idlt: "(c < (a :: 'a) \<or> c = a) = (c \<le> a)"
    "(a < c \<or> c = a) = (c \<ge> a)" for a c by auto
  define A where "A = insert (i,a) ats"
  let ?P = "\<lambda> (s :: ('i,'a) state). A \<Turnstile>\<^sub>i \<B>\<I> s"
  let ?Q = "\<lambda> bs (lt :: 'a \<Rightarrow> 'a \<Rightarrow> bool)
    (UBI :: ('i,'a) state \<Rightarrow> ('i,'a) bounds_index) (LBI :: ('i,'a) state \<Rightarrow> ('i,'a) bounds_index)
    (UB :: ('i,'a) state \<Rightarrow> 'a bounds) (LB :: ('i,'a) state \<Rightarrow> 'a bounds)
    (UBI_upd :: (('i,'a) bounds_index \<Rightarrow> ('i,'a) bounds_index) \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state)
    UI LI
    (LE :: nat \<Rightarrow> 'a \<Rightarrow> 'a atom) (GE :: nat \<Rightarrow> 'a \<Rightarrow> 'a atom) s'.
       (\<forall> I v. (I :: 'i set,v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s bs \<longrightarrow>
       ((\<forall> x c. LB s' x = Some c \<longrightarrow> LI s' x \<in> I \<longrightarrow> lt c (v x) \<or> c = v x)
      \<and> (\<forall> x c. UB s' x = Some c \<longrightarrow> UI s' x \<in> I \<longrightarrow> lt (v x) c \<or> v x = c)))"
  define Q where "Q = ?Q"
  let ?P' = "Q A"
  have equiv:
    "bs \<Turnstile>\<^sub>i \<B>\<I> s' \<longleftrightarrow> Q bs (<) \<B>\<^sub>i\<^sub>u \<B>\<^sub>i\<^sub>l \<B>\<^sub>u \<B>\<^sub>l \<B>\<^sub>i\<^sub>u_update \<I>\<^sub>u \<I>\<^sub>l Leq Geq s'"
    "bs \<Turnstile>\<^sub>i \<B>\<I> s' \<longleftrightarrow> Q bs (>) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>l \<B>\<^sub>u \<B>\<^sub>i\<^sub>l_update \<I>\<^sub>l \<I>\<^sub>u Geq Leq s'"
    for bs s'
    unfolding satisfies_bounds_set.simps in_bounds.simps bound_compare_defs index_valid_def Q_def
      atoms_imply_bounds_index.simps
    by (atomize(full), (intro conjI iff_exI allI arg_cong2[of _ _ _ _ "(\<and>)"] refl iff_allI
          arg_cong2[of _ _ _ _ "(=)"]; unfold satisfies_bounds_index.simps idlt), auto)
  have x: "\<And> s'. ?P s' = ?P' (<) \<B>\<^sub>i\<^sub>u \<B>\<^sub>i\<^sub>l \<B>\<^sub>u \<B>\<^sub>l \<B>\<^sub>i\<^sub>u_update \<I>\<^sub>u \<I>\<^sub>l Leq Geq s'"
    and xx: "\<And> s'. ?P s' = ?P' (>) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>l \<B>\<^sub>u \<B>\<^sub>i\<^sub>l_update \<I>\<^sub>l \<I>\<^sub>u Geq Leq s'"
    using equiv by blast+
  from ats equiv[of ats s]
  have Q_ats:
    "Q ats (<) \<B>\<^sub>i\<^sub>u \<B>\<^sub>i\<^sub>l \<B>\<^sub>u \<B>\<^sub>l \<B>\<^sub>i\<^sub>u_update \<I>\<^sub>u \<I>\<^sub>l Leq Geq s"
    "Q ats (>) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>l \<B>\<^sub>u \<B>\<^sub>i\<^sub>l_update \<I>\<^sub>l \<I>\<^sub>u Geq Leq s"
    by auto
  let ?P'' = "\<lambda> (dir :: ('i,'a) Direction). ?P' (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir)"
  have P_upd: "dir = Positive \<or> dir = Negative \<Longrightarrow> ?P'' dir (set_unsat I s) = ?P'' dir s" for s I dir
    unfolding Q_def
    by (intro iff_exI arg_cong2[of _ _ _ _ "(\<and>)"] refl iff_allI arg_cong2[of _ _ _ _ "(=)"]
        arg_cong2[of _ _ _ _ "(\<longrightarrow>)"], auto simp: boundsl_def boundsu_def indexl_def indexu_def)
  have P_upd: "dir = Positive \<or> dir = Negative \<Longrightarrow> ?P'' dir s \<Longrightarrow> ?P'' dir (set_unsat I s)" for s I dir
    using P_upd[of dir] by blast
  have ats_sub: "ats \<subseteq> A" unfolding A_def by auto
  {
    fix x c and dir :: "('i,'a) Direction"
    assume dir: "dir = Positive \<or> dir = Negative"
      and a: "a = LE dir x c"
    from Q_ats dir
    have Q_ats: "Q ats (lt dir) (UBI dir) (LBI dir) (UB dir) (LB dir) (UBI_upd dir) (UI dir) (LI dir) (LE dir) (GE dir) s"
      by auto
    have "?P'' dir (update\<B>\<I> (UBI_upd dir) i x c s)"
      unfolding Q_def
    proof (intro allI impI conjI)
      fix I v y d
      assume IvA: "(I, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s A"
      from i_satisfies_atom_set_mono[OF ats_sub this]
      have "(I, v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s ats" by auto
      from Q_ats[unfolded Q_def, rule_format, OF this]
      have s_bnds:
        "LB dir s x = Some c \<Longrightarrow> LI dir s x \<in> I \<Longrightarrow> lt dir c (v x) \<or> c = v x"
        "UB dir s x = Some c \<Longrightarrow> UI dir s x \<in> I \<Longrightarrow> lt dir (v x) c \<or> v x = c" for x c by auto
      from IvA[unfolded A_def, unfolded i_satisfies_atom_set.simps satisfies_atom_set_def, simplified]
      have va: "i \<in> I \<Longrightarrow> v \<Turnstile>\<^sub>a a" by auto
      with a dir have vc: "i \<in> I \<Longrightarrow> lt dir (v x) c \<or> v x = c"
        by auto
      let ?s = "(update\<B>\<I> (UBI_upd dir) i x c s)"
      show "LB dir ?s y = Some d \<Longrightarrow> LI dir ?s y \<in> I \<Longrightarrow> lt dir d (v y) \<or> d = v y"
        "UB dir ?s y = Some d \<Longrightarrow> UI dir ?s y \<in> I \<Longrightarrow> lt dir (v y) d \<or> v y = d"
      proof (atomize(full), goal_cases)
        case 1
        consider (main) "y = x" "UI dir ?s x = i" |
          (easy1) "x \<noteq> y" | (easy2) "x = y" "UI dir ?s y \<noteq> i"
          by blast
        then show ?case
        proof cases
          case easy1
          then show ?thesis using s_bnds[of y d] dir by (fastforce simp: boundsl_def boundsu_def indexl_def indexu_def)
        next
          case easy2
          then show ?thesis using s_bnds[of y d] dir by (fastforce simp: boundsl_def boundsu_def indexl_def indexu_def)
        next
          case main
          note s_bnds = s_bnds[of x]
          show ?thesis unfolding main using s_bnds dir vc by (auto simp: boundsl_def boundsu_def indexl_def indexu_def) blast+
        qed
      qed
    qed
  } note main = this
  have Ps: "dir = Positive \<or> dir = Negative \<Longrightarrow> ?P'' dir s" for dir
    using Q_ats unfolding Q_def using i_satisfies_atom_set_mono[OF ats_sub] by fastforce
  have "?P (assert_bound (i,a) s)"
  proof ((rule assert_bound_cases[of _ _ ?P']; (intro x xx P_upd main Ps)?))
    fix c x and dir :: "('i,'a) Direction"
    assume **: "dir = Positive \<or> dir = Negative"
      "a = LE dir x c"
      "x \<notin> lvars (\<T> s)"
    let ?s = "update\<B>\<I> (UBI_upd dir) i x c s"
    define s' where "s' = ?s"
    from main[OF **(1-2)] have P: "?P'' dir s'" unfolding s'_def .
    have 1: "\<triangle> (\<T> ?s)" using * ** by auto
    have 2: "\<nabla> ?s" using id(1) ** * \<open>\<nabla> s\<close> by auto
    have 3: "x \<notin> lvars (\<T> ?s)" using id(1) ** * \<open>\<nabla> s\<close> by auto
    have "\<triangle> (\<T> s')" "\<nabla> s'" "x \<notin> lvars (\<T> s')" using 1 2 3 unfolding s'_def by auto
    from update_bounds_id[OF this, of c] **(1)
    have "?P'' dir (update x c s') = ?P'' dir s'"
      unfolding Q_def
      by (intro iff_allI arg_cong2[of _ _ _ _ "(\<longrightarrow>)"] arg_cong2[of _ _ _ _ "(\<and>)"] refl, auto)
    with P
    show "?P'' dir (update x c ?s)" unfolding s'_def by blast
  qed auto
  then show "insert ia ats \<Turnstile>\<^sub>i \<B>\<I> (assert_bound ia s)" unfolding ia A_def by blast
qed


text \<open>Pivoting the tableau can be reduced to pivoting single equations,
  and substituting variable by polynomials. These operations are specified
  by:\<close>

locale PivotEq =
  fixes pivot_eq::"eq \<Rightarrow> var \<Rightarrow> eq"
  assumes
    \<comment> \<open>Lhs var of @{text eq} and @{text x\<^sub>j} are swapped,
     while the other variables do not change sides.\<close>
    vars_pivot_eq:"
\<lbrakk>x\<^sub>j \<in> rvars_eq eq; lhs eq \<notin> rvars_eq eq \<rbrakk> \<Longrightarrow> let eq' = pivot_eq eq x\<^sub>j in
    lhs eq' = x\<^sub>j \<and> rvars_eq eq' = {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})" and

\<comment> \<open>Pivoting keeps the equation equisatisfiable.\<close>

equiv_pivot_eq:
"\<lbrakk>x\<^sub>j \<in> rvars_eq eq; lhs eq \<notin> rvars_eq eq \<rbrakk> \<Longrightarrow>
    (v::'a::lrv valuation) \<Turnstile>\<^sub>e pivot_eq eq x\<^sub>j \<longleftrightarrow> v \<Turnstile>\<^sub>e eq"

begin

lemma lhs_pivot_eq:
  "\<lbrakk>x\<^sub>j \<in> rvars_eq eq; lhs eq \<notin> rvars_eq eq \<rbrakk> \<Longrightarrow> lhs (pivot_eq eq x\<^sub>j) = x\<^sub>j"
  using vars_pivot_eq
  by (simp add: Let_def)

lemma rvars_pivot_eq:
  "\<lbrakk>x\<^sub>j \<in> rvars_eq eq; lhs eq \<notin> rvars_eq eq \<rbrakk> \<Longrightarrow> rvars_eq (pivot_eq eq x\<^sub>j) = {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})"
  using vars_pivot_eq
  by (simp add: Let_def)

end


abbreviation doublesub (" _ \<subseteq>s _ \<subseteq>s _" [50,51,51] 50) where
  "doublesub a b c \<equiv> a \<subseteq> b \<and> b \<subseteq> c"


locale SubstVar =
  fixes subst_var::"var \<Rightarrow> linear_poly \<Rightarrow> linear_poly \<Rightarrow> linear_poly"
  assumes
    \<comment> \<open>Effect of @{text "subst_var x\<^sub>j lp' lp"} on @{text lp} variables.\<close>

vars_subst_var':
"(vars lp - {x\<^sub>j}) - vars lp' \<subseteq>s vars (subst_var x\<^sub>j lp' lp) \<subseteq>s (vars lp - {x\<^sub>j}) \<union> vars lp'"and

subst_no_effect: "x\<^sub>j \<notin> vars lp \<Longrightarrow> subst_var x\<^sub>j lp' lp = lp" and

subst_with_effect: "x\<^sub>j \<in> vars lp \<Longrightarrow> x \<in> vars lp' - vars lp \<Longrightarrow> x \<in> vars (subst_var x\<^sub>j lp' lp)" and

\<comment> \<open>Effect of @{text "subst_var x\<^sub>j lp' lp"} on @{text lp} value.\<close>

equiv_subst_var:
"(v::'a :: lrv valuation) x\<^sub>j = lp' \<lbrace>v\<rbrace> \<longrightarrow> lp \<lbrace>v\<rbrace> = (subst_var x\<^sub>j lp' lp) \<lbrace>v\<rbrace>"

begin

lemma vars_subst_var:
  "vars (subst_var x\<^sub>j lp' lp) \<subseteq> (vars lp - {x\<^sub>j}) \<union> vars lp'"
  using vars_subst_var'
  by simp

lemma vars_subst_var_supset:
  "vars (subst_var x\<^sub>j lp' lp) \<supseteq> (vars lp - {x\<^sub>j}) - vars lp'"
  using vars_subst_var'
  by simp

definition subst_var_eq :: "var \<Rightarrow> linear_poly \<Rightarrow> eq \<Rightarrow> eq" where
  "subst_var_eq v lp' eq \<equiv> (lhs eq, subst_var v lp' (rhs eq))"

lemma rvars_eq_subst_var_eq:
  shows "rvars_eq (subst_var_eq x\<^sub>j lp eq) \<subseteq> (rvars_eq eq - {x\<^sub>j}) \<union> vars lp"
  unfolding subst_var_eq_def
  by (auto simp add: vars_subst_var)

lemma rvars_eq_subst_var_eq_supset:
  "rvars_eq (subst_var_eq x\<^sub>j lp eq) \<supseteq> (rvars_eq eq) - {x\<^sub>j} - (vars lp)"
  unfolding subst_var_eq_def
  by (simp add: vars_subst_var_supset)

lemma equiv_subst_var_eq:
  assumes "(v::'a valuation) \<Turnstile>\<^sub>e (x\<^sub>j, lp')"
  shows "v \<Turnstile>\<^sub>e eq \<longleftrightarrow> v \<Turnstile>\<^sub>e subst_var_eq x\<^sub>j lp' eq"
  using assms
  unfolding subst_var_eq_def
  unfolding satisfies_eq_def
  using equiv_subst_var[of v x\<^sub>j lp' "rhs eq"]
  by auto
end

locale Pivot' = EqForLVar + PivotEq + SubstVar
begin
definition pivot_tableau' :: "var \<Rightarrow> var \<Rightarrow> tableau \<Rightarrow> tableau" where
  "pivot_tableau' x\<^sub>i x\<^sub>j t \<equiv>
    let x\<^sub>i_idx = eq_idx_for_lvar t x\<^sub>i; eq = t ! x\<^sub>i_idx; eq' = pivot_eq eq x\<^sub>j in
    map (\<lambda> idx. if idx = x\<^sub>i_idx then
                    eq'
                else
                    subst_var_eq x\<^sub>j (rhs eq') (t ! idx)
        ) [0..<length t]"

definition pivot' :: "var \<Rightarrow> var \<Rightarrow> ('i,'a::lrv) state \<Rightarrow> ('i,'a) state" where
  "pivot' x\<^sub>i x\<^sub>j s \<equiv> \<T>_update (pivot_tableau' x\<^sub>i x\<^sub>j (\<T> s)) s"

text\<open>\noindent Then, the next implementation of \<open>pivot\<close> satisfies its specification:\<close>

definition pivot_tableau :: "var \<Rightarrow> var \<Rightarrow> tableau \<Rightarrow> tableau" where
  "pivot_tableau x\<^sub>i x\<^sub>j t \<equiv> let eq = eq_for_lvar t x\<^sub>i; eq' = pivot_eq eq x\<^sub>j in
    map (\<lambda> e. if lhs e = lhs eq then eq' else subst_var_eq x\<^sub>j (rhs eq') e) t"

definition pivot :: "var \<Rightarrow> var \<Rightarrow> ('i,'a::lrv) state \<Rightarrow> ('i,'a) state" where
  "pivot x\<^sub>i x\<^sub>j s \<equiv> \<T>_update (pivot_tableau x\<^sub>i x\<^sub>j (\<T> s)) s"

lemma pivot_tableau'pivot_tableau:
  assumes "\<triangle> t" "x\<^sub>i \<in> lvars t"
  shows "pivot_tableau' x\<^sub>i x\<^sub>j t = pivot_tableau x\<^sub>i x\<^sub>j t"
proof-
  let ?f = "\<lambda>idx. if idx = eq_idx_for_lvar t x\<^sub>i then pivot_eq (t ! eq_idx_for_lvar t x\<^sub>i) x\<^sub>j
          else subst_var_eq x\<^sub>j (rhs (pivot_eq (t ! eq_idx_for_lvar t x\<^sub>i) x\<^sub>j)) (t ! idx)"
  let ?f' = "\<lambda>e. if lhs e = lhs (eq_for_lvar t x\<^sub>i) then pivot_eq (eq_for_lvar t x\<^sub>i) x\<^sub>j else subst_var_eq x\<^sub>j (rhs (pivot_eq (eq_for_lvar t x\<^sub>i) x\<^sub>j)) e"
  have "\<forall> i < length t. ?f' (t ! i) = ?f i"
  proof(safe)
    fix i
    assume "i < length t"
    then have "t ! i \<in> set t" "i < length t"
      by auto
    moreover
    have "t ! eq_idx_for_lvar t x\<^sub>i \<in> set t" "eq_idx_for_lvar t x\<^sub>i < length t"
      using eq_for_lvar[of x\<^sub>i t] \<open>x\<^sub>i \<in> lvars t\<close> eq_idx_for_lvar[of x\<^sub>i t]
      by (auto simp add: eq_for_lvar_def)
    ultimately
    have "lhs (t ! i) = lhs (t ! eq_idx_for_lvar t x\<^sub>i) \<Longrightarrow> t ! i = t ! (eq_idx_for_lvar t x\<^sub>i)" "distinct t"
      using \<open>\<triangle> t\<close>
      unfolding normalized_tableau_def
      by (auto simp add: distinct_map inj_on_def)
    then have "lhs (t ! i) = lhs (t ! eq_idx_for_lvar t x\<^sub>i) \<Longrightarrow> i = eq_idx_for_lvar t x\<^sub>i"
      using \<open>i < length t\<close> \<open>eq_idx_for_lvar t x\<^sub>i < length t\<close>
      by (auto simp add: distinct_conv_nth)
    then show "?f' (t ! i) = ?f i"
      by (auto simp add: eq_for_lvar_def)
  qed
  then show "pivot_tableau' x\<^sub>i x\<^sub>j t = pivot_tableau x\<^sub>i x\<^sub>j t"
    unfolding pivot_tableau'_def pivot_tableau_def
    unfolding Let_def
    by (auto simp add: map_reindex)
qed

lemma pivot'pivot: fixes s :: "('i,'a::lrv)state"
  assumes "\<triangle> (\<T> s)" "x\<^sub>i \<in> lvars (\<T> s)"
  shows "pivot' x\<^sub>i x\<^sub>j s = pivot x\<^sub>i x\<^sub>j s"
  using pivot_tableau'pivot_tableau[OF assms]
  unfolding pivot_def pivot'_def by auto
end


sublocale Pivot' < Pivot eq_idx_for_lvar pivot
proof
  fix s::"('i,'a) state" and x\<^sub>i x\<^sub>j and v::"'a valuation"
  assume "\<triangle> (\<T> s)" "x\<^sub>i \<in> lvars (\<T> s)"
    "x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)"
  show "let s' = pivot x\<^sub>i x\<^sub>j s in \<V> s' = \<V> s \<and> \<B>\<^sub>i s' = \<B>\<^sub>i s \<and> \<U> s' = \<U> s \<and> \<U>\<^sub>c s' = \<U>\<^sub>c s"
    unfolding pivot_def
    by (auto simp add: Let_def simp: boundsl_def boundsu_def indexl_def indexu_def)

  let ?t = "\<T> s"
  let ?idx = "eq_idx_for_lvar ?t x\<^sub>i"
  let ?eq = "?t ! ?idx"
  let ?eq' = "pivot_eq ?eq x\<^sub>j"

  have "?idx < length ?t" "lhs (?t ! ?idx) = x\<^sub>i"
    using \<open>x\<^sub>i \<in> lvars ?t\<close>
    using eq_idx_for_lvar
    by auto

  have "distinct (map lhs ?t)"
    using \<open>\<triangle> ?t\<close>
    unfolding normalized_tableau_def
    by simp

  have "x\<^sub>j \<in> rvars_eq ?eq"
    using \<open>x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)\<close>
    unfolding eq_for_lvar_def
    by simp
  then have "x\<^sub>j \<in> rvars ?t"
    using \<open>?idx < length ?t\<close>
    using in_set_conv_nth[of ?eq ?t]
    by (auto simp add: rvars_def)
  then have "x\<^sub>j \<notin> lvars ?t"
    using \<open>\<triangle> ?t\<close>
    unfolding normalized_tableau_def
    by auto

  have "x\<^sub>i \<notin> rvars ?t"
    using \<open>x\<^sub>i \<in> lvars ?t\<close> \<open>\<triangle> ?t\<close>
    unfolding normalized_tableau_def rvars_def
    by auto
  then have "x\<^sub>i \<notin> rvars_eq ?eq"
    unfolding rvars_def
    using \<open>?idx < length ?t\<close>
    using in_set_conv_nth[of ?eq ?t]
    by auto

  have "x\<^sub>i \<noteq> x\<^sub>j"
    using \<open>x\<^sub>j \<in> rvars_eq ?eq\<close>  \<open>x\<^sub>i \<notin> rvars_eq ?eq\<close>
    by auto

  have "?eq' = (x\<^sub>j, rhs ?eq')"
    using lhs_pivot_eq[of x\<^sub>j ?eq]
    using \<open>x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)\<close> \<open>lhs (?t ! ?idx) = x\<^sub>i\<close> \<open>x\<^sub>i \<notin> rvars_eq ?eq\<close>
    by (auto simp add: eq_for_lvar_def) (cases "?eq'", simp)+

  let ?I1 = "[0..<?idx]"
  let ?I2 = "[?idx + 1..<length ?t]"
  have "[0..<length ?t] = ?I1 @ [?idx] @ ?I2"
    using \<open>?idx < length ?t\<close>
    by (rule interval_3split)
  then have map_lhs_pivot:
    "map lhs (\<T> (pivot' x\<^sub>i x\<^sub>j s)) =
     map (\<lambda>idx. lhs (?t ! idx)) ?I1 @ [x\<^sub>j] @ map (\<lambda>idx. lhs (?t ! idx)) ?I2"
    using \<open>x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)\<close> \<open>lhs (?t ! ?idx) = x\<^sub>i\<close> \<open>x\<^sub>i \<notin> rvars_eq ?eq\<close>
    by (auto simp add: Let_def subst_var_eq_def eq_for_lvar_def lhs_pivot_eq pivot'_def pivot_tableau'_def)

  have lvars_pivot: "lvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) =
        lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
  proof-
    have "lvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) =
          {x\<^sub>j} \<union> (\<lambda>idx. lhs (?t ! idx)) ` ({0..<length?t} - {?idx})"
      using \<open>?idx < length ?t\<close> \<open>?eq' = (x\<^sub>j, rhs ?eq')\<close>
      by (cases ?eq', auto simp add: Let_def pivot'_def pivot_tableau'_def lvars_def subst_var_eq_def)+
    also have "... = {x\<^sub>j} \<union> (((\<lambda>idx. lhs (?t ! idx)) ` {0..<length?t}) - {lhs (?t ! ?idx)})"
      using \<open>?idx < length ?t\<close> \<open>distinct (map lhs ?t)\<close>
      by (auto simp add: distinct_conv_nth)
    also have "... = {x\<^sub>j} \<union> (set (map lhs ?t) - {x\<^sub>i})"
      using \<open>lhs (?t ! ?idx) = x\<^sub>i\<close>
      by (auto simp add: in_set_conv_nth rev_image_eqI) (auto simp add: image_def)
    finally show "lvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) =
      lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
      by (simp add: lvars_def)
  qed
  moreover
  have rvars_pivot: "rvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) =
        rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
  proof-
    have "rvars_eq ?eq' = {x\<^sub>i} \<union> (rvars_eq ?eq - {x\<^sub>j})"
      using rvars_pivot_eq[of x\<^sub>j ?eq]
      using \<open>lhs (?t ! ?idx) = x\<^sub>i\<close>
      using \<open>x\<^sub>j \<in> rvars_eq ?eq\<close> \<open>x\<^sub>i \<notin> rvars_eq ?eq\<close>
      by simp

    let ?S1 = "rvars_eq ?eq'"
    let ?S2 = "\<Union>idx\<in>({0..<length ?t} - {?idx}).
                  rvars_eq (subst_var_eq x\<^sub>j (rhs ?eq') (?t ! idx))"

    have "rvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) = ?S1 \<union> ?S2"
      unfolding pivot'_def pivot_tableau'_def rvars_def
      using \<open>?idx < length ?t\<close>
      by (auto simp add: Let_def split: if_splits)
    also have "... = {x\<^sub>i} \<union> (rvars ?t - {x\<^sub>j})" (is "?S1 \<union> ?S2 = ?rhs")
    proof
      show "?S1 \<union> ?S2 \<subseteq> ?rhs"
      proof-
        have "?S1 \<subseteq> ?rhs"
          using \<open>?idx < length ?t\<close>
          unfolding rvars_def
          using \<open>rvars_eq ?eq' = {x\<^sub>i} \<union> (rvars_eq ?eq - {x\<^sub>j})\<close>
          by (force simp add: in_set_conv_nth)
        moreover
        have "?S2 \<subseteq> ?rhs"
        proof-
          have "?S2 \<subseteq> (\<Union>idx\<in>{0..<length ?t}. (rvars_eq (?t ! idx) - {x\<^sub>j}) \<union> rvars_eq ?eq')"
            apply (rule UN_mono)
            using rvars_eq_subst_var_eq
            by auto
          also have "... \<subseteq> rvars_eq ?eq' \<union> (\<Union>idx\<in>{0..<length ?t}. rvars_eq (?t ! idx) - {x\<^sub>j})"
            by auto
          also have "... = rvars_eq ?eq' \<union> (rvars ?t - {x\<^sub>j})"
            unfolding rvars_def
            by (force simp add: in_set_conv_nth)
          finally show ?thesis
            using \<open>rvars_eq ?eq' = {x\<^sub>i} \<union> (rvars_eq ?eq - {x\<^sub>j})\<close>
            unfolding rvars_def
            using \<open>?idx < length ?t\<close>
            by auto
        qed
        ultimately
        show ?thesis
          by simp
      qed
    next
      show "?rhs \<subseteq> ?S1 \<union> ?S2"
      proof
        fix x
        assume "x \<in> ?rhs"
        show "x \<in> ?S1 \<union> ?S2"
        proof (cases "x \<in> rvars_eq ?eq'")
          case True
          then show ?thesis
            by auto
        next
          case False
          let ?S2'  = "\<Union>idx\<in>({0..<length ?t} - {?idx}).
                        (rvars_eq (?t ! idx) - {x\<^sub>j}) - rvars_eq ?eq'"
          have "x \<in> ?S2'"
            using False \<open>x \<in> ?rhs\<close>
            using \<open>rvars_eq ?eq' = {x\<^sub>i} \<union> (rvars_eq ?eq - {x\<^sub>j})\<close>
            unfolding rvars_def
            by (force simp add: in_set_conv_nth)
          moreover
          have "?S2 \<supseteq> ?S2'"
            apply (rule UN_mono)
            using rvars_eq_subst_var_eq_supset[of _ x\<^sub>j "rhs ?eq'" ]
            by auto
          ultimately
          show ?thesis
            by auto
        qed
      qed
    qed
    ultimately
    show ?thesis
      by simp
  qed
  ultimately
  show "let s' = pivot x\<^sub>i x\<^sub>j s in rvars (\<T> s') = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i} \<and> lvars (\<T> s') = lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
    using pivot'pivot[where ?'i = 'i]
    using \<open>\<triangle> (\<T> s)\<close> \<open>x\<^sub>i \<in> lvars (\<T> s)\<close>
    by (simp add: Let_def)
  have "\<triangle> (\<T> (pivot' x\<^sub>i x\<^sub>j s))"
    unfolding normalized_tableau_def
  proof
    have "lvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) \<inter> rvars (\<T> (pivot' x\<^sub>i x\<^sub>j s)) = {}" (is ?g1)
      using \<open>\<triangle> (\<T> s)\<close>
      unfolding normalized_tableau_def
      using lvars_pivot rvars_pivot
      using \<open>x\<^sub>i \<noteq> x\<^sub>j\<close>
      by auto

    moreover have "0 \<notin> rhs ` set (\<T> (pivot' x\<^sub>i x\<^sub>j s))" (is ?g2)
    proof
      let ?eq = "eq_for_lvar (\<T> s) x\<^sub>i" 
      from eq_for_lvar[OF \<open>x\<^sub>i \<in> lvars (\<T> s)\<close>]
      have "?eq \<in> set (\<T> s)" and var: "lhs ?eq = x\<^sub>i" by auto
      have "lhs ?eq \<notin> rvars_eq ?eq" using \<open>\<triangle> (\<T> s)\<close> \<open>?eq \<in> set (\<T> s)\<close>
        using \<open>x\<^sub>i \<notin> rvars_eq (\<T> s ! eq_idx_for_lvar (\<T> s) x\<^sub>i)\<close> eq_for_lvar_def var by auto
      from vars_pivot_eq[OF \<open>x\<^sub>j \<in> rvars_eq ?eq\<close> this]
      have vars_pivot: "lhs (pivot_eq ?eq x\<^sub>j) = x\<^sub>j" "rvars_eq (pivot_eq ?eq x\<^sub>j) = {lhs (eq_for_lvar (\<T> s) x\<^sub>i)} \<union> (rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i) - {x\<^sub>j})" 
        unfolding Let_def by auto
      from vars_pivot(2) have rhs_pivot0: "rhs (pivot_eq ?eq x\<^sub>j) \<noteq> 0" using vars_zero by auto
      assume "0 \<in> rhs ` set (\<T> (pivot' x\<^sub>i x\<^sub>j s))" 
      from this[unfolded pivot'pivot[OF \<open>\<triangle> (\<T> s)\<close> \<open>x\<^sub>i \<in> lvars (\<T> s)\<close>] pivot_def]
      have "0 \<in> rhs ` set (pivot_tableau x\<^sub>i x\<^sub>j (\<T> s))" by simp
      from this[unfolded pivot_tableau_def Let_def var, unfolded var] rhs_pivot0
      obtain e where "e \<in> set (\<T> s)" "lhs e \<noteq> x\<^sub>i" and rvars_eq: "rvars_eq (subst_var_eq x\<^sub>j (rhs (pivot_eq ?eq x\<^sub>j)) e) = {}" 
        by (auto simp: vars_zero)
      from rvars_eq[unfolded subst_var_eq_def]
      have empty: "vars (subst_var x\<^sub>j (rhs (pivot_eq ?eq x\<^sub>j)) (rhs e)) = {}" by auto 
      show False
      proof (cases "x\<^sub>j \<in> vars (rhs e)")
        case False
        from empty[unfolded subst_no_effect[OF False]]
        have "rvars_eq e = {}" by auto
        hence "rhs e = 0" using zero_coeff_zero coeff_zero by auto
        with \<open>e \<in> set (\<T> s)\<close> \<open>\<triangle> (\<T> s)\<close> show False unfolding normalized_tableau_def by auto
      next
        case True
        from \<open>e \<in> set (\<T> s)\<close> have "rvars_eq e \<subseteq> rvars (\<T> s)" unfolding rvars_def by auto
        hence "x\<^sub>i \<in> vars (rhs (pivot_eq ?eq x\<^sub>j)) - rvars_eq e" 
          unfolding vars_pivot(2) var 
          using \<open>\<triangle> (\<T> s)\<close>[unfolded normalized_tableau_def] \<open>x\<^sub>i \<in> lvars (\<T> s)\<close> by auto
        from subst_with_effect[OF True this] rvars_eq
        show ?thesis by (simp add: subst_var_eq_def)
      qed
    qed

    ultimately show "?g1 \<and> ?g2" ..

    show "distinct (map lhs (\<T> (pivot' x\<^sub>i x\<^sub>j s)))"
      using map_parametrize_idx[of lhs ?t]
      using map_lhs_pivot
      using \<open>distinct (map lhs ?t)\<close>
      using interval_3split[of ?idx "length ?t"] \<open>?idx < length ?t\<close>
      using \<open>x\<^sub>j \<notin> lvars ?t\<close>
      unfolding lvars_def
      by auto
  qed
  moreover
  have "v \<Turnstile>\<^sub>t ?t = v \<Turnstile>\<^sub>t \<T> (pivot' x\<^sub>i x\<^sub>j s)"
    unfolding satisfies_tableau_def
  proof
    assume "\<forall>e\<in>set (?t). v \<Turnstile>\<^sub>e e"
    show "\<forall>e\<in>set (\<T> (pivot' x\<^sub>i x\<^sub>j s)). v \<Turnstile>\<^sub>e e"
    proof-
      have "v \<Turnstile>\<^sub>e ?eq'"
        using \<open>x\<^sub>i \<notin> rvars_eq ?eq\<close>
        using \<open>?idx < length ?t\<close> \<open>\<forall>e\<in>set (?t). v \<Turnstile>\<^sub>e e\<close>
        using \<open>x\<^sub>j \<in> rvars_eq ?eq\<close> \<open>x\<^sub>i \<in> lvars ?t\<close>
        by (simp add: equiv_pivot_eq eq_idx_for_lvar)
      moreover
      {
        fix idx
        assume "idx < length ?t" "idx \<noteq> ?idx"

        have "v \<Turnstile>\<^sub>e subst_var_eq x\<^sub>j (rhs ?eq') (?t ! idx)"
          using \<open>?eq' = (x\<^sub>j, rhs ?eq')\<close>
          using \<open>v \<Turnstile>\<^sub>e ?eq'\<close> \<open>idx < length ?t\<close> \<open>\<forall>e\<in>set (?t). v \<Turnstile>\<^sub>e e\<close>
          using equiv_subst_var_eq[of v x\<^sub>j "rhs ?eq'" "?t ! idx"]
          by auto
      }
      ultimately
      show ?thesis
        by (auto simp add: pivot'_def pivot_tableau'_def Let_def)
    qed
  next
    assume "\<forall>e\<in>set (\<T> (pivot' x\<^sub>i x\<^sub>j s)). v \<Turnstile>\<^sub>e e"
    then have "v \<Turnstile>\<^sub>e ?eq'"
      "\<And> idx. \<lbrakk>idx < length ?t; idx \<noteq> ?idx \<rbrakk> \<Longrightarrow> v \<Turnstile>\<^sub>e subst_var_eq x\<^sub>j (rhs ?eq') (?t ! idx)"
      using \<open>?idx < length ?t\<close>
      unfolding pivot'_def pivot_tableau'_def
      by (auto simp add: Let_def)

    show "\<forall>e\<in>set (\<T> s). v \<Turnstile>\<^sub>e e"
    proof-
      {
        fix idx
        assume "idx < length ?t"
        have "v \<Turnstile>\<^sub>e (?t ! idx)"
        proof (cases "idx = ?idx")
          case True
          then show ?thesis
            using \<open>v \<Turnstile>\<^sub>e ?eq'\<close>
            using \<open>x\<^sub>j \<in> rvars_eq ?eq\<close> \<open>x\<^sub>i \<in> lvars ?t\<close> \<open>x\<^sub>i \<notin> rvars_eq ?eq\<close>
            by (simp add: eq_idx_for_lvar equiv_pivot_eq)
        next
          case False
          then show ?thesis
            using \<open>idx < length ?t\<close>
            using \<open>\<lbrakk>idx < length ?t; idx \<noteq> ?idx \<rbrakk> \<Longrightarrow> v \<Turnstile>\<^sub>e subst_var_eq x\<^sub>j (rhs ?eq') (?t ! idx)\<close>
            using \<open>v \<Turnstile>\<^sub>e ?eq'\<close> \<open>?eq' = (x\<^sub>j, rhs ?eq')\<close>
            using equiv_subst_var_eq[of v x\<^sub>j "rhs ?eq'" "?t ! idx"]
            by auto
        qed
      }
      then show ?thesis
        by (force simp add: in_set_conv_nth)
    qed
  qed
  ultimately
  show "let s' = pivot x\<^sub>i x\<^sub>j s in v \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t \<T> s' \<and> \<triangle> (\<T> s')"
    using pivot'pivot[where ?'i = 'i]
    using \<open>\<triangle> (\<T> s)\<close> \<open>x\<^sub>i \<in> lvars (\<T> s)\<close>
    by (simp add: Let_def)
qed


subsection\<open>Check implementation\<close>

text\<open>The \<open>check\<close> function is called when all rhs variables are
in bounds, and it checks if there is a lhs variable that is not. If
there is no such variable, then satisfiability is detected and \<open>check\<close> succeeds. If there is a lhs variable \<open>x\<^sub>i\<close> out of its
bounds, a rhs variable \<open>x\<^sub>j\<close> is sought which allows pivoting
with \<open>x\<^sub>i\<close> and updating \<open>x\<^sub>i\<close> to its violated bound. If
\<open>x\<^sub>i\<close> is under its lower bound it must be increased, and if
\<open>x\<^sub>j\<close> has a positive coefficient it must be increased so it
must be under its upper bound and if it has a negative coefficient it
must be decreased so it must be above its lower bound. The case when
\<open>x\<^sub>i\<close> is above its upper bound is symmetric (avoiding
symmetries is discussed in Section \ref{sec:symmetries}). If there is
no such \<open>x\<^sub>j\<close>, unsatisfiability is detected and \<open>check\<close>
fails. The procedure is recursively repeated, until it either succeeds
or fails. To ensure termination, variables \<open>x\<^sub>i\<close> and \<open>x\<^sub>j\<close> must be chosen with respect to a fixed variable ordering. For
choosing these variables auxiliary functions \<open>min_lvar_not_in_bounds\<close>, \<open>min_rvar_inc\<close> and \<open>min_rvar_dec\<close> are specified (each in its own locale). For, example:
\<close>

locale MinLVarNotInBounds = fixes min_lvar_not_in_bounds::"('i,'a::lrv) state \<Rightarrow> var option"
  assumes

min_lvar_not_in_bounds_None: "min_lvar_not_in_bounds s = None \<longrightarrow> (\<forall>x\<in>lvars (\<T> s). in_bounds x \<langle>\<V> s\<rangle> (\<B> s))" and

min_lvar_not_in_bounds_Some': "min_lvar_not_in_bounds s = Some x\<^sub>i \<longrightarrow> x\<^sub>i\<in>lvars (\<T> s) \<and> \<not>in_bounds x\<^sub>i \<langle>\<V> s\<rangle> (\<B> s)
    \<and> (\<forall>x\<in>lvars (\<T> s). x < x\<^sub>i \<longrightarrow> in_bounds x \<langle>\<V> s\<rangle> (\<B> s))"

begin
lemma min_lvar_not_in_bounds_None':
  "min_lvar_not_in_bounds s = None \<longrightarrow> (\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>b \<B> s \<parallel> lvars (\<T> s))"
  unfolding satisfies_bounds_set.simps
  by (rule min_lvar_not_in_bounds_None)

lemma min_lvar_not_in_bounds_lvars:"min_lvar_not_in_bounds s = Some x\<^sub>i \<longrightarrow> x\<^sub>i \<in> lvars (\<T> s)"
  using min_lvar_not_in_bounds_Some'
  by simp

lemma min_lvar_not_in_bounds_Some: "min_lvar_not_in_bounds s = Some x\<^sub>i \<longrightarrow> \<not> in_bounds x\<^sub>i \<langle>\<V> s\<rangle> (\<B> s)"
  using min_lvar_not_in_bounds_Some'
  by simp


lemma min_lvar_not_in_bounds_Some_min: "min_lvar_not_in_bounds s = Some x\<^sub>i \<longrightarrow>  (\<forall> x \<in> lvars (\<T> s). x < x\<^sub>i \<longrightarrow> in_bounds x \<langle>\<V> s\<rangle> (\<B> s))"
  using min_lvar_not_in_bounds_Some'
  by simp

end


abbreviation reasable_var where
  "reasable_var dir x eq s \<equiv>
   (coeff (rhs eq) x > 0 \<and> \<lhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (UB dir s x)) \<or>
   (coeff (rhs eq) x < 0 \<and> \<rhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (LB dir s x))"

locale MinRVarsEq =
  fixes min_rvar_incdec_eq :: "('i,'a) Direction \<Rightarrow> ('i,'a::lrv) state \<Rightarrow> eq \<Rightarrow> 'i list + var"
  assumes min_rvar_incdec_eq_None:
    "min_rvar_incdec_eq dir s eq = Inl is \<Longrightarrow>
      (\<forall> x \<in> rvars_eq eq. \<not> reasable_var dir x eq s) \<and>
      (set is = {LI dir s (lhs eq)} \<union> {LI dir s x | x. x \<in> rvars_eq eq \<and> coeff (rhs eq) x < 0}
          \<union> {UI dir s x | x. x \<in> rvars_eq eq \<and> coeff (rhs eq) x > 0}) \<and>
      ((dir = Positive \<or> dir = Negative) \<longrightarrow> LI dir s (lhs eq) \<in> indices_state s \<longrightarrow> set is \<subseteq> indices_state s)"
  assumes min_rvar_incdec_eq_Some_rvars:
    "min_rvar_incdec_eq dir s eq = Inr x\<^sub>j \<Longrightarrow> x\<^sub>j \<in> rvars_eq eq"
  assumes min_rvar_incdec_eq_Some_incdec:
    "min_rvar_incdec_eq dir s eq = Inr x\<^sub>j \<Longrightarrow> reasable_var dir x\<^sub>j eq s"
  assumes min_rvar_incdec_eq_Some_min:
    "min_rvar_incdec_eq dir s eq = Inr x\<^sub>j \<Longrightarrow>
    (\<forall> x \<in> rvars_eq eq. x < x\<^sub>j \<longrightarrow> \<not> reasable_var dir x eq s)"
begin
lemma min_rvar_incdec_eq_None':
  assumes *: "dir = Positive \<or> dir = Negative"
    and min: "min_rvar_incdec_eq dir s eq = Inl is"
    and sub: "I = set is"
    and Iv: "(I,v) \<Turnstile>\<^sub>i\<^sub>b \<B>\<I> s"
  shows "le (lt dir) ((rhs eq) \<lbrace>v\<rbrace>) ((rhs eq) \<lbrace>\<langle>\<V> s\<rangle>\<rbrace>)"
proof -
  have "\<forall> x \<in> rvars_eq eq. \<not> reasable_var dir x eq s"
    using min
    using min_rvar_incdec_eq_None
    by simp

  have "\<forall> x \<in> rvars_eq eq. (0 < coeff (rhs eq) x \<longrightarrow> le (lt dir) 0 (\<langle>\<V> s\<rangle> x - v x)) \<and> (coeff (rhs eq) x < 0 \<longrightarrow> le (lt dir) (\<langle>\<V> s\<rangle> x - v x) 0)"
  proof (safe)
    fix x
    assume x: "x \<in> rvars_eq eq" "0 < coeff (rhs eq) x" "0 \<noteq> \<langle>\<V> s\<rangle> x - v x"
    then have "\<not> (\<lhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (UB dir s x))"
      using \<open>\<forall> x \<in> rvars_eq eq. \<not> reasable_var dir x eq s\<close>
      by auto
    then have "\<unrhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (UB dir s x)"
      using *
      by (cases "UB dir s x") (auto simp add: bound_compare_defs)
    moreover
    from min_rvar_incdec_eq_None[OF min] x sub have "UI dir s x \<in> I" by auto
    from Iv * this
    have "\<unlhd>\<^sub>u\<^sub>b (lt dir) (v x) (UB dir s x)"
      unfolding satisfies_bounds_index.simps
      by (cases "UB dir s x", auto simp: indexl_def indexu_def boundsl_def boundsu_def bound_compare'_defs)
        (fastforce)+
    ultimately
    have "le (lt dir) (v x) (\<langle>\<V> s\<rangle> x)"
      using *
      by (cases "UB dir s x") (auto simp add: bound_compare_defs)
    then show "lt dir 0 (\<langle>\<V> s\<rangle> x - v x)"
      using \<open>0 \<noteq> \<langle>\<V> s\<rangle> x - v x\<close> *
      using minus_gt[of "v x" "\<langle>\<V> s\<rangle> x"] minus_lt[of "\<langle>\<V> s\<rangle> x" "v x"]
      by auto
  next
    fix x
    assume x: "x \<in> rvars_eq eq" "0 > coeff (rhs eq) x" "\<langle>\<V> s\<rangle> x - v x \<noteq> 0"
    then have "\<not> (\<rhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (LB dir s x))"
      using \<open>\<forall> x \<in> rvars_eq eq. \<not> reasable_var dir x eq s\<close>
      by auto
    then have "\<unlhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (LB dir s x)"
      using *
      by (cases "LB dir s x") (auto simp add: bound_compare_defs)
    moreover
    from min_rvar_incdec_eq_None[OF min] x sub have "LI dir s x \<in> I" by auto
    from Iv * this
    have "\<unrhd>\<^sub>l\<^sub>b (lt dir) (v x) (LB dir s x)"
      unfolding satisfies_bounds_index.simps
      by (cases "LB dir s x", auto simp: indexl_def indexu_def boundsl_def boundsu_def bound_compare'_defs)
        (fastforce)+

    ultimately
    have "le (lt dir) (\<langle>\<V> s\<rangle> x) (v x)"
      using *
      by (cases "LB dir s x") (auto simp add: bound_compare_defs)
    then show "lt dir (\<langle>\<V> s\<rangle> x - v x) 0"
      using \<open>\<langle>\<V> s\<rangle> x - v x \<noteq> 0\<close> *
      using minus_lt[of "\<langle>\<V> s\<rangle> x" "v x"] minus_gt[of "v x" "\<langle>\<V> s\<rangle> x"]
      by auto
  qed
  then have "le (lt dir) 0 (rhs eq \<lbrace> \<lambda> x. \<langle>\<V> s\<rangle> x - v x\<rbrace>)"
    using *
    apply auto
    using valuate_nonneg[of "rhs eq" "\<lambda>x. \<langle>\<V> s\<rangle> x - v x"]
     apply force
    using valuate_nonpos[of "rhs eq" "\<lambda>x. \<langle>\<V> s\<rangle> x - v x"]
    apply force
    done
  then show "le (lt dir) rhs eq \<lbrace> v \<rbrace> rhs eq \<lbrace> \<langle>\<V> s\<rangle> \<rbrace>"
    using \<open>dir = Positive \<or> dir = Negative\<close>
    using minus_gt[of "rhs eq \<lbrace> v \<rbrace>" "rhs eq \<lbrace> \<langle>\<V> s\<rangle> \<rbrace>"]
    by (auto simp add: valuate_diff[THEN sym])
qed
end


locale MinRVars = EqForLVar + MinRVarsEq min_rvar_incdec_eq
  for min_rvar_incdec_eq :: "('i, 'a :: lrv) Direction \<Rightarrow> _"
begin
abbreviation min_rvar_incdec :: "('i,'a) Direction \<Rightarrow> ('i,'a) state \<Rightarrow> var \<Rightarrow> 'i list + var" where
  "min_rvar_incdec dir s x\<^sub>i \<equiv> min_rvar_incdec_eq dir s (eq_for_lvar (\<T> s) x\<^sub>i)"
end


locale MinVars = MinLVarNotInBounds min_lvar_not_in_bounds + MinRVars eq_idx_for_lvar min_rvar_incdec_eq
  for min_lvar_not_in_bounds :: "('i,'a::lrv) state \<Rightarrow> _" and
    eq_idx_for_lvar and
    min_rvar_incdec_eq :: "('i, 'a :: lrv) Direction \<Rightarrow> _"

locale PivotUpdateMinVars =
  PivotAndUpdate eq_idx_for_lvar pivot_and_update +
  MinVars min_lvar_not_in_bounds eq_idx_for_lvar min_rvar_incdec_eq for
  eq_idx_for_lvar :: "tableau \<Rightarrow> var \<Rightarrow> nat" and
  min_lvar_not_in_bounds :: "('i,'a::lrv) state \<Rightarrow> var option" and
  min_rvar_incdec_eq :: "('i,'a) Direction \<Rightarrow> ('i,'a) state \<Rightarrow> eq \<Rightarrow> 'i list + var" and
  pivot_and_update :: "var \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state"
begin


definition check' where
  "check' dir x\<^sub>i s \<equiv>
     let l\<^sub>i = the (LB dir s x\<^sub>i);
         x\<^sub>j' = min_rvar_incdec dir s x\<^sub>i
     in case x\<^sub>j' of
           Inl I \<Rightarrow> set_unsat I s
         | Inr x\<^sub>j \<Rightarrow> pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s"

lemma check'_cases:
  assumes "\<And> I. \<lbrakk>min_rvar_incdec dir s x\<^sub>i = Inl I; check' dir x\<^sub>i s = set_unsat I s\<rbrakk> \<Longrightarrow> P (set_unsat I s)"
  assumes "\<And> x\<^sub>j l\<^sub>i. \<lbrakk>min_rvar_incdec dir s x\<^sub>i = Inr x\<^sub>j;
           l\<^sub>i = the (LB dir s x\<^sub>i);
           check' dir x\<^sub>i s = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s\<rbrakk> \<Longrightarrow>
        P (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s)"
  shows "P (check' dir x\<^sub>i s)"
  using assms
  unfolding check'_def
  by (cases "min_rvar_incdec dir s x\<^sub>i", auto)

partial_function (tailrec) check where
  "check s =
    (if \<U> s then s
     else let x\<^sub>i' = min_lvar_not_in_bounds s
          in case x\<^sub>i' of
               None \<Rightarrow> s
             | Some x\<^sub>i \<Rightarrow> let dir = if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive
                                    else Negative
                          in check (check' dir x\<^sub>i s))"
declare check.simps[code]

inductive check_dom where
  step: "\<lbrakk>\<And>x\<^sub>i. \<lbrakk>\<not> \<U> s; Some x\<^sub>i = min_lvar_not_in_bounds s; \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i\<rbrakk>
     \<Longrightarrow> check_dom (check' Positive x\<^sub>i s);
  \<And>x\<^sub>i. \<lbrakk>\<not> \<U> s; Some x\<^sub>i = min_lvar_not_in_bounds s; \<not> \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i\<rbrakk>
     \<Longrightarrow> check_dom (check' Negative x\<^sub>i s)\<rbrakk>
\<Longrightarrow> check_dom s"



text\<open>
The definition of \<open>check\<close> can be given by:

@{text[display]
"check s \<equiv> if \<U> s then s
            else let x\<^sub>i' = min_lvar_not_in_bounds s in
                 case x\<^sub>i' of  None \<Rightarrow> s
                           | Some x\<^sub>i \<Rightarrow> if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then check (check_inc x\<^sub>i s)
                                           else check (check_dec x\<^sub>i s)"
}

@{text[display]
"check_inc x\<^sub>i s \<equiv> let l\<^sub>i = the (\<B>\<^sub>l s x\<^sub>i); x\<^sub>j' = min_rvar_inc s x\<^sub>i in
   case x\<^sub>j' of None \<Rightarrow> s \<lparr> \<U> := True \<rparr> | Some x\<^sub>j \<Rightarrow> pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s"
}

The definition of \<open>check_dec\<close> is analogous. It is shown (mainly
by induction) that this definition satisfies the \<open>check\<close>
specification. Note that this definition uses general recursion, so
its termination is non-trivial. It has been shown that it terminates
for all states satisfying the check preconditions. The proof is based
on the proof outline given in \cite{simplex-rad}. It is very
technically involved, but conceptually uninteresting so we do not
discuss it in more details.\<close>

lemma pivotandupdate_check_precond:
  assumes
    "dir = (if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive else Negative)"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "min_rvar_incdec dir s x\<^sub>i = Inr x\<^sub>j"
    "l\<^sub>i = the (LB dir s x\<^sub>i)"
    "\<nabla> s" "\<triangle> (\<T> s)" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" " \<diamond> s"
  shows "\<triangle> (\<T> (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s)) \<and> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s) \<and> \<diamond> (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s) \<and> \<nabla> (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s)"
proof-
  have "\<B>\<^sub>l s x\<^sub>i = Some l\<^sub>i \<or> \<B>\<^sub>u s x\<^sub>i = Some l\<^sub>i"
    using \<open>l\<^sub>i = the (LB dir s x\<^sub>i)\<close> \<open>dir = (if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive else Negative)\<close>
    using \<open>min_lvar_not_in_bounds s = Some x\<^sub>i\<close> min_lvar_not_in_bounds_Some[of s x\<^sub>i]
    using \<open>\<diamond> s\<close>
    by (case_tac[!] "\<B>\<^sub>l s x\<^sub>i", case_tac[!] "\<B>\<^sub>u s x\<^sub>i") (auto simp add: bounds_consistent_def bound_compare_defs)
  then show ?thesis
    using assms
    using pivotandupdate_tableau_normalized[of s x\<^sub>i x\<^sub>j l\<^sub>i]
    using pivotandupdate_nolhs[of s x\<^sub>i x\<^sub>j l\<^sub>i]
    using pivotandupdate_bounds_consistent[of s x\<^sub>i x\<^sub>j l\<^sub>i]
    using pivotandupdate_tableau_valuated[of s x\<^sub>i x\<^sub>j l\<^sub>i]
    by (auto simp add: min_lvar_not_in_bounds_lvars  min_rvar_incdec_eq_Some_rvars)
qed


(* -------------------------------------------------------------------------- *)
(* Termination *)
(* -------------------------------------------------------------------------- *)

abbreviation gt_state' where
  "gt_state' dir s s' x\<^sub>i x\<^sub>j l\<^sub>i \<equiv>
  min_lvar_not_in_bounds s = Some x\<^sub>i \<and>
  l\<^sub>i = the (LB dir s x\<^sub>i) \<and>
  min_rvar_incdec dir s x\<^sub>i = Inr x\<^sub>j \<and>
  s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s"

definition gt_state :: "('i,'a) state \<Rightarrow> ('i,'a) state \<Rightarrow> bool" (infixl "\<succ>\<^sub>x" 100) where
  "s \<succ>\<^sub>x s' \<equiv>
   \<exists> x\<^sub>i x\<^sub>j l\<^sub>i.
     let dir = if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive else Negative in
     gt_state' dir s s' x\<^sub>i x\<^sub>j l\<^sub>i"

abbreviation succ :: "('i,'a) state \<Rightarrow> ('i,'a) state \<Rightarrow> bool" (infixl "\<succ>" 100) where
  "s \<succ> s' \<equiv> \<triangle> (\<T> s) \<and> \<diamond> s \<and> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s \<and> \<nabla> s \<and> s \<succ>\<^sub>x s' \<and> \<B>\<^sub>i s' = \<B>\<^sub>i s \<and> \<U>\<^sub>c s' = \<U>\<^sub>c s"

abbreviation succ_rel :: "('i,'a) state rel" where
  "succ_rel \<equiv> {(s, s'). s \<succ> s'}"

abbreviation succ_rel_trancl :: "('i,'a) state \<Rightarrow> ('i,'a) state \<Rightarrow> bool" (infixl "\<succ>\<^sup>+" 100) where
  "s \<succ>\<^sup>+ s' \<equiv> (s, s') \<in> succ_rel\<^sup>+"

abbreviation succ_rel_rtrancl :: "('i,'a) state \<Rightarrow> ('i,'a) state \<Rightarrow> bool" (infixl "\<succ>\<^sup>*" 100) where
  "s \<succ>\<^sup>* s' \<equiv> (s, s') \<in> succ_rel\<^sup>*"

lemma succ_vars:
  assumes "s \<succ> s'"
  obtains x\<^sub>i x\<^sub>j where
    "x\<^sub>i \<in> lvars (\<T> s)"
    "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i" "x\<^sub>j \<in> rvars (\<T> s)"
    "lvars (\<T> s') = lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
    "rvars (\<T> s') = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
proof-
  from assms
  obtain x\<^sub>i x\<^sub>j c
    where *:
      "\<triangle> (\<T> s)" "\<nabla> s"
      "min_lvar_not_in_bounds s = Some x\<^sub>i"
      "min_rvar_incdec Positive s x\<^sub>i = Inr x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Inr x\<^sub>j"
      "s' = pivot_and_update x\<^sub>i x\<^sub>j c s"
    unfolding gt_state_def
    by (auto split: if_splits)
  then have
    "x\<^sub>i \<in> lvars (\<T> s)"
    "x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)"
    "lvars (\<T> s') =  lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
    "rvars (\<T> s') = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using pivotandupdate_rvars[of s x\<^sub>i x\<^sub>j]
    using pivotandupdate_lvars[of s x\<^sub>i x\<^sub>j]
    by auto
  moreover
  have "x\<^sub>j \<in> rvars (\<T> s)"
    using \<open>x\<^sub>i \<in> lvars (\<T> s)\<close>
    using \<open>x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)\<close>
    using eq_for_lvar[of x\<^sub>i "\<T> s"]
    unfolding rvars_def
    by auto
  ultimately
  have
    "x\<^sub>i \<in> lvars (\<T> s)"
    "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i" "x\<^sub>j \<in> rvars (\<T> s)"
    "lvars (\<T> s') = lvars (\<T> s) - {x\<^sub>i} \<union> {x\<^sub>j}"
    "rvars (\<T> s') = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
    by auto
  then show thesis
    ..
qed

lemma succ_vars_id:
  assumes "s \<succ> s'"
  shows "lvars (\<T> s) \<union> rvars (\<T> s) =
         lvars (\<T> s') \<union> rvars (\<T> s')"
  using assms
  by (rule succ_vars) auto

lemma succ_inv:
  assumes "s \<succ> s'"
  shows "\<triangle> (\<T> s')" "\<nabla> s'" "\<diamond> s'" "\<B>\<^sub>i s = \<B>\<^sub>i s'"
    "(v::'a valuation) \<Turnstile>\<^sub>t (\<T> s) \<longleftrightarrow> v \<Turnstile>\<^sub>t (\<T> s')"
proof-
  from assms obtain x\<^sub>i x\<^sub>j c
    where *:
      "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s"
      "min_lvar_not_in_bounds s = Some x\<^sub>i"
      "min_rvar_incdec Positive s x\<^sub>i = Inr x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Inr x\<^sub>j"
      "s' = pivot_and_update x\<^sub>i x\<^sub>j c s"
    unfolding gt_state_def
    by (auto split: if_splits)
  then show  "\<triangle> (\<T> s')" "\<nabla> s'" "\<diamond> s'" "\<B>\<^sub>i s = \<B>\<^sub>i s'"
    "(v::'a valuation) \<Turnstile>\<^sub>t (\<T> s) \<longleftrightarrow> v \<Turnstile>\<^sub>t (\<T> s')"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using pivotandupdate_tableau_normalized[of s x\<^sub>i x\<^sub>j c]
    using pivotandupdate_bounds_consistent[of s x\<^sub>i x\<^sub>j c]
    using pivotandupdate_bounds_id[of s x\<^sub>i x\<^sub>j c]
    using pivotandupdate_tableau_equiv
    using pivotandupdate_tableau_valuated
    by auto
qed

lemma succ_rvar_valuation_id:
  assumes "s \<succ> s'" "x \<in> rvars (\<T> s)" "x \<in> rvars (\<T> s')"
  shows "\<langle>\<V> s\<rangle> x = \<langle>\<V> s'\<rangle> x"
proof-
  from assms obtain x\<^sub>i x\<^sub>j c
    where *:
      "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s"
      "min_lvar_not_in_bounds s = Some x\<^sub>i"
      "min_rvar_incdec Positive s x\<^sub>i = Inr x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Inr x\<^sub>j"
      "s' = pivot_and_update x\<^sub>i x\<^sub>j c s"
    unfolding gt_state_def
    by (auto split: if_splits)
  then show ?thesis
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using \<open>x \<in> rvars (\<T> s)\<close> \<open>x \<in> rvars (\<T> s')\<close>
    using pivotandupdate_rvars[of s x\<^sub>i x\<^sub>j c]
    using pivotandupdate_valuation_xi[of s x\<^sub>i x\<^sub>j c]
    using pivotandupdate_valuation_other_nolhs[of s x\<^sub>i x\<^sub>j x c]
    by (force simp add: normalized_tableau_def map2fun_def)
qed

lemma succ_min_lvar_not_in_bounds:
  assumes "s \<succ> s'"
    "xr \<in> lvars (\<T> s)" "xr \<in> rvars (\<T> s')"
  shows "\<not> in_bounds xr (\<langle>\<V> s\<rangle>) (\<B> s)"
    "\<forall> x \<in> lvars (\<T> s). x < xr \<longrightarrow> in_bounds x (\<langle>\<V> s\<rangle>) (\<B> s)"
proof-
  from assms obtain x\<^sub>i x\<^sub>j c
    where *:
      "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s"
      "min_lvar_not_in_bounds s = Some x\<^sub>i"
      "min_rvar_incdec Positive s x\<^sub>i = Inr x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Inr x\<^sub>j"
      "s' = pivot_and_update x\<^sub>i x\<^sub>j c s"
    unfolding gt_state_def
    by (auto split: if_splits)
  then have "x\<^sub>i = xr"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using \<open>xr \<in> lvars (\<T> s)\<close> \<open>xr \<in> rvars (\<T> s')\<close>
    using pivotandupdate_rvars
    by (auto simp add: normalized_tableau_def)
  then show "\<not> in_bounds xr (\<langle>\<V> s\<rangle>) (\<B> s)"
    "\<forall> x \<in> lvars (\<T> s). x < xr \<longrightarrow> in_bounds x (\<langle>\<V> s\<rangle>) (\<B> s)"
    using \<open>min_lvar_not_in_bounds s = Some x\<^sub>i\<close>
    using min_lvar_not_in_bounds_Some min_lvar_not_in_bounds_Some_min
    by simp_all
qed

lemma succ_min_rvar:
  assumes "s \<succ> s'"
    "xs \<in> lvars (\<T> s)" "xs \<in> rvars (\<T> s')"
    "xr \<in> rvars (\<T> s)" "xr \<in> lvars (\<T> s')"
    "eq = eq_for_lvar (\<T> s) xs" and
    dir: "dir = Positive \<or> dir = Negative"
  shows
    "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> xs) (LB dir s xs) \<longrightarrow>
             reasable_var dir xr eq s \<and> (\<forall> x \<in> rvars_eq eq. x < xr \<longrightarrow> \<not> reasable_var dir x eq s)"
proof-
  from assms(1) obtain x\<^sub>i x\<^sub>j c
    where"\<triangle> (\<T> s) \<and> \<nabla> s \<and> \<diamond> s \<and> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"
      "gt_state' (if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive else Negative) s s' x\<^sub>i x\<^sub>j c"
    by (auto simp add: gt_state_def Let_def)
  then have
    "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "s' = pivot_and_update x\<^sub>i x\<^sub>j c s" and
    *: "(\<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i \<and> min_rvar_incdec Positive s x\<^sub>i = Inr x\<^sub>j) \<or>
        (\<not> \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i \<and> min_rvar_incdec Negative s x\<^sub>i = Inr x\<^sub>j)"
    by (auto split: if_splits)

  then have "xr = x\<^sub>j" "xs = x\<^sub>i"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using \<open>xr \<in> rvars (\<T> s)\<close> \<open>xr \<in> lvars (\<T> s')\<close>
    using \<open>xs \<in> lvars (\<T> s)\<close> \<open>xs \<in> rvars (\<T> s')\<close>
    using pivotandupdate_lvars pivotandupdate_rvars
    by (auto simp add: normalized_tableau_def)
  show "\<not> (\<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> xs) (LB dir s xs)) \<longrightarrow>
            reasable_var dir xr eq s \<and> (\<forall> x \<in> rvars_eq eq. x < xr \<longrightarrow> \<not> reasable_var dir x eq s)"
  proof
    assume "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> xs) (LB dir s xs)"
    then have "\<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> xs) (LB dir s xs)"
      using dir
      by (cases "LB dir s xs") (auto simp add: bound_compare_defs)
    moreover
    then have "\<not> (\<rhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> xs) (UB dir s xs))"
      using \<open>\<diamond> s\<close> dir
      using bounds_consistent_gt_ub bounds_consistent_lt_lb
      by (force simp add:  bound_compare''_defs)
    ultimately
    have "min_rvar_incdec dir s xs = Inr xr"
      using * \<open>xr = x\<^sub>j\<close> \<open>xs = x\<^sub>i\<close> dir
      by (auto simp add: bound_compare''_defs)
    then show "reasable_var dir xr eq s \<and> (\<forall> x \<in> rvars_eq eq. x < xr \<longrightarrow> \<not> reasable_var dir x eq s)"
      using \<open>eq = eq_for_lvar (\<T> s) xs\<close>
      using min_rvar_incdec_eq_Some_min[of dir s eq xr]
      using min_rvar_incdec_eq_Some_incdec[of dir s eq xr]
      by simp
  qed
qed

lemma succ_set_on_bound:
  assumes
    "s \<succ> s'" "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>i \<in> rvars (\<T> s')" and
    dir: "dir = Positive \<or> dir = Negative"
  shows
    "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i) \<longrightarrow> \<langle>\<V> s'\<rangle> x\<^sub>i = the (LB dir s x\<^sub>i)"
    "\<langle>\<V> s'\<rangle> x\<^sub>i = the (\<B>\<^sub>l s x\<^sub>i) \<or> \<langle>\<V> s'\<rangle> x\<^sub>i = the (\<B>\<^sub>u s x\<^sub>i)"
proof-
  from assms(1) obtain x\<^sub>i' x\<^sub>j c
    where"\<triangle> (\<T> s) \<and> \<nabla> s \<and> \<diamond> s \<and> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"
      "gt_state' (if \<langle>\<V> s\<rangle> x\<^sub>i' <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i' then Positive else Negative) s s' x\<^sub>i' x\<^sub>j c"
    by (auto simp add: gt_state_def Let_def)
  then have
    "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i'"
    "s' = pivot_and_update x\<^sub>i' x\<^sub>j c s" and
    *: "(\<langle>\<V> s\<rangle> x\<^sub>i' <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i' \<and> c = the (\<B>\<^sub>l s x\<^sub>i') \<and> min_rvar_incdec Positive s x\<^sub>i' = Inr x\<^sub>j) \<or>
        (\<not> \<langle>\<V> s\<rangle> x\<^sub>i' <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i' \<and> c = the (\<B>\<^sub>u s x\<^sub>i') \<and> min_rvar_incdec Negative s x\<^sub>i' = Inr x\<^sub>j)"
    by (auto split: if_splits)
  then have "x\<^sub>i = x\<^sub>i'" "x\<^sub>i' \<in> lvars (\<T> s)"
    "x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i')"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i']
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i'" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i'" x\<^sub>j]
    using \<open>x\<^sub>i \<in> lvars (\<T> s)\<close> \<open>x\<^sub>i \<in> rvars (\<T> s')\<close>
    using pivotandupdate_rvars
    by (auto simp add: normalized_tableau_def)
  show "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i) \<longrightarrow> \<langle>\<V> s'\<rangle> x\<^sub>i = the (LB dir s x\<^sub>i)"
  proof
    assume "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i)"
    then have "\<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i)"
      using dir
      by (cases "LB dir s x\<^sub>i") (auto simp add: bound_compare_defs)
    moreover
    then have "\<not> \<rhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (UB dir s x\<^sub>i)"
      using \<open>\<diamond> s\<close> dir
      using bounds_consistent_gt_ub bounds_consistent_lt_lb
      by (force simp add: bound_compare''_defs)
    ultimately
    show "\<langle>\<V> s'\<rangle> x\<^sub>i = the (LB dir s x\<^sub>i)"
      using * \<open>x\<^sub>i = x\<^sub>i'\<close> \<open>s' = pivot_and_update x\<^sub>i' x\<^sub>j c s\<close>
      using \<open>\<triangle> (\<T> s)\<close> \<open>\<nabla> s\<close> \<open>x\<^sub>i' \<in> lvars (\<T> s)\<close>
        \<open>x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i')\<close>
      using pivotandupdate_valuation_xi[of s x\<^sub>i x\<^sub>j c] dir
      by (case_tac[!] "\<B>\<^sub>l s x\<^sub>i'", case_tac[!] "\<B>\<^sub>u s x\<^sub>i'") (auto simp add: bound_compare_defs map2fun_def)
  qed

  have "\<not> \<langle>\<V> s\<rangle> x\<^sub>i' <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i'  \<longrightarrow> \<langle>\<V> s\<rangle> x\<^sub>i' >\<^sub>u\<^sub>b \<B>\<^sub>u s x\<^sub>i'"
    using \<open>min_lvar_not_in_bounds s = Some x\<^sub>i'\<close>
    using min_lvar_not_in_bounds_Some[of s x\<^sub>i']
    using not_in_bounds[of x\<^sub>i' "\<langle>\<V> s\<rangle>" "\<B>\<^sub>l s" "\<B>\<^sub>u s"]
    by auto
  then show "\<langle>\<V> s'\<rangle> x\<^sub>i = the (\<B>\<^sub>l s x\<^sub>i) \<or> \<langle>\<V> s'\<rangle> x\<^sub>i = the (\<B>\<^sub>u s x\<^sub>i)"
    using \<open>\<triangle> (\<T> s)\<close> \<open>\<nabla> s\<close> \<open>x\<^sub>i' \<in> lvars (\<T> s)\<close>
      \<open>x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i')\<close>
    using \<open>s' = pivot_and_update x\<^sub>i' x\<^sub>j c s\<close> \<open>x\<^sub>i = x\<^sub>i'\<close>
    using pivotandupdate_valuation_xi[of s x\<^sub>i x\<^sub>j c]
    using *
    by (case_tac[!] "\<B>\<^sub>l s x\<^sub>i'", case_tac[!] "\<B>\<^sub>u s x\<^sub>i'") (auto simp add: map2fun_def bound_compare_defs)
qed

lemma succ_rvar_valuation:
  assumes
    "s \<succ> s'" "x \<in> rvars (\<T> s')"
  shows
    "\<langle>\<V> s'\<rangle> x = \<langle>\<V> s\<rangle> x \<or> \<langle>\<V> s'\<rangle> x = the (\<B>\<^sub>l s x) \<or> \<langle>\<V> s'\<rangle> x = the (\<B>\<^sub>u s x)"
proof-
  from assms
  obtain x\<^sub>i x\<^sub>j b where
    "\<triangle> (\<T> s)" "\<nabla> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "min_rvar_incdec Positive s x\<^sub>i = Inr x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Inr x\<^sub>j"
    "b = the (\<B>\<^sub>l s x\<^sub>i) \<or> b = the (\<B>\<^sub>u s x\<^sub>i)"
    "s' = pivot_and_update x\<^sub>i x\<^sub>j b s"
    unfolding gt_state_def
    by (auto simp add: Let_def split: if_splits)
  then have
    "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>i \<notin> rvars (\<T> s)"
    "x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)"
    "x\<^sub>j \<in> rvars (\<T> s)" "x\<^sub>j \<notin> lvars (\<T> s)" "x\<^sub>i \<noteq> x\<^sub>j"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using rvars_of_lvar_rvars \<open>\<triangle> (\<T> s)\<close>
    by (auto simp add: normalized_tableau_def)
  then have
    "rvars (\<T> s') = rvars (\<T> s) - {x\<^sub>j} \<union> {x\<^sub>i}"
    "x \<in> rvars (\<T> s) \<or> x = x\<^sub>i" "x \<noteq> x\<^sub>j" "x \<noteq> x\<^sub>i \<longrightarrow> x \<notin> lvars (\<T> s)"
    using \<open>x \<in> rvars (\<T> s')\<close>
    using pivotandupdate_rvars[of s x\<^sub>i x\<^sub>j]
    using \<open>\<triangle> (\<T> s)\<close> \<open>\<nabla> s\<close> \<open>s' = pivot_and_update x\<^sub>i x\<^sub>j b s\<close>
    by (auto simp add: normalized_tableau_def)
  then show ?thesis
    using pivotandupdate_valuation_xi[of s x\<^sub>i x\<^sub>j b]
    using pivotandupdate_valuation_other_nolhs[of s x\<^sub>i x\<^sub>j x b]
    using \<open>x\<^sub>i \<in> lvars (\<T> s)\<close> \<open>x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)\<close>
    using \<open>\<triangle> (\<T> s)\<close> \<open>\<nabla> s\<close> \<open>s' = pivot_and_update x\<^sub>i x\<^sub>j b s\<close> \<open>b = the (\<B>\<^sub>l s x\<^sub>i) \<or> b = the (\<B>\<^sub>u s x\<^sub>i)\<close>
    by (auto simp add: map2fun_def)
qed

lemma succ_no_vars_valuation:
  assumes
    "s \<succ> s'" "x \<notin> tvars (\<T> s')"
  shows "look (\<V> s') x = look (\<V> s) x"
proof-
  from assms
  obtain x\<^sub>i x\<^sub>j b where
    "\<triangle> (\<T> s)" "\<nabla> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "min_rvar_incdec Positive s x\<^sub>i = Inr x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Inr x\<^sub>j"
    "b = the (\<B>\<^sub>l s x\<^sub>i) \<or> b = the (\<B>\<^sub>u s x\<^sub>i)"
    "s' = pivot_and_update x\<^sub>i x\<^sub>j b s"
    unfolding gt_state_def
    by (auto simp add: Let_def split: if_splits)
  then have
    "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>i \<notin> rvars (\<T> s)"
    "x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)"
    "x\<^sub>j \<in> rvars (\<T> s)" "x\<^sub>j \<notin> lvars (\<T> s)" "x\<^sub>i \<noteq> x\<^sub>j"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using rvars_of_lvar_rvars \<open>\<triangle> (\<T> s)\<close>
    by (auto simp add: normalized_tableau_def)
  then show ?thesis
    using pivotandupdate_valuation_other_nolhs[of s x\<^sub>i x\<^sub>j x b]
    using \<open>\<triangle> (\<T> s)\<close> \<open>\<nabla> s\<close> \<open>s' = pivot_and_update x\<^sub>i x\<^sub>j b s\<close>
    using \<open>x \<notin> tvars (\<T> s')\<close>
    using pivotandupdate_rvars[of s x\<^sub>i x\<^sub>j]
    using pivotandupdate_lvars[of s x\<^sub>i x\<^sub>j]
    by (auto simp add: map2fun_def)
qed

lemma succ_valuation_satisfies:
  assumes "s \<succ> s'" "\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s"
  shows "\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>t \<T> s'"
proof-
  from \<open>s \<succ> s'\<close>
  obtain x\<^sub>i x\<^sub>j b where
    "\<triangle> (\<T> s)" "\<nabla> s"
    "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "min_rvar_incdec Positive s x\<^sub>i = Inr x\<^sub>j \<or> min_rvar_incdec Negative s x\<^sub>i = Inr x\<^sub>j"
    "b = the (\<B>\<^sub>l s x\<^sub>i) \<or> b = the (\<B>\<^sub>u s x\<^sub>i)"
    "s' = pivot_and_update x\<^sub>i x\<^sub>j b s"
    unfolding gt_state_def
    by (auto simp add: Let_def split: if_splits)
  then have
    "x\<^sub>i \<in> lvars (\<T> s)"
    "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i"
    using min_lvar_not_in_bounds_lvars[of s x\<^sub>i]
    using min_rvar_incdec_eq_Some_rvars[of Positive s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using min_rvar_incdec_eq_Some_rvars[of Negative s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j] \<open>\<triangle> (\<T> s)\<close>
    by (auto simp add: normalized_tableau_def)
  then show ?thesis
    using pivotandupdate_satisfies_tableau[of s x\<^sub>i x\<^sub>j b]
    using pivotandupdate_tableau_equiv[of s x\<^sub>i x\<^sub>j ]
    using \<open>\<triangle> (\<T> s)\<close> \<open>\<nabla> s\<close> \<open>\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s\<close> \<open>s' = pivot_and_update x\<^sub>i x\<^sub>j b s\<close>
    by auto
qed

lemma succ_tableau_valuated:
  assumes "s \<succ> s'" "\<nabla> s"
  shows "\<nabla> s'"
  using succ_inv(2) assms by blast

(* -------------------------------------------------------------------------- *)
abbreviation succ_chain where
  "succ_chain l \<equiv> rel_chain l succ_rel"

lemma succ_chain_induct:
  assumes *: "succ_chain l" "i \<le> j" "j < length l"
  assumes base: "\<And> i. P i i"
  assumes step: "\<And> i. l ! i \<succ> (l ! (i + 1)) \<Longrightarrow> P i (i + 1)"
  assumes trans: "\<And> i j k. \<lbrakk>P i j; P j k; i < j; j \<le> k\<rbrakk> \<Longrightarrow> P i k"
  shows "P i j"
  using *
proof (induct "j - i" arbitrary: i)
  case 0
  then show ?case
    by (simp add: base)
next
  case (Suc k)
  have "P (i + 1) j"
    using Suc(1)[of "i + 1"] Suc(2) Suc(3) Suc(4) Suc(5)
    by auto
  moreover
  have "P i (i + 1)"
  proof (rule step)
    show "l ! i \<succ> (l ! (i + 1))"
      using Suc(2) Suc(3) Suc(5)
      unfolding rel_chain_def
      by auto
  qed
  ultimately
  show ?case
    using trans[of i "i + 1" j] Suc(2)
    by simp
qed

lemma succ_chain_bounds_id:
  assumes "succ_chain l" "i \<le> j" "j < length l"
  shows "\<B>\<^sub>i (l ! i) = \<B>\<^sub>i (l ! j)"
  using assms
proof (rule succ_chain_induct)
  fix i
  assume "l ! i \<succ> (l ! (i + 1))"
  then show "\<B>\<^sub>i (l ! i) = \<B>\<^sub>i (l ! (i + 1))"
    by (rule succ_inv(4))
qed simp_all

lemma succ_chain_vars_id':
  assumes "succ_chain l" "i \<le> j" "j < length l"
  shows "lvars (\<T> (l ! i)) \<union> rvars (\<T> (l ! i)) =
         lvars (\<T> (l ! j)) \<union> rvars (\<T> (l ! j))"
  using assms
proof (rule succ_chain_induct)
  fix i
  assume "l ! i \<succ> (l ! (i + 1))"
  then show "tvars (\<T> (l ! i)) = tvars (\<T> (l ! (i + 1)))"
    by (rule succ_vars_id)
qed simp_all

lemma succ_chain_vars_id:
  assumes "succ_chain l" "i < length l" "j < length l"
  shows "lvars (\<T> (l ! i)) \<union> rvars (\<T> (l ! i)) =
         lvars (\<T> (l ! j)) \<union> rvars (\<T> (l ! j))"
proof (cases "i \<le> j")
  case True
  then show ?thesis
    using assms succ_chain_vars_id'[of l i j]
    by simp
next
  case False
  then have "j \<le> i"
    by simp
  then show ?thesis
    using assms succ_chain_vars_id'[of l j i]
    by simp
qed

lemma succ_chain_tableau_equiv':
  assumes "succ_chain l" "i \<le> j" "j < length l"
  shows "(v::'a valuation) \<Turnstile>\<^sub>t \<T> (l ! i) \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> (l ! j)"
  using assms
proof (rule succ_chain_induct)
  fix i
  assume "l ! i \<succ> (l ! (i + 1))"
  then show "v \<Turnstile>\<^sub>t \<T> (l ! i) = v \<Turnstile>\<^sub>t \<T> (l ! (i + 1))"
    by (rule succ_inv(5))
qed simp_all

lemma succ_chain_tableau_equiv:
  assumes "succ_chain l"  "i < length l" "j < length l"
  shows "(v::'a valuation) \<Turnstile>\<^sub>t \<T> (l ! i) \<longleftrightarrow> v \<Turnstile>\<^sub>t \<T> (l ! j)"
proof (cases "i \<le> j")
  case True
  then show ?thesis
    using assms succ_chain_tableau_equiv'[of l i j v]
    by simp
next
  case False
  then have "j \<le> i"
    by auto
  then show ?thesis
    using assms succ_chain_tableau_equiv'[of l j i v]
    by simp
qed

lemma succ_chain_no_vars_valuation:
  assumes "succ_chain l"  "i \<le> j" "j < length l"
  shows "\<forall> x. x \<notin> tvars (\<T> (l ! i)) \<longrightarrow> look (\<V> (l ! i)) x = look (\<V> (l ! j)) x" (is "?P i j")
  using assms
proof (induct "j - i" arbitrary: i)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have "?P (i + 1) j"
    using Suc(1)[of "i + 1"] Suc(2) Suc(3) Suc(4) Suc(5)
    by auto
  moreover
  have "?P (i + 1) i"
  proof (rule+, rule succ_no_vars_valuation)
    show "l ! i \<succ> (l ! (i + 1))"
      using Suc(2) Suc(3) Suc(5)
      unfolding rel_chain_def
      by auto
  qed
  moreover
  have "tvars (\<T> (l ! i)) = tvars (\<T> (l ! (i + 1)))"
  proof (rule succ_vars_id)
    show "l ! i \<succ> (l ! (i + 1))"
      using Suc(2) Suc(3) Suc(5)
      unfolding rel_chain_def
      by simp
  qed
  ultimately
  show ?case
    by simp
qed

lemma succ_chain_rvar_valuation:
  assumes "succ_chain l" "i \<le> j" "j < length l"
  shows "\<forall>x\<in>rvars (\<T> (l ! j)).
  \<langle>\<V> (l ! j)\<rangle> x = \<langle>\<V> (l ! i)\<rangle> x \<or>
  \<langle>\<V> (l ! j)\<rangle> x = the (\<B>\<^sub>l (l ! i) x) \<or>
  \<langle>\<V> (l ! j)\<rangle> x = the (\<B>\<^sub>u (l ! i) x)" (is "?P i j")
  using assms
proof (induct "j - i" arbitrary: j)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have  "k = j - 1 - i" "succ_chain l" "i \<le> j - 1" "j - 1 < length l" "j > 0"
    using Suc(2) Suc(3) Suc(4) Suc(5)
    by auto
  then have ji: "?P i (j - 1)"
    using Suc(1)
    by simp

  have "l ! (j - 1) \<succ> (l ! j)"
    using Suc(3) \<open>j < length l\<close> \<open>j > 0\<close>
    unfolding rel_chain_def
    by (erule_tac x="j - 1" in allE) simp

  then have
    jj: "?P (j - 1) j"
    using succ_rvar_valuation
    by auto

  obtain x\<^sub>i x\<^sub>j where
    vars: "x\<^sub>i \<in> lvars (\<T> (l ! (j - 1)))" "x\<^sub>j \<in> rvars (\<T> (l ! (j - 1)))"
    "rvars (\<T> (l ! j)) = rvars (\<T> (l ! (j - 1))) - {x\<^sub>j} \<union> {x\<^sub>i}"
    using \<open>l ! (j - 1) \<succ> (l ! j)\<close>
    by (rule succ_vars) simp

  then have bounds:
    "\<B>\<^sub>l (l ! (j - 1)) = \<B>\<^sub>l (l ! i)" "\<B>\<^sub>l (l ! j) = \<B>\<^sub>l (l ! i)"
    "\<B>\<^sub>u (l ! (j - 1)) = \<B>\<^sub>u (l ! i)" "\<B>\<^sub>u (l ! j) = \<B>\<^sub>u (l ! i)"
    using \<open>succ_chain l\<close>
    using succ_chain_bounds_id[of l i "j - 1", THEN sym] \<open>j - 1 < length l\<close> \<open>i \<le> j - 1\<close>
    using succ_chain_bounds_id[of l "j - 1" j, THEN sym] \<open>j < length l\<close>
    by (auto simp: indexl_def indexu_def boundsl_def boundsu_def)
  show ?case
  proof
    fix x
    assume "x \<in> rvars (\<T> (l ! j))"
    then have "x \<noteq> x\<^sub>j \<and> x \<in> rvars (\<T> (l ! (j - 1))) \<or> x = x\<^sub>i"
      using vars
      by auto
    then show "\<langle>\<V> (l ! j)\<rangle> x = \<langle>\<V> (l ! i)\<rangle> x \<or>
          \<langle>\<V> (l ! j)\<rangle> x = the (\<B>\<^sub>l (l ! i) x) \<or>
          \<langle>\<V> (l ! j)\<rangle> x = the (\<B>\<^sub>u (l ! i) x)"
    proof
      assume "x \<noteq> x\<^sub>j \<and> x \<in> rvars (\<T> (l ! (j - 1)))"
      then show ?thesis
        using jj \<open>x \<in> rvars (\<T> (l ! j))\<close> ji
        using bounds
        by force
    next
      assume "x = x\<^sub>i"
      then show ?thesis
        using succ_set_on_bound(2)[of "l ! (j - 1)" "l ! j" x\<^sub>i] \<open>l ! (j - 1) \<succ> (l ! j)\<close>
        using vars bounds
        by auto
    qed
  qed
qed

lemma succ_chain_valuation_satisfies:
  assumes "succ_chain l"  "i \<le> j" "j < length l"
  shows "\<langle>\<V> (l ! i)\<rangle> \<Turnstile>\<^sub>t \<T> (l ! i) \<longrightarrow> \<langle>\<V> (l ! j)\<rangle> \<Turnstile>\<^sub>t \<T> (l ! j)"
  using assms
proof (rule succ_chain_induct)
  fix i
  assume "l ! i \<succ> (l ! (i + 1))"
  then show "\<langle>\<V> (l ! i)\<rangle> \<Turnstile>\<^sub>t \<T> (l ! i) \<longrightarrow> \<langle>\<V> (l ! (i + 1))\<rangle> \<Turnstile>\<^sub>t \<T> (l ! (i + 1))"
    using succ_valuation_satisfies
    by auto
qed simp_all

lemma succ_chain_tableau_valuated:
  assumes "succ_chain l"  "i \<le> j" "j < length l"
  shows "\<nabla> (l ! i) \<longrightarrow> \<nabla> (l ! j)"
  using assms
proof(rule succ_chain_induct)
  fix i
  assume "l ! i \<succ> (l ! (i + 1))"
  then show "\<nabla> (l ! i) \<longrightarrow> \<nabla> (l ! (i + 1))"
    using succ_tableau_valuated
    by auto
qed simp_all

abbreviation swap_lr where
  "swap_lr l i x \<equiv> i + 1 < length l \<and> x \<in> lvars (\<T> (l ! i)) \<and> x \<in> rvars (\<T> (l ! (i + 1)))"

abbreviation swap_rl where
  "swap_rl l i x \<equiv> i + 1 < length l \<and> x \<in> rvars (\<T> (l ! i)) \<and> x \<in> lvars (\<T> (l ! (i + 1)))"

abbreviation always_r where
  "always_r l i j x \<equiv> \<forall> k. i \<le> k \<and> k \<le> j \<longrightarrow> x \<in> rvars (\<T> (l ! k))"

lemma succ_chain_always_r_valuation_id:
  assumes "succ_chain l" "i \<le> j" "j < length l"
  shows "always_r l i j x \<longrightarrow> \<langle>\<V> (l ! i)\<rangle> x = \<langle>\<V> (l ! j)\<rangle> x" (is "?P i j")
  using assms
proof (rule succ_chain_induct)
  fix i
  assume "l ! i \<succ> (l ! (i + 1))"
  then show "?P i (i + 1)"
    using succ_rvar_valuation_id
    by simp
qed simp_all

lemma succ_chain_swap_rl_exists:
  assumes "succ_chain l" "i < j" "j < length l"
    "x \<in> rvars (\<T> (l ! i))" "x \<in> lvars (\<T> (l ! j))"
  shows "\<exists> k. i \<le> k \<and> k < j \<and> swap_rl l k x"
  using assms
proof (induct "j - i" arbitrary: i)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have "l ! i \<succ> (l ! (i + 1))"
    using Suc(3) Suc(4) Suc(5)
    unfolding rel_chain_def
    by auto
  then have "\<triangle> (\<T> (l ! (i + 1)))"
    by (rule succ_inv)

  show ?case
  proof (cases "x \<in> rvars (\<T> (l ! (i + 1)))")
    case True
    then have "j \<noteq> i + 1"
      using Suc(7) \<open>\<triangle> (\<T> (l ! (i + 1)))\<close>
      by (auto simp add: normalized_tableau_def)
    have "k = j - Suc i"
      using Suc(2)
      by simp
    then obtain k where "k \<ge> i + 1" "k < j" "swap_rl l k x"
      using \<open>x \<in> rvars (\<T> (l ! (i + 1)))\<close> \<open>j \<noteq> i + 1\<close>
      using Suc(1)[of "i + 1"] Suc(2) Suc(3) Suc(4) Suc(5) Suc(6) Suc(7)
      by auto
    then show ?thesis
      by (rule_tac x="k" in exI) simp
  next
    case False
    then have "x \<in> lvars (\<T> (l ! (i + 1)))"
      using Suc(6)
      using \<open>l ! i \<succ> (l ! (i + 1))\<close> succ_vars_id
      by auto
    then show ?thesis
      using Suc(4) Suc(5) Suc(6)
      by force
  qed
qed

lemma succ_chain_swap_lr_exists:
  assumes "succ_chain l" "i < j" "j < length l"
    "x \<in> lvars (\<T> (l ! i))" "x \<in> rvars (\<T> (l ! j))"
  shows "\<exists> k. i \<le> k \<and> k < j \<and> swap_lr l k x"
  using assms
proof (induct "j - i" arbitrary: i)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have "l ! i \<succ> (l ! (i + 1))"
    using Suc(3) Suc(4) Suc(5)
    unfolding rel_chain_def
    by auto
  then have "\<triangle> (\<T> (l ! (i + 1)))"
    by (rule succ_inv)

  show ?case
  proof (cases "x \<in> lvars (\<T> (l ! (i + 1)))")
    case True
    then have "j \<noteq> i + 1"
      using Suc(7) \<open>\<triangle> (\<T> (l ! (i + 1)))\<close>
      by (auto simp add: normalized_tableau_def)
    have "k = j - Suc i"
      using Suc(2)
      by simp
    then obtain k where "k \<ge> i + 1" "k < j" "swap_lr l k x"
      using \<open>x \<in> lvars (\<T> (l ! (i + 1)))\<close> \<open>j \<noteq> i + 1\<close>
      using Suc(1)[of "i + 1"] Suc(2) Suc(3) Suc(4) Suc(5) Suc(6) Suc(7)
      by auto
    then show ?thesis
      by (rule_tac x="k" in exI) simp
  next
    case False
    then have "x \<in> rvars (\<T> (l ! (i + 1)))"
      using Suc(6)
      using \<open>l ! i \<succ> (l ! (i + 1))\<close> succ_vars_id
      by auto
    then show ?thesis
      using Suc(4) Suc(5) Suc(6)
      by force
  qed
qed

(* -------------------------------------------------------------------------- *)

lemma finite_tableaus_aux:
  shows "finite {t. lvars t = L \<and> rvars t = V - L \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t t0)}" (is "finite (?Al L)")
proof (cases "?Al L = {}")
  case True
  show ?thesis
    by (subst True) simp
next
  case False
  then have "\<exists> t. t \<in> ?Al L"
    by auto
  let ?t = "SOME t. t \<in> ?Al L"
  have "?t \<in> ?Al L"
    using \<open>\<exists> t. t \<in> ?Al L\<close>
    by (rule someI_ex)
  have "?Al L \<subseteq> {t. t <~~> ?t}"
  proof
    fix x
    assume "x \<in> ?Al L"
    have "x <~~> ?t"
      apply (rule tableau_perm)
      using \<open>?t \<in> ?Al L\<close> \<open>x \<in> ?Al L\<close>
      by auto
    then show "x \<in> {t. t <~~> ?t}"
      by simp
  qed
  moreover
  have "finite {t. t <~~> ?t}"
    by (rule perm_finite)
  ultimately
  show ?thesis
    by (rule finite_subset)
qed

lemma finite_tableaus:
  assumes "finite V"
  shows "finite {t. tvars t = V \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t t0)}" (is "finite ?A")
proof-
  let ?Al = "\<lambda> L. {t. lvars t = L \<and> rvars t = V - L \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t t0)}"
  have "?A = \<Union> (?Al ` {L. L \<subseteq> V})"
    by (auto simp add: normalized_tableau_def)
  then show ?thesis
    using \<open>finite V\<close>
    using finite_tableaus_aux
    by auto
qed

lemma finite_accessible_tableaus:
  shows "finite (\<T> ` {s'. s \<succ>\<^sup>* s'})"
proof-
  have "{s'. s \<succ>\<^sup>* s'} = {s'. s \<succ>\<^sup>+ s'} \<union> {s}"
    by (auto simp add: rtrancl_eq_or_trancl)
  moreover
  have "finite (\<T> ` {s'. s \<succ>\<^sup>+ s'})" (is "finite ?A")
  proof-
    let ?T = "{t. tvars t = tvars (\<T> s) \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t(\<T> s))}"
    have "?A \<subseteq> ?T"
    proof
      fix t
      assume "t \<in> ?A"
      then obtain s' where "s \<succ>\<^sup>+ s'" "t = \<T> s'"
        by auto
      then obtain l where *: "l \<noteq> []" "1 < length l" "hd l = s" "last l = s'" "succ_chain l"
        using trancl_rel_chain[of s s' succ_rel]
        by auto
      show "t \<in> ?T"
      proof-
        have "tvars (\<T> s') = tvars (\<T> s)"
          using succ_chain_vars_id[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          by simp
        moreover
        have "\<triangle> (\<T> s')"
          using \<open>s \<succ>\<^sup>+ s'\<close>
          using succ_inv(1)[of _ s']
          by (auto dest: tranclD2)
        moreover
        have "\<forall>v::'a valuation. v \<Turnstile>\<^sub>t \<T> s' = v \<Turnstile>\<^sub>t \<T> s"
          using succ_chain_tableau_equiv[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          by auto
        ultimately
        show ?thesis
          using \<open>t = \<T> s'\<close>
          by simp
      qed
    qed
    moreover
    have "finite (tvars (\<T> s))"
      by (auto simp add: lvars_def rvars_def finite_vars)
    ultimately
    show ?thesis
      using finite_tableaus[of "tvars (\<T> s)" "\<T> s"]
      by (auto simp add: finite_subset)
  qed
  ultimately
  show ?thesis
    by simp
qed

abbreviation check_valuation  where
  "check_valuation (v::'a valuation) v0 bl0 bu0 t0 V \<equiv>
     \<exists> t. tvars t = V \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t t0) \<and> v \<Turnstile>\<^sub>t t \<and>
     (\<forall> x \<in> rvars t. v x = v0 x \<or> v x = bl0 x \<or> v x = bu0 x) \<and>
     (\<forall> x. x \<notin> V \<longrightarrow> v x = v0 x)"

lemma finite_valuations:
  assumes "finite V"
  shows "finite {v::'a valuation. check_valuation v v0 bl0 bu0 t0 V}" (is "finite ?A")
proof-
  let ?Al = "\<lambda> L. {t. lvars t = L \<and> rvars t = V - L \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t t0)}"
  let ?Vt = "\<lambda> t. {v::'a valuation. v \<Turnstile>\<^sub>t t \<and> (\<forall> x \<in> rvars t. v x = v0 x \<or> v x = bl0 x \<or> v x = bu0 x) \<and> (\<forall> x. x \<notin> V \<longrightarrow> v x = v0 x)}"

  have "finite {L. L \<subseteq> V}"
    using \<open>finite V\<close>
    by auto
  have "\<forall> L. L \<subseteq> V \<longrightarrow> finite (?Al L)"
    using finite_tableaus_aux
    by auto
  have "\<forall> L t. L \<subseteq> V \<and> t \<in> ?Al L \<longrightarrow> finite (?Vt  t)"
  proof (safe)
    fix L t
    assume "lvars t \<subseteq> V" "rvars t = V - lvars t" "\<triangle> t" "\<forall>v. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t t0"
    then have "rvars t \<union> lvars t = V"
      by auto

    let ?f = "\<lambda> v x. if x \<in> rvars t then v x else 0"

    have "inj_on ?f (?Vt t)"
      unfolding inj_on_def
    proof (safe, rule ext)
      fix v1 v2 x
      assume "(\<lambda>x. if x \<in> rvars t then v1 x else (0 :: 'a)) =
              (\<lambda>x. if x \<in> rvars t then v2 x else (0 :: 'a))" (is "?f1 = ?f2")
      have "\<forall>x\<in>rvars t. v1 x = v2 x"
      proof
        fix x
        assume "x \<in> rvars t"
        then show "v1 x = v2 x"
          using \<open>?f1 = ?f2\<close> fun_cong[of ?f1 ?f2 x]
          by auto
      qed
      assume *: "v1 \<Turnstile>\<^sub>t t" "v2 \<Turnstile>\<^sub>t t"
        "\<forall>x. x \<notin> V \<longrightarrow> v1 x = v0 x" "\<forall>x. x \<notin> V \<longrightarrow> v2 x = v0 x"
      show "v1 x = v2 x"
      proof (cases "x \<in> lvars t")
        case False
        then show ?thesis
          using * \<open>\<forall>x\<in>rvars t. v1 x = v2 x\<close> \<open>rvars t \<union> lvars t = V\<close>
          by auto
      next
        case True
        let ?eq = "eq_for_lvar t x"
        have "?eq \<in> set t \<and> lhs ?eq = x"
          using eq_for_lvar \<open>x \<in> lvars t\<close>
          by simp
        then have "v1 x = rhs ?eq \<lbrace> v1 \<rbrace>" "v2 x = rhs ?eq \<lbrace> v2 \<rbrace>"
          using \<open>v1 \<Turnstile>\<^sub>t t\<close> \<open>v2 \<Turnstile>\<^sub>t t\<close>
          unfolding satisfies_tableau_def satisfies_eq_def
          by auto
        moreover
        have "rhs ?eq \<lbrace> v1 \<rbrace> = rhs ?eq \<lbrace> v2 \<rbrace>"
          apply (rule valuate_depend)
          using \<open>\<forall>x\<in>rvars t. v1 x = v2 x\<close> \<open>?eq \<in> set t \<and> lhs ?eq = x\<close>
          unfolding rvars_def
          by auto
        ultimately
        show ?thesis
          by simp
      qed
    qed

    let ?R = "{v. \<forall> x. if x \<in> rvars t then v x = v0 x \<or> v x = bl0 x \<or> v x = bu0 x else v x = 0 }"
    have "?f ` (?Vt t) \<subseteq> ?R"
      by auto
    moreover
    have "finite ?R"
    proof-
      have "finite (rvars t)"
        using \<open>finite V\<close> \<open>rvars t \<union> lvars t = V\<close>
        using  finite_subset[of "rvars t" V]
        by auto
      moreover
      let ?R' = "{v. \<forall> x. if x \<in> rvars t then v x \<in> {v0 x, bl0 x, bu0 x} else v x = 0}"
      have "?R = ?R'"
        by auto
      ultimately
      show ?thesis
        using finite_fun_args[of "rvars t" "\<lambda> x. {v0 x,  bl0 x, bu0 x}" "\<lambda> x. 0"]
        by auto
    qed
    ultimately
    have "finite (?f ` (?Vt t))"
      by (simp add: finite_subset)
    then show "finite (?Vt t)"
      using \<open>inj_on ?f (?Vt t)\<close>
      by (auto dest: finite_imageD)
  qed

  have "?A = \<Union> (\<Union> (((`) ?Vt) ` (?Al ` {L. L \<subseteq> V})))" (is "?A = ?A'")
    by (auto simp add: normalized_tableau_def cong del: image_cong_simp)
  moreover
  have "finite ?A'"
  proof (rule finite_Union)
    show "finite (\<Union> (((`) ?Vt) ` (?Al ` {L. L \<subseteq> V})))"
      using \<open>finite {L. L \<subseteq> V}\<close> \<open>\<forall> L. L \<subseteq> V \<longrightarrow> finite (?Al L)\<close>
      by auto
  next
    fix M
    assume "M \<in> \<Union> (((`) ?Vt) ` (?Al ` {L. L \<subseteq> V}))"
    then obtain L t where "L \<subseteq> V" "t \<in> ?Al L" "M = ?Vt t"
      by blast
    then show "finite M"
      using \<open>\<forall> L t. L \<subseteq> V \<and> t \<in> ?Al L \<longrightarrow> finite (?Vt  t)\<close>
      by blast
  qed
  ultimately
  show ?thesis
    by simp
qed


lemma finite_accessible_valuations:
  shows "finite (\<V> ` {s'. s \<succ>\<^sup>* s'})"
proof-
  have "{s'. s \<succ>\<^sup>* s'} = {s'. s \<succ>\<^sup>+ s'} \<union> {s}"
    by (auto simp add: rtrancl_eq_or_trancl)
  moreover
  have "finite (\<V> ` {s'. s \<succ>\<^sup>+ s'})" (is "finite ?A")
  proof-
    let ?P = "\<lambda> v. check_valuation v (\<langle>\<V> s\<rangle>) (\<lambda> x. the (\<B>\<^sub>l s x)) (\<lambda> x. the (\<B>\<^sub>u s x)) (\<T> s) (tvars (\<T> s))"
    let ?P' = "\<lambda> v::(var, 'a) mapping.
         \<exists> t. tvars t = tvars (\<T> s) \<and> \<triangle> t \<and> (\<forall> v::'a valuation. v \<Turnstile>\<^sub>t t = v \<Turnstile>\<^sub>t \<T> s) \<and> \<langle>v\<rangle> \<Turnstile>\<^sub>t t \<and>
    (\<forall> x \<in> rvars t. \<langle>v\<rangle> x = \<langle>\<V> s\<rangle> x \<or>
                       \<langle>v\<rangle> x = the (\<B>\<^sub>l s x) \<or>
                       \<langle>v\<rangle> x = the (\<B>\<^sub>u s x)) \<and>
    (\<forall> x. x \<notin> tvars (\<T> s) \<longrightarrow> look v x = look (\<V> s) x) \<and>
    (\<forall> x. x \<in> tvars (\<T> s) \<longrightarrow> look v x \<noteq> None)"

    have "finite (tvars (\<T> s))"
      by (auto simp add: lvars_def rvars_def finite_vars)
    then have "finite {v. ?P v}"
      using finite_valuations[of "tvars (\<T> s)" "\<T> s" "\<langle>\<V> s\<rangle>" "\<lambda> x. the (\<B>\<^sub>l s x)" "\<lambda> x. the (\<B>\<^sub>u s x)"]
      by auto
    moreover
    have "map2fun ` {v. ?P' v} \<subseteq> {v. ?P v}"
      by (auto simp add: map2fun_def)
    ultimately
    have "finite (map2fun ` {v. ?P' v})"
      by (auto simp add: finite_subset)
    moreover
    have "inj_on map2fun {v. ?P' v}"
      unfolding inj_on_def
    proof (safe)
      fix x y
      assume "\<langle>x\<rangle> = \<langle>y\<rangle>" and *:
        "\<forall>x. x \<notin> Simplex.tvars (\<T> s) \<longrightarrow> look y x = look (\<V> s) x"
        "\<forall>xa. xa \<notin> Simplex.tvars (\<T> s) \<longrightarrow> look x xa = look (\<V> s) xa"
        "\<forall>x. x \<in> Simplex.tvars (\<T> s) \<longrightarrow> look y x \<noteq> None"
        "\<forall>xa. xa \<in> Simplex.tvars (\<T> s) \<longrightarrow> look x xa \<noteq> None"
      show "x = y"
      proof (rule mapping_eqI)
        fix k
        have "\<langle>x\<rangle> k = \<langle>y\<rangle> k"
          using \<open>\<langle>x\<rangle> = \<langle>y\<rangle>\<close>
          by simp
        then show "look x k = look y k"
          using *
          by  (cases "k \<in> tvars (\<T> s)") (auto simp add: map2fun_def split: option.split)
      qed
    qed
    ultimately
    have "finite {v. ?P' v}"
      by (rule finite_imageD)
    moreover
    have "?A \<subseteq> {v. ?P' v}"
    proof (safe)
      fix s'
      assume "s \<succ>\<^sup>+ s'"
      then obtain l where *: "l \<noteq> []" "1 < length l" "hd l = s" "last l = s'" "succ_chain l"
        using trancl_rel_chain[of s s' succ_rel]
        by auto
      show "?P' (\<V> s')"
      proof-
        have "\<nabla> s" "\<triangle> (\<T> s)" "\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s"
          using \<open>s \<succ>\<^sup>+ s'\<close>
          using tranclD[of s s' succ_rel]
          by (auto simp add: curr_val_satisfies_no_lhs_def)
        have "tvars (\<T> s') = tvars (\<T> s)"
          using succ_chain_vars_id[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          by simp
        moreover
        have "\<triangle>(\<T> s')"
          using \<open>s \<succ>\<^sup>+ s'\<close>
          using succ_inv(1)[of _ s']
          by (auto dest: tranclD2)
        moreover
        have "\<forall>v::'a valuation. v \<Turnstile>\<^sub>t \<T> s' = v \<Turnstile>\<^sub>t \<T> s"
          using succ_chain_tableau_equiv[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          by auto
        moreover
        have "\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>t \<T> s'"
          using succ_chain_valuation_satisfies[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l] \<open>\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>t \<T> s\<close>
          by simp
        moreover
        have "\<forall>x\<in>rvars (\<T> s'). \<langle>\<V> s'\<rangle> x = \<langle>\<V> s\<rangle> x \<or> \<langle>\<V> s'\<rangle> x = the (\<B>\<^sub>l s x) \<or> \<langle>\<V> s'\<rangle> x = the (\<B>\<^sub>u s x)"
          using succ_chain_rvar_valuation[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          by auto
        moreover
        have "\<forall>x. x \<notin> tvars (\<T> s) \<longrightarrow> look (\<V> s') x = look (\<V> s) x"
          using succ_chain_no_vars_valuation[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          by auto
        moreover
        have "\<forall>x. x \<in> Simplex.tvars (\<T> s') \<longrightarrow> look (\<V> s') x \<noteq> None"
          using succ_chain_tableau_valuated[of l 0 "length l - 1"]
          using * hd_conv_nth[of l] last_conv_nth[of l]
          using \<open>tvars (\<T> s') = tvars (\<T> s)\<close> \<open>\<nabla> s\<close>
          by (auto simp add: tableau_valuated_def)
        ultimately
        show ?thesis
          by (rule_tac x="\<T> s'" in exI) auto
      qed
    qed
    ultimately
    show ?thesis
      by (auto simp add: finite_subset)
  qed
  ultimately
  show ?thesis
    by simp
qed

lemma accessible_bounds:
  shows "\<B>\<^sub>i ` {s'. s \<succ>\<^sup>* s'} = {\<B>\<^sub>i s}"
proof -
  have "s \<succ>\<^sup>* s' \<Longrightarrow> \<B>\<^sub>i s' = \<B>\<^sub>i s" for s'
    by (induct s s' rule: rtrancl.induct, auto)
  then show ?thesis by blast
qed

lemma accessible_unsat_core:
  shows "\<U>\<^sub>c ` {s'. s \<succ>\<^sup>* s'} = {\<U>\<^sub>c s}"
proof -
  have "s \<succ>\<^sup>* s' \<Longrightarrow> \<U>\<^sub>c s' = \<U>\<^sub>c s" for s'
    by (induct s s' rule: rtrancl.induct, auto)
  then show ?thesis by blast
qed

lemma state_eqI:
  "\<B>\<^sub>i\<^sub>l s = \<B>\<^sub>i\<^sub>l s' \<Longrightarrow> \<B>\<^sub>i\<^sub>u s = \<B>\<^sub>i\<^sub>u s' \<Longrightarrow>
   \<T> s = \<T> s' \<Longrightarrow> \<V> s = \<V> s' \<Longrightarrow>
   \<U> s = \<U> s' \<Longrightarrow> \<U>\<^sub>c s = \<U>\<^sub>c s' \<Longrightarrow>
   s = s'"
  by (cases s, cases s', auto)

lemma finite_accessible_states:
  shows "finite {s'. s \<succ>\<^sup>* s'}" (is "finite ?A")
proof-
  let ?V = "\<V> ` ?A"
  let ?T = "\<T> ` ?A"
  let ?P = "?V \<times> ?T \<times> {\<B>\<^sub>i s} \<times> {True, False} \<times> {\<U>\<^sub>c s}"
  have "finite ?P"
    using finite_accessible_valuations finite_accessible_tableaus
    by auto
  moreover
  let ?f = "\<lambda> s. (\<V> s, \<T> s, \<B>\<^sub>i s, \<U> s, \<U>\<^sub>c s)"
  have "?f ` ?A \<subseteq> ?P"
    using accessible_bounds[of s] accessible_unsat_core[of s]
    by auto
  moreover
  have "inj_on ?f ?A"
    unfolding inj_on_def by (auto intro: state_eqI)
  ultimately
  show ?thesis
    using finite_imageD [of ?f ?A]
    using finite_subset
    by auto
qed

(* -------------------------------------------------------------------------- *)
lemma acyclic_suc_rel: "acyclic succ_rel"
proof (rule acyclicI, rule allI)
  fix s
  show "(s, s) \<notin> succ_rel\<^sup>+"
  proof
    assume "s \<succ>\<^sup>+ s"
    then obtain l where
      "l \<noteq> []" "length l > 1" "hd l = s" "last l = s" "succ_chain l"
      using trancl_rel_chain[of s s succ_rel]
      by auto

    have "l ! 0 = s"
      using \<open>l \<noteq> []\<close> \<open>hd l = s\<close>
      by (simp add: hd_conv_nth)
    then have "s \<succ> (l ! 1)"
      using \<open>succ_chain l\<close>
      unfolding rel_chain_def
      using \<open>length l > 1\<close>
      by auto
    then have "\<triangle> (\<T> s)"
      by simp

    let ?enter_rvars =
      "{x. \<exists> sl. swap_lr l sl x}"

    have "finite ?enter_rvars"
    proof-
      let ?all_vars = "\<Union> (set (map (\<lambda> t. lvars t \<union> rvars t) (map \<T> l)))"
      have "finite ?all_vars"
        by (auto simp add: lvars_def rvars_def finite_vars)
      moreover
      have "?enter_rvars \<subseteq> ?all_vars"
        by force
      ultimately
      show ?thesis
        by (simp add: finite_subset)
    qed

    let ?xr = "Max ?enter_rvars"
    have "?xr \<in> ?enter_rvars"
    proof (rule Max_in)
      show "?enter_rvars \<noteq> {}"
      proof-
        from \<open>s \<succ> (l ! 1)\<close>
        obtain x\<^sub>i x\<^sub>j :: var where
          "x\<^sub>i \<in> lvars (\<T> s)" "x\<^sub>i \<in> rvars (\<T> (l ! 1))"
          by (rule succ_vars) auto
        then have "x\<^sub>i \<in> ?enter_rvars"
          using \<open>hd l = s\<close> \<open>l \<noteq> []\<close> \<open>length l > 1\<close>
          by (auto simp add: hd_conv_nth)
        then show ?thesis
          by auto
      qed
    next
      show "finite ?enter_rvars"
        using \<open>finite ?enter_rvars\<close>
        .
    qed
    then obtain xr sl where
      "xr = ?xr" "swap_lr l sl xr"
      by auto
    then have "sl + 1 < length l"
      by simp

    have "(l ! sl) \<succ> (l ! (sl + 1))"
      using \<open>sl + 1 < length l\<close> \<open>succ_chain l\<close>
      unfolding rel_chain_def
      by auto


    have "length l > 2"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      with \<open>length l > 1\<close>
      have "length l = 2"
        by auto
      then have "last l = l ! 1"
        by (cases l) (auto simp add: last_conv_nth nth_Cons split: nat.split)
      then have "xr \<in> lvars (\<T> s)" "xr \<in> rvars (\<T> s)"
        using \<open>length l = 2\<close>
        using \<open>swap_lr l sl xr\<close>
        using \<open>hd l = s\<close> \<open>last l = s\<close> \<open>l \<noteq> []\<close>
        by (auto simp add: hd_conv_nth)
      then show False
        using \<open>\<triangle> (\<T> s)\<close>
        unfolding normalized_tableau_def
        by auto
    qed

    obtain l' where
      "hd l' = l ! (sl + 1)" "last l' = l ! sl" "length l' = length l - 1"  "succ_chain l'" and
      l'_l:   "\<forall> i. i + 1 < length l' \<longrightarrow>
     (\<exists> j. j + 1 < length l \<and> l' ! i = l ! j \<and> l' ! (i + 1) = l ! (j + 1))"
      using \<open>length l > 2\<close> \<open>sl + 1 < length l\<close> \<open>hd l = s\<close> \<open>last l = s\<close> \<open>succ_chain l\<close>
      using reorder_cyclic_list[of l s sl]
      by blast

    then have "xr \<in> rvars (\<T> (hd l'))"  "xr \<in> lvars (\<T> (last l'))" "length l' > 1" "l' \<noteq> []"
      using \<open>swap_lr l sl xr\<close> \<open>length l > 2\<close>
      by auto

    then have "\<exists> sp. swap_rl l' sp xr"
      using \<open>succ_chain l'\<close>
      using succ_chain_swap_rl_exists[of l' 0 "length l' - 1" xr]
      by (auto simp add: hd_conv_nth last_conv_nth)
    then have "\<exists> sp. swap_rl l' sp xr \<and> (\<forall> sp'. sp' < sp \<longrightarrow> \<not> swap_rl l' sp' xr)"
      by (rule min_element)
    then obtain sp where
      "swap_rl l' sp xr" "\<forall> sp'. sp' < sp \<longrightarrow> \<not> swap_rl l' sp' xr"
      by blast
    then have "sp + 1 < length l'"
      by simp

    have "\<langle>\<V> (l' ! 0)\<rangle> xr = \<langle>\<V> (l' ! sp)\<rangle> xr"
    proof-
      have "always_r l' 0 sp xr"
        using \<open>xr \<in> rvars (\<T> (hd l'))\<close> \<open>sp + 1 < length l'\<close>
          \<open>\<forall> sp'. sp' < sp \<longrightarrow> \<not> swap_rl l' sp' xr\<close>
      proof (induct sp)
        case 0
        then have "l' \<noteq> []"
          by auto
        then show ?case
          using 0(1)
          by (auto simp add: hd_conv_nth)
      next
        case (Suc sp')
        show ?case
        proof (safe)
          fix k
          assume "k \<le> Suc sp'"
          show "xr \<in> rvars (\<T> (l' ! k))"
          proof (cases "k = sp' + 1")
            case False
            then show ?thesis
              using Suc \<open>k \<le> Suc sp'\<close>
              by auto
          next
            case True
            then have "xr \<in> rvars (\<T> (l' ! (k - 1)))"
              using Suc
              by auto
            moreover
            then have "xr \<notin> lvars (\<T> (l' ! k))"
              using True Suc(3) Suc(4)
              by auto
            moreover
            have "(l' ! (k - 1)) \<succ> (l' ! k)"
              using \<open>succ_chain l'\<close>
              using Suc(3) True
              by (simp add: rel_chain_def)
            ultimately
            show ?thesis
              using succ_vars_id[of "l' ! (k - 1)" "l' ! k"]
              by auto
          qed
        qed
      qed
      then show ?thesis
        using \<open>sp + 1 < length l'\<close>
        using \<open>succ_chain l'\<close>
        using succ_chain_always_r_valuation_id
        by simp
    qed

    have "(l' ! sp) \<succ> (l' ! (sp+1))"
      using \<open>sp + 1 < length l'\<close> \<open>succ_chain l'\<close>
      unfolding rel_chain_def
      by simp
    then obtain xs xr' :: var where
      "xs \<in> lvars (\<T> (l' ! sp))"
      "xr \<in> rvars (\<T> (l' ! sp))"
      "swap_lr l' sp xs"
      apply (rule succ_vars)
      using \<open>swap_rl l' sp xr\<close> \<open>sp + 1 < length l'\<close>
      by auto
    then have "xs \<noteq> xr"
      using \<open>(l' ! sp) \<succ> (l' ! (sp+1))\<close>
      by (auto simp add: normalized_tableau_def)

    obtain sp' where
      "l' ! sp = l ! sp'" "l' ! (sp + 1) = l ! (sp' + 1)"
      "sp' + 1 < length l"
      using \<open>sp + 1 < length l'\<close> l'_l
      by auto

    have "xs \<in> ?enter_rvars"
      using \<open>swap_lr l' sp xs\<close> l'_l
      by force

    have "xs < xr"
    proof-
      have "xs \<le> ?xr"
        using \<open>finite ?enter_rvars\<close> \<open>xs \<in> ?enter_rvars\<close>
        by (rule Max_ge)
      then show ?thesis
        using \<open>xr = ?xr\<close> \<open>xs \<noteq> xr\<close>
        by simp
    qed

    let ?sl = "l ! sl"
    let ?sp = "l' ! sp"
    let ?eq = "eq_for_lvar (\<T> ?sp) xs"
    let ?bl = "\<V> ?sl"
    let ?bp = "\<V> ?sp"

    have "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?sl" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?sp"
      using \<open>l ! sl \<succ> (l ! (sl + 1))\<close>
      using \<open>l' ! sp \<succ> (l' ! (sp+ 1))\<close>
      by simp_all

    have "\<B>\<^sub>i ?sp = \<B>\<^sub>i ?sl"
    proof-
      have "\<B>\<^sub>i (l' ! sp) = \<B>\<^sub>i (l' ! (length l' - 1))"
        using \<open>sp + 1 < length l'\<close> \<open>succ_chain l'\<close>
        using succ_chain_bounds_id
        by auto
      then have "\<B>\<^sub>i (last l') = \<B>\<^sub>i (l' ! sp)"
        using \<open>l' \<noteq> []\<close>
        by (simp add: last_conv_nth)
      then show ?thesis
        using \<open>last l' = l ! sl\<close>
        by simp
    qed

    have diff_satified: "\<langle>?bl\<rangle> xs - \<langle>?bp\<rangle> xs = ((rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace>) - ((rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace>)"
    proof-
      have "\<langle>?bp\<rangle> \<Turnstile>\<^sub>e ?eq"
        using \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?sp\<close>
        using eq_for_lvar[of xs "\<T> ?sp"]
        using \<open>xs \<in> lvars (\<T> (l' ! sp))\<close>
        unfolding curr_val_satisfies_no_lhs_def satisfies_tableau_def
        by auto
      moreover
      have "\<langle>?bl\<rangle> \<Turnstile>\<^sub>e ?eq"
      proof-
        have "\<langle>\<V> (l ! sl)\<rangle> \<Turnstile>\<^sub>t \<T> (l' ! sp)"
          using \<open>l' ! sp = l ! sp'\<close> \<open>sp' + 1 < length l\<close> \<open>sl + 1 < length l\<close>
          using \<open>succ_chain l\<close>
          using succ_chain_tableau_equiv[of l sl sp']
          using \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?sl\<close>
          unfolding curr_val_satisfies_no_lhs_def
          by simp
        then show ?thesis
          unfolding satisfies_tableau_def
          using eq_for_lvar
          using \<open>xs \<in> lvars (\<T> (l' ! sp))\<close>
          by simp
      qed
      moreover
      have "lhs ?eq = xs"
        using \<open>xs \<in> lvars (\<T> (l' ! sp))\<close>
        using eq_for_lvar
        by simp
      ultimately
      show ?thesis
        unfolding satisfies_eq_def
        by auto
    qed

    have "\<not> in_bounds xr \<langle>?bl\<rangle> (\<B> ?sl)"
      using \<open>l ! sl \<succ> (l ! (sl + 1))\<close>  \<open>swap_lr l sl xr\<close>
      using succ_min_lvar_not_in_bounds(1)[of ?sl "l ! (sl + 1)" xr]
      by simp

    have "\<forall> x. x < xr \<longrightarrow> in_bounds x \<langle>?bl\<rangle> (\<B> ?sl)"
    proof (safe)
      fix x
      assume "x < xr"
      show "in_bounds x \<langle>?bl\<rangle> (\<B> ?sl)"
      proof (cases "x \<in> lvars (\<T> ?sl)")
        case True
        then show ?thesis
          using succ_min_lvar_not_in_bounds(2)[of ?sl "l ! (sl + 1)" xr]
          using \<open>l ! sl \<succ> (l ! (sl + 1))\<close>  \<open>swap_lr l sl xr\<close> \<open>x < xr\<close>
          by simp
      next
        case False
        then show ?thesis
          using \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?sl\<close>
          unfolding curr_val_satisfies_no_lhs_def
          by (simp add: satisfies_bounds_set.simps)
      qed
    qed

    then have "in_bounds xs \<langle>?bl\<rangle> (\<B> ?sl)"
      using \<open>xs < xr\<close>
      by simp

    have "\<not> in_bounds xs \<langle>?bp\<rangle> (\<B> ?sp)"
      using \<open>l' ! sp \<succ> (l' ! (sp + 1))\<close>  \<open>swap_lr l' sp xs\<close>
      using succ_min_lvar_not_in_bounds(1)[of ?sp "l' ! (sp + 1)" xs]
      by simp

    have "\<forall> x \<in> rvars_eq ?eq. x > xr \<longrightarrow> \<langle>?bp\<rangle> x = \<langle>?bl\<rangle> x"
    proof (safe)
      fix x
      assume "x \<in> rvars_eq ?eq" "x > xr"
      then have "always_r l' 0 (length l' - 1) x"
      proof (safe)
        fix k
        assume "x \<in> rvars_eq ?eq" "x > xr" "0 \<le> k" "k \<le> length l' - 1"
        obtain k' where "l ! k' = l' ! k" "k' < length l"
          using l'_l \<open>k \<le> length l' - 1\<close> \<open>length l' > 1\<close>
          apply (cases "k > 0")
           apply (erule_tac x="k - 1" in allE)
           apply (drule mp)
          by auto

        let ?eq' = "eq_for_lvar (\<T> (l ! sp')) xs"

        have "\<forall> x \<in> rvars_eq ?eq'. x > xr \<longrightarrow> always_r l 0 (length l - 1) x"
        proof (safe)
          fix x k
          assume "x \<in> rvars_eq ?eq'" "xr < x" "0 \<le> k" "k \<le> length l - 1"
          then have "x \<in> rvars (\<T> (l ! sp'))"
            using eq_for_lvar[of xs "\<T> (l ! sp')"]
            using \<open>swap_lr l' sp xs\<close> \<open>l' ! sp = l ! sp'\<close>
            by (auto simp add: rvars_def)
          have *: "\<forall> i. i < sp' \<longrightarrow> x \<in> rvars (\<T> (l ! i))"
          proof (safe, rule ccontr)
            fix i
            assume "i < sp'" "x \<notin> rvars (\<T> (l ! i))"
            then have "x \<in> lvars (\<T> (l ! i))"
              using \<open>x \<in> rvars (\<T> (l ! sp'))\<close>
              using \<open>sp' + 1 < length l\<close>
              using \<open>succ_chain l\<close>
              using succ_chain_vars_id[of l i sp']
              by auto
            obtain i' where "swap_lr l i' x"
              using \<open>x \<in> lvars (\<T> (l ! i))\<close>
              using \<open>x \<in> rvars (\<T> (l ! sp'))\<close>
              using \<open>i < sp'\<close> \<open>sp' + 1 < length l\<close>
              using \<open>succ_chain l\<close>
              using succ_chain_swap_lr_exists[of l i sp' x]
              by auto
            then have "x \<in> ?enter_rvars"
              by auto
            then have "x \<le> ?xr"
              using \<open>finite ?enter_rvars\<close>
              using Max_ge[of ?enter_rvars x]
              by simp
            then show False
              using \<open>x > xr\<close>
              using \<open>xr = ?xr\<close>
              by simp
          qed

          then have "x \<in> rvars (\<T> (last l))"
            using \<open>hd l = s\<close> \<open>last l = s\<close> \<open>l \<noteq> []\<close>
            using \<open>x \<in> rvars (\<T> (l ! sp'))\<close>
            by (auto simp add: hd_conv_nth)

          show "x \<in> rvars (\<T> (l ! k))"
          proof (cases "k = length l - 1")
            case True
            then show ?thesis
              using \<open>x \<in> rvars (\<T> (last l))\<close>
              using \<open>l \<noteq> []\<close>
              by (simp add: last_conv_nth)
          next
            case False
            then have "k < length l - 1"
              using \<open>k \<le> length l - 1\<close>
              by simp
            then have "k < length l"
              using \<open>length l > 1\<close>
              by auto
            show ?thesis
            proof (rule ccontr)
              assume "\<not> ?thesis"
              then have "x \<in> lvars (\<T> (l ! k))"
                using \<open>x \<in> rvars (\<T> (l ! sp'))\<close>
                using \<open>sp' + 1 < length l\<close> \<open>k < length l\<close>
                using succ_chain_vars_id[of l k sp']
                using \<open>succ_chain l\<close> \<open>l \<noteq> []\<close>
                by auto
              obtain i' where "swap_lr l i' x"
                using \<open>succ_chain l\<close>
                using \<open>x \<in> lvars (\<T> (l ! k))\<close>
                using \<open>x \<in> rvars (\<T> (last l))\<close>
                using \<open>k < length l - 1\<close> \<open>l \<noteq> []\<close>
                using succ_chain_swap_lr_exists[of l k "length l - 1" x]
                by (auto simp add: last_conv_nth)
              then have "x \<in> ?enter_rvars"
                by auto
              then have "x \<le> ?xr"
                using \<open>finite ?enter_rvars\<close>
                using Max_ge[of ?enter_rvars x]
                by simp
              then show False
                using \<open>x > xr\<close>
                using \<open>xr = ?xr\<close>
                by simp
            qed
          qed
        qed
        then have "x \<in> rvars (\<T> (l ! k'))"
          using \<open>x \<in> rvars_eq ?eq\<close> \<open>x > xr\<close> \<open>k' < length l\<close>
          using \<open>l' ! sp = l ! sp'\<close>
          by simp

        then show "x \<in> rvars (\<T> (l' ! k))"
          using \<open>l ! k' = l' ! k\<close>
          by simp
      qed
      then have "\<langle>?bp\<rangle> x = \<langle>\<V> (l' ! (length l' - 1))\<rangle> x"
        using \<open>succ_chain l'\<close> \<open>sp + 1 < length l'\<close>
        by (auto intro!: succ_chain_always_r_valuation_id[rule_format])
      then have "\<langle>?bp\<rangle> x = \<langle>\<V> (last l')\<rangle> x"
        using \<open>l' \<noteq> []\<close>
        by (simp add: last_conv_nth)
      then show "\<langle>?bp\<rangle> x = \<langle>?bl\<rangle> x"
        using \<open>last l' = l ! sl\<close>
        by simp
    qed

    have "\<langle>?bp\<rangle> xr = \<langle>\<V> (l ! (sl + 1))\<rangle> xr"
      using \<open>\<langle>\<V> (l' ! 0)\<rangle> xr = \<langle>\<V> (l' ! sp)\<rangle> xr\<close>
      using \<open>hd l' = l ! (sl + 1)\<close> \<open>l' \<noteq> []\<close>
      by (simp add: hd_conv_nth)

    {
      fix dir1 dir2 :: "('i,'a) Direction"
      assume dir1: "dir1 = (if \<langle>?bl\<rangle> xr <\<^sub>l\<^sub>b \<B>\<^sub>l ?sl xr then Positive else Negative)"
      then have "\<lhd>\<^sub>l\<^sub>b (lt dir1) (\<langle>?bl\<rangle> xr) (LB dir1 ?sl xr)"
        using \<open>\<not> in_bounds xr \<langle>?bl\<rangle> (\<B> ?sl)\<close>
        using neg_bounds_compare(7) neg_bounds_compare(3)
        by (auto simp add: bound_compare''_defs)
      then have "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir1) (\<langle>?bl\<rangle> xr) (LB dir1 ?sl xr)"
        using bounds_compare_contradictory(7) bounds_compare_contradictory(3) neg_bounds_compare(6) dir1
        unfolding bound_compare''_defs
        by auto force
      have "LB dir1 ?sl xr \<noteq> None"
        using \<open>\<lhd>\<^sub>l\<^sub>b (lt dir1) (\<langle>?bl\<rangle> xr) (LB dir1 ?sl xr)\<close>
        by (cases "LB dir1 ?sl xr")  (auto simp add: bound_compare_defs)

      assume dir2: "dir2 = (if \<langle>?bp\<rangle> xs <\<^sub>l\<^sub>b \<B>\<^sub>l ?sp xs then Positive else Negative)"
      then have "\<lhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> xs) (LB dir2 ?sp xs)"
        using \<open>\<not> in_bounds xs \<langle>?bp\<rangle> (\<B> ?sp)\<close>
        using neg_bounds_compare(2) neg_bounds_compare(6)
        by (auto simp add: bound_compare''_defs)
      then have "\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> xs) (LB dir2 ?sp xs)"
        using bounds_compare_contradictory(3) bounds_compare_contradictory(7) neg_bounds_compare(6) dir2
        unfolding bound_compare''_defs
        by auto force
      then have "\<forall> x \<in> rvars_eq ?eq. x < xr \<longrightarrow> \<not> reasable_var dir2 x ?eq ?sp"
        using succ_min_rvar[of ?sp "l' ! (sp + 1)" xs xr ?eq]
        using \<open>l' ! sp \<succ> (l' ! (sp + 1))\<close>
        using \<open>swap_lr l' sp xs\<close> \<open>swap_rl l' sp xr\<close> dir2
        unfolding bound_compare''_defs
        by auto

      have "LB dir2 ?sp xs \<noteq> None"
        using \<open>\<lhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> xs) (LB dir2 ?sp xs)\<close>
        by (cases "LB dir2 ?sp xs")  (auto simp add: bound_compare_defs)

      have *: "\<forall> x \<in> rvars_eq ?eq. x < xr \<longrightarrow>
        ((coeff (rhs ?eq) x > 0 \<longrightarrow> \<unrhd>\<^sub>u\<^sub>b (lt dir2) (\<langle>?bp\<rangle> x) (UB dir2 ?sp x)) \<and>
         (coeff (rhs ?eq) x < 0 \<longrightarrow> \<unlhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> x) (LB dir2 ?sp x)))"
      proof (safe)
        fix x
        assume "x \<in> rvars_eq ?eq" "x < xr" "coeff (rhs ?eq) x > 0"
        then have "\<not> \<lhd>\<^sub>u\<^sub>b (lt dir2) (\<langle>?bp\<rangle> x) (UB dir2 ?sp x)"
          using \<open>\<forall> x \<in> rvars_eq ?eq. x < xr \<longrightarrow> \<not> reasable_var dir2 x ?eq ?sp\<close>
          by simp
        then show "\<unrhd>\<^sub>u\<^sub>b (lt dir2) (\<langle>?bp\<rangle> x) (UB dir2 ?sp x)"
          using dir2 neg_bounds_compare(4) neg_bounds_compare(8)
          unfolding bound_compare''_defs
          by force
      next
        fix x
        assume "x \<in> rvars_eq ?eq" "x < xr" "coeff (rhs ?eq) x < 0"
        then have "\<not> \<rhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> x) (LB dir2 ?sp x)"
          using \<open>\<forall> x \<in> rvars_eq ?eq. x < xr \<longrightarrow> \<not> reasable_var dir2 x ?eq ?sp\<close>
          by simp
        then show "\<unlhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> x) (LB dir2 ?sp x)"
          using dir2 neg_bounds_compare(4) neg_bounds_compare(8) dir2
          unfolding bound_compare''_defs
          by force
      qed

      have "(lt dir2) (\<langle>?bp\<rangle> xs) (\<langle>?bl\<rangle> xs)"
        using \<open>\<lhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> xs) (LB dir2 ?sp xs)\<close>
        using \<open>\<B>\<^sub>i ?sp = \<B>\<^sub>i ?sl\<close> dir2
        using \<open>in_bounds xs \<langle>?bl\<rangle> (\<B> ?sl)\<close>
        by (auto simp add: bound_compare''_defs
            simp: indexl_def indexu_def boundsl_def boundsu_def)
      then have "(lt dir2) 0 (\<langle>?bl\<rangle> xs - \<langle>?bp\<rangle> xs)"
        using dir2
        by (auto simp add: minus_gt[THEN sym] minus_lt[THEN sym])

      moreover

      have "le (lt dir2) ((rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace> - (rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace>) 0"
      proof-
        have "\<forall> x \<in> rvars_eq ?eq. (0 < coeff (rhs ?eq) x \<longrightarrow> le (lt dir2) 0 (\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x)) \<and>
                    (coeff (rhs ?eq) x < 0 \<longrightarrow> le (lt dir2) (\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x) 0)"
        proof
          fix x
          assume "x \<in> rvars_eq ?eq"
          show "(0 < coeff (rhs ?eq) x \<longrightarrow> le (lt dir2) 0 (\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x)) \<and>
                (coeff (rhs ?eq) x < 0 \<longrightarrow> le (lt dir2) (\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x) 0)"
          proof (cases "x < xr")
            case True
            then have "in_bounds x \<langle>?bl\<rangle> (\<B> ?sl)"
              using \<open>\<forall> x. x < xr \<longrightarrow> in_bounds x \<langle>?bl\<rangle> (\<B> ?sl)\<close>
              by simp
            show ?thesis
            proof (safe)
              assume "coeff (rhs ?eq) x > 0" "0 \<noteq> \<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x"
              then have "\<unrhd>\<^sub>u\<^sub>b (lt dir2) (\<langle>\<V> (l' ! sp)\<rangle> x) (UB dir2 (l' ! sp) x)"
                using * \<open>x < xr\<close> \<open>x \<in> rvars_eq ?eq\<close>
                by simp
              then have "le (lt dir2) (\<langle>?bl\<rangle> x) (\<langle>?bp\<rangle> x)"
                using \<open>in_bounds x \<langle>?bl\<rangle> (\<B> ?sl)\<close> \<open>\<B>\<^sub>i ?sp = \<B>\<^sub>i ?sl\<close> dir2
                apply (auto simp add: bound_compare''_defs)
                using bounds_lg(3)[of "\<langle>?bp\<rangle> x" "\<B>\<^sub>u (l ! sl) x" "\<langle>?bl\<rangle> x"]
                using bounds_lg(6)[of "\<langle>?bp\<rangle> x" "\<B>\<^sub>l (l ! sl) x" "\<langle>?bl\<rangle> x"]
                unfolding bound_compare''_defs
                by (auto simp: indexl_def indexu_def boundsl_def boundsu_def)
              then show "lt dir2 0 (\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x)"
                using \<open>0 \<noteq> \<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x\<close>
                using minus_gt[of "\<langle>?bl\<rangle> x" "\<langle>?bp\<rangle> x"] minus_lt[of "\<langle>?bp\<rangle> x" "\<langle>?bl\<rangle> x"] dir2
                by auto
            next
              assume "coeff (rhs ?eq) x < 0"  "\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x \<noteq> 0"
              then have "\<unlhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>\<V> (l' ! sp)\<rangle> x) (LB dir2 (l' ! sp) x)"
                using * \<open>x < xr\<close> \<open>x \<in> rvars_eq ?eq\<close>
                by simp
              then have "le (lt dir2) (\<langle>?bp\<rangle> x) (\<langle>?bl\<rangle> x)"
                using \<open>in_bounds x \<langle>?bl\<rangle> (\<B> ?sl)\<close> \<open>\<B>\<^sub>i ?sp = \<B>\<^sub>i ?sl\<close> dir2
                apply (auto simp add: bound_compare''_defs)
                using bounds_lg(3)[of "\<langle>?bp\<rangle> x" "\<B>\<^sub>u (l ! sl) x" "\<langle>?bl\<rangle> x"]
                using bounds_lg(6)[of "\<langle>?bp\<rangle> x" "\<B>\<^sub>l (l ! sl) x" "\<langle>?bl\<rangle> x"]
                unfolding bound_compare''_defs
                by (auto simp: indexl_def indexu_def boundsl_def boundsu_def)
              then show "lt dir2 (\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x) 0"
                using \<open>\<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x \<noteq> 0\<close>
                using minus_gt[of "\<langle>?bl\<rangle> x" "\<langle>?bp\<rangle> x"] minus_lt[of "\<langle>?bp\<rangle> x" "\<langle>?bl\<rangle> x"] dir2
                by auto
            qed
          next
            case False
            show ?thesis
            proof (cases "x = xr")
              case True
              have "\<langle>\<V> (l ! (sl + 1))\<rangle> xr = the (LB dir1 ?sl xr)"
                using \<open>l ! sl \<succ> (l ! (sl + 1))\<close>
                using \<open>swap_lr l sl xr\<close>
                using succ_set_on_bound(1)[of "l ! sl" "l ! (sl + 1)" xr]
                using \<open>\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir1) (\<langle>?bl\<rangle> xr) (LB dir1 ?sl xr)\<close> dir1
                unfolding bound_compare''_defs
                by auto
              then have "\<langle>?bp\<rangle> xr = the (LB dir1 ?sl xr)"
                using \<open>\<langle>?bp\<rangle> xr = \<langle>\<V> (l ! (sl + 1))\<rangle> xr\<close>
                by simp
              then have "lt dir1 (\<langle>?bl\<rangle> xr) (\<langle>?bp\<rangle> xr)"
                using \<open>LB dir1 ?sl xr \<noteq> None\<close>
                using \<open>\<lhd>\<^sub>l\<^sub>b (lt dir1) (\<langle>?bl\<rangle> xr) (LB dir1 ?sl xr)\<close> dir1
                by (auto simp add: bound_compare_defs)

              moreover

              have "reasable_var dir2 xr ?eq ?sp"
                using \<open>\<not> \<unrhd>\<^sub>l\<^sub>b (lt dir2) (\<langle>?bp\<rangle> xs) (LB dir2 ?sp xs)\<close>
                using \<open>l' ! sp \<succ> (l' ! (sp + 1))\<close>
                using \<open>swap_lr l' sp xs\<close> \<open>swap_rl l' sp xr\<close>
                using succ_min_rvar[of "l' ! sp" "l' ! (sp + 1)"xs xr ?eq] dir2
                unfolding bound_compare''_defs
                by auto

              then have "if dir1 = dir2 then coeff (rhs ?eq) xr > 0 else coeff (rhs ?eq) xr < 0"
                using \<open>\<langle>?bp\<rangle> xr = the (LB dir1 ?sl xr)\<close>
                using \<open>\<B>\<^sub>i ?sp = \<B>\<^sub>i ?sl\<close>[THEN sym] dir1
                using \<open>LB dir1 ?sl xr \<noteq> None\<close> dir1 dir2
                by (auto split: if_splits simp add: bound_compare_defs
                    indexl_def indexu_def boundsl_def boundsu_def)
              moreover
              have "dir1 = Positive \<or> dir1 = Negative" "dir2 = Positive \<or> dir2 = Negative"
                using dir1 dir2
                by auto
              ultimately
              show ?thesis
                using \<open>x = xr\<close>
                using minus_lt[of "\<langle>?bp\<rangle> xr" "\<langle>?bl\<rangle> xr"] minus_gt[of "\<langle>?bl\<rangle> xr" "\<langle>?bp\<rangle> xr"]
                by (auto split: if_splits)
            next
              case False
              then have "x > xr"
                using \<open>\<not> x < xr\<close>
                by simp
              then have "\<langle>?bp\<rangle> x = \<langle>?bl\<rangle> x"
                using \<open>\<forall> x \<in> rvars_eq ?eq. x > xr \<longrightarrow> \<langle>?bp\<rangle> x = \<langle>?bl\<rangle> x\<close>
                using \<open>x \<in> rvars_eq ?eq\<close>
                by simp
              then show ?thesis
                by simp
            qed
          qed
        qed
        then have "le (lt dir2) 0 (rhs ?eq \<lbrace> \<lambda> x. \<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x \<rbrace>)"
          using dir2
          apply auto
          using valuate_nonneg[of "rhs ?eq" "\<lambda> x. \<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x"]
           apply force
          using valuate_nonpos[of "rhs ?eq" "\<lambda> x. \<langle>?bp\<rangle> x - \<langle>?bl\<rangle> x"]
          apply force
          done
        then have "le (lt dir2) 0 ((rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace> - (rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace>)"
          by (subst valuate_diff)+ simp
        then have "le (lt dir2) ((rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace>) ((rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace>)"
          using minus_lt[of "(rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace>" "(rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace>"] dir2
          by auto
        then show ?thesis
          using dir2
          using minus_lt[of "(rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace>" "(rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace>"]
          using minus_gt[of "(rhs ?eq) \<lbrace> \<langle>?bp\<rangle> \<rbrace>" "(rhs ?eq) \<lbrace> \<langle>?bl\<rangle> \<rbrace>"]
          by auto
      qed
      ultimately
      have False
        using diff_satified dir2
        by (auto split: if_splits)
    }
    then show False
      by auto
  qed
qed

(* -------------------------------------------------------------------------- *)

lemma check_unsat_terminates:
  assumes "\<U> s"
  shows "check_dom s"
  by (rule check_dom.intros) (auto simp add: assms)

lemma check_sat_terminates'_aux:
  assumes
    dir: "dir = (if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive else Negative)" and
    *: "\<And> s'. \<lbrakk>s \<succ> s'; \<nabla> s'; \<triangle> (\<T> s'); \<diamond> s'; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s' \<rbrakk> \<Longrightarrow> check_dom s'" and
    "\<nabla> s" "\<triangle> (\<T> s)" "\<diamond> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"
    "\<not> \<U> s" "min_lvar_not_in_bounds s = Some x\<^sub>i"
    "\<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i)"
  shows "check_dom
            (case min_rvar_incdec dir s x\<^sub>i of Inl I \<Rightarrow> set_unsat I s
             | Inr x\<^sub>j \<Rightarrow> pivot_and_update x\<^sub>i x\<^sub>j (the (LB dir s x\<^sub>i)) s)"
proof (cases "min_rvar_incdec dir s x\<^sub>i")
  case Inl
  then show ?thesis
    using check_unsat_terminates by simp
next
  case (Inr x\<^sub>j)
  then have xj: "x\<^sub>j \<in> rvars_of_lvar (\<T> s) x\<^sub>i"
    using min_rvar_incdec_eq_Some_rvars[of _ s "eq_for_lvar (\<T> s) x\<^sub>i" x\<^sub>j]
    using dir
    by simp
  let ?s' = "pivot_and_update x\<^sub>i x\<^sub>j (the (LB dir s x\<^sub>i)) s"
  have "check_dom ?s'"
  proof (rule * )
    show **: "\<nabla> ?s'" "\<triangle> (\<T> ?s')" "\<diamond> ?s'" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?s'"
      using \<open>min_lvar_not_in_bounds s = Some x\<^sub>i\<close>  Inr
      using \<open>\<nabla> s\<close> \<open>\<triangle> (\<T> s)\<close>  \<open>\<diamond> s\<close> \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s\<close>  dir
      using pivotandupdate_check_precond
      by auto
    have xi: "x\<^sub>i \<in> lvars (\<T> s)"
      using assms(8) min_lvar_not_in_bounds_lvars by blast
    show "s \<succ> ?s'"
      unfolding gt_state_def
      using \<open>\<triangle> (\<T> s)\<close> \<open>\<diamond> s\<close> \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s\<close> \<open>\<nabla> s\<close>
      using \<open>min_lvar_not_in_bounds s = Some x\<^sub>i\<close> \<open>\<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i)\<close>
        Inr dir
      by (intro conjI pivotandupdate_bounds_id pivotandupdate_unsat_core_id,
          auto intro!: xj xi)
  qed
  then show ?thesis using Inr by simp
qed

lemma check_sat_terminates':
  assumes "\<nabla> s" "\<triangle> (\<T> s)" "\<diamond> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "s\<^sub>0 \<succ>\<^sup>* s"
  shows "check_dom s"
  using assms
proof (induct s rule: wf_induct[of "{(y, x). s\<^sub>0 \<succ>\<^sup>* x \<and> x \<succ> y}"])
  show "wf {(y, x). s\<^sub>0 \<succ>\<^sup>* x \<and> x \<succ> y}"
  proof (rule finite_acyclic_wf)
    let ?A = "{(s', s). s\<^sub>0 \<succ>\<^sup>* s \<and> s \<succ> s'}"
    let ?B = "{s. s\<^sub>0 \<succ>\<^sup>* s}"
    have "?A \<subseteq> ?B \<times> ?B"
    proof
      fix p
      assume "p \<in> ?A"
      then have "fst p \<in> ?B" "snd p \<in> ?B"
        using rtrancl_into_trancl1[of s\<^sub>0 "snd p" succ_rel "fst p"]
        by auto
      then show "p \<in> ?B \<times> ?B"
        using mem_Sigma_iff[of "fst p" "snd p"]
        by auto
    qed
    then show "finite ?A"
      using finite_accessible_states[of s\<^sub>0]
      using finite_subset[of ?A "?B \<times> ?B"]
      by simp

    show "acyclic ?A"
    proof-
      have "?A \<subseteq> succ_rel\<inverse>"
        by auto
      then show ?thesis
        using acyclic_converse acyclic_subset
        using acyclic_suc_rel
        by auto
    qed
  qed
next
  fix s
  assume "\<forall> s'. (s', s) \<in> {(y, x). s\<^sub>0 \<succ>\<^sup>* x \<and> x \<succ> y} \<longrightarrow> \<nabla> s' \<longrightarrow> \<triangle> (\<T> s') \<longrightarrow> \<diamond> s' \<longrightarrow> \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s' \<longrightarrow> s\<^sub>0 \<succ>\<^sup>* s' \<longrightarrow> check_dom s'"
    "\<nabla> s" "\<triangle> (\<T> s)" "\<diamond> s" " \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "s\<^sub>0 \<succ>\<^sup>* s"
  then have *: "\<And> s'. \<lbrakk>s \<succ> s'; \<nabla> s'; \<triangle> (\<T> s'); \<diamond> s'; \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s' \<rbrakk> \<Longrightarrow> check_dom s'"
    using rtrancl_into_trancl1[of s\<^sub>0 s succ_rel]
    using trancl_into_rtrancl[of s\<^sub>0 _ succ_rel]
    by auto
  show "check_dom s"
  proof (rule check_dom.intros, simp_all add: check'_def, unfold Positive_def[symmetric], unfold Negative_def[symmetric])
    fix x\<^sub>i
    assume "\<not> \<U> s" "Some x\<^sub>i = min_lvar_not_in_bounds s" "\<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i"
    have "\<B>\<^sub>l s x\<^sub>i = LB Positive s x\<^sub>i"
      by simp
    show "check_dom
            (case min_rvar_incdec Positive s x\<^sub>i of
               Inl I \<Rightarrow> set_unsat I s
             | Inr x\<^sub>j \<Rightarrow> pivot_and_update x\<^sub>i x\<^sub>j (the (\<B>\<^sub>l s x\<^sub>i)) s)"
      apply (subst \<open>\<B>\<^sub>l s x\<^sub>i = LB Positive s x\<^sub>i\<close>)
      apply (rule check_sat_terminates'_aux[of Positive s x\<^sub>i])
      using \<open>\<nabla> s\<close> \<open>\<triangle> (\<T> s)\<close>  \<open>\<diamond> s\<close> \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s\<close> *
      using \<open>\<not> \<U> s\<close> \<open>Some x\<^sub>i = min_lvar_not_in_bounds s\<close> \<open>\<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i\<close>
      by (simp_all add: bound_compare''_defs)
  next
    fix x\<^sub>i
    assume "\<not> \<U> s" "Some x\<^sub>i = min_lvar_not_in_bounds s" "\<not> \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i"
    then have "\<langle>\<V> s\<rangle> x\<^sub>i >\<^sub>u\<^sub>b \<B>\<^sub>u s x\<^sub>i"
      using min_lvar_not_in_bounds_Some[of s x\<^sub>i]
      using neg_bounds_compare(7) neg_bounds_compare(2)
      by auto
    have "\<B>\<^sub>u s x\<^sub>i = LB Negative s x\<^sub>i"
      by simp
    show "check_dom
            (case min_rvar_incdec Negative s x\<^sub>i of
               Inl I \<Rightarrow> set_unsat I s
             | Inr x\<^sub>j \<Rightarrow> pivot_and_update x\<^sub>i x\<^sub>j (the (\<B>\<^sub>u s x\<^sub>i)) s)"
      apply (subst \<open>\<B>\<^sub>u s x\<^sub>i = LB Negative s x\<^sub>i\<close>)
      apply (rule check_sat_terminates'_aux)
      using \<open>\<nabla> s\<close> \<open>\<triangle> (\<T> s)\<close>  \<open>\<diamond> s\<close> \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s\<close> *
      using \<open>\<not> \<U> s\<close> \<open>Some x\<^sub>i = min_lvar_not_in_bounds s\<close> \<open>\<langle>\<V> s\<rangle> x\<^sub>i >\<^sub>u\<^sub>b \<B>\<^sub>u s x\<^sub>i\<close> \<open>\<not> \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i\<close>
      by (simp_all add: bound_compare''_defs)
  qed
qed

lemma check_sat_terminates:
  assumes "\<nabla> s" "\<triangle> (\<T> s)" "\<diamond> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"
  shows "check_dom s"
  using assms
  using check_sat_terminates'[of s s]
  by simp


lemma check_cases:
  assumes "\<U> s \<Longrightarrow> P s"
  assumes "\<lbrakk>\<not> \<U> s; min_lvar_not_in_bounds s = None\<rbrakk> \<Longrightarrow> P s"
  assumes "\<And> x\<^sub>i dir I.
    \<lbrakk>dir = Positive \<or> dir = Negative;
     \<not> \<U> s; min_lvar_not_in_bounds s = Some x\<^sub>i;
     \<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i);
     min_rvar_incdec dir s x\<^sub>i = Inl I\<rbrakk> \<Longrightarrow>
        P (set_unsat I s)"
  assumes "\<And> x\<^sub>i x\<^sub>j l\<^sub>i dir.
    \<lbrakk>dir = (if \<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i then Positive else Negative);
     \<not> \<U> s; min_lvar_not_in_bounds s = Some x\<^sub>i;
     \<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i);
     min_rvar_incdec dir s x\<^sub>i = Inr x\<^sub>j;
     l\<^sub>i = the (LB dir s x\<^sub>i);
     check' dir x\<^sub>i s = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s\<rbrakk> \<Longrightarrow>
        P (check (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s))"
  assumes "\<triangle> (\<T> s)" "\<diamond> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"
  shows "P (check s)"
proof (cases "\<U> s")
  case True
  then show ?thesis
    using assms(1)
    using check.simps[of s]
    by simp
next
  case False
  show ?thesis
  proof (cases "min_lvar_not_in_bounds s")
    case None
    then show ?thesis
      using \<open>\<not> \<U> s\<close>
      using assms(2) \<open>\<triangle> (\<T> s)\<close> \<open>\<diamond> s\<close> \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s\<close>
      using check.simps[of s]
      by simp
  next
    case (Some x\<^sub>i)
    let ?dir = "if (\<langle>\<V> s\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s x\<^sub>i) then (Positive :: ('i,'a)Direction) else Negative"
    let ?s' = "check' ?dir x\<^sub>i s"
    have "\<lhd>\<^sub>l\<^sub>b (lt ?dir) (\<langle>\<V> s\<rangle> x\<^sub>i)  (LB ?dir s x\<^sub>i)"
      using \<open>min_lvar_not_in_bounds s = Some x\<^sub>i\<close>
      using min_lvar_not_in_bounds_Some[of s x\<^sub>i]
      using not_in_bounds[of x\<^sub>i "\<langle>\<V> s\<rangle>" "\<B>\<^sub>l s" "\<B>\<^sub>u s"]
      by (auto split: if_splits simp add: bound_compare''_defs)

    have "P (check ?s')"
      apply (rule check'_cases)
      using \<open>\<not> \<U> s\<close> \<open>min_lvar_not_in_bounds s = Some x\<^sub>i\<close> \<open>\<lhd>\<^sub>l\<^sub>b (lt ?dir) (\<langle>\<V> s\<rangle> x\<^sub>i)  (LB ?dir s x\<^sub>i)\<close>
      using assms(3)[of ?dir x\<^sub>i]
      using assms(4)[of ?dir x\<^sub>i]
      using check.simps[of "set_unsat (_ :: 'i list) s"]
      using \<open>\<triangle> (\<T> s)\<close> \<open>\<diamond> s\<close> \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s\<close>
      by (auto simp add:  bounds_consistent_def  curr_val_satisfies_no_lhs_def)
    then show ?thesis
      using \<open>\<not> \<U> s\<close> \<open>min_lvar_not_in_bounds s = Some x\<^sub>i\<close>
      using check.simps[of s]
      using \<open>\<triangle> (\<T> s)\<close> \<open>\<diamond> s\<close> \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s\<close>
      by auto
  qed
qed


lemma check_induct:
  fixes s :: "('i,'a) state"
  assumes *: "\<nabla> s" "\<triangle> (\<T> s)" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s"
  assumes **:
    "\<And> s. \<U> s \<Longrightarrow> P s s"
    "\<And> s. \<lbrakk>\<not> \<U> s; min_lvar_not_in_bounds s = None\<rbrakk> \<Longrightarrow> P s s"
    "\<And> s x\<^sub>i dir I. \<lbrakk>dir = Positive \<or> dir = Negative; \<not> \<U> s; min_lvar_not_in_bounds s = Some x\<^sub>i;
      \<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i); min_rvar_incdec dir s x\<^sub>i = Inl I\<rbrakk>
     \<Longrightarrow> P s (set_unsat I s)"
  assumes step': "\<And> s x\<^sub>i x\<^sub>j l\<^sub>i. \<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i)\<rbrakk> \<Longrightarrow> P s (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s)"
  assumes trans': "\<And> si sj sk. \<lbrakk>P si sj; P sj sk\<rbrakk> \<Longrightarrow> P si sk"
  shows "P s (check s)"
proof-
  have "check_dom s"
    using *
    by (simp add: check_sat_terminates)
  then show ?thesis
    using *
  proof (induct s rule: check_dom.induct)
    case (step s')
    show ?case
    proof (rule check_cases)
      fix x\<^sub>i x\<^sub>j l\<^sub>i dir
      let ?dir = "if \<langle>\<V> s'\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s' x\<^sub>i then Positive else Negative"
      let ?s' = "check' dir x\<^sub>i s'"
      assume "\<not> \<U> s'" "min_lvar_not_in_bounds s' = Some x\<^sub>i" "min_rvar_incdec dir s' x\<^sub>i = Inr x\<^sub>j" "l\<^sub>i = the (LB dir s' x\<^sub>i)"
        "?s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'" "dir = ?dir"
      moreover
      then have "\<nabla> ?s'" "\<triangle> (\<T> ?s')" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?s'" "\<diamond> ?s'"
        using \<open>\<nabla> s'\<close> \<open>\<triangle> (\<T> s')\<close> \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'\<close> \<open>\<diamond> s'\<close>
        using \<open>?s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'\<close>
        using pivotandupdate_check_precond[of dir s' x\<^sub>i x\<^sub>j l\<^sub>i]
        by auto
      ultimately
      have "P (check' dir x\<^sub>i s') (check (check' dir x\<^sub>i s'))"
        using step(2)[of x\<^sub>i] step(4)[of x\<^sub>i] \<open>\<triangle> (\<T> s')\<close> \<open>\<nabla> s'\<close>
        by auto
      then show "P s' (check (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'))"
        using \<open>?s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'\<close> \<open>\<triangle> (\<T> s')\<close> \<open>\<nabla> s'\<close>
        using \<open>min_lvar_not_in_bounds s' = Some x\<^sub>i\<close> \<open>min_rvar_incdec dir s' x\<^sub>i = Inr x\<^sub>j\<close>
        using step'[of s' x\<^sub>i x\<^sub>j l\<^sub>i]
        using trans'[of s' ?s' "check ?s'"]
        by (auto simp add: min_lvar_not_in_bounds_lvars  min_rvar_incdec_eq_Some_rvars)
    qed (simp_all add: \<open>\<nabla> s'\<close> \<open>\<triangle> (\<T> s')\<close> \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'\<close> \<open>\<diamond> s'\<close> **)
  qed
qed

lemma check_induct':
  fixes s :: "('i,'a) state"
  assumes "\<nabla> s" "\<triangle> (\<T> s)" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s"
  assumes "\<And> s x\<^sub>i dir I. \<lbrakk>dir = Positive \<or> dir = Negative; \<not> \<U> s; min_lvar_not_in_bounds s = Some x\<^sub>i;
  \<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i); min_rvar_incdec dir s x\<^sub>i = Inl I; P s\<rbrakk>
    \<Longrightarrow> P (set_unsat I s)"
  assumes "\<And> s x\<^sub>i x\<^sub>j l\<^sub>i. \<lbrakk>\<triangle> (\<T> s); \<nabla> s; x\<^sub>i \<in> lvars (\<T> s); x\<^sub>j \<in> rvars_eq (eq_for_lvar (\<T> s) x\<^sub>i); P s\<rbrakk> \<Longrightarrow> P (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s)"
  assumes "P s"
  shows "P (check s)"
proof-
  have "P s \<longrightarrow> P (check s)"
    by (rule check_induct) (simp_all add: assms)
  then show ?thesis
    using \<open>P s\<close>
    by simp
qed

lemma check_induct'':
  fixes s :: "('i,'a) state"
  assumes *: "\<nabla> s" "\<triangle> (\<T> s)" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s"
  assumes **:
    "\<U> s \<Longrightarrow> P s"
    "\<And> s. \<lbrakk>\<nabla> s; \<triangle> (\<T> s); \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s; \<not> \<U> s; min_lvar_not_in_bounds s = None\<rbrakk> \<Longrightarrow> P s"
    "\<And> s x\<^sub>i dir I. \<lbrakk>dir = Positive \<or> dir = Negative; \<nabla> s; \<triangle> (\<T> s); \<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s; \<diamond> s;  \<not> \<U> s;
    min_lvar_not_in_bounds s = Some x\<^sub>i; \<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x\<^sub>i) (LB dir s x\<^sub>i);
    min_rvar_incdec dir s x\<^sub>i = Inl I\<rbrakk>
      \<Longrightarrow> P (set_unsat I s)"
  shows "P (check s)"
proof (cases "\<U> s")
  case True
  then show ?thesis
    using \<open>\<U> s \<Longrightarrow> P s\<close>
    by (simp add: check.simps)
next
  case False
  have "check_dom s"
    using *
    by (simp add: check_sat_terminates)
  then show ?thesis
    using * False
  proof (induct s rule: check_dom.induct)
    case (step s')
    show ?case
    proof (rule check_cases)
      fix x\<^sub>i x\<^sub>j l\<^sub>i dir
      let ?dir = "if \<langle>\<V> s'\<rangle> x\<^sub>i <\<^sub>l\<^sub>b \<B>\<^sub>l s' x\<^sub>i then Positive else Negative"
      let ?s' = "check' dir x\<^sub>i s'"
      assume "\<not> \<U> s'" "min_lvar_not_in_bounds s' = Some x\<^sub>i" "min_rvar_incdec dir s' x\<^sub>i = Inr x\<^sub>j" "l\<^sub>i = the (LB dir s' x\<^sub>i)"
        "?s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'" "dir = ?dir"
      moreover
      then have "\<nabla> ?s'" "\<triangle> (\<T> ?s')" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?s'" "\<diamond> ?s'" "\<not> \<U> ?s'"
        using \<open>\<nabla> s'\<close> \<open>\<triangle> (\<T> s')\<close> \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'\<close> \<open>\<diamond> s'\<close>
        using \<open>?s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'\<close>
        using pivotandupdate_check_precond[of dir s' x\<^sub>i x\<^sub>j l\<^sub>i]
        using pivotandupdate_unsat_id[of s' x\<^sub>i x\<^sub>j l\<^sub>i]
        by (auto simp add: min_lvar_not_in_bounds_lvars  min_rvar_incdec_eq_Some_rvars)
      ultimately
      have "P (check (check' dir x\<^sub>i s'))"
        using step(2)[of x\<^sub>i] step(4)[of x\<^sub>i] \<open>\<triangle> (\<T> s')\<close> \<open>\<nabla> s'\<close>
        by auto
      then show "P (check (pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'))"
        using \<open>?s' = pivot_and_update x\<^sub>i x\<^sub>j l\<^sub>i s'\<close>
        by simp
    qed (simp_all add: \<open>\<nabla> s'\<close> \<open>\<triangle> (\<T> s')\<close> \<open>\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'\<close> \<open>\<diamond> s'\<close> \<open>\<not> \<U> s'\<close> ** )
  qed
qed


end


lemma poly_eval_update: "(p \<lbrace> v ( x := c :: 'a :: lrv) \<rbrace>) = (p \<lbrace> v \<rbrace>) + coeff p x *R (c - v x)" 
proof (transfer, simp, goal_cases) 
  case (1 p v x c)
  hence fin: "finite {v. p v \<noteq> 0}" by simp
  have "(\<Sum>y\<in>{v. p v \<noteq> 0}. p y *R (if y = x then c else v y)) = 
    (\<Sum>y\<in>{v. p v \<noteq> 0} \<inter> {x}. p y *R (if y = x then c else v y))
    + (\<Sum>y\<in>{v. p v \<noteq> 0} \<inter> (UNIV - {x}). p y *R (if y = x then c else v y))"  (is "?l = ?a + ?b")
    by (subst sum.union_disjoint[symmetric], auto intro: sum.cong fin)
  also have "?a = (if p x = 0 then 0 else p x *R c)" by auto
  also have "\<dots> = p x *R c" by auto
  also have "?b = (\<Sum>y\<in>{v. p v \<noteq> 0} \<inter> (UNIV - {x}). p y *R v y)" (is "_ = ?c") by (rule sum.cong, auto)
  finally have l: "?l = p x *R c + ?c" .
  define r where "r = (\<Sum>y\<in>{v. p v \<noteq> 0}. p y *R v y) + p x *R (c - v x)" 
  have "r = (\<Sum>y\<in>{v. p v \<noteq> 0}. p y *R v y) + p x *R (c - v x)" by (simp add: r_def)
  also have "(\<Sum>y\<in>{v. p v \<noteq> 0}. p y *R v y) =
     (\<Sum>y\<in>{v. p v \<noteq> 0} \<inter> {x}. p y *R v y) + ?c" (is "_ = ?d + _") 
    by (subst sum.union_disjoint[symmetric], auto intro: sum.cong fin)
  also have "?d = (if p x = 0 then 0 else p x *R v x)" by auto
  also have "\<dots> = p x *R v x" by auto
  finally have "(p x *R (c - v x) + p x *R v x) + ?c = r" by simp
  also have "(p x *R (c - v x) + p x *R v x) = p x *R c" unfolding scaleRat_right_distrib[symmetric] by simp 
  finally have r: "p x *R c + ?c = r" .
  show ?case unfolding l r r_def ..
qed

context PivotUpdateMinVars
begin
context
  fixes rhs_eq_val :: "(var, 'a::lrv) mapping \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> eq \<Rightarrow> 'a" 
  assumes "RhsEqVal rhs_eq_val"
begin

lemma check_minimal_unsat_state_core:
  assumes *: "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s" "\<triangle> (\<T> s)" "\<nabla> s"
shows "\<U> (check s) \<longrightarrow> minimal_unsat_state_core (check s)" 
  (is "?P (check s)")
proof (rule check_induct'')
  fix s' :: "('i,'a) state" and x\<^sub>i dir I
  assume nolhs: "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'"
    and min_rvar: "min_rvar_incdec dir s' x\<^sub>i = Inl I"
    and sat: "\<not> \<U> s'"
    and min_lvar: "min_lvar_not_in_bounds s' = Some x\<^sub>i"
    and dir: "dir = Positive \<or> dir = Negative"
    and lt: "\<lhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s'\<rangle> x\<^sub>i) (LB dir s' x\<^sub>i)"
    and norm: "\<triangle> (\<T> s')" 
    and valuated: "\<nabla> s'" 
  let ?eq = "eq_for_lvar (\<T> s') x\<^sub>i" 
  have unsat_core: "set (the (\<U>\<^sub>c (set_unsat I s'))) = set I"
    by auto

  obtain l\<^sub>i where LB_Some: "LB dir s' x\<^sub>i = Some l\<^sub>i" and lt: "lt dir (\<langle>\<V> s'\<rangle> x\<^sub>i) l\<^sub>i"
    using lt by (cases "LB dir s' x\<^sub>i") (auto simp add: bound_compare_defs)

  from LB_Some dir obtain i where LBI: "look (LBI dir s') x\<^sub>i = Some (i,l\<^sub>i)" and LI: "LI dir s' x\<^sub>i = i"
    by (auto simp: simp: indexl_def indexu_def boundsl_def boundsu_def)

  from min_rvar_incdec_eq_None[OF min_rvar] dir
  have Is': "LI dir s' (lhs (eq_for_lvar (\<T> s') x\<^sub>i)) \<in> indices_state s' \<Longrightarrow> set I \<subseteq> indices_state s'" and
    reasable: "\<And> x. x \<in> rvars_eq ?eq \<Longrightarrow> \<not> reasable_var dir x ?eq s'" and
    setI: "set I =
        {LI dir s' (lhs ?eq)} \<union>
        {LI dir s' x |x. x \<in> rvars_eq ?eq \<and> coeff (rhs ?eq) x < 0} \<union>
        {UI dir s' x |x. x \<in> rvars_eq ?eq \<and> 0 < coeff (rhs ?eq) x}" (is "_ = ?L \<union> ?R1 \<union> ?R2")  by auto
  note setI also have id: "lhs ?eq = x\<^sub>i"
    by (simp add: EqForLVar.eq_for_lvar EqForLVar_axioms min_lvar min_lvar_not_in_bounds_lvars)
  finally have iI: "i \<in> set I" unfolding LI by auto
  note setI = setI[unfolded id]
  have "LI dir s' x\<^sub>i \<in> indices_state s'" using LBI LI
    unfolding indices_state_def using dir by force
  from Is'[unfolded id, OF this]
  have Is': "set I \<subseteq> indices_state s'" .

  have "x\<^sub>i \<in> lvars (\<T> s')"
    using min_lvar
    by (simp add: min_lvar_not_in_bounds_lvars)
  then have **: "?eq \<in> set (\<T> s')" "lhs ?eq = x\<^sub>i"
    by (auto simp add: eq_for_lvar)

  have Is': "set I \<subseteq> indices_state (set_unsat I s')"
    using Is' * unfolding indices_state_def by auto

  have "\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>t \<T> s'" and b: "\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>b \<B> s' \<parallel> - lvars (\<T> s')" 
    using nolhs[unfolded curr_val_satisfies_no_lhs_def] by auto
  from norm[unfolded normalized_tableau_def]
  have lvars_rvars: "lvars (\<T> s') \<inter> rvars (\<T> s') = {}" by auto
  hence in_bnds: "x \<in> rvars (\<T> s') \<Longrightarrow> in_bounds x \<langle>\<V> s'\<rangle> (\<B> s')" for x
    by (intro b[unfolded satisfies_bounds_set.simps, rule_format, of x], auto)
  {      
    assume dist: "distinct_indices_state (set_unsat I s')" 
    hence "distinct_indices_state s'" unfolding distinct_indices_state_def by auto
    note dist = this[unfolded distinct_indices_state_def, rule_format]
    {
      fix x c i y
      assume c: "look (\<B>\<^sub>i\<^sub>l s') x = Some (i,c) \<or> look (\<B>\<^sub>i\<^sub>u s') x = Some (i,c)" 
        and y: "y \<in> rvars_eq ?eq" and
        coeff: "coeff (rhs ?eq) y < 0 \<and> i = LI dir s' y \<or> coeff (rhs ?eq) y > 0 \<and> i = UI dir s' y" 
      {
        assume coeff: "coeff (rhs ?eq) y < 0" and i: "i = LI dir s' y" 
        from reasable[OF y] coeff have not_gt: "\<not> (\<rhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s'\<rangle> y) (LB dir s' y))" by auto
        then obtain d where LB: "LB dir s' y = Some d" using dir by (cases "LB dir s' y", auto simp: bound_compare_defs)
        with not_gt have le: "le (lt dir) (\<langle>\<V> s'\<rangle> y) d" using dir by (auto simp: bound_compare_defs)
        from LB have "look (LBI dir s') y = Some (i, d)" unfolding i using dir
          by (auto simp: boundsl_def boundsu_def indexl_def indexu_def)
        with c dist[of x i c y d] dir
        have yx: "y = x" "d = c" by auto
        from y[unfolded yx] have "x \<in> rvars (\<T> s')" using **(1) unfolding rvars_def by force
        from in_bnds[OF this] le LB not_gt i have "\<langle>\<V> s'\<rangle> x = c" unfolding yx using dir by auto
        note yx(1) this
      }
      moreover
      {
        assume coeff: "coeff (rhs ?eq) y > 0" and i: "i = UI dir s' y" 
        from reasable[OF y] coeff have not_gt: "\<not> (\<lhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> s'\<rangle> y) (UB dir s' y))" by auto
        then obtain d where UB: "UB dir s' y = Some d" using dir by (cases "UB dir s' y", auto simp: bound_compare_defs)
        with not_gt have le: "le (lt dir) d (\<langle>\<V> s'\<rangle> y)" using dir by (auto simp: bound_compare_defs)
        from UB have "look (UBI dir s') y = Some (i, d)" unfolding i using dir
          by (auto simp: boundsl_def boundsu_def indexl_def indexu_def)
        with c dist[of x i c y d] dir
        have yx: "y = x" "d = c" by auto
        from y[unfolded yx] have "x \<in> rvars (\<T> s')" using **(1) unfolding rvars_def by force
        from in_bnds[OF this] le UB not_gt i have "\<langle>\<V> s'\<rangle> x = c" unfolding yx using dir by auto
        note yx(1) this
      }
      ultimately have "y = x" "\<langle>\<V> s'\<rangle> x = c" using coeff by blast+
    } note x_vars_main = this
    {
      fix x c i
      assume c: "look (\<B>\<^sub>i\<^sub>l s') x = Some (i,c) \<or> look (\<B>\<^sub>i\<^sub>u s') x = Some (i,c)" and i: "i \<in> ?R1 \<union> ?R2" 
      from i obtain y where y: "y \<in> rvars_eq ?eq" and
        coeff: "coeff (rhs ?eq) y < 0 \<and> i = LI dir s' y \<or> coeff (rhs ?eq) y > 0 \<and> i = UI dir s' y" 
        by auto
      from x_vars_main[OF c y coeff] 
      have "y = x" "\<langle>\<V> s'\<rangle> x = c" using coeff by blast+
      with y have "x \<in> rvars_eq ?eq" "x \<in> rvars (\<T> s')" "\<langle>\<V> s'\<rangle> x = c" using **(1) unfolding rvars_def by force+       
    } note x_rvars = this

    have R1R2: "(?R1 \<union> ?R2, \<langle>\<V> s'\<rangle>) \<Turnstile>\<^sub>i\<^sub>s\<^sub>e s'" 
      unfolding satisfies_state_index'.simps
    proof (intro conjI)
      show "\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>t \<T> s'" by fact
      show "(?R1 \<union> ?R2, \<langle>\<V> s'\<rangle>) \<Turnstile>\<^sub>i\<^sub>b\<^sub>e \<B>\<I> s'" 
        unfolding satisfies_bounds_index'.simps 
      proof (intro conjI impI allI)
        fix x c
        assume c: "\<B>\<^sub>l s' x = Some c" and i: "\<I>\<^sub>l s' x \<in> ?R1 \<union> ?R2" 
        from c have ci: "look (\<B>\<^sub>i\<^sub>l s') x = Some (\<I>\<^sub>l s' x, c)" unfolding boundsl_def indexl_def by auto
        from x_rvars[OF _ i] ci show "\<langle>\<V> s'\<rangle> x  = c" by auto
      next
        fix x c
        assume c: "\<B>\<^sub>u s' x = Some c" and i: "\<I>\<^sub>u s' x \<in> ?R1 \<union> ?R2" 
        from c have ci: "look (\<B>\<^sub>i\<^sub>u s') x = Some (\<I>\<^sub>u s' x, c)" unfolding boundsu_def indexu_def by auto
        from x_rvars[OF _ i] ci show "\<langle>\<V> s'\<rangle> x = c" by auto
      qed
    qed

    have id1: "set (the (\<U>\<^sub>c (set_unsat I s'))) = set I" 
      "\<And> x. x \<Turnstile>\<^sub>i\<^sub>s\<^sub>e set_unsat I s' \<longleftrightarrow> x \<Turnstile>\<^sub>i\<^sub>s\<^sub>e s'" 
      by (auto simp: satisfies_state_index'.simps boundsl_def boundsu_def indexl_def indexu_def)

    have "subsets_sat_core (set_unsat I s')" unfolding subsets_sat_core_def id1
    proof (intro allI impI)
      fix J
      assume sub: "J \<subset> set I" 
      show "\<exists>v. (J, v) \<Turnstile>\<^sub>i\<^sub>s\<^sub>e s'" 
      proof (cases "J \<subseteq> ?R1 \<union> ?R2")
        case True
        with R1R2 have "(J, \<langle>\<V> s'\<rangle>) \<Turnstile>\<^sub>i\<^sub>s\<^sub>e s'" 
          unfolding satisfies_state_index'.simps satisfies_bounds_index'.simps by blast
        thus ?thesis by blast
      next
        case False
        with sub obtain k where k: "k \<in> ?R1 \<union> ?R2" "k \<notin> J" "k \<in> set I" unfolding setI by auto
        from k(1) obtain y where y: "y \<in> rvars_eq ?eq" 
          and coeff: "coeff (rhs ?eq) y < 0 \<and> k = LI dir s' y \<or> coeff (rhs ?eq) y > 0 \<and> k = UI dir s' y" by auto
        hence cy0: "coeff (rhs ?eq) y \<noteq> 0" by auto        
        from y **(1) have ry: "y \<in> rvars (\<T> s')" unfolding rvars_def by force      
        hence yl: "y \<notin> lvars (\<T> s')" using lvars_rvars by blast
        interpret rev: RhsEqVal rhs_eq_val by fact
        note update = rev.update_valuation_nonlhs[THEN mp, OF norm valuated yl]
        define diff where "diff = l\<^sub>i - \<langle>\<V> s'\<rangle> x\<^sub>i" 
        have "\<langle>\<V> s'\<rangle> x\<^sub>i < l\<^sub>i \<Longrightarrow> 0 < l\<^sub>i - \<langle>\<V> s'\<rangle> x\<^sub>i" "l\<^sub>i < \<langle>\<V> s'\<rangle> x\<^sub>i \<Longrightarrow> l\<^sub>i - \<langle>\<V> s'\<rangle> x\<^sub>i < 0" 
          using minus_gt by (blast, insert minus_lt, blast)
        with lt dir have diff: "lt dir 0 diff" by (auto simp: diff_def) 
        define up where "up = inverse (coeff (rhs ?eq) y) *R diff" 
        define v where "v = \<langle>\<V> (rev.update y (\<langle>\<V> s'\<rangle> y + up) s')\<rangle>" 
        show ?thesis unfolding satisfies_state_index'.simps
        proof (intro exI[of _ v] conjI)
          show "v \<Turnstile>\<^sub>t \<T> s'" unfolding v_def 
            using rev.update_satisfies_tableau[OF norm valuated yl] \<open>\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>t \<T> s'\<close> by auto
          with **(1) have "v \<Turnstile>\<^sub>e ?eq" unfolding satisfies_tableau_def by auto
          from this[unfolded satisfies_eq_def id]
          have v_xi: "v x\<^sub>i = (rhs ?eq \<lbrace> v \<rbrace>)" .  
          from \<open>\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>t \<T> s'\<close> **(1) have "\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>e ?eq" unfolding satisfies_tableau_def by auto
          hence V_xi: "\<langle>\<V> s'\<rangle> x\<^sub>i = (rhs ?eq \<lbrace> \<langle>\<V> s'\<rangle> \<rbrace>)" unfolding satisfies_eq_def id .
          have "v x\<^sub>i = \<langle>\<V> s'\<rangle> x\<^sub>i + coeff (rhs ?eq) y *R up" 
            unfolding v_xi unfolding v_def rev.update_valuate_rhs[OF **(1) norm] poly_eval_update V_xi by simp
          also have "\<dots> = l\<^sub>i" unfolding up_def diff_def scaleRat_scaleRat using cy0 by simp 
          finally have v_xi_l: "v x\<^sub>i = l\<^sub>i" .

          {
            assume both: "\<I>\<^sub>u s' y \<in> ?R1 \<union> ?R2" "\<B>\<^sub>u s' y \<noteq> None" "\<I>\<^sub>l s' y \<in> ?R1 \<union> ?R2" "\<B>\<^sub>l s' y \<noteq> None" 
              and diff: "\<I>\<^sub>l s' y \<noteq> \<I>\<^sub>u s' y"
            from both(1) dir obtain xu cu where 
              looku: "look (\<B>\<^sub>i\<^sub>l s') xu = Some (\<I>\<^sub>u s' y, cu) \<or> look (\<B>\<^sub>i\<^sub>u s') xu = Some (\<I>\<^sub>u s' y,cu)"
              by (smt Is' indices_state_def le_sup_iff mem_Collect_eq setI set_unsat_simps subsetCE)
            from both(1) obtain xu' where "xu' \<in> rvars_eq ?eq" "coeff (rhs ?eq) xu' < 0 \<and> \<I>\<^sub>u s' y = LI dir s' xu' \<or>
                   coeff (rhs ?eq) xu' > 0 \<and> \<I>\<^sub>u s' y = UI dir s' xu'" by blast
            with x_vars_main(1)[OF looku this] 
            have xu: "xu \<in> rvars_eq ?eq" "coeff (rhs ?eq) xu < 0 \<and> \<I>\<^sub>u s' y = LI dir s' xu \<or>
                   coeff (rhs ?eq) xu > 0 \<and> \<I>\<^sub>u s' y = UI dir s' xu" by auto
            {
              assume "xu \<noteq> y" 
              with dist[OF looku, of y] have "look (\<B>\<^sub>i\<^sub>u s') y = None" 
                by (cases "look (\<B>\<^sub>i\<^sub>u s') y", auto simp: boundsu_def indexu_def, blast)
              with both(2) have False by (simp add: boundsu_def)
            }
            hence xu_y: "xu = y" by blast
            from both(3) dir obtain xl cl where 
              lookl: "look (\<B>\<^sub>i\<^sub>l s') xl = Some (\<I>\<^sub>l s' y, cl) \<or> look (\<B>\<^sub>i\<^sub>u s') xl = Some (\<I>\<^sub>l s' y,cl)"
              by (smt Is' indices_state_def le_sup_iff mem_Collect_eq setI set_unsat_simps subsetCE)
            from both(3) obtain xl' where "xl' \<in> rvars_eq ?eq" "coeff (rhs ?eq) xl' < 0 \<and> \<I>\<^sub>l s' y = LI dir s' xl' \<or>
                   coeff (rhs ?eq) xl' > 0 \<and> \<I>\<^sub>l s' y = UI dir s' xl'" by blast
            with x_vars_main(1)[OF lookl this] 
            have xl: "xl \<in> rvars_eq ?eq" "coeff (rhs ?eq) xl < 0 \<and> \<I>\<^sub>l s' y = LI dir s' xl \<or>
                   coeff (rhs ?eq) xl > 0 \<and> \<I>\<^sub>l s' y = UI dir s' xl" by auto
            {
              assume "xl \<noteq> y" 
              with dist[OF lookl, of y] have "look (\<B>\<^sub>i\<^sub>l s') y = None" 
                by (cases "look (\<B>\<^sub>i\<^sub>l s') y", auto simp: boundsl_def indexl_def, blast)
              with both(4) have False by (simp add: boundsl_def)
            }
            hence xl_y: "xl = y" by blast
            from xu(2) xl(2) diff have diff: "xu \<noteq> xl" by auto
            with xu_y xl_y have False by simp
          } note both_y_False = this
          show "(J, v) \<Turnstile>\<^sub>i\<^sub>b\<^sub>e \<B>\<I> s'" unfolding satisfies_bounds_index'.simps
          proof (intro conjI allI impI)
            fix x c
            assume x: "\<B>\<^sub>l s' x = Some c" "\<I>\<^sub>l s' x \<in> J" 
            with k have not_k: "\<I>\<^sub>l s' x \<noteq> k" by auto
            from x have ci: "look (\<B>\<^sub>i\<^sub>l s') x = Some (\<I>\<^sub>l s' x, c)" unfolding boundsl_def indexl_def by auto
            show "v x = c" 
            proof (cases "\<I>\<^sub>l s' x = i")
              case False
              hence iR12: "\<I>\<^sub>l s' x \<in> ?R1 \<union> ?R2" using sub x unfolding setI LI by blast
              from x_rvars(2-3)[OF _ iR12] ci have xr: "x \<in> rvars (\<T> s')" and val: "\<langle>\<V> s'\<rangle> x = c" by auto
              with lvars_rvars have xl: "x \<notin> lvars (\<T> s')" by auto
              show ?thesis
              proof (cases "x = y")
                case False
                thus ?thesis using val unfolding v_def map2fun_def' update[OF xl] using val by auto
              next
                case True
                note coeff = coeff[folded True]
                from coeff not_k dir ci have Iu: "\<I>\<^sub>u s' x = k" by auto
                with ci Iu x(2) k sub False True
                have both: "\<I>\<^sub>u s' y \<in> ?R1 \<union> ?R2" "\<I>\<^sub>l s' y \<in> ?R1 \<union> ?R2" and diff: "\<I>\<^sub>l s' y \<noteq> \<I>\<^sub>u s' y" 
                  unfolding setI LI by auto
                have "\<B>\<^sub>l s' y \<noteq> None" using x True by simp
                from both_y_False[OF both(1) _ both(2) this diff]
                have "\<B>\<^sub>u s' y = None" by metis
                with reasable[OF y] dir coeff True 
                have "dir = Negative \<Longrightarrow> 0 < coeff (rhs ?eq) y" "dir = Positive \<Longrightarrow> 0 > coeff (rhs ?eq) y" by (auto simp: bound_compare_defs)
                with dir coeff[unfolded True] have "k = \<I>\<^sub>l s' y" by auto
                with diff Iu False True
                have False by auto
                thus ?thesis ..
              qed
            next
              case True
              from LBI ci[unfolded True] dir 
                dist[unfolded distinct_indices_state_def, rule_format, of x i c x\<^sub>i l\<^sub>i]
              have xxi: "x = x\<^sub>i" and c: "c = l\<^sub>i" by auto
              have vxi: "v x = l\<^sub>i" unfolding xxi v_xi_l ..
              thus ?thesis unfolding c by simp
            qed
          next
            fix x c
            assume x: "\<B>\<^sub>u s' x = Some c" "\<I>\<^sub>u s' x \<in> J" 
            with k have not_k: "\<I>\<^sub>u s' x \<noteq> k" by auto
            from x have ci: "look (\<B>\<^sub>i\<^sub>u s') x = Some (\<I>\<^sub>u s' x, c)" unfolding boundsu_def indexu_def by auto
            show "v x = c" 
            proof (cases "\<I>\<^sub>u s' x = i")
              case False
              hence iR12: "\<I>\<^sub>u s' x \<in> ?R1 \<union> ?R2" using sub x unfolding setI LI by blast
              from x_rvars(2-3)[OF _ iR12] ci have xr: "x \<in> rvars (\<T> s')" and val: "\<langle>\<V> s'\<rangle> x = c" by auto
              with lvars_rvars have xl: "x \<notin> lvars (\<T> s')" by auto
              show ?thesis
              proof (cases "x = y")
                case False
                thus ?thesis using val unfolding v_def map2fun_def' update[OF xl] using val by auto
              next
                case True
                note coeff = coeff[folded True]
                from coeff not_k dir ci have Iu: "\<I>\<^sub>l s' x = k" by auto
                with ci Iu x(2) k sub False True
                have both: "\<I>\<^sub>u s' y \<in> ?R1 \<union> ?R2" "\<I>\<^sub>l s' y \<in> ?R1 \<union> ?R2" and diff: "\<I>\<^sub>l s' y \<noteq> \<I>\<^sub>u s' y" 
                  unfolding setI LI by auto
                have "\<B>\<^sub>u s' y \<noteq> None" using x True by simp
                from both_y_False[OF both(1) this both(2) _ diff]
                have "\<B>\<^sub>l s' y = None" by metis
                with reasable[OF y] dir coeff True 
                have "dir = Negative \<Longrightarrow> 0 > coeff (rhs ?eq) y" "dir = Positive \<Longrightarrow> 0 < coeff (rhs ?eq) y" by (auto simp: bound_compare_defs)
                with dir coeff[unfolded True] have "k = \<I>\<^sub>u s' y" by auto
                with diff Iu False True
                have False by auto
                thus ?thesis ..
              qed
            next
              case True
              from LBI ci[unfolded True] dir 
                dist[unfolded distinct_indices_state_def, rule_format, of x i c x\<^sub>i l\<^sub>i]
              have xxi: "x = x\<^sub>i" and c: "c = l\<^sub>i" by auto
              have vxi: "v x = l\<^sub>i" unfolding xxi v_xi_l ..
              thus ?thesis unfolding c by simp
            qed
          qed
        qed
      qed
    qed
  } note minimal_core = this

  have unsat_core: "unsat_state_core (set_unsat I s')" 
    unfolding unsat_state_core_def unsat_core
  proof (intro impI conjI Is', clarify)
    fix v
    assume "(set I, v) \<Turnstile>\<^sub>i\<^sub>s set_unsat I s'"
    then have Iv: "(set I, v) \<Turnstile>\<^sub>i\<^sub>s s'"
      unfolding satisfies_state_index.simps
      by (auto simp: indexl_def indexu_def boundsl_def boundsu_def)
    from Iv have vt: "v \<Turnstile>\<^sub>t \<T> s'" and Iv: "(set I, v) \<Turnstile>\<^sub>i\<^sub>b \<B>\<I> s'"
      unfolding satisfies_state_index.simps by auto

    have lt_le_eq: "\<And> x y :: 'a. (x < y) \<longleftrightarrow> (x \<le> y \<and> x \<noteq> y)" by auto
    from Iv dir
    have lb: "\<And> x i c l. look (LBI dir s') x = Some (i,l) \<Longrightarrow> i \<in> set I \<Longrightarrow> le (lt dir) l (v x)"
      unfolding satisfies_bounds_index.simps
      by (auto simp: lt_le_eq indexl_def indexu_def boundsl_def boundsu_def)

    from lb[OF LBI iI] have li_x: "le (lt dir) l\<^sub>i (v x\<^sub>i)" .

    have "\<langle>\<V> s'\<rangle> \<Turnstile>\<^sub>e ?eq"
      using nolhs \<open>?eq \<in> set (\<T> s')\<close>
      unfolding curr_val_satisfies_no_lhs_def
      by (simp add: satisfies_tableau_def)
    then have "\<langle>\<V> s'\<rangle> x\<^sub>i = (rhs ?eq) \<lbrace> \<langle>\<V> s'\<rangle> \<rbrace>"
      using \<open>lhs ?eq = x\<^sub>i\<close>
      by (simp add: satisfies_eq_def)

    moreover

    have "v \<Turnstile>\<^sub>e ?eq"
      using vt \<open>?eq \<in> set (\<T> s')\<close>
      by (simp add: satisfies_state_def satisfies_tableau_def)
    then have "v x\<^sub>i = (rhs ?eq) \<lbrace> v \<rbrace>"
      using \<open>lhs ?eq = x\<^sub>i\<close>
      by (simp add: satisfies_eq_def)

    moreover

    have "\<unrhd>\<^sub>l\<^sub>b (lt dir) (v x\<^sub>i) (LB dir s' x\<^sub>i)"
      using li_x dir unfolding LB_Some by (auto simp: bound_compare'_defs)

    moreover

    from min_rvar_incdec_eq_None'[rule_format, OF dir min_rvar refl Iv]
    have "le (lt dir) (rhs (?eq) \<lbrace>v\<rbrace>) (rhs (?eq) \<lbrace> \<langle>\<V> s'\<rangle> \<rbrace>)" .

    ultimately

    show False
      using dir lt LB_Some
      by (auto simp add: bound_compare_defs)
  qed

  thus "\<U> (set_unsat I s') \<longrightarrow> minimal_unsat_state_core (set_unsat I s')" using minimal_core
    by (auto simp: minimal_unsat_state_core_def) 
qed (simp_all add: *)

lemma Check_check: "Check check" 
proof
  fix s :: "('i,'a) state"
  assume "\<U> s"
  then show "check s = s"
    by (simp add: check.simps)
next
  fix s :: "('i,'a) state" and v :: "'a valuation"
  assume *: "\<nabla> s" "\<triangle> (\<T> s)" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s"
  then have "v \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t \<T> (check s)"
    by (rule check_induct, simp_all add: pivotandupdate_tableau_equiv)
  moreover
  have "\<triangle> (\<T> (check s))"
    by (rule check_induct', simp_all add: * pivotandupdate_tableau_normalized)
  moreover
  have "\<nabla> (check s)"
  proof (rule check_induct', simp_all add: * pivotandupdate_tableau_valuated)
    fix s I
    show "\<nabla> s \<Longrightarrow> \<nabla> (set_unsat I s)"
      by (simp add: tableau_valuated_def)
  qed
  ultimately
  show "let s' = check s in v \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t \<T> s' \<and> \<triangle> (\<T> s') \<and> \<nabla> s'"
    by (simp add: Let_def)
next
  fix s :: "('i,'a) state"
  assume *: "\<nabla> s" "\<triangle> (\<T> s)" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s"
  from * show "\<B>\<^sub>i (check s) = \<B>\<^sub>i s"
    by (rule check_induct, simp_all add: pivotandupdate_bounds_id)
next
  fix s :: "('i,'a) state"
  assume *: "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s" "\<triangle> (\<T> s)" "\<nabla> s"
  have "\<not> \<U> (check s) \<longrightarrow> \<Turnstile> (check s)"
  proof (rule check_induct'', simp_all add: *)
    fix s
    assume "min_lvar_not_in_bounds s = None" "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s"
    then show " \<Turnstile> s"
      using min_lvar_not_in_bounds_None[of s]
      unfolding curr_val_satisfies_state_def satisfies_state_def
      unfolding curr_val_satisfies_no_lhs_def
      by (auto simp add: satisfies_bounds_set.simps satisfies_bounds.simps)
  qed
  then show "\<not> \<U> (check s) \<Longrightarrow> \<Turnstile> (check s)" by blast
next
  fix s :: "('i,'a) state"
  assume *: "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<diamond> s" "\<triangle> (\<T> s)" "\<nabla> s"
  have "\<U> (check s) \<longrightarrow> minimal_unsat_state_core (check s)"
    by (rule check_minimal_unsat_state_core[OF *])
  then show "\<U> (check s) \<Longrightarrow> minimal_unsat_state_core (check s)" by blast
qed
end
end

subsection\<open>Symmetries\<close>

text\<open>\label{sec:symmetries} Simplex algorithm exhibits many
symmetric cases. For example, \<open>assert_bound\<close> treats atoms
\<open>Leq x c\<close> and \<open>Geq x c\<close> in a symmetric manner, \<open>check_inc\<close> and \<open>check_dec\<close> are symmetric, etc. These
symmetric cases differ only in several aspects: order relations
between numbers (\<open><\<close> vs \<open>>\<close> and \<open>\<le>\<close> vs \<open>\<ge>\<close>), the role of lower and upper bounds (\<open>\<B>\<^sub>l\<close> vs
\<open>\<B>\<^sub>u\<close>) and their updating functions, comparisons with bounds
(e.g., \<open>\<ge>\<^sub>u\<^sub>b\<close> vs \<open>\<le>\<^sub>l\<^sub>b\<close> or
\<open><\<^sub>l\<^sub>b\<close> vs \<open>>\<^sub>u\<^sub>b\<close>), and atom constructors (\<open>Leq\<close>
and \<open>Geq\<close>). These can be attributed to two different
orientations (positive and negative) of rational axis. To avoid
duplicating definitions and proofs, \<open>assert_bound\<close> definition
cases for \<open>Leq\<close> and \<open>Geq\<close> are replaced by a call to a
newly introduced function parametrized by a \<open>Direction\<close> --- a
record containing minimal set of aspects listed above that differ in
two definition cases such that other aspects can be derived from them
(e.g., only \<open><\<close> need to be stored while \<open>\<le>\<close> can be
derived from it). Two constants of the type \<open>Direction\<close> are
defined: \<open>Positive\<close> (with \<open><\<close>, \<open>\<le>\<close> orders,
\<open>\<B>\<^sub>l\<close> for lower and \<open>\<B>\<^sub>u\<close> for upper bounds and their
corresponding updating functions, and \<open>Leq\<close> constructor) and
\<open>Negative\<close> (completely opposite from the previous
one). Similarly, \<open>check_inc\<close> and \<open>check_dec\<close> are
replaced by a new function \<open>check_incdec\<close> parametrized by a
\<open>Direction\<close>. All lemmas, previously repeated for each
symmetric instance, were replaced by a more abstract one, again
parametrized by a \<open>Direction\<close> parameter.
\vspace{-3mm}
\<close>

(*-------------------------------------------------------------------------- *)
subsection\<open>Concrete implementation\<close>
  (*-------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Init init_state *)
(* -------------------------------------------------------------------------- *)

text\<open>It is easy to give a concrete implementation of the initial
state constructor, which satisfies the specification of the @{term
Init} locale.  For example:\<close>
definition init_state :: "_ \<Rightarrow> ('i,'a :: zero)state" where
  "init_state t = State t Mapping.empty Mapping.empty (Mapping.tabulate (vars_list t) (\<lambda> v. 0)) False None"

interpretation Init "init_state :: _ \<Rightarrow> ('i,'a :: lrv)state"
proof
  fix t
  let ?init = "init_state t :: ('i,'a)state"
  show "\<langle>\<V> ?init\<rangle> \<Turnstile>\<^sub>t t"
    unfolding satisfies_tableau_def satisfies_eq_def
  proof (safe)
    fix l r
    assume "(l, r) \<in> set t"
    then have "l \<in> set (vars_list t)" "vars r \<subseteq> set (vars_list t)"
      by (auto simp: set_vars_list) (transfer, force)
    then have *: "vars r \<subseteq> lhs ` set t \<union> (\<Union>x\<in>set t. rvars_eq x)" by (auto simp: set_vars_list)
    have "\<langle>\<V> ?init\<rangle> l = (0::'a)"
      using \<open>l \<in> set (vars_list t)\<close>
      unfolding init_state_def by (auto simp: map2fun_def lookup_tabulate)
    moreover
    have "r \<lbrace> \<langle>\<V> ?init\<rangle> \<rbrace> = (0::'a)" using *
    proof (transfer fixing: t, goal_cases)
      case (1 r)
      {
        fix x
        assume "x\<in>{v. r v \<noteq> 0}"
        then have "r x *R \<langle>\<V> ?init\<rangle> x = (0::'a)"
          using 1
          unfolding init_state_def
          by (auto simp add: map2fun_def lookup_tabulate comp_def restrict_map_def set_vars_list Abstract_Linear_Poly.vars_def)
      }
      then show ?case by auto
    qed
    ultimately
    show "\<langle>\<V> ?init\<rangle> (lhs (l, r)) = rhs (l, r) \<lbrace> \<langle>\<V> ?init\<rangle> \<rbrace>"
      by auto
  qed
next
  fix t
  show "\<nabla> (init_state t)"
    unfolding init_state_def
    by (auto simp add: lookup_tabulate tableau_valuated_def comp_def restrict_map_def set_vars_list lvars_def rvars_def)
qed (simp_all add: init_state_def add: boundsl_def boundsu_def indexl_def indexu_def)


(* -------------------------------------------------------------------------- *)
(* MinVars min_lvar_not_in_bounds min_rvar_incdec_eq *)
(* -------------------------------------------------------------------------- *)
definition min_lvar_not_in_bounds :: "('i,'a::{linorder,zero}) state \<Rightarrow> var option" where
  "min_lvar_not_in_bounds s \<equiv>
      min_satisfying  (\<lambda> x. \<not> in_bounds x (\<langle>\<V> s\<rangle>) (\<B> s)) (map lhs (\<T> s))"

interpretation MinLVarNotInBounds "min_lvar_not_in_bounds :: ('i,'a::lrv) state \<Rightarrow> _"
proof
  fix s::"('i,'a) state"
  show "min_lvar_not_in_bounds s = None \<longrightarrow>
        (\<forall>x\<in>lvars (\<T> s). in_bounds x (\<langle>\<V> s\<rangle>) (\<B> s))"
    unfolding min_lvar_not_in_bounds_def lvars_def
    using min_satisfying_None
    by blast
next
  fix s x\<^sub>i
  show "min_lvar_not_in_bounds s = Some x\<^sub>i \<longrightarrow> 
            x\<^sub>i \<in> lvars (\<T> s) \<and>
            \<not> in_bounds x\<^sub>i \<langle>\<V> s\<rangle> (\<B> s) \<and>
            (\<forall>x\<in>lvars (\<T> s). x < x\<^sub>i \<longrightarrow> in_bounds x \<langle>\<V> s\<rangle> (\<B> s))"
    unfolding min_lvar_not_in_bounds_def lvars_def
    using min_satisfying_Some
    by blast+
qed

\<comment> \<open>all variables in vs have either a positive or a negative coefficient, so no equal-zero test required.\<close>
definition unsat_indices :: "('i,'a :: linorder) Direction \<Rightarrow> ('i,'a) state \<Rightarrow> var list \<Rightarrow> eq \<Rightarrow> 'i list" where
  "unsat_indices dir s vs eq = (let r = rhs eq; li = LI dir s; ui = UI dir s in
       remdups (li (lhs eq) # map (\<lambda> x. if coeff r x < 0 then li x else ui x) vs))"

definition min_rvar_incdec_eq :: "('i,'a) Direction \<Rightarrow> ('i,'a::lrv) state \<Rightarrow> eq \<Rightarrow> 'i list + var" where
  "min_rvar_incdec_eq dir s eq = (let rvars = Abstract_Linear_Poly.vars_list (rhs eq)
      in case min_satisfying (\<lambda> x. reasable_var dir x eq s) rvars of
         None \<Rightarrow> Inl (unsat_indices dir s rvars eq)
      | Some x\<^sub>j \<Rightarrow> Inr x\<^sub>j)"

interpretation MinRVarsEq "min_rvar_incdec_eq :: ('i,'a :: lrv) Direction \<Rightarrow> _"
proof
  fix s eq "is" and dir :: "('i,'a) Direction"
  let ?min = "min_satisfying (\<lambda> x. reasable_var dir x eq s) (Abstract_Linear_Poly.vars_list (rhs eq))"
  let ?vars = "Abstract_Linear_Poly.vars_list (rhs eq)"
  {
    assume "min_rvar_incdec_eq dir s eq = Inl is"
    from this[unfolded min_rvar_incdec_eq_def Let_def, simplified]
    have "?min = None" and I: "set is = set (unsat_indices dir s ?vars eq)" by (cases ?min, auto)+
    from this min_satisfying_None set_vars_list
    have 1: "\<And> x. x \<in> rvars_eq eq \<Longrightarrow> \<not> reasable_var dir x eq s" by blast
    {
      fix i
      assume "i \<in> set is" and dir: "dir = Positive \<or> dir = Negative" and lhs_eq: "LI dir s (lhs eq) \<in> indices_state s"
      from this[unfolded I unsat_indices_def Let_def]
      consider (lhs) "i = LI dir s (lhs eq)"
        | (LI_rhs) x where "i = LI dir s x" "x \<in> rvars_eq eq" "coeff (rhs eq) x < 0"
        | (UI_rhs) x where "i = UI dir s x" "x \<in> rvars_eq eq" "coeff (rhs eq) x \<ge> 0"
        by (auto split: if_splits simp: set_vars_list)
      then have "i \<in> indices_state s"
      proof cases
        case lhs
        show ?thesis unfolding lhs using lhs_eq by auto
      next
        case LI_rhs
        from 1[OF LI_rhs(2)] LI_rhs(3)
        have "\<not> (\<rhd>\<^sub>l\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (LB dir s x))" by auto
        then show ?thesis unfolding LI_rhs(1) unfolding indices_state_def using dir
          by (auto simp: bound_compare'_defs boundsl_def boundsu_def indexl_def indexu_def
              split: option.splits intro!: exI[of _ x]) auto
      next
        case UI_rhs
        from UI_rhs(2) have "coeff (rhs eq) x \<noteq> 0"
          by (simp add: coeff_zero)
        with UI_rhs(3) have "0 < coeff (rhs eq) x" by auto
        from 1[OF UI_rhs(2)] this have "\<not> (\<lhd>\<^sub>u\<^sub>b (lt dir) (\<langle>\<V> s\<rangle> x) (UB dir s x))" by auto
        then show ?thesis unfolding UI_rhs(1) unfolding indices_state_def using dir
          by (auto simp: bound_compare'_defs boundsl_def boundsu_def indexl_def indexu_def
              split: option.splits intro!: exI[of _ x]) auto
      qed
    }
    then have 2: "dir = Positive \<or> dir = Negative \<Longrightarrow> LI dir s (lhs eq) \<in> indices_state s \<Longrightarrow>
      set is \<subseteq> indices_state s" by auto
    show "
    (\<forall> x \<in> rvars_eq eq. \<not> reasable_var dir x eq s) \<and> set is =
       {LI dir s (lhs eq)} \<union> {LI dir s x |x. x \<in> rvars_eq eq \<and> 
         coeff (rhs eq) x < 0} \<union> {UI dir s x |x. x \<in> rvars_eq eq \<and> 0 < coeff (rhs eq) x} \<and>
       (dir = Positive \<or> dir = Negative \<longrightarrow> LI dir s (lhs eq) \<in> indices_state s \<longrightarrow> set is \<subseteq> indices_state s)"
    proof (intro conjI impI 2, goal_cases)
      case 2
      have "set is = {LI dir s (lhs eq)} \<union> LI dir s ` (rvars_eq eq \<inter> {x. coeff (rhs eq) x < 0}) \<union> UI dir s ` (rvars_eq eq \<inter> {x. \<not> coeff (rhs eq) x < 0})" 
        unfolding I unsat_indices_def Let_def 
        by (auto simp add: set_vars_list) 
      also have "\<dots> = {LI dir s (lhs eq)} \<union> LI dir s ` {x. x \<in> rvars_eq eq \<and> coeff (rhs eq) x < 0} 
       \<union> UI dir s ` { x. x \<in> rvars_eq eq \<and> 0 < coeff (rhs eq) x}"
      proof (intro arg_cong2[of _ _ _ _ "(\<union>)"] arg_cong[of _ _ "\<lambda> x. _ ` x"] refl, goal_cases)
        case 2
        {
          fix x
          assume "x \<in> rvars_eq eq"
          hence "coeff (rhs eq) x \<noteq> 0" 
            by (simp add: coeff_zero)
          hence or: "coeff (rhs eq) x < 0 \<or> coeff (rhs eq) x > 0" by auto
          assume "\<not> coeff (rhs eq) x < 0" 
          hence "coeff (rhs eq) x > 0" using or by simp
        } note [dest] = this
        show ?case by auto
      qed auto
      finally
      show "set is = {LI dir s (lhs eq)} \<union> {LI dir s x |x. x \<in> rvars_eq eq \<and> coeff (rhs eq) x < 0} 
       \<union> {UI dir s x |x. x \<in> rvars_eq eq \<and> 0 < coeff (rhs eq) x}" by auto
    qed (insert 1, auto)
  }
  fix x\<^sub>j
  assume "min_rvar_incdec_eq dir s eq = Inr x\<^sub>j"
  from this[unfolded min_rvar_incdec_eq_def Let_def]
  have "?min = Some x\<^sub>j" by (cases ?min, auto)
  then show "x\<^sub>j \<in> rvars_eq eq" "reasable_var dir x\<^sub>j eq s"
    "(\<forall> x' \<in> rvars_eq eq. x' < x\<^sub>j \<longrightarrow> \<not> reasable_var dir x' eq s)"
    using min_satisfying_Some set_vars_list by blast+
qed

(* -------------------------------------------------------------------------- *)
(* EqForLVar eq_idx_for_lvar *)
(* -------------------------------------------------------------------------- *)

primrec eq_idx_for_lvar_aux :: "tableau \<Rightarrow> var \<Rightarrow> nat \<Rightarrow> nat" where
  "eq_idx_for_lvar_aux [] x i = i"
| "eq_idx_for_lvar_aux (eq # t) x i =
     (if lhs eq = x then i else eq_idx_for_lvar_aux t x (i+1))"

definition eq_idx_for_lvar where
  "eq_idx_for_lvar t x \<equiv> eq_idx_for_lvar_aux t x 0"

lemma eq_idx_for_lvar_aux:
  assumes "x \<in> lvars t"
  shows "let idx = eq_idx_for_lvar_aux t x i in
            i \<le> idx \<and> idx < i + length t \<and> lhs (t ! (idx - i)) = x"
  using assms
proof (induct t arbitrary: i)
  case Nil
  then show ?case
    by (simp add: lvars_def)
next
  case (Cons eq t)
  show ?case
    using Cons(1)[of "i+1"] Cons(2)
    by (cases "x = lhs eq") (auto simp add: Let_def lvars_def nth_Cons')
qed

global_interpretation EqForLVarDefault: EqForLVar eq_idx_for_lvar
  defines eq_for_lvar_code = EqForLVarDefault.eq_for_lvar
proof (unfold_locales)
  fix x t
  assume "x \<in> lvars t"
  then show "eq_idx_for_lvar t x < length t \<and>
          lhs (t ! eq_idx_for_lvar t x) = x"
    using eq_idx_for_lvar_aux[of x t 0]
    by (simp add: Let_def  eq_idx_for_lvar_def)
qed

(* -------------------------------------------------------------------------- *)
(* PivotEq pivot_eq *)
(* -------------------------------------------------------------------------- *)

definition pivot_eq :: "eq \<Rightarrow> var \<Rightarrow> eq" where
  "pivot_eq e y \<equiv> let cy = coeff (rhs e) y in
     (y, (-1/cy) *R ((rhs e) - cy *R (Var y)) + (1/cy) *R (Var (lhs e)))"

lemma pivot_eq_satisfies_eq:
  assumes "y \<in> rvars_eq e"
  shows "v \<Turnstile>\<^sub>e e = v \<Turnstile>\<^sub>e pivot_eq e y"
  using assms
  using scaleRat_right_distrib[of "1 / Rep_linear_poly (rhs e) y" "- (rhs e \<lbrace> v \<rbrace>)" "v (lhs e)"]
  using Groups.group_add_class.minus_unique[of "- ((rhs e) \<lbrace> v \<rbrace>)" "v (lhs e)"]
  unfolding coeff_def vars_def
  by (simp add: coeff_def vars_def Let_def pivot_eq_def satisfies_eq_def)
    (auto simp add: rational_vector.scale_right_diff_distrib valuate_add valuate_minus valuate_uminus valuate_scaleRat valuate_Var)

lemma pivot_eq_rvars:
  assumes "x \<in> vars (rhs (pivot_eq e v))" "x \<noteq> lhs e" "coeff (rhs e) v \<noteq> 0" "v \<noteq> lhs e"
  shows "x \<in> vars (rhs e)"
proof-
  have "v \<notin> vars ((1 / coeff (rhs e) v) *R (rhs e - coeff (rhs e) v *R Var v))"
    using coeff_zero
    by force
  then have "x \<noteq> v"
    using assms(1) assms(3) assms(4)
    using vars_plus[of "(-1 / coeff (rhs e) v) *R (rhs e - coeff (rhs e) v *R Var v)" "(1 / coeff (rhs e) v) *R Var (lhs e)"]
    by (auto simp add: Let_def vars_scaleRat pivot_eq_def)
  then show ?thesis
    using assms
    using vars_plus[of "(-1 / coeff (rhs e) v) *R (rhs e - coeff (rhs e) v *R Var v)" "(1 / coeff (rhs e) v) *R Var (lhs e)"]
    using vars_minus[of "rhs e" "coeff (rhs e) v *R Var v"]
    by (auto simp add: vars_scaleRat Let_def pivot_eq_def)
qed

interpretation PivotEq pivot_eq
proof
  fix eq x\<^sub>j
  assume "x\<^sub>j \<in> rvars_eq eq" "lhs eq \<notin> rvars_eq eq"
  have "lhs (pivot_eq eq x\<^sub>j) = x\<^sub>j"
    unfolding pivot_eq_def
    by (simp add: Let_def)
  moreover
  have "rvars_eq (pivot_eq eq x\<^sub>j) =
          {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})"
  proof
    show "rvars_eq (pivot_eq eq x\<^sub>j) \<subseteq> {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})"
    proof
      fix x
      assume "x \<in> rvars_eq (pivot_eq eq x\<^sub>j)"
      have *: "coeff (rhs (pivot_eq eq x\<^sub>j)) x\<^sub>j = 0"
        using \<open>x\<^sub>j \<in> rvars_eq eq\<close> \<open>lhs eq \<notin> rvars_eq eq\<close>
        using coeff_Var2[of "lhs eq" x\<^sub>j]
        by (auto simp add: Let_def pivot_eq_def)
      have "coeff (rhs eq) x\<^sub>j \<noteq> 0"
        using \<open>x\<^sub>j \<in> rvars_eq eq\<close>
        using coeff_zero
        by (cases eq) (auto simp add:)
      then show "x \<in> {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})"
        using pivot_eq_rvars[of x eq x\<^sub>j]
        using \<open>x \<in> rvars_eq (pivot_eq eq x\<^sub>j)\<close> \<open>x\<^sub>j \<in> rvars_eq eq\<close> \<open>lhs eq \<notin> rvars_eq eq\<close>
        using coeff_zero *
        by auto
    qed
    show "{lhs eq} \<union> (rvars_eq eq - {x\<^sub>j}) \<subseteq> rvars_eq (pivot_eq eq x\<^sub>j)"
    proof
      fix x
      assume "x \<in> {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})"
      have *: "coeff (rhs eq) (lhs eq) = 0"
        using coeff_zero
        using \<open>lhs eq \<notin> rvars_eq eq\<close>
        by auto
      have **: "coeff (rhs eq) x\<^sub>j \<noteq> 0"
        using \<open>x\<^sub>j \<in> rvars_eq eq\<close>
        by (simp add: coeff_zero)
      have ***: "x \<in> rvars_eq eq \<Longrightarrow> coeff (Var (lhs eq)) x = 0"
        using \<open>lhs eq \<notin> rvars_eq eq\<close>
        using coeff_Var2[of "lhs eq" x]
        by auto
      have "coeff (Var x\<^sub>j) (lhs eq) = 0"
        using \<open>x\<^sub>j \<in> rvars_eq eq\<close> \<open>lhs eq \<notin> rvars_eq eq\<close>
        using coeff_Var2[of x\<^sub>j "lhs eq"]
        by auto
      then have "coeff (rhs (pivot_eq eq x\<^sub>j)) x \<noteq> 0"
        using \<open>x \<in> {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})\<close> * ** ***
        using coeff_zero[of "rhs eq" x]
        by (auto simp add: Let_def coeff_Var2 pivot_eq_def)
      then show "x \<in> rvars_eq (pivot_eq eq x\<^sub>j)"
        by (simp add: coeff_zero)
    qed
  qed
  ultimately
  show "let eq' = pivot_eq eq x\<^sub>j in lhs eq' = x\<^sub>j \<and> rvars_eq eq' = {lhs eq} \<union> (rvars_eq eq - {x\<^sub>j})"
    by (simp add: Let_def)
next
  fix v eq x\<^sub>j
  assume "x\<^sub>j \<in> rvars_eq eq"
  then show "v \<Turnstile>\<^sub>e pivot_eq eq x\<^sub>j = v \<Turnstile>\<^sub>e eq"
    using pivot_eq_satisfies_eq
    by blast
qed

(* -------------------------------------------------------------------------- *)
(* SubstVar subst_var  *)
(* -------------------------------------------------------------------------- *)

definition subst_var:: "var \<Rightarrow> linear_poly \<Rightarrow> linear_poly \<Rightarrow> linear_poly" where
  "subst_var v lp' lp \<equiv> lp + (coeff lp v) *R lp' - (coeff lp v) *R (Var v)"

definition "subst_var_eq_code = SubstVar.subst_var_eq subst_var"

global_interpretation SubstVar subst_var rewrites
  "SubstVar.subst_var_eq subst_var = subst_var_eq_code"
proof (unfold_locales)
  fix x\<^sub>j lp' lp
  have *: "\<And>x. \<lbrakk>x \<in> vars (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j); x \<notin> vars lp'\<rbrakk> \<Longrightarrow> x \<in> vars lp"
  proof-
    fix x
    assume "x \<in> vars (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j)"
    then have "coeff (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j) x \<noteq> 0"
      using coeff_zero
      by force
    assume "x \<notin> vars lp'"
    then have "coeff lp' x = 0"
      using coeff_zero
      by auto
    show "x \<in> vars lp"
    proof(rule ccontr)
      assume "x \<notin> vars lp"
      then have "coeff lp x = 0"
        using coeff_zero
        by auto
      then show False
        using \<open>coeff (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j) x \<noteq> 0\<close>
        using \<open>coeff lp' x = 0\<close>
        by (cases "x = x\<^sub>j") (auto simp add: coeff_Var2)
    qed
  qed
  have "vars (subst_var x\<^sub>j lp' lp) \<subseteq> (vars lp - {x\<^sub>j}) \<union> vars lp'"
    unfolding subst_var_def
    using coeff_zero[of "lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j" x\<^sub>j]
    using coeff_zero[of lp' x\<^sub>j]
    using *
    by auto
  moreover
  have "\<And>x. \<lbrakk>x \<notin> vars (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j); x \<in> vars lp; x \<notin> vars lp'\<rbrakk> \<Longrightarrow> x = x\<^sub>j"
  proof-
    fix x
    assume "x \<in> vars lp" "x \<notin> vars lp'"
    then have "coeff lp x \<noteq> 0" "coeff lp' x = 0"
      using coeff_zero
      by auto
    assume "x \<notin> vars (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j)"
    then have "coeff (lp + coeff lp x\<^sub>j *R lp' - coeff lp x\<^sub>j *R Var x\<^sub>j) x = 0"
      using coeff_zero
      by force
    then show "x = x\<^sub>j"
      using \<open>coeff lp x \<noteq> 0\<close> \<open>coeff lp' x = 0\<close>
      by (cases "x = x\<^sub>j") (auto simp add: coeff_Var2)
  qed
  then have "vars lp - {x\<^sub>j} - vars lp' \<subseteq> vars (subst_var x\<^sub>j lp' lp)"
    by (auto simp add: subst_var_def)
  ultimately show "vars lp - {x\<^sub>j} - vars lp' \<subseteq>s vars (subst_var x\<^sub>j lp' lp)
       \<subseteq>s vars lp - {x\<^sub>j} \<union> vars lp'"
    by simp
next
  fix v x\<^sub>j lp' lp
  show "v x\<^sub>j = lp' \<lbrace> v \<rbrace> \<longrightarrow> lp \<lbrace> v \<rbrace> = (subst_var x\<^sub>j lp' lp) \<lbrace> v \<rbrace>"
    unfolding subst_var_def
    using valuate_minus[of "lp + coeff lp x\<^sub>j *R lp'" "coeff lp x\<^sub>j *R Var x\<^sub>j" v]
    using valuate_add[of lp "coeff lp x\<^sub>j *R lp'" v]
    using valuate_scaleRat[of "coeff lp x\<^sub>j" lp' v] valuate_scaleRat[of "coeff lp x\<^sub>j" "Var x\<^sub>j" v]
    using valuate_Var[of x\<^sub>j v]
    by auto
next
  fix x\<^sub>j lp lp'
  assume "x\<^sub>j \<notin> vars lp" 
  hence 0: "coeff lp x\<^sub>j = 0" using coeff_zero by blast
  show "subst_var x\<^sub>j lp' lp = lp" 
    unfolding subst_var_def 0 by simp
next
  fix x\<^sub>j lp x lp'
  assume "x\<^sub>j \<in> vars lp" "x \<in> vars lp' - vars lp" 
  hence x: "x \<noteq> x\<^sub>j" and 0: "coeff lp x = 0" and no0: "coeff lp x\<^sub>j \<noteq> 0" "coeff lp' x \<noteq> 0" 
    using coeff_zero by blast+
  from x have 00: "coeff (Var x\<^sub>j) x = 0" using coeff_Var2 by auto
  show "x \<in> vars (subst_var x\<^sub>j lp' lp)" 
    unfolding subst_var_def coeff_zero[symmetric]
    by (simp add: 0 00 no0)
qed (simp_all add: subst_var_eq_code_def)

(* -------------------------------------------------------------------------- *)
(* Update update  *)
(* -------------------------------------------------------------------------- *)

definition rhs_eq_val where
  "rhs_eq_val v x\<^sub>i c e \<equiv> let x\<^sub>j = lhs e; a\<^sub>i\<^sub>j = coeff (rhs e) x\<^sub>i in
      \<langle>v\<rangle> x\<^sub>j + a\<^sub>i\<^sub>j *R (c - \<langle>v\<rangle> x\<^sub>i)"

definition "update_code = RhsEqVal.update rhs_eq_val"
definition "assert_bound'_code = Update.assert_bound' update_code"
definition "assert_bound_code = Update.assert_bound update_code"

global_interpretation RhsEqValDefault': RhsEqVal rhs_eq_val
  rewrites
    "RhsEqVal.update rhs_eq_val = update_code" and
    "Update.assert_bound update_code = assert_bound_code" and
    "Update.assert_bound' update_code = assert_bound'_code"
proof unfold_locales
  fix v x c e
  assume "\<langle>v\<rangle> \<Turnstile>\<^sub>e e"
  then show "rhs_eq_val v x c e = rhs e \<lbrace> \<langle>v\<rangle>(x := c) \<rbrace>"
    unfolding rhs_eq_val_def Let_def
    using valuate_update_x[of "rhs e" x "\<langle>v\<rangle>" "\<langle>v\<rangle>(x := c)"]
    by (auto simp add: satisfies_eq_def)
qed (auto simp: update_code_def assert_bound'_code_def assert_bound_code_def)

sublocale PivotUpdateMinVars < Check check
proof (rule Check_check)
  show "RhsEqVal rhs_eq_val" ..
qed

definition "pivot_code = Pivot'.pivot eq_idx_for_lvar pivot_eq subst_var"
definition "pivot_tableau_code = Pivot'.pivot_tableau eq_idx_for_lvar pivot_eq subst_var"

global_interpretation Pivot'Default: Pivot' eq_idx_for_lvar pivot_eq subst_var
  rewrites
    "Pivot'.pivot eq_idx_for_lvar pivot_eq subst_var = pivot_code" and
    "Pivot'.pivot_tableau eq_idx_for_lvar pivot_eq subst_var = pivot_tableau_code" and
    "SubstVar.subst_var_eq subst_var = subst_var_eq_code"
  by (unfold_locales, auto simp: pivot_tableau_code_def pivot_code_def subst_var_eq_code_def)

definition "pivot_and_update_code = PivotUpdate.pivot_and_update pivot_code update_code"

global_interpretation PivotUpdateDefault: PivotUpdate eq_idx_for_lvar pivot_code update_code
  rewrites
    "PivotUpdate.pivot_and_update pivot_code update_code = pivot_and_update_code"
  by (unfold_locales, auto simp: pivot_and_update_code_def)

sublocale Update < AssertBoundNoLhs assert_bound
proof (rule update_to_assert_bound_no_lhs)
  show "Pivot eq_idx_for_lvar pivot_code" ..
qed

definition "check_code = PivotUpdateMinVars.check eq_idx_for_lvar min_lvar_not_in_bounds min_rvar_incdec_eq pivot_and_update_code"
definition "check'_code = PivotUpdateMinVars.check' eq_idx_for_lvar min_rvar_incdec_eq pivot_and_update_code"

global_interpretation PivotUpdateMinVarsDefault: PivotUpdateMinVars eq_idx_for_lvar min_lvar_not_in_bounds min_rvar_incdec_eq pivot_and_update_code
  rewrites
    "PivotUpdateMinVars.check eq_idx_for_lvar min_lvar_not_in_bounds min_rvar_incdec_eq pivot_and_update_code = check_code" and
    "PivotUpdateMinVars.check' eq_idx_for_lvar min_rvar_incdec_eq pivot_and_update_code = check'_code"
  by (unfold_locales) (simp_all add: check_code_def check'_code_def)


definition "assert_code = Assert'.assert assert_bound_code check_code"

global_interpretation Assert'Default: Assert' assert_bound_code check_code
  rewrites
    "Assert'.assert assert_bound_code check_code = assert_code"
  by (unfold_locales, auto simp: assert_code_def)

definition "assert_bound_loop_code = AssertAllState''.assert_bound_loop assert_bound_code"
definition "assert_all_state_code = AssertAllState''.assert_all_state init_state assert_bound_code check_code"
definition "assert_all_code = AssertAllState.assert_all assert_all_state_code"

global_interpretation AssertAllStateDefault: AssertAllState'' init_state assert_bound_code check_code
  rewrites
    "AssertAllState''.assert_bound_loop assert_bound_code = assert_bound_loop_code" and
    "AssertAllState''.assert_all_state init_state assert_bound_code check_code = assert_all_state_code" and
    "AssertAllState.assert_all assert_all_state_code = assert_all_code"
  by unfold_locales (simp_all add: assert_bound_loop_code_def assert_all_state_code_def assert_all_code_def)

(* -------------------------------------------------------------------------- *)
(* Preprocess preprocess  *)
(* -------------------------------------------------------------------------- *)

primrec
  monom_to_atom:: "QDelta ns_constraint \<Rightarrow> QDelta atom" where
  "monom_to_atom (LEQ_ns l r) = (if (monom_coeff l < 0) then
                                                (Geq (monom_var l) (r /R monom_coeff l))
                                            else
                                                (Leq (monom_var l) (r /R monom_coeff l)))"
| "monom_to_atom (GEQ_ns l r) = (if (monom_coeff l < 0) then
                                                (Leq (monom_var l) (r /R monom_coeff l))
                                            else
                                                (Geq (monom_var l) (r /R monom_coeff l)))"

primrec
  qdelta_constraint_to_atom:: "QDelta ns_constraint \<Rightarrow> var \<Rightarrow> QDelta atom" where
  "qdelta_constraint_to_atom (LEQ_ns l r) v = (if (is_monom l) then (monom_to_atom (LEQ_ns l r)) else (Leq v r))"
| "qdelta_constraint_to_atom (GEQ_ns l r) v = (if (is_monom l) then (monom_to_atom (GEQ_ns l r)) else (Geq v r))"

primrec
  qdelta_constraint_to_atom':: "QDelta ns_constraint \<Rightarrow> var \<Rightarrow> QDelta atom" where
  "qdelta_constraint_to_atom' (LEQ_ns l r) v = (Leq v r)"
| "qdelta_constraint_to_atom' (GEQ_ns l r) v = (Geq v r)"

fun linear_poly_to_eq:: "linear_poly \<Rightarrow> var \<Rightarrow> eq" where
  "linear_poly_to_eq p v = (v, p)"

datatype 'i istate = IState
  (FirstFreshVariable: var)
  (Tableau: tableau)
  (Atoms: "('i,QDelta) i_atom list")
  (Poly_Mapping: "linear_poly \<rightharpoonup> var")
  (UnsatIndices: "'i list")

primrec zero_satisfies :: "'a :: lrv ns_constraint \<Rightarrow> bool" where
  "zero_satisfies (LEQ_ns l r) \<longleftrightarrow> 0 \<le> r"
| "zero_satisfies (GEQ_ns l r) \<longleftrightarrow> 0 \<ge> r"

 
lemma zero_satisfies: "poly c = 0 \<Longrightarrow> zero_satisfies c \<Longrightarrow> v \<Turnstile>\<^sub>n\<^sub>s c" 
  by (cases c, auto simp: valuate_zero)

lemma not_zero_satisfies: "poly c = 0 \<Longrightarrow> \<not> zero_satisfies c \<Longrightarrow> \<not> v \<Turnstile>\<^sub>n\<^sub>s c" 
  by (cases c, auto simp: valuate_zero)

fun
  preprocess' :: "('i,QDelta) i_ns_constraint list \<Rightarrow> var \<Rightarrow> 'i istate" where
  "preprocess' [] v = IState v [] [] (\<lambda> p. None) []"
| "preprocess' ((i,h) # t) v = (let s' = preprocess' t v; p = poly h; is_monom_h = is_monom p;
                         v' = FirstFreshVariable s';
                         t' = Tableau s';
                         a' = Atoms s';
                         m' = Poly_Mapping s';
                         u' = UnsatIndices s' in
                         if is_monom_h then IState v' t'
                           ((i,qdelta_constraint_to_atom h v') # a') m' u'
                         else if p = 0 then
                           if zero_satisfies h then s' else 
                              IState v' t' a' m' (i # u')
                         else (case m' p of Some v \<Rightarrow>
                            IState v' t' ((i,qdelta_constraint_to_atom h v) # a') m' u'
                          | None \<Rightarrow> IState (v' + 1) (linear_poly_to_eq p v' # t')
                           ((i,qdelta_constraint_to_atom h v') # a') (m' (p \<mapsto> v')) u')
)"

lemma preprocess'_simps: "preprocess' ((i,h) # t) v = (let s' = preprocess' t v; p = poly h; is_monom_h = is_monom p;
                         v' = FirstFreshVariable s';
                         t' = Tableau s';
                         a' = Atoms s';
                         m' = Poly_Mapping s';
                         u' = UnsatIndices s' in
                         if is_monom_h then IState v' t'
                           ((i,monom_to_atom h) # a') m' u'
                         else if p = 0 then
                           if zero_satisfies h then s' else 
                              IState v' t' a' m' (i # u')
                         else (case m' p of Some v \<Rightarrow>
                            IState v' t' ((i,qdelta_constraint_to_atom' h v) # a') m' u'
                          | None \<Rightarrow> IState (v' + 1) (linear_poly_to_eq p v' # t')
                           ((i,qdelta_constraint_to_atom' h v') # a') (m' (p \<mapsto> v')) u')
    )" by (cases h, auto simp add: Let_def split: option.splits)

lemmas preprocess'_code = preprocess'.simps(1) preprocess'_simps
declare preprocess'_code[code]

text \<open>Normalization of constraints helps to identify same polynomials, e.g., 
  the constraints $x + y \leq 5$ and $-2x-2y \leq -12$ will be normalized
  to $x + y \leq 5$ and $x + y \geq 6$, so that only one slack-variable will
  be introduced for the polynomial $x+y$, and not another one for $-2x-2y$.
  Normalization will take care that the max-var of the polynomial in the constraint
  will have coefficient 1 (if the polynomial is non-zero)\<close>

fun normalize_ns_constraint :: "'a :: lrv ns_constraint \<Rightarrow> 'a ns_constraint" where
  "normalize_ns_constraint (LEQ_ns l r) = (let v = max_var l; c = coeff l v in 
     if c = 0 then LEQ_ns l r else 
     let ic = inverse c in if c < 0 then GEQ_ns (ic *R l) (scaleRat ic r) else LEQ_ns (ic *R l) (scaleRat ic r))" 
| "normalize_ns_constraint (GEQ_ns l r) = (let v = max_var l; c = coeff l v in 
     if c = 0 then GEQ_ns l r else 
     let ic = inverse c in if c < 0 then LEQ_ns (ic *R l) (scaleRat ic r) else GEQ_ns (ic *R l) (scaleRat ic r))" 

lemma normalize_ns_constraint[simp]: "v \<Turnstile>\<^sub>n\<^sub>s (normalize_ns_constraint c) \<longleftrightarrow> v \<Turnstile>\<^sub>n\<^sub>s (c :: 'a :: lrv ns_constraint)" 
proof -
  let ?c = "coeff (poly c) (max_var (poly c))" 
  consider (0) "?c = 0" | (pos) "?c > 0" | (neg) "?c < 0" by linarith
  thus ?thesis
  proof cases
    case 0
    thus ?thesis by (cases c, auto)
  next
    case pos
    from pos have id: "a /R ?c \<le> b /R ?c \<longleftrightarrow> (a :: 'a) \<le> b" for a b 
      using scaleRat_leq1 by fastforce
    show ?thesis using pos id by (cases c, auto simp: Let_def valuate_scaleRat id)
  next
    case neg
    from neg have id: "a /R ?c \<le> b /R ?c \<longleftrightarrow> (a :: 'a) \<ge> b" for a b 
      using scaleRat_leq2 by fastforce
    show ?thesis using neg id by (cases c, auto simp: Let_def valuate_scaleRat id)
  qed
qed
    
declare normalize_ns_constraint.simps[simp del]

lemma i_satisfies_normalize_ns_constraint[simp]: "Iv \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s (map_prod id normalize_ns_constraint ` cs)
  \<longleftrightarrow> Iv \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s cs" 
  by (cases Iv, force)


abbreviation max_var:: "QDelta ns_constraint \<Rightarrow> var" where
  "max_var C \<equiv> Abstract_Linear_Poly.max_var (poly C)"

fun
  start_fresh_variable :: "('i,QDelta) i_ns_constraint list \<Rightarrow> var" where
  "start_fresh_variable [] = 0"
| "start_fresh_variable ((i,h)#t) = max (max_var h + 1) (start_fresh_variable t)"


definition
  preprocess_part_1  :: "('i,QDelta) i_ns_constraint list \<Rightarrow> tableau \<times> (('i,QDelta) i_atom list) \<times> 'i list" where
  "preprocess_part_1 l \<equiv> let start = start_fresh_variable l; is = preprocess' l start in (Tableau is, Atoms is, UnsatIndices is)"

lemma lhs_linear_poly_to_eq [simp]:
  "lhs (linear_poly_to_eq h v) = v"
  by (cases h) auto

lemma rvars_eq_linear_poly_to_eq [simp]:
  "rvars_eq (linear_poly_to_eq h v) = vars h"
  by simp

lemma fresh_var_monoinc:
  "FirstFreshVariable (preprocess' cs start) \<ge> start"
  by (induct cs) (auto simp add: Let_def split: option.splits)

abbreviation vars_constraints where
  "vars_constraints cs \<equiv> \<Union> (set (map vars (map poly cs)))"

lemma start_fresh_variable_fresh:
  "\<forall> var \<in> vars_constraints (flat_list cs). var < start_fresh_variable cs"
  using max_var_max
  by (induct cs, auto simp add: max_def) force+

lemma vars_tableau_vars_constraints:
  "rvars (Tableau (preprocess' cs start)) \<subseteq> vars_constraints (flat_list cs)"
  by (induct cs start rule: preprocess'.induct) (auto simp add: rvars_def Let_def split: option.splits)

lemma lvars_tableau_ge_start:
  "\<forall> var \<in> lvars (Tableau (preprocess' cs start)). var \<ge> start"
  by (induct cs start rule: preprocess'.induct) (auto simp add: Let_def lvars_def fresh_var_monoinc split: option.splits)

lemma rhs_no_zero_tableau_start:
  "0 \<notin> rhs ` set (Tableau (preprocess' cs start))"
  by (induct cs start rule: preprocess'.induct, auto simp add: Let_def rvars_def fresh_var_monoinc split: option.splits)

lemma first_fresh_variable_not_in_lvars:
  "\<forall>var \<in> lvars (Tableau (preprocess' cs start)). FirstFreshVariable (preprocess' cs start) > var"
  by (induct cs start rule: preprocess'.induct) (auto simp add: Let_def lvars_def split: option.splits)

lemma sat_atom_sat_eq_sat_constraint_non_monom:
  assumes "v \<Turnstile>\<^sub>a qdelta_constraint_to_atom h var" "v \<Turnstile>\<^sub>e linear_poly_to_eq (poly h) var" "\<not> is_monom (poly h)"
  shows "v \<Turnstile>\<^sub>n\<^sub>s h"
  using assms
  by (cases h) (auto simp add: satisfies_eq_def split: if_splits)

lemma qdelta_constraint_to_atom_monom:
  assumes "is_monom (poly h)"
  shows "v \<Turnstile>\<^sub>a qdelta_constraint_to_atom h var \<longleftrightarrow> v \<Turnstile>\<^sub>n\<^sub>s h"
proof (cases h)
  case (LEQ_ns l a)
  then show ?thesis
    using assms
    using monom_valuate[of _ v]
    apply auto
    using scaleRat_leq2[of "a /R monom_coeff l" "v (monom_var l)" "monom_coeff l"]
    using divide_leq1[of "monom_coeff l" "v (monom_var l)" a]
       apply (force, simp add: divide_rat_def)
    using scaleRat_leq1[of "v (monom_var l)" "a /R monom_coeff l" "monom_coeff l"]
    using is_monom_monom_coeff_not_zero[of l]
    using divide_leq[of "monom_coeff l" "v (monom_var l)" a]
    using is_monom_monom_coeff_not_zero[of l]
    by (simp_all add: divide_rat_def)
next
  case (GEQ_ns l a)
  then show ?thesis
    using assms
    using monom_valuate[of _ v]
    apply auto
    using scaleRat_leq2[of "v (monom_var l)" "a /R monom_coeff l" "monom_coeff l"]
    using divide_geq1[of a "monom_coeff l" "v (monom_var l)"]
       apply (force, simp add: divide_rat_def)
    using scaleRat_leq1[of "a /R monom_coeff l" "v (monom_var l)" "monom_coeff l"]
    using is_monom_monom_coeff_not_zero[of l]
    using divide_geq[of a "monom_coeff l" "v (monom_var l)"]
    using is_monom_monom_coeff_not_zero[of l]
    by (simp_all add: divide_rat_def)
qed

lemma preprocess'_Tableau_Poly_Mapping_None: "(Poly_Mapping (preprocess' cs start)) p = None
  \<Longrightarrow> linear_poly_to_eq p v \<notin> set (Tableau (preprocess' cs start))"
  by (induct cs start rule: preprocess'.induct, auto simp: Let_def split: option.splits if_splits)

lemma preprocess'_Tableau_Poly_Mapping_Some: "(Poly_Mapping (preprocess' cs start)) p = Some v
  \<Longrightarrow> linear_poly_to_eq p v \<in> set (Tableau (preprocess' cs start))"
  by (induct cs start rule: preprocess'.induct, auto simp: Let_def split: option.splits if_splits)

lemma preprocess'_Tableau_Poly_Mapping_Some': "(Poly_Mapping (preprocess' cs start)) p = Some v
  \<Longrightarrow> \<exists> h. poly h = p \<and> \<not> is_monom (poly h) \<and> qdelta_constraint_to_atom h v \<in> flat (set (Atoms (preprocess' cs start)))"
  by (induct cs start rule: preprocess'.induct, auto simp: Let_def split: option.splits if_splits)

lemma not_one_le_zero_qdelta: "\<not> (1 \<le> (0 :: QDelta))" by code_simp

lemma one_zero_contra[dest,consumes 2]: "1 \<le> x \<Longrightarrow> (x :: QDelta) \<le> 0 \<Longrightarrow> False" 
  using order.trans[of 1 x 0] not_one_le_zero_qdelta by simp

lemma i_preprocess'_sat:
  assumes "(I,v) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set (Atoms (preprocess' s start))" "v \<Turnstile>\<^sub>t Tableau (preprocess' s start)" 
    "I \<inter> set (UnsatIndices (preprocess' s start)) = {}" 
  shows "(I,v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set s"
  using assms
  by (induct s start rule: preprocess'.induct)
    (auto simp add: Let_def satisfies_atom_set_def satisfies_tableau_def qdelta_constraint_to_atom_monom
      sat_atom_sat_eq_sat_constraint_non_monom 
      split: if_splits option.splits dest!: preprocess'_Tableau_Poly_Mapping_Some zero_satisfies)

lemma preprocess'_sat:
  assumes "v \<Turnstile>\<^sub>a\<^sub>s flat (set (Atoms (preprocess' s start)))" "v \<Turnstile>\<^sub>t Tableau (preprocess' s start)" "set (UnsatIndices (preprocess' s start)) = {}" 
  shows "v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s flat (set s)"
  using i_preprocess'_sat[of UNIV v s start] assms by simp

lemma sat_constraint_valuation:
  assumes "\<forall> var \<in> vars (poly c). v1 var = v2 var"
  shows "v1 \<Turnstile>\<^sub>n\<^sub>s c \<longleftrightarrow> v2 \<Turnstile>\<^sub>n\<^sub>s c"
  using assms
  using valuate_depend
  by (cases c) (force)+

lemma atom_var_first:
  assumes "a \<in> flat (set (Atoms (preprocess' cs start)))" "\<forall> var \<in> vars_constraints (flat_list cs). var < start"
  shows "atom_var a < FirstFreshVariable (preprocess' cs start)"
  using assms
proof(induct cs arbitrary: a)
  case (Cons hh t a)
  obtain i h where hh: "hh = (i,h)" by force
  let ?s = "preprocess' t start"
  show ?case
  proof(cases "a \<in> flat (set (Atoms ?s))")
    case True
    then show ?thesis
      using Cons(1)[of a] Cons(3) hh
      by (auto simp add: Let_def split: option.splits)
  next
    case False
    consider (monom) "is_monom (poly h)" | (normal) "\<not> is_monom (poly h)" "poly h \<noteq> 0" "(Poly_Mapping ?s) (poly h) = None"
      | (old) var where "\<not> is_monom (poly h)" "poly h \<noteq> 0" "(Poly_Mapping ?s) (poly h) = Some var"
      | (zero) "\<not> is_monom (poly h)" "poly h = 0" 
      by auto
    then show ?thesis
    proof cases
      case monom
      from Cons(3) monom_var_in_vars hh monom
      have "monom_var (poly h) < start" by auto
      moreover from False have "a = qdelta_constraint_to_atom h (FirstFreshVariable (preprocess' t start))"
        using Cons(2) hh monom by (auto simp: Let_def)
      ultimately show ?thesis
        using fresh_var_monoinc[of start t] hh monom
        by (cases a; cases h) (auto simp add: Let_def )
    next
      case normal
      have "a = qdelta_constraint_to_atom h (FirstFreshVariable (preprocess' t start))"
        using False normal Cons(2) hh by (auto simp: Let_def)
      then show ?thesis using hh normal
        by (cases a; cases h) (auto simp add: Let_def )
    next
      case (old var)
      from preprocess'_Tableau_Poly_Mapping_Some'[OF old(3)]
      obtain h' where "poly h' = poly h" "qdelta_constraint_to_atom h' var \<in> flat (set (Atoms ?s))"
        by blast
      from Cons(1)[OF this(2)] Cons(3) this(1) old(1)
      have var: "var < FirstFreshVariable ?s" by (cases h', auto)
      have "a = qdelta_constraint_to_atom h var"
        using False old Cons(2) hh by (auto simp: Let_def)
      then have a: "atom_var a = var" using old by (cases a; cases h; auto simp: Let_def)
      show ?thesis unfolding a hh by (simp add: old Let_def var)
    next
      case zero
      from False show ?thesis using Cons(2) hh zero by (auto simp: Let_def split: if_splits)
    qed
  qed
qed simp

lemma satisfies_tableau_satisfies_tableau:
  assumes "v1 \<Turnstile>\<^sub>t t" "\<forall> var \<in> tvars t. v1 var = v2 var"
  shows "v2 \<Turnstile>\<^sub>t t"
  using assms
  using valuate_depend[of _ v1 v2]
  by (force simp add: lvars_def rvars_def satisfies_eq_def satisfies_tableau_def)

lemma preprocess'_unsat_indices:
  assumes "i \<in> set (UnsatIndices (preprocess' s start))" 
  shows "\<not> ({i},v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set s" 
  using assms
proof (induct s start rule: preprocess'.induct)
  case (2 j h t v)
  then show ?case by (auto simp: Let_def not_zero_satisfies split: if_splits option.splits)
qed simp

lemma preprocess'_unsat:
  assumes "(I,v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set s" "vars_constraints (flat_list s) \<subseteq> V" "\<forall>var \<in> V. var < start"
  shows "\<exists>v'. (\<forall>var \<in> V. v var = v' var)
    \<and> v' \<Turnstile>\<^sub>a\<^sub>s restrict_to I (set (Atoms (preprocess' s start)))
    \<and> v' \<Turnstile>\<^sub>t Tableau (preprocess' s start)"
  using assms
proof(induct s)
  case Nil
  show ?case
    by (auto simp add: satisfies_atom_set_def satisfies_tableau_def)
next
  case (Cons hh t)
  obtain i h where hh: "hh = (i,h)" by force
  from Cons hh obtain v' where
    var: "(\<forall>var\<in>V. v var = v' var)"
    and v'_as: "v' \<Turnstile>\<^sub>a\<^sub>s restrict_to I (set (Atoms (preprocess' t start)))"
    and v'_t: "v' \<Turnstile>\<^sub>t Tableau (preprocess' t start)"
    and vars_h: "vars_constraints [h] \<subseteq> V"
    by auto
  from Cons(2)[unfolded hh]
  have i: "i \<in> I \<Longrightarrow> v \<Turnstile>\<^sub>n\<^sub>s h" by auto
  have "\<forall> var \<in> vars (poly h). v var = v' var"
    using \<open>(\<forall>var\<in>V. v var = v' var)\<close> Cons(3) hh
    by auto
  then have vh_v'h: "v \<Turnstile>\<^sub>n\<^sub>s h \<longleftrightarrow> v' \<Turnstile>\<^sub>n\<^sub>s h"
    by (rule sat_constraint_valuation)
  show ?case
  proof(cases "is_monom (poly h)")
    case True
    then have id: "is_monom (poly h) = True" by simp
    show ?thesis
      unfolding hh preprocess'.simps Let_def id if_True istate.simps istate.sel
    proof (intro exI[of _ v'] conjI v'_t var satisifies_atom_restrict_to_Cons[OF v'_as])
      assume "i \<in> I"
      from i[OF this] var vh_v'h
      show "v' \<Turnstile>\<^sub>a qdelta_constraint_to_atom h (FirstFreshVariable (preprocess' t start))"
        unfolding qdelta_constraint_to_atom_monom[OF True] by auto
    qed
  next
    case False
    then have id: "is_monom (poly h) = False" by simp
    let ?s = "preprocess' t start"
    let ?x = "FirstFreshVariable ?s"
    show ?thesis
    proof (cases "poly h = 0")
      case zero: False
      hence id': "(poly h = 0) = False" by simp
      let ?look = "(Poly_Mapping ?s) (poly h)"
      show ?thesis
      proof (cases ?look)
        case None
        let ?y = "poly h \<lbrace> v'\<rbrace>"
        let ?v' = "v'(?x:=?y)"
        show ?thesis unfolding preprocess'.simps hh Let_def id id' if_False istate.simps istate.sel None option.simps
        proof (rule exI[of _ ?v'], intro conjI satisifies_atom_restrict_to_Cons satisfies_tableau_Cons)
          show vars': "(\<forall>var\<in>V. v var = ?v' var)"
            using \<open>(\<forall>var\<in>V. v var = v' var)\<close>
            using fresh_var_monoinc[of start t]
            using Cons(4)
            by auto
          {
            assume "i \<in> I"
            from vh_v'h i[OF this] False
            show "?v' \<Turnstile>\<^sub>a qdelta_constraint_to_atom h (FirstFreshVariable (preprocess' t start))"
              by (cases h, auto)
          }
          let ?atoms = "restrict_to I (set (Atoms (preprocess' t start)))"
          show "?v' \<Turnstile>\<^sub>a\<^sub>s ?atoms"
            unfolding satisfies_atom_set_def
          proof
            fix a
            assume "a \<in> ?atoms"
            then have "v' \<Turnstile>\<^sub>a a"
              using \<open>v' \<Turnstile>\<^sub>a\<^sub>s ?atoms\<close> hh by (force simp add: satisfies_atom_set_def)
            then show "?v' \<Turnstile>\<^sub>a a"
              using \<open>a \<in> ?atoms\<close> atom_var_first[of a t start]
              using Cons(3) Cons(4)
              by (cases a) auto
          qed
          show "?v' \<Turnstile>\<^sub>e linear_poly_to_eq (poly h) (FirstFreshVariable (preprocess' t start))"
            using Cons(3) Cons(4)
            using valuate_depend[of "poly h" v' "v'(FirstFreshVariable (preprocess' t start) := (poly h) \<lbrace> v' \<rbrace>)"]
            using fresh_var_monoinc[of start t] hh
            by (cases h) (force simp add: satisfies_eq_def)+
          have "FirstFreshVariable (preprocess' t start) \<notin> tvars (Tableau (preprocess' t start))"
            using first_fresh_variable_not_in_lvars[of t start]
            using Cons(3) Cons(4)
            using vars_tableau_vars_constraints[of t start]
            using fresh_var_monoinc[of start t]
            by force
          then show "?v' \<Turnstile>\<^sub>t Tableau (preprocess' t start)"
            using \<open>v' \<Turnstile>\<^sub>t Tableau (preprocess' t start)\<close>
            using satisfies_tableau_satisfies_tableau[of v' "Tableau (preprocess' t start)" ?v']
            by auto
        qed
      next
        case (Some var)
        from preprocess'_Tableau_Poly_Mapping_Some[OF Some]
        have "linear_poly_to_eq (poly h) var \<in> set (Tableau ?s)" by auto
        with v'_t[unfolded satisfies_tableau_def]
        have v'_h_var: "v' \<Turnstile>\<^sub>e linear_poly_to_eq (poly h) var" by auto
        show ?thesis unfolding preprocess'.simps hh Let_def id id' if_False istate.simps istate.sel Some option.simps
        proof (intro exI[of _ v'] conjI var v'_t satisifies_atom_restrict_to_Cons satisfies_tableau_Cons v'_as)
          assume "i \<in> I"
          from vh_v'h i[OF this] False v'_h_var
          show "v' \<Turnstile>\<^sub>a qdelta_constraint_to_atom h var"
            by (cases h, auto simp: satisfies_eq_iff)
        qed
      qed
    next
      case zero: True
      hence id': "(poly h = 0) = True" by simp
      show ?thesis
      proof (cases "zero_satisfies h") 
        case True
        hence id'': "zero_satisfies h = True" by simp
        show ?thesis
          unfolding hh preprocess'.simps Let_def id id' id'' if_True if_False istate.simps istate.sel
          by (intro exI[of _ v'] conjI v'_t var v'_as)
      next
        case False
        hence id'': "zero_satisfies h = False" by simp
        { 
          assume "i \<in> I"
          from i[OF this] not_zero_satisfies[OF zero False] have False by simp
        } note no_I = this
        show ?thesis
          unfolding hh preprocess'.simps Let_def id id' id'' if_True if_False istate.simps istate.sel
        proof (rule Cons(1)[OF _ _ Cons(4)])
          show "(I, v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s  set t" using Cons(2) by auto
          show "vars_constraints (map snd t) \<subseteq> V" using Cons(3) by force
        qed
      qed
    qed
  qed
qed

lemma lvars_distinct:
  "distinct (map lhs (Tableau (preprocess' cs start)))"
  using first_fresh_variable_not_in_lvars[where ?'a = 'a]
  by (induct cs, auto simp add: Let_def lvars_def) (force split: option.splits)

lemma normalized_tableau_preprocess': "\<triangle> (Tableau (preprocess' cs (start_fresh_variable cs)))"
proof -
  let ?s = "start_fresh_variable cs"
  show ?thesis
    using lvars_distinct[of cs ?s]
    using lvars_tableau_ge_start[of cs ?s]
    using vars_tableau_vars_constraints[of cs ?s]
    using start_fresh_variable_fresh[of cs] 
    unfolding normalized_tableau_def Let_def
    by (smt disjoint_iff_not_equal inf.absorb_iff2 inf.strict_order_iff rhs_no_zero_tableau_start subsetD)
qed


text \<open>Improved preprocessing: Deletion. An equation x = p can be deleted from the tableau,
  if x does not occur in the atoms.\<close>

lemma delete_lhs_var: assumes norm: "\<triangle> t" and t: "t = t1 @ (x,p) # t2"
  and t': "t' = t1 @ t2"
  and tv: "tv = (\<lambda> v. upd x (p \<lbrace> \<langle>v\<rangle> \<rbrace>) v)"
  and x_as: "x \<notin> atom_var ` snd ` set as"
shows "\<triangle> t'" \<comment> \<open>new tableau is normalized\<close>
  "\<langle>w\<rangle> \<Turnstile>\<^sub>t t' \<Longrightarrow> \<langle>tv w\<rangle> \<Turnstile>\<^sub>t t" \<comment> \<open>solution of new tableau is translated to solution of old tableau\<close>
  "(I, \<langle>w\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as \<Longrightarrow> (I, \<langle>tv w\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as" \<comment> \<open>solution translation also works for bounds\<close>
  "v \<Turnstile>\<^sub>t t \<Longrightarrow> v \<Turnstile>\<^sub>t t'" \<comment> \<open>solution of old tableau is also solution for new tableau\<close>
proof -
  have tv: "\<langle>tv w\<rangle> = \<langle>w\<rangle> (x := p \<lbrace> \<langle>w\<rangle> \<rbrace>)" unfolding tv map2fun_def' by auto
  from norm
  show "\<triangle> t'" unfolding t t' normalized_tableau_def by (auto simp: lvars_def rvars_def)
  show "v \<Turnstile>\<^sub>t t \<Longrightarrow> v \<Turnstile>\<^sub>t t'" unfolding t t' satisfies_tableau_def by auto
  from norm have dist: "distinct (map lhs t)" "lvars t \<inter> rvars t = {}"
    unfolding normalized_tableau_def by auto
  from x_as have x_as: "x \<notin> atom_var ` snd ` (set as \<inter> I \<times> UNIV)" by auto
  have "(I, \<langle>tv w\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as \<longleftrightarrow> (I, \<langle>w\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as" unfolding i_satisfies_atom_set.simps
      satisfies_atom_set_def
  proof (intro ball_cong[OF refl])
    fix a
    assume "a \<in> snd ` (set as \<inter> I \<times> UNIV)"
    with x_as have "x \<noteq> atom_var a" by auto
    then show "\<langle>tv w\<rangle> \<Turnstile>\<^sub>a a = \<langle>w\<rangle> \<Turnstile>\<^sub>a a" unfolding tv
      by (cases a, auto)
  qed
  then show "(I, \<langle>w\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as \<Longrightarrow> (I, \<langle>tv w\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as" by blast
  assume w: "\<langle>w\<rangle> \<Turnstile>\<^sub>t t'"
  from dist(2)[unfolded t] have xp: "x \<notin> vars p"
    unfolding lvars_def rvars_def by auto
  {
    fix eq
    assume mem: "eq \<in> set t1 \<union> set t2"
    then have "eq \<in> set t'" unfolding t' by auto
    with w have w: "\<langle>w\<rangle> \<Turnstile>\<^sub>e eq" unfolding satisfies_tableau_def by auto
    obtain y q where eq: "eq = (y,q)" by force
    from mem[unfolded eq] dist(1)[unfolded t] have xy: "x \<noteq> y" by force
    from mem[unfolded eq] dist(2)[unfolded t] have xq: "x \<notin> vars q"
      unfolding lvars_def rvars_def by auto
    from w have "\<langle>tv w\<rangle> \<Turnstile>\<^sub>e eq" unfolding tv eq satisfies_eq_iff using xy xq
      by (auto intro!: valuate_depend)
  }
  moreover
  have "\<langle>tv w\<rangle> \<Turnstile>\<^sub>e (x,p)" unfolding satisfies_eq_iff tv using xp
    by (auto intro!: valuate_depend)
  ultimately
  show "\<langle>tv w\<rangle> \<Turnstile>\<^sub>t t" unfolding t satisfies_tableau_def by auto
qed

definition pivot_tableau_eq :: "tableau \<Rightarrow> eq \<Rightarrow> tableau \<Rightarrow> var \<Rightarrow> tableau \<times> eq \<times> tableau" where
  "pivot_tableau_eq t1 eq t2 x \<equiv> let eq' = pivot_eq eq x; m = map (\<lambda> e. subst_var_eq x (rhs eq') e) in
    (m t1, eq', m t2)"

lemma pivot_tableau_eq: assumes t: "t = t1 @ eq # t2" "t' = t1' @ eq' # t2'"
  and x: "x \<in> rvars_eq eq" and norm: "\<triangle> t" and pte: "pivot_tableau_eq t1 eq t2 x = (t1',eq',t2')"
shows "\<triangle> t'" "lhs eq' = x" "(v :: 'a :: lrv valuation) \<Turnstile>\<^sub>t t' \<longleftrightarrow> v \<Turnstile>\<^sub>t t"
proof -
  let ?s = "\<lambda> t. State t undefined undefined undefined undefined undefined"
  let ?y = "lhs eq"
  have yl: "?y \<in> lvars t" unfolding t lvars_def by auto
  from norm have eq_t12: "?y \<notin> lhs ` (set t1 \<union> set t2)"
    unfolding normalized_tableau_def t lvars_def by auto
  have eq: "eq_for_lvar_code t ?y = eq"
    by (metis (mono_tags, lifting) EqForLVarDefault.eq_for_lvar Un_insert_right eq_t12
        image_iff insert_iff list.set(2) set_append t(1) yl)
  have *: "(?y, b) \<in> set t1 \<Longrightarrow> ?y \<in> lhs ` (set t1)" for b t1
    by (metis image_eqI lhs.simps)
  have pivot: "pivot_tableau_code ?y x t = t'"
    unfolding Pivot'Default.pivot_tableau_def Let_def eq using pte[symmetric]
    unfolding t pivot_tableau_eq_def Let_def using eq_t12 by (auto dest!: *)
  note thms = Pivot'Default.pivot_vars' Pivot'Default.pivot_tableau
  note thms = thms[unfolded Pivot'Default.pivot_def, of "?s t", simplified,
      OF norm yl, unfolded eq, OF x, unfolded pivot]
  from thms(1) thms(2)[of v] show "\<triangle> t'" "v \<Turnstile>\<^sub>t t' \<longleftrightarrow> v \<Turnstile>\<^sub>t t" by auto
  show "lhs eq' = x" using pte[symmetric]
    unfolding t pivot_tableau_eq_def Let_def pivot_eq_def by auto
qed

function preprocess_opt :: "var set \<Rightarrow> tableau \<Rightarrow> tableau \<Rightarrow> tableau \<times> ((var,'a :: lrv)mapping \<Rightarrow> (var,'a)mapping)" where
  "preprocess_opt X t1 [] = (t1,id)"
| "preprocess_opt X t1 ((x,p) # t2) = (if x \<notin> X then
    case preprocess_opt X t1 t2 of (t,tv) \<Rightarrow> (t, (\<lambda> v. upd x (p \<lbrace> \<langle>v\<rangle> \<rbrace>) v) o tv)
    else case find (\<lambda> x. x \<notin> X) (Abstract_Linear_Poly.vars_list p) of
     None \<Rightarrow> preprocess_opt X ((x,p) # t1) t2
   | Some y \<Rightarrow> case pivot_tableau_eq t1 (x,p) t2 y of
      (tt1,(z,q),tt2) \<Rightarrow> case preprocess_opt X tt1 tt2 of (t,tv) \<Rightarrow> (t, (\<lambda> v. upd z (q \<lbrace> \<langle>v\<rangle> \<rbrace>) v) o tv))"
  by pat_completeness auto

termination by (relation "measure (\<lambda> (X,t1,t2). length t2)", auto simp: pivot_tableau_eq_def Let_def)

lemma preprocess_opt: assumes "X = atom_var ` snd ` set as"
  "preprocess_opt X t1 t2 = (t',tv)" "\<triangle> t" "t = rev t1 @ t2"
shows "\<triangle> t'"
  "(\<langle>w\<rangle> :: 'a :: lrv valuation) \<Turnstile>\<^sub>t t' \<Longrightarrow> \<langle>tv w\<rangle> \<Turnstile>\<^sub>t t"
  "(I, \<langle>w\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as \<Longrightarrow> (I, \<langle>tv w\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as"
  "v \<Turnstile>\<^sub>t t \<Longrightarrow> (v :: 'a valuation) \<Turnstile>\<^sub>t t'"
  using assms
proof (atomize(full), induct X t1 t2 arbitrary: t tv w rule: preprocess_opt.induct)
  case (1 X t1 t tv)
  then show ?case by (auto simp: normalized_tableau_def lvars_def rvars_def satisfies_tableau_def
        simp flip: rev_map)
next
  case (2 X t1 x p t2 t tv w)
  note IH = 2(1-3)
  note X = 2(4)
  note res = 2(5)
  have norm: "\<triangle> t" by fact
  have t: "t = rev t1 @ (x, p) # t2" by fact
  show ?case
  proof (cases "x \<in> X")
    case False
    with res obtain tv' where res: "preprocess_opt X t1 t2 = (t', tv')" and
      tv: "tv = (\<lambda>v. Mapping.update x (p \<lbrace> \<langle>v\<rangle> \<rbrace>) v) o tv'"
      by (auto split: prod.splits)
    note delete = delete_lhs_var[OF norm t refl refl False[unfolded X]]
    note IH = IH(1)[OF False X res delete(1) refl]
    from delete(2)[of "tv' w"] delete(3)[of I "tv' w"] delete(4)[of v] IH[of w]
    show ?thesis unfolding tv o_def
      by auto
  next
    case True
    then have "\<not> x \<notin> X" by simp
    note IH = IH(2-3)[OF this]
    show ?thesis
    proof (cases "find (\<lambda>x. x \<notin> X) (Abstract_Linear_Poly.vars_list p)")
      case None
      with res True have pre: "preprocess_opt X ((x, p) # t1) t2 = (t', tv)" by auto
      from t have t: "t = rev ((x, p) # t1) @ t2" by simp
      from IH(1)[OF None X pre norm t]
      show ?thesis .
    next
      case (Some z)
      from Some[unfolded find_Some_iff] have zX: "z \<notin> X" and "z \<in> set (Abstract_Linear_Poly.vars_list p)"
        unfolding set_conv_nth by auto
      then have z: "z \<in> rvars_eq (x, p)" by (simp add: set_vars_list)
      obtain tt1 z' q tt2 where pte: "pivot_tableau_eq t1 (x, p) t2 z = (tt1,(z',q),tt2)"
        by (cases "pivot_tableau_eq t1 (x, p) t2 z", auto)
      then have pte_rev: "pivot_tableau_eq (rev t1) (x, p) t2 z = (rev tt1,(z',q),tt2)"
        unfolding pivot_tableau_eq_def Let_def by (auto simp: rev_map)
      note eq = pivot_tableau_eq[OF t refl z norm pte_rev]
      then have z': "z' = z" by auto
      note eq = eq(1,3)[unfolded z']
      note pte = pte[unfolded z']
      note pte_rev = pte_rev[unfolded z']
      note delete = delete_lhs_var[OF eq(1) refl refl refl zX[unfolded X]]
      from res[unfolded preprocess_opt.simps Some option.simps pte] True
      obtain tv' where res: "preprocess_opt X tt1 tt2 = (t', tv')" and
        tv: "tv = (\<lambda>v. Mapping.update z (q \<lbrace> \<langle>v\<rangle> \<rbrace>) v) o tv'"
        by (auto split: prod.splits)
      note IH = IH(2)[OF Some, unfolded pte, OF refl refl refl X res delete(1) refl]
      from IH[of w] delete(2)[of "tv' w"] delete(3)[of I "tv' w"] delete(4)[of v] show ?thesis
        unfolding tv o_def eq(2) by auto
    qed
  qed
qed

definition "preprocess_part_2 as t = preprocess_opt (atom_var ` snd ` set as) [] t"

lemma preprocess_part_2: assumes "preprocess_part_2 as t = (t',tv)" "\<triangle> t"
  shows "\<triangle> t'"
    "(\<langle>w\<rangle> :: 'a :: lrv valuation) \<Turnstile>\<^sub>t t' \<Longrightarrow> \<langle>tv w\<rangle> \<Turnstile>\<^sub>t t"
    "(I, \<langle>w\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as \<Longrightarrow> (I, \<langle>tv w\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as"
    "v \<Turnstile>\<^sub>t t \<Longrightarrow> (v :: 'a valuation) \<Turnstile>\<^sub>t t'"
  using preprocess_opt[OF refl assms(1)[unfolded preprocess_part_2_def] assms(2)] by auto

definition preprocess :: "('i,QDelta) i_ns_constraint list \<Rightarrow> _ \<times> _ \<times> (_ \<Rightarrow> (var,QDelta)mapping) \<times> 'i list" where
  "preprocess l = (case preprocess_part_1 (map (map_prod id normalize_ns_constraint) l) of 
     (t,as,ui) \<Rightarrow> case preprocess_part_2 as t of (t,tv) \<Rightarrow> (t,as,tv,ui))"

lemma preprocess: 
  assumes id: "preprocess cs = (t, as, trans_v, ui)"
  shows "\<triangle> t" 
  "fst ` set as \<union> set ui \<subseteq> fst ` set cs" 
  "distinct_indices_ns (set cs) \<Longrightarrow> distinct_indices_atoms (set as)" 
  "I \<inter> set ui = {} \<Longrightarrow> (I, \<langle>v\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as \<Longrightarrow>
       \<langle>v\<rangle> \<Turnstile>\<^sub>t t \<Longrightarrow> (I, \<langle>trans_v v\<rangle>) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s  set cs" 
  "i \<in> set ui \<Longrightarrow> \<nexists>v. ({i}, v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s  set cs"
  "\<exists> v. (I,v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set cs \<Longrightarrow> \<exists>v'. (I,v') \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as \<and> v' \<Turnstile>\<^sub>t t" 
proof -
  define ncs where "ncs = map (map_prod id normalize_ns_constraint) cs" 
  have ncs: "fst ` set ncs = fst ` set cs" "\<And> Iv. Iv \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set ncs \<longleftrightarrow> Iv \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set cs"
    unfolding ncs_def by force auto
  from id obtain t1 where part1: "preprocess_part_1 ncs = (t1,as,ui)"
    unfolding preprocess_def by (auto simp: ncs_def split: prod.splits)
  from id[unfolded preprocess_def part1 split ncs_def[symmetric]]
  have part_2: "preprocess_part_2 as t1 = (t,trans_v)" 
    by (auto split: prod.splits)
  have norm: "\<triangle> t1" using normalized_tableau_preprocess' part1
    by (auto simp: preprocess_part_1_def Let_def)
  note part_2 = preprocess_part_2[OF part_2 norm]
  show "\<triangle> t" by fact
  have unsat: "(I,\<langle>v\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>t t1 \<Longrightarrow> I \<inter> set ui = {} \<Longrightarrow> (I,\<langle>v\<rangle>) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set ncs" for v 
    using part1[unfolded preprocess_part_1_def Let_def, simplified] i_preprocess'_sat[of I] by blast
  with part_2(2,3) show "I \<inter> set ui = {} \<Longrightarrow> (I,\<langle>v\<rangle>) \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>t t \<Longrightarrow> (I,\<langle>trans_v v\<rangle>) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set cs" 
    by (auto simp: ncs)
  from part1[unfolded preprocess_part_1_def Let_def] obtain var where
    as: "as = Atoms (preprocess' ncs var)" and ui: "ui = UnsatIndices (preprocess' ncs var)" by auto
  note min_defs = distinct_indices_atoms_def distinct_indices_ns_def
  have min1: "(distinct_indices_ns (set ncs) \<longrightarrow> (\<forall> k a. (k,a) \<in> set as \<longrightarrow> (\<exists> v p. a = qdelta_constraint_to_atom p v \<and> (k,p) \<in> set ncs
    \<and> (\<not> is_monom (poly p) \<longrightarrow> Poly_Mapping (preprocess' ncs var) (poly p) = Some v)  ))) 
    \<and> fst ` set as \<union> set ui \<subseteq> fst ` set ncs" 
    unfolding as ui
  proof (induct ncs var rule: preprocess'.induct)
    case (2 i h t v)
    hence sub: "fst ` set (Atoms (preprocess' t v)) \<union> set (UnsatIndices (preprocess' t v)) \<subseteq> fst ` set t" by auto
    show ?case 
    proof (intro conjI impI allI, goal_cases)
      show "fst ` set (Atoms (preprocess' ((i, h) # t) v)) \<union> set (UnsatIndices (preprocess' ((i,h) #t) v)) \<subseteq> fst ` set ((i, h) # t)" 
        using sub by (auto simp: Let_def split: option.splits)
    next
      case (1 k a)
      hence min': "distinct_indices_ns (set t)" unfolding min_defs list.simps by blast
      note IH = 2[THEN conjunct1, rule_format, OF min']
      show ?case
      proof (cases "(k,a) \<in> set (Atoms (preprocess' t v))")
        case True
        from IH[OF this] show ?thesis  
          by (force simp: Let_def split: option.splits if_split) 
      next
        case new: False
        with 1(2) have ki: "k = i" by (auto simp: Let_def split: if_splits option.splits)
        show ?thesis 
        proof (cases "is_monom (poly h)")
          case True
          thus ?thesis using new 1(2) by (auto simp: Let_def True intro!: exI)
        next    
          case no_monom: False
          thus ?thesis using new 1(2) by (auto simp: Let_def no_monom split: option.splits if_splits intro!: exI)
        qed
      qed
    qed
  qed (auto simp: min_defs)
  then show "fst ` set as \<union> set ui \<subseteq> fst ` set cs" by (auto simp: ncs)
  {
    assume mini: "distinct_indices_ns (set cs)" 
    have mini: "distinct_indices_ns (set ncs)" unfolding distinct_indices_ns_def
    proof (intro impI allI, goal_cases)
      case (1 n1 n2 i)
      from 1(1) obtain c1 where c1: "(i,c1) \<in> set cs" and n1: "n1 = normalize_ns_constraint c1" 
        unfolding ncs_def by auto
      from 1(2) obtain c2 where c2: "(i,c2) \<in> set cs" and n2: "n2 = normalize_ns_constraint c2" 
        unfolding ncs_def by auto
      from mini[unfolded distinct_indices_ns_def, rule_format, OF c1 c2]
      show ?case unfolding n1 n2 
        by (cases c1; cases c2; auto simp: normalize_ns_constraint.simps Let_def)
    qed
    note min = min1[THEN conjunct1, rule_format, OF this]
    show "distinct_indices_atoms (set as)" 
      unfolding distinct_indices_atoms_def
    proof (intro allI impI)
      fix i a b 
      assume a: "(i,a) \<in> set as" and b: "(i,b) \<in> set as" 
      from min[OF a] obtain v p where aa: "a = qdelta_constraint_to_atom p v" "(i, p) \<in> set ncs" 
        "\<not> is_monom (poly p) \<Longrightarrow> Poly_Mapping (preprocess' ncs var) (poly p) = Some v"
        by auto
      from min[OF b] obtain w q where bb: "b = qdelta_constraint_to_atom q w" "(i, q) \<in> set ncs" 
        "\<not> is_monom (poly q) \<Longrightarrow> Poly_Mapping (preprocess' ncs var) (poly q) = Some w"
        by auto
      from mini[unfolded distinct_indices_ns_def, rule_format, OF aa(2) bb(2)]
      have *: "poly p = poly q" "ns_constraint_const p = ns_constraint_const q" by auto
      show "atom_var a = atom_var b \<and> atom_const a = atom_const b" 
      proof (cases "is_monom (poly q)")
        case True
        thus ?thesis unfolding aa(1) bb(1) using * by (cases p; cases q, auto)
      next
        case False
        thus ?thesis unfolding aa(1) bb(1) using * aa(3) bb(3) by (cases p; cases q, auto)
      qed
    qed 
  }
  show "i \<in> set ui \<Longrightarrow> \<nexists>v. ({i}, v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s  set cs" 
    using preprocess'_unsat_indices[of i ncs] part1 unfolding preprocess_part_1_def Let_def 
    by (auto simp: ncs)
  assume "\<exists> w. (I,w) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set cs" 
  then obtain w where "(I,w) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set cs" by blast
  hence "(I,w) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set ncs" unfolding ncs .
  from preprocess'_unsat[OF this _  start_fresh_variable_fresh, of ncs]
  have "\<exists>v'. (I,v') \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as \<and> v' \<Turnstile>\<^sub>t t1"
    using part1
    unfolding preprocess_part_1_def Let_def by auto
  then show "\<exists>v'. (I,v') \<Turnstile>\<^sub>i\<^sub>a\<^sub>s set as \<and> v' \<Turnstile>\<^sub>t t"
    using part_2(4) by auto
qed

interpretation PreprocessDefault: Preprocess preprocess
  by (unfold_locales; rule preprocess, auto)

global_interpretation Solve_exec_ns'Default: Solve_exec_ns' preprocess assert_all_code
  defines solve_exec_ns_code = Solve_exec_ns'Default.solve_exec_ns
  by unfold_locales

(* -------------------------------------------------------------------------- *)
(* To_ns to_ns from_ns  *)
(* -------------------------------------------------------------------------- *)

primrec
  constraint_to_qdelta_constraint:: "constraint \<Rightarrow> QDelta ns_constraint list" where
  "constraint_to_qdelta_constraint (LT l r) = [LEQ_ns l (QDelta.QDelta r (-1))]"
| "constraint_to_qdelta_constraint (GT l r) = [GEQ_ns l (QDelta.QDelta r 1)]"
| "constraint_to_qdelta_constraint (LEQ l r) = [LEQ_ns l (QDelta.QDelta r 0)]"
| "constraint_to_qdelta_constraint (GEQ l r) = [GEQ_ns l (QDelta.QDelta r 0)]"
| "constraint_to_qdelta_constraint (EQ l r) = [LEQ_ns l (QDelta.QDelta r 0), GEQ_ns l (QDelta.QDelta r 0)]"
| "constraint_to_qdelta_constraint (LTPP l1 l2) = [LEQ_ns (l1 - l2) (QDelta.QDelta 0 (-1))]"
| "constraint_to_qdelta_constraint (GTPP l1 l2) = [GEQ_ns (l1 - l2) (QDelta.QDelta 0 1)]"
| "constraint_to_qdelta_constraint (LEQPP l1 l2) = [LEQ_ns (l1 - l2) 0]"
| "constraint_to_qdelta_constraint (GEQPP l1 l2) = [GEQ_ns (l1 - l2) 0]"
| "constraint_to_qdelta_constraint (EQPP l1 l2) = [LEQ_ns (l1 - l2) 0, GEQ_ns (l1 - l2) 0]"

primrec
  i_constraint_to_qdelta_constraint:: "'i i_constraint \<Rightarrow> ('i,QDelta) i_ns_constraint list" where
  "i_constraint_to_qdelta_constraint (i,c) = map (Pair i) (constraint_to_qdelta_constraint c)"

definition
  to_ns :: "'i i_constraint list \<Rightarrow> ('i,QDelta) i_ns_constraint list" where
  "to_ns l \<equiv> concat (map i_constraint_to_qdelta_constraint l)"

primrec
  \<delta>0_val :: "QDelta ns_constraint \<Rightarrow> QDelta valuation \<Rightarrow> rat" where
  "\<delta>0_val (LEQ_ns lll rrr) vl = \<delta>0 lll\<lbrace>vl\<rbrace> rrr"
| "\<delta>0_val (GEQ_ns lll rrr) vl = \<delta>0 rrr lll\<lbrace>vl\<rbrace>"

primrec
  \<delta>0_val_min :: "QDelta ns_constraint list \<Rightarrow> QDelta valuation \<Rightarrow> rat" where
  "\<delta>0_val_min [] vl = 1"
| "\<delta>0_val_min (h#t) vl = min (\<delta>0_val_min t vl) (\<delta>0_val h vl)"

abbreviation vars_list_constraints where
  "vars_list_constraints cs \<equiv> remdups (concat (map Abstract_Linear_Poly.vars_list (map poly cs)))"

definition
  from_ns ::"(var, QDelta) mapping \<Rightarrow> QDelta ns_constraint list \<Rightarrow> (var, rat) mapping" where
  "from_ns vl cs \<equiv> let \<delta> = \<delta>0_val_min cs \<langle>vl\<rangle> in
      Mapping.tabulate (vars_list_constraints cs) (\<lambda> var. val (\<langle>vl\<rangle> var) \<delta>)"

global_interpretation SolveExec'Default: SolveExec' to_ns from_ns solve_exec_ns_code
  defines solve_exec_code = SolveExec'Default.solve_exec
    and solve_code = SolveExec'Default.solve
proof unfold_locales
  {
    fix ics :: "'i i_constraint list" and v' and I
    let ?to_ns = "to_ns ics"
    let ?flat = "set ?to_ns"
    assume sat: "(I,\<langle>v'\<rangle>) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s ?flat"
    define cs where "cs = map snd (filter (\<lambda> ic. fst ic \<in> I) ics)"
    define to_ns' where to_ns: "to_ns' = (\<lambda> l. concat (map constraint_to_qdelta_constraint l))"
    show "(I,\<langle>from_ns v' (flat_list ?to_ns)\<rangle>) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics"  unfolding i_satisfies_cs.simps
    proof
      let ?listf = "map (\<lambda>C. case C of (LEQ_ns l r) \<Rightarrow> (l\<lbrace>\<langle>v'\<rangle>\<rbrace>, r)
                                    | (GEQ_ns l r) \<Rightarrow> (r, l\<lbrace>\<langle>v'\<rangle>\<rbrace>)
                       )"
      let ?to_ns = "\<lambda> ics. to_ns' (map snd (filter (\<lambda>ic. fst ic \<in> I) ics))"
      let ?list = "?listf (to_ns' cs)"              (* index-filtered list *)
      let ?f_list = "flat_list (to_ns ics)"
      let ?flist = "?listf ?f_list" (* full list *)
      obtain i_list where i_list: "?list = i_list" by force
      obtain f_list where f_list: "?flist = f_list" by force
      have if_list: "set i_list \<subseteq> set f_list" unfolding
          i_list[symmetric] f_list[symmetric] to_ns_def to_ns set_map set_concat cs_def
        by (intro image_mono, force)
      have "\<And> qd1 qd2. (qd1, qd2) \<in> set ?list \<Longrightarrow> qd1 \<le> qd2"
      proof-
        fix qd1 qd2
        assume "(qd1, qd2) \<in> set ?list"
        then show "qd1 \<le> qd2"
          using sat unfolding cs_def
        proof(induct ics)
          case Nil
          then show ?case
            by (simp add: to_ns)
        next
          case (Cons h t)
          obtain i c where h: "h = (i,c)" by force
          from Cons(2) consider (ic) "(qd1,qd2) \<in> set (?listf (?to_ns [(i,c)]))"
            | (t) "(qd1,qd2) \<in> set (?listf (?to_ns t))"
            unfolding to_ns h set_map set_concat by fastforce
          then show ?case
          proof cases
            case t
            from Cons(1)[OF this] Cons(3) show ?thesis unfolding to_ns_def by auto
          next
            case ic
            note ic = ic[unfolded to_ns, simplified]
            from ic have i: "(i \<in> I) = True" by (cases "i \<in> I", auto)
            note ic = ic[unfolded i if_True, simplified]
            from Cons(3)[unfolded h] i have "\<langle>v'\<rangle> \<Turnstile>\<^sub>n\<^sub>s\<^sub>s set (to_ns' [c])"
              unfolding i_satisfies_ns_constraints.simps unfolding to_ns to_ns_def by force
            with ic show ?thesis by (induct c) (auto simp add: to_ns)
          qed
        qed
      qed
      then have l1: "\<epsilon> > 0 \<Longrightarrow> \<epsilon> \<le> (\<delta>_min ?list) \<Longrightarrow> \<forall>qd1 qd2. (qd1, qd2) \<in> set ?list \<longrightarrow> val qd1 \<epsilon> \<le> val qd2 \<epsilon>" for \<epsilon>
        unfolding i_list
        by (simp add: delta_gt_zero delta_min[of i_list])
      have "\<delta>_min ?flist \<le> \<delta>_min ?list" unfolding f_list i_list
        by (rule delta_min_mono[OF if_list])
      from l1[OF delta_gt_zero this]
      have l1: "\<forall>qd1 qd2. (qd1, qd2) \<in> set ?list \<longrightarrow> val qd1 (\<delta>_min f_list) \<le> val qd2 (\<delta>_min f_list)"
        unfolding f_list .
      have "\<delta>0_val_min (flat_list (to_ns ics)) \<langle>v'\<rangle> = \<delta>_min f_list" unfolding f_list[symmetric]
      proof(induct ics)
        case Nil
        show ?case
          by (simp add: to_ns_def)
      next
        case (Cons h t)
        then show ?case
          by (cases h; cases "snd h") (auto simp add: to_ns_def)
      qed
      then have l2: "from_ns v' ?f_list = Mapping.tabulate (vars_list_constraints ?f_list) (\<lambda> var. val (\<langle>v'\<rangle> var) (\<delta>_min f_list))"
        by (auto simp add: from_ns_def)
      fix c
      assume "c \<in> restrict_to I (set ics)"
      then obtain i where i: "i \<in> I" and mem: "(i,c) \<in> set ics" by auto
      from mem show "\<langle>from_ns v' ?f_list\<rangle> \<Turnstile>\<^sub>c c"
      proof (induct c)
        case (LT lll rrr)
        then have "(lll\<lbrace>\<langle>v'\<rangle>\<rbrace>, (QDelta.QDelta rrr (-1))) \<in> set ?list" using i unfolding cs_def
          by (force simp add: to_ns)
        then have "val (lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min f_list) \<le> val (QDelta.QDelta rrr (-1)) (\<delta>_min f_list)"
          using l1
          by simp
        moreover
        have "lll\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min f_list))\<rbrace> =
              lll\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace>"
        proof (rule valuate_depend, rule)
          fix x
          assume "x \<in> vars lll"
          then show "val (\<langle>v'\<rangle> x) (\<delta>_min f_list) = \<langle>from_ns v' ?f_list\<rangle> x"
            using l2
            using LT
            by (auto simp add: comp_def lookup_tabulate restrict_map_def set_vars_list to_ns_def map2fun_def')
        qed
        ultimately
        have "lll\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace> \<le> (val (QDelta.QDelta rrr (-1)) (\<delta>_min f_list))"
          by (auto simp add: valuate_rat_valuate)
        then show ?case
          using delta_gt_zero[of f_list]
          by (simp add: val_def)
      next
        case (GT lll rrr)
        then have "((QDelta.QDelta rrr 1), lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) \<in> set ?list" using i unfolding cs_def
          by (force simp add: to_ns)
        then have "val (lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min f_list) \<ge> val (QDelta.QDelta rrr 1) (\<delta>_min f_list)"
          using l1
          by simp
        moreover
        have "lll\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min f_list))\<rbrace> =
              lll\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace>"
        proof (rule valuate_depend, rule)
          fix x
          assume "x \<in> vars lll"
          then show "val (\<langle>v'\<rangle> x) (\<delta>_min f_list) = \<langle>from_ns v' ?f_list\<rangle> x"
            using l2
            using GT
            by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
        qed
        ultimately
        have "lll\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace> \<ge> val (QDelta.QDelta rrr 1) (\<delta>_min f_list)"
          using l2
          by (simp add: valuate_rat_valuate)
        then show ?case
          using delta_gt_zero[of f_list]
          by (simp add: val_def)
      next
        case (LEQ lll rrr)
        then have "(lll\<lbrace>\<langle>v'\<rangle>\<rbrace>, (QDelta.QDelta rrr 0) ) \<in> set ?list" using i unfolding cs_def
          by (force simp add: to_ns)
        then have "val (lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min f_list) \<le> val (QDelta.QDelta rrr 0) (\<delta>_min f_list)"
          using l1
          by simp
        moreover
        have "lll\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min f_list))\<rbrace> =
              lll\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace>"
        proof (rule valuate_depend, rule)
          fix x
          assume "x \<in> vars lll"
          then show "val (\<langle>v'\<rangle> x) (\<delta>_min f_list) = \<langle>from_ns v' ?f_list\<rangle> x"
            using l2
            using LEQ
            by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
        qed
        ultimately
        have "lll\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace> \<le> val (QDelta.QDelta rrr 0) (\<delta>_min f_list)"
          using l2
          by (simp add: valuate_rat_valuate)
        then show ?case
          by (simp add: val_def)
      next
        case (GEQ lll rrr)
        then have "((QDelta.QDelta rrr 0), lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) \<in> set ?list" using i unfolding cs_def
          by (force simp add: to_ns)
        then have "val (lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min f_list) \<ge> val (QDelta.QDelta rrr 0) (\<delta>_min f_list)"
          using l1
          by simp
        moreover
        have "lll\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min f_list))\<rbrace> =
              lll\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace>"
        proof (rule valuate_depend, rule)
          fix x
          assume "x \<in> vars lll"
          then show "val (\<langle>v'\<rangle> x) (\<delta>_min f_list) = \<langle>from_ns v' ?f_list\<rangle> x"
            using l2
            using GEQ
            by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
        qed
        ultimately
        have "lll\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace> \<ge> val (QDelta.QDelta rrr 0) (\<delta>_min f_list)"
          using l2
          by (simp add: valuate_rat_valuate)
        then show ?case
          by (simp add: val_def)
      next
        case (EQ lll rrr)
        then have "((QDelta.QDelta rrr 0), lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) \<in> set ?list" and
          "(lll\<lbrace>\<langle>v'\<rangle>\<rbrace>, (QDelta.QDelta rrr 0) ) \<in> set ?list" using i unfolding cs_def
          by (force simp add: to_ns)+
        then have "val (lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min f_list) \<ge> val (QDelta.QDelta rrr 0) (\<delta>_min f_list)" and
          "val (lll\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min f_list) \<le> val (QDelta.QDelta rrr 0) (\<delta>_min f_list)"
          using l1
          by simp_all
        moreover
        have "lll\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min f_list))\<rbrace> =
              lll\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace>"
        proof (rule valuate_depend, rule)
          fix x
          assume "x \<in> vars lll"
          then show "val (\<langle>v'\<rangle> x) (\<delta>_min f_list) = \<langle>from_ns v' ?f_list\<rangle> x"
            using l2
            using EQ
            by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
        qed
        ultimately
        have "lll\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace> \<ge> val (QDelta.QDelta rrr 0) (\<delta>_min f_list)" and
          "lll\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace> \<le> val (QDelta.QDelta rrr 0) (\<delta>_min f_list)"
          using l1
          by (auto simp add: valuate_rat_valuate)
        then show ?case
          by (simp add: val_def)
      next
        case (LTPP ll1 ll2)
        then have "((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>, (QDelta.QDelta 0 (-1)) ) \<in> set ?list" using i unfolding cs_def
          by (force simp add: to_ns)
        then have "val ((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min f_list) \<le> val (QDelta.QDelta 0 (-1)) (\<delta>_min f_list)"
          using l1
          by simp
        moreover
        have "(ll1-ll2)\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min f_list))\<rbrace> =
              (ll1-ll2)\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace>"
        proof (rule valuate_depend, rule)
          fix x
          assume "x \<in> vars (ll1 - ll2)"
          then show "val (\<langle>v'\<rangle> x) (\<delta>_min f_list) = \<langle>from_ns v' ?f_list\<rangle> x"
            using l2
            using LTPP
            by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
        qed
        ultimately
        have "(ll1-ll2)\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace> \<le> val (QDelta.QDelta 0 (-1)) (\<delta>_min f_list)"
          using l1
          by (simp add: valuate_rat_valuate)
        then show ?case
          using delta_gt_zero[of f_list]
          by (simp add: val_def valuate_minus)
      next
        case (GTPP ll1 ll2)
        then have "((QDelta.QDelta 0 1), (ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) \<in> set ?list" using i unfolding cs_def
          by (force simp add: to_ns)
        then have "val ((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min f_list) \<ge> val (QDelta.QDelta 0 1) (\<delta>_min f_list)"
          using l1
          by simp
        moreover
        have "(ll1-ll2)\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min f_list))\<rbrace> =
              (ll1-ll2)\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace>"
        proof (rule valuate_depend, rule)
          fix x
          assume "x \<in> vars (ll1 - ll2)"
          then show "val (\<langle>v'\<rangle> x) (\<delta>_min f_list) = \<langle>from_ns v' ?f_list\<rangle> x"
            using l2
            using GTPP
            by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
        qed
        ultimately
        have "(ll1-ll2)\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace> \<ge> val (QDelta.QDelta 0 1) (\<delta>_min f_list)"
          using l1
          by (simp add: valuate_rat_valuate)
        then show ?case
          using delta_gt_zero[of f_list]
          by (simp add: val_def valuate_minus)
      next
        case (LEQPP ll1 ll2)
        then have "((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>, (QDelta.QDelta 0 0) ) \<in> set ?list" using i unfolding cs_def
          by (force simp add: to_ns zero_QDelta_def)
        then have "val ((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min f_list) \<le> val (QDelta.QDelta 0 0) (\<delta>_min f_list)"
          using l1
          by simp
        moreover
        have "(ll1-ll2)\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min f_list))\<rbrace> =
              (ll1-ll2)\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace>"
        proof (rule valuate_depend, rule)
          fix x
          assume "x \<in> vars (ll1 - ll2)"
          then show "val (\<langle>v'\<rangle> x) (\<delta>_min f_list) = \<langle>from_ns v' ?f_list\<rangle> x"
            using l2
            using LEQPP
            by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
        qed
        ultimately
        have "(ll1-ll2)\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace> \<le> val (QDelta.QDelta 0 0) (\<delta>_min f_list)"
          using l1
          by (simp add: valuate_rat_valuate)
        then show ?case
          using delta_gt_zero[of f_list]
          by (simp add: val_def valuate_minus)
      next
        case (GEQPP ll1 ll2)
        then have "((QDelta.QDelta 0 0), (ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) \<in> set ?list" using i unfolding cs_def
          by (force simp add: to_ns zero_QDelta_def)
        then have "val ((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min f_list) \<ge> val (QDelta.QDelta 0 0) (\<delta>_min f_list)"
          using l1
          by simp
        moreover
        have "(ll1-ll2)\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min f_list))\<rbrace> =
              (ll1-ll2)\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace>"
        proof (rule valuate_depend, rule)
          fix x
          assume "x \<in> vars (ll1 - ll2)"
          then show "val (\<langle>v'\<rangle> x) (\<delta>_min f_list) = \<langle>from_ns v' ?f_list\<rangle> x"
            using l2
            using GEQPP
            by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
        qed
        ultimately
        have "(ll1-ll2)\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace> \<ge> val (QDelta.QDelta 0 0) (\<delta>_min f_list)"
          using l1
          by (simp add: valuate_rat_valuate)
        then show ?case
          using delta_gt_zero[of f_list]
          by (simp add: val_def valuate_minus)
      next
        case (EQPP ll1 ll2)
        then have "((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>, (QDelta.QDelta 0 0) ) \<in> set ?list" and
          "((QDelta.QDelta 0 0), (ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) \<in> set ?list" using i unfolding cs_def
          by (force simp add: to_ns zero_QDelta_def)+
        then have "val ((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min f_list) \<ge> val (QDelta.QDelta 0 0) (\<delta>_min f_list)" and
          "val ((ll1-ll2)\<lbrace>\<langle>v'\<rangle>\<rbrace>) (\<delta>_min f_list) \<le> val (QDelta.QDelta 0 0) (\<delta>_min f_list)"
          using l1
          by simp_all
        moreover
        have "(ll1-ll2)\<lbrace>(\<lambda>x. val (\<langle>v'\<rangle> x) (\<delta>_min f_list))\<rbrace> =
              (ll1-ll2)\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace>"
        proof (rule valuate_depend, rule)
          fix x
          assume "x \<in> vars (ll1 - ll2)"
          then show "val (\<langle>v'\<rangle> x) (\<delta>_min f_list) = \<langle>from_ns v' ?f_list\<rangle> x"
            using l2
            using EQPP
            by (auto simp add: lookup_tabulate comp_def restrict_map_def set_vars_list to_ns_def map2fun_def')
        qed
        ultimately
        have "(ll1-ll2)\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace> \<ge> val (QDelta.QDelta 0 0) (\<delta>_min f_list)" and
          "(ll1-ll2)\<lbrace>\<langle>from_ns v' ?f_list\<rangle>\<rbrace> \<le> val (QDelta.QDelta 0 0) (\<delta>_min f_list)"
          using l1
          by (auto simp add: valuate_rat_valuate)
        then show ?case
          by (simp add: val_def valuate_minus)
      qed
    qed
  } note sat = this
  fix cs :: "('i \<times> constraint) list" 
  have set_to_ns: "set (to_ns cs) = { (i,n) | i n c. (i,c) \<in> set cs \<and> n \<in> set (constraint_to_qdelta_constraint c)}" 
    unfolding to_ns_def by auto
  show indices: "fst ` set (to_ns cs) = fst ` set cs" 
  proof 
    show "fst ` set (to_ns cs) \<subseteq> fst ` set cs" 
      unfolding set_to_ns by force
    {
      fix i
      assume "i \<in> fst ` set cs" 
      then obtain c where "(i,c) \<in> set cs" by force
      hence "i \<in> fst ` set (to_ns cs)" unfolding set_to_ns by (cases c; force)
    }
    thus "fst ` set cs \<subseteq> fst ` set (to_ns cs)" by blast
  qed
  {
    assume dist: "distinct_indices cs" 
    show "distinct_indices_ns (set (to_ns cs))" unfolding distinct_indices_ns_def
    proof (intro allI impI conjI notI)
      fix n1 n2 i 
      assume "(i,n1) \<in> set (to_ns cs)" "(i,n2) \<in> set (to_ns cs)" 
      then obtain c1 c2 where i: "(i,c1) \<in> set cs" "(i,c2) \<in> set cs" 
        and n: "n1 \<in> set (constraint_to_qdelta_constraint c1)" "n2 \<in> set (constraint_to_qdelta_constraint c2)" 
        unfolding set_to_ns by auto
      from dist 
      have "distinct (map fst cs)" unfolding distinct_indices_def by auto
      with i have c12: "c1 = c2" by (metis eq_key_imp_eq_value) 
      note n = n[unfolded c12]
      show "poly n1 = poly n2" using n by (cases c2, auto)
      show "ns_constraint_const n1 = ns_constraint_const n2" using n by (cases c2, auto)
    qed
  } note mini = this
  fix I mode
  assume unsat: "minimal_unsat_core_ns I (set (to_ns cs))"
  note unsat = unsat[unfolded minimal_unsat_core_ns_def indices]
  hence indices: "I \<subseteq> fst ` set cs" by auto
  show "minimal_unsat_core I cs"
    unfolding minimal_unsat_core_def
  proof (intro conjI indices impI allI, clarify)
    fix v
    assume v: "(I,v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs"
    let ?v = "\<lambda>var. QDelta.QDelta (v var) 0"
    have "(I,?v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s (set (to_ns cs))" using v
    proof(induct cs)
      case (Cons ic cs)
      obtain i c where ic: "ic = (i,c)" by force
      from Cons(2-) ic
      have rec: "(I,v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs" and c: "i \<in> I \<Longrightarrow> v \<Turnstile>\<^sub>c c" by auto
      {
        fix jn
        assume i: "i \<in> I" and "jn \<in> set (to_ns [(i,c)])"
        then have "jn \<in> set (i_constraint_to_qdelta_constraint (i,c))"
          unfolding to_ns_def by auto
        then obtain n where n: "n \<in> set (constraint_to_qdelta_constraint c)"
          and jn: "jn = (i,n)" by force
        from c[OF i] have c: "v \<Turnstile>\<^sub>c c" by force
        from c n jn have "?v \<Turnstile>\<^sub>n\<^sub>s snd jn"
          by (cases c) (auto simp add: less_eq_QDelta_def to_ns_def valuate_valuate_rat valuate_minus zero_QDelta_def)
      } note main = this
      from Cons(1)[OF rec] have IH: "(I,?v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s set (to_ns cs)" .
      show ?case unfolding i_satisfies_ns_constraints.simps
      proof (intro ballI)
        fix x
        assume "x \<in> snd ` (set (to_ns (ic # cs)) \<inter> I \<times> UNIV)"
        then consider (1) "x \<in> snd ` (set (to_ns cs) \<inter> I \<times> UNIV)"
          | (2) "x \<in> snd ` (set (to_ns [(i,c)]) \<inter> I \<times> UNIV)"
          unfolding ic to_ns_def by auto
        then show "?v \<Turnstile>\<^sub>n\<^sub>s x"
        proof cases
          case 1
          then show ?thesis using IH by auto
        next
          case 2
          then obtain jn where x: "snd jn = x" and "jn \<in> set (to_ns [(i,c)]) \<inter> I \<times> UNIV"
            by auto
          with main[of jn] show ?thesis unfolding to_ns_def by auto
        qed
      qed
    qed (simp add: to_ns_def)
    with unsat show False unfolding minimal_unsat_core_ns_def by simp blast
  next
    fix J
    assume *: "distinct_indices cs" "J \<subset> I" 
    hence "distinct_indices_ns (set (to_ns cs))" 
      using mini by auto
    with * unsat obtain v where model: "(J, v) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s  set (to_ns cs)" by blast
    define w where "w = Mapping.Mapping (\<lambda> x. Some (v x))"
    have "v = \<langle>w\<rangle>" unfolding w_def map2fun_def
      by (intro ext, transfer, auto)
    with model have model: "(J, \<langle>w\<rangle>) \<Turnstile>\<^sub>i\<^sub>n\<^sub>s\<^sub>s  set (to_ns cs)" by auto
    from sat[OF this]
    show " \<exists>v. (J, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs" by blast
  qed
qed

(* cleanup *)

hide_const (open) le lt LE GE LB UB LI UI LBI UBI UBI_upd le_rat
  inv zero Var add flat flat_list restrict_to look upd



(* -------------------------------------------------------------------------- *)
(* Main soundness lemma and executability *)
(* -------------------------------------------------------------------------- *)

text \<open>Simplex version with indexed constraints as input\<close>

definition simplex_index :: "'i i_constraint list \<Rightarrow> 'i list + (var, rat) mapping" where
  "simplex_index = solve_exec_code"

lemma simplex_index:
  "simplex_index cs = Unsat I \<Longrightarrow> set I \<subseteq> fst ` set cs \<and> \<not> (\<exists> v. (set I, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs) \<and> 
     (distinct_indices cs \<longrightarrow> (\<forall> J \<subset> set I. (\<exists> v. (J, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs)))" \<comment> \<open>minimal unsat core\<close>
  "simplex_index cs = Sat v \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s (snd ` set cs)" \<comment> \<open>satisfying assingment\<close>
proof (unfold simplex_index_def)
  assume "solve_exec_code cs = Unsat I"
  from SolveExec'Default.simplex_unsat0[OF this]
  have core: "minimal_unsat_core (set I) cs" by auto
  then show "set I \<subseteq> fst ` set cs \<and> \<not> (\<exists> v. (set I, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs) \<and>
    (distinct_indices cs \<longrightarrow> (\<forall>J\<subset>set I. \<exists>v. (J, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs))"
    unfolding minimal_unsat_core_def by auto
next
  assume "solve_exec_code cs = Sat v"
  from SolveExec'Default.simplex_sat0[OF this]
  show "\<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s (snd ` set cs)" .
qed

text \<open>Simplex version where indices will be created\<close>

definition simplex where "simplex cs = simplex_index (zip [0..<length cs] cs)"

lemma simplex:
  "simplex cs = Unsat I \<Longrightarrow> \<not> (\<exists> v. v \<Turnstile>\<^sub>c\<^sub>s set cs)" \<comment> \<open>unsat of original constraints\<close>
  "simplex cs = Unsat I \<Longrightarrow> set I \<subseteq> {0..<length cs} \<and> \<not> (\<exists> v. v \<Turnstile>\<^sub>c\<^sub>s {cs ! i | i. i \<in> set I})
    \<and> (\<forall>J\<subset>set I. \<exists>v. v \<Turnstile>\<^sub>c\<^sub>s {cs ! i |i. i \<in> J})" \<comment> \<open>minimal unsat core\<close>
  "simplex cs = Sat v \<Longrightarrow> \<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s set cs"  \<comment> \<open>satisfying assignment\<close>
proof (unfold simplex_def)
  let ?cs = "zip [0..<length cs] cs"
  assume "simplex_index ?cs = Unsat I"
  from simplex_index(1)[OF this]
  have index: "set I \<subseteq> {0 ..< length cs}" and
    core: "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s (snd ` (set ?cs \<inter> set I \<times> UNIV))" 
    "(distinct_indices (zip [0..<length cs] cs) \<longrightarrow> (\<forall> J \<subset> set I. \<exists>v. v \<Turnstile>\<^sub>c\<^sub>s (snd ` (set ?cs \<inter> J \<times> UNIV))))" 
    by (auto simp flip: set_map)
  note core(2)
  also have "distinct_indices (zip [0..<length cs] cs)" 
    unfolding distinct_indices_def set_zip by (auto simp: set_conv_nth)
  also have "(\<forall> J \<subset> set I. \<exists>v. v \<Turnstile>\<^sub>c\<^sub>s (snd ` (set ?cs \<inter> J \<times> UNIV))) =
    (\<forall> J \<subset> set I. \<exists>v. v \<Turnstile>\<^sub>c\<^sub>s { cs ! i | i.  i \<in> J})" using index
    by (intro all_cong1 imp_cong ex_cong1 arg_cong[of _ _ "\<lambda> x. _ \<Turnstile>\<^sub>c\<^sub>s x"] refl, force simp: set_zip)
  finally have core': "(\<forall>J\<subset>set I. \<exists>v. v \<Turnstile>\<^sub>c\<^sub>s {cs ! i |i. i \<in> J}) " .
  note unsat = unsat_mono[OF core(1)]
  show "\<not> (\<exists> v. v \<Turnstile>\<^sub>c\<^sub>s set cs)"
    by (rule unsat, auto simp: set_zip)
  show "set I \<subseteq> {0..<length cs} \<and> \<not> (\<exists> v. v \<Turnstile>\<^sub>c\<^sub>s {cs ! i | i. i \<in> set I})
    \<and> (\<forall>J\<subset>set I. \<exists>v. v \<Turnstile>\<^sub>c\<^sub>s {cs ! i |i. i \<in> J})"
    by (intro conjI index core', rule unsat, auto simp: set_zip)
next
  assume "simplex_index (zip [0..<length cs] cs) = Sat v"
  from simplex_index(2)[OF this]
  show "\<langle>v\<rangle> \<Turnstile>\<^sub>c\<^sub>s set cs" by (auto simp flip: set_map)
qed

text \<open>check executability\<close>

lemma "case simplex [LTPP (lp_monom 2 1) (lp_monom 3 2 - lp_monom 3 0), GT (lp_monom 1 1) 5]
   of Sat _ \<Rightarrow> True | Unsat _ \<Rightarrow> False"
  by eval

text \<open>check unsat core\<close>

lemma
  "case simplex_index [
    (1 :: int, LT (lp_monom 1 1) 4),
    (2, GTPP (lp_monom 2 1) (lp_monom 1 2)),
    (3, EQPP (lp_monom 1 1) (lp_monom 2 2)),
    (4, GT (lp_monom 2 2) 5),
    (5, GT (lp_monom 3 0) 7)]
    of Sat _ \<Rightarrow> False | Unsat I \<Rightarrow> set I = {1,3,4}" \<comment> \<open>Constraints 1,3,4 are unsat core\<close>
  by eval

end