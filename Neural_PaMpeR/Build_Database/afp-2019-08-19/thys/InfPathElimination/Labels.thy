theory Labels
imports Aexp Bexp
begin

(* DEF : 2 *)
(* LEM : 0 *)

section \<open>Labels\<close>

text \<open>In the following, we model programs by control flow graphs where edges (rather than vertices) are labelled 
with either assignments or with the condition associated with a branch of a conditional statement.
We put a label on every edge : statements that do not modify the program state (like \verb?jump?, 
\verb?break?, etc) are labelled by a @{term Skip}.\<close>


datatype ('v,'d) label = Skip | Assume "('v,'d) bexp" | Assign 'v "('v,'d) aexp"


text \<open>We say that a label is \emph{finite} if the set of variables of its sub-expression is 
finite (@{term Skip} labels are thus considered finite).\<close>


definition finite_label ::
  "('v,'d) label \<Rightarrow> bool"
where
  "finite_label l \<equiv> case l of 
                    Assume e   \<Rightarrow> finite (Bexp.vars e) 
                  | Assign _ e \<Rightarrow> finite (Aexp.vars e) 
                  | _          \<Rightarrow> True"

abbreviation finite_labels :: 
  "('v,'d) label list \<Rightarrow> bool" 
where
  "finite_labels ls \<equiv> (\<forall> l \<in> set ls. finite_label l)"

end
