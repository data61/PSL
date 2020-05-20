theory Store
imports Aexp Bexp
begin

section\<open>Stores\<close>

text \<open>In this section, we introduce the type of stores, which we use to link program variables 
with their symbolic counterpart during symbolic execution. We define the notion of consistency 
of a pair of program and symbolic states w.r.t.\ a store. This notion will prove helpful when 
defining various concepts and proving facts related to subsumption (see \verb?Conf.thy?). Finally, we 
model substitutions that will be performed during symbolic execution (see \verb?SymExec.thy?) by two 
operations: @{term adapt_aexp} and @{term adapt_bexp}.\<close>

subsection \<open>Basic definitions\<close>

subsubsection \<open>The @{term "store"} type-synonym\<close>

text \<open>Symbolic execution performs over configurations (see \verb?Conf.thy?), which are pairs made 
of:
\begin{itemize} 
\item a \emph{store} mapping program variables to symbolic variables,
\item a set of boolean expressions which records constraints over symbolic variables and whose 
conjunction is the actual path predicate of the configuration.
\end{itemize}
We define stores as total functions from program variables to indexes.\<close>


type_synonym 'a store = "'a \<Rightarrow> nat"


subsubsection \<open>Symbolic variables of a store\<close>

text \<open>The symbolic variable associated to a program variable @{term "v"} by a store 
@{term "s"} is the couple @{term "(v,s v)"}.\<close>


definition symvar :: 
  "'a \<Rightarrow> 'a store \<Rightarrow> 'a symvar"
where
  "symvar v s \<equiv> (v,s v)"


text \<open>The function associating symbolic variables to program variables obtained from 
@{term "s"} is injective.\<close>


lemma 
  "inj (\<lambda> v. symvar v s)"
by (auto simp add : inj_on_def symvar_def)


text \<open>The sets of symbolic variables of a store is the image set of the function @{term "symvar"}.\<close>


definition symvars :: 
  "'a store \<Rightarrow> 'a symvar set" 
where
 "symvars s = (\<lambda> v. symvar v s) ` (UNIV::'a set)"


subsubsection \<open>Fresh symbolic variables\<close>

text \<open>A symbolic variable is said to be fresh for a store if it is not a member of its set of 
symbolic variables.\<close>


definition fresh_symvar :: 
  "'v symvar \<Rightarrow> 'v store \<Rightarrow> bool" 
where
 "fresh_symvar sv s = (sv \<notin> symvars s)"


subsection \<open>Consistency\<close>

text \<open>We say that a program state @{term "\<sigma>"} and a symbolic state @{term "\<sigma>\<^sub>s\<^sub>y\<^sub>m"} are 
\emph{consistent} with respect to a store @{term "s"} if, for each variable @{term "v"}, the 
value associated by @{term "\<sigma>"} to @{term "v"} is equal to the value associated by @{term "\<sigma>\<^sub>s\<^sub>y\<^sub>m"} 
to the symbolic variable associated to @{term "v"} by @{term "s"}.\<close>


definition consistent ::
  "('v,'d) state \<Rightarrow> ('v symvar, 'd) state \<Rightarrow> 'v store \<Rightarrow> bool"
where
  "consistent \<sigma> \<sigma>\<^sub>s\<^sub>y\<^sub>m s \<equiv> (\<forall> v. \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar v s) = \<sigma> v)"


text \<open>There always exists a couple of consistent states for a given store.\<close>


lemma
  "\<exists> \<sigma> \<sigma>\<^sub>s\<^sub>y\<^sub>m. consistent \<sigma> \<sigma>\<^sub>s\<^sub>y\<^sub>m s"
by (auto simp add : consistent_def)


text \<open>Moreover, given a store and a program (resp. symbolic) state, one can always build a symbolic 
(resp. program) state such that the two states are coherent wrt.\ the store. The four following 
lemmas show how to build the second state given the first one.\<close>


lemma consistent_eq1 :
  "consistent \<sigma> \<sigma>\<^sub>s\<^sub>y\<^sub>m s = (\<forall> sv \<in> symvars s. \<sigma>\<^sub>s\<^sub>y\<^sub>m sv = \<sigma> (fst sv))"
by (auto simp add : consistent_def symvars_def symvar_def)


lemma consistent_eq2 :
  "consistent \<sigma> \<sigma>\<^sub>s\<^sub>y\<^sub>m store = (\<sigma> = (\<lambda> v. \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar v store)))"
by (auto simp add : consistent_def)


lemma consistentI1 : 
  "consistent \<sigma> (\<lambda> sv. \<sigma> (fst sv)) store" 
using consistent_eq1 by fast


lemma consistentI2 :
  "consistent (\<lambda> v. \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar v store)) \<sigma>\<^sub>s\<^sub>y\<^sub>m store"
using consistent_eq2 by fast



subsection \<open>Adaptation of an arithmetic expression to a store\<close>

text \<open>Suppose that @{term "e"} is a term representing an arithmetic expression over program 
variables and let @{term "s"} be a store. We call \emph{adaptation of @{term "e"} to @{term "s"}} 
the term obtained by substituting occurrences of program variables in @{term "e"} by their 
symbolic counterpart given by @{term "s"}. Since we model arithmetic expressions by total 
functions and not terms, we define the adaptation of such expressions as follows.\<close>


definition adapt_aexp :: 
  "('v,'d) aexp \<Rightarrow> 'v store \<Rightarrow> ('v symvar,'d) aexp" 
where
  "adapt_aexp e s = (\<lambda> \<sigma>\<^sub>s\<^sub>y\<^sub>m. e (\<lambda> v. \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar v s)))"


text \<open>Given an arithmetic expression @{term "e"}, a program state @{term "\<sigma>"} and a symbolic 
state @{term "\<sigma>\<^sub>s\<^sub>y\<^sub>m"} coherent with a store @{term "s"}, the value associated to @{term "\<sigma>\<^sub>s\<^sub>y\<^sub>m"} by 
the adaptation of @{term "e"} to @{term "s"} is the same than the value associated by @{term "e"} to 
@{term "\<sigma>"}. This confirms the fact that @{term "adapt_aexp"} models the act of substituting 
occurrences of program variables by their symbolic counterparts in a term over program variables.\<close>


lemma adapt_aexp_is_subst :
  assumes "consistent \<sigma> \<sigma>\<^sub>s\<^sub>y\<^sub>m s" 
  shows   "(adapt_aexp e s) \<sigma>\<^sub>s\<^sub>y\<^sub>m = e \<sigma>"
using assms by (simp add : consistent_eq2 adapt_aexp_def)



text \<open>As said earlier, we will later need to prove that symbolic execution preserves finiteness 
of the set of symbolic variables in use, which requires that the adaptation of an arithmetic 
expression to a store preserves finiteness of the set of variables of expressions. We proceed as 
follows.\<close>

text \<open>First, we show that if @{term "v"} is a variable of an expression @{term "e"}, 
then the symbolic variable associated to @{term "v"} by a store is a variable of the adaptation of 
@{term "e"} to this store.\<close>


lemma var_imp_symvar_var :
  assumes "v \<in> Aexp.vars e"
  shows   "symvar v s \<in> Aexp.vars (adapt_aexp e s)" (is "?sv \<in> Aexp.vars ?e'")
proof -
  obtain \<sigma> val where "e (\<sigma> (v := val)) \<noteq> e \<sigma>" 
  using assms unfolding Aexp.vars_def by blast  
  
  moreover
  have "(\<lambda>va. ((\<lambda>sv. \<sigma> (fst sv))(?sv := val)) (symvar va s)) = (\<sigma>(v := val))"
  by (auto simp add : symvar_def)  

  ultimately
  show ?thesis
  unfolding Aexp.vars_def mem_Collect_eq
  using consistentI1[of \<sigma> s] 
        consistentI2[of "(\<lambda>sv. \<sigma> (fst sv))(?sv:= val)" s]
  by (rule_tac ?x="\<lambda>sv. \<sigma> (fst sv)" in exI, rule_tac ?x="val" in exI) 
     (simp add : adapt_aexp_is_subst)
qed


text \<open>On the other hand, if @{term "sv"} is a symbolic variable in the adaptation of an expression 
to a store, then the program variable it represents is a variable of this expression. This requires 
to prove that the set of variables of the adaptation of an expression to a store is a subset of the 
symbolic variables of this store.\<close>


lemma symvars_of_adapt_aexp :
  "Aexp.vars (adapt_aexp e s) \<subseteq> symvars s" (is "Aexp.vars ?e' \<subseteq> symvars s")
unfolding subset_iff
proof (intro allI impI)
  fix sv

  assume "sv \<in> Aexp.vars ?e'"

  then obtain \<sigma>\<^sub>s\<^sub>y\<^sub>m val 
  where "?e' (\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)) \<noteq> ?e' \<sigma>\<^sub>s\<^sub>y\<^sub>m" 
  by (simp add : Aexp.vars_def, blast)

  hence "(\<lambda> x. (\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)) (symvar x s)) \<noteq> (\<lambda> x. \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar x s))"
  proof (intro notI)
    assume "(\<lambda>x. (\<sigma>\<^sub>s\<^sub>y\<^sub>m(sv := val)) (symvar x s)) = (\<lambda>x. \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar x s))"
    
    hence "?e' (\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)) = ?e' \<sigma>\<^sub>s\<^sub>y\<^sub>m" 
    by (simp add : adapt_aexp_def)
    
    thus False 
    using \<open>?e' (\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)) \<noteq> ?e' \<sigma>\<^sub>s\<^sub>y\<^sub>m\<close> 
    by (elim notE)
  qed

  then obtain v 
  where "(\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)) (symvar v s) \<noteq> \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar v s)" 
  by blast

  hence "sv = symvar v s" by (case_tac "sv = symvar v s", simp_all)

  thus "sv \<in> symvars s" by (simp add : symvars_def)
qed


lemma symvar_var_imp_var :
  assumes "sv \<in> Aexp.vars (adapt_aexp e s)" (is "sv \<in> Aexp.vars ?e'")
  shows   "fst sv \<in> Aexp.vars e"
proof -
  obtain v where "sv = (v, s v)" 
  using assms(1) symvars_of_adapt_aexp 
  unfolding symvars_def symvar_def 
  by blast
  
  obtain \<sigma>\<^sub>s\<^sub>y\<^sub>m val where "?e' (\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)) \<noteq> ?e' \<sigma>\<^sub>s\<^sub>y\<^sub>m"
  using assms unfolding Aexp.vars_def by blast

  moreover
  have "(\<lambda> v. (\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)) (symvar v s)) = (\<lambda> v. \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar v s)) (v := val)"
  using \<open>sv = (v, s v)\<close> by (auto simp add : symvar_def)
  
  ultimately
  show ?thesis
  using \<open>sv = (v, s v)\<close> 
        consistentI2[of \<sigma>\<^sub>s\<^sub>y\<^sub>m s] 
        consistentI2[of "\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)" s]
  unfolding Aexp.vars_def 
  by (simp add : adapt_aexp_is_subst) blast
qed



text \<open>Thus, we have that the set of variables of the adaptation of an expression to a store is 
the set of symbolic variables associated by this store to the variables of this 
expression.\<close>


lemma adapt_aexp_vars :
  "Aexp.vars (adapt_aexp e s) = (\<lambda> v. symvar v s) ` Aexp.vars e"
unfolding set_eq_iff image_def mem_Collect_eq Bex_def
proof (intro allI iffI, goal_cases)
  case (1 sv)

  moreover
  have "sv = symvar (fst sv) s" 
  using 1 symvars_of_adapt_aexp 
  by (force simp add:  symvar_def symvars_def)

  ultimately
  show ?case using symvar_var_imp_var by blast
next
  case (2 sv) thus ?case using var_imp_symvar_var by fast
qed 


text \<open>The fact that the adaptation of an arithmetic expression to a store preserves finiteness 
of the set of variables trivially follows the previous lemma.\<close>


lemma finite_vars_imp_finite_adapt_a :
  assumes "finite (Aexp.vars e)"
  shows   "finite (Aexp.vars (adapt_aexp e s))"
unfolding adapt_aexp_vars using assms by auto

subsection \<open>Adaptation of a boolean expression to a store\<close>

text \<open>We proceed analogously for the adaptation of boolean expressions to a store.\<close>


definition adapt_bexp :: 
  "('v,'d) bexp \<Rightarrow> 'v store \<Rightarrow> ('v symvar,'d) bexp" 
where
  "adapt_bexp e s = (\<lambda> \<sigma>. e (\<lambda> x. \<sigma> (symvar x s)))"


lemma adapt_bexp_is_subst :
  assumes "consistent \<sigma> \<sigma>\<^sub>s\<^sub>y\<^sub>m s" 
  shows   "(adapt_bexp e s) \<sigma>\<^sub>s\<^sub>y\<^sub>m = e \<sigma>"
using assms by (simp add : consistent_eq2 adapt_bexp_def)


lemma var_imp_symvar_var2 :
  assumes "v \<in> Bexp.vars e"
  shows   "symvar v s \<in> Bexp.vars (adapt_bexp e s)" (is "?sv \<in> Bexp.vars ?e'")
proof -
  obtain \<sigma> val where A : "e (\<sigma> (v := val)) \<noteq> e \<sigma>" 
  using assms unfolding Bexp.vars_def by blast  
  
  moreover
  have "(\<lambda>va. ((\<lambda>sv. \<sigma> (fst sv))(?sv := val)) (symvar va s)) = (\<sigma>(v := val))"
  by (auto simp add : symvar_def)  

  ultimately
  show ?thesis
  unfolding Bexp.vars_def mem_Collect_eq
  using consistentI1[of \<sigma> s] 
        consistentI2[of "(\<lambda>sv. \<sigma> (fst sv))(?sv:= val)" s]
  by (rule_tac ?x="\<lambda>sv. \<sigma> (fst sv)" in exI, rule_tac ?x="val" in exI) 
     (simp add : adapt_bexp_is_subst)
qed


lemma symvars_of_adapt_bexp :
  "Bexp.vars (adapt_bexp e s) \<subseteq> symvars s" (is "Bexp.vars ?e' \<subseteq> ?SV")
proof
  fix sv
  assume "sv \<in> Bexp.vars ?e'"

  then obtain \<sigma>\<^sub>s\<^sub>y\<^sub>m val 
  where "?e' (\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)) \<noteq> ?e' \<sigma>\<^sub>s\<^sub>y\<^sub>m"
  by (simp add : Bexp.vars_def, blast)

  hence "(\<lambda> x. (\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)) (symvar x s)) \<noteq> (\<lambda> x. \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar x s))"
  by (auto simp add : adapt_bexp_def)

  hence "\<exists> v. (\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)) (symvar v s) \<noteq> \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar v s)" by force

  then obtain v 
  where "(\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)) (symvar v s) \<noteq> \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar v s)" 
  by blast

  hence "sv = symvar v s" by (case_tac "sv = symvar v s", simp_all)

  thus "sv \<in> symvars s" by (simp add : symvars_def)
qed


lemma symvar_var_imp_var2 :
  assumes "sv \<in> Bexp.vars (adapt_bexp e s)" (is "sv \<in> Bexp.vars ?e'")
  shows   "fst sv \<in> Bexp.vars e"
proof -
  obtain v where "sv = (v, s v)" 
  using assms symvars_of_adapt_bexp 
  unfolding symvars_def symvar_def 
  by blast
  
  obtain \<sigma>\<^sub>s\<^sub>y\<^sub>m val where "?e' (\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)) \<noteq> ?e' \<sigma>\<^sub>s\<^sub>y\<^sub>m"
  using assms unfolding vars_def by blast

  moreover
  have "(\<lambda> v. (\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)) (symvar v s)) = (\<lambda> v. \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar v s)) (v := val)"
  using \<open>sv = (v, s v)\<close> by (auto simp add : symvar_def)
  
  ultimately
  show ?thesis
  using \<open>sv = (v, s v)\<close> 
        consistentI2[of \<sigma>\<^sub>s\<^sub>y\<^sub>m s] 
        consistentI2[of "\<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := val)" s]
  unfolding vars_def by (simp add : adapt_bexp_is_subst) blast
qed


lemma adapt_bexp_vars :
  "Bexp.vars (adapt_bexp e s) = (\<lambda> v. symvar v s) ` Bexp.vars e"
  (is "Bexp.vars ?e' = ?R")
unfolding set_eq_iff image_def mem_Collect_eq Bex_def
proof (intro allI iffI, goal_cases)
  case (1 sv)

  hence "fst sv \<in> vars e" by (rule symvar_var_imp_var2)

  moreover
  have "sv = symvar (fst sv) s" 
  using 1 symvars_of_adapt_bexp 
  by (force simp add:  symvar_def symvars_def)

  ultimately
  show ?case by blast
next
  case (2 sv)

  then obtain v where "v \<in> vars e" "sv = symvar v s" by blast

  thus ?case using var_imp_symvar_var2 by simp
qed 


lemma finite_vars_imp_finite_adapt_b :
  assumes "finite (Bexp.vars e)"
  shows   "finite (Bexp.vars (adapt_bexp e s))"
unfolding adapt_bexp_vars using assms by auto

end
