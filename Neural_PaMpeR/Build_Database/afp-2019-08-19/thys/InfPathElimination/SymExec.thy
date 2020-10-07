theory SymExec
imports Conf Labels
begin

subsection \<open>Symbolic Execution\<close>

text \<open>We model symbolic execution by an inductive predicate @{term "se"} which takes two 
configurations @{term "c\<^sub>1"} and @{term "c\<^sub>2"} and a label @{term "l"} and evaluates to \emph{true} if 
and only if @{term "c\<^sub>2"} is a \emph{possible result} of the symbolic execution of @{term "l"} from 
@{term "c\<^sub>1"}. We say that @{term "c\<^sub>2"} is a possible result because, when @{term "l"} is of the 
form @{term "Assign v e"}, we associate a fresh symbolic variable to the program variable @{term "v"}, 
but we do no specify how this fresh variable is chosen (see the two assumptions in the third case). 
We could have model @{term "se"} (and @{term "se_star"}) by a function producing the new 
configuration, instead of using inductive predicates. However this would require to provide the two 
said assumptions in each lemma involving @{term se}, which is not necessary using a predicate. Modeling 
symbolic execution in this way has the advantage that it simplifies the following proofs while not 
requiring additional lemmas.\<close>

subsubsection \<open>Definitions of $\mathit{se}$ and $\mathit{se\_star}$\<close>

text \<open>Symbolic execution of @{term "Skip"} does not change the configuration from which it is 
performed.\<close> 

text \<open>When the label 
is of the form @{term "Assume e"}, the adaptation of @{term "e"} to the store is added to the 
@{term "pred"} component.\<close> 

text \<open>In the case of an assignment, the @{term "store"} component is updated 
such that it now maps a fresh symbolic variable to the assigned program variable. A constraint 
relating this program variable with its new symbolic value is added to the @{term "pred"} 
component.\<close>

text \<open>The second assumption in the third case requires that there exists at least one fresh 
symbolic variable for @{term "c"}. In the following, a number of theorems are needed
to show that such variables exist for the configurations on which symbolic execution is performed.  
\<close>


inductive se ::
  "('v,'d) conf \<Rightarrow> ('v,'d) label \<Rightarrow> ('v,'d) conf \<Rightarrow> bool"
where
  "se c Skip c"

| "se c (Assume e) \<lparr> store = store c, pred = pred c \<union> {adapt_bexp e (store c)} \<rparr>"

| "fst sv = v        \<Longrightarrow>
   fresh_symvar sv c \<Longrightarrow>
   se c (Assign v e) \<lparr> store = (store c)(v := snd sv), 
                       pred  = pred c \<union> {(\<lambda> \<sigma>. \<sigma> sv = (adapt_aexp e (store c)) \<sigma>)} \<rparr>"

text \<open>In the same spirit, we extend symbolic execution to sequence of labels.\<close>


inductive se_star :: "('v,'d) conf \<Rightarrow> ('v,'d) label list \<Rightarrow> ('v,'d) conf \<Rightarrow> bool" where
  "se_star c [] c"
| "se c1 l c2 \<Longrightarrow> se_star c2 ls c3 \<Longrightarrow> se_star c1 (l # ls) c3"



subsubsection \<open>Basic properties of $\mathit{se}$\<close>

text \<open>If symbolic execution yields a satisfiable configuration, then it has been performed from 
a satisfiable configuration.\<close>


lemma se_sat_imp_sat :
  assumes "se c l c'"
  assumes "sat c'"
  shows   "sat c"
using assms by cases (auto simp add : sat_def conjunct_def)


text \<open>If symbolic execution is performed from an unsatisfiable configuration, then it will yield 
an unsatisfiable configuration.\<close>


lemma unsat_imp_se_unsat :
  assumes "se c l c'"
  assumes "\<not> sat c"
  shows   "\<not> sat c'"
using assms by cases (simp add : sat_def conjunct_def)+


text \<open>Given two configurations @{term "c"} and @{term "c'"} and a label @{term "l"} such that 
@{term "se c l c'"}, the three following lemmas express @{term "c'"} as a function of @{term "c"}.\<close>


lemma [simp] :
  "se c Skip c' = (c' = c)"
by (simp add : se.simps)


lemma se_Assume_eq :
  "se c (Assume e) c' = (c' = \<lparr> store = store c, pred = pred c \<union> {adapt_bexp e (store c)} \<rparr>)"
by (simp add : se.simps)


lemma se_Assign_eq :
  "se c (Assign v e) c' = 
  (\<exists> sv. fresh_symvar sv c 
       \<and> fst sv = v 
       \<and> c' = \<lparr> store = (store c)(v := snd sv), 
                pred  = insert (\<lambda>\<sigma>. \<sigma> sv = adapt_aexp e (store c) \<sigma>) (pred c)\<rparr>)"
by (simp only : se.simps, blast)


text \<open>Given two configurations @{term "c"} and @{term "c'"} and a label @{term "l"} such that 
@{term "se c l c'"}, the two following lemmas express the path predicate of @{term "c'"} as 
a function of the path predicate of @{term "c"} when @{term "l"} models a guard or an 
assignment.\<close>


lemma path_pred_of_se_Assume :
  assumes "se c (Assume e) c'"
  shows   "conjunct (pred c') = 
            (\<lambda> \<sigma>. conjunct (pred c) \<sigma> \<and> adapt_bexp e (store c) \<sigma>)"
using assms se_Assume_eq[of c e c'] 
by (auto simp add : conjunct_def)


lemma path_pred_of_se_Assign :
  assumes "se c (Assign v e) c'"
  shows   "\<exists> sv. conjunct (pred c') = 
            (\<lambda> \<sigma>. conjunct (pred c) \<sigma> \<and> \<sigma> sv = adapt_aexp e (store c) \<sigma>)"
using assms se_Assign_eq[of c v e c']
by (fastforce simp add : conjunct_def)


text \<open>Let @{term "c"} and @{term "c'"} be two configurations  such that @{term "c'"} is obtained 
from @{term "c"} by symbolic execution of a label of the form @{term "Assume e"}. The states of 
@{term "c'"} are the states of @{term "c"} that satisfy @{term "e"}. This theorem will help prove 
that symbolic execution is monotonic wrt.\ subsumption.\<close>


theorem states_of_se_assume :
  assumes "se c (Assume e) c'"
  shows   "states c' = {\<sigma> \<in> states c. e \<sigma>}"
using assms se_Assume_eq[of c e c'] 
by (auto simp add : adapt_bexp_is_subst states_def conjunct_def)


text \<open>Let @{term "c"} and @{term "c'"} be two configurations  such that @{term "c'"} is obtained 
from @{term "c"} by symbolic execution of a label of the form @{term "Assign v e"}. We want to 
express the set of states of @{term "c'"} as a function of the set of states of @{term "c"}. Since 
the proof requires a number of details, we split into two sub lemmas.\<close>

text \<open>First, we show that if @{term "\<sigma>'"} is a state of @{term "c'"}, then it has been obtain from 
an adequate update of a state @{term "\<sigma>"} of @{term "c"}.\<close>


lemma states_of_se_assign1 :
  assumes "se c (Assign v e) c'"
  assumes "\<sigma>' \<in> states c'"
  shows   "\<exists> \<sigma> \<in> states c. \<sigma>' = (\<sigma> (v := e \<sigma>))"
proof -
  obtain \<sigma>\<^sub>s\<^sub>y\<^sub>m
  where 1 : "consistent \<sigma>' \<sigma>\<^sub>s\<^sub>y\<^sub>m (store c')"
  and   2 : "conjunct (pred c') \<sigma>\<^sub>s\<^sub>y\<^sub>m"
  using assms(2) unfolding states_def by blast

  then obtain \<sigma> 
  where 3 : "consistent \<sigma> \<sigma>\<^sub>s\<^sub>y\<^sub>m (store c)" 
  using consistentI2 by blast

  moreover
  have "conjunct (pred c) \<sigma>\<^sub>s\<^sub>y\<^sub>m" 
  using assms(1) 2 by (auto simp add : se_Assign_eq conjunct_def)
  
  ultimately
  have "\<sigma> \<in> states c" by (simp add : states_def) blast

  moreover
  have "\<sigma>' = \<sigma> (v := e \<sigma>)"
  proof -
    have "\<sigma>' v = e \<sigma>" 
    proof -
      have "\<sigma>' v = \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar v (store c'))" 
      using 1 by (simp add : consistent_def)

      moreover
      have "\<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar v (store c')) = (adapt_aexp e (store c)) \<sigma>\<^sub>s\<^sub>y\<^sub>m"
      using assms(1) 2 se_Assign_eq[of c v e c'] 
      by (force simp add : symvar_def conjunct_def)

      moreover
      have "(adapt_aexp e (store c)) \<sigma>\<^sub>s\<^sub>y\<^sub>m = e \<sigma>" 
      using 3 by (rule adapt_aexp_is_subst)
    
      ultimately
      show ?thesis by simp
    qed

    moreover
    have "\<forall> x. x \<noteq> v \<longrightarrow> \<sigma>' x = \<sigma> x" 
    proof (intro allI impI)
      fix x

      assume "x \<noteq> v"

      moreover
      hence "\<sigma>' x = \<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar x (store c))"
      using assms(1) 1 unfolding consistent_def symvar_def
      by (drule_tac ?x="x" in spec) (auto simp add : se_Assign_eq)

      moreover
      have "\<sigma>\<^sub>s\<^sub>y\<^sub>m (symvar x (store c)) = \<sigma> x" 
      using 3 by (auto simp add : consistent_def)
      
      ultimately
      show "\<sigma>' x = \<sigma> x" by simp
    qed

    ultimately
    show ?thesis by auto
  qed

  ultimately
  show ?thesis by (simp add : states_def) blast
qed


text \<open>Then, we show that if there exists a state @{term "\<sigma>"} of @{term "c"} from which 
@{term "\<sigma>'"} is obtained by an adequate update, then @{term "\<sigma>'"} is a state of @{term "c'"}.\<close>


lemma states_of_se_assign2 :
  assumes "se c (Assign v e) c'"
  assumes "\<exists> \<sigma> \<in> states c. \<sigma>' = \<sigma> (v := e \<sigma>)"
  shows   "\<sigma>' \<in> states c'"
proof -
  obtain \<sigma> 
  where "\<sigma> \<in> states c" 
  and   "\<sigma>' = \<sigma> (v := e \<sigma>)" 
  using assms(2) by blast

  then obtain \<sigma>\<^sub>s\<^sub>y\<^sub>m 
  where 1 : "consistent \<sigma> \<sigma>\<^sub>s\<^sub>y\<^sub>m (store c)"
  and   2 : "conjunct (pred c) \<sigma>\<^sub>s\<^sub>y\<^sub>m"
  unfolding states_def by blast

  obtain sv 
  where 3 : "fresh_symvar sv c"
  and   4 : "fst sv = v"
  and   5 : "c' = \<lparr> store = (store c)(v := snd sv), 
                    pred    = insert (\<lambda>\<sigma>. \<sigma> sv = adapt_aexp e (store c) \<sigma>) (pred c) \<rparr>"
  using assms(1) se_Assign_eq[of c v e c'] by blast

  define \<sigma>\<^sub>s\<^sub>y\<^sub>m' where "\<sigma>\<^sub>s\<^sub>y\<^sub>m' = \<sigma>\<^sub>s\<^sub>y\<^sub>m (sv := e \<sigma>)"
  
  have "consistent \<sigma>' \<sigma>\<^sub>s\<^sub>y\<^sub>m' (store c')"
  using \<open>\<sigma>' = \<sigma> (v := e \<sigma>)\<close> 1 4 5 
  by (auto simp add : symvar_def consistent_def \<sigma>\<^sub>s\<^sub>y\<^sub>m'_def)
  
  moreover
  have "conjunct (pred c') \<sigma>\<^sub>s\<^sub>y\<^sub>m'"
  proof -
    have "conjunct (pred c) \<sigma>\<^sub>s\<^sub>y\<^sub>m'" 
    using 2 3 by (simp add : fresh_symvar_def symvars_def Bexp.vars_def \<sigma>\<^sub>s\<^sub>y\<^sub>m'_def)

    moreover
    have "\<sigma>\<^sub>s\<^sub>y\<^sub>m' sv = (adapt_aexp e (store c)) \<sigma>\<^sub>s\<^sub>y\<^sub>m'"
    proof -
      have "Aexp.fresh sv (adapt_aexp e (store c))" 
      using 3 symvars_of_adapt_aexp[of e "store c"]
      by (auto simp add : fresh_symvar_def symvars_def)

      thus ?thesis 
      using adapt_aexp_is_subst[OF 1, of e] 
      by (simp add : Aexp.vars_def \<sigma>\<^sub>s\<^sub>y\<^sub>m'_def)
    qed

    ultimately
    show ?thesis using 5 by (simp add: conjunct_def)
  qed

  ultimately
  show ?thesis unfolding states_def by blast
qed

text \<open>The following theorem expressing the set of states of @{term c'} as a function of the set 
of states of @{term c} trivially follows the two preceding lemmas.\<close>

theorem states_of_se_assign :
  assumes "se c (Assign v e) c'"
  shows   "states c' = {\<sigma> (v := e \<sigma>) | \<sigma>. \<sigma> \<in> states c}"
using assms states_of_se_assign1 states_of_se_assign2 by fast


subsubsection \<open>Monotonicity of $\mathit{se}$\<close>

text \<open>We are now ready to prove that symbolic execution is monotonic with respect to subsumption. 
\<close>


theorem se_mono_for_sub :
  assumes "se c1 l c1'"
  assumes "se c2 l c2'"
  assumes "c2 \<sqsubseteq> c1"
  shows   "c2' \<sqsubseteq> c1'"
using assms 
by ((cases l),
    (simp add : ),
    (simp add : states_of_se_assume subsums_def, blast),
    (simp add : states_of_se_assign subsums_def, blast))


text \<open>A stronger version of the previous theorem: symbolic execution is monotonic with respect to 
states equality.\<close>


theorem se_mono_for_states_eq :
  assumes "states c1 = states c2"
  assumes "se c1 l c1'"
  assumes "se c2 l c2'"
  shows   "states c2' = states c1'"
using assms(1) 
      se_mono_for_sub[OF assms(2,3)] 
      se_mono_for_sub[OF assms(3,2)]
by (simp add : subsums_def)


text \<open>The previous theorem confirms the fact that the way the fresh symbolic variable is chosen 
in the case of symbolic execution of an assignment does not matter as long as the new symbolic 
variable is indeed fresh, which is more precisely expressed by the following lemma.\<close>


lemma se_succs_states :
  assumes "se c l c1"
  assumes "se c l c2"
  shows   "states c1 = states c2"
using assms se_mono_for_states_eq by fast


subsubsection \<open>Basic properties of $\mathit{se\_star}$\<close>

text \<open>Some simplification lemmas for @{term "se_star"}.\<close>


lemma [simp] :
  "se_star c [] c' = (c' = c)"
by (subst se_star.simps) auto


lemma se_star_Cons :
  "se_star c1 (l # ls) c2 = (\<exists> c. se c1 l c \<and> se_star c ls c2)"
by (subst (1) se_star.simps) blast


lemma se_star_one :
  "se_star c1 [l] c2 = se c1 l c2"
using se_star_Cons by force


lemma se_star_append :
  "se_star c1 (ls1 @ ls2) c2 = (\<exists> c. se_star c1 ls1 c \<and> se_star c ls2 c2)"
by (induct ls1 arbitrary : c1, simp_all add : se_star_Cons) blast


lemma se_star_append_one :
  "se_star c1 (ls @ [l]) c2 = (\<exists> c. se_star c1 ls c \<and> se c l c2)"
unfolding se_star_append se_star_one by (rule refl)


text \<open>Symbolic execution of a sequence of labels from an unsatisfiable configuration yields 
an unsatisfiable configuration.\<close>


lemma unsat_imp_se_star_unsat :
  assumes "se_star c ls c'"
  assumes "\<not> sat c"
  shows   "\<not> sat c'"
using assms 
by (induct ls arbitrary : c) 
   (simp, force simp add : se_star_Cons unsat_imp_se_unsat)


text \<open>If symbolic execution yields a satisfiable configuration, then it has been performed from 
a satisfiable configuration.\<close>


lemma se_star_sat_imp_sat :
  assumes "se_star c ls c'"
  assumes "sat c'"
  shows   "sat c"
using assms 
by (induct ls arbitrary : c) 
   (simp, force simp add : se_star_Cons se_sat_imp_sat)



subsubsection \<open>Monotonicity of $\mathit{se\_star}$\<close>

text \<open>Monotonicity of @{term "se"} extends to @{term "se_star"}.\<close>


theorem se_star_mono_for_sub :
  assumes "se_star c1 ls c1'"
  assumes "se_star c2 ls c2'"
  assumes "c2  \<sqsubseteq> c1"
  shows   "c2' \<sqsubseteq> c1'"
using assms 
by (induct ls arbitrary : c1 c2) 
   (auto simp add :  se_star_Cons se_mono_for_sub)


lemma se_star_mono_for_states_eq : 
  assumes "states c1 = states c2"
  assumes "se_star c1 ls c1'"
  assumes "se_star c2 ls c2'"
  shows   "states c2' = states c1'"
using assms(1) 
      se_star_mono_for_sub[OF assms(2,3)] 
      se_star_mono_for_sub[OF assms(3,2)]
by (simp add : subsums_def)


lemma se_star_succs_states :
  assumes "se_star c ls c1"
  assumes "se_star c ls c2"
  shows   "states c1 = states c2"
using assms se_star_mono_for_states_eq by fast


subsubsection \<open>Existence of successors\<close>

text \<open>Here, we are interested in proving that, under certain assumptions, there will always exist 
fresh symbolic variables for configurations on which symbolic execution is performed. Thus symbolic 
execution cannot ``block'' when an assignment is met. For symbolic execution not to block in this 
case, the configuration from which it is performed must be such that there exist fresh symbolic 
variables for each program variable. Such configurations are said to be \emph{updatable}.\<close> 


definition updatable :: 
  "('v,'d) conf \<Rightarrow> bool" 
where
  "updatable c \<equiv> \<forall> v. \<exists> sv. fst sv = v \<and> fresh_symvar sv c"


text \<open>The following lemma shows that being updatable is a sufficient condition for a configuration 
in order for @{term "se"} not to block.\<close>


lemma updatable_imp_ex_se_suc :
  assumes "updatable c"
  shows   "\<exists> c'. se c l c'"
using assms 
by (cases l, simp_all add :  se_Assume_eq se_Assign_eq updatable_def)


text \<open>A sufficient condition for a configuration to be updatable is that its path predicate has 
a finite number of variables. The @{term "store"} component has no influence here, since its set of 
symbolic variables is always a strict subset of the set of symbolic variables (i.e.\ there always 
exist fresh symbolic variables for a store). To establish this proof, we need the following 
intermediate lemma.\<close>

text \<open>We want to prove that if the set of symbolic variables of the path predicate of a 
configuration is finite, then we can find a fresh symbolic variable for it. However, we express this 
with a more general lemma. We show that given a finite set of symbolic variables @{term "SV"} and a
program variable @{term "v"} such that there exist symbolic variables in @{term "SV"} that are 
indexed versions of @{term "v"}, then there exists a symbolic variable for @{term "v"} whose index 
is greater or equal than the index of any other symbolic variable for @{term "v"} in @{term SV}.\<close>


lemma finite_symvars_imp_ex_greatest_symvar :
  fixes SV :: "'a symvar set"
  assumes "finite SV"
  assumes "\<exists> sv \<in> SV. fst sv = v"
  shows   "\<exists> sv  \<in> {sv \<in> SV. fst sv = v}. 
           \<forall> sv' \<in> {sv \<in> SV. fst sv = v}. snd sv' \<le> snd sv"
proof -
  have "finite (snd ` {sv \<in> SV. fst sv = v})"
  and  "snd ` {sv \<in> SV. fst sv = v} \<noteq> {}" 
  using assms by auto

  moreover
  have "\<forall> (E::nat set). finite E \<and> E \<noteq> {} \<longrightarrow> (\<exists> n \<in> E. \<forall> m \<in> E. m \<le> n)"
  by (intro allI impI, induct_tac rule : finite_ne_induct) 
     (simp+, force)

  ultimately
  obtain n 
  where "n \<in> snd ` {sv \<in> SV. fst sv = v}"
  and   "\<forall> m \<in> snd ` {sv \<in> SV. fst sv = v}. m \<le> n"
  by blast

  moreover
  then obtain sv 
  where "sv \<in> {sv \<in> SV. fst sv = v}" and "snd sv = n" 
  by blast

  ultimately
  show ?thesis by blast
qed


text \<open>Thus, a configuration whose path predicate has a finite set of variables is updatable. For
example, for any program variable @{term "v"}, the symbolic variable  \<open>(v,i+1)\<close> is fresh for 
this configuration, where @{term "i"} is the greater index associated to @{term "v"} among the 
symbolic variables of this configuration. In practice, this is how we choose the fresh symbolic 
variable.\<close>


lemma finite_pred_imp_se_updatable :
  assumes "finite (Bexp.vars (conjunct (pred c)))" (is "finite ?V")
  shows   "updatable c"
unfolding updatable_def
proof (intro allI)
  fix v

  show "\<exists>sv. fst sv = v \<and> fresh_symvar sv c"
  proof (case_tac "\<exists> sv \<in> ?V. fst sv = v", goal_cases)
    case 1

    then obtain max_sv 
    where       "max_sv \<in> ?V"
    and         "fst max_sv = v"
    and   max : "\<forall>sv'\<in>{sv \<in> ?V. fst sv = v}. snd sv' \<le> snd max_sv"
    using assms finite_symvars_imp_ex_greatest_symvar[of ?V v] 
    by blast

    show ?thesis
    using max 
    unfolding fresh_symvar_def symvars_def Store.symvars_def symvar_def
    proof (case_tac "snd max_sv \<le> store c v", goal_cases)
      case 1 thus ?case by (rule_tac ?x="(v,Suc (store c v))" in exI) auto
    next
      case 2 thus ?case by (rule_tac ?x="(v,Suc (snd max_sv))" in exI) auto
    qed
  next
    case 2 thus ?thesis
    by (rule_tac ?x="(v, Suc (store c v))" in exI)
       (auto simp add : fresh_symvar_def symvars_def Store.symvars_def symvar_def)
  qed
qed


text \<open>The path predicate of a configuration whose @{term "pred"} component is finite and whose 
elements all have finite sets of variables has a finite set of variables. Thus, this configuration 
is updatable, and it has a successor by symbolic execution of any label. The following lemma 
starts from these two assumptions and use the previous ones in order to directly get to the 
conclusion (this will ease some of the following proofs).\<close>


lemma finite_imp_ex_se_succ :
  assumes "finite (pred c)"
  assumes "\<forall> e \<in> pred c. finite (Bexp.vars e)"
  shows   "\<exists> c'. se c l c'"
using finite_pred_imp_se_updatable[OF finite_conj[OF assms(1,2)]] 
by (rule updatable_imp_ex_se_suc)


text \<open>For symbolic execution not to block \emph{along a sequence of labels}, it is not sufficient 
for the first configuration to be updatable. It must also be such that (all) its successors are 
updatable. A sufficient condition for this is that the set of variables of its path predicate is 
finite and that the sub-expression of the label that is executed also has a finite set of variables. 
Under these assumptions, symbolic execution preserves finiteness of the @{term "pred"} component and 
of the sets of variables of its elements. Thus, successors @{term "se"} are also updatable because 
they also have a path predicate with a finite set of variables. In the following, to prove 
this we need two intermediate lemmas: 
\begin{itemize}
  \item one stating that symbolic execution perserves the finiteness of the set of variables of the 
elements of the @{term "pred"} component, provided that the sub expression of the label that is 
executed has a finite set of variables, 
  \item one stating that symbolic execution preserves the finiteness of the @{term "pred"} 
component.
\end{itemize}\<close>


lemma se_preserves_finiteness1 :
  assumes "finite_label l"
  assumes "se c l c'"
  assumes "\<forall> e \<in> pred c.  finite (Bexp.vars e)"
  shows   "\<forall> e \<in> pred c'. finite (Bexp.vars e)"
proof (cases l)
  case Skip thus ?thesis using assms by (simp add : )
next
  case (Assume e) thus ?thesis 
  using assms finite_vars_imp_finite_adapt_b
  by (auto simp add : se_Assume_eq finite_label_def)
next
  case (Assign v e) 

  then obtain sv 
  where "fresh_symvar sv c"
  and   "fst sv = v"
  and   "c' = \<lparr> store = (store c)(v := snd sv),
                pred  = insert (\<lambda>\<sigma>. \<sigma> sv = adapt_aexp e (store c) \<sigma>) (pred c)\<rparr>"
  using assms(2) se_Assign_eq[of c v e c'] by blast

  moreover
  have "finite (Bexp.vars (\<lambda>\<sigma>. \<sigma> sv = adapt_aexp e (store c) \<sigma>))"
  proof -
    have "finite (Aexp.vars (\<lambda>\<sigma>. \<sigma> sv))" 
    by (auto simp add : Aexp.vars_def)

    moreover
    have "finite (Aexp.vars (adapt_aexp e (store c)))"
    using assms(1) Assign finite_vars_imp_finite_adapt_a
    by (auto simp add : finite_label_def)

    ultimately
    show ?thesis using finite_vars_of_a_eq by auto
  qed
  
  ultimately
  show ?thesis using assms by auto
qed


lemma se_preserves_finiteness2 :
  assumes "se c l c'"
  assumes "finite (pred c)"
  shows   "finite (pred c')"
using assms 
by (cases l) 
   (auto simp add :  se_Assume_eq se_Assign_eq)


text \<open>We are now ready to prove that a sufficient condition for symbolic execution not to block 
along a sequence of labels is that the @{term "pred"} component of the ``initial 
configuration'' is finite, as well as the set of variables of its elements,  and that the 
sub-expression of the label that is executed also has a finite set of variables.\<close>


lemma finite_imp_ex_se_star_succ :
  assumes "finite (pred c)"
  assumes "\<forall> e \<in> pred c. finite (Bexp.vars e)"
  assumes "finite_labels ls"
  shows   "\<exists> c'. se_star c ls c'"
using assms
proof (induct ls arbitrary : c, goal_cases)
  case 1 show ?case using se_star.simps by blast
next
  case (2 l ls c)

  then obtain c1 where "se c l c1" using finite_imp_ex_se_succ by blast

  hence "finite (pred c1)"
  and   "\<forall> e \<in> pred c1. finite (Bexp.vars e)" 
  using 2 se_preserves_finiteness1 se_preserves_finiteness2 by fastforce+

  moreover
  have "finite_labels ls" using 2 by simp

  ultimately
  obtain c2 where "se_star c1 ls c2" using 2 by blast

  thus ?case using \<open>se c l c1\<close> using se_star_Cons by blast
qed



subsection \<open>Feasibility of a sequence of labels\<close>

text \<open>A sequence of labels @{term "ls"} is said to be feasible from a configuration @{term "c"} 
if there exists a satisfiable configuration @{term "c'"} obtained by symbolic execution of 
@{term "ls"} from @{term "c"}.\<close>


definition feasible :: "('v,'d) conf \<Rightarrow> ('v,'d) label list \<Rightarrow> bool" where
  "feasible c ls \<equiv> (\<exists> c'. se_star c ls c' \<and> sat c')"


text \<open>A simplification lemma for the case where @{term "ls"} is not empty.\<close>


lemma feasible_Cons :
  "feasible c (l#ls) = (\<exists> c'. se c l c' \<and> sat c' \<and> feasible c' ls)"
proof (intro iffI, goal_cases)
  case 1 thus ?case
  using se_star_sat_imp_sat by (simp add : feasible_def se_star_Cons) blast
next
  case 2 thus ?case 
  unfolding feasible_def se_star_Cons by blast
qed


text \<open>The following theorem is very important for the rest of this formalization. It states that, 
given two 
configurations @{term "c1"} and @{term "c2"} such that @{term "c1"} subsums @{term "c2"}, then 
any feasible sequence of labels from @{term "c2"} is also feasible from @{term "c1"}. This is a crucial 
point in order to prove that our approach preserves the set of feasible paths of the original LTS. 
This proof requires a number of assumptions about the finiteness of the sequence of labels, of 
the path predicates of the two configurations and of their states of variables. 
Those assumptions are needed in order to show that there exist successors of 
both configurations by symbolic execution of the sequence of labels.\<close>


lemma subsums_imp_feasible :
  assumes "finite_labels ls"
  assumes "finite (pred c1)"
  assumes "finite (pred c2)"
  assumes "\<forall> e \<in> pred c1. finite (Bexp.vars e)"
  assumes "\<forall> e \<in> pred c2. finite (Bexp.vars e)"
  assumes "c2 \<sqsubseteq> c1"
  assumes "feasible c2 ls"
  shows   "feasible c1 ls"
using assms
proof (induct ls arbitrary : c1 c2)
  case Nil thus ?case by (simp add : feasible_def sat_sub_by_sat)
next
  case (Cons l ls c1 c2)

  then obtain c2' where "se c2 l c2'"
                  and   "sat c2'"
                  and   "feasible c2' ls"
  using feasible_Cons by blast

  obtain c1' where "se c1 l c1'"
  using finite_conj[OF Cons(3,5)]
        finite_pred_imp_se_updatable
        updatable_imp_ex_se_suc
  by blast

  moreover
  hence "sat c1'" 
  using  se_mono_for_sub[OF _ \<open>se c2 l c2'\<close> Cons(7)]
         sat_sub_by_sat[OF \<open>sat c2'\<close>]
  by fast

  moreover
  have "feasible c1' ls"
  proof -

    have "finite_label  l" 
    and  "finite_labels ls" using Cons(2) by simp_all

    have "finite (pred c1')" 
    by (rule se_preserves_finiteness2[OF \<open>se c1 l c1'\<close> Cons(3)])
     
    moreover
    have "finite (pred c2')" 
    by (rule se_preserves_finiteness2[OF \<open>se c2 l c2'\<close> Cons(4)])

    moreover
    have "\<forall>e\<in>pred c1'. finite (Bexp.vars e)" 
    by (rule se_preserves_finiteness1[OF \<open>finite_label l\<close> \<open>se c1 l c1'\<close> Cons(5)])

    moreover
    have "\<forall>e\<in>pred c2'. finite (Bexp.vars e)"
    by (rule se_preserves_finiteness1[OF \<open>finite_label l\<close> \<open>se c2 l c2'\<close> Cons(6)])
    
    moreover
    have "c2' \<sqsubseteq> c1'" 
    by (rule se_mono_for_sub[OF \<open>se c1 l c1'\<close> \<open>se c2 l c2'\<close> Cons(7)])
    
    ultimately
    show ?thesis using Cons(1) \<open>feasible c2' ls\<close> \<open>finite_labels ls\<close> by fast
  qed

  ultimately
  show ?case by (auto simp add : feasible_Cons)
qed



subsection \<open>Concrete execution\<close>

text \<open>We illustrate our notion of symbolic execution by relating it with @{term ce}, an inductive 
predicate describing concrete execution. Unlike symbolic execution, concrete execution describes 
program behavior given program states, i.e.\ concrete valuations for program variables. The 
goal of this section is to show that our notion of symbolic execution is correct, that is: given two 
configurations such that one results from the symbolic execution of a sequence of labels from the 
other, then the resulting configuration represents the set of states that are reachable by 
concrete execution from the states of the original configuration.\<close>

inductive ce ::
  "('v,'d) state \<Rightarrow> ('v,'d) label \<Rightarrow> ('v,'d) state \<Rightarrow> bool"
where
  "ce \<sigma> Skip \<sigma>"
| "e \<sigma> \<Longrightarrow> ce \<sigma> (Assume e) \<sigma>"
| "ce \<sigma> (Assign v e) (\<sigma>(v := e \<sigma>))"

inductive ce_star :: "('v,'d) state \<Rightarrow> ('v,'d) label list \<Rightarrow> ('v,'d) state \<Rightarrow> bool" where
  "ce_star c [] c"
| "ce c1 l c2 \<Longrightarrow> ce_star c2 ls c3 \<Longrightarrow> ce_star c1 (l # ls) c3"

lemma [simp] :
  "ce \<sigma> Skip \<sigma>' = (\<sigma>' = \<sigma>)"
by (auto simp add : ce.simps)

lemma [simp] :
  "ce \<sigma> (Assume e) \<sigma>' = (\<sigma>' = \<sigma> \<and> e \<sigma>)"
by (auto simp add : ce.simps)

lemma [simp] :
  "ce \<sigma> (Assign v e) \<sigma>' = (\<sigma>' = \<sigma>(v := e \<sigma>))"
by (auto simp add : ce.simps)

lemma se_as_ce :
  assumes "se c l c'"
  shows   "states c' = {\<sigma>'. \<exists> \<sigma> \<in> states c. ce \<sigma> l \<sigma>'} "
using assms
by (cases l)
   (auto simp add: states_of_se_assume states_of_se_assign)


lemma [simp] :
  "ce_star \<sigma> [] \<sigma>' = (\<sigma>' = \<sigma>)"
by (subst ce_star.simps) simp

lemma ce_star_Cons :
  "ce_star \<sigma>1 (l # ls) \<sigma>2 = (\<exists> \<sigma>. ce \<sigma>1 l \<sigma> \<and> ce_star \<sigma> ls \<sigma>2)"
by (subst (1) ce_star.simps) blast

lemma se_star_as_ce_star :
  assumes "se_star c ls c'"
  shows   "states c' = {\<sigma>'. \<exists> \<sigma> \<in> states c. ce_star \<sigma> ls \<sigma>'}"
using assms
proof (induct ls arbitrary : c)
  case Nil thus ?case by simp
next
  case (Cons l ls c)

  then obtain c'' where "se c l c''"
                  and   "se_star c'' ls c'"
  using se_star_Cons by blast

  show ?case
  unfolding set_eq_iff Bex_def mem_Collect_eq
  proof (intro allI iffI, goal_cases)
    case (1 \<sigma>')

    then obtain \<sigma>'' where "\<sigma>'' \<in> states c''"
                    and   "ce_star \<sigma>'' ls \<sigma>'"
    using Cons(1) \<open>se_star c'' ls c'\<close> by blast

    moreover
    then obtain \<sigma> where "\<sigma> \<in> states c"
                  and   "ce \<sigma> l \<sigma>''"
    using \<open>se c l c''\<close>  se_as_ce by blast

    ultimately
    show ?case by (simp add: ce_star_Cons) blast
  next
    case (2 \<sigma>')

    then obtain \<sigma> where "\<sigma> \<in> states c"
                  and   "ce_star \<sigma> (l#ls) \<sigma>'"
    by blast
    
    moreover
    then obtain \<sigma>'' where "ce \<sigma> l \<sigma>''"
                    and   "ce_star \<sigma>'' ls \<sigma>'"
    using ce_star_Cons by blast

    ultimately
    show ?case
    using Cons(1) \<open>se_star c'' ls c'\<close> \<open>se c l c''\<close> by (auto simp add : se_as_ce)
  qed
qed

end
