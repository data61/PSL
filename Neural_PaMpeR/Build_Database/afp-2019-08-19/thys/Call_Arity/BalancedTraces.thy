theory BalancedTraces
imports Main
begin

locale traces = 
  fixes step :: "'c => 'c => bool"  (infix "\<Rightarrow>" 50) 
begin

abbreviation steps (infix "\<Rightarrow>\<^sup>*" 50) where "steps \<equiv> step\<^sup>*\<^sup>*"

inductive trace :: "'c \<Rightarrow> 'c list \<Rightarrow> 'c \<Rightarrow> bool"  where
  trace_nil[iff]: "trace final [] final"
| trace_cons[intro]: "trace conf' T final \<Longrightarrow> conf \<Rightarrow> conf' \<Longrightarrow> trace conf (conf'#T) final"

inductive_cases trace_consE: "trace conf (conf'#T) final"

lemma trace_induct_final[consumes 1, case_names trace_nil trace_cons]:
  "trace x1 x2 final \<Longrightarrow> P final [] final \<Longrightarrow> (\<And>conf' T  conf. trace conf' T final \<Longrightarrow> P conf' T final \<Longrightarrow> conf \<Rightarrow> conf' \<Longrightarrow> P conf (conf' # T) final) \<Longrightarrow> P x1 x2 final"
  by (induction rule:trace.induct) auto

lemma build_trace:
  "c \<Rightarrow>\<^sup>* c' \<Longrightarrow> \<exists> T. trace c T c'"
proof(induction rule: converse_rtranclp_induct)
  have "trace c' [] c'"..
  thus "\<exists>T. trace c' T c'"..
next
  fix y z
  assume "y \<Rightarrow> z"
  assume "\<exists>T. trace z T c'"
  then obtain T where "trace z T c'"..
  with \<open>y \<Rightarrow> z\<close>
  have "trace y (z#T) c'" by auto
  thus "\<exists>T. trace y T c'" by blast
qed

lemma destruct_trace:  "trace c T c' \<Longrightarrow> c \<Rightarrow>\<^sup>* c'"
  by (induction rule:trace.induct) auto

lemma traceWhile:
  assumes "trace c\<^sub>1 T c\<^sub>4"
  assumes "P c\<^sub>1"
  assumes "\<not> P c\<^sub>4"
  obtains  T\<^sub>1 c\<^sub>2 c\<^sub>3 T\<^sub>2
  where "T = T\<^sub>1 @ c\<^sub>3 # T\<^sub>2"  and "trace c\<^sub>1 T\<^sub>1 c\<^sub>2" and "\<forall>x\<in>set T\<^sub>1.  P x" and "P c\<^sub>2" and "c\<^sub>2 \<Rightarrow> c\<^sub>3" and "\<not> P c\<^sub>3" and "trace c\<^sub>3 T\<^sub>2 c\<^sub>4"
proof-
  from assms
  have "\<exists> T\<^sub>1 c\<^sub>2 c\<^sub>3 T\<^sub>2 . (T = T\<^sub>1 @ c\<^sub>3 # T\<^sub>2 \<and> trace c\<^sub>1 T\<^sub>1 c\<^sub>2 \<and> (\<forall>x\<in>set T\<^sub>1. P x) \<and> P c\<^sub>2 \<and> c\<^sub>2 \<Rightarrow> c\<^sub>3 \<and> \<not> P c\<^sub>3 \<and> trace c\<^sub>3 T\<^sub>2 c\<^sub>4)"
  proof(induction)
    case trace_nil thus ?case by auto
  next
    case (trace_cons conf' T "end" conf)
    thus ?case 
    proof (cases "P conf'")
    case True
      from trace_cons.IH[OF True \<open>\<not> P end\<close>]
      obtain T\<^sub>1 c\<^sub>2 c\<^sub>3 T\<^sub>2 where "T = T\<^sub>1 @ c\<^sub>3 # T\<^sub>2 \<and> trace conf' T\<^sub>1 c\<^sub>2 \<and> (\<forall>x\<in>set T\<^sub>1. P x) \<and> P c\<^sub>2 \<and> c\<^sub>2 \<Rightarrow> c\<^sub>3 \<and> \<not> P c\<^sub>3 \<and> trace c\<^sub>3 T\<^sub>2 end" by auto
      with True
      have "conf' # T = (conf' # T\<^sub>1) @ c\<^sub>3 # T\<^sub>2 \<and> trace conf (conf' # T\<^sub>1) c\<^sub>2 \<and> (\<forall>x\<in>set (conf' # T\<^sub>1). P x)  \<and> P c\<^sub>2 \<and> c\<^sub>2 \<Rightarrow> c\<^sub>3 \<and> \<not> P c\<^sub>3  \<and> trace c\<^sub>3 T\<^sub>2 end" by (auto intro: trace_cons)
      thus ?thesis by blast
    next
    case False with trace_cons
      have "conf' # T = [] @ conf' # T \<and> (\<forall>x\<in>set []. P x) \<and> P conf \<and> conf \<Rightarrow> conf' \<and> \<not> P conf' \<and> trace conf' T end" by auto
      thus ?thesis by blast
    qed
  qed
  thus ?thesis by (auto intro: that)
qed

lemma traces_list_all:
  "trace c T c' \<Longrightarrow> P c' \<Longrightarrow> (\<And> c c'. c \<Rightarrow> c' \<Longrightarrow> P c' \<Longrightarrow> P c) \<Longrightarrow> (\<forall> x\<in>set T. P x) \<and> P c"
  by (induction rule:trace.induct) auto

lemma trace_nil[simp]: "trace c [] c' \<longleftrightarrow> c = c'"
  by (metis list.distinct(1) trace.cases traces.trace_nil)
  
end

definition extends :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "\<lesssim>" 50) where
  "S \<lesssim> S' = (\<exists> S''. S' = S'' @ S)"

lemma extends_refl[simp]: "S \<lesssim> S" unfolding extends_def by auto
lemma extends_cons[simp]: "S \<lesssim> x # S" unfolding extends_def by auto
lemma extends_append[simp]: "S \<lesssim> L @ S" unfolding extends_def by auto
lemma extends_not_cons[simp]: "\<not> (x # S) \<lesssim> S" unfolding extends_def by auto
lemma extends_trans[trans]: "S \<lesssim> S' \<Longrightarrow> S' \<lesssim> S'' \<Longrightarrow> S \<lesssim> S''" unfolding extends_def by auto

locale balance_trace = traces + 
  fixes stack :: "'a \<Rightarrow> 's list"
  assumes one_step_only: "c \<Rightarrow> c' \<Longrightarrow> (stack c) = (stack c') \<or> (\<exists> x.  stack c' = x # stack c) \<or>  (\<exists> x. stack c = x # stack c')"
begin

inductive bal :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  balI[intro]: "trace c T c' \<Longrightarrow> \<forall>c'\<in> set T. stack c \<lesssim> stack c' \<Longrightarrow> stack c' = stack c \<Longrightarrow> bal c T c'"

inductive_cases balE: "bal c T c'"

lemma bal_nil[simp]: "bal c [] c' \<longleftrightarrow> c = c'"
  by (auto elim: balE trace.cases)
  

lemma bal_stackD: "bal c T c' \<Longrightarrow> stack c' = stack c" by (auto dest: balE)

lemma stack_passes_lower_bound:
  assumes "c\<^sub>3 \<Rightarrow> c\<^sub>4" 
  assumes "stack c\<^sub>2 \<lesssim> stack c\<^sub>3" 
  assumes "\<not> stack c\<^sub>2 \<lesssim> stack c\<^sub>4" 
  shows "stack c\<^sub>3 = stack c\<^sub>2" and "stack c\<^sub>4 = tl (stack c\<^sub>2)"
proof-  
  from one_step_only[OF assms(1)]
  have "stack c\<^sub>3 = stack c\<^sub>2 \<and> stack c\<^sub>4 = tl (stack c\<^sub>2)"
  proof(elim disjE exE)
    assume "stack c\<^sub>3 = stack c\<^sub>4" with assms(2,3)
    have False by auto
    thus ?thesis..
  next
    fix x
    note \<open>stack c\<^sub>2 \<lesssim> stack c\<^sub>3\<close>
    also
    assume "stack c\<^sub>4 = x # stack c\<^sub>3"
    hence "stack c\<^sub>3 \<lesssim> stack c\<^sub>4" by simp
    finally
    have "stack c\<^sub>2 \<lesssim> stack c\<^sub>4".
    with assms(3) show ?thesis..
  next
    fix x
    assume c\<^sub>3: "stack c\<^sub>3 = x # stack c\<^sub>4"
    with assms(2)
    obtain L where L: "x # stack c\<^sub>4 = L @ stack c\<^sub>2" unfolding extends_def by auto
    show ?thesis
    proof(cases L)
      case Nil with c\<^sub>3 L have "stack c\<^sub>3 = stack c\<^sub>2" by simp
      moreover
      from  Nil  c\<^sub>3 L have "stack c\<^sub>4 = tl (stack c\<^sub>2)" by (cases "stack c\<^sub>2") auto
      ultimately
      show ?thesis..
    next
      case (Cons y L')
      with L have "stack c\<^sub>4 = L' @ stack c\<^sub>2" by simp
      hence "stack c\<^sub>2 \<lesssim> stack c\<^sub>4" by simp
      with assms(3) show ?thesis..
    qed
  qed
  thus "stack c\<^sub>3 = stack c\<^sub>2" and "stack c\<^sub>4 = tl (stack c\<^sub>2)" by auto
qed


lemma bal_consE:
  assumes "bal c\<^sub>1 (c\<^sub>2 # T) c\<^sub>5"
  and c\<^sub>2: "stack c\<^sub>2 = s # stack c\<^sub>1"
  obtains T\<^sub>1 c\<^sub>3 c\<^sub>4 T\<^sub>2
  where "T = T\<^sub>1 @ c\<^sub>4 # T\<^sub>2" and  "bal c\<^sub>2 T\<^sub>1 c\<^sub>3" and "c\<^sub>3 \<Rightarrow> c\<^sub>4" "bal c\<^sub>4 T\<^sub>2 c\<^sub>5"
using assms(1)
proof(rule balE)
  
  assume c\<^sub>5: "stack c\<^sub>5 = stack c\<^sub>1"
  assume T: "\<forall> c' \<in> set (c\<^sub>2 # T). stack c\<^sub>1 \<lesssim> stack c'"

  assume "trace c\<^sub>1 (c\<^sub>2 # T) c\<^sub>5"
  hence "c\<^sub>1 \<Rightarrow> c\<^sub>2" and "trace c\<^sub>2 T c\<^sub>5" by (auto elim: trace_consE)

  note \<open>trace c\<^sub>2 T c\<^sub>5\<close>
  moreover
  have "stack c\<^sub>2 \<lesssim> stack c\<^sub>2" by simp
  moreover
  have "\<not> (stack c\<^sub>2 \<lesssim> stack c\<^sub>5)" unfolding c\<^sub>5 c\<^sub>2  by simp
  ultimately
  obtain T\<^sub>1 c\<^sub>3 c\<^sub>4 T\<^sub>2
    where "T = T\<^sub>1 @ c\<^sub>4 # T\<^sub>2" and "trace c\<^sub>2 T\<^sub>1 c\<^sub>3" and "\<forall> c' \<in> set T\<^sub>1. stack c\<^sub>2 \<lesssim> stack c'" 
     and "stack c\<^sub>2 \<lesssim> stack c\<^sub>3" and "c\<^sub>3 \<Rightarrow> c\<^sub>4" and "\<not> stack c\<^sub>2 \<lesssim> stack c\<^sub>4" and "trace c\<^sub>4 T\<^sub>2 c\<^sub>5"
     by (rule traceWhile)

  show ?thesis
  proof (rule that)
    show "T = T\<^sub>1 @ c\<^sub>4 # T\<^sub>2" by fact

    from \<open>c\<^sub>3 \<Rightarrow> c\<^sub>4\<close> \<open>stack c\<^sub>2 \<lesssim> stack c\<^sub>3\<close> \<open>\<not> stack c\<^sub>2 \<lesssim> stack c\<^sub>4\<close>
    have "stack c\<^sub>3 = stack c\<^sub>2" and c\<^sub>2': "stack c\<^sub>4 = tl (stack c\<^sub>2)" by (rule stack_passes_lower_bound)+

    from  \<open>trace c\<^sub>2 T\<^sub>1 c\<^sub>3\<close> \<open>\<forall> a \<in> set T\<^sub>1. stack c\<^sub>2 \<lesssim> stack a\<close> this(1)
    show "bal c\<^sub>2 T\<^sub>1 c\<^sub>3"..

    show "c\<^sub>3 \<Rightarrow> c\<^sub>4" by fact

    have c\<^sub>4: "stack c\<^sub>4 = stack c\<^sub>1" using c\<^sub>2 c\<^sub>2' by simp

    note  \<open>trace c\<^sub>4 T\<^sub>2 c\<^sub>5\<close> 
    moreover
    have "\<forall> a\<in>set T\<^sub>2. stack c\<^sub>4 \<lesssim> stack a" using c\<^sub>4 T \<open>T = _\<close>  by auto
    moreover
    have "stack c\<^sub>5 = stack c\<^sub>4" unfolding c\<^sub>4 c\<^sub>5..
    ultimately
    show "bal c\<^sub>4 T\<^sub>2 c\<^sub>5"..
  qed
qed

end


end  
