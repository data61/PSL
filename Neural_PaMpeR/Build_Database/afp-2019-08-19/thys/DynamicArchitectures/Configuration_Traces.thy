(*
  Title:      Configuration_Traces.thy
  Author:     Diego Marmsoler
*)
section "A Theory of Dynamic Architectures"
text \<open>
  The following theory formalizes configuration traces~\cite{Marmsoler2016a,Marmsoler2016} as a model for dynamic architectures.
  Since configuration traces may be finite as well as infinite, the theory depends on Lochbihler's theory of co-inductive lists~\cite{Lochbihler2010}.
\<close>
theory Configuration_Traces
  imports Coinductive.Coinductive_List
begin
text \<open>
  In the following we first provide some preliminary results for natural numbers, extended natural numbers, and lazy lists.
  Then, we introduce a locale @text{dynamic\_architectures} which introduces basic definitions and corresponding properties for dynamic architectures.
\<close>
  
subsection "Natural Numbers"
text \<open>
  We provide one additional property for natural numbers.
\<close>
lemma boundedGreatest:
  assumes "P (i::nat)"
    and "\<forall>n' > n. \<not> P n'"
  shows "\<exists>i'\<le>n. P i' \<and> (\<forall>n'. P n' \<longrightarrow> n'\<le>i')"
proof -
  have "P (i::nat) \<Longrightarrow> n\<ge>i \<Longrightarrow> \<forall>n' > n. \<not> P n' \<Longrightarrow> (\<exists>i'\<le>n. P i' \<and> (\<forall>n'\<le>n. P n' \<longrightarrow> n'\<le>i'))"
  proof (induction n)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then show ?case
    proof cases
      assume "i = Suc n"
      then show ?thesis using Suc.prems by auto
    next
      assume "\<not>(i = Suc n)"
      thus ?thesis
      proof cases
        assume "P (Suc n)"
        thus ?thesis by auto
      next
        assume "\<not> P (Suc n)"
        with Suc.prems have "\<forall>n' > n. \<not> P n'" using Suc_lessI by blast
        moreover from \<open>\<not>(i = Suc n)\<close> have "i \<le> n" and "P i" using Suc.prems by auto
        ultimately obtain i' where "i'\<le>n \<and> P i' \<and> (\<forall>n'\<le>n. P n' \<longrightarrow> n' \<le> i')" using Suc.IH by blast
        hence "i' \<le> n" and "P i'" and "(\<forall>n'\<le>n. P n' \<longrightarrow> n' \<le> i')" by auto
        thus ?thesis by (metis le_SucI le_Suc_eq)
      qed
    qed
  qed
  moreover have "n\<ge>i"
  proof (rule ccontr)
    assume "\<not> (n \<ge> i)"
    hence "n < i" by arith
    thus False using assms by blast
  qed
  ultimately obtain i' where "i'\<le>n" and "P i'" and "\<forall>n'\<le>n. P n' \<longrightarrow> n' \<le> i'" using assms by blast
  with assms have "\<forall>n'. P n' \<longrightarrow> n' \<le> i'" using not_le_imp_less by blast
  with \<open>i' \<le> n\<close> and \<open>P i'\<close> show ?thesis by auto
qed

subsection "Extended Natural Numbers"
text \<open>
  We provide one simple property for the \emph{strict} order over extended natural numbers.
\<close>
lemma enat_min:
  assumes "m \<ge> enat n'"
    and "enat n < m - enat n'"
  shows "enat n + enat n' < m" 
  using assms by (metis add.commute enat.simps(3) enat_add_mono enat_add_sub_same le_iff_add)

subsection "Lazy Lists"
text \<open>
  In the following we provide some additional notation and properties for lazy lists.
\<close>
notation LNil ("[]\<^sub>l")
notation LCons (infixl "#\<^sub>l" 60)
notation lappend (infixl "@\<^sub>l" 60)

lemma lnth_lappend[simp]:
  assumes "lfinite xs"
    and "\<not> lnull ys"
  shows "lnth (xs @\<^sub>l ys) (the_enat (llength xs)) = lhd ys"
proof -
  from assms have "\<exists>k. llength xs = enat k" using lfinite_conv_llength_enat by auto
  then obtain k where "llength xs = enat k" by blast
  hence "lnth (xs @\<^sub>l ys) (the_enat (llength xs)) = lnth ys 0"
    using lnth_lappend2[of xs k k ys] by simp
  with assms show ?thesis using lnth_0_conv_lhd by simp
qed

lemma lfilter_ltake:
  assumes "\<forall>(n::nat)\<le>llength xs. n\<ge>i \<longrightarrow> (\<not> P (lnth xs n))"
  shows "lfilter P xs = lfilter P (ltake i xs)"
proof -
  have "lfilter P xs = lfilter P ((ltake i xs) @\<^sub>l (ldrop i xs))"
    using lappend_ltake_ldrop[of "(enat i)" xs] by simp
  hence "lfilter P xs = (lfilter P ((ltake i) xs)) @\<^sub>l (lfilter P (ldrop i xs))" by simp
  show ?thesis
  proof cases
    assume "enat i \<le> llength xs"
  
    have "\<forall>x<llength (ldrop i xs). \<not> P (lnth (ldrop i xs) x)"
    proof (rule allI)
      fix x show "enat x < llength (ldrop (enat i) xs) \<longrightarrow> \<not> P (lnth (ldrop (enat i) xs) x)"
      proof
        assume "enat x < llength (ldrop (enat i) xs)"
        moreover have "llength (ldrop (enat i) xs) = llength xs - enat i"
          using llength_ldrop[of "enat i"] by simp
        ultimately have "enat x < llength xs - enat i" by simp
        with \<open>enat i \<le> llength xs\<close> have "enat x + enat i < llength xs"
          using enat_min[of i "llength xs" x] by simp
        moreover have "enat i + enat x = enat x + enat i" by simp
        ultimately have "enat i + enat x < llength xs" by arith
        hence "i + x < llength xs" by simp
        hence "lnth (ldrop i xs) x = lnth xs (x + the_enat i)" using lnth_ldrop[of "enat i" "x" xs] by simp
        moreover have "x + i \<ge> i" by simp
        with assms \<open>i + x < llength xs\<close> have "\<not> P (lnth xs (x + the_enat i))"
          by (simp add: assms(1) add.commute)
        ultimately show "\<not> P (lnth (ldrop i xs) x)" using assms by simp
      qed
    qed
    hence "lfilter P (ldrop i xs) = []\<^sub>l" by (metis diverge_lfilter_LNil in_lset_conv_lnth)
    with \<open>lfilter P xs = (lfilter P ((ltake i) xs)) @\<^sub>l (lfilter P (ldrop i xs))\<close>
      show "lfilter P xs = lfilter P (ltake i xs)" by simp
  next
    assume "\<not> enat i \<le> llength xs"
    hence "enat i > llength xs" by simp
    hence "ldrop i xs = []\<^sub>l" by simp
    hence "lfilter P (ldrop i xs) = []\<^sub>l" using lfilter_LNil[of P] by arith
    with \<open>lfilter P xs = (lfilter P ((ltake i) xs)) @\<^sub>l (lfilter P (ldrop i xs))\<close>
      show "lfilter P xs = lfilter P (ltake i xs)" by simp        
  qed
qed

lemma lfilter_lfinite[simp]:
  assumes "lfinite (lfilter P t)"
    and "\<not> lfinite t"
  shows "\<exists>n. \<forall>n'>n. \<not> P (lnth t n')"
proof -
  from assms have "finite {n. enat n < llength t \<and> P (lnth t n)}" using lfinite_lfilter by auto
  then obtain k
    where sset: "{n. enat n < llength t \<and> P (lnth t n)} \<subseteq> {n. n<k \<and> enat n < llength t \<and> P (lnth t n)}"
    using finite_nat_bounded[of "{n. enat n < llength t \<and> P (lnth t n)}"] by auto
  show ?thesis
  proof (rule ccontr)
    assume "\<not>(\<exists>n. \<forall>n'>n. \<not> P (lnth t n'))"
    hence "\<forall>n. \<exists>n'>n. P (lnth t n')" by simp
    then obtain n' where "n'>k" and "P (lnth t n')" by auto
    moreover from \<open>\<not> lfinite t\<close> have "n' < llength t" by (simp add: not_lfinite_llength)
    ultimately have "n' \<notin> {n. n<k \<and> enat n < llength t \<and> P (lnth t n)}" and
      "n'\<in>{n. enat n < llength t \<and> P (lnth t n)}" by auto
    with sset show False by auto
  qed
qed

subsection "Specifying Dynamic Architectures"
text \<open>
  In the following we formalize dynamic architectures in terms of configuration traces, i.e., sequences of architecture configurations.
  Moreover, we introduce definitions for operations to support the specification of configuration traces.
\<close>
typedecl cnf
type_synonym trace = "nat \<Rightarrow> cnf"
consts arch:: "trace set"

type_synonym cta = "trace \<Rightarrow> nat \<Rightarrow> bool"

subsubsection "Implication"

definition imp :: "cta \<Rightarrow> cta \<Rightarrow> cta" (infixl "\<longrightarrow>\<^sup>c" 10)
  where "\<gamma> \<longrightarrow>\<^sup>c \<gamma>' \<equiv> \<lambda> t n. \<gamma> t n \<longrightarrow> \<gamma>' t n"

declare imp_def[simp]

lemma impI[intro!]:
  fixes t n
  assumes "\<gamma> t n \<Longrightarrow> \<gamma>' t n"
  shows "(\<gamma> \<longrightarrow>\<^sup>c \<gamma>') t n" using assms by simp

lemma impE[elim!]:
  fixes t n
  assumes "(\<gamma> \<longrightarrow>\<^sup>c \<gamma>') t n" and "\<gamma> t n" and "\<gamma>' t n \<Longrightarrow> \<gamma>'' t n"
  shows "\<gamma>'' t n" using assms by simp

subsubsection "Disjunction"  
    
definition disj :: "cta \<Rightarrow> cta \<Rightarrow> cta" (infixl "\<or>\<^sup>c" 15)
  where "\<gamma> \<or>\<^sup>c \<gamma>' \<equiv> \<lambda> t n. \<gamma> t n \<or> \<gamma>' t n"

declare disj_def[simp]

lemma disjI1[intro]:
  assumes "\<gamma> t n"
  shows "(\<gamma> \<or>\<^sup>c \<gamma>') t n" using assms by simp

lemma disjI2[intro]:
  assumes "\<gamma>' t n"
  shows "(\<gamma> \<or>\<^sup>c \<gamma>') t n" using assms by simp

lemma disjE[elim!]:
  assumes "(\<gamma> \<or>\<^sup>c \<gamma>') t n"
    and "\<gamma> t n \<Longrightarrow> \<gamma>'' t n"
    and "\<gamma>' t n \<Longrightarrow> \<gamma>'' t n"
  shows "\<gamma>'' t n" using assms by auto

subsubsection "Conjunction"
  
definition conj :: "cta \<Rightarrow> cta \<Rightarrow> cta" (infixl "\<and>\<^sup>c" 20)
  where "\<gamma> \<and>\<^sup>c \<gamma>' \<equiv> \<lambda> t n. \<gamma> t n \<and> \<gamma>' t n"

declare conj_def[simp]

lemma conjI[intro!]:
  fixes n
  assumes "\<gamma> t n" and "\<gamma>' t n"
  shows "(\<gamma> \<and>\<^sup>c \<gamma>') t n" using assms by simp

lemma conjE[elim!]:
  fixes n
  assumes "(\<gamma> \<and>\<^sup>c \<gamma>') t n" and "\<gamma> t n \<Longrightarrow> \<gamma>' t n \<Longrightarrow> \<gamma>'' t n"
  shows "\<gamma>'' t n" using assms by simp

subsubsection "Negation"
  
definition neg :: "cta \<Rightarrow> cta" ("\<not>\<^sup>c _" [19] 19)
  where "\<not>\<^sup>c \<gamma> \<equiv> \<lambda> t n. \<not> \<gamma> t n"

declare neg_def[simp]

lemma negI[intro!]:
  assumes "\<gamma> t n \<Longrightarrow> False"
  shows "(\<not>\<^sup>c \<gamma>) t n" using assms by auto

lemma negE[elim!]:
  assumes "(\<not>\<^sup>c \<gamma>) t n"
    and "\<gamma> t n"
  shows "\<gamma>' t n" using assms by simp

subsubsection "Quantifiers"

definition all :: "('a \<Rightarrow> cta)
  \<Rightarrow> cta" (binder "\<forall>\<^sub>c" 10)
  where "all P \<equiv> \<lambda>t n. (\<forall>y. (P y t n))"

declare all_def[simp]

lemma allI[intro!]:
  assumes "\<And>x. \<gamma> x t n"
  shows "(\<forall>\<^sub>cx. \<gamma> x) t n" using assms by simp

lemma allE[elim!]:
  fixes n
  assumes "(\<forall>\<^sub>cx. \<gamma> x) t n" and "\<gamma> x t n \<Longrightarrow> \<gamma>' t n"
  shows "\<gamma>' t n" using assms by simp

definition ex :: "('a \<Rightarrow> cta)
  \<Rightarrow> cta" (binder "\<exists>\<^sub>c" 10)
  where "ex P \<equiv> \<lambda>t n. (\<exists>y. (P y t n))"

declare ex_def[simp]

lemma exI[intro!]:
  assumes "\<gamma> x t n"
  shows "(\<exists>\<^sub>cx. \<gamma> x) t n" using assms HOL.exI by simp

lemma exE[elim!]:
  assumes "(\<exists>\<^sub>cx. \<gamma> x) t n" and "\<And>x. \<gamma> x t n \<Longrightarrow> \<gamma>' t n"
  shows "\<gamma>' t n" using assms HOL.exE by auto

subsubsection "Atomic Assertions"
text \<open>
  First we provide rules for basic behavior assertions.
\<close>

definition ca :: "(cnf \<Rightarrow> bool) \<Rightarrow> cta"
  where "ca \<phi> \<equiv> \<lambda> t n. \<phi> (t n)"

lemma caI[intro]:
  fixes n
  assumes "\<phi> (t n)"
  shows "(ca \<phi>) t n" using assms ca_def by simp

lemma caE[elim]:
  fixes n
  assumes "(ca \<phi>) t n"
  shows "\<phi> (t n)" using assms ca_def by simp

subsubsection "Next Operator"

definition nxt :: "cta \<Rightarrow> cta" ("\<circle>\<^sub>c(_)" 24)
  where "\<circle>\<^sub>c(\<gamma>) \<equiv> \<lambda>(t::(nat \<Rightarrow> cnf)) n. \<gamma> t (Suc n)"

subsubsection "Eventually Operator"  

definition evt :: "cta \<Rightarrow> cta" ("\<diamond>\<^sub>c(_)" 23)
  where "\<diamond>\<^sub>c(\<gamma>) \<equiv> \<lambda>(t::(nat \<Rightarrow> cnf)) n. \<exists>n'\<ge>n. \<gamma> t n'"

subsubsection "Globally Operator"

definition glob :: "cta \<Rightarrow> cta" ("\<box>\<^sub>c(_)" 22)
  where "\<box>\<^sub>c(\<gamma>) \<equiv> \<lambda>(t::(nat \<Rightarrow> cnf)) n. \<forall>n'\<ge>n. \<gamma> t n'"

lemma globI[intro!]:
  fixes n'
  assumes "\<forall>n\<ge>n'. \<gamma> t n"
  shows "(\<box>\<^sub>c(\<gamma>)) t n'" using assms glob_def by simp

lemma globE[elim!]:
  fixes n n'
  assumes "(\<box>\<^sub>c(\<gamma>)) t n" and "n'\<ge>n"
  shows "\<gamma> t n'" using assms glob_def by simp

subsubsection "Until Operator"

definition until :: "cta \<Rightarrow> cta \<Rightarrow> cta" (infixl "\<UU>\<^sub>c" 21)
  where "\<gamma>' \<UU>\<^sub>c \<gamma> \<equiv> \<lambda>(t::(nat \<Rightarrow> cnf)) n. \<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')"

lemma untilI[intro]:
  fixes n
  assumes "\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n'<n'' \<longrightarrow> \<gamma>' t n')"
  shows "(\<gamma>' \<UU>\<^sub>c \<gamma>) t n" using assms until_def by simp

lemma untilE[elim]:
  fixes n
  assumes "(\<gamma>' \<UU>\<^sub>c \<gamma>) t n"
  shows "\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n'<n'' \<longrightarrow> \<gamma>' t n')" using assms until_def by simp

subsubsection "Weak Until"

definition wuntil :: "cta \<Rightarrow> cta \<Rightarrow> cta" (infixl "\<WW>\<^sub>c" 20)
  where "\<gamma>' \<WW>\<^sub>c \<gamma> \<equiv> \<gamma>' \<UU>\<^sub>c \<gamma> \<or>\<^sup>c \<box>\<^sub>c(\<gamma>')"

lemma wUntilI[intro]:
  fixes n
  assumes "(\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n'<n'' \<longrightarrow> \<gamma>' t n')) \<or> (\<forall>n'\<ge>n. \<gamma>' t n')"
  shows "(\<gamma>' \<WW>\<^sub>c \<gamma>) t n" using assms wuntil_def by auto

lemma wUntilE[elim]:
  fixes n n'
  assumes "(\<gamma>' \<WW>\<^sub>c \<gamma>) t n"
  shows "(\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n'<n'' \<longrightarrow> \<gamma>' t n')) \<or> (\<forall>n'\<ge>n. \<gamma>' t n')"
proof -
  from assms have "(\<gamma>' \<UU>\<^sub>c \<gamma> \<or>\<^sup>c \<box>\<^sub>c(\<gamma>')) t n" using wuntil_def by simp
  hence "(\<gamma>' \<UU>\<^sub>c \<gamma>) t n \<or> (\<box>\<^sub>c(\<gamma>')) t n" by simp
  thus ?thesis
  proof
    assume "(\<gamma>' \<UU>\<^sub>c \<gamma>) t n"
    hence "\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')" by auto
    thus ?thesis by auto
  next
    assume "(\<box>\<^sub>c\<gamma>') t n"
    hence "\<forall>n'\<ge>n. \<gamma>' t n'" by auto
    thus ?thesis by auto
  qed
qed

lemma wUntil_Glob:
  assumes "(\<gamma>' \<WW>\<^sub>c \<gamma>) t n"
    and "(\<box>\<^sub>c(\<gamma>' \<longrightarrow>\<^sup>c \<gamma>'')) t n"
  shows "(\<gamma>'' \<WW>\<^sub>c \<gamma>) t n"
proof
  from assms(1) have "(\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')) \<or> (\<forall>n'\<ge>n. \<gamma>' t n')" using wUntilE by simp
  thus "(\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>'' t n')) \<or> (\<forall>n'\<ge>n. \<gamma>'' t n')"
  proof
    assume "\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')"
    show "(\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>'' t n')) \<or> (\<forall>n'\<ge>n. \<gamma>'' t n')"
    proof -
      from \<open>\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n')\<close> obtain n'' where "n''\<ge>n" and "\<gamma> t n''" and a1: "\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>' t n'" by auto
      moreover have "\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>'' t n'"
      proof
        fix n'
        show "n'\<ge>n \<longrightarrow> n'< n'' \<longrightarrow> \<gamma>'' t n'"
        proof (rule HOL.impI[OF HOL.impI])
          assume "n'\<ge>n" and "n'<n''"
          with assms(2) have "(\<gamma>' \<longrightarrow>\<^sup>c \<gamma>'') t n'" using globE by simp
          hence "\<gamma>' t n' \<longrightarrow> \<gamma>'' t n'" using impE by auto
          moreover from a1 \<open>n'\<ge>n\<close> \<open>n'<n''\<close> have "\<gamma>' t n'" by simp
          ultimately show "\<gamma>'' t n'" by simp
        qed
      qed
      ultimately show ?thesis by auto
    qed
  next
    assume a1: "\<forall>n'\<ge>n. \<gamma>' t n'"
    have "\<forall>n'\<ge>n. \<gamma>'' t n'"
    proof
      fix n'
      show "n'\<ge>n \<longrightarrow> \<gamma>'' t n'"
      proof
        assume "n'\<ge>n"
        with assms(2) have "(\<gamma>' \<longrightarrow>\<^sup>c \<gamma>'') t n'" using globE by simp
        hence "\<gamma>' t n' \<longrightarrow> \<gamma>'' t n'" using impE by auto
        moreover from a1 \<open>n'\<ge>n\<close> have "\<gamma>' t n'" by simp
        ultimately show "\<gamma>'' t n'" by simp
      qed
    qed
    thus "(\<exists>n''\<ge>n. \<gamma> t n'' \<and> (\<forall>n'\<ge>n. n' < n'' \<longrightarrow> \<gamma>'' t n')) \<or> (\<forall>n'\<ge>n. \<gamma>'' t n')" by simp
  qed
qed

subsection "Dynamic Components"
text \<open>
  To support the specification of patterns over dynamic architectures we provide a locale for dynamic components.
  It takes the following type parameters:
  \begin{itemize}
    \item id: a type for component identifiers
    \item cmp: a type for components
    \item cnf: a type for architecture configurations
  \end{itemize}
\<close>
locale dynamic_component =
  fixes tCMP :: "'id \<Rightarrow> cnf \<Rightarrow> 'cmp" ("\<sigma>\<^bsub>_\<^esub>(_)" [0,110]60)
    and active :: "'id \<Rightarrow> cnf \<Rightarrow> bool" ("\<parallel>_\<parallel>\<^bsub>_\<^esub>" [0,110]60)
begin
  
text \<open>
  The locale requires two parameters:
  \begin{itemize}
    \item @{term tCMP} is an operator to obtain a component with a certain identifier from an architecture configuration.
    \item @{term active} is a predicate to assert whether a certain component is activated within an architecture configuration.
  \end{itemize}
\<close>

text \<open>
  The locale provides some general properties about its parameters and introduces six important operators over configuration traces:
  \begin{itemize}
    \item An operator to extract the behavior of a certain component out of a given configuration trace.
    \item An operator to obtain the number of activations of a certain component within a given configuration trace.
    \item An operator to obtain the least point in time (before a certain point in time) from which on a certain component is not activated anymore.
    \item An operator to obtain the latest point in time where a certain component was activated.
    \item Two operators to map time-points between configuration traces and behavior traces.
  \end{itemize}
  Moreover, the locale provides several properties about the operators and their relationships.
\<close>

lemma nact_active:
  fixes t::"nat \<Rightarrow> cnf"
    and n::nat
    and n''
    and id
  assumes "\<parallel>id\<parallel>\<^bsub>t n\<^esub>"
    and "n'' \<ge> n"    
    and "\<not> (\<exists>n'\<ge>n. n' < n'' \<and> \<parallel>id\<parallel>\<^bsub>t n'\<^esub>)"    
  shows "n=n''"
  using assms le_eq_less_or_eq by auto

lemma nact_exists:
  fixes t::"nat \<Rightarrow> cnf"
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  shows "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub> \<and> (\<nexists>k. n\<le>k \<and> k<i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
proof -
  let ?L = "LEAST i. (i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  from assms have "?L\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t ?L\<^esub>" using LeastI[of "\<lambda>x::nat. (x\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t x\<^esub>)"] by auto
  moreover have "\<nexists>k. n\<le>k \<and> k<?L \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>" using not_less_Least by auto
  ultimately show ?thesis by blast
qed

lemma lActive_least:
  assumes "\<exists>i\<ge>n. i < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
  shows "\<exists>i\<ge>n. (i < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub> \<and> (\<nexists>k. n\<le>k \<and> k<i \<and> k<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>))"
proof -
  let ?L = "LEAST i. (i\<ge>n \<and> i < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>)"
  from assms have "?L\<ge>n \<and> ?L < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t ?L\<^esub>"
    using LeastI[of "\<lambda>x::nat.(x\<ge>n \<and> x<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t x\<^esub>)"] by auto
  moreover have "\<nexists>k. n\<le>k \<and> k<llength t \<and> k<?L \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>" using not_less_Least by auto
  ultimately show ?thesis by blast
qed

subsection "Projection"
text \<open>
  In the following we introduce an operator which extracts the behavior of a certain component out of a given configuration trace.
\<close>

definition proj:: "'id \<Rightarrow> (cnf llist) \<Rightarrow> ('cmp llist)" ("\<pi>\<^bsub>_\<^esub>(_)" [0,110]60) 
  where "proj c = lmap (\<lambda>cnf. (\<sigma>\<^bsub>c\<^esub>(cnf))) \<circ> (lfilter (active c))"

lemma proj_lnil [simp,intro]:
  "\<pi>\<^bsub>c\<^esub>([]\<^sub>l) = []\<^sub>l" using proj_def by simp

lemma proj_lnull [simp]:
  "\<pi>\<^bsub>c\<^esub>(t) = []\<^sub>l \<longleftrightarrow> (\<forall>k \<in> lset t. \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>)"
proof
  assume "\<pi>\<^bsub>c\<^esub>(t) = []\<^sub>l"
  hence "lfilter (active c) t = []\<^sub>l" using proj_def lmap_eq_LNil by auto
  thus "\<forall>k \<in> lset t. \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>" using lfilter_eq_LNil[of "active c"] by simp
next
  assume "\<forall>k\<in>lset t. \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>"
  hence "lfilter (active c) t = []\<^sub>l" by simp
  thus "\<pi>\<^bsub>c\<^esub>(t) = []\<^sub>l" using proj_def by simp
qed
  
lemma proj_LCons [simp]:
  "\<pi>\<^bsub>i\<^esub>(x #\<^sub>l xs) = (if \<parallel>i\<parallel>\<^bsub>x\<^esub> then (\<sigma>\<^bsub>i\<^esub>(x)) #\<^sub>l (\<pi>\<^bsub>i\<^esub>(xs)) else \<pi>\<^bsub>i\<^esub>(xs))"
  using proj_def by simp
    
lemma proj_llength[simp]:
  "llength (\<pi>\<^bsub>c\<^esub>(t)) \<le> llength t"
  using llength_lfilter_ile proj_def by simp

lemma proj_ltake:
  assumes "\<forall>(n'::nat)\<le>llength t. n'\<ge>n \<longrightarrow> (\<not> \<parallel>c\<parallel>\<^bsub>lnth t n'\<^esub>)"
  shows "\<pi>\<^bsub>c\<^esub>(t) = \<pi>\<^bsub>c\<^esub>(ltake n t)" using lfilter_ltake proj_def assms by (metis comp_apply)
    
lemma proj_finite_bound:
  assumes "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
  shows "\<exists>n. \<forall>n'>n. \<not> \<parallel>c\<parallel>\<^bsub>t n'\<^esub>"
  using assms lfilter_lfinite[of "active c" "inf_llist t"] proj_def by simp

subsubsection "Monotonicity and Continuity"

lemma proj_mcont:
  shows "mcont lSup lprefix lSup lprefix (proj c)"
proof -
  have "mcont lSup lprefix lSup lprefix (\<lambda>x. lmap (\<lambda>cnf. \<sigma>\<^bsub>c\<^esub>(cnf)) (lfilter (active c) x))"
    by simp
  moreover have "(\<lambda>x. lmap (\<lambda>cnf. \<sigma>\<^bsub>c\<^esub>(cnf)) (lfilter (active c) x)) =
    lmap (\<lambda>cnf. \<sigma>\<^bsub>c\<^esub>(cnf)) \<circ> lfilter (active c)" by auto
  ultimately show ?thesis using proj_def by simp
qed

lemma proj_mcont2mcont:
  assumes "mcont lub ord lSup lprefix f"
  shows "mcont lub ord lSup lprefix (\<lambda>x. \<pi>\<^bsub>c\<^esub>(f x))"
proof -
  have "mcont lSup lprefix lSup lprefix (proj c)" using proj_mcont by simp
  with assms show ?thesis using llist.mcont2mcont[of lSup lprefix "proj c"] by simp
qed
    
lemma proj_mono_prefix[simp]:
  assumes "lprefix t t'"
  shows "lprefix (\<pi>\<^bsub>c\<^esub>(t)) (\<pi>\<^bsub>c\<^esub>(t'))"
proof -
  from assms have "lprefix (lfilter (active c) t) (lfilter (active c) t')" using lprefix_lfilterI by simp
  hence "lprefix (lmap (\<lambda>cnf. \<sigma>\<^bsub>c\<^esub>(cnf)) (lfilter (active c) t))
    (lmap (\<lambda>cnf. \<sigma>\<^bsub>c\<^esub>(cnf)) (lfilter (active c) t'))" using lmap_lprefix by simp
  thus ?thesis using proj_def by simp
qed
 
subsubsection "Finiteness"
    
lemma proj_finite[simp]:
  assumes "lfinite t"
  shows "lfinite (\<pi>\<^bsub>c\<^esub>(t))"
  using assms proj_def by simp

lemma proj_finite2:
  assumes "\<forall>(n'::nat)\<le>llength t. n'\<ge>n \<longrightarrow> (\<not> \<parallel>c\<parallel>\<^bsub>lnth t n'\<^esub>)"
  shows "lfinite (\<pi>\<^bsub>c\<^esub>(t))" using assms proj_ltake proj_finite by simp

lemma proj_append_lfinite[simp]:
  fixes t t'
  assumes "lfinite t"
  shows "\<pi>\<^bsub>c\<^esub>(t @\<^sub>l t') = (\<pi>\<^bsub>c\<^esub>(t)) @\<^sub>l (\<pi>\<^bsub>c\<^esub>(t'))" (is "?lhs=?rhs")
proof -
  have "?lhs = (lmap (\<lambda>cnf. \<sigma>\<^bsub>c\<^esub>(cnf)) \<circ> (lfilter (active c))) (t @\<^sub>l t')" using proj_def by simp
  also have "\<dots> = lmap (\<lambda>cnf. \<sigma>\<^bsub>c\<^esub>(cnf)) (lfilter (active c) (t @\<^sub>l t'))" by simp
  also from assms have "\<dots> = lmap (\<lambda>cnf. \<sigma>\<^bsub>c\<^esub>(cnf))
    ((lfilter (active c) t) @\<^sub>l (lfilter (active c) t'))" by simp
  also have "\<dots> = (@\<^sub>l) (lmap (\<lambda>cnf. \<sigma>\<^bsub>c\<^esub>(cnf)) (lfilter (active c) t))
    (lmap (\<lambda>cnf. \<sigma>\<^bsub>c\<^esub>(cnf)) (lfilter (active c) t'))" using lmap_lappend_distrib by simp
  also have "\<dots> = ?rhs" using proj_def by simp
  finally show ?thesis .
qed
  
lemma proj_one:
  assumes "\<exists>i. i < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
  shows "llength (\<pi>\<^bsub>c\<^esub>(t)) \<ge> 1"
proof -
  from assms have "\<exists>x\<in>lset t. \<parallel>c\<parallel>\<^bsub>x\<^esub>" using lset_conv_lnth by force
  hence "\<not> lfilter (\<lambda>k. \<parallel>c\<parallel>\<^bsub>k\<^esub>) t = []\<^sub>l" using lfilter_eq_LNil[of "(\<lambda>k. \<parallel>c\<parallel>\<^bsub>k\<^esub>)"] by blast
  hence "\<not> \<pi>\<^bsub>c\<^esub>(t) = []\<^sub>l" using proj_def by fastforce
  thus ?thesis by (simp add: ileI1 lnull_def one_eSuc)
qed

subsubsection "Projection not Active"
  
lemma proj_not_active[simp]:
  assumes "enat n < llength t"
    and "\<not> \<parallel>c\<parallel>\<^bsub>lnth t n\<^esub>"
  shows "\<pi>\<^bsub>c\<^esub>(ltake (Suc n) t) = \<pi>\<^bsub>c\<^esub>(ltake n t)" (is "?lhs = ?rhs")
proof -
  from assms have "ltake (enat (Suc n)) t = (ltake (enat n) t) @\<^sub>l ((lnth t n) #\<^sub>l []\<^sub>l)"
    using ltake_Suc_conv_snoc_lnth by blast
  hence "?lhs = \<pi>\<^bsub>c\<^esub>((ltake (enat n) t) @\<^sub>l ((lnth t n) #\<^sub>l []\<^sub>l))" by simp
  moreover have "\<dots> = (\<pi>\<^bsub>c\<^esub>(ltake (enat n) t)) @\<^sub>l (\<pi>\<^bsub>c\<^esub>((lnth t n) #\<^sub>l []\<^sub>l))" by simp
  moreover from assms have "\<pi>\<^bsub>c\<^esub>((lnth t n) #\<^sub>l []\<^sub>l) = []\<^sub>l" by simp
  ultimately show ?thesis by simp
qed

lemma proj_not_active_same:
  assumes "enat n \<le> (n'::enat)"
      and "\<not> lfinite t \<or> n'-1 < llength t"
      and "\<nexists>k. k\<ge>n \<and> k<n' \<and> k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
    shows "\<pi>\<^bsub>c\<^esub>(ltake n' t) = \<pi>\<^bsub>c\<^esub>(ltake n t)"
proof -
  have "\<pi>\<^bsub>c\<^esub>(ltake (n + (n' - n)) t) = \<pi>\<^bsub>c\<^esub>((ltake n t) @\<^sub>l (ltake (n'-n) (ldrop n t)))"
    by (simp add: ltake_plus_conv_lappend)
  hence "\<pi>\<^bsub>c\<^esub>(ltake (n + (n' - n)) t) =
    (\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l (\<pi>\<^bsub>c\<^esub>(ltake (n'-n) (ldrop n t)))" by simp
  moreover have "\<pi>\<^bsub>c\<^esub>(ltake (n'-n) (ldrop n t)) = []\<^sub>l"
  proof -
    have "\<forall>k\<in>{lnth (ltake (n' - enat n) (ldrop (enat n) t)) na |
      na. enat na < llength (ltake (n' - enat n) (ldrop (enat n) t))}. \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>"
    proof
      fix k assume "k\<in>{lnth (ltake (n' - enat n) (ldrop (enat n) t)) na |
        na. enat na < llength (ltake (n' - enat n) (ldrop (enat n) t))}"
      then obtain k' where "enat k' < llength (ltake (n' - enat n) (ldrop (enat n) t))"
        and "k=lnth (ltake (n' - enat n) (ldrop (enat n) t)) k'" by auto
      have "enat (k' + n) < llength t"
      proof -
        from \<open>enat k' < llength (ltake (n' - enat n) (ldrop (enat n) t))\<close> have "enat k' < n'-n" by simp
        hence "enat k' + n < n'" using assms(1) enat_min by auto
        show ?thesis
        proof cases
          assume "lfinite t"
          with \<open>\<not> lfinite t \<or> n'-1 < llength t\<close> have "n'-1<llength t" by simp
          hence "n'< eSuc (llength t)" by (metis eSuc_minus_1 enat_minus_mono1 leD leI)
          hence "n'\<le> llength t" using eSuc_ile_mono ileI1 by blast
          with \<open>enat k' + n < n'\<close> show ?thesis by (simp add: add.commute)
        next
          assume "\<not> lfinite t"
          hence "llength t = \<infinity>" using not_lfinite_llength by auto
          thus ?thesis by simp
        qed
      qed
      moreover have "k = lnth t (k' + n)"
      proof -
        from \<open>enat k' < llength (ltake (n' - enat n) (ldrop (enat n) t))\<close>
          have "enat k'<n' - enat n" by auto
        hence "lnth (ltake (n' - enat n) (ldrop (enat n) t)) k' = lnth (ldrop (enat n) t) k'"
          using lnth_ltake[of k' "n' - enat n"] by simp
        with \<open>enat (k' + n) < llength t\<close> show ?thesis using lnth_ldrop[of n k' t ]
          using \<open>k = lnth (ltake (n' - enat n) (ldrop (enat n) t)) k'\<close> by (simp add: add.commute)
      qed
      moreover from \<open>enat n \<le> (n'::enat)\<close> have "k' + the_enat n\<ge>n" by auto
      moreover from \<open>enat k' < llength (ltake (n' - enat n) (ldrop (enat n) t))\<close> have "k' + n<n'"
        using assms(1) enat_min by auto
      ultimately show "\<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>" using \<open>\<nexists>k. k\<ge>n \<and> k<n' \<and> k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>\<close> by simp
    qed
    hence "\<forall>k\<in>lset (ltake (n'-n) (ldrop n t)). \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>"
      using lset_conv_lnth[of "(ltake (n' - enat n) (ldrop (enat n) t))"] by simp
    thus ?thesis using proj_lnull by auto
  qed
  moreover from assms have "n + (n' - n) = n'"
    by (meson enat.distinct(1) enat_add_sub_same enat_diff_cancel_left enat_le_plus_same(1) less_imp_le)
  ultimately show ?thesis by simp
qed
  
subsubsection "Projection Active"

lemma proj_active[simp]:
  assumes "enat i < llength t" "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
  shows "\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t) = (\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l)" (is "?lhs = ?rhs")
proof -
  from assms have "ltake (enat (Suc i)) t = (ltake (enat i) t) @\<^sub>l ((lnth t i) #\<^sub>l []\<^sub>l)"
    using ltake_Suc_conv_snoc_lnth by blast
  hence "?lhs = \<pi>\<^bsub>c\<^esub>((ltake (enat i) t) @\<^sub>l ((lnth t i) #\<^sub>l []\<^sub>l))" by simp
  moreover have "\<dots> = (\<pi>\<^bsub>c\<^esub>(ltake (enat i) t)) @\<^sub>l (\<pi>\<^bsub>c\<^esub>((lnth t i) #\<^sub>l []\<^sub>l))" by simp
  moreover from assms have "\<pi>\<^bsub>c\<^esub>((lnth t i) #\<^sub>l []\<^sub>l) = (\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l" by simp
  ultimately show ?thesis by simp
qed
  
lemma proj_active_append:
  assumes a1: "(n::nat) \<le> i"
      and a2: "enat i < (n'::enat)"
      and a3: "\<not> lfinite t \<or> n'-1 < llength t"
      and a4: "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
      and "\<forall>i'. (n \<le> i' \<and> enat i'<n' \<and> i' < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i'\<^esub>) \<longrightarrow> (i' = i)"
    shows "\<pi>\<^bsub>c\<^esub>(ltake n' t) = (\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l)" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<pi>\<^bsub>c\<^esub>(ltake (Suc i) t)"
  proof -
    from a2 have "Suc i \<le> n'" by (simp add: Suc_ile_eq)
    moreover from a3 have "\<not> lfinite t \<or> n'-1 < llength t" by simp
    moreover have "\<nexists>k. enat k\<ge>enat (Suc i) \<and> k<n' \<and> k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
    proof
      assume "\<exists>k. enat k\<ge>enat (Suc i) \<and> k<n' \<and> k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
      then obtain k where "enat k\<ge>enat (Suc i)" and "k<n'" and "k < llength t" and "\<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>" by blast
      moreover from \<open>enat k\<ge>enat (Suc i)\<close> have "enat k\<ge>n"
        using assms by (meson dual_order.trans enat_ord_simps(1) le_SucI)
      ultimately have "enat k=enat i" using assms using enat_ord_simps(1) by blast
      with \<open>enat k\<ge>enat (Suc i)\<close> show False by simp
    qed
    ultimately show ?thesis using proj_not_active_same[of "Suc i" n' t c] by simp
  qed
  also have "\<dots> = (\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l)"
  proof -
    have "i < llength t"
    proof cases
      assume "lfinite t"
      with a3 have "n'-1 < llength t" by simp
      hence "n' \<le> llength t" by (metis eSuc_minus_1 enat_minus_mono1 ileI1 not_le)
      with a2 show "enat i < llength t" by simp
    next
      assume "\<not> lfinite t"
      thus ?thesis by (metis enat_ord_code(4) llength_eq_infty_conv_lfinite)
    qed
    with a4 show ?thesis by simp
  qed
  also have "\<dots> = ?rhs"
  proof -
    from a1 have "enat n \<le> enat i" by simp
    moreover from a2 a3 have "\<not> lfinite t \<or> enat i-1 < llength t"
      using enat_minus_mono1 less_imp_le order.strict_trans1 by blast
    moreover have "\<nexists>k. k\<ge>n \<and> enat k<enat i \<and> enat k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
    proof
      assume "\<exists>k. k\<ge>n \<and> enat k<enat i \<and> enat k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
      then obtain k where "k\<ge>n" and "enat k<enat i" and "enat k < llength t" and "\<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>" by blast
      moreover from \<open>enat k<enat i\<close> have "enat k<n'" using assms dual_order.strict_trans by blast
      ultimately have "enat k=enat i" using assms by simp
      with \<open>enat k<enat i\<close> show False by simp
    qed
    ultimately show ?thesis using proj_not_active_same[of n i t c] by simp
  qed    
  finally show ?thesis by simp
qed
  
subsubsection "Same and not Same"

lemma proj_same_not_active:
  assumes "n \<le> n'"
    and "enat (n'-1) < llength t"
    and "\<pi>\<^bsub>c\<^esub>(ltake n' t) = \<pi>\<^bsub>c\<^esub>(ltake n t)"
  shows "\<nexists>k. k\<ge>n \<and> k<n' \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
proof
  assume "\<exists>k. k\<ge>n \<and> k<n' \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
  then obtain i where "i\<ge>n" and "i<n'" and "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>" by blast
  moreover from \<open>enat (n'-1)<llength t\<close> and \<open>i<n'\<close> have "i<llength t"
    by (metis diff_Suc_1 dual_order.strict_trans enat_ord_simps(2) lessE)
  ultimately have "\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t) =
    (\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l)" by simp
  moreover from \<open>i<n'\<close> have "Suc i \<le> n'" by simp
    hence "lprefix(\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t)) (\<pi>\<^bsub>c\<^esub>(ltake n' t))" by simp
    then obtain "tl" where "\<pi>\<^bsub>c\<^esub>(ltake n' t) = (\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t)) @\<^sub>l tl"
      using lprefix_conv_lappend by auto
  moreover from \<open>n\<le>i\<close> have "lprefix(\<pi>\<^bsub>c\<^esub>(ltake n t)) (\<pi>\<^bsub>c\<^esub>(ltake i t))" by simp
    hence "lprefix(\<pi>\<^bsub>c\<^esub>(ltake n t)) (\<pi>\<^bsub>c\<^esub>(ltake i t))" by simp
    then obtain "hd" where "\<pi>\<^bsub>c\<^esub>(ltake i t) = (\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l hd"
      using lprefix_conv_lappend by auto
  ultimately have "\<pi>\<^bsub>c\<^esub>(ltake n' t) =
    (((\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l hd) @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l)) @\<^sub>l tl" by simp
  also have "\<dots> = ((\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l hd) @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l tl)"
    using lappend_snocL1_conv_LCons2[of "(\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l hd" "\<sigma>\<^bsub>c\<^esub>(lnth t i)"] by simp
  also have "\<dots> = (\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l (hd @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l tl))"
    using lappend_assoc by auto
  also have "\<pi>\<^bsub>c\<^esub>(ltake n' t) = (\<pi>\<^bsub>c\<^esub>(ltake n' t)) @\<^sub>l []\<^sub>l" by simp
  finally have "(\<pi>\<^bsub>c\<^esub>(ltake n' t)) @\<^sub>l []\<^sub>l = (\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l (hd @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l tl))" .
  moreover from assms(3) have "llength (\<pi>\<^bsub>c\<^esub>(ltake n' t)) = llength (\<pi>\<^bsub>c\<^esub>(ltake n t))" by simp
  ultimately have "lfinite (\<pi>\<^bsub>c\<^esub>(ltake n' t)) \<longrightarrow> []\<^sub>l = hd @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l tl)"
    using assms(3) lappend_eq_lappend_conv[of "\<pi>\<^bsub>c\<^esub>(ltake n' t)" "\<pi>\<^bsub>c\<^esub>(ltake n t)" "[]\<^sub>l"] by simp
  moreover have "lfinite (\<pi>\<^bsub>c\<^esub>(ltake n' t))" by simp
  ultimately have "[]\<^sub>l = hd @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l tl)" by simp
  hence "(\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l tl = []\<^sub>l" using LNil_eq_lappend_iff by auto
  thus False by simp
qed

lemma proj_not_same_active:
  assumes "enat n \<le> (n'::enat)"
    and "(\<not> lfinite t) \<or> n'-1 < llength t"
    and "\<not>(\<pi>\<^bsub>c\<^esub>(ltake n' t) = \<pi>\<^bsub>c\<^esub>(ltake n t))"
  shows "\<exists>k. k\<ge>n \<and> k<n' \<and> enat k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
proof (rule ccontr)
  assume "\<not>(\<exists>k. k\<ge>n \<and> k<n' \<and> enat k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>)"
  have "\<pi>\<^bsub>c\<^esub>(ltake n' t) = \<pi>\<^bsub>c\<^esub>(ltake (enat n) t)"
  proof cases
    assume "lfinite t"
    hence "llength t\<noteq>\<infinity>" by (simp add: lfinite_llength_enat) 
    hence "enat (the_enat (llength t)) = llength t" by auto
    with assms \<open>\<not> (\<exists>k\<ge>n. k < n' \<and> enat k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>)\<close>
      show ?thesis using proj_not_active_same[of n n' t c] by simp
  next
    assume "\<not> lfinite t"
    with assms \<open>\<not> (\<exists>k\<ge>n. k < n' \<and> enat k < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>)\<close>
      show ?thesis using proj_not_active_same[of n n' t c] by simp
  qed
  with assms show False by simp
qed

subsection "Activations"
text \<open>
  We also introduce an operator to obtain the number of activations of a certain component within a given configuration trace.
\<close>

definition nAct :: "'id \<Rightarrow> enat \<Rightarrow> (cnf llist) \<Rightarrow> enat" ("\<langle>_ #\<^bsub>_\<^esub>_\<rangle>") where
"\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<equiv> llength (\<pi>\<^bsub>c\<^esub>(ltake n t))"

lemma nAct_0[simp]:
  "\<langle>c #\<^bsub>0\<^esub> t\<rangle> = 0" by (simp add: nAct_def)

lemma nAct_NIL[simp]:
  "\<langle>c #\<^bsub>n\<^esub> []\<^sub>l\<rangle> = 0" by (simp add: nAct_def)    

lemma nAct_Null:
  assumes "llength t \<ge> n"
      and "\<langle>c #\<^bsub>n\<^esub> t\<rangle> = 0"
    shows "\<forall>i<n. \<not> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
proof -
  from assms have "lnull (\<pi>\<^bsub>c\<^esub>(ltake n t))" using nAct_def lnull_def by simp
  hence "\<pi>\<^bsub>c\<^esub>(ltake n t) = []\<^sub>l" using lnull_def by blast
  hence "(\<forall>k\<in>lset (ltake n t). \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>)" by simp
  show ?thesis
  proof (rule ccontr)
    assume "\<not> (\<forall>i<n. \<not> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>)"
    then obtain i where "i<n" and "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>" by blast
    moreover have "enat i < llength (ltake n t)  \<and> lnth (ltake n t) i = (lnth t i)"
    proof
      from \<open>llength t \<ge> n\<close> have "n = min n (llength t)" using min.orderE by auto
      hence "llength (ltake n t) = n" by simp
      with \<open>i<n\<close> show "enat i < llength (ltake n t)" by auto
      from \<open>i<n\<close> show "lnth (ltake n t) i = (lnth t i)" using lnth_ltake by auto
    qed
    hence "(lnth t i \<in> lset (ltake n t))" using in_lset_conv_lnth[of "lnth t i" "ltake n t"] by blast
    ultimately show False using \<open>(\<forall>k\<in>lset (ltake n t). \<not> \<parallel>c\<parallel>\<^bsub>k\<^esub>)\<close> by simp
  qed
qed

lemma nAct_ge_one[simp]:
  assumes "llength t \<ge> n"
      and "i < n"
      and "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
    shows "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<ge> enat 1"
proof (rule ccontr)
  assume "\<not> (\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<ge> enat 1)"
  hence "\<langle>c #\<^bsub>n\<^esub> t\<rangle> < enat 1" by simp
  hence "\<langle>c #\<^bsub>n\<^esub> t\<rangle> < 1" using enat_1 by simp
  hence "\<langle>c #\<^bsub>n\<^esub> t\<rangle> = 0" using Suc_ile_eq \<open>\<not> enat 1 \<le> \<langle>c #\<^bsub>n\<^esub> t\<rangle>\<close> zero_enat_def by auto
  with \<open>llength t \<ge> n\<close> have "\<forall>i<n. \<not> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>" using nAct_Null by simp
  with assms show False by simp
qed
    
lemma nAct_finite[simp]:
  assumes "n \<noteq> \<infinity>"
  shows "\<exists>n'. \<langle>c #\<^bsub>n\<^esub> t\<rangle> = enat n'"
proof -
  from assms have "lfinite (ltake n t)" by simp
  hence "lfinite (\<pi>\<^bsub>c\<^esub>(ltake n t))" by simp
  hence "\<exists>n'. llength (\<pi>\<^bsub>c\<^esub>(ltake n t)) = enat n'" using lfinite_llength_enat[of "\<pi>\<^bsub>c\<^esub>(ltake n t)"] by simp
  thus ?thesis using nAct_def by simp
qed

lemma nAct_enat_the_nat[simp]:
  assumes "n \<noteq> \<infinity>"
  shows "enat (the_enat (\<langle>c #\<^bsub>n\<^esub> t\<rangle>)) = \<langle>c #\<^bsub>n\<^esub> t\<rangle>"
proof -
  from assms have "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<noteq> \<infinity>" by simp
  thus ?thesis using enat_the_enat by simp
qed
  
subsubsection "Monotonicity and Continuity"
  
lemma nAct_mcont:
  shows "mcont lSup lprefix Sup (\<le>) (nAct c n)"
proof -
  have "mcont lSup lprefix lSup lprefix (ltake n)" by simp
  hence "mcont lSup lprefix lSup lprefix (\<lambda>t. \<pi>\<^bsub>c\<^esub>(ltake n t))"
    using proj_mcont2mcont[of lSup lprefix "(ltake n)"] by simp
  hence "mcont lSup lprefix Sup (\<le>) (\<lambda>t. llength (\<pi>\<^bsub>c\<^esub>(ltake n t)))" by simp
  moreover have "nAct c n = (\<lambda>t. llength (\<pi>\<^bsub>c\<^esub>(ltake n t)))" using nAct_def by auto
  ultimately show ?thesis by simp
qed
  
lemma nAct_mono:
  assumes "n \<le> n'"
    shows "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<le> \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
proof -
  from assms have "lprefix (ltake n t) (ltake n' t)" by simp
  hence "lprefix (\<pi>\<^bsub>c\<^esub>(ltake n t)) (\<pi>\<^bsub>c\<^esub>(ltake n' t))" by simp
  hence "llength (\<pi>\<^bsub>c\<^esub>(ltake n t)) \<le> llength (\<pi>\<^bsub>c\<^esub>(ltake n' t))"
    using lprefix_llength_le[of "(\<pi>\<^bsub>c\<^esub>(ltake n t))"] by simp
  thus ?thesis using nAct_def by simp
qed
  
lemma nAct_strict_mono_back:
  assumes "\<langle>c #\<^bsub>n\<^esub> t\<rangle> < \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
    shows "n < n'"
proof (rule ccontr)
  assume "\<not> n<n'"
  hence "n\<ge>n'" by simp
  hence "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<ge> \<langle>c #\<^bsub>n'\<^esub> t\<rangle>" using nAct_mono by simp
  thus False using assms by simp
qed

subsubsection "Not Active"

lemma nAct_not_active[simp]:
  fixes n::nat
    and n'::nat
    and t::"(cnf llist)"
    and c::'id
  assumes "enat i < llength t"
    and "\<not> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
  shows "\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle> = \<langle>c #\<^bsub>i\<^esub> t\<rangle>"
proof -
  from assms have "\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t) = \<pi>\<^bsub>c\<^esub>(ltake i t)" by simp
  hence "llength (\<pi>\<^bsub>c\<^esub>(ltake (enat (Suc i)) t)) = llength (\<pi>\<^bsub>c\<^esub>(ltake i t))" by simp
  moreover have "llength (\<pi>\<^bsub>c\<^esub>(ltake i t)) \<noteq> \<infinity>"
    using llength_eq_infty_conv_lfinite[of "\<pi>\<^bsub>c\<^esub>(ltake (enat i) t)"] by simp
  ultimately have "llength (\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t)) = llength (\<pi>\<^bsub>c\<^esub>(ltake i t))"
    using the_enat_eSuc by simp
  with nAct_def show ?thesis by simp
qed
  
lemma nAct_not_active_same:
  assumes "enat n \<le> (n'::enat)"
      and "n'-1 < llength t"
      and "\<nexists>k. enat k\<ge>n \<and> k<n' \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
    shows "\<langle>c #\<^bsub>n'\<^esub> t\<rangle> = \<langle>c #\<^bsub>n\<^esub> t\<rangle>"
  using assms proj_not_active_same nAct_def by simp
    
subsubsection "Active"
  
lemma nAct_active[simp]:
  fixes n::nat
    and n'::nat
    and t::"(cnf llist)"
    and c::'id
  assumes "enat i < llength t"
    and "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
  shows "\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle> = eSuc (\<langle>c #\<^bsub>i\<^esub> t\<rangle>)"
proof -
  from assms have "\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t) =
    (\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l)" by simp
  hence "llength (\<pi>\<^bsub>c\<^esub>(ltake (enat (Suc i)) t)) = eSuc (llength (\<pi>\<^bsub>c\<^esub>(ltake i t)))"
    using plus_1_eSuc one_eSuc by simp
  moreover have "llength (\<pi>\<^bsub>c\<^esub>(ltake i t)) \<noteq> \<infinity>"
    using llength_eq_infty_conv_lfinite[of "\<pi>\<^bsub>c\<^esub>(ltake (enat i) t)"] by simp
  ultimately have "llength (\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t)) = eSuc (llength (\<pi>\<^bsub>c\<^esub>(ltake i t)))"
    using the_enat_eSuc by simp
  with nAct_def show ?thesis by simp
qed

lemma nAct_active_suc:
  fixes n::nat
    and n'::enat
    and t::"(cnf llist)"
    and c::'id
  assumes "\<not> lfinite t \<or> n'-1 < llength t"
    and "n \<le> i"
    and "enat i < n'"
    and "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
    and "\<forall>i'. (n \<le> i' \<and> enat i'<n' \<and> i' < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i'\<^esub>) \<longrightarrow> (i' = i)"
  shows "\<langle>c #\<^bsub>n'\<^esub> t\<rangle> = eSuc (\<langle>c #\<^bsub>n\<^esub> t\<rangle>)"
proof -
  from assms have "\<pi>\<^bsub>c\<^esub>(ltake n' t) = (\<pi>\<^bsub>c\<^esub>(ltake (enat n) t)) @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l)"
    using proj_active_append[of n i n' t c] by blast
  moreover have "llength ((\<pi>\<^bsub>c\<^esub>(ltake (enat n) t)) @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l)) =
    eSuc (llength (\<pi>\<^bsub>c\<^esub>(ltake (enat n) t)))" using one_eSuc eSuc_plus_1 by simp
  ultimately show ?thesis using nAct_def by simp
qed
  
lemma nAct_less:
  assumes "enat k < llength t"
    and "n \<le> k"
    and "k < (n'::enat)"
    and "\<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>"
  shows "\<langle>c #\<^bsub>n\<^esub> t\<rangle> < \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
proof -
  have "\<langle>c #\<^bsub>k\<^esub> t\<rangle> \<noteq> \<infinity>" by simp
  then obtain en where en_def: "\<langle>c #\<^bsub>k\<^esub> t\<rangle> = enat en" by blast  
  moreover have "eSuc (enat en) \<le> \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
  proof -
    from assms have "Suc k \<le> n'" using Suc_ile_eq by simp
    hence "\<langle>c #\<^bsub>Suc k\<^esub> t\<rangle> \<le> \<langle>c #\<^bsub>n'\<^esub> t\<rangle>" using nAct_mono by simp
    moreover from assms have "\<langle>c #\<^bsub>Suc k\<^esub> t\<rangle> = eSuc (\<langle>c #\<^bsub>k\<^esub> t\<rangle>)" by simp
    ultimately have "eSuc (\<langle>c #\<^bsub>k\<^esub> t\<rangle>) \<le> \<langle>c #\<^bsub>n'\<^esub> t\<rangle>" by simp
    thus ?thesis using en_def by simp
  qed
  moreover have "enat en < eSuc (enat en)" by simp
  ultimately have "enat en < \<langle>c #\<^bsub>n'\<^esub> t\<rangle>" using less_le_trans[of "enat en" "eSuc (enat en)"] by simp
  moreover have "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<le> enat en"
  proof -
    from assms have "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<le> \<langle>c #\<^bsub>k\<^esub> t\<rangle>" using nAct_mono by simp
    thus ?thesis using en_def by simp
  qed
  ultimately show ?thesis using le_less_trans[of "\<langle>c #\<^bsub>n\<^esub> t\<rangle>"] by simp
qed
  
lemma nAct_less_active:
  assumes "n' - 1 < llength t"
      and "\<langle>c #\<^bsub>enat n\<^esub> t\<rangle> < \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
  shows "\<exists>i\<ge>n. i<n' \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
proof (rule ccontr)
  assume "\<not> (\<exists>i\<ge>n. i<n' \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>)"
  moreover have "enat n \<le> n'" using assms(2) less_imp_le nAct_strict_mono_back by blast
  ultimately have "\<langle>c #\<^bsub>n\<^esub> t\<rangle> = \<langle>c #\<^bsub>n'\<^esub> t\<rangle>" using \<open>n' - 1 < llength t\<close> nAct_not_active_same by simp
  thus False using assms by simp
qed

subsubsection "Same and Not Same"
  
lemma nAct_same_not_active:
  assumes "\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>"
  shows "\<forall>k\<ge>n. k<n' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
proof (rule ccontr)
  assume "\<not>(\<forall>k\<ge>n. k<n' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
  then obtain k where "k\<ge>n" and "k<n'" and "\<parallel>c\<parallel>\<^bsub>t k\<^esub>" by blast
  hence "\<langle>c #\<^bsub>Suc k\<^esub> inf_llist t\<rangle> = eSuc (\<langle>c #\<^bsub>k\<^esub> inf_llist t\<rangle>)" by simp
  moreover have "\<langle>c #\<^bsub>k\<^esub> inf_llist t\<rangle>\<noteq>\<infinity>" by simp
  ultimately have "\<langle>c #\<^bsub>k\<^esub> inf_llist t\<rangle> < \<langle>c #\<^bsub>Suc k\<^esub> inf_llist t\<rangle>" by fastforce
  moreover from \<open>n\<le>k\<close> have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>k\<^esub> inf_llist t\<rangle>" using nAct_mono by simp
  moreover from \<open>k<n'\<close> have "Suc k \<le> n'" by (simp add: Suc_ile_eq)
  hence "\<langle>c #\<^bsub>Suc k\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" using nAct_mono by simp
  ultimately show False using assms by simp
qed
  
lemma nAct_not_same_active:
  assumes "\<langle>c #\<^bsub>enat n\<^esub> t\<rangle> < \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
    and "\<not> lfinite t \<or> n' - 1 < llength t"
  shows "\<exists>(i::nat)\<ge>n. enat i< n' \<and> i<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
proof -
  from assms have "llength(\<pi>\<^bsub>c\<^esub>(ltake n t)) < llength (\<pi>\<^bsub>c\<^esub>(ltake n' t))" using nAct_def by simp
  hence "\<pi>\<^bsub>c\<^esub>(ltake n' t) \<noteq> \<pi>\<^bsub>c\<^esub>(ltake n t)" by auto
  moreover from assms have "enat n < n'" using nAct_strict_mono_back[of c "enat n" t n'] by simp
  ultimately show ?thesis using proj_not_same_active[of n n' t c] assms by simp
qed
  
lemma nAct_less_llength_active:
  assumes "x < llength (\<pi>\<^bsub>c\<^esub>(t))"
    and "enat x = \<langle>c #\<^bsub>enat n'\<^esub> t\<rangle>"
  shows "\<exists>(i::nat)\<ge>n'. i<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
proof -
  have "llength(\<pi>\<^bsub>c\<^esub>(ltake n' t)) < llength (\<pi>\<^bsub>c\<^esub>(t))" using assms(1) assms(2) nAct_def by auto
  hence "llength(\<pi>\<^bsub>c\<^esub>(ltake n' t)) < llength (\<pi>\<^bsub>c\<^esub>(ltake (llength t) t))" by (simp add: ltake_all)
  hence "\<langle>c #\<^bsub>enat n'\<^esub> t\<rangle> < \<langle>c #\<^bsub>llength t\<^esub> t\<rangle>" using nAct_def by simp
  moreover have "\<not> lfinite t \<or> llength t - 1 < llength t"
  proof (rule Meson.imp_to_disjD[OF HOL.impI])
    assume "lfinite t"
    hence "llength t \<noteq> \<infinity>" by (simp add: llength_eq_infty_conv_lfinite)
    moreover have "llength t>0"
    proof -
      from \<open>x < llength (\<pi>\<^bsub>c\<^esub>(t))\<close> have "llength (\<pi>\<^bsub>c\<^esub>(t))>0" by auto
      thus ?thesis using proj_llength Orderings.order_class.order.strict_trans2 by blast
    qed
    ultimately show "llength t - 1 < llength t" by (metis One_nat_def \<open>lfinite t\<close> diff_Suc_less
      enat_ord_simps(2) idiff_enat_enat lfinite_conv_llength_enat one_enat_def zero_enat_def)
  qed
  ultimately show ?thesis using nAct_not_same_active[of c n' t "llength t"] by simp
qed

lemma nAct_exists:
  assumes "x < llength (\<pi>\<^bsub>c\<^esub>(t))"
  shows "\<exists>(n'::nat). enat x = \<langle>c #\<^bsub>n'\<^esub> t\<rangle>"
proof -
  have "x < llength (\<pi>\<^bsub>c\<^esub>(t)) \<longrightarrow> (\<exists>(n'::nat). enat x = \<langle>c #\<^bsub>n'\<^esub> t\<rangle>)"
  proof (induction x)
    case 0
    thus ?case by (metis nAct_0 zero_enat_def)
  next
    case (Suc x)
    show ?case
    proof
      assume "Suc x < llength (\<pi>\<^bsub>c\<^esub>(t))"
      hence "x < llength (\<pi>\<^bsub>c\<^esub>(t))" using Suc_ile_eq less_imp_le by auto
      with Suc.IH obtain n' where "enat x = \<langle>c #\<^bsub>enat n'\<^esub> t\<rangle>" by blast
      with \<open>x < llength (\<pi>\<^bsub>c\<^esub>(t))\<close> have "\<exists>i\<ge>n'. i < llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
        using nAct_less_llength_active[of x c t n'] by simp
      then obtain i where "i\<ge>n'" and "i<llength t" and "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
        and "\<nexists>k. n'\<le>k \<and> k<i \<and> k<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>" using lActive_least[of n' t c] by auto
      moreover from \<open>i<llength t\<close> have "\<not> lfinite t \<or> enat (Suc i) - 1 < llength t"
        by (simp add: one_enat_def)
      moreover have "enat i < enat (Suc i)" by simp
      moreover have "\<forall>i'. (n' \<le> i' \<and> enat i'<enat (Suc i) \<and> i'<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i'\<^esub>) \<longrightarrow> (i' = i)"
      proof (rule HOL.impI[THEN HOL.allI])
        fix i' assume "n' \<le> i' \<and> enat i'<enat (Suc i) \<and> i'<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t i'\<^esub>"
        with \<open>\<nexists>k. n'\<le>k \<and> k<i \<and> k<llength t \<and> \<parallel>c\<parallel>\<^bsub>lnth t k\<^esub>\<close> show "i'=i" by fastforce
      qed
      ultimately have "\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle> = eSuc (\<langle>c #\<^bsub>n'\<^esub> t\<rangle>)" using nAct_active_suc[of t "Suc i" n' i c] by simp
      with \<open>enat x = \<langle>c #\<^bsub>enat n'\<^esub> t\<rangle>\<close> have "\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle> = eSuc (enat x)" by simp
      thus "\<exists>n'. enat (Suc x) = \<langle>c #\<^bsub>enat n'\<^esub> t\<rangle>" by (metis eSuc_enat)
    qed
  qed
  with assms show ?thesis by simp
qed
  
subsection "Projection and Activation"
text \<open>
  In the following we provide some properties about the relationship between the projection and activations operator.
\<close>
  
lemma nAct_le_proj:
  "\<langle>c #\<^bsub>n\<^esub> t\<rangle> \<le> llength (\<pi>\<^bsub>c\<^esub>(t))"
proof -
  from nAct_def have "\<langle>c #\<^bsub>n\<^esub> t\<rangle> = llength (\<pi>\<^bsub>c\<^esub>(ltake n t))" by simp
  moreover have "llength (\<pi>\<^bsub>c\<^esub>(ltake n t)) \<le> llength (\<pi>\<^bsub>c\<^esub>(t))"
  proof -
    have "lprefix (ltake n t) t" by simp
    hence "lprefix (\<pi>\<^bsub>c\<^esub>(ltake n t)) (\<pi>\<^bsub>c\<^esub>(t))" by simp
    hence "llength (\<pi>\<^bsub>c\<^esub>(ltake n t)) \<le> llength (\<pi>\<^bsub>c\<^esub>(t))" using lprefix_llength_le by blast
    thus ?thesis by auto
  qed
  thus ?thesis using nAct_def by simp
qed
  
lemma proj_nAct:
  assumes "(enat n < llength t)"
  shows "\<pi>\<^bsub>c\<^esub>(ltake n t) = ltake (\<langle>c #\<^bsub>n\<^esub> t\<rangle>) (\<pi>\<^bsub>c\<^esub>(t))" (is "?lhs = ?rhs")
proof -
  have "?lhs = ltake (llength (\<pi>\<^bsub>c\<^esub>(ltake n t))) (\<pi>\<^bsub>c\<^esub>(ltake n t))"
    using ltake_all[of "\<pi>\<^bsub>c\<^esub>(ltake n t)" "llength (\<pi>\<^bsub>c\<^esub>(ltake n t))"] by simp
  also have "\<dots> = ltake (llength (\<pi>\<^bsub>c\<^esub>(ltake n t))) ((\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l (\<pi>\<^bsub>c\<^esub>(ldrop n t)))"
    using ltake_lappend1[of "llength (\<pi>\<^bsub>c\<^esub>(ltake (enat n) t))" "\<pi>\<^bsub>c\<^esub>(ltake n t)" "(\<pi>\<^bsub>c\<^esub>(ldrop n t))"] by simp
  also have "\<dots> = ltake (\<langle>c #\<^bsub>n\<^esub> t\<rangle>) ((\<pi>\<^bsub>c\<^esub>(ltake n t)) @\<^sub>l (\<pi>\<^bsub>c\<^esub>(ldrop n t)))" using nAct_def by simp      
  also have "\<dots> = ltake (\<langle>c #\<^bsub>n\<^esub> t\<rangle>) (\<pi>\<^bsub>c\<^esub>((ltake (enat n) t) @\<^sub>l (ldrop n t)))" by simp
  also have "\<dots> = ltake (\<langle>c #\<^bsub>n\<^esub> t\<rangle>) (\<pi>\<^bsub>c\<^esub>(t))" using lappend_ltake_ldrop[of n t] by simp
  finally show ?thesis by simp
qed

lemma proj_active_nth:
  assumes "enat (Suc i) < llength t" "\<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>"
  shows "lnth (\<pi>\<^bsub>c\<^esub>(t)) (the_enat (\<langle>c #\<^bsub>i\<^esub> t\<rangle>)) = \<sigma>\<^bsub>c\<^esub>(lnth t i)"
proof -
  from assms have "enat i < llength t" using Suc_ile_eq[of i "llength t"] by auto
  with assms have "\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t) = (\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l)" by simp
  moreover have "lnth ((\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l))
    (the_enat (llength (\<pi>\<^bsub>c\<^esub>(ltake i t)))) = \<sigma>\<^bsub>c\<^esub>(lnth t i)"
  proof -
    have "\<not> lnull ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l)" by simp
    moreover have "lfinite (\<pi>\<^bsub>c\<^esub>(ltake i t))" by simp
    ultimately have "lnth ((\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l))
      (the_enat (llength (\<pi>\<^bsub>c\<^esub>(ltake i t)))) = lhd ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l)" by simp
    also have "\<dots> = \<sigma>\<^bsub>c\<^esub>(lnth t i)" by simp
    finally show "lnth ((\<pi>\<^bsub>c\<^esub>(ltake i t)) @\<^sub>l ((\<sigma>\<^bsub>c\<^esub>(lnth t i)) #\<^sub>l []\<^sub>l))
      (the_enat (llength (\<pi>\<^bsub>c\<^esub>(ltake i t)))) = \<sigma>\<^bsub>c\<^esub>(lnth t i)" by simp
  qed
  ultimately have "\<sigma>\<^bsub>c\<^esub>(lnth t i) = lnth (\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t))
    (the_enat (llength (\<pi>\<^bsub>c\<^esub>(ltake i t))))" by simp
  also have "\<dots> = lnth (\<pi>\<^bsub>c\<^esub>(ltake (Suc i) t)) (the_enat (\<langle>c #\<^bsub>i\<^esub> t\<rangle>))" using nAct_def by simp
  also have "\<dots> = lnth (ltake (\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle>) (\<pi>\<^bsub>c\<^esub>(t))) (the_enat (\<langle>c #\<^bsub>i\<^esub> t\<rangle>))"
    using proj_nAct[of "Suc i" t c] assms by simp
  also have "\<dots> = lnth (\<pi>\<^bsub>c\<^esub>(t)) (the_enat (\<langle>c #\<^bsub>i\<^esub> t\<rangle>))"
  proof -
    from assms have "\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle> = eSuc (\<langle>c #\<^bsub>i\<^esub> t\<rangle>)" using \<open>enat i < llength t\<close> by simp
    moreover have "\<langle>c #\<^bsub>i\<^esub> t\<rangle> < eSuc (\<langle>c #\<^bsub>i\<^esub> t\<rangle>)" using iless_Suc_eq[of "the_enat (\<langle>c #\<^bsub>enat i\<^esub> t\<rangle>)"] by simp
    ultimately have "\<langle>c #\<^bsub>i\<^esub> t\<rangle> < (\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle>)" by simp
    hence "enat (the_enat (\<langle>c #\<^bsub>Suc i\<^esub> t\<rangle>)) > enat (the_enat (\<langle>c #\<^bsub>i\<^esub> t\<rangle>))" by simp
    thus ?thesis using lnth_ltake[of "the_enat (\<langle>c #\<^bsub>i\<^esub> t\<rangle>)" "the_enat (\<langle>c #\<^bsub>enat (Suc i)\<^esub> t\<rangle>)" "\<pi>\<^bsub>c\<^esub>(t)"] by simp
  qed
  finally show ?thesis ..
qed

lemma nAct_eq_proj:
  assumes "\<not>(\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>lnth t i\<^esub>)"
  shows "\<langle>c #\<^bsub>n\<^esub> t\<rangle> = llength (\<pi>\<^bsub>c\<^esub>(t))" (is "?lhs = ?rhs")
proof -
  from nAct_def have "?lhs = llength (\<pi>\<^bsub>c\<^esub>(ltake n t))" by simp
  moreover from assms have "\<forall>(n'::nat)\<le>llength t. n'\<ge>n \<longrightarrow> (\<not> \<parallel>c\<parallel>\<^bsub>lnth t n'\<^esub>)" by simp
  hence "\<pi>\<^bsub>c\<^esub>(t) = \<pi>\<^bsub>c\<^esub>(ltake n t)" using proj_ltake by simp
  ultimately show ?thesis by simp
qed

lemma nAct_llength_proj:
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  shows "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) \<ge> eSuc (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
proof -
  from \<open>\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> obtain i where "i\<ge>n" and "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<not> (\<exists>k\<ge>n. k < i \<and> k < llength (inf_llist t) \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
    using lActive_least[of n "inf_llist t" c] by auto
  moreover have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) \<ge> \<langle>c #\<^bsub>Suc i\<^esub> inf_llist t\<rangle>" using nAct_le_proj by simp
  moreover have "eSuc (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>) = \<langle>c #\<^bsub>Suc i\<^esub> inf_llist t\<rangle>"
  proof -
    have "enat (Suc i) < llength (inf_llist t)" by simp
    moreover have "i < Suc i" by simp
    moreover from \<open>\<not> (\<exists>k\<ge>n. k < i \<and> k < llength (inf_llist t) \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)\<close>
      have "\<forall>i'. n \<le> i' \<and> i' < Suc i \<and> \<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) i'\<^esub> \<longrightarrow> i' = i" by fastforce
    ultimately show ?thesis using nAct_active_suc \<open>i\<ge>n\<close> \<open>\<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> by simp
  qed
  ultimately show ?thesis by simp
qed
  
subsection "Least not Active"
text \<open>
  In the following, we introduce an operator to obtain the least point in time before a certain point in time where a component was deactivated.
\<close>

definition lNAct :: "'id \<Rightarrow> (nat \<Rightarrow> cnf) \<Rightarrow> nat \<Rightarrow> nat" ("\<langle>_ \<Leftarrow> _\<rangle>\<^bsub>_\<^esub>")
  where "\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<equiv> (LEAST n'. n=n' \<or> (n'<n \<and> (\<nexists>k. k\<ge>n' \<and> k<n \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)))"

lemma lNact0[simp]:
  "\<langle>c \<Leftarrow> t\<rangle>\<^bsub>0\<^esub> = 0"
  by (simp add: lNAct_def)
    
lemma lNact_least:
  assumes "n=n' \<or> n'<n \<and> (\<nexists>k. k\<ge>n' \<and> k<n \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
  shows "\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n'"
using Least_le[of "\<lambda>n'. n=n' \<or> (n'<n \<and> (\<nexists>k. k\<ge>n' \<and> k<n \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>))" n'] lNAct_def using assms by auto
    
lemma lNAct_ex: "\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>=n \<or> \<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub><n \<and> (\<nexists>k. k\<ge>\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> k<n \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
proof -
  let ?P="\<lambda>n'. n=n' \<or> n'<n \<and> (\<nexists>k. k\<ge>n' \<and> k<n \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
  from lNAct_def have "\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> = (LEAST n'. ?P n')" by simp
  moreover have "?P n" by simp
  with LeastI have "?P (LEAST n'. ?P n')" .
  ultimately show ?thesis by auto
qed
    
lemma lNact_notActive:
  fixes c t n k
  assumes "k\<ge>\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
    and "k<n"
  shows "\<not>\<parallel>c\<parallel>\<^bsub>t k\<^esub>"
  by (metis assms lNAct_ex leD)
    
lemma lNactGe:
  fixes c t n n'
  assumes "n' \<ge> \<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>" 
    and "\<parallel>c\<parallel>\<^bsub>t n'\<^esub>"
  shows "n' \<ge> n"
  using assms lNact_notActive leI by blast

lemma lNactLe[simp]:
  fixes n n'
  shows "\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n"
  using lNAct_ex less_or_eq_imp_le by blast
    
lemma lNactLe_nact:
  fixes n n'
  assumes "n'=n \<or> (n'<n \<and> (\<nexists>k. k\<ge>n' \<and> k<n \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>))"
  shows "\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n'"
  using assms lNAct_def Least_le[of "\<lambda>n'. n=n' \<or> (n'<n \<and> (\<nexists>k. k\<ge>n' \<and> k<n \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>))"] by auto
    
lemma lNact_active:
  fixes cid t n
  assumes "\<forall>k<n. \<parallel>cid\<parallel>\<^bsub>t k\<^esub>"
  shows "\<langle>cid \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> = n"
  using assms lNAct_ex by blast
    
lemma nAct_mono_back:
  fixes c t and n and n'
  assumes "\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> \<ge> \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>"
  shows "n'\<ge>\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
proof cases
  assume "\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>"
  thus ?thesis
  proof cases
    assume "n'\<ge>n"
    thus ?thesis using lNactLe by (metis HOL.no_atp(11))
  next
    assume "\<not> n'\<ge>n"
    hence "n'<n" by simp
    with \<open>\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>\<close> have "\<nexists>k. k\<ge>n' \<and> k<n \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>"
      by (metis enat_ord_simps(1) enat_ord_simps(2) nAct_same_not_active)
    thus ?thesis using lNactLe_nact by (simp add: \<open>n' < n\<close>)
  qed
next
  assume "\<not>\<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle> = \<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>"
  with assms have "\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle> > \<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>" by simp
  hence "n' > n" using nAct_strict_mono_back[of c "enat n" "inf_llist t" "enat n'"] by simp
  thus ?thesis by (meson dual_order.strict_implies_order lNactLe le_trans)
qed
  
lemma nAct_mono_lNact:
  assumes "\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n'"
  shows "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>"
proof -
  have "\<nexists>k. k\<ge>\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<and> k<n \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>" using lNact_notActive by auto
  moreover have "enat n - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
  moreover from \<open>\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n'\<close> have "enat \<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> enat n" by simp
  ultimately have "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>=\<langle>c #\<^bsub>\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle>" using nAct_not_active_same by simp
  thus ?thesis using nAct_mono assms by simp
qed
 
subsection "Next Active"
text \<open>
  In the following, we introduce an operator to obtain the next point in time when a component is activated.
\<close>
  
definition nxtAct :: "'id \<Rightarrow> (nat \<Rightarrow> cnf) \<Rightarrow> nat \<Rightarrow> nat" ("\<langle>_ \<rightarrow> _\<rangle>\<^bsub>_\<^esub>")
  where "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<equiv> (THE n'. n'\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t n'\<^esub> \<and> (\<nexists>k. k\<ge>n \<and> k<n' \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>))"

lemma nxtActI:
  fixes n::nat
    and t::"nat \<Rightarrow> cnf"
    and c::'id
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  shows "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<ge> n \<and> \<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> \<and> (\<nexists>k. k\<ge>n \<and> k<\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
proof -
  let ?P = "THE n'. n'\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t n'\<^esub> \<and> (\<nexists>k. k\<ge>n \<and> k<n' \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
  from assms obtain i where "i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub> \<and> (\<nexists>k. k\<ge>n \<and> k<i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
    using lActive_least[of n "inf_llist t" c] by auto
  moreover have "(\<And>x. n \<le> x \<and> \<parallel>c\<parallel>\<^bsub>t x\<^esub> \<and> \<not> (\<exists>k\<ge>n. k < x \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>) \<Longrightarrow> x = i)"
  proof -
    fix x assume "n \<le> x \<and> \<parallel>c\<parallel>\<^bsub>t x\<^esub> \<and> \<not> (\<exists>k\<ge>n. k < x \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
    show "x = i"
    proof (rule ccontr)
      assume "\<not> (x = i)"
      thus False using \<open>i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub> \<and> (\<nexists>k. k\<ge>n \<and> k<i \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)\<close>
        \<open>n \<le> x \<and> \<parallel>c\<parallel>\<^bsub>t x\<^esub> \<and> \<not> (\<exists>k\<ge>n. k < x \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)\<close> by fastforce
    qed
  qed
  ultimately have "(?P) \<ge> n \<and> \<parallel>c\<parallel>\<^bsub>t (?P)\<^esub> \<and> (\<nexists>k. k\<ge>n \<and> k<?P \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
    using theI[of "\<lambda>n'. n'\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t n'\<^esub> \<and> (\<nexists>k. k\<ge>n \<and> k<n' \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"] by blast
  thus ?thesis using nxtAct_def[of c t n] by metis
qed
  
lemma nxtActLe:
  fixes n n'
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  shows "n \<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"
  by (simp add: assms nxtActI)

lemma nxtAct_eq:
  assumes "n'\<ge>n"
    and "\<parallel>c\<parallel>\<^bsub>t n'\<^esub>"
    and "\<forall>n''\<ge>n. n''<n' \<longrightarrow> \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>"
  shows "n' = \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"
  by (metis assms(1) assms(2) assms(3) nxtActI linorder_neqE_nat nxtActLe)

lemma nxtAct_active:
  fixes i::nat
    and t::"nat \<Rightarrow> cnf"
    and c::'id
  assumes "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  shows "\<langle>c \<rightarrow> t\<rangle>\<^bsub>i\<^esub> = i" by (metis assms le_eq_less_or_eq nxtActI)
    
lemma nxtActive_no_active:
  assumes "\<exists>!i. i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  shows "\<not> (\<exists>i'\<ge>Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)"
proof
  assume "\<exists>i'\<ge>Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"
  then obtain i' where "i'\<ge>Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" and "\<parallel>c\<parallel>\<^bsub>t i'\<^esub>" by auto
  moreover from assms(1) have "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n" using nxtActI by auto
  ultimately have "i'\<ge>n" and "\<parallel>c\<parallel>\<^bsub>t i'\<^esub>" and "i'\<noteq>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" by auto
  moreover from assms(1) have "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" and "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n" using nxtActI by auto
  ultimately show False using assms(1) by auto
qed
  
lemma nxt_geq_lNact[simp]:
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  shows "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>"
proof -
  from assms have "n \<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" using nxtActLe by simp
  moreover have "\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>\<le>n" by simp
  ultimately show ?thesis by arith
qed
  
lemma active_geq_nxtAct:
  assumes "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)"
  shows "i\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"
proof cases
  assume "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>=\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>"
  show ?thesis
  proof (rule ccontr)
    assume "\<not> i\<ge>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"
    hence "i<\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" by simp
    with \<open>\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>=\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>\<close> have "\<not> (\<exists>k\<ge>i. k < n \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)"
      by (metis enat_ord_simps(1) leD leI nAct_same_not_active)
    moreover have "\<not> (\<exists>k\<ge>n. k <\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)" using nxtActI by blast
    ultimately have "\<not> (\<exists>k\<ge>i. k <\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>)" by auto
    with \<open>i<\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<close> show False using \<open>\<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> by simp
  qed
next
  assume "\<not>\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>=\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>"
  moreover from \<open>the_enat (\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>)\<ge>the_enat (\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>)\<close>
  have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>\<ge>\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>"
    by (metis enat.distinct(2) enat_ord_simps(1) nAct_enat_the_nat)
  ultimately have "\<langle>c #\<^bsub>i\<^esub> inf_llist t\<rangle>>\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>" by simp
  hence "i>n" using nAct_strict_mono_back[of c n "inf_llist t" i] by simp
  with \<open>\<parallel>c\<parallel>\<^bsub>t i\<^esub>\<close> show ?thesis by (meson dual_order.strict_implies_order leI nxtActI)
qed

lemma nAct_same:
  assumes "\<langle>c \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n'" and "n' \<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"
  shows "the_enat (\<langle>c #\<^bsub>enat n'\<^esub> inf_llist t\<rangle>) = the_enat (\<langle>c #\<^bsub>enat n\<^esub> inf_llist t\<rangle>)"
proof cases
  assume "n \<le> n'"
  moreover have "n' - 1 < llength (inf_llist t)" by simp
  moreover have "\<not> (\<exists>i\<ge>n. i <n' \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>)" by (meson assms(2) less_le_trans nxtActI)
  ultimately show ?thesis using nAct_not_active_same by (simp add: one_enat_def)
next
  assume "\<not> n \<le> n'"
  hence "n' < n" by simp
  moreover have "n - 1 < llength (inf_llist t)" by simp
  moreover have "\<not> (\<exists>i\<ge>n'. i < n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>)" by (metis \<open>\<not> n \<le> n'\<close> assms(1) dual_order.trans lNAct_ex)
  ultimately show ?thesis using nAct_not_active_same[of n' n] by (simp add: one_enat_def)
qed
  
lemma nAct_mono_nxtAct:
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n'"
  shows "\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>"
proof -
  from assms have "\<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle> \<le> \<langle>c #\<^bsub>n'\<^esub> inf_llist t\<rangle>" using nAct_mono assms by simp
  moreover have "\<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle>=\<langle>c #\<^bsub>n\<^esub> inf_llist t\<rangle>"
  proof -
    from assms have "\<nexists>k. k\<ge>n \<and> k<\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>c\<parallel>\<^bsub>t k\<^esub>" and "n \<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" using nxtActI by auto
    moreover have "enat \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
    ultimately show ?thesis using nAct_not_active_same[of n "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"] by auto
  qed
  ultimately show ?thesis by simp
qed

subsection "Latest Activation"
text \<open>
  In the following, we introduce an operator to obtain the latest point in time when a component is activated.
\<close>

abbreviation latestAct_cond:: "'id \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where "latestAct_cond c t n n' \<equiv> n'<n \<and> \<parallel>c\<parallel>\<^bsub>t n'\<^esub>"

definition latestAct:: "'id \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> nat" ("\<langle>_ \<leftarrow> _\<rangle>\<^bsub>_\<^esub>")
  where "latestAct c t n = (GREATEST n'. latestAct_cond c t n n')"

lemma latestActEx:
  assumes "\<exists>n'<n. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<exists>n'. latestAct_cond nid t n n' \<and> (\<forall>n''. latestAct_cond nid t n n'' \<longrightarrow> n'' \<le> n')"
proof -
  from assms obtain n' where "latestAct_cond nid t n n'" by auto
  moreover have "\<forall>n''>n. \<not> latestAct_cond nid t n n''" by simp
  ultimately obtain n' where "latestAct_cond nid t n n' \<and> (\<forall>n''. latestAct_cond nid t n n'' \<longrightarrow> n'' \<le> n')"
    using boundedGreatest[of "latestAct_cond nid t n" n'] by blast
  thus ?thesis ..
qed

lemma latestAct_prop:
  assumes "\<exists>n'<n. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<parallel>nid\<parallel>\<^bsub>t (latestAct nid t n)\<^esub>" and "latestAct nid t n<n"
proof -
  from assms latestActEx have "latestAct_cond nid t n (GREATEST x. latestAct_cond nid t n x)"
    using GreatestI_ex_nat[of "latestAct_cond nid t n"] by blast
  thus "\<parallel>nid\<parallel>\<^bsub>t \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" and "latestAct nid t n<n" using latestAct_def by auto
qed

lemma latestAct_less:
  assumes "latestAct_cond nid t n n'"
  shows "n' \<le> \<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"
proof -
  from assms latestActEx have "n' \<le> (GREATEST x. latestAct_cond nid t n x)"
    using Greatest_le_nat[of "latestAct_cond nid t n"] by blast
  thus ?thesis using latestAct_def by auto
qed

lemma latestActNxt:
  assumes "\<exists>n'<n. \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<langle>nid \<rightarrow> t\<rangle>\<^bsub>\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>=\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"
  using assms latestAct_prop(1) nxtAct_active by auto

lemma latestActNxtAct:
  assumes "\<exists>n'\<ge>n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
    and "\<exists>n'<n. \<parallel>tid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<langle>tid \<rightarrow> t\<rangle>\<^bsub>n\<^esub> > \<langle>tid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>"
  by (meson assms latestAct_prop(2) less_le_trans nxtActI zero_le)

lemma latestActless:
  assumes "\<exists>n'\<ge>n\<^sub>s. n'<n \<and> \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>"
  shows "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n\<^sub>s"
  by (meson assms dual_order.trans latestAct_less)

lemma latestActEq:
  fixes nid::'id
  assumes "\<parallel>nid\<parallel>\<^bsub>t n'\<^esub>" and "\<not>(\<exists>n''>n'. n''<n \<and> \<parallel>nid\<parallel>\<^bsub>t n'\<^esub>)" and "n'<n"
  shows "\<langle>nid \<leftarrow> t\<rangle>\<^bsub>n\<^esub> = n'"
  using latestAct_def
proof
  have "(GREATEST n'. latestAct_cond nid t n n') = n'"
  proof (rule Greatest_equality[of "latestAct_cond nid t n" n'])
    from assms(1) assms (3) show "latestAct_cond nid t n n'" by simp
  next
    fix y assume "latestAct_cond nid t n y"
    hence "\<parallel>nid\<parallel>\<^bsub>t y\<^esub>" and "y<n" by auto
    thus "y \<le> n'" using assms(1) assms (2) leI by blast
  qed
  thus "n' = (GREATEST n'. latestAct_cond nid t n n')" by simp
qed
  
subsection "Last Activation"
text \<open>
  In the following we introduce an operator to obtain the latest point in time where a certain component was activated within a certain configuration trace.
\<close>

definition lActive :: "'id \<Rightarrow> (nat \<Rightarrow> cnf) \<Rightarrow> nat" ("\<langle>_ \<and> _\<rangle>")
  where "\<langle>c \<and> t\<rangle> \<equiv> (GREATEST i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"

lemma lActive_active:
  assumes "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<forall>n' > n. \<not> (\<parallel>c\<parallel>\<^bsub>t n'\<^esub>)"
  shows "\<parallel>c\<parallel>\<^bsub>t (\<langle>c \<and> t\<rangle>)\<^esub>"
proof -
  from assms obtain i' where "\<parallel>c\<parallel>\<^bsub>t i'\<^esub>" and "(\<forall>y. \<parallel>c\<parallel>\<^bsub>t y\<^esub> \<longrightarrow> y \<le> i')"
    using boundedGreatest[of "\<lambda>i'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" i n] by blast
  thus ?thesis using lActive_def Nat.GreatestI_nat[of "\<lambda>i'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"] by simp
qed

lemma lActive_less:
  assumes "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<forall>n' > n. \<not> (\<parallel>c\<parallel>\<^bsub>t n'\<^esub>)"
  shows "\<langle>c \<and> t\<rangle> \<le> n"
proof (rule ccontr)
  assume "\<not> \<langle>c \<and> t\<rangle> \<le> n"
  hence "\<langle>c \<and> t\<rangle> > n" by simp
  moreover from assms have "\<parallel>c\<parallel>\<^bsub>t (\<langle>c \<and> t\<rangle>)\<^esub>" using lActive_active by simp
  ultimately show False using assms by simp
qed

lemma lActive_greatest:
  assumes "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<forall>n' > n. \<not> (\<parallel>c\<parallel>\<^bsub>t n'\<^esub>)"
  shows "i \<le> \<langle>c \<and> t\<rangle>"
proof -
  from assms obtain i' where "\<parallel>c\<parallel>\<^bsub>t i'\<^esub>" and "(\<forall>y. \<parallel>c\<parallel>\<^bsub>t y\<^esub> \<longrightarrow> y \<le> i')"
    using boundedGreatest[of "\<lambda>i'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" i n] by blast
  with assms show ?thesis using lActive_def Nat.Greatest_le_nat[of "\<lambda>i'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>" i] by simp
qed
  
lemma lActive_greater_active:
  assumes "n > \<langle>c \<and> t\<rangle>"
    and "\<forall>n'' > n'. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>"
  shows "\<not> \<parallel>c\<parallel>\<^bsub>t n\<^esub>"
proof (rule ccontr)
  assume "\<not> \<not> \<parallel>c\<parallel>\<^bsub>t n\<^esub>"
  with \<open>\<forall>n'' > n'. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>\<close> have "n \<le> \<langle>c \<and> t\<rangle>" using lActive_greatest by simp
  thus False using assms by simp
qed
  
lemma lActive_greater_active_all:
  assumes "\<forall>n'' > n'. \<not> \<parallel>c\<parallel>\<^bsub>t n''\<^esub>"
  shows "\<not>(\<exists>n > \<langle>c \<and> t\<rangle>. \<parallel>c\<parallel>\<^bsub>t n\<^esub>)" 
proof (rule ccontr)
  assume "\<not>\<not>(\<exists>n > \<langle>c \<and> t\<rangle>. \<parallel>c\<parallel>\<^bsub>t n\<^esub>)"
  then obtain "n" where "n>\<langle>c \<and> t\<rangle>" and "\<parallel>c\<parallel>\<^bsub>t n\<^esub>" by blast
  with \<open>\<forall>n'' > n'. \<not> (\<parallel>c\<parallel>\<^bsub>t n''\<^esub>)\<close> have "\<not> \<parallel>c\<parallel>\<^bsub>t n\<^esub>" using lActive_greater_active by simp
  with \<open>\<parallel>c\<parallel>\<^bsub>t n\<^esub>\<close> show False by simp
qed

lemma lActive_equality:
  assumes "\<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "(\<And>x. \<parallel>c\<parallel>\<^bsub>t x\<^esub> \<Longrightarrow> x \<le> i)"
  shows "\<langle>c \<and> t\<rangle> = i" unfolding lActive_def using assms Greatest_equality[of "\<lambda>i'. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>"] by simp
    
lemma nxtActive_lactive:
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<not> (\<exists>i>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  shows "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>=\<langle>c \<and> t\<rangle>"
proof -
  from assms(1) have "\<parallel>c\<parallel>\<^bsub>t \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>" using nxtActI by auto
  moreover from assms have "\<not> (\<exists>i'\<ge>Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)" using nxtActive_no_active by simp
  hence "(\<And>x. \<parallel>c\<parallel>\<^bsub>t x\<^esub> \<Longrightarrow> x \<le> \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)" using not_less_eq_eq by auto
  ultimately show ?thesis using \<open>\<not> (\<exists>i'\<ge>Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)\<close> lActive_equality by simp
qed
    
subsection "Mapping Time Points"
text \<open>
  In the following we introduce two operators to map time-points between configuration traces and behavior traces.
\<close>

subsubsection "Configuration Trace to Behavior Trace"
text \<open>
  First we provide an operator which maps a point in time of a configuration trace to the corresponding point in time of a behavior trace.
\<close>
  
definition cnf2bhv :: "'id \<Rightarrow> (nat \<Rightarrow> cnf) \<Rightarrow> nat \<Rightarrow> nat" ("\<^bsub>_\<^esub>\<down>\<^bsub>_\<^esub>(_)" [150,150,150] 110)
  where "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) \<equiv> the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 + (n - \<langle>c \<and> t\<rangle>)"

lemma cnf2bhv_mono:
  assumes "n'\<ge>n"
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)"
  by (simp add: assms cnf2bhv_def diff_le_mono)

lemma cnf2bhv_mono_strict:
  assumes "n\<ge>\<langle>c \<and> t\<rangle>" and "n'>n"
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') > \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)"
  using assms cnf2bhv_def by auto

text "Note that the functions are nat, that means that also in the case the difference is negative they will return a 0!"
lemma cnf2bhv_ge_llength[simp]:
  assumes "n\<ge>\<langle>c \<and> t\<rangle>"
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) \<ge> the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
  using assms cnf2bhv_def by simp

lemma cnf2bhv_greater_llength[simp]:
  assumes "n>\<langle>c \<and> t\<rangle>"
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) > the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
  using assms cnf2bhv_def by simp

lemma cnf2bhv_suc[simp]:
  assumes "n\<ge>\<langle>c \<and> t\<rangle>"
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(Suc n) = Suc (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n))"
  using assms cnf2bhv_def by simp

lemma cnf2bhv_lActive[simp]:
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<langle>c \<and> t\<rangle>) = the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
  using cnf2bhv_def by simp
    
lemma cnf2bhv_lnth_lappend:
  assumes act: "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and nAct: "\<nexists>i. i\<ge>n \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
  shows "lnth ((\<pi>\<^bsub>c\<^esub>(inf_llist t)) @\<^sub>l (inf_llist t')) (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)) = lnth (inf_llist t') (n - \<langle>c \<and> t\<rangle> - 1)"
    (is "?lhs = ?rhs")
proof -
  from nAct have "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))" using proj_finite2 by auto
  then obtain k where k_def: "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) = enat k" using lfinite_llength_enat by blast
  moreover have "k \<le> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)"
  proof -
    from nAct have "\<nexists>i. i>n-1 \<and> \<parallel>c\<parallel>\<^bsub>t i\<^esub>" by simp
    with act have "\<langle>c \<and> t\<rangle> \<le> n-1" using lActive_less by auto
    moreover have "n>0" using act nAct by auto
    ultimately have "\<langle>c \<and> t\<rangle> < n" by simp
    hence "the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t)) - 1 < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)" using cnf2bhv_greater_llength by simp
    with k_def show ?thesis by simp
  qed
  ultimately have "?lhs = lnth (inf_llist t') (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) - k)" using lnth_lappend2 by blast
  moreover have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) - k = n - \<langle>c \<and> t\<rangle> - 1"
  proof -
    from cnf2bhv_def have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) - k = the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t)) - 1 + (n - \<langle>c \<and> t\<rangle>) - k"
      by simp
    also have "\<dots> = the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t)) - 1 + (n - \<langle>c \<and> t\<rangle>) -
      the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))" using k_def by simp
    also have "\<dots> = the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t)) + (n - \<langle>c \<and> t\<rangle>) - 1 -
      the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))"
    proof -
      have "\<exists>i. enat i < llength (inf_llist t) \<and> \<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) i\<^esub>" by (simp add: act)
      hence "llength (\<pi>\<^bsub>c\<^esub>inf_llist t) \<ge> 1" using proj_one by simp
      moreover from k_def have "llength (\<pi>\<^bsub>c\<^esub>inf_llist t) \<noteq> \<infinity>" by simp
      ultimately have "the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t)) \<ge> 1" by (simp add: k_def one_enat_def)
      thus ?thesis by simp
    qed
    also have "\<dots> = the_enat (llength (\<pi>\<^bsub>c\<^esub>inf_llist t)) + (n - \<langle>c \<and> t\<rangle>) -
      the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1" by simp
    also have "\<dots> = n - \<langle>c \<and> t\<rangle> - 1" by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis by simp
qed

lemma nAct_cnf2proj_Suc_dist:
  assumes "\<exists>i\<ge>n. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "\<not>(\<exists>i>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. \<parallel>c\<parallel>\<^bsub>t i\<^esub>)"
  shows "Suc (the_enat \<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle>)=\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)"
proof -
  have "the_enat \<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle> = \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)" (is "?LHS = ?RHS")
  proof -
    from assms have "?RHS = the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
      using nxtActive_lactive[of n c t] by simp
    also have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) = eSuc (\<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle>)"
    proof -
      from assms have "\<not> (\<exists>i'\<ge> Suc (\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>). \<parallel>c\<parallel>\<^bsub>t i'\<^esub>)" using nxtActive_no_active by simp
      hence "\<langle>c #\<^bsub>Suc (\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)\<^esub> inf_llist t\<rangle> = llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
        using nAct_eq_proj[of "Suc (\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)" c "inf_llist t"] by simp
      moreover from assms(1) have "\<parallel>c\<parallel>\<^bsub>t (\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)\<^esub>" using nxtActI by blast
      hence "\<langle>c #\<^bsub>Suc (\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)\<^esub> inf_llist t\<rangle> = eSuc (\<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle>)" by simp
      ultimately show ?thesis by simp
    qed
    also have "the_enat(eSuc (\<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle>)) - 1 = (\<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle>)"
    proof -
      have "\<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle> \<noteq> \<infinity>" by simp
      hence "the_enat(eSuc (\<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle>)) = Suc(the_enat(\<langle>c #\<^bsub>\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub> inf_llist t\<rangle>))"
        using the_enat_eSuc by simp
      thus ?thesis by simp
    qed
    also have "\<dots> = ?LHS"
    proof -
      have "enat \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> - 1 < llength (inf_llist t)" by (simp add: one_enat_def)
      moreover from assms(1) have "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<ge>n" and
        "\<nexists>k. enat n \<le> enat k \<and> enat k < enat \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub> \<and> \<parallel>c\<parallel>\<^bsub>lnth (inf_llist t) k\<^esub>" using nxtActI by auto
      ultimately have "\<langle>c #\<^bsub>enat \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<^esub>inf_llist t\<rangle> = \<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle>"
        using nAct_not_active_same[of n "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" "inf_llist t" c] by simp
      moreover have "\<langle>c #\<^bsub>enat n\<^esub>inf_llist t\<rangle>\<noteq>\<infinity>" by simp
      ultimately show ?thesis by auto
    qed
    finally show ?thesis by fastforce
  qed      
  moreover from assms have "\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>=\<langle>c \<and> t\<rangle>" using nxtActive_lactive by simp
  hence "Suc (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)) = \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(Suc \<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>)" using cnf2bhv_suc[where n="\<langle>c \<rightarrow> t\<rangle>\<^bsub>n\<^esub>"] by simp
  ultimately show ?thesis by simp
qed

subsubsection "Behavior Trace to Configuration Trace"
text \<open>
  Next we define an operator to map a point in time of a behavior trace back to a corresponding point in time for a configuration trace.
\<close>

definition bhv2cnf :: "'id \<Rightarrow> (nat \<Rightarrow> cnf) \<Rightarrow> nat \<Rightarrow> nat" ("\<^bsub>_\<^esub>\<up>\<^bsub>_\<^esub>(_)" [150,150,150] 110)
  where "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) \<equiv> \<langle>c \<and> t\<rangle> + (n - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1))"

lemma bhv2cnf_mono:
  assumes "n'\<ge>n"
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)"
  by (simp add: assms bhv2cnf_def diff_le_mono)    

lemma bhv2cnf_mono_strict:
  assumes "n'>n"
    and "n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') > \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)"
  using assms bhv2cnf_def by auto

text "Note that the functions are nat, that means that also in the case the difference is negative they will return a 0!"
lemma bhv2cnf_ge_lActive[simp]:
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) \<ge> \<langle>c \<and> t\<rangle>"
  using bhv2cnf_def by simp

lemma bhv2cnf_greater_lActive[simp]:
  assumes "n>the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) > \<langle>c \<and> t\<rangle>"
  using assms bhv2cnf_def by simp
    
lemma bhv2cnf_lActive[simp]:
  assumes "\<exists>i. \<parallel>c\<parallel>\<^bsub>t i\<^esub>"
    and "lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))"
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) = Suc (\<langle>c \<and> t\<rangle>)"
proof -
  from assms have "\<pi>\<^bsub>c\<^esub>(inf_llist t)\<noteq> []\<^sub>l" by simp
  hence "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) > 0" by (simp add: lnull_def)
  moreover from \<open>lfinite (\<pi>\<^bsub>c\<^esub>(inf_llist t))\<close> have "llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)) \<noteq> \<infinity>"
    using llength_eq_infty_conv_lfinite by auto
  ultimately have "the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) > 0" using enat_0_iff(1) by fastforce
  hence "the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1) = 1" by simp
  thus ?thesis using bhv2cnf_def by simp
qed
  
subsubsection "Relating the Mappings"
text \<open>
  In the following we provide some properties about the relationship between the two mapping operators.
\<close>
  
lemma bhv2cnf_cnf2bhv:
  assumes "n \<ge> \<langle>c \<and> t\<rangle>"
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)) = n" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<langle>c \<and> t\<rangle> + ((\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)) - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1))"
    using bhv2cnf_def by simp
  also have "\<dots> = \<langle>c \<and> t\<rangle> + (((the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) - 1 + (n - \<langle>c \<and> t\<rangle>)) -
    (the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1))" using cnf2bhv_def by simp
  also have "(the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) - 1 + (n - (\<langle>c \<and> t\<rangle>)) -
    (the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1) = (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) - 1 -
    ((the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t)))) - 1) + (n - (\<langle>c \<and> t\<rangle>))" by simp
  also have "\<dots> = n - (\<langle>c \<and> t\<rangle>)" by simp
  also have "(\<langle>c \<and> t\<rangle>) + (n - (\<langle>c \<and> t\<rangle>)) = (\<langle>c \<and> t\<rangle>) + n - \<langle>c \<and> t\<rangle>" using assms by simp
  also have "\<dots> = ?rhs" by simp
  finally show ?thesis .
qed
    
lemma cnf2bhv_bhv2cnf:
  assumes "n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) = n" (is "?lhs = ?rhs")
proof -
  have "?lhs = the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 + ((\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)) - (\<langle>c \<and> t\<rangle>))"
    using cnf2bhv_def by simp
  also have "\<dots> = the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 + (\<langle>c \<and> t\<rangle> +
    (n - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1)) - (\<langle>c \<and> t\<rangle>))" using bhv2cnf_def by simp
  also have "\<langle>c \<and> t\<rangle> + (n - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1)) - (\<langle>c \<and> t\<rangle>) =
    \<langle>c \<and> t\<rangle> - (\<langle>c \<and> t\<rangle>) + (n - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1))" by simp
  also have "\<dots> = n - (the_enat(llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1)" by simp      
  also have "the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1 + (n - (the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1)) =
    n - (the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1) + (the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1)" by simp
  also have "\<dots> = n + ((the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1) -
    (the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1))" using assms by simp
  also have "\<dots> = ?rhs" by simp
  finally show ?thesis .
qed
  
lemma p2c_mono_c2p:
  assumes "n \<ge> \<langle>c \<and> t\<rangle>"
      and "n' \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)"
    shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<ge> n"
proof -
  from \<open>n' \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n)\<close> have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n') \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n))" using bhv2cnf_mono by simp
  thus ?thesis using bhv2cnf_cnf2bhv \<open>n \<ge> \<langle>c \<and> t\<rangle>\<close> by simp
qed
  
lemma p2c_mono_c2p_strict:
  assumes "n \<ge> \<langle>c \<and> t\<rangle>"
      and "n<\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')"
  shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) < n'"
proof (rule ccontr)
  assume "\<not> (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) < n')"
  hence "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n) \<ge> n'" by simp
  with \<open>n \<ge> \<langle>c \<and> t\<rangle>\<close> have "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(nat (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n))) \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n')"
    using bhv2cnf_mono by simp
  hence "\<not>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(nat (\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n))) < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'))" by simp
  with \<open>n \<ge> \<langle>c \<and> t\<rangle>\<close> have  "\<not>(n < \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n'))"
    using "bhv2cnf_cnf2bhv" by simp
  with assms show False by simp
qed
  
lemma c2p_mono_p2c:
  assumes "n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
      and "n' \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)"
    shows "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> n"
proof -
  from \<open>n' \<ge> \<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n)\<close> have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n') \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n))" using cnf2bhv_mono by simp
  thus ?thesis using cnf2bhv_bhv2cnf \<open>n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1\<close> by simp
qed

lemma c2p_mono_p2c_strict:
  assumes "n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1"
      and "n<\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n')"
  shows "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) < n'"
proof (rule ccontr)
  assume "\<not> (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) < n')"
  hence "\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n) \<ge> n'" by simp
  with \<open>n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1\<close> have "\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(nat (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n))) \<ge> \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n')"
    using cnf2bhv_mono by simp
  hence "\<not>(\<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(nat (\<^bsub>c\<^esub>\<up>\<^bsub>t\<^esub>(n))) < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'))" by simp
  with \<open>n \<ge> the_enat (llength (\<pi>\<^bsub>c\<^esub>(inf_llist t))) - 1\<close> have  "\<not>(n < \<^bsub>c\<^esub>\<down>\<^bsub>t\<^esub>(n'))"
    using "cnf2bhv_bhv2cnf" by simp
  with assms show False by simp
qed

end

end
