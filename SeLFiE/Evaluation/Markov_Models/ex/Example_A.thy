theory Example_A
  imports "../Classifying_Markov_Chain_States"
begin

section \<open>Example A\<close> text_raw \<open>\label{ex:A}\<close>

text \<open>

We formalize the following Markov chain:

\begin{center}
\begin{tikzpicture}[thick]

  \path [fill, color = gray!30] (0, 0) circle(0.6) ;

  \path [fill, color = gray!30] (1, 1) circle(0.6) ;

  \path [fill, color = gray!30] (4.5, 0.66) ellipse(2 and 1.9) ;

  \node (bot)  at (-1, 0) {} ;

  \node[draw,circle] (A)  at (0, 0) {$A$} ;

  \node[draw,circle] (B)  at (1, 1) {$B$} ;

  \node[draw,circle] (C1) at (3, 0) {$C_1$} ;

  \node[draw,circle] (C2) at (6, 0) {$C_2$} ;

  \node[draw,circle] (C3) at (4.5, 2) {$C_3$} ;

  \path[->, >=latex]
    (bot) edge (A)
    (A)   edge                node [above] {$\frac{1}{2}$} (B)
          edge                node [below] {$\frac{1}{2}$} (C1)
    (B)   edge [loop above]   node [left]  {$\frac{1}{2}$} (B)
          edge [out = 0]      node [above] {$\frac{1}{2}$} (C1)
    (C1)  edge [loop above]   node [above] {$\frac{1}{3}$} (C1)
          edge [bend left=15] node [above] {$\frac{1}{3}$} (C2)
          edge [bend left=15] node [above] {$\frac{1}{3}$} (C3)
    (C2)  edge [loop right]   node [above] {$\frac{1}{3}$} (C2)
          edge [bend left=15] node [above] {$\frac{1}{3}$} (C1)
          edge [bend left=15] node [above] {$\frac{1}{3}$} (C3)
    (C3)  edge [loop right]   node [above] {$\frac{1}{2}$} (C3)
          edge [bend left=15] node [above] {$\frac{1}{4}$} (C1)
          edge [bend left=15] node [above] {$\frac{1}{4}$} (C2) ;

\end{tikzpicture}
\end{center}

First we define the state space as its own type:

\<close>

datatype state = A | B | C1 | C2 | C3

text \<open>Now the state space is \<open>UNIV :: state set\<close>\<close>

lemma UNIV_state: "UNIV = {A, B, C1, C2, C3}"
  using state.nchotomy by auto

instance state :: finite
  by standard (simp add: UNIV_state)

text \<open>The transition function \<open>tau\<close> is easily defined using the case statement, this allows
us to give a sparse specification as all \<open>0\<close> cases are collected at the end.\<close>

definition tau :: "state \<Rightarrow> state \<Rightarrow> real" where
  "tau s t = (case (s, t) of
      (A,  B)  \<Rightarrow> 1 / 2 | (A,  C1) \<Rightarrow> 1 / 2
    | (B,  B)  \<Rightarrow> 1 / 2 | (B,  C1) \<Rightarrow> 1 / 2
    | (C1, C1) \<Rightarrow> 1 / 3 | (C1, C2) \<Rightarrow> 1 / 3 | (C1, C3) \<Rightarrow> 1 / 3
    | (C2, C1) \<Rightarrow> 1 / 3 | (C2, C2) \<Rightarrow> 1 / 3 | (C2, C3) \<Rightarrow> 1 / 3
    | (C3, C1) \<Rightarrow> 1 / 4 | (C3, C2) \<Rightarrow> 1 / 4 | (C3, C3) \<Rightarrow> 1 / 2
    | _ \<Rightarrow> 0)"

lift_definition K :: "state \<Rightarrow> state pmf" is tau
  by (auto simp: tau_def nn_integral_count_space_finite UNIV_state split: state.split simp del: ennreal_plus)

text \<open>We use the \<open>finite_pmf\<close>-locale which introduces the point measure \<open>tau.M\<close>, and
  provides us with the necessary simplifier setup.\<close>

interpretation A: MC_syntax K .

subsection \<open>The essential classs @{term "{C1, C2, C3}"}\<close>

context
begin

interpretation pmf_as_function .

lemma A_E_eq:
  "set_pmf (K x) = (case x of A \<Rightarrow> {B, C1} | B \<Rightarrow> {B, C1} | _ \<Rightarrow> {C1, C2, C3})"
  using state.nchotomy by transfer (auto simp: tau_def split: prod.split state.split)

lemma A_essential: "A.essential_class {C1, C2, C3}"
  by (rule A.essential_classI2) (auto simp: A_E_eq)

lemma A_aperiodic: "A.aperiodic {C1, C2, C3}"
  unfolding A.aperiodic_def
proof safe
  have eq: "\<And>x'. (if x' = C1 then 1 else 0) = indicator {C1} x'" by auto

  show "{C1, C2, C3} \<in> UNIV // A.communicating"
    using A_essential by (simp add: A.essential_class_def)
  then have "A.period {C1, C2, C3} = Gcd (A.period_set C1)"
    by (rule A.period_eq) simp
  also have "\<dots> = 1"
    by (rule Gcd_nat_eq_one) (simp add: A_E_eq A.period_set_def A.p_Suc' A.p_0 eq measure_pmf_single pmf_positive)
  finally show "A.period {C1, C2, C3} = 1" .
qed

subsection \<open>The stationary distribution \<open>n\<close>\<close>

text \<open>Similar to \<open>tau\<close> we introduce \<open>n\<close> using the \<open>finite_pmf\<close>-locale.\<close>

lift_definition n :: "state pmf" is "\<lambda>C1 \<Rightarrow> 0.3 | C2 \<Rightarrow> 0.3 | C3 \<Rightarrow> 0.4 | _ \<Rightarrow> 0"
  by (auto simp: UNIV_state nn_integral_count_space_finite split: state.split)

lemma stationary_distribution_N: "A.stationary_distribution n"
  unfolding A.stationary_distribution_def
  apply (auto intro!: pmf_eqI simp: pmf_bind integral_measure_pmf[of UNIV])
  apply transfer
  apply (auto simp: UNIV_state tau_def split: state.split)
  done

lemma exclusive_N[simp]: "set_pmf n = {C1, C2, C3}"
  using state.nchotomy by transfer (auto split: state.splits)

end

lemma n_is_limit:
  assumes x: "x \<in> {C1, C2, C3}" and y: "y \<in> {C1, C2, C3}"
  shows "(A.p x y) \<longlonglongrightarrow> pmf n y"
  using A.stationary_distribution_imp_p_limit[OF A_aperiodic A_essential _ stationary_distribution_N _ x y]
  by simp

lemma C_is_pos_recurrent: "x \<in> {C1, C2, C3} \<Longrightarrow> A.pos_recurrent x"
  using A.stationary_distributionD(1)[OF A_essential _ stationary_distribution_N] by auto

lemma C_recurrence_time:
  assumes x: "x \<in> {C1, C2, C3}"
  shows "A.U' x x = 1 / pmf n x"
proof -
  from A.stationary_distributionD(2)[OF A_essential _ stationary_distribution_N _]
  have "A.stat {C1, C2, C3} = n" by simp
  with x have "1 / pmf n x = 1 / emeasure (A.stat {C1, C2, C3}) {x}"
    by (simp add: emeasure_pmf_single pmf_positive divide_ennreal ennreal_1[symmetric] del: ennreal_1)
  also have "\<dots> = A.U' x x"
    unfolding A.stat_def using x
    by (subst emeasure_point_measure_finite) (simp_all add:  A.U'_def)
  finally show ?thesis ..
qed

end

