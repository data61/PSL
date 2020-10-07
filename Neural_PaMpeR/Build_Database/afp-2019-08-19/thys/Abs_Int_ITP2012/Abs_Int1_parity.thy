(* Author: Tobias Nipkow *)

theory Abs_Int1_parity
imports Abs_Int1
begin

subsection "Parity Analysis"

datatype parity = Even | Odd | Either

text\<open>Instantiation of class @{class preord} with type @{typ parity}:\<close>

instantiation parity :: preord
begin

text\<open>First the definition of the interface function \<open>\<sqsubseteq>\<close>. Note that
the header of the definition must refer to the ascii name @{const le} of the
constants as \<open>le_parity\<close> and the definition is named \<open>le_parity_def\<close>.  Inside the definition the symbolic names can be used.\<close>

definition le_parity where
"x \<sqsubseteq> y = (y = Either \<or> x=y)"

text\<open>Now the instance proof, i.e.\ the proof that the definition fulfills
the axioms (assumptions) of the class. The initial proof-step generates the
necessary proof obligations.\<close>

instance
proof
  fix x::parity show "x \<sqsubseteq> x" by(auto simp: le_parity_def)
next
  fix x y z :: parity assume "x \<sqsubseteq> y" "y \<sqsubseteq> z" thus "x \<sqsubseteq> z"
    by(auto simp: le_parity_def)
qed

end

text\<open>Instantiation of class @{class SL_top} with type @{typ parity}:\<close>

instantiation parity :: SL_top
begin


definition join_parity where
"x \<squnion> y = (if x \<sqsubseteq> y then y else if y \<sqsubseteq> x then x else Either)"

definition Top_parity where
"\<top> = Either"

text\<open>Now the instance proof. This time we take a lazy shortcut: we do not
write out the proof obligations but use the \<open>goali\<close> primitive to refer
to the assumptions of subgoal i and \<open>case?\<close> to refer to the
conclusion of subgoal i. The class axioms are presented in the same order as
in the class definition.\<close>

instance
proof (standard, goal_cases)
  case 1 (*join1*) show ?case by(auto simp: le_parity_def join_parity_def)
next
  case 2 (*join2*) show ?case by(auto simp: le_parity_def join_parity_def)
next
  case 3 (*join least*) thus ?case by(auto simp: le_parity_def join_parity_def)
next
  case 4 (*Top*) show ?case by(auto simp: le_parity_def Top_parity_def)
qed

end


text\<open>Now we define the functions used for instantiating the abstract
interpretation locales. Note that the Isabelle terminology is
\emph{interpretation}, not \emph{instantiation} of locales, but we use
instantiation to avoid confusion with abstract interpretation.\<close>

fun \<gamma>_parity :: "parity \<Rightarrow> val set" where
"\<gamma>_parity Even = {i. i mod 2 = 0}" |
"\<gamma>_parity Odd  = {i. i mod 2 = 1}" |
"\<gamma>_parity Either = UNIV"

fun num_parity :: "val \<Rightarrow> parity" where
"num_parity i = (if i mod 2 = 0 then Even else Odd)"

fun plus_parity :: "parity \<Rightarrow> parity \<Rightarrow> parity" where
"plus_parity Even Even = Even" |
"plus_parity Odd  Odd  = Even" |
"plus_parity Even Odd  = Odd" |
"plus_parity Odd  Even = Odd" |
"plus_parity Either y  = Either" |
"plus_parity x Either  = Either"

text\<open>First we instantiate the abstract value interface and prove that the
functions on type @{typ parity} have all the necessary properties:\<close>

interpretation Val_abs
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
proof (standard, goal_cases) txt\<open>of the locale axioms\<close>
  fix a b :: parity
  assume "a \<sqsubseteq> b" thus "\<gamma>_parity a \<subseteq> \<gamma>_parity b"
    by(auto simp: le_parity_def)
next txt\<open>The rest in the lazy, implicit way\<close>
  case 2 show ?case by(auto simp: Top_parity_def)
next
  case 3 show ?case by auto
next
  case (4 _ a1 _ a2) thus ?case
  proof(cases a1 a2 rule: parity.exhaust[case_product parity.exhaust])
  qed (auto, presburger)
qed

text\<open>Instantiating the abstract interpretation locale requires no more
proofs (they happened in the instatiation above) but delivers the
instantiated abstract interpreter which we call AI:\<close>

global_interpretation Abs_Int
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
defines aval_parity = aval' and step_parity = step' and AI_parity = AI
..


subsubsection "Tests"

definition "test1_parity =
  ''x'' ::= N 1;;
  WHILE Less (V ''x'') (N 100) DO ''x'' ::= Plus (V ''x'') (N 2)"

value "show_acom_opt (AI_parity test1_parity)"

definition "test2_parity =
  ''x'' ::= N 1;;
  WHILE Less (V ''x'') (N 100) DO ''x'' ::= Plus (V ''x'') (N 3)"

value "show_acom ((step_parity \<top> ^^1) (anno None test2_parity))"
value "show_acom ((step_parity \<top> ^^2) (anno None test2_parity))"
value "show_acom ((step_parity \<top> ^^3) (anno None test2_parity))"
value "show_acom ((step_parity \<top> ^^4) (anno None test2_parity))"
value "show_acom ((step_parity \<top> ^^5) (anno None test2_parity))"
value "show_acom_opt (AI_parity test2_parity)"


subsubsection "Termination"

global_interpretation Abs_Int_mono
where \<gamma> = \<gamma>_parity and num' = num_parity and plus' = plus_parity
proof (standard, goal_cases)
  case (1 a1 a2 b1 b2) thus ?case
  proof(cases a1 a2 b1 b2
   rule: parity.exhaust[case_product parity.exhaust[case_product parity.exhaust[case_product parity.exhaust]]]) (* FIXME - UGLY! *)
  qed (auto simp add:le_parity_def)
qed


definition m_parity :: "parity \<Rightarrow> nat" where
"m_parity x = (if x=Either then 0 else 1)"

lemma measure_parity:
  "(strict{(x::parity,y). x \<sqsubseteq> y})^-1 \<subseteq> measure m_parity"
by(auto simp add: m_parity_def le_parity_def)

lemma measure_parity_eq:
  "\<forall>x y::parity. x \<sqsubseteq> y \<and> y \<sqsubseteq> x \<longrightarrow> m_parity x = m_parity y"
by(auto simp add: m_parity_def le_parity_def)

lemma AI_parity_Some: "\<exists>c'. AI_parity c = Some c'"
by(rule AI_Some_measure[OF measure_parity measure_parity_eq])

end
