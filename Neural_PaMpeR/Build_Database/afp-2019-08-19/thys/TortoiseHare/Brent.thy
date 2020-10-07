(*<*)
theory Brent
imports
  Basis
begin
(*>*)
section\<open> Brent's algorithm \label{sec:brent} \<close>

text\<open>

@{cite "Brent:1980"} improved on the Tortoise and Hare algorithm and
used it to factor large primes. In practice it makes significantly
fewer calls to the function \<open>f\<close> before detecting a loop.

We begin by defining the base-2 logarithm.

\<close>

fun lg :: "nat \<Rightarrow> nat" where
[simp del]: "lg x = (if x \<le> 1 then 0 else 1 + lg (x div 2))"

lemma lg_safe:
  "lg 0 = 0"
  "lg (Suc 0) = 0"
  "lg (Suc (Suc 0)) = 1"
  "0 < x \<Longrightarrow> lg (x + x) = 1 + lg x"
by (simp_all add: lg.simps)

lemma lg_inv:
  "0 < x \<Longrightarrow> lg (2 ^ x) = x"
proof(induct x)
  case (Suc x) then show ?case
    by (cases x, simp_all add: lg.simps Suc_lessI not_le)
qed simp

lemma lg_inv2:
  "2 ^ i = x \<Longrightarrow> 2 ^ lg x = x"
by (induct i arbitrary: x) (auto simp: lg.simps, arith)

lemmas lg_simps = lg_safe lg_inv lg_inv2

subsection\<open> Finding \<open>lambda\<close> \<close>

text (in properties) \<open>

Imagine now that the Tortoise carries an unbounded number of carrots,
which he passes to the Hare when they meet, and the Hare has a
teleporter. The Hare eats a carrot each time she waits for the
function @{term "f"} to execute, and initially has just one. If she
runs out of carrots before meeting the Tortoise again, she teleports
him to her position, and he gives her twice as many carrots as the
last time they met (tracked by the variable \<open>carrots\<close>). By
counting how many carrots she has eaten from when she last teleported
the Tortoise (recorded in \<open>l\<close>) until she finally has surplus
carrots when she meets him again, the Hare directly discovers @{term
"lambda"}.

\<close>

record 'a state =
  m :: nat  \<comment> \<open>\<open>\<mu>\<close>\<close>
  l :: nat  \<comment> \<open>\<open>\<lambda>\<close>\<close>
  carrots :: nat
  hare :: "'a"
  tortoise :: "'a"

context properties
begin

definition (in fx0) find_lambda :: "'a state \<Rightarrow> 'a state" where
  "find_lambda \<equiv>
    (\<lambda>s. s\<lparr> carrots := 1, l := 1, tortoise := x0, hare := f x0 \<rparr>) ;;
    while (hare \<^bold>\<noteq> tortoise)
          ( ( \<^bold>if carrots \<^bold>= l \<^bold>then (\<lambda>s. s\<lparr> tortoise := hare s, carrots := 2 * carrots s, l := 0 \<rparr>)
                             \<^bold>else SKIP ) ;;
            (\<lambda>s. s\<lparr> hare := f (hare s), l := l s + 1 \<rparr>) )"

text\<open>

The termination argument goes intuitively as follows. The Hare eats as
many carrots as it takes to teleport the Tortoise into the
loop. Afterwards she continues the teleportation dance until the
Tortoise has given her enough carrots to make it all the way around
the loop and back to him.

We can calculate the Tortoise's position as a function of \<open>carrots\<close>.

\<close>

definition carrots_total :: "nat \<Rightarrow> nat" where
  "carrots_total c \<equiv> \<Sum>i<lg c. 2 ^ i"

lemma carrots_total_simps:
  "carrots_total (Suc 0) = 0"
  "carrots_total (Suc (Suc 0)) = 1"
  "2 ^ i = c \<Longrightarrow> carrots_total (c + c) = c + carrots_total c"
by (auto simp: carrots_total_def lg_simps)

definition find_lambda_measures :: "( (nat \<times> nat) \<times> (nat \<times> nat) ) set" where
  "find_lambda_measures \<equiv>
    measures [\<lambda>(l, c). mu - carrots_total c,
              \<lambda>(l, c). LEAST i. lambda \<le> c * 2^i,
              \<lambda>(l, c). c - l]"

lemma find_lambda_measures_wellfounded:
  "wf find_lambda_measures"
by (simp add: find_lambda_measures_def)

lemma find_lambda_measures_decreases1:
  assumes "c = 2 ^ i"
  assumes "mu \<le> carrots_total c \<longrightarrow> c \<le> lambda"
  assumes "seq (carrots_total c) \<noteq> seq (carrots_total c + c)"
  shows "( (c', 2 * c), (c, c) ) \<in> find_lambda_measures"
proof(cases "mu \<le> carrots_total c")
  case False with assms show ?thesis
    by (auto simp: find_lambda_measures_def carrots_total_simps mult_2 field_simps diff_less_mono2)
next
  case True
  { fix x assume x: "(0::nat) < x" have "\<exists>n. lambda \<le> x * 2 ^ n"
    proof(induct lambda)
      case (Suc i)
      then obtain n where "i \<le> x * 2 ^ n" by blast
      with x show ?case
        by (clarsimp intro!: exI[where x="Suc n"] simp: field_simps mult_2)
           (metis Nat.add_0_right Suc_leI linorder_neqE_nat mult_eq_0_iff nat_add_left_cancel not_le numeral_2_eq_2 old.nat.distinct(2) power_not_zero trans_le_add2)
    qed simp } note ex = this
  have "(LEAST j. lambda \<le> 2 ^ (i + 1) * 2 ^ j) < (LEAST j. lambda \<le> 2 ^ i * 2 ^ j)"
  proof(rule LeastI2_wellorder_ex[OF ex, rotated], rule LeastI2_wellorder_ex[OF ex, rotated])
    fix x y
    assume "lambda \<le> 2 ^ i * 2 ^ y"
           "lambda \<le> 2 ^ (i + 1) * 2 ^ x"
           "\<forall>z. lambda \<le> 2 ^ (i + 1) * 2 ^ z \<longrightarrow> x \<le> z"
    with True assms properties_loop[where i="carrots_total c" and j=1]
    show "x < y" by (cases y, auto simp: less_Suc_eq_le)
  qed simp_all
  with True \<open>c = 2 ^ i\<close> show ?thesis
    by (clarsimp simp: find_lambda_measures_def mult_2 carrots_total_simps field_simps power_add)
qed

lemma find_lambda_measures_decreases2:
  assumes "ls < c"
  shows "( (Suc ls, c), (ls, c) ) \<in> find_lambda_measures"
using assms by (simp add: find_lambda_measures_def)

lemma find_lambda:
  "\<lbrace>\<langle>True\<rangle>\<rbrace> find_lambda \<lbrace>l \<^bold>= \<langle>lambda\<rangle>\<rbrace>"
apply (simp add: find_lambda_def)
apply (rule hoare_pre)
apply (rule whileI[where I="\<langle>0\<rangle> \<^bold>< l \<^bold>\<and> l \<^bold>\<le> carrots \<^bold>\<and> (\<langle>mu\<rangle> \<^bold>\<le> carrots_total \<circ> carrots \<^bold>\<longrightarrow> l \<^bold>\<le> \<langle>lambda\<rangle>) \<^bold>\<and> (\<^bold>\<exists>i. carrots \<^bold>= \<langle>2^i\<rangle>)
                           \<^bold>\<and> tortoise \<^bold>= seq \<circ> carrots_total \<circ> carrots \<^bold>\<and> hare \<^bold>= seq \<circ> (l \<^bold>+ (carrots_total \<circ> carrots))"
                      and r="inv_image find_lambda_measures (l \<^bold>\<bowtie> carrots)"]
            wp_intro)+
   using properties_lambda_gt_0
   apply (clarsimp simp: field_simps mult_2_right carrots_total_simps)
   apply (intro conjI impI)
      apply (metis mult_2 power_Suc)
     apply (case_tac "mu \<le> carrots_total (l s)")
      apply (cut_tac i="carrots_total (l s)" and j="l s" in properties_distinct_contrapos, simp_all add: field_simps)[1]
     apply (cut_tac i="carrots_total (l s)" and j="l s" in properties_loops_ge_mu, simp_all add: field_simps)[1]
    apply (cut_tac i="carrots_total (2 ^ x)" and j=1 in properties_loop, simp)
    apply (fastforce simp: le_eq_less_or_eq field_simps)
   apply (cut_tac i="carrots_total (2 ^ x)" and j="l s" in properties_loops_ge_mu, simp_all add: field_simps)[1]
   apply (cut_tac i="carrots_total (2 ^ x)" and j="l s" in properties_distinct_contrapos, simp_all add: field_simps)[1]
  apply (simp add: find_lambda_measures_wellfounded)
 apply (clarsimp simp: add.commute find_lambda_measures_decreases1 find_lambda_measures_decreases2)
apply (rule wp_intro)
using properties_lambda_gt_0
apply (simp add: carrots_total_simps exI[where x=0])
done

subsection\<open> Finding \<open>mu\<close> \<close>

text\<open>

With @{term "lambda"} in hand, we can find \<open>mu\<close> using the same
approach as for the Tortoise and Hare (\S\ref{sec:th-finding-mu}),
after we first move the Hare to @{term "lambda"}.

\<close>

definition (in fx0) find_mu :: "'a state \<Rightarrow> 'a state" where
  "find_mu \<equiv>
    (\<lambda>s. s\<lparr> m := 0, tortoise := x0, hare := seq (l s) \<rparr>) ;;
    while (hare \<^bold>\<noteq> tortoise)
          (\<lambda>s. s\<lparr> tortoise := f (tortoise s), hare := f (hare s), m := m s + 1 \<rparr>)"

lemma find_mu:
  "\<lbrace>l \<^bold>= \<langle>lambda\<rangle>\<rbrace> find_mu \<lbrace>l \<^bold>= \<langle>lambda\<rangle> \<^bold>\<and> m \<^bold>= \<langle>mu\<rangle>\<rbrace>"
apply (simp add: find_mu_def)
apply (rule hoare_pre)
apply (rule whileI[where I="l \<^bold>= \<langle>lambda\<rangle> \<^bold>\<and> m \<^bold>\<le> \<langle>mu\<rangle> \<^bold>\<and> tortoise \<^bold>= seq \<circ> m \<^bold>\<and> hare \<^bold>= seq \<circ> (m \<^bold>+ l)"
                      and r="measure (\<langle>mu\<rangle> \<^bold>- m)"]
            wp_intro)+
   using properties_lambda_gt_0 properties_loop[where i=mu and j=1]
   apply (fastforce simp: le_less dest: properties_loops_ge_mu)
  apply simp
 using properties_loop[where i=mu and j=1, simplified]
 apply (fastforce simp: le_eq_less_or_eq)
apply (rule wp_intro)
apply simp
done


subsection\<open> Top level \<close>

definition (in fx0) brent :: "'a state \<Rightarrow> 'a state" where
  "brent \<equiv> find_lambda ;; find_mu"

theorem brent:
  "\<lbrace>\<langle>True\<rangle>\<rbrace> brent \<lbrace>l \<^bold>= \<langle>lambda\<rangle> \<^bold>\<and> m \<^bold>= \<langle>mu\<rangle>\<rbrace>"
unfolding brent_def
by (rule find_lambda find_mu wp_intro)+

end

corollary brent_correct:
  assumes s': "s' = fx0.brent f x arbitrary"
  shows "fx0.properties f x (l s') (m s')"
using assms properties.brent[where f=f and ?x0.0=x]
by (fastforce intro: fx0.properties_existence[where f=f and ?x0.0=x]
               simp:  Basis.properties_def valid_def)

schematic_goal brent_code[code]:
  "fx0.brent f x = ?code"
unfolding fx0.brent_def fx0.find_lambda_def fx0.find_mu_def fcomp_assoc[symmetric] fcomp_comp
by (rule refl)

export_code fx0.brent in SML
(*<*)

end
(*>*)
