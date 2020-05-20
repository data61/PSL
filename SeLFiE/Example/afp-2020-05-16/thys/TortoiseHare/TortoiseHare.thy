(*<*)
theory TortoiseHare
imports
  Basis
begin

(*>*)
section\<open> The Tortoise and the Hare \label{sec:th} \<close>

text (in properties) \<open>

The key to the Tortoise and Hare algorithm is that any @{term "nu"}
such that @{term "seq (nu + nu) = seq nu"} must be divisible by @{term
"lambda"}. Intuitively the first @{term "nu"} steps get us into the
loop. If the second @{term "nu"} steps return us to the same value of
the sequence, then we must have gone around the loop one or more
times.

\<close>

lemma (in properties) lambda_dvd_nu:
  assumes "seq (i + i) = seq i"
  shows "lambda dvd i"
proof(cases "i = 0")
  case False
  with assms have "mu \<le> i" by (auto simp: properties_loops_ge_mu)
  with assms have "seq (i + i mod lambda) = seq i"
    using properties_loop[where i="i + i mod lambda" and j="i div lambda"] by simp
  from properties_distinct_contrapos[OF this] show ?thesis
    by simp (meson dvd_eq_mod_eq_0 mod_less_divisor not_less properties_lambda_gt_0)
qed simp

text (in properties) \<open>

The program is split into three loops; we find @{term "nu"}, @{term
"mu"} and @{term "lambda"} in that order.

\<close>

subsection\<open> Finding \<open>nu\<close> \<close>

text\<open>

The state space of the program tracks each of the variables we wish to
discover, and the current positions of the Tortoise and Hare.

\<close>

record 'a state =
  nu :: nat \<comment> \<open>\<open>\<nu>\<close>\<close>
  m :: nat  \<comment> \<open>\<open>\<mu>\<close>\<close>
  l :: nat  \<comment> \<open>\<open>\<lambda>\<close>\<close>
  hare :: "'a"
  tortoise :: "'a"

context properties
begin

text\<open>

The Hare proceeds at twice the speed of the Tortoise. The program
tracks how many steps the Tortoise has taken in @{term "nu"}.

\<close>

definition (in fx0) find_nu :: "'a state \<Rightarrow> 'a state" where
  "find_nu \<equiv>
    (\<lambda>s. s\<lparr> nu := 1, tortoise := f(x0), hare := f(f(x0)) \<rparr>) ;;
    while (hare \<^bold>\<noteq> tortoise)
          (\<lambda>s. s\<lparr> nu := nu s + 1, tortoise := f(tortoise s), hare := f(f(hare s)) \<rparr>)"

text\<open>

If this program terminates, we expect \<open>seq \<circ> (nu
\<^bold>+ nu) \<^bold>= seq \<circ> nu\<close> to hold in the final state.

The simplest approach to showing termination is to define a suitable
\<open>nu\<close> in terms of \<open>lambda\<close> and \<open>mu\<close>, which also
gives us an upper bound on the number of calls to \<open>f\<close>.

\<close>

definition nu_witness :: nat where
  "nu_witness \<equiv> mu + lambda - mu mod lambda"

text\<open>

This constant has the following useful properties:

\<close>

lemma nu_witness_properties:
  "mu < nu_witness"
  "nu_witness \<le> lambda + mu"
  "lambda dvd nu_witness"
  "mu = 0 \<Longrightarrow> nu_witness = lambda"
unfolding nu_witness_def
using properties_lambda_gt_0
apply (simp_all add: less_diff_conv divide_simps)
apply (metis minus_mod_eq_div_mult [symmetric] dvd_def mod_add_self2 mult.commute)
done

text\<open>

These demonstrate that @{term "nu_witness"} has the key property:

\<close>

lemma nu_witness:
  shows "seq (nu_witness + nu_witness) = seq nu_witness"
using nu_witness_properties properties_loop
by (clarsimp simp: dvd_def field_simps)

text\<open>

Termination amounts to showing that the Tortoise gets closer to @{term
"nu_witness"} on each iteration of the loop.

\<close>

definition find_nu_measure :: "(nat \<times> nat) set" where
  "find_nu_measure \<equiv> measure (\<lambda>\<nu>. nu_witness - \<nu>)"

lemma find_nu_measure_wellfounded:
  "wf find_nu_measure"
by (simp add: find_nu_measure_def)

lemma find_nu_measure_decreases:
  assumes "seq (\<nu> + \<nu>) \<noteq> seq \<nu>"
  assumes "\<nu> \<le> nu_witness"
  shows "(Suc \<nu>, \<nu>) \<in> find_nu_measure"
using nu_witness_properties nu_witness assms
by (auto simp: find_nu_measure_def le_eq_less_or_eq)

text\<open>

The remainder of the Hoare proof is straightforward.

\<close>

lemma find_nu:
  "\<lbrace>\<langle>True\<rangle>\<rbrace> find_nu \<lbrace>nu \<^bold>\<in> \<langle>{0<..lambda + mu}\<rangle> \<^bold>\<and> seq \<circ> (nu \<^bold>+ nu) \<^bold>= seq \<circ> nu \<^bold>\<and> hare \<^bold>= seq \<circ> nu\<rbrace>"
apply (simp add: find_nu_def)
apply (rule hoare_pre)
 apply (rule whileI[where I="nu \<^bold>\<in> \<langle>{0<..nu_witness}\<rangle> \<^bold>\<and> (\<^bold>\<forall>i. \<langle>0 < i\<rangle> \<^bold>\<and> \<langle>i\<rangle> \<^bold>< nu \<^bold>\<longrightarrow> \<langle>seq (i + i) \<noteq> seq i\<rangle>)
                            \<^bold>\<and> tortoise \<^bold>= seq \<circ> nu \<^bold>\<and> hare \<^bold>= seq \<circ> (nu \<^bold>+ nu)"
                       and r="inv_image find_nu_measure nu"]
             wp_intro)+
    using nu_witness_properties nu_witness
    apply (fastforce simp: le_eq_less_or_eq elim: less_SucE)
   apply (simp add: find_nu_measure_wellfounded)
  apply (simp add: find_nu_measure_decreases)
 apply (rule wp_intro)
using nu_witness_properties
apply auto
done


subsubsection\<open> Side observations \<close>

text\<open>

We can also show termination ala \citet{Filliatre:2007}.

\<close>

definition find_nu_measures :: "(nat \<times> nat) set" where
  "find_nu_measures \<equiv>
    measures [\<lambda>\<nu>. mu - \<nu>, \<lambda>\<nu>. LEAST i. seq (\<nu> + \<nu> + i) = seq \<nu>]"

lemma find_nu_measures_wellfounded:
  "wf find_nu_measures"
by (simp add: find_nu_measures_def)

lemma find_nu_measures_existence:
  assumes \<nu>: "mu \<le> \<nu>"
  shows "\<exists>i. seq (\<nu> + \<nu> + i) = seq \<nu>"
proof(cases "seq (\<nu> + \<nu>) = seq \<nu>")
 case False
 from properties_lambda_gt_0 obtain k where k: "\<nu> \<le> k * lambda"
   by (metis One_nat_def Suc_leI mult.right_neutral mult_le_mono order_refl)
 from \<nu> k have "seq (\<nu> + \<nu> + (k * lambda - \<nu>)) = seq (mu + (\<nu> - mu) + k * lambda)" by (simp add: field_simps)
 also from \<nu> properties_loop have "\<dots> = seq \<nu>" by simp
 finally show ?thesis by blast
qed (simp add: exI[where x=0])

lemma find_nu_measures_decreases:
  assumes \<nu>: "seq (\<nu> + \<nu>) \<noteq> seq \<nu>"
  shows "(Suc \<nu>, \<nu>) \<in> find_nu_measures"
proof(cases "mu \<le> \<nu>")
  case True
  then have "mu \<le> Suc \<nu>" by simp
  have "(LEAST i. seq (Suc \<nu> + Suc \<nu> + i) = seq (Suc \<nu>)) < (LEAST i. seq (\<nu> + \<nu> + i) = seq \<nu>)"
  proof(rule LeastI2_wellorder_ex[OF find_nu_measures_existence[OF \<open>mu \<le> Suc \<nu>\<close>]],
        rule LeastI2_wellorder_ex[OF find_nu_measures_existence[OF \<open>mu \<le> \<nu>\<close>]])
    fix x y
    assume x: "seq (Suc \<nu> + Suc \<nu> + x) = seq (Suc \<nu>)"
              "\<forall>z. seq (Suc \<nu> + Suc \<nu> + z) = seq (Suc \<nu>) \<longrightarrow> x \<le> z"
    assume y: "seq (\<nu> + \<nu> + y) = seq \<nu>"
    from \<nu> \<open>mu \<le> \<nu>\<close> y have "0 < y" by (cases y) simp_all
    with y have "seq (Suc \<nu> + Suc \<nu> + (y - 1)) = seq (Suc \<nu>)" by (auto elim: seq_inj)
    with \<open>0 < y\<close> spec[OF x(2), where x="y - 1"] y show "x < y" by simp
  qed
  with True \<nu> show ?thesis by (simp add: find_nu_measures_def)
qed (auto simp: find_nu_measures_def)

lemma "find_nu_Filliâtre":
  "\<lbrace>\<langle>True\<rangle>\<rbrace> find_nu \<lbrace>\<langle>0\<rangle> \<^bold>< nu \<^bold>\<and> seq \<circ> (nu \<^bold>+ nu) \<^bold>= seq \<circ> nu \<^bold>\<and> hare \<^bold>= seq \<circ> nu\<rbrace>"
apply (simp add: find_nu_def)
apply (rule hoare_pre)
 apply (rule whileI[where I="\<langle>0\<rangle> \<^bold>< nu \<^bold>\<and> tortoise \<^bold>= seq \<circ> nu \<^bold>\<and> hare \<^bold>= seq \<circ> (nu \<^bold>+ nu)"
                      and r="inv_image find_nu_measures nu"]
             wp_intro)+
    apply clarsimp
   apply (simp add: find_nu_measures_wellfounded)
  apply (simp add: find_nu_measures_decreases)
 apply (rule wp_intro)
apply (simp add: properties_lambda_gt_0)
done

text\<open>

This approach does not provide an upper bound on \<open>nu\<close> however.

@{cite "Harper:PiSML:2011"} observes (in his \S13.5.2) that if \<open>mu\<close> is zero then \<open>nu = lambda\<close>.

\<close>

lemma Harper:
  assumes "mu = 0"
  shows "\<lbrace>\<langle>True\<rangle>\<rbrace> find_nu \<lbrace>nu \<^bold>= \<langle>lambda\<rangle>\<rbrace>"
by (rule hoare_post_imp[OF find_nu]) (fastforce simp: assms dvd_def dest: lambda_dvd_nu)


subsection\<open> Finding \<open>mu\<close> \label{sec:th-finding-mu} \<close>

text\<open>

We recover \<open>mu\<close> from \<open>nu\<close> by exploiting the fact that
lambda divides @{term "nu"}: the Tortoise, reset to @{term "x0"}
and the Hare, both now moving at the same speed, will meet at @{term
"mu"}.

\<close>

lemma mu_nu:
  assumes si: "seq (i + i) = seq i"
  assumes j: "mu \<le> j"
  shows "seq (j + i) = seq j"
using lambda_dvd_nu[OF si] properties_loop[OF j]
by (clarsimp simp: dvd_def field_simps)

definition (in fx0) find_mu :: "'a state \<Rightarrow> 'a state" where
  "find_mu \<equiv>
    (\<lambda>s. s\<lparr> m := 0, tortoise := x0 \<rparr>) ;;
    while (hare \<^bold>\<noteq> tortoise)
          (\<lambda>s. s\<lparr> tortoise := f (tortoise s), hare := f (hare s), m := m s + 1 \<rparr>)"

lemma find_mu:
  "\<lbrace>nu \<^bold>\<in> \<langle>{0<..lambda + mu}\<rangle> \<^bold>\<and> seq \<circ> (nu \<^bold>+ nu) \<^bold>= seq \<circ> nu \<^bold>\<and> hare \<^bold>= seq \<circ> nu\<rbrace>
     find_mu
   \<lbrace>nu \<^bold>\<in> \<langle>{0<..lambda + mu}\<rangle> \<^bold>\<and> tortoise \<^bold>= \<langle>seq mu\<rangle> \<^bold>\<and> m \<^bold>= \<langle>mu\<rangle>\<rbrace>"
apply (simp add: find_mu_def)
apply (rule hoare_pre)
 apply (rule whileI[where I="nu \<^bold>\<in> \<langle>{0<..lambda + mu}\<rangle> \<^bold>\<and> seq \<circ> (nu \<^bold>+ nu) \<^bold>= seq \<circ> nu \<^bold>\<and> m \<^bold>\<le> \<langle>mu\<rangle>
                           \<^bold>\<and> tortoise \<^bold>= seq \<circ> m \<^bold>\<and> hare \<^bold>= seq \<circ> (m \<^bold>+ nu)"
                      and r="measure (\<langle>mu\<rangle> \<^bold>- m)"]
             wp_intro)+
    using properties_loops_ge_mu
    apply (force dest: mu_nu simp: less_eq_Suc_le[symmetric])
   apply simp
  apply (force dest: mu_nu simp: le_eq_less_or_eq)
 apply (rule wp_intro)
apply simp
done


subsection\<open> Finding \<open>lambda\<close> \<close>

text\<open>

With the Tortoise parked at @{term "mu"}, we find \<open>lambda\<close> by
walking the Hare around the loop.

\<close>

definition (in fx0) find_lambda :: "'a state \<Rightarrow> 'a state" where
  "find_lambda \<equiv>
    (\<lambda>s. s\<lparr> l := 1, hare := f (tortoise s) \<rparr>) ;;
    while (hare \<^bold>\<noteq> tortoise)
          (\<lambda>s. s\<lparr> hare := f (hare s), l := l s + 1 \<rparr>)"

lemma find_lambda:
  "\<lbrace>nu \<^bold>\<in> \<langle>{0<..lambda + mu}\<rangle> \<^bold>\<and> tortoise \<^bold>= \<langle>seq mu\<rangle> \<^bold>\<and> m \<^bold>= \<langle>mu\<rangle>\<rbrace>
     find_lambda
   \<lbrace>nu \<^bold>\<in> \<langle>{0<..lambda + mu}\<rangle> \<^bold>\<and> l \<^bold>= \<langle>lambda\<rangle> \<^bold>\<and> m \<^bold>= \<langle>mu\<rangle>\<rbrace>"
apply (simp add: find_lambda_def)
apply (rule hoare_pre)
 apply (rule whileI[where I="nu \<^bold>\<in> \<langle>{0<..lambda + mu}\<rangle> \<^bold>\<and> l \<^bold>\<in> \<langle>{0<..lambda}\<rangle>
                           \<^bold>\<and> tortoise \<^bold>= \<langle>seq mu\<rangle> \<^bold>\<and> hare \<^bold>= seq \<circ> (\<langle>mu\<rangle> \<^bold>+ l) \<^bold>\<and> m \<^bold>= \<langle>mu\<rangle>"
                      and r="measure (\<langle>lambda\<rangle> \<^bold>- l)"]
             wp_intro)+
    using properties_lambda_gt_0 properties_mod_lambda[where i="mu + lambda"] properties_distinct[where i=mu]
    apply (fastforce simp: less_eq_Suc_le[symmetric])
   apply simp
  using properties_mod_lambda[where i="mu + lambda"]
  apply (fastforce simp: le_eq_less_or_eq)
 apply (rule wp_intro)
using properties_lambda_gt_0
apply simp
done


subsection\<open> Top level \<close>

text\<open>

The complete program is simply the steps composed in order.

\<close>

definition (in fx0) tortoise_hare :: "'a state \<Rightarrow> 'a state" where
  "tortoise_hare \<equiv> find_nu ;; find_mu ;; find_lambda"

theorem tortoise_hare:
  "\<lbrace>\<langle>True\<rangle>\<rbrace> tortoise_hare \<lbrace>nu \<^bold>\<in> \<langle>{0<..lambda + mu}\<rangle> \<^bold>\<and> l \<^bold>= \<langle>lambda\<rangle> \<^bold>\<and> m \<^bold>= \<langle>mu\<rangle>\<rbrace>"
unfolding tortoise_hare_def
by (rule find_nu find_mu find_lambda wp_intro)+

end

corollary tortoise_hare_correct:
  assumes s': "s' = fx0.tortoise_hare f x arbitrary"
  shows "fx0.properties f x (l s') (m s')"
using assms properties.tortoise_hare[where f=f and ?x0.0=x]
by (fastforce intro: fx0.properties_existence[where f=f and ?x0.0=x]
               simp:  Basis.properties_def valid_def)

text\<open>

Isabelle can generate code from these definitions.

\<close>

schematic_goal tortoise_hare_code[code]:
  "fx0.tortoise_hare f x = ?code"
unfolding fx0.tortoise_hare_def fx0.find_nu_def fx0.find_mu_def fx0.find_lambda_def fcomp_assoc[symmetric] fcomp_comp
by (rule refl)

export_code fx0.tortoise_hare in SML
(*<*)

end
(*>*)
