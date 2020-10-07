(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Eager Unfolding Optimisation\<close>

theory LTL_Rabin_Unfold_Opt
  imports Main LTL_Rabin
begin

subsection \<open>Preliminary Facts\<close>

lemma finite_reach_af_opt:
  "finite (reach \<Sigma> \<up>af\<^sub>\<UU> (Abs \<phi>))"
proof (cases "\<Sigma> \<noteq> {}")
  case True
    thus ?thesis
      using af_abs_opt.finite_abs_reach unfolding af_abs_opt.abs_reach_def reach_foldl_def[OF True]
      using finite_subset[of "{foldl \<up>af\<^sub>\<UU> (Abs \<phi>) w |w. set w \<subseteq> \<Sigma>}" "{foldl \<up>af\<^sub>\<UU> (Abs \<phi>) w |w. True}"] 
      unfolding af_letter_abs_opt_def
      by blast
qed (simp add: reach_def)

lemma finite_reach_af_G_opt:
  "finite (reach \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs \<phi>))"
proof (cases "\<Sigma> \<noteq> {}")
  case True
    thus ?thesis
      using af_G_abs_opt.finite_abs_reach unfolding af_G_abs_opt.abs_reach_def reach_foldl_def[OF True]
      using finite_subset[of "{foldl \<up>af\<^sub>G\<^sub>\<UU> (Abs \<phi>) w |w. set w \<subseteq> \<Sigma>}" "{foldl \<up>af\<^sub>G\<^sub>\<UU> (Abs \<phi>) w |w. True}"] 
      unfolding af_G_letter_abs_opt_def
      by blast
qed (simp add: reach_def)

lemma wellformed_mojmir_opt:
  assumes "Only_G \<G>"
  assumes "finite \<Sigma>"
  assumes "range w \<subseteq> \<Sigma>"
  shows "mojmir \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs \<phi>) w {q. \<G> \<Turnstile>\<^sub>P Rep q}"
proof -
  have "\<forall>q \<nu>. q \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q} \<longrightarrow> af_G_letter_abs_opt q \<nu> \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}"
    using \<open>Only_G \<G>\<close> af_G_letter_opt_sat_core_lifted by auto
  thus "?thesis"
    using finite_reach_af_G_opt assms by (unfold_locales; auto)
qed

locale ltl_FG_to_rabin_opt_def = 
  fixes 
    \<Sigma> :: "'a set set"
  fixes
    \<phi> :: "'a ltl"
  fixes
    \<G> :: "'a ltl set"
  fixes 
    w :: "'a set word"
begin

sublocale mojmir_to_rabin_def \<Sigma> "\<up>af\<^sub>G\<^sub>\<UU>" "Abs (Unf\<^sub>G \<phi>)" w "{q. \<G> \<Turnstile>\<^sub>P Rep q}" .

end

locale ltl_FG_to_rabin_opt = ltl_FG_to_rabin_opt_def +
  assumes 
    wellformed_\<G>: "Only_G \<G>"
  assumes
    bounded_w: "range w \<subseteq> \<Sigma>"
  assumes
    finite_\<Sigma>: "finite \<Sigma>"
begin
  
sublocale mojmir_to_rabin \<Sigma> "\<up>af\<^sub>G\<^sub>\<UU>" "Abs (Unf\<^sub>G \<phi>)" w "{q. \<G> \<Turnstile>\<^sub>P Rep q}"
proof
  show "\<And>q \<nu>. q \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q} \<Longrightarrow> \<up>af\<^sub>G\<^sub>\<UU> q \<nu> \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}"
    using wellformed_\<G> af_G_letter_opt_sat_core_lifted by auto
  have nonempty_\<Sigma>: "\<Sigma> \<noteq> {}"
    using bounded_w by blast
  show "finite (reach \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G \<phi>)))" (is "finite ?A")
    using finite_reach_af_G_opt wellformed_\<G> by blast
qed (insert finite_\<Sigma> bounded_w)

end

subsection \<open>Equivalences between the standard and the eager Mojmir construction\<close>

context
  fixes 
    \<Sigma> :: "'a set set"
  fixes 
    \<phi> :: "'a ltl"
  fixes
    \<G> :: "'a ltl set"
  fixes
    w :: "'a set word"
  assumes 
    context_assms: "Only_G \<G>" "finite \<Sigma>" "range w \<subseteq> \<Sigma>"
begin

\<comment> \<open>Create an interpretation of the mojmir locale for the standard construction\<close>
interpretation \<MM>: ltl_FG_to_rabin \<Sigma> \<phi> \<G> w
  by (unfold_locales; insert context_assms; auto)

\<comment> \<open>Create an interpretation of the mojmir locale for the optimised construction\<close>
interpretation \<UU>: ltl_FG_to_rabin_opt \<Sigma> \<phi> \<G> w
  by (unfold_locales; insert context_assms; auto)

lemma unfold_token_run_eq:
  assumes "x \<le> n"
  shows "\<MM>.token_run x (Suc n) = \<up>step (\<UU>.token_run x n) (w n)" 
  (is "?lhs = ?rhs")
proof -
  have "x + (n - x) = n" and "x + (Suc n - x) = Suc n"
   using assms by arith+
  have "w [x \<rightarrow> Suc n] = w [x \<rightarrow> n] @ [w n]"
    unfolding upt_Suc subsequence_def using assms by simp

  have "af\<^sub>G \<phi> (w [x \<rightarrow> Suc n]) = step (af\<^sub>G\<^sub>\<UU> (Unf\<^sub>G \<phi>) (w [x \<rightarrow> n])) (w n)" (is "?l = ?r")
    unfolding af_to_af_opt[symmetric] \<open>w [x \<rightarrow> Suc n] = w [x \<rightarrow> n] @ [w n]\<close> foldl_append
    using af_letter_alt_def by auto
  moreover
  have "?lhs = Abs ?l"
    unfolding \<MM>.token_run.simps run_foldl 
    using subsequence_shift \<open>x + (Suc n - x) = Suc n\<close> Nat.add_0_right subsequence_def 
    by (metis af_G_abs.f_foldl_abs_alt_def af_G_abs.f_foldl_abs.abs_eq af_G_letter_abs_def) 
  moreover
  have "Abs ?r = ?rhs"
    unfolding \<UU>.token_run.simps run_foldl subsequence_def[symmetric]
    unfolding subsequence_shift \<open>x + (n - x) = n\<close> Nat.add_0_right af_G_letter_abs_opt_def
    unfolding af_G_abs_opt.f_foldl_abs_alt_def[unfolded af_G_abs_opt.f_foldl_abs.abs_eq, symmetric]  
    by (simp add: step_abs.abs_eq)
  ultimately
  show "?lhs = ?rhs"
    by presburger
qed

lemma unfold_token_succeeds_eq:
  "\<MM>.token_succeeds x = \<UU>.token_succeeds x"
proof 
  assume "\<MM>.token_succeeds x"

  then obtain n where "\<And>m. m > n \<Longrightarrow> \<MM>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}" 
    unfolding \<MM>.token_succeeds_alt_def MOST_nat by blast
  then obtain n where "\<MM>.token_run x (Suc n) \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}" and "x \<le> n" 
    by (cases "x \<le> n") auto

  hence 1: "\<G> \<Turnstile>\<^sub>P Rep (step_abs (\<UU>.token_run x n) (w n))"
    using unfold_token_run_eq by fastforce
  moreover
  have "Suc n - x = Suc (n - x)" and "x + (n - x) = n"
    using \<open>x \<le> n\<close> by arith+
  ultimately
  have "\<UU>.token_run x (Suc n) = Unf\<^sub>G_abs (step_abs (\<UU>.token_run x n) (w n))"
    unfolding af_G_letter_abs_opt_split by simp
  
  hence "\<G> \<Turnstile>\<^sub>P Rep (\<UU>.token_run x (Suc n))"
    using 1 Unf\<^sub>G_\<G>[OF \<open>Only_G \<G>\<close>] by (simp add: Rep_Abs_equiv Unf\<^sub>G_abs_def)
  thus "\<UU>.token_succeeds x"
    unfolding \<UU>.token_succeeds_def by blast
next
  assume "\<UU>.token_succeeds x"

  then obtain n where "\<And>m. m > n \<Longrightarrow> \<UU>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}" 
    unfolding \<UU>.token_succeeds_alt_def MOST_nat by blast
  then obtain n where "\<UU>.token_run x n \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}" and "x \<le> n"
    by (cases "x \<le> n") (fastforce, auto)

  hence "\<G> \<Turnstile>\<^sub>P Rep (step_abs (\<UU>.token_run x n) (w n))"
    using step_\<G>[OF \<open>Only_G \<G>\<close>] Rep_step[unfolded ltl_prop_equiv_def] by blast
  thus "\<MM>.token_succeeds x"
    unfolding \<MM>.token_succeeds_def unfold_token_run_eq[OF \<open>x \<le> n\<close>, symmetric] by blast
qed    

lemma unfold_accept_eq:
  "\<MM>.accept = \<UU>.accept"
  unfolding \<MM>.accept_def \<UU>.accept_def MOST_nat_le unfold_token_succeeds_eq ..

lemma unfold_\<S>_eq:
  assumes "\<MM>.accept"
  shows "\<forall>\<^sub>\<infinity>n. \<MM>.\<S> (Suc n) = (\<lambda>q. step_abs q (w n)) ` (\<UU>.\<S> n) \<union> {Abs \<phi>} \<union> {q. \<G> \<Turnstile>\<^sub>P Rep q}"
proof -
  \<comment> \<open>Obtain lower bounds for proof\<close>
  obtain i\<^sub>\<MM> where i\<^sub>\<MM>_def: "\<MM>.smallest_accepting_rank = Some i\<^sub>\<MM>"
    using assms unfolding \<MM>.smallest_accepting_rank_def by simp
  obtain n\<^sub>\<MM> where n\<^sub>\<MM>_def: "\<And>x m. m \<ge> n\<^sub>\<MM> \<Longrightarrow> \<MM>.token_succeeds x = (m < x \<or> (\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.rank x m = Some j) \<or> \<MM>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q})"
    using \<MM>.token_smallest_accepting_rank[OF i\<^sub>\<MM>_def] unfolding MOST_nat_le by metis

  have "\<UU>.accept"
    using assms unfold_accept_eq by simp
  obtain i\<^sub>\<UU> where i\<^sub>\<UU>_def: "\<UU>.smallest_accepting_rank = Some i\<^sub>\<UU>"
    using \<open>\<UU>.accept\<close> unfolding \<UU>.smallest_accepting_rank_def by simp
  obtain n\<^sub>\<UU> where n\<^sub>\<UU>_def: "\<And>x m. m \<ge> n\<^sub>\<UU> \<Longrightarrow> \<UU>.token_succeeds x = (m < x \<or> (\<exists>j\<ge>i\<^sub>\<UU>. \<UU>.rank x m = Some j) \<or> \<UU>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q})"
    using \<UU>.token_smallest_accepting_rank[OF i\<^sub>\<UU>_def] unfolding MOST_nat_le by metis
  
  show ?thesis
  proof (unfold MOST_nat_le, rule, rule, rule)
    fix m 
    assume "m \<ge> max n\<^sub>\<MM> n\<^sub>\<UU>"
    hence "m \<ge> n\<^sub>\<MM>" and "m \<ge> n\<^sub>\<UU>" and "Suc m \<ge> n\<^sub>\<MM>" 
      by simp+
    \<comment> \<open>Using the properties of @{term n\<^sub>\<MM>} and @{term n\<^sub>\<UU>} and the lemma @{thm unfold_token_succeeds_eq}, 
       we prove that the behaviour of x in @{text \<MM>} and @{text \<UU>} is similar in regards to 
       creation time, accepting rank or final states.\<close>
    hence token_trans: "\<And>x. Suc m < x \<or> (\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.rank x (Suc m) = Some j) \<or> \<MM>.token_run x (Suc m) \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}
      \<longleftrightarrow> m < x \<or> (\<exists>j\<ge>i\<^sub>\<UU>. \<UU>.rank x m = Some j) \<or> \<UU>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}"
      using n\<^sub>\<MM>_def n\<^sub>\<UU>_def unfolding unfold_token_succeeds_eq by presburger

    show "\<MM>.\<S> (Suc m) = (\<lambda>q. step_abs q (w m)) ` (\<UU>.\<S> m) \<union> {Abs \<phi>} \<union> {q. \<G> \<Turnstile>\<^sub>P Rep q}" (is "?lhs = ?rhs")
    proof 
      {
        fix q assume "\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.state_rank q (Suc m) = Some j"
        moreover
        then obtain x where q_def: "q = \<MM>.token_run x (Suc m)" and "x \<le> Suc m"
           using \<MM>.push_down_state_rank_tokens by fastforce
        ultimately
        have "\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.rank x (Suc m) = Some j"
          using \<MM>.rank_eq_state_rank by metis
        hence token_cases: "(\<exists>j\<ge>i\<^sub>\<UU>. \<UU>.rank x m = Some j) \<or> \<UU>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q} \<or> x = Suc m"
          using token_trans[of x] \<MM>.rank_Some_time by fastforce
        have "q \<in> ?rhs"
        proof (cases "x \<noteq> Suc m")
          case True
            hence "x \<le> m"
              using \<open>x \<le> Suc m\<close> by arith
            have "\<UU>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q} \<Longrightarrow> \<G> \<Turnstile>\<^sub>P Rep q"
              unfolding \<open>q = \<MM>.token_run x (Suc m)\<close> unfold_token_run_eq[OF \<open>x \<le> m\<close>]
              using Rep_step[unfolded ltl_prop_equiv_def] step_\<G>[OF \<open>Only_G \<G>\<close>] by blast
            moreover
            {
              assume "\<exists>j \<ge> i\<^sub>\<UU>. \<UU>.rank x m = Some j"
              moreover
              define q' where "q' = \<UU>.token_run x m"
              ultimately
              have "\<exists>j \<ge> i\<^sub>\<UU>. \<UU>.state_rank q' m = Some j"
                unfolding \<UU>.rank_eq_state_rank[OF \<open>x \<le> m\<close>] q'_def by blast
              hence "q' \<in> \<UU>.\<S> m"
                using assms i\<^sub>\<UU>_def by simp
              moreover
              have "q = step_abs q' (w m)"
                unfolding q_def q'_def unfold_token_run_eq[OF \<open>x \<le> m\<close>] ..
              ultimately
              have "q \<in> (\<lambda>q. step_abs q (w m)) ` (\<UU>.\<S> m)"
                by blast
            }
            ultimately
            show ?thesis 
              using token_cases True by blast
        qed (simp add: q_def)
      }
      thus "?lhs \<subseteq> ?rhs"   
        unfolding \<MM>.\<S>.simps i\<^sub>\<MM>_def option.sel by blast
    next   
      {
        fix q
        assume "q \<in> (\<lambda>q. step_abs q (w m)) ` (\<UU>.\<S> m)"
        then obtain q' where q_def: "q = step_abs q' (w m)" and "q' \<in> \<UU>.\<S> m"
          by blast
        hence "q \<in> ?lhs"
        proof (cases "\<G> \<Turnstile>\<^sub>P Rep q'")
          case False
            hence "\<exists>j \<ge> i\<^sub>\<UU>. \<UU>.state_rank q' m = Some j"
              using \<open>q' \<in> \<UU>.\<S> m\<close> unfolding \<UU>.\<S>.simps i\<^sub>\<UU>_def option.sel by blast
            moreover
            then obtain x where q'_def: "q' = \<UU>.token_run x m" and "x \<le> m" and "x \<le> Suc m"
              using \<UU>.push_down_state_rank_tokens by force
            ultimately
            have "\<exists>j \<ge> i\<^sub>\<UU>. \<UU>.rank x m = Some j" 
              unfolding \<UU>.rank_eq_state_rank[OF \<open>x \<le> m\<close>] q'_def by blast
            hence "(\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.rank x (Suc m) = Some j) \<or> \<MM>.token_run x (Suc m) \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}"
              using token_trans[of x] \<UU>.rank_Some_time by fastforce
            moreover
            have "\<MM>.token_run x (Suc m) = q"
              unfolding q_def q'_def unfold_token_run_eq[OF \<open>x \<le> m\<close>] ..
            ultimately
            have "(\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.state_rank q (Suc m) = Some j) \<or> q \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}"
              using \<MM>.rank_eq_state_rank[OF \<open>x \<le> Suc m\<close>] by metis
            thus ?thesis
              unfolding \<MM>.\<S>.simps option.sel i\<^sub>\<MM>_def by blast
        qed (insert step_\<G>[OF \<open>Only_G \<G>\<close>, of "Rep q'"], unfold q_def Rep_step[unfolded ltl_prop_equiv_def, rule_format, symmetric], auto)
      }
      moreover
      have "(\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.rank (Suc m) (Suc m) = Some j) \<or> \<G> \<Turnstile>\<^sub>P Rep (Abs \<phi>)" 
        using token_trans[of "Suc m"] by simp
      hence "Abs \<phi> \<in> ?lhs"
        using i\<^sub>\<MM>_def \<MM>.rank_eq_state_rank[OF order_refl] by (cases "\<G> \<Turnstile>\<^sub>P Rep (Abs \<phi>)") simp+
      ultimately
      show "?lhs \<supseteq> ?rhs"   
        unfolding \<MM>.\<S>.simps by blast
    qed
  qed
qed

end

subsection \<open>Automaton Definition\<close>

fun M\<^sub>\<UU>_fin :: "('a ltl \<rightharpoonup> nat) \<Rightarrow> ('a ltl\<^sub>P \<times> ('a ltl \<rightharpoonup> 'a ltl\<^sub>P \<rightharpoonup> nat), 'a set) transition set"
where
  "M\<^sub>\<UU>_fin \<pi> = {((\<phi>', m), \<nu>, p). \<not>(\<forall>S. (\<forall>\<chi> \<in> (dom \<pi>). S \<up>\<Turnstile>\<^sub>P Abs \<chi> \<and> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) (Abs (theG \<chi>)) \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi> \<chi>). the (m \<chi>) q = Some j) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) (\<up>step q \<nu>))) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P (\<up>step \<phi>' \<nu>))}"

locale ltl_to_rabin_af_unf = ltl_to_rabin_base "\<up>af\<^sub>\<UU>" "\<up>af\<^sub>G\<^sub>\<UU>" "Abs o Unf" "Abs o Unf\<^sub>G" M\<^sub>\<UU>_fin begin

abbreviation "\<delta>\<^sub>\<UU> \<equiv> delta"
abbreviation "\<iota>\<^sub>\<UU> \<equiv> initial"
abbreviation "Acc\<^sub>\<UU>_fin \<equiv> Acc_fin"
abbreviation "Acc\<^sub>\<UU>_inf \<equiv> Acc_inf"
abbreviation "F\<^sub>\<UU> \<equiv> rabin_pairs"
abbreviation "Acc\<^sub>\<UU> \<equiv> Acc" 
abbreviation "\<A>\<^sub>\<UU> \<equiv> ltl_to_generalized_rabin"

subsection \<open>Properties\<close>

subsection \<open>Correctness Theorem\<close>

lemma unfold_optimisation_correct_M:
  assumes "dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>"
  assumes "dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>"
  assumes "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> \<pi>\<^sub>\<A> \<chi> = mojmir_def.smallest_accepting_rank \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<up>\<Turnstile>\<^sub>P q}"
  assumes "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<UU> \<Longrightarrow> \<pi>\<^sub>\<UU> \<chi> = mojmir_def.smallest_accepting_rank \<Sigma> af_G_letter_abs_opt (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi>\<^sub>\<UU> \<up>\<Turnstile>\<^sub>P q}"
  shows "accepting_pair\<^sub>R (ltl_to_rabin_af.\<delta>\<^sub>\<A> \<Sigma>) (ltl_to_rabin_af.\<iota>\<^sub>\<A> \<phi>) (M_fin \<pi>\<^sub>\<A>, UNIV) w \<longleftrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU>, UNIV) w"
proof -
  \<comment> \<open>Preliminary Facts\<close>
  note \<G>_properties[OF \<open>dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>\<close>]

  interpret \<A>: ltl_to_rabin_af
    using ltl_to_generalized_rabin_af_wellformed bounded_w finite_\<Sigma> by auto

  \<comment> \<open>Define constants for both runs\<close>
  define r\<^sub>\<A> r\<^sub>\<UU>
    where "r\<^sub>\<A> = run\<^sub>t (ltl_to_rabin_af.\<delta>\<^sub>\<A> \<Sigma>) (ltl_to_rabin_af.\<iota>\<^sub>\<A> \<phi>) w"
      and "r\<^sub>\<UU> = run\<^sub>t (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) w"
  hence "finite (range r\<^sub>\<A>)" and "finite (range r\<^sub>\<UU>)"
    using run\<^sub>t_finite[OF \<A>.finite_reach] run\<^sub>t_finite[OF finite_reach] bounded_w finite_\<Sigma> by simp+

  \<comment> \<open>Prove that the limit of both runs behave the same in respect to the M acceptance condition\<close>
  have "limit r\<^sub>\<A> \<inter> M_fin \<pi>\<^sub>\<A> = {} \<longleftrightarrow> limit r\<^sub>\<UU> \<inter> M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU> = {}"
  proof -
    have "ltl_FG_to_rabin \<Sigma> (dom \<pi>\<^sub>\<A>) w"
      by (unfold_locales; insert \<G>_elements[OF \<open>dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>\<close>] finite_\<Sigma> bounded_w) 
    hence X: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> mojmir_def.accept \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
      by (metis assms(3)[unfolded ltl_prop_entails_abs.rep_eq] ltl_FG_to_rabin.smallest_accepting_rank_properties(1) domD)
    have "\<forall>\<^sub>\<infinity>i. \<forall>\<chi> \<in> dom \<pi>\<^sub>\<A>. mojmir_def.\<S> \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q} (Suc i)
       = (\<lambda>q. step_abs q (w i)) ` (mojmir_def.\<S> \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q} i) \<union> {Abs (theG \<chi>)} \<union> {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
      using almost_all_commutative'[OF \<open>finite (dom \<pi>\<^sub>\<A>)\<close>] X unfold_\<S>_eq[OF \<open>Only_G (dom \<pi>\<^sub>\<A>)\<close>] finite_\<Sigma> bounded_w by simp
    
    then obtain i where i_def: "\<And>j \<chi>. j \<ge> i \<Longrightarrow> \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> mojmir_def.\<S> \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q} (Suc j)
       = (\<lambda>q. step_abs q (w j)) ` (mojmir_def.\<S> \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q} j) \<union> {Abs (theG \<chi>)} \<union> {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
       unfolding MOST_nat_le by blast

    obtain j where "limit r\<^sub>\<A> = range (suffix j r\<^sub>\<A>)"
      and "limit r\<^sub>\<UU> = range (suffix j r\<^sub>\<UU>)"
      using \<open>finite (range r\<^sub>\<A>)\<close> \<open>finite (range r\<^sub>\<UU>)\<close> 
      by (rule common_range_limit)
    hence "limit r\<^sub>\<A> = range (suffix (j + i + 1) r\<^sub>\<A>)"
      and "limit r\<^sub>\<UU> = range (suffix (j + i) r\<^sub>\<UU>)"
      by (meson le_add1 limit_range_suffix_incr)+
    moreover
    have "\<And>j. j \<ge> i \<Longrightarrow> r\<^sub>\<A> (Suc j) \<in> M_fin \<pi>\<^sub>\<A> \<longleftrightarrow> r\<^sub>\<UU> j \<in> M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU>"
    proof -
      fix j
      assume "j \<ge> i"
       
      obtain \<phi>\<^sub>\<A> m\<^sub>\<A> x where r\<^sub>\<A>_def': "r\<^sub>\<A> (Suc j) = ((\<phi>\<^sub>\<A>, m\<^sub>\<A>), w (Suc j), x)"
        unfolding r\<^sub>\<A>_def run\<^sub>t.simps using prod.exhaust by fastforce

      obtain \<phi>\<^sub>\<UU> m\<^sub>\<UU> y where r\<^sub>\<UU>_def': "r\<^sub>\<UU> j = ((\<phi>\<^sub>\<UU>, m\<^sub>\<UU>), w j, y)"
        unfolding r\<^sub>\<UU>_def run\<^sub>t.simps using prod.exhaust by fastforce

      have m\<^sub>\<A>_def: "\<And>\<chi> q. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> the (m\<^sub>\<A> \<chi>) q = semi_mojmir_def.state_rank \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w q (Suc j)"
        using \<A>.run_properties(2)[of _ \<phi> "Suc j"] r\<^sub>\<A>_def'[unfolded r\<^sub>\<A>_def] prod.sel  by simp

      have m\<^sub>\<UU>_def: "\<And>\<chi> q. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> the (m\<^sub>\<UU> \<chi>) q = semi_mojmir_def.state_rank \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G (theG \<chi>))) w q j"
        using run_properties(2)[of _ \<phi> j] r\<^sub>\<UU>_def'[unfolded r\<^sub>\<UU>_def] prod.sel by simp

      {
        have upt_Suc_0: "[0..<Suc j] = [0..<j] @ [j]"
          by simp
        have "Rep (fst (fst (r\<^sub>\<A> (Suc j)))) \<equiv>\<^sub>P step (Rep (fst (fst (r\<^sub>\<UU> j)))) (w j)"
          unfolding r\<^sub>\<A>_def r\<^sub>\<UU>_def run\<^sub>t.simps fst_conv \<A>.run_properties(1)[of \<phi> "Suc j"] run_properties(1) comp_apply 
          unfolding subsequence_def upt_Suc_0 map_append map_def list.map af_abs_equiv Unf_abs.abs_eq using Rep_step by auto
        hence A: "\<And>S. S \<Turnstile>\<^sub>P Rep \<phi>\<^sub>\<A> \<longleftrightarrow> S \<Turnstile>\<^sub>P step (Rep \<phi>\<^sub>\<UU>) (w j)"
          unfolding r\<^sub>\<A>_def' r\<^sub>\<UU>_def' prod.sel ltl_prop_equiv_def ..
        
        {
          fix S assume "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> S \<Turnstile>\<^sub>P \<chi>"
          hence "dom \<pi>\<^sub>\<A> \<subseteq> S"
            using \<open>Only_G (dom \<pi>\<^sub>\<A>)\<close> assms by (metis ltl_prop_entailment.simps(8) subsetI)
          {
            fix \<chi> assume "\<chi> \<in> dom \<pi>\<^sub>\<A>"
          

            interpret \<MM>: ltl_FG_to_rabin \<Sigma> "theG \<chi>" "dom \<pi>\<^sub>\<A>" 
              by (unfold_locales, insert \<open>Only_G (dom \<pi>\<^sub>\<A>)\<close> bounded_w finite_\<Sigma>)
            interpret \<UU>: ltl_FG_to_rabin_opt \<Sigma> "theG \<chi>" "dom \<pi>\<^sub>\<A>"
              by (unfold_locales, insert \<open>Only_G (dom \<pi>\<^sub>\<A>)\<close> bounded_w finite_\<Sigma>)
  
            have "\<And>q \<nu>. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q \<Longrightarrow> dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep (step_abs q \<nu>)"
              using \<open>Only_G (dom \<pi>\<^sub>\<A>)\<close> by (metis ltl_prop_equiv_def Rep_step step_\<G>) 
            then have subsetStep: "\<And>\<nu>. (\<lambda>q. step_abs q \<nu>) ` {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q} \<subseteq> {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
              by auto
               
            let ?P = "\<lambda>q. S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (Rep q)"
            have "\<And>q \<nu>. (dom \<pi>\<^sub>\<A>) \<Turnstile>\<^sub>P Rep q \<Longrightarrow> ?P q"
              using \<open>Only_G (dom \<pi>\<^sub>\<A>)\<close> eval\<^sub>G_prop_entailment \<open>(dom \<pi>\<^sub>\<A>) \<subseteq> S\<close> by blast 
            hence "\<And>q. q \<in> {q. (dom \<pi>\<^sub>\<A>) \<Turnstile>\<^sub>P Rep q} \<Longrightarrow> ?P q"
              by simp
            moreover
            have Y: "\<MM>.\<S> (Suc j) = (\<lambda>q. step_abs q (w j)) ` (\<UU>.\<S> j) \<union> {Abs (theG \<chi>)} \<union> {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
              using i_def[OF \<open>j \<ge> i\<close> \<open>\<chi> \<in> dom \<pi>\<^sub>\<A>\<close>] by simp
            
            have 1: "\<MM>.smallest_accepting_rank = (\<pi>\<^sub>\<A> \<chi>)"
              and 2: "\<UU>.smallest_accepting_rank = (\<pi>\<^sub>\<UU> \<chi>)"
              and 3: "\<chi> \<in> \<^bold>G \<phi>"
              using \<open>\<chi> \<in> dom \<pi>\<^sub>\<A>\<close> assms[unfolded ltl_prop_entails_abs.rep_eq] by auto
            ultimately
            have "(\<forall>q \<in> \<MM>.\<S> (Suc j). ?P q) = (\<forall>q \<in> (\<lambda>q. step_abs q (w j)) ` (\<UU>.\<S> j) \<union> {Abs (theG \<chi>)}. ?P q)"
              unfolding Y by blast
            hence 4: "(\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<A> \<chi>). the (m\<^sub>\<A> \<chi>) q = Some j) \<longrightarrow> ?P q) = ((\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<UU> \<chi>). the (m\<^sub>\<UU> \<chi>) q = Some j) \<longrightarrow> ?P (step_abs q (w j))) \<and> ?P (Abs (theG \<chi>)))"
              using \<open>\<And>q. q \<in> {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q} \<Longrightarrow> ?P q\<close> subsetStep
              unfolding m\<^sub>\<A>_def[OF 3, symmetric] m\<^sub>\<UU>_def[OF 3, symmetric] \<MM>.\<S>.simps \<UU>.\<S>.simps 1 2 Set.image_Un option.sel by blast
            have "S \<Turnstile>\<^sub>P \<chi> \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<A> \<chi>). the (m\<^sub>\<A> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (Rep q)) \<longleftrightarrow>
              S \<Turnstile>\<^sub>P \<chi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (theG \<chi>) \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<UU> \<chi>). the (m\<^sub>\<UU> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (step (Rep q) (w j)))"
              unfolding 4 using eval\<^sub>G_respectfulness(2)[OF Rep_Abs_equiv, unfolded ltl_prop_equiv_def]
              using eval\<^sub>G_respectfulness(2)[OF Rep_step, unfolded ltl_prop_equiv_def] by blast
          }
          hence "((\<forall>\<chi> \<in> dom \<pi>\<^sub>\<A>. S \<Turnstile>\<^sub>P \<chi> \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<A> \<chi>). the (m\<^sub>\<A> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (Rep q))) \<longrightarrow> S \<Turnstile>\<^sub>P Rep \<phi>\<^sub>\<A>)
            \<longleftrightarrow> ((\<forall>\<chi> \<in> dom \<pi>\<^sub>\<UU>. S \<Turnstile>\<^sub>P \<chi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<UU>) (theG \<chi>) \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<UU> \<chi>). the (m\<^sub>\<UU> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<UU>) (step (Rep q) (w j)))) \<longrightarrow> S \<Turnstile>\<^sub>P step (Rep \<phi>\<^sub>\<UU>) (w j))"
            by (simp add: \<open>\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> (S \<Turnstile>\<^sub>P \<chi> \<and> (\<forall>q. (\<exists>j\<ge>the (\<pi>\<^sub>\<A> \<chi>). the (m\<^sub>\<A> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (Rep q))) = (S \<Turnstile>\<^sub>P \<chi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (theG \<chi>) \<and> (\<forall>q. (\<exists>j\<ge>the (\<pi>\<^sub>\<UU> \<chi>). the (m\<^sub>\<UU> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (step (Rep q) (w j))))\<close> A assms(2))
        }
        hence "(\<forall>S. (\<forall>\<chi> \<in> dom \<pi>\<^sub>\<A>. S \<Turnstile>\<^sub>P \<chi> \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<A> \<chi>). the (m\<^sub>\<A> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (Rep q))) \<longrightarrow> S \<Turnstile>\<^sub>P Rep \<phi>\<^sub>\<A>) \<longleftrightarrow> 
        (\<forall>S. (\<forall>\<chi> \<in> dom \<pi>\<^sub>\<UU>. S \<Turnstile>\<^sub>P \<chi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<UU>) (theG \<chi>) \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<UU> \<chi>). the (m\<^sub>\<UU> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<UU>) (step (Rep q) (w j)))) \<longrightarrow> S \<Turnstile>\<^sub>P step (Rep \<phi>\<^sub>\<UU>) (w j))"
          unfolding assms by auto
      }
      hence "((\<phi>\<^sub>\<A>, m\<^sub>\<A>), w (Suc j), x) \<in> M_fin \<pi>\<^sub>\<A> \<longleftrightarrow> ((\<phi>\<^sub>\<UU>, m\<^sub>\<UU>), w j, y) \<in> M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU>"
        unfolding M_fin.simps M\<^sub>\<UU>_fin.simps ltl_prop_entails_abs.abs_eq[symmetric] eval\<^sub>G_abs.abs_eq[symmetric] ltl\<^sub>P_abs_rep step_abs.abs_eq[symmetric] by blast
      thus "?thesis j" 
        unfolding r\<^sub>\<A>_def' r\<^sub>\<UU>_def' .
    qed 
    hence "\<And>n. r\<^sub>\<A> (j + i + 1 + n) \<in> M_fin \<pi>\<^sub>\<A> \<longleftrightarrow> r\<^sub>\<UU> (j + i + n) \<in> M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU>"
      by simp
    hence "range (suffix (j + i + 1) r\<^sub>\<A>) \<inter> M_fin \<pi>\<^sub>\<A> = {} \<longleftrightarrow> range (suffix (j + i) r\<^sub>\<UU>) \<inter> M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU> = {}"
      unfolding suffix_def by blast
    ultimately
    show "limit r\<^sub>\<A> \<inter> M_fin \<pi>\<^sub>\<A> = {} \<longleftrightarrow> limit r\<^sub>\<UU> \<inter> M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU> = {}"
      by force
  qed
  moreover
  have "limit r\<^sub>\<A> \<inter> UNIV \<noteq> {}" and "limit r\<^sub>\<UU> \<inter> UNIV \<noteq> {}"
    using limit_nonempty \<open>finite (range r\<^sub>\<UU>)\<close> \<open>finite (range r\<^sub>\<A>)\<close> by auto
  ultimately
  show ?thesis
    unfolding accepting_pair\<^sub>R_def fst_conv snd_conv r\<^sub>\<A>_def[symmetric] r\<^sub>\<UU>_def[symmetric] Let_def by blast
qed

theorem ltl_to_generalized_rabin_correct:
  "w \<Turnstile> \<phi> \<longleftrightarrow> accept\<^sub>G\<^sub>R (\<A>\<^sub>\<UU> \<Sigma> \<phi>) w" 
  (is "_ \<longleftrightarrow> ?rhs")
proof (unfold ltl_to_generalized_rabin_af_correct[OF finite_\<Sigma> bounded_w], standard)
  let ?lhs = "accept\<^sub>G\<^sub>R (ltl_to_generalized_rabin_af \<Sigma> \<phi>) w"

  interpret \<A>: ltl_to_rabin_af \<Sigma> w
    using ltl_to_generalized_rabin_af_wellformed bounded_w finite_\<Sigma> by auto
   
  {
    assume ?lhs
    then obtain \<pi> where I: "dom \<pi> \<subseteq> \<^bold>G \<phi>" 
      and II:  "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi> \<chi>) < \<A>.max_rank_of \<Sigma> \<chi>"
      and III: "accepting_pair\<^sub>R (ltl_to_rabin_af.\<delta>\<^sub>\<A> \<Sigma>) (ltl_to_rabin_af.\<iota>\<^sub>\<A> \<phi>) (M_fin \<pi>, UNIV) w"
      and IV:  "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> accepting_pair\<^sub>R (\<A>.\<delta>\<^sub>\<A> \<Sigma>) (ltl_to_rabin_af.\<iota>\<^sub>\<A> \<phi>) (\<A>.Acc \<Sigma> \<pi> \<chi>) w"
      by (unfold ltl_to_generalized_rabin_af.simps; blast intro: \<A>.accept\<^sub>G\<^sub>R_I)
 
    \<comment> \<open>Normalise @{text \<pi>} to the smallest accepting ranks\<close>
    then obtain \<pi>\<^sub>\<A> where A: "dom \<pi> = dom \<pi>\<^sub>\<A>"
      and B: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> \<pi>\<^sub>\<A> \<chi> = mojmir_def.smallest_accepting_rank \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<up>\<Turnstile>\<^sub>P q}"
      and C: "accepting_pair\<^sub>R (\<A>.\<delta>\<^sub>\<A> \<Sigma>) (\<A>.\<iota>\<^sub>\<A> \<phi>) (M_fin \<pi>\<^sub>\<A>, UNIV) w" 
      and D: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> accepting_pair\<^sub>R (\<A>.\<delta>\<^sub>\<A> \<Sigma>) (\<A>.\<iota>\<^sub>\<A> \<phi>) (\<A>.Acc \<Sigma> \<pi>\<^sub>\<A> \<chi>) w"
      using \<A>.normalize_\<pi> by blast
  
    \<comment> \<open>Properties about the domain of @{text \<pi>}\<close>
    note \<G>_properties[OF \<open>dom \<pi> \<subseteq> \<^bold>G \<phi>\<close>]
    hence \<MM>_Accept: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> mojmir_def.accept af_G_letter_abs (Abs (theG \<chi>)) w {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q}"
      using I II IV \<A>.Acc_to_mojmir_accept unfolding ltl_to_rabin_base_def.max_rank_of_def by (metis ltl.sel(8)) 
    hence \<UU>_Accept: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> mojmir_def.accept af_G_letter_abs_opt (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q}"
      using unfold_accept_eq[OF \<open>Only_G (dom \<pi>)\<close> finite_\<Sigma> bounded_w] unfolding ltl_prop_entails_abs.rep_eq by blast
  
    \<comment> \<open>Define @{text \<pi>} for the other automaton\<close>
    define \<pi>\<^sub>\<UU>
      where "\<pi>\<^sub>\<UU> \<chi> = (if \<chi> \<in> dom \<pi> then mojmir_def.smallest_accepting_rank \<Sigma> af_G_letter_abs_opt (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q} else None)"
      for \<chi>
    
    have 1: "dom \<pi>\<^sub>\<UU> = dom \<pi>"
      using \<UU>_Accept by (auto simp add: \<pi>\<^sub>\<UU>_def dom_def mojmir_def.smallest_accepting_rank_def)   
    hence "dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>" and "dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>" and "dom \<pi>\<^sub>\<UU> \<subseteq> \<^bold>G \<phi>"
      using A \<open>dom \<pi> \<subseteq> \<^bold>G \<phi>\<close> by blast+
    have 2: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<UU> \<Longrightarrow> \<pi>\<^sub>\<UU> \<chi> = mojmir_def.smallest_accepting_rank \<Sigma> af_G_letter_abs_opt (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi>\<^sub>\<UU> \<up>\<Turnstile>\<^sub>P q}"
      using 1 unfolding \<open>dom \<pi>\<^sub>\<UU> = dom \<pi>\<close> \<pi>\<^sub>\<UU>_def by simp
    hence 3: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<UU> \<Longrightarrow> the (\<pi>\<^sub>\<UU> \<chi>) < semi_mojmir_def.max_rank \<Sigma> af_G_letter_abs_opt (Abs (Unf\<^sub>G (theG \<chi>))) "
      using wellformed_mojmir_opt[OF \<G>_elements[OF \<open>dom \<pi>\<^sub>\<UU> \<subseteq> \<^bold>G \<phi>\<close>] finite_\<Sigma> bounded_w, THEN mojmir.smallest_accepting_rank_properties(6)]
       unfolding ltl_prop_entails_abs.rep_eq by fastforce
  
    \<comment> \<open>Use correctness of the translation of individual accepting pairs\<close>
    have Acc: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<UU> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<Sigma> \<pi>\<^sub>\<UU> \<chi>) w"
      using mojmir_accept_to_Acc[OF _ \<open>dom \<pi>\<^sub>\<UU> \<subseteq> \<^bold>G \<phi>\<close>] \<G>_elements[OF \<open>dom \<pi>\<^sub>\<UU> \<subseteq> \<^bold>G \<phi>\<close>] 
      using 1 2[of "G _"] 3[of "G _"] \<UU>_Accept[of "G _"] ltl.sel(8) unfolding comp_apply by metis
    have M: "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU>, UNIV) w"
      using unfold_optimisation_correct_M[OF \<open>dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>\<close> \<open>dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>\<close> B 2] C
      using \<open>dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>\<close> by blast+
  
    show ?rhs
      using Acc 3 \<open>dom \<pi>\<^sub>\<UU> \<subseteq> \<^bold>G \<phi>\<close> combine_rabin_pairs_UNIV[OF M combine_rabin_pairs] 
      by (simp only: accept\<^sub>G\<^sub>R_def fst_conv snd_conv ltl_to_generalized_rabin.simps rabin_pairs.simps max_rank_of_def comp_apply) blast 
  }

  {
    assume ?rhs
    then obtain \<pi> where I: "dom \<pi> \<subseteq> \<^bold>G \<phi>" 
      and II:  "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi> \<chi>) < max_rank_of \<Sigma> \<chi>"
      and III: "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (M\<^sub>\<UU>_fin \<pi>, UNIV) w"
      and IV:  "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<Sigma> \<pi> \<chi>) w"
      by (blast intro: accept\<^sub>G\<^sub>R_I)
  
    \<comment> \<open>Normalize @{text \<pi>} to the smallest accepting ranks\<close>
    then obtain \<pi>\<^sub>\<UU> where A: "dom \<pi> = dom \<pi>\<^sub>\<UU>"
      and B: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<UU> \<Longrightarrow> \<pi>\<^sub>\<UU> \<chi> = mojmir_def.smallest_accepting_rank \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi>\<^sub>\<UU> \<up>\<Turnstile>\<^sub>P q}"
      and C: "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU>, UNIV) w" 
      and D: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<UU> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<Sigma> \<pi>\<^sub>\<UU> \<chi>) w"
      using normalize_\<pi> unfolding comp_apply by blast
  
    \<comment> \<open>Properties about the domain of @{text \<pi>}\<close>
    note \<G>_properties[OF \<open>dom \<pi> \<subseteq> \<^bold>G \<phi>\<close>]
    hence \<UU>_Accept: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> mojmir_def.accept af_G_letter_abs_opt (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q}"
      using I II IV Acc_to_mojmir_accept unfolding max_rank_of_def comp_apply by (metis ltl.sel(8)) 
    hence \<MM>_Accept: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> mojmir_def.accept af_G_letter_abs (Abs (theG \<chi>)) w {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q}"
      using unfold_accept_eq[OF \<open>Only_G (dom \<pi>)\<close> finite_\<Sigma> bounded_w]
      unfolding ltl_prop_entails_abs.rep_eq by blast
  
    \<comment> \<open>Define @{text \<pi>} for the other automaton\<close>
    define \<pi>\<^sub>\<A>
      where "\<pi>\<^sub>\<A> \<chi> = (if \<chi> \<in> dom \<pi> then mojmir_def.smallest_accepting_rank \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q} else None)"
      for \<chi>
    
    have 1: "dom \<pi>\<^sub>\<A> = dom \<pi>"
      using \<MM>_Accept by (auto simp add: \<pi>\<^sub>\<A>_def dom_def mojmir_def.smallest_accepting_rank_def)   
    hence "dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>" and "dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>" and "dom \<pi>\<^sub>\<UU> \<subseteq> \<^bold>G \<phi>"
      using A \<open>dom \<pi> \<subseteq> \<^bold>G \<phi>\<close> by blast+
    hence "ltl_FG_to_rabin \<Sigma> (dom \<pi>\<^sub>\<A>) w"
      by (unfold_locales; insert \<G>_elements[OF \<open>dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>\<close>] finite_\<Sigma> bounded_w) 
    have 2: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> \<pi>\<^sub>\<A> \<chi> = mojmir_def.smallest_accepting_rank \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<up>\<Turnstile>\<^sub>P q}"
      using 1 unfolding \<open>dom \<pi>\<^sub>\<A> = dom \<pi>\<close> \<pi>\<^sub>\<A>_def by simp
    hence 3: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> the (\<pi>\<^sub>\<A> \<chi>) < semi_mojmir_def.max_rank \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>))"
      using ltl_FG_to_rabin.smallest_accepting_rank_properties(6)[OF \<open>ltl_FG_to_rabin \<Sigma> (dom \<pi>\<^sub>\<A>) w\<close>]
      unfolding ltl_prop_entails_abs.rep_eq by fastforce
  
    \<comment> \<open>Use correctness of the translation of individual accepting pairs\<close>
    have Acc: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> accepting_pair\<^sub>R (\<A>.\<delta>\<^sub>\<A> \<Sigma>) (\<A>.\<iota>\<^sub>\<A> \<phi>) (\<A>.Acc \<Sigma> \<pi>\<^sub>\<A> \<chi>) w"
      using \<A>.mojmir_accept_to_Acc[OF _ \<open>dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>\<close>] \<G>_elements[OF \<open>dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>\<close>] 
      using 1 2[of "G _"] 3[of "G _"] \<MM>_Accept[of "G _"] ltl.sel(8) by metis 
    have M: "accepting_pair\<^sub>R (\<A>.\<delta>\<^sub>\<A> \<Sigma>) (\<A>.\<iota>\<^sub>\<A> \<phi>) (M_fin \<pi>\<^sub>\<A>, UNIV) w" 
      using unfold_optimisation_correct_M[OF \<open>dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>\<close> \<open>dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>\<close> 2 B] C
      using \<open>dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>\<close> by blast+
  
    show ?lhs
      using Acc 3 \<open>dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>\<close> combine_rabin_pairs_UNIV[OF M combine_rabin_pairs]
      by (simp only: accept\<^sub>G\<^sub>R_def fst_conv snd_conv \<A>.ltl_to_generalized_rabin.simps \<A>.rabin_pairs.simps
                     ltl_to_generalized_rabin_af.simps  \<A>.max_rank_of_def comp_apply) blast 
  }
qed

end

fun ltl_to_generalized_rabin_af\<^sub>\<UU>
where
  "ltl_to_generalized_rabin_af\<^sub>\<UU> \<Sigma> \<phi> = ltl_to_rabin_base_def.ltl_to_generalized_rabin \<up>af\<^sub>\<UU> \<up>af\<^sub>G\<^sub>\<UU> (Abs \<circ> Unf) (Abs \<circ> Unf\<^sub>G) M\<^sub>\<UU>_fin \<Sigma> \<phi>"  

lemma ltl_to_generalized_rabin_af\<^sub>\<UU>_wellformed:
  "finite \<Sigma> \<Longrightarrow> range w \<subseteq> \<Sigma> \<Longrightarrow> ltl_to_rabin_af_unf \<Sigma> w"
  apply (unfold_locales)
  apply (auto simp add: af_G_letter_opt_sat_core_lifted ltl_prop_entails_abs.rep_eq intro: finite_reach_af_opt finite_reach_af_G_opt) 
  apply (meson le_trans ltl_semi_mojmir[unfolded semi_mojmir_def])+
  done

theorem ltl_to_generalized_rabin_af\<^sub>\<UU>_correct:
  assumes "finite \<Sigma>"
  assumes "range w \<subseteq> \<Sigma>"
  shows "w \<Turnstile> \<phi> = accept\<^sub>G\<^sub>R (ltl_to_generalized_rabin_af\<^sub>\<UU> \<Sigma> \<phi>) w"
  using ltl_to_generalized_rabin_af\<^sub>\<UU>_wellformed[OF assms, THEN ltl_to_rabin_af_unf.ltl_to_generalized_rabin_correct] by simp

thm ltl_FG_to_generalized_rabin_correct ltl_to_generalized_rabin_af_correct ltl_to_generalized_rabin_af\<^sub>\<UU>_correct

end
