section \<open>Transition Systems and Trace Theory\<close>

theory Transition_System_Traces
imports
  Transition_System_Extensions
  Traces
begin

  lemma (in transition_system) words_infI_construct[rule_format, intro?]:
    assumes "\<forall> v. v \<le>\<^sub>F\<^sub>I w \<longrightarrow> path v p"
    shows "run w p"
    using assms by coinduct auto

  lemma (in transition_system) words_infI_construct':
    assumes "\<And> k. \<exists> v. v \<le>\<^sub>F\<^sub>I w \<and> k < length v \<and> path v p"
    shows "run w p"
  proof
    fix u
    assume 1: "u \<le>\<^sub>F\<^sub>I w"
    obtain v where 2: "v \<le>\<^sub>F\<^sub>I w" "length u < length v" "path v p" using assms(1) by auto
    have 3: "length u \<le> length v" using 2(2) by simp
    have 4: "u \<le> v" using prefix_fininf_length 1 2(1) 3 by this
    show "path u p" using 4 2(3) by auto
  qed

  lemma (in transition_system) words_infI_construct_chain[intro]:
    assumes "chain w" "\<And> k. path (w k) p"
    shows "run (limit w) p"
  proof (rule words_infI_construct')
    fix k
    obtain l where 1: "k < length (w l)" using assms(1) by rule
    show "\<exists> v. v \<le>\<^sub>F\<^sub>I limit w \<and> k < length v \<and> path v p"
    proof (intro exI conjI)
      show "w l \<le>\<^sub>F\<^sub>I limit w" using chain_prefix_limit assms(1) by this
      show "k < length (w l)" using 1 by this
      show "path (w l) p" using assms(2) by this
    qed
  qed

  lemma (in transition_system) words_fin_blocked:
    assumes "\<And> w. path w p \<Longrightarrow> A \<inter> set w = {} \<Longrightarrow> A \<inter> {a. enabled a (target w p)} \<subseteq> A \<inter> {a. enabled a p}"
    assumes "path w p" "A \<inter> {a. enabled a p} \<inter> set w = {}"
    shows "A \<inter> set w = {}"
    using assms by (induct w rule: rev_induct, auto)

  locale transition_system_traces =
    transition_system ex en +
    traces ind
    for ex :: "'action \<Rightarrow> 'state \<Rightarrow> 'state"
    and en :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    and ind :: "'action \<Rightarrow> 'action \<Rightarrow> bool"
    +
    assumes en: "ind a b \<Longrightarrow> en a p \<Longrightarrow> en b p \<longleftrightarrow> en b (ex a p)"
    assumes ex: "ind a b \<Longrightarrow> en a p \<Longrightarrow> en b p \<Longrightarrow> ex b (ex a p) = ex a (ex b p)"
  begin

    lemma diamond_bottom:
      assumes "ind a b"
      assumes "en a p" "en b p"
      shows "en a (ex b p)" "en b (ex a p)" "ex b (ex a p) = ex a (ex b p)"
      using assms independence_symmetric en ex by metis+
    lemma diamond_right:
      assumes "ind a b"
      assumes "en a p" "en b (ex a p)"
      shows "en a (ex b p)" "en b p" "ex b (ex a p) = ex a (ex b p)"
      using assms independence_symmetric en ex by metis+
    lemma diamond_left:
      assumes "ind a b"
      assumes "en a (ex b p)" "en b p"
      shows "en a p" "en b (ex a p)" "ex b (ex a p) = ex a (ex b p)"
      using assms independence_symmetric en ex by metis+

    lemma eq_swap_word:
      assumes "w\<^sub>1 =\<^sub>S w\<^sub>2" "path w\<^sub>1 p"
      shows "path w\<^sub>2 p"
      using assms diamond_right by (induct, auto)
    lemma eq_fin_word:
      assumes "w\<^sub>1 =\<^sub>F w\<^sub>2" "path w\<^sub>1 p"
      shows "path w\<^sub>2 p"
      using assms eq_swap_word by (induct, auto)
    lemma le_fin_word:
      assumes "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2" "path w\<^sub>2 p"
      shows "path w\<^sub>1 p"
      using assms eq_fin_word by blast
    lemma le_fininf_word:
      assumes "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2" "run w\<^sub>2 p"
      shows "path w\<^sub>1 p"
      using assms le_fin_word by blast
    lemma le_inf_word:
      assumes "w\<^sub>2 \<preceq>\<^sub>I w\<^sub>1" "run w\<^sub>1 p"
      shows "run w\<^sub>2 p"
      using assms le_fininf_word by (blast intro: words_infI_construct)
    lemma eq_inf_word:
      assumes "w\<^sub>1 =\<^sub>I w\<^sub>2" "run w\<^sub>1 p"
      shows "run w\<^sub>2 p"
      using assms le_inf_word by auto

    lemma eq_swap_execute:
      assumes "path w\<^sub>1 p" "w\<^sub>1 =\<^sub>S w\<^sub>2"
      shows "fold ex w\<^sub>1 p = fold ex w\<^sub>2 p"
      using assms(2, 1) diamond_right by (induct, auto)
    lemma eq_fin_execute:
      assumes "path w\<^sub>1 p" "w\<^sub>1 =\<^sub>F w\<^sub>2"
      shows "fold ex w\<^sub>1 p = fold ex w\<^sub>2 p"
      using assms(2, 1) eq_fin_word eq_swap_execute by (induct, auto)

    lemma diamond_fin_word_step:
      assumes "Ind {a} (set v)" "en a p" "path v p"
      shows "path v (ex a p)"
      using diamond_bottom assms by (induct v arbitrary: p, auto, metis)
    lemma diamond_inf_word_step:
      assumes "Ind {a} (sset w)" "en a p" "run w p"
      shows "run w (ex a p)"
      using diamond_fin_word_step assms by (fast intro: words_infI_construct)
    lemma diamond_fin_word_inf_word:
      assumes "Ind (set v) (sset w)" "path v p" "run w p"
      shows "run w (fold ex v p)"
      using diamond_inf_word_step assms by (induct v arbitrary: p, auto)
    lemma diamond_fin_word_inf_word':
      assumes "Ind (set v) (sset w)" "path (u @ v) p" "run (u @- w) p"
      shows "run (u @- v @- w) p"
      using assms diamond_fin_word_inf_word by auto

  end

end
