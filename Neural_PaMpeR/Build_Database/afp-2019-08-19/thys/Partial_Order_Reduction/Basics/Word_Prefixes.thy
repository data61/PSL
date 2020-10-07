section \<open>Finite Prefixes of Infinite Sequences\<close>

theory Word_Prefixes
imports
  List_Prefixes
  "../Extensions/List_Extensions"
  Transition_Systems_and_Automata.Sequence
begin

  definition prefix_fininf :: "'a list \<Rightarrow> 'a stream \<Rightarrow> bool" (infix "\<le>\<^sub>F\<^sub>I" 50)
    where "u \<le>\<^sub>F\<^sub>I v \<equiv> \<exists> w. u @- w = v"

  lemma prefix_fininfI[intro]:
    assumes "u @- w = v"
    shows "u \<le>\<^sub>F\<^sub>I v"
    using assms unfolding prefix_fininf_def by auto
  lemma prefix_fininfE[elim]:
    assumes "u \<le>\<^sub>F\<^sub>I v"
    obtains w
    where "v = u @- w"
    using assms unfolding prefix_fininf_def by auto

  lemma prefix_fininfI_empty[intro!]: "[] \<le>\<^sub>F\<^sub>I w" by force
  lemma prefix_fininfI_item[intro!]:
    assumes "a = b" "u \<le>\<^sub>F\<^sub>I v"
    shows "a # u \<le>\<^sub>F\<^sub>I b ## v"
    using assms by force
  lemma prefix_fininfE_item[elim!]:
    assumes "a # u \<le>\<^sub>F\<^sub>I b ## v"
    obtains "a = b" "u \<le>\<^sub>F\<^sub>I v"
    using assms by force

  lemma prefix_fininf_item[simp]: "a # u \<le>\<^sub>F\<^sub>I a ## v \<longleftrightarrow> u \<le>\<^sub>F\<^sub>I v" by force
  lemma prefix_fininf_list[simp]: "w @ u \<le>\<^sub>F\<^sub>I w @- v \<longleftrightarrow> u \<le>\<^sub>F\<^sub>I v" by (induct w, auto)
  lemma prefix_fininf_conc[intro]: "u \<le>\<^sub>F\<^sub>I u @- v" by auto
  lemma prefix_fininf_prefix[intro]: "stake k w \<le>\<^sub>F\<^sub>I w" using stake_sdrop by blast
  lemma prefix_fininf_set_range[dest]: "u \<le>\<^sub>F\<^sub>I v \<Longrightarrow> set u \<subseteq> sset v" by auto

  lemma prefix_fininf_absorb:
    assumes "u \<le>\<^sub>F\<^sub>I v @- w" "length u \<le> length v"
    shows "u \<le> v"
  proof -
    obtain x where 1: "u @- x = v @- w" using assms(1) by auto
    have "u \<le> u @ stake (length v - length u) x" by rule
    also have "\<dots> = stake (length v) (u @- x)" using assms(2) by (simp add: stake_shift)
    also have "\<dots> = stake (length v) (v @- w)" unfolding 1 by rule
    also have "\<dots> = v" using eq_shift by blast
    finally show ?thesis by this
  qed
  lemma prefix_fininf_extend:
    assumes "u \<le>\<^sub>F\<^sub>I v @- w" "length v \<le> length u"
    shows "v \<le> u"
  proof -
    obtain x where 1: "u @- x = v @- w" using assms(1) by auto
    have "v \<le> v @ stake (length u - length v) w" by rule
    also have "\<dots> = stake (length u) (v @- w)" using assms(2) by (simp add: stake_shift)
    also have "\<dots> = stake (length u) (u @- x)" unfolding 1 by rule
    also have "\<dots> = u" using eq_shift by blast
    finally show ?thesis by this
  qed
  lemma prefix_fininf_length:
    assumes "u \<le>\<^sub>F\<^sub>I w" "v \<le>\<^sub>F\<^sub>I w" "length u \<le> length v"
    shows "u \<le> v"
  proof -
    obtain u' v' where 1: "w = u @- u'" "w = v @- v'" using assms(1, 2) by blast+
    have "u = stake (length u) (u @- u')" using shift_eq by blast
    also have "\<dots> = stake (length u) w" unfolding 1(1) by rule
    also have "\<dots> = stake (length u) (v @- v')" unfolding 1(2) by rule
    also have "\<dots> = take (length u) v" using assms by (simp add: min.absorb2 stake_append)
    also have "\<dots> \<le> v" by rule
    finally show ?thesis by this
  qed

  lemma prefix_fininf_append:
    assumes "u \<le>\<^sub>F\<^sub>I v @- w"
    obtains (absorb) "u \<le> v" | (extend) z where "u = v @ z" "z \<le>\<^sub>F\<^sub>I w"
  proof (cases "length u" "length v" rule: le_cases)
    case le
    obtain x where 1: "u @- x = v @- w" using assms(1) by auto
    show ?thesis
    proof (rule absorb)
      have "u \<le> u @ stake (length v - length u) x" by rule
      also have "\<dots> = stake (length v) (u @- x)" using le by (simp add: stake_shift)
      also have "\<dots> = stake (length v) (v @- w)" unfolding 1 by rule
      also have "\<dots> = v" using eq_shift by blast
      finally show "u \<le> v" by this
    qed
  next
    case ge
    obtain x where 1: "u @- x = v @- w" using assms(1) by auto
    show ?thesis
    proof (rule extend)
      have "u = stake (length u) (u @- x)" using shift_eq by auto
      also have "\<dots> = stake (length u) (v @- w)" unfolding 1 by rule
      also have "\<dots> = v @ stake (length u - length v) w" using ge by (simp add: stake_shift)
      finally show "u = v @ stake (length u - length v) w" by this
      show "stake (length u - length v) w \<le>\<^sub>F\<^sub>I w" by rule
    qed
  qed

  lemma prefix_fin_prefix_fininf_trans[trans, intro]: "u \<le> v \<Longrightarrow> v \<le>\<^sub>F\<^sub>I w \<Longrightarrow> u \<le>\<^sub>F\<^sub>I w"
    by (metis Prefix_Order.prefixE prefix_fininf_def shift_append)

  lemma prefix_finE_nth:
    assumes "u \<le> v" "i < length u"
    shows "u ! i = v ! i"
  proof -
    obtain w where 1: "v = u @ w" using assms(1) by auto
    show ?thesis unfolding 1 using assms(2) by (simp add: nth_append)
  qed
  lemma prefix_fininfI_nth:
    assumes "\<And> i. i < length u \<Longrightarrow> u ! i = w !! i"
    shows "u \<le>\<^sub>F\<^sub>I w"
  proof (rule prefix_fininfI)
    show "u @- sdrop (length u) w = w" by (simp add: assms list_eq_iff_nth_eq shift_eq)
  qed

  definition chain :: "(nat \<Rightarrow> 'a list) \<Rightarrow> bool"
    where "chain w \<equiv> mono w \<and> (\<forall> k. \<exists> l. k < length (w l))"
  definition limit :: "(nat \<Rightarrow> 'a list) \<Rightarrow> 'a stream"
    where "limit w \<equiv> smap (\<lambda> k. w (SOME l. k < length (w l)) ! k) nats"

  lemma chainI[intro?]:
    assumes "mono w"
    assumes "\<And> k. \<exists> l. k < length (w l)"
    shows "chain w"
    using assms unfolding chain_def by auto
  lemma chainD_mono[dest?]:
    assumes "chain w"
    shows "mono w"
    using assms unfolding chain_def by auto
  lemma chainE_length[elim?]:
    assumes "chain w"
    obtains l
    where "k < length (w l)"
    using assms unfolding chain_def by auto

  lemma chain_prefix_limit:
    assumes "chain w"
    shows "w k \<le>\<^sub>F\<^sub>I limit w"
  proof (rule prefix_fininfI_nth)
    fix i
    assume 1: "i < length (w k)"
    have 2: "mono w" "\<And> k. \<exists> l. k < length (w l)" using chainD_mono chainE_length assms by blast+
    have 3: "i < length (w (SOME l. i < length (w l)))" using someI_ex 2(2) by this
    show "w k ! i = limit w !! i"
    proof (cases "k" "SOME l. i < length (w l)" rule: le_cases)
      case (le)
      have 4: "w k \<le> w (SOME l. i < length (w l))" using monoD 2(1) le by this
      show ?thesis unfolding limit_def using prefix_finE_nth 4 1 by auto
    next
      case (ge)
      have 4: "w (SOME l. i < length (w l)) \<le> w k" using monoD 2(1) ge by this
      show ?thesis unfolding limit_def using prefix_finE_nth 4 3 by auto
    qed
  qed

  lemma chain_construct_1:
    assumes "P 0 x\<^sub>0" "\<And> k x. P k x \<Longrightarrow> \<exists> x'. P (Suc k) x' \<and> f x \<le> f x'"
    assumes "\<And> k x. P k x \<Longrightarrow> k \<le> length (f x)"
    obtains Q
    where "\<And> k. P k (Q k)" "chain (f \<circ> Q)"
  proof -
    obtain x' where 1:
      "P 0 x\<^sub>0" "\<And> k x. P k x \<Longrightarrow> P (Suc k) (x' k x) \<and> f x \<le> f (x' k x)"
      using assms(1, 2) by metis
    define Q where "Q \<equiv> rec_nat x\<^sub>0 x'"
    have [simp]: "Q 0 = x\<^sub>0" "\<And> k. Q (Suc k) = x' k (Q k)" unfolding Q_def by simp+
    have 2: "\<And> k. P k (Q k)"
    proof -
      fix k
      show "P k (Q k)" using 1 by (induct k, auto)
    qed
    show ?thesis
    proof (intro that chainI monoI, unfold comp_apply)
      fix k
      show "P k (Q k)" using 2 by this
    next
      fix x y :: nat
      assume "x \<le> y"
      thus "f (Q x) \<le> f (Q y)"
      proof (induct "y - x" arbitrary: x y)
        case 0
        show ?case using 0 by simp
      next
        case (Suc k)
        have "f (Q x) \<le> f (Q (Suc x))" using 1(2) 2 by auto
        also have "\<dots> \<le> f (Q y)" using Suc(2) by (intro Suc(1), auto)
        finally show ?case by this
      qed
    next
      fix k
      have 3: "P (Suc k) (Q (Suc k))" using 2 by this
      have 4: "Suc k \<le> length (f (Q (Suc k)))" using assms(3) 3 by this
      have 5: "k < length (f (Q (Suc k)))" using 4 by auto
      show "\<exists> l. k < length (f (Q l))" using 5 by blast
    qed
  qed
  lemma chain_construct_2:
    assumes "P 0 x\<^sub>0" "\<And> k x. P k x \<Longrightarrow> \<exists> x'. P (Suc k) x' \<and> f x \<le> f x' \<and> g x \<le> g x'"
    assumes "\<And> k x. P k x \<Longrightarrow> k \<le> length (f x)" "\<And> k x. P k x \<Longrightarrow> k \<le> length (g x)"
    obtains Q
    where "\<And> k. P k (Q k)" "chain (f \<circ> Q)" "chain (g \<circ> Q)"
  proof -
    obtain x' where 1:
      "P 0 x\<^sub>0" "\<And> k x. P k x \<Longrightarrow> P (Suc k) (x' k x) \<and> f x \<le> f (x' k x) \<and> g x \<le> g (x' k x)"
      using assms(1, 2) by metis
    define Q where "Q \<equiv> rec_nat x\<^sub>0 x'"
    have [simp]: "Q 0 = x\<^sub>0" "\<And> k. Q (Suc k) = x' k (Q k)" unfolding Q_def by simp+
    have 2: "\<And> k. P k (Q k)"
    proof -
      fix k
      show "P k (Q k)" using 1 by (induct k, auto)
    qed
    show ?thesis
    proof (intro that chainI monoI, unfold comp_apply)
      fix k
      show "P k (Q k)" using 2 by this
    next
      fix x y :: nat
      assume "x \<le> y"
      thus "f (Q x) \<le> f (Q y)"
      proof (induct "y - x" arbitrary: x y)
        case 0
        show ?case using 0 by simp
      next
        case (Suc k)
        have "f (Q x) \<le> f (Q (Suc x))" using 1(2) 2 by auto
        also have "\<dots> \<le> f (Q y)" using Suc(2) by (intro Suc(1), auto)
        finally show ?case by this
      qed
    next
      fix k
      have 3: "P (Suc k) (Q (Suc k))" using 2 by this
      have 4: "Suc k \<le> length (f (Q (Suc k)))" using assms(3) 3 by this
      have 5: "k < length (f (Q (Suc k)))" using 4 by auto
      show "\<exists> l. k < length (f (Q l))" using 5 by blast
    next
      fix x y :: nat
      assume "x \<le> y"
      thus "g (Q x) \<le> g (Q y)"
      proof (induct "y - x" arbitrary: x y)
        case 0
        show ?case using 0 by simp
      next
        case (Suc k)
        have "g (Q x) \<le> g (Q (Suc x))" using 1(2) 2 by auto
        also have "\<dots> \<le> g (Q y)" using Suc(2) by (intro Suc(1), auto)
        finally show ?case by this
      qed
    next
      fix k
      have 3: "P (Suc k) (Q (Suc k))" using 2 by this
      have 4: "Suc k \<le> length (g (Q (Suc k)))" using assms(4) 3 by this
      have 5: "k < length (g (Q (Suc k)))" using 4 by auto
      show "\<exists> l. k < length (g (Q l))" using 5 by blast
    qed
  qed
  lemma chain_construct_2':
    assumes "P 0 u\<^sub>0 v\<^sub>0" "\<And> k u v. P k u v \<Longrightarrow> \<exists> u' v'. P (Suc k) u' v' \<and> u \<le> u' \<and> v \<le> v'"
    assumes "\<And> k u v. P k u v \<Longrightarrow> k \<le> length u" "\<And> k u v. P k u v \<Longrightarrow> k \<le> length v"
    obtains u v
    where "\<And> k. P k (u k) (v k)" "chain u" "chain v"
  proof -
    obtain Q where 1: "\<And> k. (case_prod \<circ> P) k (Q k)" "chain (fst \<circ> Q)" "chain (snd \<circ> Q)"
    proof (rule chain_construct_2)
      show "\<exists> x'. (case_prod \<circ> P) (Suc k) x' \<and> fst x \<le> fst x' \<and> snd x \<le> snd x'"
        if "(case_prod \<circ> P) k x" for k x using assms that by auto
      show "(case_prod \<circ> P) 0 (u\<^sub>0, v\<^sub>0)" using assms by auto
      show "k \<le> length (fst x)" if "(case_prod \<circ> P) k x" for k x using assms that by auto
      show "k \<le> length (snd x)" if "(case_prod \<circ> P) k x" for k x using assms that by auto
    qed rule
    show ?thesis
    proof
      show "P k ((fst \<circ> Q) k) ((snd \<circ> Q) k)" for k using 1(1) by (auto simp: prod.case_eq_if)
      show "chain (fst \<circ> Q)" "chain (snd \<circ> Q)" using 1(2, 3) by this
    qed
  qed

end