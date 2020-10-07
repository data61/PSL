section \<open>Stuttering\<close>

theory Stuttering
imports
  Stuttering_Equivalence.StutterEquivalence
  LList_Prefixes
begin

  function nth_least_ext :: "nat set \<Rightarrow> nat \<Rightarrow> nat"
    where
      "enat k < esize A \<Longrightarrow> nth_least_ext A k = nth_least A k" |
      "enat k \<ge> esize A \<Longrightarrow> nth_least_ext A k = Suc (Max A + (k - card A))"
    by force+ termination by lexicographic_order

  lemma nth_least_ext_strict_mono:
    assumes "k < l"
    shows "nth_least_ext s k < nth_least_ext s l"
  proof (cases "enat l < esize s")
    case True
    have 1: "enat k < esize s" using assms True by (metis enat_ord_simps(2) less_trans)
    show ?thesis using nth_least_strict_mono assms True 1 by simp
  next
    case False
    have 1: "finite s" using False esize_infinite_enat by auto
    have 2: "enat l \<ge> esize s" using False by simp
    have 3: "l \<ge> card s" using 1 2 by simp
    show ?thesis
    proof (cases "enat k < esize s")
      case True
      have 4: "s \<noteq> {}" using True by auto
      have "nth_least_ext s k = nth_least s k" using True by simp
      also have "\<dots> \<le> Max s" using nth_least_le_Max 1 4 True by this
      also have "\<dots> < Suc (Max s)" by auto
      also have "\<dots> \<le> Suc (Max s + (l - card s))" by auto
      also have "Suc (Max s + (l - card s)) = nth_least_ext s l" using 2 by simp
      finally show ?thesis by this
    next
      case False
      have 4: "enat k \<ge> esize s" using False by simp
      have 5: "k \<ge> card s" using 1 4 by simp
      have "nth_least_ext s k = Suc (Max s + (k - card s))" using 4 by simp
      also have "\<dots> < Suc (Max s + (l - card s))" using assms 5 by simp
      also have "\<dots> = nth_least_ext s l" using 2 by simp
      finally show ?thesis by this
    qed
  qed

  definition stutter_selection :: "nat set \<Rightarrow> 'a llist \<Rightarrow> bool"
    where "stutter_selection s w \<equiv> 0 \<in> s \<and>
      (\<forall> k i. enat i < llength w \<longrightarrow> enat (Suc k) < esize s \<longrightarrow>
      nth_least s k < i \<longrightarrow> i < nth_least s (Suc k) \<longrightarrow> w ? i = w ? nth_least s k) \<and>
      (\<forall> i. enat i < llength w \<longrightarrow> finite s \<longrightarrow> Max s < i \<longrightarrow> w ? i = w ? Max s)"

  lemma stutter_selectionI[intro]:
    assumes "0 \<in> s"
    assumes "\<And> k i. enat i < llength w \<Longrightarrow> enat (Suc k) < esize s \<Longrightarrow>
      nth_least s k < i \<Longrightarrow> i < nth_least s (Suc k) \<Longrightarrow> w ? i = w ? nth_least s k"
    assumes "\<And> i. enat i < llength w \<Longrightarrow> finite s \<Longrightarrow> Max s < i \<Longrightarrow> w ? i = w ? Max s"
    shows "stutter_selection s w"
    using assms unfolding stutter_selection_def by auto
  lemma stutter_selectionD_0[dest]:
    assumes "stutter_selection s w"
    shows "0 \<in> s"
    using assms unfolding stutter_selection_def by auto
  lemma stutter_selectionD_inside[dest]:
    assumes "stutter_selection s w"
    assumes "enat i < llength w" "enat (Suc k) < esize s"
    assumes "nth_least s k < i" "i < nth_least s (Suc k)"
    shows "w ? i = w ? nth_least s k"
    using assms unfolding stutter_selection_def by auto
  lemma stutter_selectionD_infinite[dest]:
    assumes "stutter_selection s w"
    assumes "enat i < llength w" "finite s" "Max s < i"
    shows "w ? i = w ? Max s"
    using assms unfolding stutter_selection_def by auto

  lemma stutter_selection_stutter_sampler[intro]:
    assumes "linfinite w" "stutter_selection s w"
    shows "stutter_sampler (nth_least_ext s) (lnth w)"
  unfolding stutter_sampler_def
  proof safe
    show "nth_least_ext s 0 = 0" using assms(2) by (cases "enat 0 < esize s", auto)
    show "strict_mono (nth_least_ext s)" using strict_monoI nth_least_ext_strict_mono by blast
  next
    fix k i
    assume 1: "nth_least_ext s k < i" "i < nth_least_ext s (Suc k)"
    show "w ? i = w ? nth_least_ext s k"
    proof (cases "enat (Suc k)" "esize s" rule: linorder_cases)
      case less
      have "w ? i = w ? nth_least s k"
      proof (rule stutter_selectionD_inside)
        show "stutter_selection s w" using assms(2) by this
        show "enat i < llength w" using assms(1) by auto
        show "enat (Suc k) < esize s" using less by this
        show "nth_least s k < i" using 1(1) less by auto
        show "i < nth_least s (Suc k)" using 1(2) less by simp
      qed
      also have "w ? nth_least s k = w ? nth_least_ext s k" using less by auto
      finally show ?thesis by this
    next
      case equal
      have 2: "enat k < esize s" using equal by (metis enat_ord_simps(2) lessI)
      have 3: "finite s" using equal by (metis esize_infinite_enat less_irrefl)
      have 4: "\<And> i. i > Max s \<Longrightarrow> w ? i = w ? Max s" using assms 3 by auto
      have 5: "k = card s - 1" using equal 3 by (metis diff_Suc_1 enat.inject esize_set.simps(1))
      have "Max s = nth_least s (card s - 1)" using nth_least_Max 3 assms(2) by force
      also have "\<dots> = nth_least s k" unfolding 5 by rule
      also have "\<dots> = nth_least_ext s k" using 2 by simp 
      finally have 6: "Max s = nth_least_ext s k" by this
      have "w ? i = w ? Max s" using 1(1) 4 6 by auto
      also have "\<dots> = w ? nth_least_ext s k" unfolding 6 by rule
      finally show ?thesis by this
    next
      case greater
      have 2: "enat k \<ge> esize s" using greater by (metis Suc_ile_eq not_le)
      have 3: "finite s" using greater by (metis esize_infinite_enat less_asym)
      have 4: "\<And> i. i > Max s \<Longrightarrow> w ? i = w ? Max s" using assms 3 by auto
      have "w ? i = w ? Max s" using 1(1) 2 4 by auto 
      also have "\<dots> = w ? Suc (Max s + (k - card s))" using 4 by simp
      also have "\<dots> = w ? nth_least_ext s k" using 2 by simp
      finally show ?thesis by this
    qed
  qed

  lemma stutter_equivI_selection[intro]:
    assumes "linfinite u" "linfinite v"
    assumes "stutter_selection s u" "stutter_selection t v"
    assumes "lselect s u = lselect t v"
    shows "lnth u \<approx> lnth v"
  proof (rule stutter_equivI)
    have 1: "llength (lselect s u) = llength (lselect t v)" unfolding assms(5) by rule
    have 2: "esize s = esize t" using 1 assms(1, 2) unfolding lselect_llength by simp
    show "stutter_sampler (nth_least_ext s) (lnth u)" using assms(1, 3) by rule
    show "stutter_sampler (nth_least_ext t) (lnth v)" using assms(2, 4) by rule
    show "lnth u \<circ> nth_least_ext s = lnth v \<circ> nth_least_ext t"
    proof (rule ext, unfold comp_apply)
      fix i
      show "u ? nth_least_ext s i = v ? nth_least_ext t i" 
      proof (cases "enat i < esize s")
        case True
        have 3: "enat i < llength (lselect s u)" "enat i < llength (lselect t v)"
          using assms(1, 2) 2 True unfolding lselect_llength by auto
        have "u ? nth_least_ext s i = u ? nth_least s i" using True by simp
        also have "\<dots> = lselect s u ? i" using 3(1) by simp
        also have "\<dots> = lselect t v ? i" unfolding assms(5) by rule
        also have "\<dots> = v ? nth_least t i" using 3(2) by simp
        also have "\<dots> = v ? nth_least_ext t i" using True unfolding 2 by simp
        finally show "u ? nth_least_ext s i = v ? nth_least_ext t i" by this
      next
        case False
        have 3: "s \<noteq> {}" "t \<noteq> {}" using assms(3, 4) by auto
        have 4: "finite s" "finite t" using esize_infinite_enat 2 False by metis+
        have 5: "\<And> i. i > Max s \<Longrightarrow> u ? i = u ? Max s" using assms(1, 3) 4(1) by auto
        have 6: "\<And> i. i > Max t \<Longrightarrow> v ? i = v ? Max t" using assms(2, 4) 4(2) by auto
        have 7: "esize s = enat (card s)" "esize t = enat (card t)" using 4 by auto
        have 8: "card s \<noteq> 0" "card t \<noteq> 0" using 3 4 by auto
        have 9: "enat (card s - 1) < llength (lselect s u)"
          using assms(1) 7(1) 8(1) unfolding lselect_llength by simp
        have 10: "enat (card t - 1) < llength (lselect t v)"
          using assms(2) 7(2) 8(2) unfolding lselect_llength by simp
        have "u ? nth_least_ext s i = u ? Suc (Max s + (i - card s))" using False by simp
        also have "\<dots> = u ? Max s" using 5 by simp
        also have "\<dots> = u ? nth_least s (card s - 1)" using nth_least_Max 4(1) 3(1) by force
        also have "\<dots> = lselect s u ? (card s - 1)" using lselect_lnth 9 by simp
        also have "\<dots> = lselect s u ? (card t - 1)" using 2 4 by simp
        also have "\<dots> = lselect t v ? (card t - 1)" unfolding assms(5) by rule
        also have "\<dots> = v ? nth_least t (card t - 1)" using lselect_lnth 10 by simp
        also have "\<dots> = v ? Max t" using nth_least_Max 4(2) 3(2) by force
        also have "\<dots> = v ? Suc (Max t + (i - card t))" using 6 by simp
        also have "\<dots> = v ? nth_least_ext t i" using 2 False by simp
        finally show ?thesis by this
      qed
    qed
  qed

  definition stuttering_invariant :: "'a word set \<Rightarrow> bool"
    where "stuttering_invariant A \<equiv> \<forall> u v. u \<approx> v \<longrightarrow> u \<in> A \<longleftrightarrow> v \<in> A"

  lemma stuttering_invariant_complement[intro!]:
    assumes "stuttering_invariant A"
    shows "stuttering_invariant (- A)"
    using assms unfolding stuttering_invariant_def by simp

  lemma stutter_equiv_forw_subst[trans]: "w\<^sub>1 = w\<^sub>2 \<Longrightarrow> w\<^sub>2 \<approx> w\<^sub>3 \<Longrightarrow> w\<^sub>1 \<approx> w\<^sub>3" by auto

  lemma stutter_sampler_build:
    assumes "stutter_sampler f w"
    shows "stutter_sampler (0 ## (Suc \<circ> f)) (a ## w)"
  unfolding stutter_sampler_def
  proof safe
    have 0: "f 0 = 0" using assms unfolding stutter_sampler_def by auto
    have 1: "f x < f y" if "x < y" for x y
      using assms that unfolding stutter_sampler_def strict_mono_def by auto
    have 2: "(0 ## (Suc \<circ> f)) x < (0 ## (Suc \<circ> f)) y" if "x < y" for x y
      using 1 that by (cases x; cases y) (auto)
    have 3: "w n = w (f k)" if "f k < n" "n < f (Suc k)" for k n
      using assms that unfolding stutter_sampler_def by auto
    show "(0 ## (Suc \<circ> f)) 0 = 0" by simp
    show "strict_mono (0 ## (Suc \<circ> f))" using 2 by rule
    show "(a ## w) n = (a ## w) ((0 ## (Suc \<circ> f)) k)"
      if "(0 ## (Suc \<circ> f)) k < n" "n < (0 ## (Suc \<circ> f)) (Suc k)" for k n
      using 0 3 that by (cases k; cases n) (force)+
  qed
  lemma stutter_extend_build:
    assumes "u \<approx> v"
    shows "a ## u \<approx> a ## v"
  proof -
    obtain f g where 1: "stutter_sampler f u" "stutter_sampler g v" "u \<circ> f = v \<circ> g"
      using stutter_equivE assms by this
    show ?thesis
    proof (intro stutter_equivI ext)
      show "stutter_sampler (0 ## (Suc \<circ> f)) (a ## u)" using stutter_sampler_build 1(1) by this
      show "stutter_sampler (0 ## (Suc \<circ> g)) (a ## v)" using stutter_sampler_build 1(2) by this
      show "(a ## u \<circ> 0 ## (Suc \<circ> f)) i = (a ## v \<circ> 0 ## (Suc \<circ> g)) i" for i
        using fun_cong[OF 1(3)] by (cases i) (auto)
    qed
  qed
  lemma stutter_extend_concat:
    assumes "u \<approx> v"
    shows "w \<frown> u \<approx> w \<frown> v"
    using stutter_extend_build assms by (induct w, force+)
  lemma build_stutter: "w 0 ## w \<approx> w"
  proof (rule stutter_equivI)
    show "stutter_sampler (Suc (0 := 0)) (w 0 ## w)"
    unfolding stutter_sampler_def
    proof safe
      show "(Suc (0 := 0)) 0 = 0" by simp
      show "strict_mono (Suc (0 := 0))" by (rule strict_monoI, simp)
    next
      fix k n
      assume 1: "(Suc (0 := 0)) k < n" "n < (Suc (0 := 0)) (Suc k)"
      show "(w 0 ## w) n = (w 0 ## w) ((Suc (0 := 0)) k)" using 1 by (cases n, auto)
    qed
    show "stutter_sampler id w" by rule
    show "w 0 ## w \<circ> (Suc (0 := 0)) = w \<circ> id" by auto
  qed
  lemma replicate_stutter: "replicate n (v 0) \<frown> v \<approx> v"
  proof (induct n)
    case 0
    show ?case using stutter_equiv_refl by simp
  next
    case (Suc n)
    have "replicate (Suc n) (v 0) \<frown> v = v 0 ## replicate n (v 0) \<frown> v" by simp
    also have "\<dots> = (replicate n (v 0) \<frown> v) 0 ## replicate n (v 0) \<frown> v" by (cases n, auto)
    also have "\<dots> \<approx> replicate n (v 0) \<frown> v" using build_stutter by this
    also have "\<dots> \<approx> v" using Suc by this
    finally show ?case by this
  qed

  lemma replicate_stutter': "u \<frown> replicate n (v 0) \<frown> v \<approx> u \<frown> v"
    using stutter_extend_concat replicate_stutter by this

end