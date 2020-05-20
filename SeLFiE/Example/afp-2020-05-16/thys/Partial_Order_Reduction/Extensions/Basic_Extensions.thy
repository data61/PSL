section \<open>Basics\<close>

theory Basic_Extensions
imports "HOL-Library.Infinite_Set"
begin

  subsection \<open>Types\<close>

    type_synonym 'a step = "'a \<Rightarrow> 'a"

  subsection \<open>Rules\<close>

    declare less_imp_le[dest, simp]
  
    declare le_funI[intro]
    declare le_funE[elim]
    declare le_funD[dest]
  
    lemma IdI'[intro]:
      assumes "x = y"
      shows "(x, y) \<in> Id"
      using assms by auto

    lemma (in order) order_le_cases:
      assumes "x \<le> y"
      obtains (eq) "x = y" | (lt) "x < y"
      using assms le_less by auto  

    lemma (in linorder) linorder_cases':
      obtains (le) "x \<le> y" | (gt) "x > y"
      by force
  
    lemma monoI_comp[intro]:
      assumes "mono f" "mono g"
      shows "mono (f \<circ> g)"
      using assms by (intro monoI, auto dest: monoD)
    lemma strict_monoI_comp[intro]:
      assumes "strict_mono f" "strict_mono g"
      shows "strict_mono (f \<circ> g)"
      using assms by (intro strict_monoI, auto dest: strict_monoD)

    lemma eq_le_absorb[simp]:
      fixes x y :: "'a :: order"
      shows "x = y \<and> x \<le> y \<longleftrightarrow> x = y" "x \<le> y \<and> x = y \<longleftrightarrow> x = y"
      by auto

    lemma INFM_Suc[simp]: "(\<exists>\<^sub>\<infinity> i. P (Suc i)) \<longleftrightarrow> (\<exists>\<^sub>\<infinity> i. P i)"
      unfolding INFM_nat using Suc_lessE less_Suc_eq by metis
    lemma INFM_plus[simp]: "(\<exists>\<^sub>\<infinity> i. P (i + n :: nat)) \<longleftrightarrow> (\<exists>\<^sub>\<infinity> i. P i)"
    proof (induct n)
      case 0
      show ?case by simp
    next
      case (Suc n)
      have "(\<exists>\<^sub>\<infinity> i. P (i + Suc n)) \<longleftrightarrow> (\<exists>\<^sub>\<infinity> i. P (Suc i + n))" by simp
      also have "\<dots> \<longleftrightarrow> (\<exists>\<^sub>\<infinity> i. P (i + n))" using INFM_Suc by this
      also have "\<dots> \<longleftrightarrow> (\<exists>\<^sub>\<infinity> i. P i)" using Suc by this
      finally show ?case by this
    qed
    lemma INFM_minus[simp]: "(\<exists>\<^sub>\<infinity> i. P (i - n :: nat)) \<longleftrightarrow> (\<exists>\<^sub>\<infinity> i. P i)"
    proof (induct n)
      case 0
      show ?case by simp
    next
      case (Suc n)
      have "(\<exists>\<^sub>\<infinity> i. P (i - Suc n)) \<longleftrightarrow> (\<exists>\<^sub>\<infinity> i. P (Suc i - Suc n))" using INFM_Suc by meson
      also have "\<dots> \<longleftrightarrow> (\<exists>\<^sub>\<infinity> i. P (i - n))" by simp
      also have "\<dots> \<longleftrightarrow> (\<exists>\<^sub>\<infinity> i. P i)" using Suc by this
      finally show ?case by this
    qed

  subsection \<open>Constants\<close>

    definition const :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"
      where "const x \<equiv> \<lambda> _. x"
    definition const2 :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a"
      where "const2 x \<equiv> \<lambda> _ _. x"
    definition const3 :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'a"
      where "const3 x \<equiv> \<lambda> _ _ _. x"
    definition const4 :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'a"
      where "const4 x \<equiv> \<lambda> _ _ _ _. x"
    definition const5 :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'a"
      where "const5 x \<equiv> \<lambda> _ _ _ _ _. x"
  
    lemma const_apply[simp]: "const x y = x" unfolding const_def by rule
    lemma const2_apply[simp]: "const2 x y z = x" unfolding const2_def by rule
    lemma const3_apply[simp]: "const3 x y z u = x" unfolding const3_def by rule
    lemma const4_apply[simp]: "const4 x y z u v = x" unfolding const4_def by rule
    lemma const5_apply[simp]: "const5 x y z u v w = x" unfolding const5_def by rule

    definition zip_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'c" (infixr "\<parallel>" 51)
      where "f \<parallel> g \<equiv> \<lambda> x. (f x, g x)"
  
    lemma zip_fun_simps[simp]:
      "(f \<parallel> g) x = (f x, g x)"
      "fst \<circ> (f \<parallel> g) = f"
      "snd \<circ> (f \<parallel> g) = g"
      "fst \<circ> h \<parallel> snd \<circ> h = h"
      "fst ` range (f \<parallel> g) = range f"
      "snd ` range (f \<parallel> g) = range g"
      unfolding zip_fun_def by force+
  
    lemma zip_fun_eq[dest]:
      assumes "f \<parallel> g = h \<parallel> i"
      shows "f = h" "g = i"
      using assms unfolding zip_fun_def by (auto dest: fun_cong)
  
    lemma zip_fun_range_subset[intro, simp]: "range (f \<parallel> g) \<subseteq> range f \<times> range g"
      unfolding zip_fun_def by blast
    lemma zip_fun_range_finite[elim]:
      assumes "finite (range (f \<parallel> g))"
      obtains "finite (range f)" "finite (range g)"
    proof
      show "finite (range f)" using finite_imageI [OF assms(1), of fst]
        by (simp add: image_image)
      show "finite (range g)" using finite_imageI [OF assms(1), of snd]
        by (simp add: image_image)
    qed
  
    lemma zip_fun_split:
      obtains f g
      where "h = f \<parallel> g"
    proof
      show "h = fst \<circ> h \<parallel> snd \<circ> h" by simp
    qed
  
    abbreviation "None_None \<equiv> (None, None)"
    abbreviation "None_Some \<equiv> \<lambda> (y). (None, Some y)"
    abbreviation "Some_None \<equiv> \<lambda> (x). (Some x, None)"
    abbreviation "Some_Some \<equiv> \<lambda> (x, y). (Some x, Some y)"
  
    abbreviation "None_None_None \<equiv> (None, None, None)"
    abbreviation "None_None_Some \<equiv> \<lambda> (z). (None, None, Some z)"
    abbreviation "None_Some_None \<equiv> \<lambda> (y). (None, Some y, None)"
    abbreviation "None_Some_Some \<equiv> \<lambda> (y, z). (None, Some y, Some z)"
    abbreviation "Some_None_None \<equiv> \<lambda> (x). (Some x, None, None)"
    abbreviation "Some_None_Some \<equiv> \<lambda> (x, z). (Some x, None, Some z)"
    abbreviation "Some_Some_None \<equiv> \<lambda> (x, y). (Some x, Some y, None)"
    abbreviation "Some_Some_Some \<equiv> \<lambda> (x, y, z). (Some x, Some y, Some z)"

    lemma inj_Some2[simp, intro]:
      "inj None_Some"
      "inj Some_None"
      "inj Some_Some"
      by (rule injI, force)+
  
    lemma inj_Some3[simp, intro]:
      "inj None_None_Some"
      "inj None_Some_None"
      "inj None_Some_Some"
      "inj Some_None_None"
      "inj Some_None_Some"
      "inj Some_Some_None"
      "inj Some_Some_Some"
      by (rule injI, force)+
  
    definition swap :: "'a \<times> 'b \<Rightarrow> 'b \<times> 'a"
      where "swap x \<equiv> (snd x, fst x)"
  
    lemma swap_simps[simp]: "swap (a, b) = (b, a)" unfolding swap_def by simp
    lemma swap_inj[intro, simp]: "inj swap" by (rule injI, auto)
    lemma swap_surj[intro, simp]: "surj swap" by (rule surjI[where ?f = swap], auto)
    lemma swap_bij[intro, simp]: "bij swap" by (rule bijI, auto)
  
    definition push :: "('a \<times> 'b) \<times> 'c \<Rightarrow> 'a \<times> 'b \<times> 'c"
      where "push x \<equiv> (fst (fst x), snd (fst x), snd x)"
    definition pull :: "'a \<times> 'b \<times> 'c \<Rightarrow> ('a \<times> 'b) \<times> 'c"
      where "pull x \<equiv> ((fst x, fst (snd x)), snd (snd x))"
  
    lemma push_simps[simp]: "push ((x, y), z) = (x, y, z)" unfolding push_def by simp
    lemma pull_simps[simp]: "pull (x, y, z) = ((x, y), z)" unfolding pull_def by simp

    definition label :: "'vertex \<times> 'label \<times> 'vertex \<Rightarrow> 'label"
      where "label \<equiv> fst \<circ> snd"
  
    lemma label_select[simp]: "label (p, a, q) = a" unfolding label_def by simp

  subsection \<open>Theorems for @term{curry} and @term{split}\<close>

    lemma curry_split[simp]: "curry \<circ> case_prod = id" by auto
    lemma split_curry[simp]: "case_prod \<circ> curry = id" by auto
  
    lemma curry_le[simp]: "curry f \<le> curry g \<longleftrightarrow> f \<le> g" unfolding le_fun_def by force
    lemma split_le[simp]: "case_prod f \<le> case_prod g \<longleftrightarrow> f \<le> g" unfolding le_fun_def by force
  
    lemma mono_curry_left[simp]: "mono (curry \<circ> h) \<longleftrightarrow> mono h"
      unfolding mono_def by fastforce
    lemma mono_split_left[simp]: "mono (case_prod \<circ> h) \<longleftrightarrow> mono h"
      unfolding mono_def by fastforce
    lemma mono_curry_right[simp]: "mono (h \<circ> curry) \<longleftrightarrow> mono h"
      unfolding mono_def split_le[symmetric] by bestsimp
    lemma mono_split_right[simp]: "mono (h \<circ> case_prod) \<longleftrightarrow> mono h"
      unfolding mono_def curry_le[symmetric] by bestsimp
  
    lemma Collect_curry[simp]: "{x. P (curry x)} = case_prod ` {x. P x}" using image_Collect by fastforce
    lemma Collect_split[simp]: "{x. P (case_prod x)} = curry ` {x. P x}" using image_Collect by force
  
    lemma gfp_split_curry[simp]: "gfp (case_prod \<circ> f \<circ> curry) = case_prod (gfp f)"
    proof -
      have "gfp (case_prod \<circ> f \<circ> curry) = Sup {u. u \<le> case_prod (f (curry u))}" unfolding gfp_def by simp
      also have "\<dots> = Sup {u. curry u \<le> curry (case_prod (f (curry u)))}" unfolding curry_le by simp
      also have "\<dots> = Sup {u. curry u \<le> f (curry u)}" by simp
      also have "\<dots> = Sup (case_prod ` {u. u \<le> f u})" unfolding Collect_curry[of "\<lambda> u. u \<le> f u"] by simp
      also have "\<dots> = case_prod (Sup {u. u \<le> f u})" by (force simp add: image_comp)
      also have "\<dots> = case_prod (gfp f)" unfolding gfp_def by simp
      finally show ?thesis by this
    qed
    lemma gfp_curry_split[simp]: "gfp (curry \<circ> f \<circ> case_prod) = curry (gfp f)"
    proof -
      have "gfp (curry \<circ> f \<circ> case_prod) = Sup {u. u \<le> curry (f (case_prod u))}" unfolding gfp_def by simp
      also have "\<dots> = Sup {u. case_prod u \<le> case_prod (curry (f (case_prod u)))}" unfolding split_le by simp
      also have "\<dots> = Sup {u. case_prod u \<le> f (case_prod u)}" by simp
      also have "\<dots> = Sup (curry ` {u. u \<le> f u})" unfolding Collect_split[of "\<lambda> u. u \<le> f u"] by simp
      also have "\<dots> = curry (Sup {u. u \<le> f u})" by (force simp add: image_comp)
      also have "\<dots> = curry (gfp f)" unfolding gfp_def by simp
      finally show ?thesis by this
    qed

    lemma not_someI:
      assumes "\<And> x. P x \<Longrightarrow> False"
      shows "\<not> P (SOME x. P x)"
      using assms by blast
    lemma some_ccontr:
      assumes "(\<And> x. \<not> P x) \<Longrightarrow> False"
      shows "P (SOME x. P x)"
      using assms someI_ex ccontr by metis

end