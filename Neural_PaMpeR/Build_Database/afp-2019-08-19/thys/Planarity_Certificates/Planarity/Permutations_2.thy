theory Permutations_2
imports
  "HOL-Library.Permutations"
  Executable_Permutations
  Graph_Theory.Funpow
begin

section \<open>Modifying Permutations\<close>

abbreviation funswapid :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<rightleftharpoons>\<^sub>F" 90) where
  "x \<rightleftharpoons>\<^sub>F y \<equiv> Fun.swap x y id"

definition perm_swap :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "perm_swap x y f \<equiv> x \<rightleftharpoons>\<^sub>F y o f o x \<rightleftharpoons>\<^sub>F y"

definition perm_rem :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "perm_rem x f \<equiv> if f x \<noteq> x then x \<rightleftharpoons>\<^sub>F f x o f else f"


text \<open>
  An example:

  @{lemma "perm_rem (2 :: nat) (list_succ [1,2,3,4]) x = list_succ [1,3,4] x"
      by (auto simp: perm_rem_def Fun.swap_def list_succ_def)}
\<close>

lemma perm_swap_id[simp]: "perm_swap a b id = id"
  by (auto simp: perm_swap_def)
  
lemma perm_rem_permutes:
  assumes "f permutes S \<union> {x}"
  shows "perm_rem x f permutes S"
  using assms by (auto simp: permutes_def perm_rem_def) (metis swap_id_eq)+

lemma perm_rem_same:
  assumes "bij f" "f y = y" shows "perm_rem x f y = f y"
  using assms by (auto simp: perm_rem_def swap_id_eq bij_iff)

lemma perm_rem_simps:
  assumes "bij f"
  shows
  "x = y \<Longrightarrow> perm_rem x f y = x"
  "f y = x \<Longrightarrow> perm_rem x f y = f x"
  "y \<noteq> x \<Longrightarrow> f y \<noteq> x \<Longrightarrow> perm_rem x f y = f y"
  using assms
  apply (auto simp: perm_rem_def )
  by (metis bij_iff id_apply swap_apply(3))

lemma bij_swap_compose: "bij (x \<rightleftharpoons>\<^sub>F y o f) \<longleftrightarrow> bij f"
  by (metis UNIV_I bij_betw_comp_iff2 bij_betw_id bij_swap_iff subsetI)

lemma bij_perm_rem[simp]: "bij (perm_rem x f) \<longleftrightarrow> bij f"
  by (simp add: perm_rem_def bij_swap_compose)

lemma perm_rem_conv: "\<And>f x y. bij f \<Longrightarrow> perm_rem x f y = (
    if x = y then x
    else if f y = x then f (f y)
    else f y)"
  by (auto simp: perm_rem_simps)

lemma perm_rem_commutes:
  assumes "bij f" shows "perm_rem a (perm_rem b f) = perm_rem b (perm_rem a f)"
proof -
  have bij_simp: "\<And>x y. f x = f y \<longleftrightarrow> x = y"
    using assms by (auto simp: bij_iff)
  show ?thesis using assms by (auto simp: perm_rem_conv bij_simp fun_eq_iff)
qed

lemma perm_rem_id[simp]: "perm_rem a id = id"
  by (simp add: perm_rem_def)

lemma bij_eq_iff:
  assumes "bij f" shows "f x = f y \<longleftrightarrow> x = y"
  using assms by (metis bij_iff) 

lemma swap_swap_id[simp]: "(x \<rightleftharpoons>\<^sub>F y) ((x \<rightleftharpoons>\<^sub>F y) z) = z"
  by (simp add: swap_id_eq)

lemma in_funswapid_image_iff: "\<And>a b x S. x \<in> (a \<rightleftharpoons>\<^sub>F b) ` S \<longleftrightarrow> (a \<rightleftharpoons>\<^sub>F b) x \<in> S"
  by (metis bij_def bij_id bij_swap_iff inj_image_mem_iff swap_swap_id)

lemma perm_swap_comp: "perm_swap a b (f \<circ> g) x = perm_swap a b f (perm_swap a b g x)"
  by (auto simp: perm_swap_def)

lemma bij_perm_swap_iff[simp]: "bij (perm_swap a b f) \<longleftrightarrow> bij f"
  by (auto simp: perm_swap_def bij_swap_compose bij_comp comp_swap)

lemma funpow_perm_swap: "perm_swap a b f ^^ n = perm_swap a b (f ^^ n)"
  by (induct n) (auto simp: perm_swap_def fun_eq_iff)

lemma orbit_perm_swap: "orbit (perm_swap a b f) x = (a \<rightleftharpoons>\<^sub>F b) ` orbit f ((a \<rightleftharpoons>\<^sub>F b) x)"
  by (auto simp: orbit_altdef funpow_perm_swap) (auto simp: perm_swap_def)

lemma has_dom_perm_swap: "has_dom (perm_swap a b f) S = has_dom f ((a \<rightleftharpoons>\<^sub>F b) ` S)"
  by (auto simp: has_dom_def perm_swap_def inj_image_mem_iff) (metis image_iff swap_swap_id)

lemma perm_restrict_dom_subset:
  assumes "has_dom f A" shows "perm_restrict f A = f"
proof -
  from assms have "\<And>x. x \<notin> A \<Longrightarrow> f x = x" by (auto simp: has_dom_def)
  then show ?thesis by (auto simp: perm_restrict_def fun_eq_iff)
qed

lemma has_domD: "has_dom f S \<Longrightarrow> x \<notin> S \<Longrightarrow> f x = x"
  by (auto simp: has_dom_def)

lemma has_domI: "(\<And>x. x \<notin> S \<Longrightarrow> f x = x) \<Longrightarrow> has_dom f S"
  by (auto simp: has_dom_def)

lemma perm_swap_permutes2:
  assumes "f permutes ((x \<rightleftharpoons>\<^sub>F y) ` S)"
  shows "perm_swap x y f permutes S"
  using assms
  by (auto simp: perm_swap_def permutes_conv_has_dom has_dom_perm_swap[unfolded perm_swap_def])
    (metis bij_swap_iff bij_swap_compose_bij comp_id comp_swap)

section \<open>Cyclic Permutations\<close>

lemma cyclic_on_perm_swap:
  assumes "cyclic_on f S" shows "cyclic_on (perm_swap x y f) ((x \<rightleftharpoons>\<^sub>F y) ` S)"
  using assms by (rule cyclic_on_FOO) (auto simp: perm_swap_def swap_swap_id)

lemma orbit_perm_rem:
  assumes "bij f" "x \<noteq> y" shows "orbit (perm_rem y f) x = orbit f x - {y}" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix z assume "z \<in> ?L"
  then show "z \<in> ?R"
    using assms by induct (auto simp: perm_rem_conv bij_iff intro: orbit.intros)
next
  fix z assume A: "z \<in> ?R"

  { assume "z \<in> orbit f x"
    then have "(z \<noteq> y \<longrightarrow> z \<in> ?L) \<and> (z = y \<longrightarrow> f z \<in> ?L)"
    proof induct
      case base with assms show ?case by (auto intro: orbit_eqI(1) simp: perm_rem_conv)
    next
      case (step z) then show ?case
        using assms by (cases "y = z") (auto intro: orbit_eqI simp: perm_rem_conv)
    qed
  } with A show "z \<in> ?L" by auto
qed

lemma orbit_perm_rem_eq:
  assumes "bij f" shows "orbit (perm_rem y f) x = (if x = y then {y} else orbit f x - {y})"
  using assms by (simp add: orbit_eq_singleton_iff orbit_perm_rem perm_rem_simps)

lemma cyclic_on_perm_rem:
  assumes "cyclic_on f S" "bij f" "S \<noteq> {x}" shows "cyclic_on (perm_rem x f) (S - {x})"
  using assms[unfolded cyclic_on_alldef] by (simp add: cyclic_on_def orbit_perm_rem_eq) auto



end
