(* Author: Julian Brunner *)
(* This is originally a part of the CAVA model checker *)
theory Basic
imports
  Main
begin

  abbreviation (input) "const x \<equiv> \<lambda> _. x"

  lemma infinite_subset[trans]: "infinite A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> infinite B" using infinite_super by this
  lemma finite_subset[trans]: "A \<subseteq> B \<Longrightarrow> finite B \<Longrightarrow> finite A" using finite_subset by this

  declare infinite_coinduct[case_names infinite, coinduct pred: infinite]
  lemma infinite_psubset_coinduct[case_names infinite, consumes 1]:
    assumes "R A"
    assumes "\<And> A. R A \<Longrightarrow> \<exists> B \<subset> A. R B"
    shows "infinite A"
  proof
    assume "finite A"
    then show "False" using assms by (induct rule: finite_psubset_induct) (auto)
  qed

  lemma GreatestI:
    fixes k :: nat
    assumes "P k" "\<And> k. P k \<Longrightarrow> k \<le> l"
    shows "P (GREATEST k. P k)"
  proof (rule GreatestI_nat, safe)
    show "P k" using assms(1) by this
    show "k \<le> l" if "P k" for k using assms(2) that by force
  qed
  lemma Greatest_le:
    fixes k :: nat
    assumes "P k" "\<And> k. P k \<Longrightarrow> k \<le> l"
    shows "k \<le> (GREATEST k. P k)"
  proof (rule Greatest_le_nat, safe)
    show "P k" using assms(1) by this
    show "k \<le> l" if "P k" for k using assms(2) that by force
  qed
  lemma Greatest_not_less:
    fixes k :: nat
    assumes "k > (GREATEST k. P k)" "\<And> k. P k \<Longrightarrow> k \<le> l"
    shows "\<not> P k"
  proof
    assume 1: "P k"
    have 2: "k \<le> (GREATEST k. P k)" using Greatest_le 1 assms(2) by this
    show "False" using assms(1) 2 by auto
  qed

  lemma finite_set_of_finite_maps':
    assumes "finite A" "finite B"
    shows "finite {m. dom m \<subseteq> A \<and> ran m \<subseteq> B}"
  proof -
    have "{m. dom m \<subseteq> A \<and> ran m \<subseteq> B} = (\<Union> \<A> \<in> Pow A. {m. dom m = \<A> \<and> ran m \<subseteq> B})" by auto
    also have "finite \<dots>" using finite_subset assms by (auto intro: finite_set_of_finite_maps)
    finally show ?thesis by this
  qed

  primrec alternate :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)" where
    "alternate f g 0 = id" | "alternate f g (Suc k) = alternate g f k \<circ> f"

  lemma alternate_Suc[simp]: "alternate f g (Suc k) = (if even k then f else g) \<circ> alternate f g k"
  proof (induct k arbitrary: f g)
    case (0)
    show ?case by simp
  next
    case (Suc k)
    have "alternate f g (Suc (Suc k)) = alternate g f (Suc k) \<circ> f" by auto
    also have "\<dots> = (if even k then g else f) \<circ> (alternate g f k \<circ> f)" unfolding Suc by auto
    also have "\<dots> = (if even (Suc k) then f else g) \<circ> alternate f g (Suc k)" by auto
    finally show ?case by this
  qed

  declare alternate.simps(2)[simp del]

  lemma alternate_antimono:
    assumes "\<And> x. f x \<le> x" "\<And> x. g x \<le> x"
    shows "antimono (alternate f g)"
  proof
    fix k l :: nat
    assume 1: "k \<le> l"
    obtain n where 2: "l = k + n" using le_Suc_ex 1 by auto
    have 3: "alternate f g (k + n) \<le> alternate f g k"
    proof (induct n)
      case (0)
      show ?case by simp
    next
      case (Suc n)
      have "alternate f g (k + Suc n) \<le> alternate f g (k + n)" using assms by (auto intro: le_funI)
      also have "\<dots> \<le> alternate f g k" using Suc by this
      finally show ?case by this
    qed
    show "alternate f g l \<le> alternate f g k" using 3 unfolding 2 by this
  qed

end
