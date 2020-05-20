section \<open>Alternating Function Iteration\<close>

theory Alternate
imports Main
begin

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
