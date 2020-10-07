(* Author: Tobias Nipkow *)

section \<open>Weight-Balanced Trees Have Logarithmic Height\<close>

text \<open>This theory is based on the original definition of weight-balanced trees
\cite{NievergeltR72,NievergeltR73}
where the size of the child of a node must be a minimum and a maximum fraction
of the size of the node.\<close>

theory Weight_Balanced_Trees_log
imports
  Complex_Main
  "HOL-Library.Tree"
begin

(* FIXME mod field_simps *)
lemmas neq0_if = less_imp_neq dual_order.strict_implies_not_eq

locale WBT0 =
fixes \<alpha> :: real
assumes alpha_pos: "0 < \<alpha>" and alpha_ub: "\<alpha> \<le> 1/2"
begin

fun wbt :: "'a tree \<Rightarrow> bool" where
"wbt Leaf = True" |
"wbt (Node l _ r) = (wbt l \<and> wbt r \<and> (let ratio = size1 l / (size1 l + size1 r)
  in \<alpha> \<le> ratio \<and> ratio \<le> 1 - \<alpha>))"

lemma height_size1_exp:
  "wbt t \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> 2 \<le> (1-\<alpha>) ^ (height t - 1) * size1 t"
proof(induction  t)
  case Leaf thus ?case by simp
next
  case (Node l a r)
  have 0: "0 \<le> (1 - \<alpha>) ^ k" for k using alpha_ub by simp
  let ?t = "Node l a r" let ?s = "size1 ?t"
  from Node.prems(1) have 1: "size1 l \<le> (1-\<alpha>) * ?s" and 2: "size1 r \<le> (1-\<alpha>) * ?s"
    by (auto simp: Let_def field_simps add_pos_pos neq0_if)
  show ?case
  proof (cases "l = Leaf \<and> r = Leaf")
    case True thus ?thesis by simp
  next
    case not_Leafs: False
    show ?thesis
    proof (cases "height l \<le> height r")
      case hlr: True
      hence r: "r \<noteq> Leaf" and hr: "height r \<noteq> 0" using not_Leafs by (auto)
      have "2 \<le> (1-\<alpha>) ^ (height r - 1) * size1 r"
        using Node.IH(2)[OF _ r] Node.prems by simp
      also have "\<dots> \<le> (1-\<alpha>) ^ (height r - 1) * ((1-\<alpha>) * ?s)"
        by(rule mult_left_mono[OF 2 0])
      also have "\<dots> = (1-\<alpha>) ^ (height r - 1 + 1) * ?s" by simp
      also have "\<dots> = (1-\<alpha>) ^ (height r) * ?s"
        using hr by (auto simp del: eq_height_0)
      finally show ?thesis using hlr by (simp)
    next
      case hlr: False
      hence l: "l \<noteq> Leaf" and hl: "height l \<noteq> 0" using not_Leafs by (auto)
      have "2 \<le> (1-\<alpha>) ^ (height l - 1) * size1 l"
        using Node.IH(1)[OF _ l] Node.prems by simp
      also have "\<dots> \<le> (1-\<alpha>) ^ (height l - 1) * ((1-\<alpha>) * ?s)"
        by(rule mult_left_mono[OF 1 0])
      also have "\<dots> = (1-\<alpha>) ^ (height l - 1 + 1) * ?s" by simp
      also have "\<dots> = (1-\<alpha>) ^ (height l) * ?s"
        using hl by (auto simp del: eq_height_0)
      finally show ?thesis using hlr by (simp)
    qed
  qed
qed

lemma height_size1_log: assumes "wbt t" "t \<noteq> Leaf"
shows "height t \<le> (log 2 (size1 t) - 1) / log 2 (1/(1-\<alpha>)) + 1"
proof -
  have "1 \<le> log 2 ((1-\<alpha>) ^ (height t - 1) * size1 t)"
    using height_size1_exp[OF assms] by simp
  hence "1 \<le> log 2 ((1-\<alpha>) ^ (height t - 1)) + log 2 (size1 t)"
    using alpha_ub by(simp add: log_mult)
  hence "1 \<le> (height t - 1) * log 2 (1-\<alpha>) + log 2 (size1 t)"
    using alpha_ub by(simp add: log_nat_power)
  hence "- (height t - 1) * log 2 (1-\<alpha>) \<le> log 2 (size1 t) - 1"
    by(simp add: algebra_simps)
  hence "(height t - 1) * log 2 (1/(1-\<alpha>)) \<le> log 2 (size1 t) - 1"
    using alpha_ub by(simp add: log_divide)
  hence "height t - 1 \<le> (log 2 (size1 t) - 1) / log 2 (1/(1-\<alpha>))"
    using alpha_pos alpha_ub by(simp add: field_simps log_divide)
  thus ?thesis by(simp)
qed

end

end
