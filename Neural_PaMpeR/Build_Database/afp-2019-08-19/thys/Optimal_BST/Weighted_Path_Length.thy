(* Author: Tobias Nipkow *)

section "Weighted Path Length of BST"

theory Weighted_Path_Length
imports "HOL-Library.Tree"
begin

text \<open>This theory presents two definitions of the \emph{weighted path length} of a BST,
the objective function we want to minimize,
and proves them equivalent. Function \<open>Wpl\<close> is the intuitive global definition
that sums \<open>a\<close> over all leaves and \<open>b\<close> over all nodes, taking their depth (= number of
comparisons to reach that point) into account. Function \<open>wpl\<close> is a recursive definition
and thus suitable for the later dynamic programming approaches
to building a BST with the minimal weighted path length.
\<close>

lemma inorder_upto_split:
  assumes "inorder \<langle>l,k,r\<rangle> = [i..j]"
  shows "inorder l = [i..k-1]" "inorder r = [k+1..j]" "i \<le> k" "k \<le> j"
proof -
  have k: "k\<in>set[i..j]" using assms by (metis set_inorder tree.set_intros(2))
  have "[i..k-1] @ k # [k+1..j] = [i..j]"
    using k upto_rec1 upto_split1 by (metis atLeastAtMost_iff set_upto)
  also have "\<dots> = inorder l @ k # inorder r" using assms by auto
  finally have "inorder l = [i..k-1] \<and> inorder r = [k+1..j]" (is "?A \<and> ?B")
    by(auto simp: append_Cons_eq_iff)
  thus ?A ?B by auto
  show "i \<le> k" "k \<le> j" using k by auto
qed

fun incr2 :: "int \<times> nat \<Rightarrow> int \<times> nat" where
"incr2 (x,n) = (x, n + 1)"

fun leaves :: "int \<Rightarrow> int tree \<Rightarrow> (int * nat) set" where
"leaves i Leaf = {(i,0)}" |
"leaves i (Node l k r) = incr2 ` (leaves i l \<union> leaves (k+1) r)"

fun nodes :: "int tree \<Rightarrow> (int * nat) set" where
"nodes Leaf = {}" |
"nodes (Node l k r) = {(k,1)} \<union> incr2 ` (nodes l \<union> nodes r)"

lemma finite_nodes: "finite (nodes t)"
by(induction t) auto

lemma finite_leaves: "finite (leaves i t)"
by(induction i t rule: leaves.induct) auto

lemma notin_nodes0: "(k, 0) \<notin> nodes t"
by(induction t) auto

lemma sum_incr2: "sum f (incr2 ` A) = sum (\<lambda>xy. f(fst xy,snd xy+1)) A"
proof -
  have "sum f (incr2 ` A) = sum (f o incr2) A"
    by(subst sum.reindex)(auto simp: inj_on_def)
  also have "f o incr2 = (\<lambda>xy. f(fst xy,snd xy+1))"
    by(auto simp: fun_eq_iff)
  finally show ?thesis by simp
qed

lemma fst_nodes: "fst ` nodes t = set_tree t"
apply(induction t)
 apply simp
apply (fastforce simp: image_def set_eq_iff ball_Un)
done

lemma fst_leaves: "\<lbrakk> inorder t = [i..j]; i \<le> j+1\<rbrakk> \<Longrightarrow> fst ` leaves i t = {i..j+1}"
proof(induction t arbitrary: i j)
  case Leaf
  then show ?case by auto
next
  case (Node t1 k t2)
  note inorder = inorder_upto_split[OF Node.prems(1)]
  show ?case
    using  Node.IH(1)[OF inorder(1)] Node.IH(2)[OF inorder(2)] inorder(3,4) Node.prems(2)
    by (fastforce simp: image_def set_eq_iff bex_Un)
qed

lemma sum_leaves: "\<lbrakk> inorder t = [i..j];  i \<le> j+1 \<rbrakk> \<Longrightarrow>
  (\<Sum>x\<in>leaves i t. (f(fst x) :: nat)) = sum f {i..j+1}"
proof(induction t arbitrary: i j)
  case Leaf
  hence "i = j+1" by simp
  thus ?case by simp
next
  case (Node l k r)
  note inorder = inorder_upto_split[OF Node.prems(1)]
  let ?Ll = "leaves i l" let ?Lr = "leaves (k+1) r" let ?L = "?Ll \<union> ?Lr"
  have "fst ` ?Ll \<inter> fst ` ?Lr = {}" using inorder
    by(simp add: fst_leaves del: set_inorder add: set_inorder[symmetric])
  hence l0: "?Ll \<inter> ?Lr = {}" by auto
  have "{i..j+1} = {i..k} \<union> {k+1..j+1}" using inorder(3,4) by auto 
  thus ?case
    using Node.IH(1)[OF inorder(1)] Node.IH(2)[OF inorder(2)] inorder(3,4) Node.prems(2)
    by(simp add: sum_incr2 sum_Un_nat finite_leaves l0)
qed

lemma sum_nodes: "inorder t = [i..j] \<Longrightarrow>
  (\<Sum>xy\<in>nodes t. (f(fst xy) :: nat)) = sum f {i..j}"
proof(induction t arbitrary: i j)
  case Leaf thus ?case by simp
next
  case (Node l k r)
  note inorder = inorder_upto_split[OF Node.prems(1)]
  let ?Nl = "nodes l" let ?Nr = "nodes r" let ?N = "?Nl \<union> ?Nr"
  have "(fst ` ?Nl) \<inter> (fst ` ?Nr) = {}" using inorder(1,2)
    by(simp add: fst_nodes del: set_inorder add: set_inorder[symmetric])
  hence n0: "?Nl \<inter> ?Nr = {}" by auto
  have "(\<Sum>xy\<in>nodes(Node l k r). (f (fst xy) :: nat))
    = (\<Sum>xy\<in>insert (k, Suc 0) (incr2 ` (nodes l \<union> nodes r)). f(fst xy))"
    by(simp)
  also have "\<dots> = f k + (\<Sum>xy\<in>(incr2 ` (nodes l \<union> nodes r)). f(fst xy))"
    by(subst sum.insert, auto simp: finite_nodes notin_nodes0)
  also have "\<dots> = sum f {i..j}"
  proof -
    have "{i..j} = {i..k-1} \<union> {k} \<union> {k+1..j}" using inorder(3,4) by auto 
    thus ?thesis
      using Node.IH(1)[OF inorder(1)] Node.IH(2)[OF inorder(2)] inorder(3,4)
      by(simp add: sum_incr2 sum_Un_nat finite_nodes n0)
  qed
  finally show ?case .
qed

locale wpl =
fixes w :: "int \<Rightarrow> int \<Rightarrow> nat"
begin

fun wpl :: "int \<Rightarrow> int \<Rightarrow> int tree \<Rightarrow> nat" where
"wpl i j Leaf = 0" |
"wpl i j (Node l k r) = wpl i (k-1) l + wpl (k+1) j r + w i j"

end

locale Wpl =
fixes a b :: "int \<Rightarrow> nat"
begin

definition Wpl :: "int \<Rightarrow> int tree \<Rightarrow> nat" where
"Wpl i t = sum (\<lambda>(k,c). c * b k) (nodes t) + sum (\<lambda>(k,c). c * a k) (leaves i t)"

definition w :: "int \<Rightarrow> int \<Rightarrow> nat" where
"w i j = sum a {i..j+1} + sum b {i..j}"

sublocale wpl where w = w .

lemma "inorder t = [i..j] \<Longrightarrow> wpl i j t = Wpl i t"
proof(induction t arbitrary: i j)
  case Leaf thus ?case by(simp add: Wpl_def)
next
  case (Node l k r)
  let ?b = "\<lambda>(k,c). c * b k" let ?a = "\<lambda>(k,c). c * a k"
  note inorder = inorder_upto_split[OF Node.prems]
  let ?Nl = "nodes l" let ?Nr = "nodes r" let ?N = "?Nl \<union> ?Nr"
  let ?Ll = "leaves i l" let ?Lr = "leaves (k+1) r" let ?L = "?Ll \<union> ?Lr"
  have "(fst ` ?Nl) \<inter> (fst ` ?Nr) = {}" using inorder(1,2)
    by(simp add: fst_nodes del: set_inorder add: set_inorder[symmetric])
  hence n0: "?Nl \<inter> ?Nr = {}" by auto
  have "fst ` ?Ll \<inter> fst ` ?Lr = {}" using inorder
    by(simp add: fst_leaves del: set_inorder add: set_inorder[symmetric])
  hence l0: "?Ll \<inter> ?Lr = {}" by auto
  have "wpl i j (Node l k r) =  Wpl i l + Wpl (k + 1) r + w i j"
    using Node.IH inorder by(simp)
  also have "\<dots> = sum ?b (nodes l) + sum ?a (leaves i l) +
    sum ?b (nodes r) + sum ?a (leaves (k+1) r) + w i j"
    by (simp add: Wpl_def)
  also have "\<dots> = (sum ?b (nodes l) + sum ?b (nodes r))
    + (sum ?a (leaves i l) + sum ?a (leaves (k+1) r)) + w i j"
    by(simp add: algebra_simps)
  also have "\<dots> = sum ?b ?N + sum ?a ?L + w i j"
    by(simp add: sum_Un_nat finite_nodes finite_leaves l0 n0)
  also have "\<dots> = sum ?b ?N + sum ?a ?L + sum a {i..j+1} + sum b {i..j}"
    by (simp add: w_def)
  also have "\<dots> = sum ?b ?N + sum b {i..j} + (sum ?a ?L + sum a {i..j+1})"
    by(simp add: algebra_simps)
  also have "sum ?a ?L + sum a {i..j+1} = sum ?a (incr2 ` ?L)"
  proof -
    have "{i..j+1} = {i..k} \<union> {k+1..j+1}" using inorder(3,4) by auto 
    thus ?thesis using inorder(3,4)
      by (simp add: sum_incr2 split_def sum.distrib sum_Un_nat finite_leaves l0
        sum_leaves[OF inorder(1)] sum_leaves[OF inorder(2)])
  qed
  also have "sum ?b ?N + sum b {i..j}
     = sum ?b ?N + sum b ({i..k-1} \<union> {k+1..j}) + b k"
  proof -
    have "{i..j} = {k} \<union> {i..k-1} \<union> {k+1..j}" using inorder(3,4) by auto 
    thus ?thesis by simp
  qed
  also have "sum ?b ?N + sum b ({i..k-1} \<union> {k+1..j}) = sum ?b (incr2 ` ?N)"
    by (simp add: sum_incr2 split_def sum.distrib sum_Un_nat finite_nodes n0
        sum_nodes[OF inorder(1)] sum_nodes[OF inorder(2)])
  also have "sum ?b (incr2 ` ?N) + b k = sum ?b ({(k,1)} \<union> incr2 ` ?N)"
    by(simp, subst sum.insert, auto simp add: finite_nodes notin_nodes0)
  also have "sum ?b ({(k,1)} \<union> incr2 ` ?N) + sum ?a (incr2 ` ?L) = Wpl i \<langle>l,k,r\<rangle>"
    by(simp add: Wpl_def)
  finally show ?case .
qed

end

end