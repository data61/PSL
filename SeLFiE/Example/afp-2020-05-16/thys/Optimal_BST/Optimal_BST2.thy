(* Author: Tobias Nipkow, based on work by Daniel Somogyi *)

section \<open>Optimal BSTs: The `Quadratic' Algorithm\label{sec:quadratic}\<close>

theory Optimal_BST2
imports
  Optimal_BST
  Quadrilateral_Inequality
begin

text \<open>Knuth presented an optimization of the previously known cubic dynamic programming algorithm
to a quadratic one. A simplified proof of this optimization was found by Yao~\cite{Yao80}.
Mehlhorn follows Yao closely. The core of the optimization argument is given abstractly
in theory @{theory Optimal_BST.Quadrilateral_Inequality}. In addition we first need to establish some more
properties of @{const argmin}.\<close>

text\<open>An index-based specification of @{const argmin}
expressing that the last minimal list-element is picked:\<close>

lemma argmin_takes_last: "xs \<noteq> [] \<Longrightarrow>
  argmin f xs = xs ! Max {i. i < length xs \<and> (\<forall>x \<in> set xs. f(xs!i) \<le> f x)}"
  (is "_ \<Longrightarrow> _ = _ ! Max (?M xs)")
proof(induction xs)
  case (Cons x xs)
  show ?case
  proof cases
    assume "xs = []" thus ?thesis by(simp cong: conj_cong)
  next
    assume 0: "xs \<noteq> []"
    show ?thesis
    proof cases
      assume 1: "\<forall>u \<in> set xs. f x < f u"
      hence 2: "?M (x#xs) = {0}"
        by (fastforce simp: not_less[symmetric] less_Suc_eq_0_disj)
      have "f x < f (argmin f xs)" using 0 1 argmin_Min[of xs f] by auto
      with 1 Cons.prems show ?case by(subst 2) (auto simp: Let_def)
    next
      assume 1: "\<not>(\<forall>u \<in> set xs. f x < f u)"
      have 2: "\<not> f x < f (argmin f xs)" using 1 argmin_Min[of xs f] 0 by auto
      have "argmin f xs : {u \<in> set xs. \<forall>x\<in>set xs. f u \<le> f x}"
        using 0 argmin_Min[of xs f] by (simp add: argmin_in)
      hence "{u \<in> set xs. \<forall>x\<in>set xs. f u \<le> f x} \<noteq> {}" by blast
      hence ne: "?M xs \<noteq> {}" by(auto simp: in_set_conv_nth)
      have "Max (?M (x#xs)) = Max (?M xs) + 1"
      proof (cases "\<exists>u \<in> set xs. f u < f x")
        case True
        hence "?M (x#xs) = (+) 1 ` ?M xs"
          by (auto simp: nth_Cons' image_def less_Suc_eq_0_disj)
        thus ?thesis
          using mono_Max_commute[of "(+) 1" "?M xs"] ne by (auto simp: mono_def)
      next
        case False
        hence *: "?M (x#xs) = insert 0 ((+) 1 ` ?M xs)"
          using 1 by (auto simp: nth_Cons' image_def less_Suc_eq_0_disj)
        hence "Max (?M (x#xs)) = Max ((+) 1 ` ?M xs)" using Max_insert ne by simp
        thus ?thesis using mono_Max_commute[of "(+) 1" "?M xs"] ne by (auto simp: mono_def)
      qed
      with Cons 2 0 show ?case by auto
    qed
  qed
qed simp

lemma Min_ex: "\<lbrakk> finite F; F \<noteq> {} \<rbrakk> \<Longrightarrow> \<exists>m \<in> F. \<forall>n \<in> F. m \<le> (n::_::linorder)"
using eq_Min_iff[of F "Min F"] by (fastforce)

text \<open>A consequence of @{thm [source] argmin_takes_last}:\<close>

lemma argmin_Max_Args_min_on: assumes [arith]: "i \<le> j"
shows "argmin f [i..j] = Max (Args_min_on f {i..j})"
proof -
  let ?min = "\<lambda>k. \<forall>n \<in> {i..j}. f([i..j]!k) \<le> f n"
  let ?M = "{k. k < nat(j-i+1) \<and> ?min k}"
  let ?Max = "Max ?M"
  have "?M \<noteq> {}" using Min_ex[of "f ` {i..j}"]
    apply(auto simp add: nth_upto)
    apply(rule_tac x="nat (m-i)" in exI)
    by simp
  hence "?Max < nat(j-i+1)" by(simp add: nth_upto)
  hence 1: "i + int ?Max \<le> j" by linarith
  have "argmin f [i..j] = [i..j] ! ?Max"
    using argmin_takes_last[of "[i..j]" f] by simp
  also have "\<dots> = i + int ?Max" using 1 by(simp add: nth_upto)
  also have "\<dots> = i + Max(int ` {k. k < nat(j-i+1) \<and> ?min k})"
    using \<open>?M \<noteq> {}\<close> by (simp add: monoI mono_Max_commute)
  also have "\<dots> = Max ((\<lambda>x. i + x) ` (int ` {k. k < nat(j-i+1) \<and> ?min k}))"
    using \<open>?M \<noteq> {}\<close> by (simp add: monoI mono_Max_commute)
  also have "(\<lambda>x. i + x) ` (int ` {k. k < nat(j-i+1) \<and> ?min k}) =
   {k. is_arg_min_on f {i..j} k}"
    apply(auto simp: is_arg_min_on_def Ball_def nth_upto image_def cong: conj_cong)
    apply(rule_tac x = "x-i" in exI)
    apply auto
    apply(rule_tac x = "nat(x-i)" in exI)
    by auto
   finally show ?thesis by(simp add: Args_min_simps)
qed

text \<open>As a consequence of @{thm [source] argmin_Max_Args_min_on} the following lemma
allows us to justify the restriction of the index range of @{const argmin}
used below in the optimized (quadratic) algorithm.\<close>

lemma argmin_red_ivl:
assumes "i \<le> i'" "argmin f [i..j] \<in> {i'..j'}" "j' \<le> j"
shows "argmin f [i'..j'] = argmin f [i..j]"
proof -
  have ij[arith]: "i \<le> j" using assms by simp
  have ij'[arith]: "i' \<le> j'" using assms by simp
  from Min_ex[of "f ` {i..j}"] have m: "\<exists>m \<in> {i..j}. \<forall>n \<in> {i..j}. f m \<le> f n" by auto
  note * = argmin_Max_Args_min_on[OF ij, of f]
  note ** = argmin_Max_Args_min_on[OF ij', of f]
  let ?M = "Args_min_on f {i..j}"
  let ?M' = "Args_min_on f {i'..j'}"
  have M: "finite ?M" "?M \<noteq> {}"
    using m by (fastforce simp: Args_min_simps simp del: atLeastAtMost_iff)+
  have "Max ?M \<in> ?M" by (simp add: M)
  have "Max ?M \<in> ?M'" using Max_in[OF M] assms * by(auto simp: Args_min_simps)
  have "?M' \<subseteq> ?M" using \<open>Max ?M \<in> ?M\<close> \<open>Max ?M \<in> ?M'\<close> assms(1,3)
    by(force simp add: Args_min_simps Ball_def)
  have "finite ?M'" using M(1) \<open>?M' \<subseteq> ?M\<close> infinite_super by blast
  hence "Max ?M \<le> Max ?M'" by (simp add: \<open>Max ?M \<in> ?M'\<close>)
  have "Max ?M' \<le> Max ?M" using Max.subset_imp[OF \<open>?M' \<subseteq> ?M\<close> _ M(1)] \<open>Max ?M \<in> ?M'\<close> by auto
  thus ?thesis using * ** \<open>Max ?M \<le> Max ?M'\<close> by force
qed

fun root:: "'a tree \<Rightarrow> 'a" where
"root \<langle>_,r,_\<rangle> = r"

text \<open>Now we can formulate and verify the improved algorithm. This requires two
assumptions on the weight function \<open>w\<close>.\<close>

locale Optimal_BST2 = Optimal_BST +
assumes monotone_w: "\<lbrakk>i \<le> i'; i' \<le> j; j \<le> j'\<rbrakk> \<Longrightarrow> w i' j \<le> w i j'"
assumes QI_w: "\<lbrakk>i \<le> i'; i' \<le> j; j \<le> j'\<rbrakk>\<Longrightarrow> w i j + w i' j'\<le> w i' j + w i j'"
begin

text\<open>When finding an optimal tree for @{term "[i..j]"} the optimization consists in reducing
the search for the root from @{term "[i..j]"} to
@{term "[root (opt_bst2 i (j-1)) .. root (opt_bst2 (i+1) j)]"}:\<close>

function opt_bst2 :: "int \<Rightarrow> int \<Rightarrow> int tree" where
"opt_bst2 i j =
  (if i > j then Leaf else
   if i = j then Node Leaf i Leaf else
   let left = root (opt_bst2 i (j-1)) in
   let right= root (opt_bst2 (i+1) j) in
     argmin (wpl i j) [\<langle>opt_bst2 i (k-1), k, opt_bst2 (k+1) j\<rangle>. k \<leftarrow> [left..right]])"
by auto

text \<open>The termination of @{const opt_bst2} is not completely obvious.
We first need to establish some functional properties of the terminating computations.
We start by showing that the root of the returned tree is always between \<open>left\<close> and \<open>right\<close>.
This is essentially equivalent to proving that \<open>left \<le> right\<close>
because otherwise @{const argmin} is applied to \<open>[]\<close>, which is undefined.\<close>

lemma left_le_right:
 "opt_bst2_dom(i,j) \<Longrightarrow>
  (i=j \<longrightarrow> root(opt_bst2 i j) = i) \<and>
  (i<j \<longrightarrow> root(opt_bst2 i j) \<in> {root(opt_bst2 i (j-1)) .. root(opt_bst2 (i+1) j)})"
proof (induction rule: opt_bst2.pinduct)
  case (1 i j)
  let ?left = "root (opt_bst2 i (j-1))"
  let ?right = "root (opt_bst2 (i+1) j)"
  let ?f ="(\<lambda>k. \<langle>opt_bst2 i (k - 1), k, opt_bst2 (k + 1) j\<rangle>)"
  show ?case
  proof cases
    assume "i > j" thus ?thesis by auto
  next
    assume [arith]: "\<not> i > j"
    show ?thesis 
    proof cases
      assume "i = j" thus ?thesis using opt_bst2.psimps[OF "1.hyps"] by simp
    next
      assume [arith]: "i \<noteq> j"
      have left_le_right: "?left \<le> ?right"
      proof cases
        assume [arith]: "i = j-1"
        have l: "root (opt_bst2 i (j - 1)) = i" using "1.IH"(1) by auto
        have r: "root (opt_bst2 (i+1) j) = j" using "1.IH"(2) by auto
        show ?thesis using l r by auto
      next
        assume "\<not> i = j-1"
        hence[arith]: "i < j-1" by arith
        have "?left \<le> root (opt_bst2 (i + 1) (j - 1))" using "1.IH"(1) by auto
        also have "... \<le> root (opt_bst2 (i+1) j)" using "1.IH"(2) by auto
        finally have "?left \<le> ?right" .
        thus ?thesis by auto
      qed

      let ?lambda = "\<lambda>t. root t \<in> {?left .. ?right}"
      show ?thesis
        using argmin_forall[of \<open>map ?f [?left..?right]\<close> \<open>?lambda\<close> \<open>wpl i j\<close>] left_le_right
        by (fastforce simp add: opt_bst2.psimps[OF "1.hyps"])
    qed
  qed
qed

text \<open>Now we can bound the result of @{const opt_bst2} easily:\<close>

lemma root_opt_bst2_bound:
  "opt_bst2_dom (i,j) \<Longrightarrow> i \<le> j \<Longrightarrow> root (opt_bst2 i j) \<in> {i..j}"
proof(induction i j rule:opt_bst2.pinduct)
  case (1 i j)
  show ?case using  "1.prems" "1.IH"(1,2) left_le_right[OF "1.hyps"] by force
qed                                                                           

text \<open>Now termination follows easily:\<close>

lemma opt_bst2_dom: "\<forall>args. opt_bst2_dom args"
proof (relation "measure (\<lambda>(i,j). nat (j-i+1))")
  let ?R = "measure (\<lambda>(i,j). nat (j-i+1))"
  show "wf ?R" ..

  fix i j::int 
  assume [arith]: "\<not>j < i" "i \<noteq> j"
  thus "((i, j - 1), (i, j)) \<in> ?R" by auto

  fix left
  assume left: "left = root (opt_bst2 i (j - 1))" "opt_bst2_dom (i, j - 1)" 
  thus "((i + 1, j), (i, j)) \<in> ?R" by(auto)

  fix right k
  assume right: "right = root (opt_bst2 (i + 1) j)" "k \<in> set[left..right]"
    "opt_bst2_dom (i+1, j)"
    
  thus "((i, k - 1), (i, j)) \<in> ?R"
    using root_opt_bst2_bound[of "i+1" j] by(auto)

  show "((k + 1, j), (i, j)) \<in> ?R"
    using left right root_opt_bst2_bound[of i "j-1"] by(auto)
qed

termination by(rule opt_bst2_dom)

declare opt_bst2.simps[simp del]

abbreviation "min_wpl3 i j k \<equiv> min_wpl i (k-1) + min_wpl (k+1) j + w i j"

text\<open>The correctness proof \cite{Yao} is based on a general theory of `quatrilateral inequalities'
developed in locale QI that we now instantiate:\<close>

interpretation QI
  where
    c = "\<lambda>i j. min_wpl (i+1) j"
    and c_k = "\<lambda>i j. min_wpl3 (i+1) j"
    and w = "\<lambda>i j. w (i+1) j"
proof (standard, goal_cases)
  case (1 i i' j j')
  thus ?case using QI_w by simp
next
  case (2 i i' j j')
  thus ?case using monotone_w by simp
next
  case (3 i j)
  thus ?case by simp
next
  case (4 i j k)
  show ?case by simp
qed

lemma K_argmin: "i < j \<Longrightarrow> K i j = argmin (min_wpl3 (i+1) j) [i+1..j]"
by(simp add: K_def argmin_Max_Args_min_on Args_min_on_def)

theorem opt_bst2_opt_bst: "opt_bst2 i j = opt_bst i j"
proof (induction i j rule: opt_bst2.induct)
  case (1 i j)
  show ?case
  proof cases
    assume "i \<ge> j" thus ?thesis by(cases "i=j") (auto simp: opt_bst2.simps)
  next
    assume [arith]: "\<not> i \<ge> j"
    let ?c = "\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j + w i j"
    let ?opt = "\<lambda>k. \<langle>opt_bst i (k-1), k, opt_bst (k+1) j\<rangle>"
    have 1: "i \<le> K (i-1) (j-1)"
      using argmin_in[of "[i..j-1]"] by(auto simp add: K_argmin)
    have 2: "argmin ?c [i..j] \<in> {K (i-1) (j-1)..K i j}"
      using lemma_3[of "i-1" "j-1"] by(simp add: K_argmin)
    have 3: "K i j \<le> j" using argmin_in[of "[i+1..j]"] by(auto simp: K_argmin)
    have *: "argmin ?c [K (i-1) (j-1)..K i j] = argmin ?c [i..j]"
      by(rule argmin_red_ivl[OF 1 2 3])
    have "opt_bst2 i j =
     argmin (wpl i j) (map ?opt [root(opt_bst2 i (j-1))..root(opt_bst2 (i+1) j)])"
      using [[simp_depth_limit=3]]
      by(simp add: "1.IH"(3,4)[OF _ _ refl refl] opt_bst2.simps[of i j] cong: list.map_cong_simp)
    also have "\<dots> = argmin (wpl i j) (map ?opt [root(opt_bst i (j-1))..root(opt_bst (i+1) j)])"
      by (simp add: "1.IH"(1,2))
    also have "root(opt_bst i (j-1)) = K (i-1) (j-1)"
      by(simp add: argmin_map wpl_opt_bst comp_def K_argmin)
    also have "root(opt_bst (i+1) j) = K i j"
      by(simp add: argmin_map wpl_opt_bst comp_def K_argmin)
    also have "argmin (wpl i j) (map ?opt [K (i - 1) (j - 1)..K i j])
       = ?opt (argmin (wpl i j o ?opt) [K (i-1) (j-1)..K i j])"
      using lemma_3[of "i-1" "j-1"] by(simp add: argmin_map)
    also have "\<dots> = ?opt (argmin ?c [K (i-1) (j-1)..K i j])"
      by(simp add: comp_def wpl_opt_bst)
    also have "\<dots> = ?opt(argmin ?c [i..j])"
      by (simp add: "*")
    also have "\<dots> = ?opt(argmin (wpl i j o ?opt) [i..j])"
      by(simp add: comp_def wpl_opt_bst)
    also have "\<dots> = argmin (wpl i j) (map ?opt [i..j])"
      by(simp add: argmin_map)
    also have "\<dots> = opt_bst i j"
      by simp
    finally show ?thesis .
  qed
qed

corollary opt_bst2_is_optimal: "wpl i j (opt_bst2 i j) = min_wpl i j"
by (simp add: opt_bst2_opt_bst wpl_opt_bst)


function opt_bst_wpl2 :: "int \<Rightarrow> int \<Rightarrow> int tree \<times> nat" where
"opt_bst_wpl2 i j =
  (if i > j then (Leaf,0) else
   if i = j then (Node Leaf i Leaf, w i i) else
   let l = root(fst(opt_bst_wpl2 i (j-1)));
      r = root(fst(opt_bst_wpl2 (i+1) j)) in
     argmin snd
       [let (tl,wl) = opt_bst_wpl2 i (k-1); (tr,wr) = opt_bst_wpl2 (k+1) j
        in (\<langle>tl, k, tr\<rangle>, wl + wr + w i j) . k \<leftarrow> [l..r]])"
by auto

lemma left_le_right2:
 "opt_bst_wpl2_dom(i,j) \<Longrightarrow>
  (i=j \<longrightarrow> root(fst(opt_bst_wpl2 i j)) = i) \<and>
  (i<j \<longrightarrow> root(fst(opt_bst_wpl2 i j)) \<in>
    {root(fst(opt_bst_wpl2 i (j-1))) .. root(fst(opt_bst_wpl2 (i+1) j))})"
proof (induction rule: opt_bst_wpl2.pinduct)
  case (1 i j)
  let ?l = "root (fst(opt_bst_wpl2 i (j-1)))"
  let ?r = "root (fst(opt_bst_wpl2 (i+1) j))"
  let ?f ="\<lambda>k. let (tl,wl) = opt_bst_wpl2 i (k-1); (tr,wr) = opt_bst_wpl2 (k+1) j
               in (\<langle>tl, k, tr\<rangle>, wl + wr + w i j)"
  show ?case
  proof cases
    assume "i > j" thus ?thesis by auto
  next
    assume [arith]: "\<not> i > j"
    show ?thesis 
    proof cases
      assume "i = j" thus ?thesis using opt_bst_wpl2.psimps[OF "1.hyps"] by simp
    next
      assume [arith]: "i \<noteq> j"
      have left_le_right: "?l \<le> ?r"
      proof cases
        assume [arith]: "i = j-1"
        have l: "root (fst(opt_bst_wpl2 i (j-1))) = i" using "1.IH"(1) by auto
        have r: "root (fst(opt_bst_wpl2 (i+1) j)) = j" using \<open>i = j-1\<close> "1.IH"(2)
          by auto
        show ?thesis using l r by auto
      next
        assume "\<not> i = j-1"
        hence[arith]: "i < j-1" by arith
        have "?l \<le> root (fst(opt_bst_wpl2 (i+1) (j-1)))" using "1.IH"(1) by auto
        also have "... \<le> root (fst(opt_bst_wpl2 (i+1) j))" using "1.IH"(2) by auto
        finally have "?l \<le> ?r" .
        thus ?thesis by auto
      qed

      let ?P = "\<lambda>t. root (fst t) \<in> {?l .. ?r}"
      show ?thesis
        using argmin_forall[of \<open>map ?f [?l..?r]\<close> ?P snd] left_le_right
        by (fastforce simp add: opt_bst_wpl2.psimps[OF "1.hyps"] split: prod.splits)
    qed
  qed
qed

text \<open>Now we can bound the result of @{const opt_bst_wpl2}:\<close>

lemma root_opt_bst_wpl2_bound:
  "opt_bst_wpl2_dom (i,j) \<Longrightarrow> i \<le> j \<Longrightarrow> root (fst(opt_bst_wpl2 i j)) \<in> {i..j}"
proof(induction i j rule:opt_bst_wpl2.pinduct)
  case (1 i j)
  show ?case using  "1.prems" "1.IH"(1)  "1.IH"(2)[OF _ _ refl] left_le_right2[OF "1.hyps"]
    by fastforce
qed

text \<open>Now termination follows easily:\<close>

lemma opt_bst_wpl2_dom: "\<forall>args. opt_bst_wpl2_dom args"
proof (relation "measure (\<lambda>(i,j). nat (j-i+1))")
  let ?R = "measure (\<lambda>(i,j). nat (j-i+1))"
  show "wf ?R" ..

  fix i j::int 
  assume [arith]: "\<not>j < i" "i \<noteq> j"
  thus "((i, j - 1), (i, j)) \<in> ?R" by auto

  fix left
  assume left: "left = root (fst(opt_bst_wpl2 i (j-1)))" "opt_bst_wpl2_dom (i, j-1)" 
  thus "((i+1, j), (i, j)) \<in> ?R" by(auto)

  fix right k
  assume right: "right = root (fst(opt_bst_wpl2 (i+1) j))" "k \<in> set[left..right]"
    "opt_bst_wpl2_dom (i+1, j)"
    
  thus "((i, k-1), (i, j)) \<in> ?R"
    using root_opt_bst_wpl2_bound[of "i+1" j] by(auto)

  show "((k+1, j), (i, j)) \<in> ?R"
    using left right root_opt_bst_wpl2_bound[of i "j-1"] by(auto)
qed

termination by(rule opt_bst_wpl2_dom)

declare opt_bst_wpl2.simps[simp del]

lemma opt_bst_wpl2_eq_pair:
  "opt_bst_wpl2 i j = (opt_bst2 i j, wpl i j (opt_bst2 i j))"
proof(induction i j rule: opt_bst_wpl2.induct)
  case (1 i j)
  note [simp] = opt_bst2.simps[of i j] opt_bst_wpl2.simps[of i j] (*opt_bst2_opt_bst*)
  show ?case 
  proof cases
    assume "i > j" thus ?thesis using "1.prems" by (simp)
  next
    assume [arith]: "\<not> i > j"
    show ?case
    proof cases
      assume [arith]: "i = j"
      show ?thesis by(simp) (simp add: \<open>i = j\<close>)
    next
      assume [arith]: "i \<noteq> j"
      let ?l = "root (opt_bst2 i (j-1))" let ?r = "root (opt_bst2 (i+1) j)"
      have *: "?l \<le> ?r"
        using left_le_right[of i j] by (fastforce simp: opt_bst2_opt_bst opt_bst2_dom)
      let ?f = "\<lambda>k. case opt_bst_wpl2 i (k-1) of
             (l,wl) \<Rightarrow> case opt_bst_wpl2 (k+1) j of
                         (r,wr) \<Rightarrow> (\<langle>l,k,r\<rangle>, wl + wr + w i j)"
      let ?g = "\<lambda>k. (\<langle>opt_bst2 i (k-1), k, opt_bst2 (k+1) j\<rangle>,
                    wpl i (k-1) (opt_bst2 i (k-1)) + wpl (k+1) j (opt_bst2 (k+1) j) + w i j)"
      have fg: "?f k = ?g k" if k: "k \<in> {?l..?r}" for k
      proof -
        have 1: "opt_bst_wpl2 i (k-1) = (opt_bst2 i (k-1), wpl i (k-1) (opt_bst2 i (k-1)))"
          using k "1.IH"(3) by(simp add: "1.IH"(1,2))
        have 2: "opt_bst_wpl2 (k+1) j = (opt_bst2 (k+1) j, wpl (k+1) j (opt_bst2 (k+1) j))"
          using 1 k "1.IH"(4) by(simp add: "1.IH"(1,2))
        show ?thesis using 1 2 by(simp)
      qed
      have "opt_bst_wpl2 i j =
        argmin snd (map ?f [root(fst(opt_bst_wpl2 i (j-1)))..root(fst(opt_bst_wpl2 (i+1) j))])"
        by(simp)
      also have "\<dots> = argmin snd (map ?f [?l..?r])"
        by(simp add: "1.IH"(1,2))
      also have "\<dots> = argmin snd (map ?g [?l..?r])"
        using fg by (simp cong: list.map_cong_simp)
      also have "\<dots> = (opt_bst2 i j, wpl i j (opt_bst2 i j))" using *
        by(simp add: argmin_pairs comp_def)
      finally show ?thesis .
    qed
  qed
qed

corollary opt_bst_wpl2_eq_pair': "opt_bst_wpl2 i j = (opt_bst i j, min_wpl i j)"
by (simp add: opt_bst_wpl2_eq_pair opt_bst2_opt_bst wpl_opt_bst)

end (* locale Optimal_BST2 *)

end
