(*
  File:    Descartes_Sign_Rule.thy
  Author:  Manuel Eberl <eberlm@in.tum.de>

  Descartes' Rule of Signs, which relates the number of positive real roots of a polynomial
  with the number of sign changes in its coefficient list.
*)
section \<open>Sign changes and Descartes' Rule of Signs\<close>

theory Descartes_Sign_Rule
imports 
  Complex_Main
  "HOL-Computational_Algebra.Polynomial"
begin

lemma op_plus_0: "((+) (0 :: 'a :: monoid_add)) = id"
  by auto

lemma filter_dropWhile: 
  "filter (\<lambda>x. \<not>P x) (dropWhile P xs) = filter (\<lambda>x. \<not>P x) xs"
  by (induction xs) simp_all


subsection \<open>Polynomials\<close> 

text\<open>
  A real polynomial whose leading and constant coefficients have opposite
  non-zero signs must have a positive root.
\<close>
lemma pos_root_exI:
  assumes "poly p 0 * lead_coeff p < (0 :: real)"
  obtains x where "x > 0" "poly p x = 0"
proof -
  have P: "\<exists>x>0. poly p x = (0::real)" if "lead_coeff p > 0" "poly p 0 < 0" for p
  proof -
    note that(1)
    also from poly_pinfty_gt_lc[OF \<open>lead_coeff p > 0\<close>] obtain x0 
      where "\<And>x. x \<ge> x0 \<Longrightarrow> poly p x \<ge> lead_coeff p" by auto
    hence "poly p (max x0 1) \<ge> lead_coeff p" by auto
    finally have "poly p (max x0 1) > 0" .
    with that have "\<exists>x. x > 0 \<and> x < max x0 1 \<and> poly p x = 0"
      by (intro poly_IVT mult_neg_pos) auto
    thus "\<exists>x>0. poly p x = 0"  by auto
  qed

  show ?thesis
  proof (cases "lead_coeff p > 0")
    case True
    with assms have "poly p 0 < 0" 
      by (auto simp: mult_less_0_iff)
    from P[OF True this] that show ?thesis 
      by blast
  next
    case False
    from False assms have "poly (-p) 0 < 0" 
      by (auto simp: mult_less_0_iff)
    moreover from assms have "p \<noteq> 0"
      by auto
    with False have "lead_coeff (-p) > 0" 
      by (cases rule: linorder_cases[of "lead_coeff p" 0]) 
         (simp_all add:)
    ultimately show ?thesis using that P[of "-p"] by auto
  qed
qed

text \<open>
  Substitute $X$ with $aX$ in a polynomial $p(X)$. This turns all the $X - a$ factors in $p$
  into factors of the form $X - 1$.
\<close>
definition reduce_root where
  "reduce_root a p = pcompose p [:0, a:]"

lemma reduce_root_pCons: 
  "reduce_root a (pCons c p) = pCons c (smult a (reduce_root a p))"
  by (simp add: reduce_root_def pcompose_pCons)

lemma reduce_root_nonzero [simp]: 
  "a \<noteq> 0 \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> reduce_root a p \<noteq> (0 :: 'a :: idom poly)"
  unfolding reduce_root_def using pcompose_eq_0[of p "[:0, a:]"] 
  by auto


subsection \<open>List of partial sums\<close>

text \<open>
  We first define, for a given list, the list of accumulated partial sums from left to right: 
  the list @{term "psums xs"} has as its $i$-th entry $\sum_{j=0}^i \mathrm{xs}_i$.
\<close>

fun psums where
  "psums [] = []"
| "psums [x] = [x]"
| "psums (x#y#xs) = x # psums ((x+y) # xs)"

lemma length_psums [simp]: "length (psums xs) = length xs"
  by (induction xs rule: psums.induct) simp_all

lemma psums_Cons: 
  "psums (x#xs) = (x :: 'a :: semigroup_add) # map ((+) x) (psums xs)"
  by (induction xs rule: psums.induct) (simp_all add: algebra_simps)

lemma last_psums: 
  "(xs :: 'a :: monoid_add list) \<noteq> [] \<Longrightarrow> last (psums xs) = sum_list xs"
  by (induction xs rule: psums.induct) 
     (auto simp add: add.assoc [symmetric] psums_Cons o_def)

lemma psums_0_Cons [simp]: 
  "psums (0#xs :: 'a :: monoid_add list) = 0 # psums xs"
  by (induction xs rule: psums.induct) (simp_all add: algebra_simps)

lemma map_uminus_psums: 
  fixes xs :: "'a :: ab_group_add list"
  shows "map uminus (psums xs) = psums (map uminus xs)"
  by (induction xs rule: psums.induct) (simp_all)

lemma psums_replicate_0_append:
  "psums (replicate n (0 :: 'a :: monoid_add) @ xs) = 
     replicate n 0 @ psums xs"
  by (induction n) (simp_all add: psums_Cons op_plus_0)

lemma psums_nth: "n < length xs \<Longrightarrow> psums xs ! n = (\<Sum>i\<le>n. xs ! i)"
proof (induction xs arbitrary: n rule: psums.induct[case_names Nil sng rec])
  case (rec x y xs n)
  show ?case
  proof (cases n)
    case (Suc m)
    from Suc have "psums (x # y # xs) ! n = psums ((x+y) # xs) ! m" by simp
    also from rec.prems Suc have "\<dots> = (\<Sum>i\<le>m. ((x+y) # xs) ! i)" 
      by (intro rec.IH) simp_all
    also have "\<dots> = x + y + (\<Sum>i=1..m. (y#xs) ! i)"
      by (auto simp: atLeast0AtMost [symmetric] sum.atLeast_Suc_atMost[of 0])
    also have "(\<Sum>i=1..m. (y#xs) ! i) = (\<Sum>i=Suc 1..Suc m. (x#y#xs) ! i)"
      by (subst sum.shift_bounds_cl_Suc_ivl) simp
    also from Suc have "x + y + \<dots> = (\<Sum>i\<le>n. (x#y#xs) ! i)"
      by (auto simp: atLeast0AtMost [symmetric] sum.atLeast_Suc_atMost add_ac)
    finally show ?thesis .
  qed simp
qed simp_all


subsection \<open>Sign changes in a list\<close>

text \<open>
  Next, we define the number of sign changes in a sequence. Intuitively, this is the number 
  of times that, when passing through the list, a sign change between one element and the next 
  element occurs (while ignoring all zero entries).

  We implement this by filtering all zeros from the list of signs, removing all adjacent equal 
  elements and taking the length of the resulting list minus one.
\<close>
definition sign_changes :: "('a :: {sgn,zero} list) \<Rightarrow> nat" where
  "sign_changes xs = length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map sgn xs))) - 1"

lemma sign_changes_Nil [simp]: "sign_changes [] = 0" 
  by (simp add: sign_changes_def)

lemma sign_changes_singleton [simp]: "sign_changes [x] = 0" 
  by (simp add: sign_changes_def)

lemma sign_changes_cong:
  assumes "map sgn xs = map sgn ys"
  shows   "sign_changes xs = sign_changes ys"
  using assms unfolding sign_changes_def by simp

lemma sign_changes_Cons_ge: "sign_changes (x # xs) \<ge> sign_changes xs"
  unfolding sign_changes_def by (simp add: remdups_adj_Cons split: list.split)

lemma sign_changes_Cons_Cons_different: 
  fixes x y :: "'a :: linordered_idom"
  assumes "x * y < 0"
  shows "sign_changes (x # y # xs) = 1 + sign_changes (y # xs)"
proof -
  from assms have "sgn x = -1 \<and> sgn y = 1 \<or> sgn x = 1 \<and> sgn y = -1"
    by (auto simp: mult_less_0_iff)
  thus ?thesis by (fastforce simp: sign_changes_def)
qed

lemma sign_changes_Cons_Cons_same: 
  fixes x y :: "'a :: linordered_idom"
  shows "x * y > 0 \<Longrightarrow> sign_changes (x # y # xs) = sign_changes (y # xs)"
  by (subst (asm) zero_less_mult_iff) (fastforce simp: sign_changes_def)

lemma sign_changes_0_Cons [simp]: 
  "sign_changes (0 # xs :: 'a :: idom_abs_sgn list) = sign_changes xs"
  by (simp add: sign_changes_def)

lemma sign_changes_two: 
  fixes x y :: "'a :: linordered_idom"
  shows "sign_changes [x,y] = 
           (if x > 0 \<and> y < 0 \<or> x < 0 \<and> y > 0 then 1 else 0)"
  by (auto simp: sgn_if sign_changes_def mult_less_0_iff)

lemma sign_changes_induct [case_names nil sing zero nonzero]:
  assumes "P []" "\<And>x. P [x]" "\<And>xs. P xs \<Longrightarrow> P (0#xs)"
          "\<And>x y xs. x \<noteq> 0 \<Longrightarrow> P ((x + y) # xs) \<Longrightarrow> P (x # y # xs)"
  shows   "P xs"
proof (induction "length xs" arbitrary: xs rule: less_induct)
  case (less xs)
  show ?case
  proof (cases xs rule: psums.cases)
    fix x y xs' assume "xs = x # y # xs'"
    with assms less show ?thesis by (cases "x = 0") auto
  qed (insert less assms, auto)
qed 

lemma sign_changes_filter: 
  fixes xs :: "'a :: linordered_idom list"
  shows "sign_changes (filter (\<lambda>x. x \<noteq> 0) xs) = sign_changes xs"
  by (simp add: sign_changes_def filter_map o_def sgn_0_0)

lemma sign_changes_Cons_Cons_0: 
  fixes xs :: "'a :: linordered_idom list"
  shows "sign_changes (x # 0 # xs) = sign_changes (x # xs)"
  by (subst (1 2) sign_changes_filter [symmetric]) simp_all

lemma sign_changes_uminus: 
  fixes xs :: "'a :: linordered_idom list"
  shows   "sign_changes (map uminus xs) = sign_changes xs"
proof -
  have "sign_changes (map uminus xs) = 
          length (remdups_adj [x\<leftarrow>map sgn (map uminus xs) . x \<noteq> 0]) - 1" 
   unfolding sign_changes_def ..
  also have "map sgn (map uminus xs) = map uminus (map sgn xs)" 
    by (auto simp: sgn_minus)
  also have "remdups_adj (filter (\<lambda>x. x \<noteq> 0) \<dots>) = 
                 map uminus (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map sgn xs)))"
    by (subst filter_map, subst remdups_adj_map_injective) 
       (simp_all add: o_def)
  also have "length \<dots> - 1 = sign_changes xs" by (simp add: sign_changes_def)
  finally show ?thesis .
qed

lemma sign_changes_replicate: "sign_changes (replicate n x) = 0"
  by (simp add: sign_changes_def remdups_adj_replicate filter_replicate)

lemma sign_changes_decompose:
  assumes "x \<noteq> (0 :: 'a :: linordered_idom)"
  shows   "sign_changes (xs @ x # ys) = 
             sign_changes (xs @ [x]) + sign_changes (x # ys)"
proof -
  have "sign_changes (xs @ x # ys) = 
            length (remdups_adj ([x\<leftarrow>map sgn xs . x \<noteq> 0] @ 
                      sgn x # [x\<leftarrow>map sgn ys . x \<noteq> 0])) - 1"
    by (simp add: sgn_0_0 assms sign_changes_def)
  also have "\<dots> = sign_changes (xs @ [x]) + sign_changes (x # ys)"
    by (subst remdups_adj_append) (simp add: sign_changes_def assms sgn_0_0)
  finally show ?thesis .
qed

text \<open>
  If the first and the last entry of a list are non-zero, its number of sign changes is even 
  if and only if the first and the last element have the same sign. This will be important 
  later to establish the base case of Descartes' Rule. (if there are no positive roots, 
  the number of sign changes is even)
\<close>
lemma even_sign_changes_iff:
  assumes "xs \<noteq> ([] :: 'a :: linordered_idom list)" "hd xs \<noteq> 0" "last xs \<noteq> 0"
  shows   "even (sign_changes xs) \<longleftrightarrow> sgn (hd xs) = sgn (last xs)"
using assms
proof (induction "length xs" arbitrary: xs rule: less_induct)
  case (less xs)
  show ?case
  proof (cases xs)
    case (Cons x xs')
    note x = this
    show ?thesis
    proof (cases xs')
      case (Cons y xs'')
      note y = this
      show ?thesis
      proof (rule linorder_cases[of "x*y" 0])
        assume xy: "x*y = 0"
        with x y less(1,3,4) show ?thesis by (auto simp: sign_changes_Cons_Cons_0)
      next
        assume xy: "x*y > 0"
        with less(1,4) show ?thesis
          by (auto simp add: x y sign_changes_Cons_Cons_same zero_less_mult_iff)
      next
        assume xy: "x*y < 0"
        moreover from xy have "sgn x = - sgn y" by (auto simp: mult_less_0_iff)
        moreover have "even (sign_changes (y # xs'')) \<longleftrightarrow> 
                         sgn (hd (y # xs'')) = sgn (last (y # xs''))"
          using xy less.prems by (intro less) (auto simp: x y)
        moreover from xy less.prems 
          have "sgn y = sgn (last xs) \<longleftrightarrow> -sgn y \<noteq> sgn (last xs)"
          by (auto simp: sgn_if)
        ultimately show ?thesis by (auto simp: sign_changes_Cons_Cons_different x y)
      qed
    qed (auto simp: x)
  qed (insert less.prems, simp_all)
qed


subsection \<open>Arthan's lemma\<close>

context
begin

text \<open>
  We first prove an auxiliary lemma that allows us to assume w.l.o.g. that the first element of 
  the list is non-negative, similarly to what Arthan does in his proof.
\<close>
private lemma arthan_wlog [consumes 3, case_names nonneg lift]:
  fixes xs :: "'a :: linordered_idom list"
  assumes "xs \<noteq> []" "last xs \<noteq> 0" "x + y + sum_list xs = 0"
  assumes "\<And>x y xs. xs \<noteq> [] \<Longrightarrow> last xs \<noteq> 0 \<Longrightarrow> 
               x + y + sum_list xs = 0 \<Longrightarrow> x \<ge> 0 \<Longrightarrow> P x y xs"
  assumes "\<And>x y xs. xs \<noteq> [] \<Longrightarrow> P x y xs \<Longrightarrow> P (-x) (-y) (map uminus xs)"
  shows   "P x y xs"
proof (cases "x \<ge> 0")
  assume x: "\<not>(x \<ge> 0)"
  from assms have "map uminus xs \<noteq> []" by simp
  moreover from x assms(1,2,3) have"P (-x) (-y) (map uminus xs)"
    using uminus_sum_list_map[of "\<lambda>x. x" xs, symmetric]
    by (intro assms) (auto simp: last_map algebra_simps o_def neg_eq_iff_add_eq_0)
  ultimately have "P (- (-x)) (- (-y)) (map uminus (map uminus xs))" by (rule assms)
  thus ?thesis by (simp add: o_def)
qed (simp_all add: assms)

text \<open>
  We now show that the $\alpha$ and $\beta$ in Arthan's proof have the necessary properties:
  their difference is non-negative and even.
\<close>
private lemma arthan_aux1:
  fixes xs :: "'a :: {linordered_idom} list"
  assumes "xs \<noteq> []" "last xs \<noteq> 0" "x + y + sum_list xs = 0"
  defines "v \<equiv> \<lambda>xs. int (sign_changes xs)"
  shows "v (x # y # xs) - v ((x + y) # xs) \<ge> 
             v (psums (x # y # xs)) - v (psums ((x + y) # xs)) \<and> 
         even (v (x # y # xs) - v ((x + y) # xs) - 
                  (v (psums (x # y # xs)) - v (psums ((x + y) # xs))))"
using assms(1-3)
proof (induction rule: arthan_wlog)
  have uminus_v: "v (map uminus xs) = v xs" for xs by (simp add: v_def sign_changes_uminus)

  case (lift x y xs)
  note lift(2)
  also have "v (psums (x#y#xs)) - v (psums ((x+y)#xs)) =
                 v (psums (- x # - y # map uminus xs)) - 
                 v (psums ((- x + - y) # map uminus xs))"
    by (subst (1 2) uminus_v [symmetric]) (simp add: map_uminus_psums)
  also have "v (x # y # xs) - v ((x + y) # xs) = 
                 v (-x # -y # map uminus xs) - v ((-x + -y) # map uminus xs)"
    by (subst (1 2) uminus_v [symmetric]) simp
  finally show ?case .
next
  case (nonneg x y xs)
  define p where "p = (LEAST n. xs ! n \<noteq> 0)"
  define xs1 :: "'a list" where "xs1 = replicate p 0"
  define xs2 where "xs2 = drop (Suc p) xs"
  from nonneg have "xs ! (length xs - 1) \<noteq> 0" by (simp add: last_conv_nth)
  hence p_nz: "xs ! p \<noteq> 0" unfolding p_def by (rule LeastI)
  {
    fix q assume "q < p" hence "xs ! q = 0"
      using Least_le[of "\<lambda>n. xs ! n \<noteq> 0" q] unfolding p_def by force
  } note less_p_zero = this
  from Least_le[of "\<lambda>n. xs ! n \<noteq> 0" "length xs - 1"] nonneg 
    have "p \<le> length xs - 1" unfolding p_def by (auto simp: last_conv_nth)
  with nonneg have p_less_length: "p < length xs" by (cases xs) simp_all

  from p_less_length less_p_zero have "take p xs = replicate p 0" 
    by (subst list_eq_iff_nth_eq) auto
  with p_less_length have xs_decompose: "xs = xs1 @ xs ! p # xs2" 
    unfolding xs1_def xs2_def
    by (subst append_take_drop_id [of p, symmetric], 
        subst Cons_nth_drop_Suc) simp_all

  have v_decompose: "v (xs' @ xs) = v (xs' @ [xs ! p]) + v (xs ! p # xs2)" for xs'
  proof -
    have "xs' @ xs = (xs' @ xs1) @ xs ! p # xs2" by (subst xs_decompose) simp
    also have "v \<dots> = v (xs' @ [xs ! p]) + v (xs ! p # xs2)" unfolding v_def
      by (subst sign_changes_decompose[OF p_nz], 
          subst (1 2 3 4) sign_changes_filter [symmetric]) (simp_all add: xs1_def)
    finally show ?thesis .
  qed

  have psums_decompose: "psums xs = replicate p 0 @ psums (xs!p # xs2)" 
    by (subst xs_decompose) (simp add: xs1_def psums_replicate_0_append)
  have v_psums_decompose: "sign_changes (xs' @ psums xs) = sign_changes (xs' @ [xs!p]) + 
         sign_changes (xs!p # map ((+) (xs!p)) (psums xs2))" for xs'
  proof -
    fix xs' :: "'a list"
    have "sign_changes (xs' @ psums xs) = 
            sign_changes (xs' @ xs ! p # map ((+) (xs!p)) (psums xs2))"
      by (subst psums_decompose, subst (1 2) sign_changes_filter [symmetric]) 
         (simp_all add: psums_Cons)
    also have "\<dots> = sign_changes (xs' @ [xs!p]) + 
                      sign_changes (xs!p # map ((+) (xs!p)) (psums xs2))"
      by (subst sign_changes_decompose[OF p_nz]) simp_all
    finally show "sign_changes (xs' @ psums xs) = \<dots>" .
  qed

  show ?case
  proof (cases "x > 0")
    assume "\<not>(x > 0)"
    with nonneg show ?thesis by (auto simp: v_def)
  next
    assume x: "x > 0"
    show ?thesis
    proof (rule linorder_cases[of y 0])
      assume y: "y > 0"
      from x and this have xy: "x + y > 0" by (rule add_pos_pos)
      with y have "sign_changes ((x + y) # xs) = sign_changes (y # xs)"
        by (intro sign_changes_cong) auto
      moreover have "sign_changes (x # psums ((x + y) # xs)) = 
                       sign_changes (psums ((x+y) # xs))"
        using x xy by (subst (1 2) psums_Cons) (simp_all add: sign_changes_Cons_Cons_same)
      ultimately show ?thesis using x y 
        by (simp add: v_def algebra_simps sign_changes_Cons_Cons_same)
    next
      assume y: "y = 0"
      with x show ?thesis
        by (simp add: v_def sign_changes_Cons_Cons_0 psums_Cons 
                      o_def sign_changes_Cons_Cons_same)
    next
      assume y: "y < 0"
      with x have different: "x * y < 0" by (rule mult_pos_neg)
      show ?thesis
      proof (rule linorder_cases[of "x + y" 0])
        assume xy: "x + y < 0"
        with x have different': "x * (x + y) < 0" by (rule mult_pos_neg)
        have "(\<lambda>t. t + (x + y)) = ((+) (x + y))" by (rule ext) simp
        moreover from y xy have "sign_changes ((x+y) # xs) = sign_changes (y # xs)" 
          by (intro sign_changes_cong) auto
        ultimately show ?thesis using xy different different' y
          by (simp add: v_def sign_changes_Cons_Cons_different psums_Cons o_def add_ac)
      next
        assume xy: "x + y = 0"
        show ?case
        proof (cases "xs ! p > 0")
          assume p: "xs ! p > 0"
          from p y have different': "y * xs ! p < 0" by (intro mult_neg_pos)
          with v_decompose[of "[x, y]"] v_decompose[of "[x+y]"] x xy p different different' 
               v_psums_decompose[of "[x]"] v_psums_decompose[of "[]"]
          show ?thesis by (auto simp add: algebra_simps v_def sign_changes_Cons_Cons_0 
                             sign_changes_Cons_Cons_different sign_changes_Cons_Cons_same)
        next
          assume "\<not>(xs ! p > 0)"
          with p_nz have p: "xs ! p < 0" by simp
          from p y have same: "y * xs ! p > 0" by (intro mult_neg_neg)
          from p x have different': "x * xs ! p < 0" by (intro mult_pos_neg)
          from v_decompose[of "[x, y]"] v_decompose[of "[x+y]"] xy different different' same 
               v_psums_decompose[of "[x]"] v_psums_decompose[of "[]"]
          show ?thesis by (auto simp add: algebra_simps v_def sign_changes_Cons_Cons_0 
                             sign_changes_Cons_Cons_different sign_changes_Cons_Cons_same)
        qed
      next
        assume xy: "x + y > 0"
        from x and this have same: "x * (x + y) > 0" by (rule mult_pos_pos)
        show ?case
        proof (cases "xs ! p > 0")
          assume p: "xs ! p > 0"
          from xy p have same': "(x + y) * xs ! p > 0" by (intro mult_pos_pos)
          from p y have different': "y * xs ! p < 0" by (intro mult_neg_pos)
          have "(\<lambda>t. t + (x + y)) = ((+) (x + y))" by (rule ext) simp
          with v_decompose[of "[x, y]"] v_decompose[of "[x+y]"] different different' same same'
          show ?thesis by (auto simp add: algebra_simps v_def psums_Cons o_def
                             sign_changes_Cons_Cons_different sign_changes_Cons_Cons_same)
        next
          assume "\<not>(xs ! p > 0)"
          with p_nz have p: "xs ! p < 0" by simp
          from xy p have different': "(x + y) * xs ! p < 0" by (rule mult_pos_neg)
          from y p have same': "y * xs ! p > 0" by (rule mult_neg_neg)
          have "(\<lambda>t. t + (x + y)) = ((+) (x + y))" by (rule ext) simp
          with v_decompose[of "[x, y]"] v_decompose[of "[x+y]"] different different' same same'
          show ?thesis by (auto simp add: algebra_simps v_def psums_Cons o_def
                              sign_changes_Cons_Cons_different sign_changes_Cons_Cons_same)
        qed
      qed
    qed
  qed
qed


text \<open>
  Now we can prove the main lemma of the proof by induction over the list with our specialised
  induction rule for @{term "sign_changes"}. It states that for a non-empty list whose last element 
  is non-zero and whose sum is zero, the difference of the sign changes in the list and in the list 
  of its partial sums is odd and positive. 
\<close>
lemma arthan:
  fixes xs :: "'a :: linordered_idom list"
  assumes "xs \<noteq> []" "last xs \<noteq> 0" "sum_list xs = 0"
  shows   "sign_changes xs > sign_changes (psums xs) \<and> 
           odd (sign_changes xs - sign_changes (psums xs))"
using assms
proof (induction xs rule: sign_changes_induct)
  case (nonzero x y xs)
  show ?case
  proof (cases "xs = []")
    case False
    define \<alpha> where "\<alpha> = int (sign_changes (x # y # xs)) - int (sign_changes ((x + y) # xs))"
    define \<beta> where "\<beta> = int (sign_changes (psums (x # y # xs))) - int (sign_changes (psums ((x+y) # xs)))"
    from nonzero False have "\<alpha> \<ge> \<beta> \<and> even (\<alpha> - \<beta>)" unfolding \<alpha>_def \<beta>_def
      by (intro arthan_aux1) auto
    from False and nonzero.prems have
       "sign_changes (psums ((x + y) # xs)) < sign_changes ((x + y) # xs) \<and>
        odd (sign_changes ((x + y) # xs) - sign_changes (psums ((x + y) # xs)))"
      by (intro nonzero.IH) (auto simp: add.assoc)
    with arthan_aux1[of xs x y] nonzero(4,5) False(1) show ?thesis by force
  qed (insert nonzero.prems, auto split: if_split_asm simp: sign_changes_two add_eq_0_iff)
qed (auto split: if_split_asm simp: add_eq_0_iff)

end


subsection \<open>Roots of a polynomial with a certain property\<close>

text \<open>
  The set of roots of a polynomial @{term "p"} that fulfil a given property @{term "P"}:
\<close>
definition "roots_with P p = {x. P x \<and> poly p x = 0}"

text \<open>
  The number of roots of a polynomial @{term "p"} with a given property @{term "P"}, where 
  multiple roots are counted multiple times.
 \<close>
definition "count_roots_with P p = (\<Sum>x\<in>roots_with P p. order x p)"

abbreviation "pos_roots \<equiv> roots_with (\<lambda>x. x > 0)"
abbreviation "count_pos_roots \<equiv> count_roots_with (\<lambda>x. x > 0)"


lemma finite_roots_with [simp]: 
  "(p :: 'a :: linordered_idom poly) \<noteq> 0 \<Longrightarrow> finite (roots_with P p)"
  by (rule finite_subset[OF _ poly_roots_finite[of p]]) (auto simp: roots_with_def)

lemma count_roots_with_times_root:
  assumes "p \<noteq> 0" "P (a :: 'a :: linordered_idom)"
  shows   "count_roots_with P ([:a, -1:] * p) = Suc (count_roots_with P p)"
proof -
  define q where "q = [:a, -1:] * p"
  from assms have a: "a \<in> roots_with P q" by (simp_all add: roots_with_def q_def)
  have q_nz: "q \<noteq> 0" unfolding q_def by (rule no_zero_divisors) (simp_all add: assms)

  have "count_roots_with P q = (\<Sum>x\<in>roots_with P q. order x q)" by (simp add: count_roots_with_def)
  also from a q_nz have "\<dots> = order a q + (\<Sum>x\<in>roots_with P q - {a}. order x q)"
    by (subst sum.remove) simp_all
  also have "order a q = order a [:a, -1:] + order a p" unfolding q_def
    by (subst order_mult[OF no_zero_divisors]) (simp_all add: assms)
  also have "order a [:a, -1:] = 1"
    by (subst order_smult [of "-1", symmetric])
       (insert order_power_n_n[of a 1], simp_all add: order_1)
  also have "(\<Sum>x\<in>roots_with P q - {a}. order x q) = (\<Sum>x\<in>roots_with P q - {a}. order x p)"
  proof (intro sum.cong refl)
    fix x assume x: "x \<in> roots_with P q - {a}"
    from assms have "order x q = order x [:a, -1:] + order x p" unfolding q_def
      by (subst order_mult[OF no_zero_divisors]) (simp_all add: assms)
    also from x have "order x [:a, -1:] = 0" by (intro order_0I) simp_all
    finally show "order x q = order x p" by simp
  qed
  also from a q_nz have "1 + order a p + (\<Sum>x\<in>roots_with P q - {a}. order x p) = 
                           1 + (\<Sum>x\<in>roots_with P q. order x p)"
    by (subst add.assoc, subst sum.remove[symmetric]) simp_all
  also from q_nz have "(\<Sum>x\<in>roots_with P q. order x p) = (\<Sum>x\<in>roots_with P p. order x p)"
  proof (intro sum.mono_neutral_right)
    show "roots_with P p \<subseteq> roots_with P q" 
      by (auto simp: roots_with_def q_def simp del: mult_pCons_left)
    show "\<forall>x\<in>roots_with P q - roots_with P p. order x p = 0"
      by (auto simp: roots_with_def q_def order_root simp del: mult_pCons_left)
  qed simp_all
  finally show ?thesis by (simp add: q_def count_roots_with_def)
qed


subsection \<open>Coefficient sign changes of a polynomial\<close>

abbreviation (input) "coeff_sign_changes f \<equiv> sign_changes (coeffs f)"

text \<open>
  We first show that when building a polynomial from a coefficient list, the coefficient sign
  sign changes of the resulting polynomial are the same as the same sign changes in the list.

  Note that constructing a polynomial from a list removes all trailing zeros.
\<close>
lemma sign_changes_coeff_sign_changes:
  assumes "Poly xs = (p :: 'a :: linordered_idom poly)"
  shows   "sign_changes xs = coeff_sign_changes p"
proof -
  have "coeffs p = coeffs (Poly xs)" by (subst assms) (rule refl)
  also have "\<dots> = strip_while ((=) 0) xs" by simp
  also have "filter ((\<noteq>) 0) \<dots> = filter ((\<noteq>) 0) xs" unfolding strip_while_def o_def
    by (subst rev_filter [symmetric], subst filter_dropWhile) (simp_all add: rev_filter)
  also have "sign_changes \<dots> = sign_changes xs" by (simp add: sign_changes_filter)
  finally show ?thesis by (simp add: sign_changes_filter)
qed

text \<open>
  By applying @{term "reduce_root a"}, we can assume w.l.o.g. that the root in
  question is 1, since applying root reduction does not change the number of 
  sign changes.
\<close>
lemma coeff_sign_changes_reduce_root: 
  assumes "a > (0 :: 'a :: linordered_idom)"
  shows   "coeff_sign_changes (reduce_root a p) = coeff_sign_changes p"
proof (intro sign_changes_cong, induction p)
  case (pCons c p)
  have "map sgn (coeffs (reduce_root a (pCons c p))) = 
             cCons (sgn c) (map sgn (coeffs (reduce_root a p)))"
    using assms by (auto simp add: cCons_def sgn_0_0 sgn_mult reduce_root_pCons coeffs_smult)
  also note pCons.IH
  also have "cCons (sgn c) (map sgn (coeffs p)) = map sgn (coeffs (pCons c p))"
    using assms by (auto simp add: cCons_def sgn_0_0)
  finally show ?case .
qed (simp_all add: reduce_root_def)

text \<open>
  Multiplying a polynomial with a positive constant also does not change the number 
  of sign changes. (in fact, any non-zero constant would also work, but the proof 
  is slightly more difficult and positive constants suffice in our use case)
\<close>
lemma coeff_sign_changes_smult: 
  assumes "a > (0 :: 'a :: linordered_idom)"
  shows   "coeff_sign_changes (smult a p) = coeff_sign_changes p"
  using assms by (auto intro!: sign_changes_cong simp: sgn_mult coeffs_smult)


context
begin

text \<open>
  We now show that a polynomial with an odd number of sign changes contains a 
  positive root. We first assume that the constant coefficient is non-zero. Then it is 
  clear that the polynomial's sign at 0 will be the sign of the constant coefficient, whereas 
  the polynomial's sign for sufficiently large inputs will be the sign of the leading coefficient.

  Moreover, we have shown before that in a list with an odd number of sign changes and 
  non-zero initial and last coefficients, the initial coefficient and the last coefficient have 
  opposite and non-zero signs. Then, the polynomial obviously has a positive root.
\<close>
private lemma odd_coeff_sign_changes_imp_pos_roots_aux:
  assumes [simp]: "p \<noteq> (0 :: real poly)" "poly p 0 \<noteq> 0"
  assumes "odd (coeff_sign_changes p)"
  obtains x where "x > 0" "poly p x = 0"
proof -
  from \<open>poly p 0 \<noteq> 0\<close>
  have [simp]: "hd (coeffs p) \<noteq> 0"
    by (induct p) auto
  from assms have  "\<not> even (coeff_sign_changes p)"
    by blast
  also have "even (coeff_sign_changes p) \<longleftrightarrow> sgn (hd (coeffs p)) = sgn (lead_coeff p)"
    by (auto simp add: even_sign_changes_iff last_coeffs_eq_coeff_degree)
  finally have "sgn (hd (coeffs p)) * sgn (lead_coeff p) < 0" 
    by (auto simp: sgn_if split: if_split_asm)
  also from \<open>p \<noteq> 0\<close> have "hd (coeffs p) = poly p 0" by (induction p) auto
  finally have "poly p 0 * lead_coeff p < 0" by (auto simp: mult_less_0_iff)

  from pos_root_exI[OF this] that show ?thesis by blast
qed

text \<open>
  We can now show the statement without the restriction to a non-zero constant coefficient.
  We can do this by simply factoring $p$ into the form $p \cdot x^n$, where $n$ is chosen as
  large as possible. This corresponds to stripping all initial zeros of the coefficient list,
  which obviously changes neither the existence of positive roots nor the number of coefficient 
  sign changes.
\<close>
lemma odd_coeff_sign_changes_imp_pos_roots:
  assumes "p \<noteq> (0 :: real poly)"
  assumes "odd (coeff_sign_changes p)"
  obtains x where "x > 0" "poly p x = 0"
proof -
  define s where "s = sgn (lead_coeff p)"
  define n where "n = order 0 p"
  define r where "r = p div [:0, 1:] ^ n"
  have p: "p = [:0, 1:] ^ n * r" unfolding r_def n_def
    using order_1[of 0 p] by (simp del: mult_pCons_left)
  from assms p have r_nz: "r \<noteq> 0" by auto

  obtain x where "x > 0" "poly r x = 0"
  proof (rule odd_coeff_sign_changes_imp_pos_roots_aux)
    show "r \<noteq> 0" by fact
    have "order 0 p = order 0 p + order 0 r"
      by (subst p, insert order_power_n_n[of "0::real" n] r_nz)
         (simp del: mult_pCons_left add: order_mult n_def)
    hence "order 0 r = 0" by simp
    with r_nz show nz: "poly r 0 \<noteq> 0" by (simp add: order_root)

    note \<open>odd (coeff_sign_changes p)\<close> 
    also have "p = [:0, 1:] ^ n * r" by (simp add: p)
    also have "[:0, 1:] ^ n = monom 1 n" 
      by (induction n) (simp_all add: monom_Suc monom_0)
    also have "coeffs (monom 1 n * r) = replicate n 0 @ coeffs r"
      by (induction n) (simp_all add: monom_Suc cCons_def r_nz monom_0)
    also have "sign_changes \<dots> = coeff_sign_changes r"
      by (subst (1 2) sign_changes_filter [symmetric]) simp
    finally show "odd (coeff_sign_changes r)" .
  qed
  thus ?thesis by (intro that[of x]) (simp_all add: p)
qed

end


subsection \<open>Proof of Descartes' sign rule\<close>

text \<open>
  For a polynomial $p(X) = a_0 + \ldots + a_n X^n$, we have 
  $[X^i] (1-X)p(X) = (\sum\limits_{j=0}^i a_j)$.
\<close>
lemma coeff_poly_times_one_minus_x:
  fixes g :: "'a :: linordered_idom poly"
  shows "coeff g n = (\<Sum>i\<le>n. coeff (g * [:1, -1:]) i)"
  by (induction n) simp_all

text \<open>
  We apply the previous lemma to the coefficient list of a polynomial and show: 
  given a polynomial $p(X)$ and $q(X) = (1 - X)p(X)$, the coefficient list of $p(X)$ is the 
  list of partial sums of the coefficient list of $q(X)$.
\<close>
lemma Poly_times_one_minus_x_eq_psums:
  fixes xs :: "'a :: linordered_idom list"
  assumes [simp]: "length xs = length ys"
  assumes "Poly xs = Poly ys * [:1, -1:]"
  shows   "ys = psums xs"
proof (rule nth_equalityI; safe?)
  fix i assume i: "i < length ys"
  hence "ys ! i = coeff (Poly ys) i"
    by (simp add: nth_default_def)
  also from coeff_poly_times_one_minus_x[of "Poly ys" i] assms
    have "\<dots> = (\<Sum>j\<le>i. coeff (Poly xs) j)" by simp
    also from i have "\<dots> = psums xs ! i"
      by (auto simp: nth_default_def psums_nth)
  finally show "ys ! i = psums xs ! i" .
qed simp_all

text \<open>
  We can now apply our main lemma on the sign changes in lists to the coefficient lists of 
  a nonzero polynomial $p(X)$ and $(1-X)p(X)$: the difference of the changes in the 
  coefficient lists is odd and positive.
\<close>
lemma sign_changes_poly_times_one_minus_x:
  fixes g :: "'a :: linordered_idom poly" and a :: 'a
  assumes nz: "g \<noteq> 0"
  defines "v \<equiv> coeff_sign_changes"
  shows "v ([:1, -1:] * g) - v g > 0 \<and> odd (v ([:1, -1:] * g) - v g)"
proof -
  define xs where "xs = coeffs ([:1, -1:] * g)"
  define ys where "ys = coeffs g @ [0]"
  have ys: "ys = psums xs"
  proof (rule Poly_times_one_minus_x_eq_psums)
    show "length xs = length ys" unfolding xs_def ys_def
      by (simp add: length_coeffs nz degree_mult_eq no_zero_divisors del: mult_pCons_left)
    show "Poly xs = Poly ys * [:1, - 1:]" unfolding xs_def ys_def
      by (simp only: Poly_snoc Poly_coeffs) simp
  qed
  have "sign_changes (psums xs) < sign_changes xs \<and> 
        odd (sign_changes xs - sign_changes (psums xs))"
  proof (rule arthan)
    show "xs \<noteq> []"
      by (auto simp: xs_def nz simp del: mult_pCons_left)
    then show "sum_list xs = 0" by (simp add: last_psums [symmetric] ys [symmetric] ys_def)
    show "last xs \<noteq> 0"
      by (auto simp: xs_def nz last_coeffs_eq_coeff_degree simp del: mult_pCons_left)
  qed
  with ys have "sign_changes ys < sign_changes xs \<and> 
                odd (sign_changes xs - sign_changes ys)" by simp
  also have "sign_changes xs = v ([:1, -1:] * g)" unfolding v_def
    by (intro sign_changes_coeff_sign_changes) (simp_all add: xs_def)
  also have "sign_changes ys = v g" unfolding v_def
    by (intro sign_changes_coeff_sign_changes) (simp_all add: ys_def Poly_snoc)
  finally show ?thesis by simp
qed

text \<open>
  We can now lift the previous lemma to the case of $p(X)$ and $(a-X)p(X)$ by substituting $X$ 
  with $aX$, yielding the polynomials $p(aX)$ and $a \cdot (1-X) \cdot p(aX)$.
\<close>
lemma sign_changes_poly_times_root_minus_x:
  fixes g :: "'a :: linordered_idom poly" and a :: 'a
  assumes nz: "g \<noteq> 0" and pos: "a > 0"
  defines "v \<equiv> coeff_sign_changes"
  shows "v ([:a, -1:] * g) - v g > 0 \<and> odd (v ([:a, -1:] * g) - v g)"
proof -
  have "0 < v ([:1, - 1:] * reduce_root a g) - v (reduce_root a g) \<and>
            odd (v ([:1, - 1:] * reduce_root a g) - v (reduce_root a g))"
    using nz pos unfolding v_def by (intro sign_changes_poly_times_one_minus_x) simp_all
  also have "v ([:1, -1:] * reduce_root a g) = v (smult a ([:1, -1:] * reduce_root a g))"
    unfolding v_def by (simp add: coeff_sign_changes_smult pos)
  also have "smult a ([:1, -1:] * reduce_root a g) = [:a:] * [:1, -1:] * reduce_root a g" 
    by (subst mult.assoc) simp
  also have "[:a:] * [:1, -1:] = reduce_root a [:a, -1:]" 
    by (simp add: reduce_root_def pcompose_pCons)
  also have "\<dots> * reduce_root a g = reduce_root a ([:a, -1:] * g)" 
    unfolding reduce_root_def by (simp only: pcompose_mult)
  also have "v \<dots> = v ([:a, -1:] * g)" by (simp add: v_def coeff_sign_changes_reduce_root pos)
  also have "v (reduce_root a g) = v g" by (simp add: v_def coeff_sign_changes_reduce_root pos)
  finally show ?thesis .
qed

text \<open>
  Finally, the difference of the number of coefficient sign changes and the number of
  positive roots is non-negative and even. This follows straightforwardly by induction 
  over the roots.
\<close>
lemma descartes_sign_rule_aux:
  fixes p :: "real poly"
  assumes "p \<noteq> 0"
  shows   "coeff_sign_changes p \<ge> count_pos_roots p \<and> 
           even (coeff_sign_changes p - count_pos_roots p)"
using assms
proof (induction p rule: poly_root_induct[where P = "\<lambda>a. a > 0"])
  case (root a p)
  define q where "q = [:a, -1:] * p"
  from root.prems have p: "p \<noteq> 0" by auto
  with root p sign_changes_poly_times_root_minus_x[of p a] 
       count_roots_with_times_root[of p "\<lambda>x. x > 0" a] show ?case by (fold q_def) fastforce
next
  case (no_roots p)
  from no_roots have "pos_roots p = {}" by (auto simp: roots_with_def)
  hence [simp]: "count_pos_roots p = 0" by (simp add: count_roots_with_def)
  thus ?case using no_roots \<open>p \<noteq> 0\<close> odd_coeff_sign_changes_imp_pos_roots[of p]
    by (auto simp: roots_with_def)
qed simp_all

text \<open>
  The main theorem is then an obvious consequence
\<close>
theorem descartes_sign_rule:
  fixes p :: "real poly"
  assumes "p \<noteq> 0"
  shows "\<exists>d. even d \<and> coeff_sign_changes p = count_pos_roots p + d"
proof
  define d where "d = coeff_sign_changes p - count_pos_roots p"
  show "even d \<and> coeff_sign_changes p = count_pos_roots p + d"
    unfolding d_def using descartes_sign_rule_aux[OF assms] by auto
qed

end
