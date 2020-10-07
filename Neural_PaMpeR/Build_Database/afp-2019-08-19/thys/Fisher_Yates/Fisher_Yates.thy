(*
    File: Fisher_Yates.thy
    Author: Manuel Eberl, TU München
    
    Definition and correctness proofs for two variants of the 
    Fisher-Yates shuffle, an algorithm to shuffle an array in-place
    in linear time, i.e. produce a permutation uniformly at random.
*)
section \<open>Fisher--Yates shuffle\<close>
theory Fisher_Yates
  imports "HOL-Probability.Probability"
begin

(* TODO Move *)

lemma integral_pmf_of_multiset:
  "A \<noteq> {#} \<Longrightarrow> (\<integral>x. (f x :: real) \<partial>measure_pmf (pmf_of_multiset A)) = 
     (\<Sum>x\<in>set_mset A. of_nat (count A x) * f x) / of_nat (size A)"
  by (subst integral_measure_pmf[where A = "set_mset A"])
     (simp_all add: sum_divide_distrib mult_ac)

lemma pmf_bind_pmf_of_multiset:
  "A \<noteq> {#} \<Longrightarrow> pmf (pmf_of_multiset A \<bind> f) y = 
     (\<Sum>x\<in>set_mset A. real (count A x) * pmf (f x) y) / real (size A)"
  by (simp add: pmf_bind integral_pmf_of_multiset)

lemma pmf_map_inj_inv:
  assumes "inj_on f (set_pmf p)"
  assumes "\<And>x. f' (f x) = x"
  shows   "pmf (map_pmf f p) x = (if x \<in> range f then pmf p (f' x) else 0)"
proof (cases "x \<in> f ` set_pmf p")
  case True
  from this obtain y where y: "y \<in> set_pmf p" "x = f y" by blast
  with assms(1) have "pmf (map_pmf f p) x = pmf p y"
    by (simp add: pmf_map_inj)
  also from y assms(2)[of y] have "y = f' x" by simp
  finally show ?thesis using y by simp
next
  case False
  hence "x \<notin> set_pmf (map_pmf f p)" by simp
  hence "pmf (map_pmf f p) x = 0" by (simp add: set_pmf_eq)
  also from False have "0 = (if x \<in> range f then pmf p (f' x) else 0)"
    by (auto simp: assms(2) set_pmf_eq)
  finally show ?thesis .
qed
(* END MOVE *)

subsection \<open>Swapping elements in a list\<close>

definition swap where "swap xs i j = xs[i := xs!j, j := xs ! i]"

lemma length_swap [simp]: "length (swap xs i j) = length xs"
  by (simp add: swap_def)

lemma swap_eq_Nil_iff [simp]: "swap xs i j = [] \<longleftrightarrow> xs = []"
  by (simp add: swap_def)

lemma nth_swap: "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> 
    swap xs i j ! k = (if k = i then xs ! j else if k = j then xs ! i else xs ! k)"
  by (auto simp: swap_def nth_list_update)

lemma map_swap: "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> map f (swap xs i j) = swap (map f xs) i j"
  by (simp add: swap_def map_update map_nth)

lemma swap_swap: "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> swap (swap xs i j) j i = xs"
  by (intro nth_equalityI) (auto simp: nth_swap nth_list_update)
  
lemma mset_swap: "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> mset (swap xs i j) = mset xs"
  by (simp add: mset_update swap_def nth_list_update)

lemma hd_swap_0: "i < length xs \<Longrightarrow> hd (swap xs 0 i) = xs ! i"
  unfolding swap_def by (subst hd_conv_nth) (subst nth_list_update | force)+

  
subsection \<open>Random Permutations\<close>

text \<open>
  First, we prove the intuitively obvious fact that choosing a random 
  permutation of a multiset can be done by first randomly choosing the 
  first element and then randomly choosing the rest of the list.
\<close>

lemma pmf_of_set_permutations_of_multiset_nonempty:
  assumes "(A :: 'a multiset) \<noteq> {#}"
  shows "pmf_of_set (permutations_of_multiset A) =
           do {x \<leftarrow> pmf_of_multiset A;
               xs \<leftarrow> pmf_of_set (permutations_of_multiset (A - {#x#}));
               return_pmf (x#xs)
              }" (is "?lhs = ?rhs")
proof (rule pmf_eqI)
  fix xs :: "'a list"
  show "pmf ?lhs xs = pmf ?rhs xs"
  proof (cases "xs \<in> permutations_of_multiset A")
    case False
    with assms have "xs \<notin> set_pmf ?lhs" by simp
    moreover from assms False have "xs \<notin> set_pmf ?rhs" 
      by (auto simp: permutations_of_multiset_Cons_iff)
    ultimately show ?thesis by (simp add: set_pmf_eq)
  next
    case True
    with assms have nonempty: "xs \<noteq> []" by (auto dest: permutations_of_multisetD)
    hence range_Cons: "xs \<in> range ((#) x) \<longleftrightarrow> hd xs = x" for x
      by (cases xs) auto
    from True nonempty 
      have hd_tl: "hd xs \<in># A \<and> tl xs \<in> permutations_of_multiset (A - {#hd xs#})"
      by (cases xs) (auto simp: permutations_of_multiset_Cons_iff)

    from assms have "pmf ?rhs xs = 
      (\<Sum>x\<in>set_mset A. real (count A x) * pmf (map_pmf ((#) x) 
        (pmf_of_set (permutations_of_multiset (A - {#x#})))) xs) / real (size A)" (is "_ = ?S / _")
      unfolding map_pmf_def [symmetric] by (simp add: pmf_bind_pmf_of_multiset)
    also have "?S = 
      (\<Sum>x\<in>set_mset A. if x = hd xs then real (count A (hd xs)) / 
         real (card (permutations_of_multiset (A - {#hd xs#}))) else 0)"
      using range_Cons hd_tl
      by (intro sum.cong refl, subst pmf_map_inj_inv[where f' = tl]) auto
    also have "\<dots> = real (count A (hd xs)) / 
                      real (card (permutations_of_multiset (A - {#hd xs#})))"
      using hd_tl by (simp add: sum.delta)
    also from hd_tl have "\<dots> = real (size A) / real (card (permutations_of_multiset A))"
      by (simp add: divide_simps real_card_permutations_of_multiset_remove[of "hd xs"])
    also have " \<dots> / real (size A) = pmf (pmf_of_set (permutations_of_multiset A)) xs" 
      using assms True by simp
    finally show ?thesis ..
  qed
qed

  
subsection \<open>Shuffling Lists\<close>

text \<open>
  We define shuffling of a list as choosing from the set of all lists
  that correspond to the same multiset uniformly at random.
\<close>
definition shuffle :: "'a list \<Rightarrow> 'a list pmf" where
  "shuffle xs = pmf_of_set (permutations_of_multiset (mset xs))"

lemma shuffle_empty [simp]: "shuffle [] = return_pmf []"
  by (simp add: shuffle_def pmf_of_set_singleton)

lemma shuffle_singleton [simp]: "shuffle [x] = return_pmf [x]"
  by (simp add: shuffle_def pmf_of_set_singleton)

text \<open>
  The crucial ingredient of the Fisher--Yates shuffle is the following lemma,
  which decomposes a shuffle into swapping the first element of the list with 
  a random element of the remaining list and shuffling the new remaining list.

  With a random-access implementation of a list -- such as an array -- all of
  the required operations are cheap and the resulting algorithm runs in linear 
  time. 
\<close>
lemma shuffle_fisher_yates_step:
  assumes xs_nonempty [simp]: "xs \<noteq> []"
  shows "shuffle xs =  
           do {i \<leftarrow> pmf_of_set {..<length xs}; 
               let ys = swap xs 0 i; 
               zs \<leftarrow> shuffle (tl ys);
               return_pmf (hd ys # zs)
              }"
proof -
  have "shuffle xs = do {x \<leftarrow> pmf_of_multiset (mset xs);
             xs \<leftarrow> pmf_of_set (permutations_of_multiset (mset xs - {#x#}));
             return_pmf (x#xs)
            }" unfolding shuffle_def
    by (simp add: pmf_of_set_permutations_of_multiset_nonempty)
  also have "pmf_of_multiset (mset xs) = 
               pmf_of_multiset (image_mset ((!) xs) (mset (upt 0 (length xs))))"
    by (subst mset_map [symmetric]) (simp add: map_nth)
  also have "\<dots> = map_pmf ((!) xs) (pmf_of_set {..<length xs})"
    by (subst map_pmf_of_set) (auto simp add: map_pmf_of_set atLeast0LessThan lessThan_empty_iff)
  also have "do {x \<leftarrow> map_pmf ((!) xs) (pmf_of_set {..<length xs});
                 ys \<leftarrow> pmf_of_set (permutations_of_multiset (mset xs - {#x#}));
                 return_pmf (x # ys)
                } = 
             do {i \<leftarrow> pmf_of_set {..<length xs};
                 ys \<leftarrow> pmf_of_set (permutations_of_multiset (mset xs - {#xs ! i#}));
                 return_pmf (xs ! i # ys)
                }"
    by (simp add: map_pmf_def bind_assoc_pmf bind_return_pmf)
  also have "\<dots> = do {i \<leftarrow> pmf_of_set {..<length xs};
                      let ys = swap xs 0 i; 
                      zs \<leftarrow> shuffle (tl (swap xs 0 i));
                      return_pmf (hd ys # zs)
                     }" unfolding Let_def shuffle_def
    by (intro bind_pmf_cong refl, subst (asm) set_pmf_of_set)
       (auto simp: lessThan_empty_iff mset_tl mset_swap hd_swap_0)
  finally show ?thesis by (simp add: Let_def)
qed


subsection \<open>Forward Fisher-Yates Shuffle\<close>

text \<open>
  The actual Fisher--Yates shuffle is now merely a kind of tail-recursive version of
  decomposition described above. Note that unlike the traditional Fisher--Yates shuffle, 
  we shuffle the list from front to back, which is the more natural way to do it when 
  working with linked lists.
\<close>

function fisher_yates_aux where
  "fisher_yates_aux i xs = (if i + 1 \<ge> length xs then return_pmf xs else 
     do {j \<leftarrow> pmf_of_set {i..<length xs};
         fisher_yates_aux (i + 1) (swap xs i j)})"
by auto
termination by (relation "Wellfounded.measure (\<lambda>(i,xs). length xs - i)") simp_all

declare fisher_yates_aux.simps [simp del]

lemma fisher_yates_aux_correct:
  "fisher_yates_aux i xs = map_pmf (\<lambda>ys. take i xs @ ys) (shuffle (drop i xs))"
proof (induction i xs rule: fisher_yates_aux.induct)
  case (1 i xs)
  show ?case
  proof (cases "i + 1 \<ge> length xs")
    case True
    show ?thesis
    proof (cases "i \<ge> length xs")
      case False
      with True have "length xs = Suc i" and i: "i = length xs - 1" by simp_all
      hence "xs \<noteq> []" by auto
      hence "xs = butlast xs @ [last xs]" by (rule append_butlast_last_id [symmetric])
      also have "butlast xs = take i xs" by (simp add: butlast_conv_take i)
      finally have eq: "take i xs @ [last xs] = xs" ..
      moreover have "xs = take i xs @ drop i xs" by simp
      ultimately have "take i xs @ [last xs] = take i xs @ drop i xs" by (rule trans)
      hence "drop i xs = [last xs]" by (subst (asm) same_append_eq) simp_all
      with True show ?thesis by (simp add: eq fisher_yates_aux.simps)
    qed (simp_all add: fisher_yates_aux.simps)
  next
    case False
    from False have xs_nonempty [simp]: "xs \<noteq> []" by auto
    have "fisher_yates_aux i xs = 
             pmf_of_set {i..<length xs} \<bind> (\<lambda>j. fisher_yates_aux (i+1) (swap xs i j))"
      using False by (subst fisher_yates_aux.simps) simp
    also have "{i..<length xs} = ((\<lambda>j. j + i) ` {..<length xs - i})"
      using False by (simp add: lessThan_atLeast0)
    also from False have "pmf_of_set \<dots> = map_pmf (\<lambda>j. j + i) (pmf_of_set {..<length xs - i})"
      by (subst map_pmf_of_set_inj) (simp_all add: lessThan_empty_iff)
    also from False have "length xs - i = length (drop i xs)" by simp
    also have "map_pmf (\<lambda>j. j + i) (pmf_of_set {..<length (drop i xs)}) \<bind>
                   (\<lambda>j. fisher_yates_aux (i + 1) (swap xs i j)) =
               pmf_of_set {..<length (drop i xs)} \<bind> (\<lambda>j. fisher_yates_aux (i + 1) (swap xs i (j+i)))"
      by (simp add: map_pmf_def bind_return_pmf bind_assoc_pmf)
    also have "\<dots> = do {j \<leftarrow> pmf_of_set {..<length (drop i xs)};
                        let ys = swap (drop i xs) 0 j;
                        zs \<leftarrow> shuffle (tl ys);
                        return_pmf (take i xs @ hd ys # zs)}" (is "_ = bind_pmf _ ?T")
    proof (intro bind_pmf_cong refl)
      fix j assume "j \<in> set_pmf (pmf_of_set {..<length (drop i xs)})"
      with False have j: "j < length (drop i xs)" by (simp_all add: lessThan_empty_iff)
      define ys where "ys = swap xs i (j + i)"
      have "fisher_yates_aux (i + 1) ys = map_pmf ((@) (take (i+1) ys)) (shuffle (drop (i+1) ys))"
        using False j unfolding ys_def by (intro "1.IH") simp_all
      also from False have "take (i+1) ys = take i ys @ [hd (drop i ys)]"
        by (simp add: ys_def take_hd_drop)
      also have "drop (i+1) ys = tl (drop i ys)" by (simp add: ys_def tl_drop drop_Suc)
      also from False j have "drop i ys = swap (drop i xs) 0 j"
        by (simp add: ys_def swap_def drop_update_swap add_ac)
      also from False j have "take i ys = take i xs" 
        by (simp add: ys_def swap_def)
      finally show "fisher_yates_aux (i + 1) ys = ?T j"
        by (simp add: ys_def map_pmf_def Let_def bind_assoc_pmf bind_return_pmf)
    qed
    also from False have "\<dots> = map_pmf (\<lambda>zs. take i xs @ zs) (shuffle (drop i xs))"
      by (subst shuffle_fisher_yates_step[of "drop i xs"])
         (simp_all add: map_pmf_def Let_def bind_return_pmf bind_assoc_pmf)
    finally show ?thesis .
  qed
qed

definition fisher_yates where
  "fisher_yates = fisher_yates_aux 0"

lemma fisher_yates_correct: "fisher_yates xs = shuffle xs"
  unfolding fisher_yates_def
  by (subst fisher_yates_aux_correct) (simp_all add: map_pmf_def bind_return_pmf')


subsection \<open>Backwards Fisher-Yates Shuffle\<close>

text \<open>
  We can now easily derive the classical Fisher--Yates shuffle, which goes through 
  the list from back to front and show its equivalence to the forward Fisher--Yates
  shuffle.
\<close>
fun fisher_yates_alt_aux where
  "fisher_yates_alt_aux i xs = (if i = 0 then return_pmf xs else 
     do {j \<leftarrow> pmf_of_set {..i};
         fisher_yates_alt_aux (i - 1) (swap xs i j)})"

declare fisher_yates_alt_aux.simps [simp del]

lemma fisher_yates_alt_aux_altdef:
  "i < length xs \<Longrightarrow> fisher_yates_alt_aux i xs = 
     map_pmf rev (fisher_yates_aux (length xs - i - 1) (rev xs))"
proof (induction i xs rule: fisher_yates_alt_aux.induct)
  case (1 i xs)
  show ?case
  proof (cases "i = 0")
    case False
    with "1.prems" have "map_pmf rev (fisher_yates_aux (length xs - i - 1) (rev xs)) = 
      pmf_of_set {length xs - Suc i..<length xs} \<bind>
        (\<lambda>x. fisher_yates_aux (Suc (length xs - Suc i))
          (swap (rev xs) (length xs - Suc i) x) \<bind>
            (\<lambda>x. return_pmf (rev x)))"
      by (subst fisher_yates_aux.simps) (auto simp: map_pmf_def bind_return_pmf bind_assoc_pmf)
    also from "1.prems" False 
      have bij: "bij_betw (\<lambda>j. length xs - Suc j) {..i} {length xs - Suc i..<length xs}"
      by (intro bij_betwI[where g = "\<lambda>j. length xs - Suc j"]) auto
    from bij have "{length xs - Suc i..<length xs} = (\<lambda>j. length xs - Suc j) ` {..i}"
      by (simp add: bij_betw_def)
    also from bij have "pmf_of_set \<dots> = map_pmf (\<lambda>j. length xs - Suc j) (pmf_of_set {..i})"
      by (subst map_pmf_of_set_inj) (auto simp: bij_betw_def)
    also have "map_pmf (\<lambda>j. length xs - Suc j) (pmf_of_set {..i}) \<bind>
                 (\<lambda>x. fisher_yates_aux (Suc (length xs - Suc i))
                   (swap (rev xs) (length xs - Suc i) x) \<bind> (\<lambda>x. return_pmf (rev x))) =
               pmf_of_set {..i} \<bind> (\<lambda>x. map_pmf rev (
                 fisher_yates_aux (length xs - i) (rev (swap xs i x))))"
      using "1.prems" False
      by (auto simp add: map_pmf_def bind_assoc_pmf bind_return_pmf Suc_diff_Suc
            swap_def rev_update rev_nth intro!: bind_pmf_cong)
    also have "\<dots> = pmf_of_set {..i} \<bind> (\<lambda>j. fisher_yates_alt_aux (i - 1) (swap xs i j))"
      using "1.prems" False "1.IH" [symmetric] by (auto intro!: bind_pmf_cong)
    also from "1.prems" False have "\<dots> = fisher_yates_alt_aux i xs"
      by (subst fisher_yates_alt_aux.simps[of i]) simp_all
    finally show ?thesis ..
  qed (insert "1.prems", simp_all add: fisher_yates_aux.simps fisher_yates_alt_aux.simps)
qed

definition fisher_yates_alt where
  "fisher_yates_alt xs = fisher_yates_alt_aux (length xs - 1) xs"

lemma fisher_yates_alt_aux_correct:
  "fisher_yates_alt xs = shuffle xs"
proof (cases "xs = []")
  case True
  thus ?thesis 
    by (simp add: fisher_yates_alt_def fisher_yates_alt_aux.simps)
next
  case False
  thus ?thesis unfolding fisher_yates_alt_def
    by (subst fisher_yates_alt_aux_altdef)
       (simp_all add: fisher_yates_aux_correct shuffle_def map_pmf_of_set_inj)
qed

subsection \<open>Code generation test\<close>

text \<open>
  Isabelle's code generator allows us to produce executable code both for
  @{const shuffle} and for @{const fisher_yates} and @{const fisher_yates_alt}.
  However, this code does not produce a random sample (i.e. a single randomly 
  permuted list) -- which is, in fact, the only purpose of the Fisher--Yates 
  algorithm -- but the entire probability distribution consisting of $n!$ 
  lists, each with probability $1/n!$.

  In the future, it would be nice if Isabelle also had some code generation 
  facility that supports generating sampling code.
\<close>

value [code] "shuffle ''abcd''"
value [code] "fisher_yates ''abcd''"
value [code] "fisher_yates_alt ''abcd''"

end
