(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Neville Aitken Interpolation\<close>

text \<open>We prove soundness of Neville-Aitken's polynomial interpolation algorithm 
  using the recursive formula directly. We further provide an implementation 
  which avoids the exponential branching in the recursion.\<close>

theory Neville_Aitken_Interpolation
imports 
  "HOL-Computational_Algebra.Polynomial"
begin

context
  fixes x :: "nat \<Rightarrow> 'a :: field"
  and f :: "nat \<Rightarrow> 'a"
begin

private definition X :: "nat \<Rightarrow> 'a poly" where [code_unfold]: "X i = [:-x i, 1:]"

function neville_aitken_main :: "nat \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "neville_aitken_main i j = (if i < j then 
      (smult (inverse (x j - x i)) (X i * neville_aitken_main (i + 1) j -
      X j * neville_aitken_main i (j - 1))) 
    else [:f i:])"
  by pat_completeness auto

termination by (relation "measure (\<lambda> (i,j). j - i)", auto)

definition neville_aitken :: "nat \<Rightarrow> 'a poly" where
  "neville_aitken = neville_aitken_main 0"

declare neville_aitken_main.simps[simp del]

lemma neville_aitken_main: assumes dist: "\<And> i j. i < j \<Longrightarrow> j \<le> n \<Longrightarrow> x i \<noteq> x j"
  shows "i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> j \<le> n \<Longrightarrow> poly (neville_aitken_main i j) (x k) = (f k)"
proof (induct i j arbitrary: k rule: neville_aitken_main.induct)
  case (1 i j k)
  note neville_aitken_main.simps[of i j, simp]
  show ?case
  proof (cases "i < j")
    case False
    with 1(3-) have "k = i" by auto
    with False show ?thesis by auto
  next
    case True note ij = this
    from dist[OF True 1(5)] have diff: "x i \<noteq> x j" by auto
    from True have id: "neville_aitken_main i j = 
      (smult (inverse (x j - x i)) (X i * neville_aitken_main (i + 1) j - X j 
        * neville_aitken_main i (j - 1)))" by simp
    note IH = 1(1-2)[OF True]
    show ?thesis
    proof (cases "k = i")
      case True
      show ?thesis unfolding id True poly_smult using IH(2)[of i] ij 1(3-) diff
        by (simp add: X_def field_simps)
    next
      case False note ki = this
      show ?thesis 
      proof (cases "k = j")
        case True
        show ?thesis unfolding id True poly_smult using IH(1)[of j] ij 1(3-) diff
          by (simp add: X_def field_simps)
      next
        case False
        with ki show ?thesis unfolding id poly_smult using IH(1-2)[of k] ij 1(3-) diff
          by (simp add: X_def field_simps)
      qed
    qed
  qed
qed

lemma degree_neville_aitken_main: "degree (neville_aitken_main i j) \<le> j - i"
proof (induct i j rule: neville_aitken_main.induct)
  case (1 i j)
  note simp = neville_aitken_main.simps[of i j]
  show ?case
  proof (cases "i < j")
    case False
    thus ?thesis unfolding simp by simp
  next
    case True
    note IH = 1[OF this]
    let ?n = neville_aitken_main
    have X: "\<And> i. degree (X i) = Suc 0" unfolding X_def by auto
    have "degree (X i * ?n (i + 1) j) \<le> Suc (degree (?n (i+1) j))"
      by (rule order.trans[OF degree_mult_le], simp add: X)
    also have "\<dots> \<le> Suc (j - (i+1))" using IH(1) by simp
    finally have 1: "degree (X i * ?n (i + 1) j) \<le> j - i" using True by auto
    have "degree (X j * ?n i (j - 1)) \<le> Suc (degree (?n i (j - 1)))"
      by (rule order.trans[OF degree_mult_le], simp add: X)
    also have "\<dots> \<le> Suc ((j - 1) - i)" using IH(2) by simp
    finally have 2: "degree (X j * ?n i (j - 1)) \<le> j - i" using True by auto
    have id: "?n i j = smult (inverse (x j - x i))
            (X i * ?n (i + 1) j - X j * ?n i (j - 1))" unfolding simp using True by simp
    have "degree (?n i j) \<le> degree (X i * ?n (i + 1) j - X j * ?n i (j - 1))"
      unfolding id by simp
    also have "\<dots> \<le> max (degree (X i * ?n (i + 1) j)) (degree (X j * ?n i (j - 1)))"
      by (rule degree_diff_le_max)
    also have "\<dots> \<le> j - i" using 1 2 by auto
    finally show ?thesis .
  qed
qed

lemma degree_neville_aitken: "degree (neville_aitken n) \<le> n"
  unfolding neville_aitken_def using degree_neville_aitken_main[of 0 n] by simp

fun neville_aitken_merge :: "('a \<times> 'a \<times> 'a poly) list \<Rightarrow> ('a \<times> 'a \<times> 'a poly) list" where
  "neville_aitken_merge ((xi,xj,p_ij) # (xsi,xsj,p_sisj) # rest) = 
     (xi,xsj, smult (inverse (xsj - xi)) ([:-xi,1:] * p_sisj
      + [:xsj,-1:] * p_ij)) # neville_aitken_merge ((xsi,xsj,p_sisj) # rest)"
| "neville_aitken_merge [_] = []"
| "neville_aitken_merge [] = []"

lemma length_neville_aitken_merge[termination_simp]: "length (neville_aitken_merge xs) = length xs - 1"
  by (induct xs rule: neville_aitken_merge.induct, auto)

fun neville_aitken_impl_main :: "('a \<times> 'a \<times> 'a poly) list \<Rightarrow> 'a poly" where
  "neville_aitken_impl_main (e1 # e2 # es) = 
     neville_aitken_impl_main (neville_aitken_merge (e1 # e2 # es))"
| "neville_aitken_impl_main [(_,_,p)] = p"
| "neville_aitken_impl_main [] = 0"

lemma neville_aitken_merge: 
  "xs = map (\<lambda> i. (x i, x (i + j), neville_aitken_main i (i + j)))  [l ..< Suc (l + k)] 
   \<Longrightarrow> neville_aitken_merge xs
       = (map (\<lambda> i. (x i, x (i + Suc j), neville_aitken_main i (i + Suc j))) [l ..< l + k])"
proof (induct xs arbitrary: l k rule: neville_aitken_merge.induct)
  case (1 xi xj p_ij xsi xsj p_sisj rest l k)
  let ?n = neville_aitken_main
  let ?f = "\<lambda> j i. (x i, x (i + j), ?n i (i + j))"
  define f where "f = ?f"
  let ?map = "\<lambda> j. map (?f j)"
  note res = 1(2)
  from arg_cong[OF res, of length] obtain kk where k: "k = Suc kk" by (cases k, auto)
  hence id: "[l..<Suc (l + k)] = l # [Suc l ..< Suc (Suc l + kk)]"
    by (simp add: upt_rec)
  from res[unfolded id] have id2: "(xsi, xsj, p_sisj) # rest =
    ?map j [Suc l..< Suc (Suc l + kk)]" 
    and id3: "xi = x l" "xj = x (l + j)" "p_ij = ?n l (l + j)" 
        "xsi = x (Suc l)" "xsj = x (Suc (l + j))" "p_sisj = ?n (Suc l) (Suc (l + j))"
      by (auto simp: upt_rec)
  note IH = 1(1)[OF id2]
  have X: "[:x (Suc (l + j)), - 1:] = - X (Suc l + j)" unfolding X_def by simp
  have id4: "(xi, xsj, smult (inverse (xsj - xi)) ([:- xi, 1:] * p_sisj +
     [:xsj, - 1:] * p_ij)) = (x l, x (l + Suc j), ?n l (l + Suc j))"
    unfolding id3 neville_aitken_main.simps[of l "l + Suc j"] 
      X_def[symmetric] X by simp
  have id5: "[l..<l + k] = l # [Suc l ..< Suc l + kk]" unfolding k
    by (simp add: upt_rec)
  show ?case unfolding neville_aitken_merge.simps IH id4
    unfolding id5 by simp
qed auto

lemma neville_aitken_impl_main: 
  "xs = map (\<lambda> i. (x i, x (i + j), neville_aitken_main i (i + j)))  [l ..< Suc (l + k)] 
   \<Longrightarrow> neville_aitken_impl_main xs = neville_aitken_main l (l + j + k)"
proof (induct xs arbitrary: l k j rule: neville_aitken_impl_main.induct)
  case (1 e1 e2 es l k j)
  note res = 1(2)
  from res obtain kk where k: "k = Suc kk" by (cases k, auto)
  hence id1: "l + k = Suc (l + kk)" by auto
  show ?case unfolding neville_aitken_impl_main.simps 1(1)[OF neville_aitken_merge[OF 1(2), unfolded id1]]
    by (simp add: k)
qed auto

lemma neville_aitken_impl:
  "xs = map (\<lambda> i. (x i, x i, [:f i:]))  [0 ..< Suc k] 
   \<Longrightarrow> neville_aitken_impl_main xs = neville_aitken k"
  unfolding neville_aitken_def using neville_aitken_impl_main[of xs 0 0 k]
  by (simp add: neville_aitken_main.simps)
end

lemma neville_aitken: assumes "\<And> i j. i < j \<Longrightarrow> j \<le> n \<Longrightarrow> x i \<noteq> x j"
  shows "j \<le> n \<Longrightarrow> poly (neville_aitken x f n) (x j) = (f j)"
  unfolding neville_aitken_def
  by (rule neville_aitken_main[OF assms, of n], auto)

definition neville_aitken_interpolation_poly :: "('a :: field \<times> 'a)list \<Rightarrow> 'a poly" where
  "neville_aitken_interpolation_poly x_fs = (let 
    start = map (\<lambda> (xi,fi). (xi,xi,[:fi:])) x_fs in 
    neville_aitken_impl_main start)"

lemma neville_aitken_interpolation_impl: assumes "x_fs \<noteq> []"
  shows "neville_aitken_interpolation_poly x_fs =
  neville_aitken (\<lambda> i. fst (x_fs ! i)) (\<lambda> i. snd (x_fs ! i)) (length x_fs - 1)"
proof -
  from assms have id: "Suc (length x_fs - 1) = length x_fs" by auto
  show ?thesis
    unfolding neville_aitken_interpolation_poly_def Let_def
    by (rule neville_aitken_impl, unfold id, rule nth_equalityI, auto split: prod.splits)
qed
  
lemma neville_aitken_interpolation_poly: assumes dist: "distinct (map fst xs_ys)"
  and p: "p = neville_aitken_interpolation_poly xs_ys"
  and xy: "(x,y) \<in> set xs_ys"
  shows "poly p x = y"
proof -
  have p: "p = neville_aitken (\<lambda> i. fst (xs_ys ! i)) (\<lambda> i. snd (xs_ys ! i)) (length xs_ys - 1)"
    unfolding p
    by (rule neville_aitken_interpolation_impl, insert xy, auto)
  from xy obtain i where i: "i < length xs_ys" and x: "x = fst (xs_ys ! i)" and y: "y = snd (xs_ys ! i)"
    unfolding set_conv_nth by (metis fst_conv in_set_conv_nth snd_conv xy)
  show ?thesis unfolding p x y
  proof (rule neville_aitken)
    fix i j
    show "i < j \<Longrightarrow> j \<le> length xs_ys - 1 \<Longrightarrow> fst (xs_ys ! i) \<noteq> fst (xs_ys ! j)" using dist
      by (metis (mono_tags, lifting) One_nat_def diff_less dual_order.strict_trans2 length_map 
        length_pos_if_in_set lessI less_or_eq_imp_le neq_iff nth_eq_iff_index_eq nth_map xy)
  qed (insert i, auto)
qed

lemma degree_neville_aitken_interpolation_poly:  
  shows "degree (neville_aitken_interpolation_poly xs_ys) \<le> length xs_ys - 1"
proof (cases "length xs_ys")
  case 0
  hence id: "xs_ys = []" by (cases xs_ys, auto)
  show ?thesis unfolding id neville_aitken_interpolation_poly_def Let_def by simp
next
  case (Suc nn)
  have id: "neville_aitken_interpolation_poly xs_ys = 
    neville_aitken (\<lambda> i. fst (xs_ys ! i)) (\<lambda> i. snd (xs_ys ! i)) (length xs_ys - 1)"
    by (rule neville_aitken_interpolation_impl, insert Suc, auto)
  show ?thesis unfolding id by (rule degree_neville_aitken)
qed

end
