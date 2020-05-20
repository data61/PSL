(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Maximal Degree during Reconstruction\<close>

text \<open>We define a function which computes an upper bound on the degree of
  a factor for which we have to reconstruct the integer values of the coefficients.
  This degree will determine how large the second parameter of the factor-bound will
  be.

  In essence, if the Berlekamp-factorization will produce $n$ factors with degrees
  $d_1,\ldots,d_n$, then our bound will be the sum of the $\frac{n}2$ largest degrees.
  The reason is that we will combine at most $\frac{n}2$ factors before reconstruction.

  Soundness of the bound is proven, as well as a monotonicity property.\<close>
  
theory Degree_Bound
  imports Containers.Set_Impl (* for sort_append_Cons_swap *)
  "HOL-Library.Multiset"
  Polynomial_Interpolation.Missing_Polynomial
  "Efficient-Mergesort.Efficient_Sort"
begin

definition max_factor_degree :: "nat list \<Rightarrow> nat" where 
  "max_factor_degree degs = (let 
     ds = sort degs
     in sum_list (drop (length ds div 2) ds))"

definition degree_bound where "degree_bound vs = max_factor_degree (map degree vs)" 

lemma insort_middle: "sort (xs @ x # ys) = insort x (sort (xs @ ys))"
  by (metis append.assoc sort_append_Cons_swap sort_snoc)

lemma sum_list_insort[simp]: 
  "sum_list (insort (d :: 'a :: {comm_monoid_add,linorder}) xs) = d + sum_list xs" 
proof (induct xs)
  case (Cons x xs)
  thus ?case by (cases "d \<le> x", auto simp: ac_simps)
qed simp

lemma half_largest_elements_mono: "sum_list (drop (length ds div 2) (sort ds))
    \<le> sum_list (drop (Suc (length ds) div 2) (insort (d :: nat) (sort ds)))"
proof -
  define n  where "n  = length ds div 2" 
  define m  where "m  = Suc (length ds) div 2"
  define xs where "xs = sort ds" 
  have xs: "sorted xs" unfolding xs_def by auto
  have nm: "m \<in> {n, Suc n}" unfolding n_def m_def by auto
  show ?thesis unfolding n_def[symmetric] m_def[symmetric] xs_def[symmetric]
    using nm xs
  proof (induct xs arbitrary: n m d)
    case (Cons x xs n m d)
    show ?case
    proof (cases n)
      case 0
      with Cons(2) have m: "m = 0 \<or> m = 1" by auto
      show ?thesis
      proof (cases "d \<le> x")
        case True
        hence ins: "insort d (x # xs) = d # x # xs" by auto
        show ?thesis unfolding ins 0 using True m by auto
      next
        case False
        hence ins: "insort d (x # xs) = x # insort d xs" by auto
        show ?thesis unfolding ins 0 using False m by auto
      qed
    next
      case (Suc nn)
      with Cons(2) obtain mm where m: "m = Suc mm" and mm: "mm \<in> {nn, Suc nn}" by auto
      from Cons(3) have sort: "sorted xs" by (simp)
      note IH = Cons(1)[OF mm]
      show ?thesis
      proof (cases "d \<le> x")
        case True
        with Cons(3) have ins: "insort d (x # xs) = d # insort x xs"
          by (cases xs, auto) 
        show ?thesis unfolding ins Suc m using IH[OF sort] by auto
      next
        case False
        hence ins: "insort d (x # xs) = x # insort d xs" by auto
        show ?thesis unfolding ins Suc m using IH[OF sort] Cons(3) by auto 
      qed
    qed
  qed auto
qed

lemma max_factor_degree_mono: 
  "max_factor_degree (map degree (fold remove1 ws vs)) \<le> max_factor_degree (map degree vs)" 
  unfolding max_factor_degree_def Let_def length_sort length_map 
proof (induct ws arbitrary: vs)
  case (Cons w ws vs)
  show ?case 
  proof (cases "w \<in> set vs")
    case False
    hence "remove1 w vs = vs" by (rule remove1_idem)
    thus ?thesis using Cons[of vs] by auto
  next
    case True
    then obtain bef aft where vs: "vs = bef @ w # aft" and rem1: "remove1 w vs = bef @ aft"
      by (metis remove1.simps(2) remove1_append split_list_first)
    let ?exp = "\<lambda> ws vs. sum_list (drop (length (fold remove1 ws vs) div 2) 
      (sort (map degree (fold remove1 ws vs))))" 
    let ?bnd = "\<lambda> vs. sum_list (drop (length vs div 2) (sort (map degree vs)))" 
    let ?bd = "\<lambda> vs. sum_list (drop (length vs div 2) (sort vs))" 
    define ba where "ba = bef @ aft" 
    define ds where "ds = map degree ba" 
    define d  where "d  = degree w" 
    have "?exp (w # ws) vs = ?exp ws (bef @ aft)" by (auto simp: rem1)
    also have "\<dots> \<le> ?bnd ba" unfolding ba_def by (rule Cons)
    also have "\<dots> = ?bd ds" unfolding ds_def by simp
    also have "\<dots> \<le> sum_list (drop (Suc (length ds) div 2) (insort d (sort ds)))" 
      by (rule half_largest_elements_mono)
    also have "\<dots> = ?bnd vs" unfolding vs ds_def d_def by (simp add: ba_def insort_middle)
    finally show "?exp (w # ws) vs \<le> ?bnd vs" by simp
  qed
qed auto

lemma mset_sub_decompose: "mset ds \<subseteq># mset bs + as \<Longrightarrow> length ds < length bs \<Longrightarrow> \<exists> b1 b b2. 
   bs = b1 @ b # b2 \<and> mset ds \<subseteq># mset (b1 @ b2) + as"
proof (induct ds arbitrary: bs as)
  case Nil
  hence "bs = [] @ hd bs # tl bs" by auto
  thus ?case by fastforce
next
  case (Cons d ds bs as)
  have "d \<in># mset (d # ds)" by auto
  with Cons(2) have d: "d \<in># mset bs + as" by (rule mset_subset_eqD)
  hence "d \<in> set bs \<or> d \<in># as" by auto
  thus ?case
  proof
    assume "d \<in> set bs" 
    from this[unfolded in_set_conv_decomp] obtain b1 b2 where bs: "bs = b1 @ d # b2" by auto
    from Cons(2) Cons(3) 
    have "mset ds \<subseteq># mset (b1 @ b2) + as" "length ds < length (b1 @ b2)" by (auto simp: ac_simps bs)
    from Cons(1)[OF this] obtain b1' b b2' where split: "b1 @ b2 = b1' @ b # b2'" 
      and sub: "mset ds \<subseteq># mset (b1' @ b2') + as" by auto
    from split[unfolded append_eq_append_conv2]
    obtain us where "b1 = b1' @ us \<and> us @ b2 = b # b2' \<or> b1 @ us = b1' \<and> b2 = us @ b # b2'" ..
    thus ?thesis
    proof
      assume "b1 @ us = b1' \<and> b2 = us @ b # b2'" 
      hence *: "b1 @ us = b1'" "b2 = us @ b # b2'" by auto
      hence bs: "bs = (b1 @ d # us) @ b # b2'" unfolding bs by auto
      show ?thesis
        by (intro exI conjI, rule bs, insert * sub, auto simp: ac_simps)
    next      
      assume "b1 = b1' @ us \<and> us @ b2 = b # b2'" 
      hence *: "b1 = b1' @ us" "us @ b2 = b # b2'" by auto
      show ?thesis
      proof (cases us)
        case Nil
        with * have *: "b1 = b1'" "b2 = b # b2'" by auto
        hence bs: "bs = (b1' @ [d]) @ b # b2'" unfolding bs by simp
        show ?thesis 
          by (intro exI conjI, rule bs, insert * sub, auto simp: ac_simps)
      next
        case (Cons u vs)
        with * have *: "b1 = b1' @ b # vs" "vs @ b2 = b2'" by auto
        hence bs: "bs = b1' @ b # (vs @ d # b2)" unfolding bs by auto
        show ?thesis 
          by (intro exI conjI, rule bs, insert * sub, auto simp: ac_simps)
      qed
    qed
  next
    define as' where "as' = as - {#d#}" 
    assume "d \<in># as" 
    hence as': "as = {#d#} + as'" unfolding as'_def by auto
    from Cons(2)[unfolded as'] Cons(3) have "mset ds \<subseteq># mset bs + as'" "length ds < length bs" 
      by (auto simp: ac_simps)
    from Cons(1)[OF this] obtain b1 b b2 where bs: "bs = b1 @ b # b2" and 
      sub: "mset ds \<subseteq># mset (b1 @ b2) + as'" by auto        
    show ?thesis
      by (intro exI conjI, rule bs, insert sub, auto simp: as' ac_simps)
  qed
qed
  

lemma max_factor_degree_aux: fixes es :: "nat list" 
  assumes sub: "mset ds \<subseteq># mset es" 
    and len: "length ds + length ds \<le> length es" and sort: "sorted es" 
  shows "sum_list ds \<le> sum_list (drop (length es div 2) es)"
proof - 
  define bef where "bef = take (length es div 2) es" 
  define aft where "aft = drop (length es div 2) es" 
  have es: "es = bef @ aft" unfolding bef_def aft_def by auto
  from len have len: "length ds \<le> length bef" "length ds \<le> length aft" unfolding bef_def aft_def 
    by auto
  from sub have sub: "mset ds \<subseteq># mset bef + mset aft" unfolding es by auto
  from sort have sort: "sorted (bef @ aft)" unfolding es .
  show ?thesis unfolding aft_def[symmetric] using sub len sort
  proof (induct ds arbitrary: bef aft)
    case (Cons d ds bef aft)
    have "d \<in># mset (d # ds)" by auto
    with Cons(2) have "d \<in># mset bef + mset aft" by (rule mset_subset_eqD)
    hence "d \<in> set bef \<or> d \<in> set aft" by auto
    thus ?case
    proof
      assume "d \<in> set aft" 
      from this[unfolded in_set_conv_decomp] obtain a1 a2 where aft: "aft = a1 @ d # a2" by auto
      from Cons(4) have len_a: "length ds \<le> length (a1 @ a2)" unfolding aft by auto
      from Cons(2)[unfolded aft] Cons(3) 
      have "mset ds \<subseteq># mset bef + (mset (a1 @ a2))" "length ds < length bef" by auto
      from mset_sub_decompose[OF this]
      obtain b b1 b2 
        where bef: "bef = b1 @ b # b2" and sub: "mset ds \<subseteq># (mset (b1 @ b2) + mset (a1 @ a2))" by auto
      from Cons(3) have len_b: "length ds \<le> length (b1 @ b2)" unfolding bef by auto
      from Cons(5)[unfolded bef aft] have sort: "sorted ( (b1 @ b2) @ (a1 @ a2))" 
        unfolding sorted_append by auto
      note IH = Cons(1)[OF sub len_b len_a sort]
      show ?thesis using IH unfolding aft by simp
    next
      assume "d \<in> set bef" 
      from this[unfolded in_set_conv_decomp] obtain b1 b2 where bef: "bef = b1 @ d # b2" by auto
      from Cons(3) have len_b: "length ds \<le> length (b1 @ b2)" unfolding bef by auto
      from Cons(2)[unfolded bef] Cons(4) 
      have "mset ds \<subseteq># mset aft + (mset (b1 @ b2))" "length ds < length aft" by (auto simp: ac_simps)
      from mset_sub_decompose[OF this]
      obtain a a1 a2 
        where aft: "aft = a1 @ a # a2" and sub: "mset ds \<subseteq># (mset (b1 @ b2) + mset (a1 @ a2))" 
        by (auto simp: ac_simps)
      from Cons(4) have len_a: "length ds \<le> length (a1 @ a2)" unfolding aft by auto
      from Cons(5)[unfolded bef aft] have sort: "sorted ( (b1 @ b2) @ (a1 @ a2))" and ad: "d \<le> a"
        unfolding sorted_append by auto
      note IH = Cons(1)[OF sub len_b len_a sort]
      show ?thesis using IH ad unfolding aft by simp
    qed
  qed auto
qed 

lemma max_factor_degree: assumes sub: "mset ws \<subseteq># mset vs"
  and len: "length ws + length ws \<le> length vs"
  shows "degree (prod_list ws) \<le> max_factor_degree (map degree vs)"
proof -
  define ds where "ds \<equiv> map degree ws"
  define es where "es \<equiv> sort (map degree vs)"
  from sub len have sub: "mset ds \<subseteq># mset es" and len: "length ds + length ds \<le> length es"
    and es: "sorted es"
    unfolding ds_def es_def
    by (auto simp: image_mset_subseteq_mono)
  have "degree (prod_list ws) \<le> sum_list (map degree ws)" by (rule degree_prod_list_le)
  also have "\<dots> \<le> max_factor_degree (map degree vs)"
    unfolding max_factor_degree_def Let_def ds_def[symmetric] es_def[symmetric]
    using sub len es by (rule max_factor_degree_aux)
  finally show ?thesis .
qed

lemma degree_bound: assumes sub: "mset ws \<subseteq># mset vs"
  and len: "length ws + length ws \<le> length vs"
shows "degree (prod_list ws) \<le> degree_bound vs" 
  using max_factor_degree[OF sub len] unfolding degree_bound_def by auto

end
