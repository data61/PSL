(*
    Authors:    René Thiemann
    License:    BSD
*)
subsection \<open>Integer LLL Implementation which Stores Multiples of the $\mu$-Values\<close>

text \<open>In this part we aim to update the integer values $d\,(j+1) * \mu_{i,j}$ as well as the
  Gramian determinants $d\,i$. \<close>


theory LLL_Impl
  imports
   LLL
   List_Representation
   Gram_Schmidt_Int
begin

subsubsection \<open>Updates of the integer values for Swap, Add, etc.\<close>

text \<open>We provide equations how to implement the LLL-algorithm by storing the integer values
  $d\, (j+1) * \mu_{i,j}$ and all $d\ i$ in addition to the vectors in $f$.
  Moreover, we show how to check condition like the one on norms via the integer values.\<close>

definition round_num_denom :: "int \<Rightarrow> int \<Rightarrow> int" where
  "round_num_denom n d = ((2 * n + d) div (2 * d))" 

lemma round_num_denom: "round_num_denom num denom = 
  round (of_int num / rat_of_int denom)" 
proof (cases "denom = 0")
  case False
  have "denom \<noteq> 0 \<Longrightarrow> ?thesis" 
    unfolding round_def round_num_denom_def
    unfolding floor_divide_of_int_eq[where ?'a = rat, symmetric]
    by (rule arg_cong[of _ _ floor], simp add: add_divide_distrib)
  with False show ?thesis by auto
next
  case True
  show ?thesis unfolding True round_num_denom_def by auto
qed

context fs_int_indpt
begin
lemma round_num_denom_d\<mu>_d:
  assumes j: "j \<le> i" and i: "i < m"  
shows "round_num_denom (d\<mu> i j) (d fs (Suc j)) = round (gs.\<mu> i j)" 
proof -
  from j i have sj: "Suc j \<le> m" by auto
  show ?thesis unfolding round_num_denom
    by (rule arg_cong[of _ _ round], subst d\<mu>[OF _ i], insert j i fs_int_d_pos[OF sj], auto)
qed

lemma d_sq_norm_comparison:
  assumes quot: "quotient_of \<alpha> = (num,denom)" 
  and i: "i < m" 
  and i0: "i \<noteq> 0" 
  shows "(d fs i * d fs i * denom \<le> num * d fs (i - 1) * d fs (Suc i))
   = (sq_norm (gs.gso (i - 1)) \<le> \<alpha> * sq_norm (gs.gso i))" 
proof -
  let ?r = "rat_of_int" 
  let ?x = "sq_norm (gs.gso (i - 1))" 
  let ?y = "\<alpha> * sq_norm (gs.gso i)" 
  from i have le: "i - 1 \<le> m" " i \<le> m" "Suc i \<le> m" by auto
  note pos = fs_int_d_pos[OF le(1)] fs_int_d_pos[OF le(2)] quotient_of_denom_pos[OF quot]
  have "(d fs i * d fs i * denom \<le> num * d fs (i - 1) * d fs (Suc i))
    = (?r (d fs i * d fs i * denom) \<le> ?r (num * d fs (i - 1) * d fs (Suc i)))" (is "?cond = _") by presburger
  also have "\<dots> = (?r (d fs i) * ?r (d fs i) * ?r denom \<le> ?r num * ?r (d fs (i - 1)) * ?r (d fs (Suc i)))" by simp
  also have "\<dots> = (?r (d fs i) * ?r (d fs i) \<le> \<alpha> * ?r (d fs (i - 1)) * ?r (d fs (Suc i)))" 
    using pos unfolding quotient_of_div[OF quot] by (auto simp: field_simps)
  also have "\<dots> = (?r (d fs i) / ?r (d fs (i - 1)) \<le> \<alpha> * (?r (d fs (Suc i)) / ?r (d fs i)))" 
    using pos by (auto simp: field_simps)
  also have "?r (d fs i) / ?r (d fs (i - 1)) = ?x" using fs_int_d_Suc[of "i - 1"] pos i i0
    by (auto simp: field_simps)
  also have "\<alpha> * (?r (d fs (Suc i)) / ?r (d fs i)) = ?y" using fs_int_d_Suc[OF i] pos i i0
    by (auto simp: field_simps)
  finally show "?cond = (?x \<le> ?y)" .
qed

end


context LLL
begin

lemma d_d\<mu>_add_row: assumes Linv: "LLL_invariant True i fs"
  and i: "i < m"  and j: "j < i" 
  and fs': "fs' = fs[ i := fs ! i - c \<cdot>\<^sub>v fs ! j]" 
shows  
  (* d-updates: none *)
  "\<And> ii. ii \<le> m \<Longrightarrow> d fs' ii = d fs ii" 
  (* d\<mu>-updates: *)
  "\<And> i' j'. i' < m \<Longrightarrow> j' < i' \<Longrightarrow>       
     d\<mu> fs' i' j' = (
       if i' = i \<and> j' < j 
         then d\<mu> fs i' j' - c * d\<mu> fs j j' 
       else if i' = i \<and> j' = j 
         then d\<mu> fs i' j' - c * d fs (Suc j) 
       else d\<mu> fs i' j')"
    (is "\<And> i' j'. _ \<Longrightarrow> _ \<Longrightarrow> _ = ?new_mu i' j'")
proof -
  interpret fs: fs_int' n m fs_init \<alpha> True i fs
    by standard (use Linv in auto)
  note add = basis_reduction_add_row_main[OF Linv i j fs']
  interpret fs': fs_int' n m fs_init \<alpha> True i fs'
    by standard (use add in auto)
  show d: "\<And> ii. ii \<le> m \<Longrightarrow> d fs' ii = d fs ii" by fact
  fix i' j'
  assume i': "i' < m" and j': "j' < i'"    
  hence j'm: "j' < m" and j'': "j' \<le> i'" by auto
  note updates = add(5)[OF i' j'm]
  show "d\<mu> fs' i' j' = ?new_mu i' j'" 
  proof (cases "i' = i")
    case False
    thus ?thesis using d i' j' unfolding d\<mu>_def updates by auto
  next
    case True
    have id': "d fs' (Suc j') = d fs (Suc j')" by (rule d, insert i' j', auto)
    note fs'.d\<mu>[]
    have *: "rat_of_int (d\<mu> fs' i' j') = rat_of_int (d fs' (Suc j')) * fs'.gs.\<mu> i' j'"
      unfolding d\<mu>_def d_def
      apply(rule fs'.d\<mu>[unfolded fs'.d\<mu>_def fs'.d_def])
      using j' i'  LLL_invD[OF add(1)]  by (auto)
    have **: "rat_of_int (d\<mu> fs i' j') = rat_of_int (d fs (Suc j')) * fs.gs.\<mu> i' j'"
      unfolding d\<mu>_def d_def
      apply(rule fs.d\<mu>[unfolded fs.d\<mu>_def fs.d_def])
      using j' i' LLL_invD[OF Linv]  by (auto)
    have ***: "rat_of_int (d\<mu> fs j j') = rat_of_int (d fs (Suc j')) * fs.gs.\<mu> j j'" if "j' < j"
      unfolding d\<mu>_def d_def
      apply(rule fs.d\<mu>[unfolded fs.d\<mu>_def fs.d_def])
      using that j i LLL_invD[OF Linv]  by (auto)

    show ?thesis
      apply(intro int_via_rat_eqI)
      apply(unfold if_distrib[of rat_of_int] of_int_diff of_int_mult ** * updates id' ring_distribs)
      apply(insert True i' j' i j)
      by(auto simp: fs.gs.\<mu>.simps algebra_simps ***)
  qed
qed

end

context LLL_with_assms
begin

lemma d_d\<mu>_swap: assumes inv: "LLL_invariant False k fs"
  and k: "k < m"
  and k0: "k \<noteq> 0" 
  and norm_ineq: "sq_norm (gso fs (k - 1)) > \<alpha> * sq_norm (gso fs k)" 
  and fs'_def: "fs' = fs[k := fs ! (k - 1), k - 1 := fs ! k]" 
shows (* d-updates *)
  "\<And> i. i \<le> m \<Longrightarrow>
      d fs' i = (
        if i = k then 
          (d fs (Suc k) * d fs (k - 1) + d\<mu> fs k (k - 1) * d\<mu> fs k (k - 1)) div d fs k 
        else d fs i)"
and (* d\<mu>-updates *)
  "\<And> i j. i < m \<Longrightarrow> j < i \<Longrightarrow> 
      d\<mu> fs' i j = (
        if i = k - 1 then 
           d\<mu> fs k j
        else if i = k \<and> j \<noteq> k - 1 then 
             d\<mu> fs (k - 1) j
        else if i > k \<and> j = k then
           (d fs (Suc k) * d\<mu> fs i (k - 1) - d\<mu> fs k (k - 1) * d\<mu> fs i j) div d fs k
        else if i > k \<and> j = k - 1 then 
           (d\<mu> fs k (k - 1) * d\<mu> fs i j + d\<mu> fs i k * d fs (k - 1)) div d fs k
        else d\<mu> fs i j)" 
    (is "\<And> i j. _ \<Longrightarrow> _ \<Longrightarrow> _ = ?new_mu i j")
proof -
  note swap = basis_reduction_swap_main[OF inv k k0 norm_ineq fs'_def]
  from k k0 have kk: "k - 1 < k" and le_m: "k - 1 \<le> m" "k \<le> m" "Suc k \<le> m" by auto
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  interpret fs: fs_int' n m fs_init \<alpha> False k fs
    by standard (use inv in auto)
  interpret fs': fs_int' n m fs_init \<alpha> False "k - 1" fs'
    by standard (use swap(1) in auto)
  let ?r = rat_of_int
  let ?n = "\<lambda> i. sq_norm (gso fs i)" 
  let ?n' = "\<lambda> i. sq_norm (gso fs' i)" 
  let ?dn = "\<lambda> i. ?r (d fs i * d fs i) * ?n i" 
  let ?dn' = "\<lambda> i. ?r (d fs' i * d fs' i) * ?n' i" 
  let ?dmu = "\<lambda> i j. ?r (d fs (Suc j)) * \<mu> fs i j" 
  let ?dmu' = "\<lambda> i j. ?r (d fs' (Suc j)) * \<mu> fs' i j" 
  note dmu = fs.d\<mu>
  note dmu' = fs'.d\<mu>
  note inv' = LLL_invD[OF inv]
  have nim1: "?n k + square_rat (\<mu> fs k (k - 1)) * ?n (k - 1) = 
    ?n' (k - 1)" by (subst swap(4), insert k, auto)
  have ni: "?n k * (?n (k - 1) / ?n' (k - 1)) = ?n' k"
    by (subst swap(4)[of k], insert k k0, auto)
  have mu': "\<mu> fs k (k - 1) * (?n (k - 1) / ?n' (k - 1)) = \<mu> fs' k (k - 1)"
    by (subst swap(5), insert k k0, auto)
  have fi: "fs ! (k - 1) = fs' ! k" "fs ! k = fs' ! (k - 1)" 
    unfolding fs'_def using inv'(6) k k0 by auto
  let ?d'i = "(d fs (Suc k) * d fs (k - 1) + d\<mu> fs k (k - 1) * d\<mu> fs k (k - 1)) div (d fs k)" 
  have rat': "i < m \<Longrightarrow> j < i \<Longrightarrow> ?r (d\<mu> fs' i j) = ?dmu' i j" for i j 
     using dmu'[of j i] LLL_invD[OF swap(1)] unfolding d\<mu>_def fs'.d\<mu>_def d_def fs'.d_def by auto
   have rat: "i < m \<Longrightarrow> j < i \<Longrightarrow> ?r (d\<mu> fs i j) = ?dmu i j" for i j
     using dmu[of j i] LLL_invD[OF inv] unfolding d\<mu>_def fs.d\<mu>_def d_def fs.d_def by auto
  from k k0 have sim1: "Suc (k - 1) = k" and km1: "k - 1 < m" by auto
  from LLL_d_Suc[OF inv km1, unfolded sim1] 
  have dn_km1: "?dn (k - 1) = ?r (d fs k) * ?r (d fs (k - 1))" by simp
  note pos = Gramian_determinant[OF inv le_refl] 
  from pos(2) have "?r (gs.Gramian_determinant fs m) \<noteq> 0" by auto
  from this[unfolded pos(1)] have nzero: "i < m \<Longrightarrow> ?n i \<noteq> 0" for i by auto
  note pos = Gramian_determinant[OF swap(1) le_refl] 
  from pos(2) have "?r (gs.Gramian_determinant fs' m) \<noteq> 0" by auto
  from this[unfolded pos(1)] have nzero': "i < m \<Longrightarrow> ?n' i \<noteq> 0" for i by auto
  have dzero: "i \<le> m \<Longrightarrow> d fs i \<noteq> 0" for i using LLL_d_pos[OF inv, of i] by auto
  have dzero': "i \<le> m \<Longrightarrow> d fs' i \<noteq> 0" for i using LLL_d_pos[OF swap(1), of i] by auto

  {
    define start where "start = ?dmu' k (k - 1)" 
    have "start = (?n' (k - 1) / ?n (k - 1) * ?r (d fs k)) * \<mu> fs' k (k - 1)" 
      using start_def swap(6)[of k] k k0 by simp
    also have "\<mu> fs' k (k - 1) = \<mu> fs k (k - 1) * (?n (k - 1) / ?n' (k - 1))" 
      using mu' by simp
    also have "(?n' (k - 1) / ?n (k - 1) * ?r (d fs k)) * \<dots> = ?r (d fs k) * \<mu> fs k (k - 1)" 
      using nzero[OF km1] nzero'[OF km1] by simp
    also have "\<dots> = ?dmu k (k - 1)" using k0 by simp
    finally have "?dmu' k (k - 1) = ?dmu k (k - 1)" unfolding start_def .
  } note dmu_i_im1 = this
  { (* d updates *)
    fix j
    assume j: "j \<le> m" 
    define start where "start = d fs' j" 
    {
      assume jj: "j \<noteq> k" 
      have "?r start = ?r (d fs' j)" unfolding start_def ..
      also have "?r (d fs' j) = ?r (d fs j)" 
        by (subst swap(6), insert j jj, auto)
      finally have "start = d fs j" by simp
    } note d_j = this 
    {
      assume jj: "j = k"  
      have "?r start = ?r (d fs' k)" unfolding start_def unfolding jj by simp
      also have "\<dots> = ?n' (k - 1) / ?n (k - 1) * ?r (d fs k)" 
        by (subst swap(6), insert k, auto)
      also have "?n' (k - 1) = (?r (d fs k) / ?r (d fs k)) * (?r (d fs k) / ?r (d fs k)) 
          * (?n k  + \<mu> fs k (k - 1) * \<mu> fs k (k - 1) * ?n (k - 1))" 
        by (subst swap(4)[OF km1], insert dzero[of k], insert k, simp)
      also have "?n (k - 1) = ?r (d fs k) / ?r (d fs (k - 1))" 
        unfolding LLL_d_Suc[OF inv km1, unfolded sim1] using dzero[of "k - 1"] k k0 by simp
      finally have "?r start = 
          ((?r (d fs k) * ?n k) * ?r (d fs (k - 1)) + ?dmu k (k - 1) * ?dmu k (k - 1)) 
          / (?r (d fs k))" 
        using k k0 dzero[of k] dzero[of "k - 1"]
        by (simp add: ring_distribs)
      also have "?r (d fs k) * ?n k = ?r (d fs (Suc k))" 
        unfolding LLL_d_Suc[OF inv k] by simp
      also have "?dmu k (k - 1) = ?r (d\<mu> fs k (k - 1))" by (subst rat, insert k k0, auto)
      finally have "?r start = (?r (d fs (Suc k) * d fs (k - 1) + d\<mu> fs k (k - 1) * d\<mu> fs k (k - 1)))
          / (?r (d fs k))" by simp
      from division_to_div[OF this]
      have "start = ?d'i" .
    } note d_i = this
    from d_j d_i show "d fs' j = (if j = k then ?d'i else d fs j)" unfolding start_def by auto
  } 
  have "length fs' = m" 
    using fs'_def inv'(6) by auto
  {
    fix i j
    assume i: "i < m" and j: "j < i" 
    from j i have sj: "Suc j \<le> m" by auto
    note swaps = swap(5)[OF i j] swap(6)[OF sj]
    show "d\<mu> fs' i j = ?new_mu i j" 
    proof (cases "i < k - 1")
      case small: True
      hence id: "?new_mu i j = d\<mu> fs i j" by auto
      show ?thesis using swaps small i j k k0 by (auto simp: d\<mu>_def)
    next
      case False
      from j i have sj: "Suc j \<le> m" by auto
      let ?start = "d\<mu> fs' i j" 
      define start where "start = ?start" 
      note rat'[OF i j]
      note rat_i_j = rat[OF i j]
      from False consider (i_k) "i = k" "j = k - 1" | (i_small) "i = k" "j \<noteq> k - 1" | 
          (i_km1) "i = k - 1" | (i_large) "i > k" by linarith
      thus ?thesis
      proof cases
        case *: i_small
        show ?thesis unfolding swaps d\<mu>_def using * i k k0 by auto
      next
        case *: i_k
        show ?thesis using dmu_i_im1 rat_i_j * k0 by (auto simp: d\<mu>_def)
      next
        case *: i_km1
        show ?thesis unfolding swaps d\<mu>_def using * i j k k0 by auto
      next
        case *: i_large
        consider (jj) "j \<noteq> k - 1" "j \<noteq> k" | (ji) "j = k" | (jim1) "j = k - 1" by linarith
        thus ?thesis 
        proof cases
          case jj
          show ?thesis unfolding swaps d\<mu>_def using * i j jj k k0 by auto
        next
          case ji
          have "?r start = ?dmu' i j" unfolding start_def by fact
          also have "?r (d fs' (Suc j)) = ?r (d fs (Suc k))" unfolding swaps unfolding ji by simp 
          also have "\<mu> fs' i j = \<mu> fs i (k - 1) - \<mu> fs k (k - 1) * \<mu> fs i k" 
            unfolding swaps unfolding ji using k0 * by auto
          also have "?r (d fs (Suc k)) * \<dots> = ?r (d fs (Suc k)) * ?r (d fs k) / ?r (d fs k) * \<dots>" 
            using dzero[of k] k by auto
          also have "\<dots> =  
            (?r (d fs (Suc k)) * ?dmu i (k - 1) - ?dmu k (k - 1) * ?dmu i k) / ?r (d fs k)" 
            using k0 by (simp add: field_simps)
          also have "\<dots> = 
            (?r (d fs (Suc k)) * ?r (d\<mu> fs i (k - 1)) - ?r (d\<mu> fs k (k - 1)) * ?r (d\<mu> fs i k)) / ?r (d fs k)" 
            by (subst (1 2 3) rat, insert k k0 i *, auto)
          also have "\<dots> = ?r (d fs (Suc k) * d\<mu> fs i (k - 1) - d\<mu> fs k (k - 1) * d\<mu> fs i k) / ?r (d fs k)" 
            (is "_ = of_int ?x / _")
            by simp
          finally have "?r start = ?r ?x / ?r (d fs k)" .
          from division_to_div[OF this]
          have id: "?start = (d fs (Suc k) * d\<mu> fs i (k - 1) - d\<mu> fs k (k - 1) * d\<mu> fs i j) div d fs k" 
            unfolding start_def ji .
          show ?thesis unfolding id using * ji by simp
        next
          case jim1
          hence id'': "(j = k - 1) = True" "(j = k) = False" using k0 by auto
          have "?r (start) = ?dmu' i j" unfolding start_def by fact
          also have "\<mu> fs' i j = \<mu> fs i (k - 1) * \<mu> fs' k (k - 1) +
                             \<mu> fs i k * ?n k / ?n' (k - 1)" (is "_ = ?x1 + ?x2")
            unfolding swaps unfolding jim1 using k0 * by auto
          also have "?r (d fs' (Suc j)) * (?x1 + ?x2)
              = ?r (d fs' (Suc j)) * ?x1 + ?r (d fs' (Suc j)) * ?x2" by (simp add: ring_distribs)
          also have "?r (d fs' (Suc j)) * ?x1 = ?dmu' k (k - 1) * (?r (d fs k) * \<mu> fs i (k - 1))
            / ?r (d fs k)"
            unfolding jim1 using k0 dzero[of k] k by simp
          also have "?dmu' k (k - 1) = ?dmu k (k - 1)" by fact
          also have "?r (d fs k) * \<mu> fs i (k - 1) = ?dmu i (k - 1)" using k0 by simp
          also have "?r (d fs' (Suc j)) = ?n' (k - 1) * ?r (d fs k) / ?n (k - 1)" 
            unfolding swaps unfolding jim1 using k k0 by simp 
          also have "\<dots> * ?x2 = (?n k * ?r (d fs k)) / ?n (k - 1) * \<mu> fs i k" 
            using k k0 nzero'[of "k - 1"] by simp
          also have "?n k * ?r (d fs k) = ?r (d fs (Suc k))" unfolding LLL_d_Suc[OF inv k] ..
          also have "?r (d fs (Suc k)) / ?n (k - 1) * \<mu> fs i k = ?dmu i k / ?n (k - 1)" by simp
          also have "\<dots> = ?dmu i k * ?r (d fs (k - 1) * d fs (k - 1)) / ?dn (k - 1)" 
            using dzero[of "k - 1"] k by simp
          finally have "?r start = (?dmu k (k - 1) * ?dmu i j * ?dn (k - 1) + 
             ?dmu i k * (?r (d fs (k - 1) * d fs (k - 1) * d fs k))) / (?r (d fs k) * ?dn (k - 1))"
            unfolding add_divide_distrib of_int_mult jim1
            using dzero[of "k - 1"] nzero[of "k - 1"] k dzero[of k] by auto
          also have "\<dots> = (?r (d\<mu> fs k (k - 1)) * ?r (d\<mu> fs i j) * (?r (d fs k) * ?r (d fs (k - 1))) + 
             ?r (d\<mu> fs i k) * (?r (d fs (k - 1) * d fs (k - 1) * d fs k))) / (?r (d fs k) * (?r (d fs k) * ?r (d fs (k - 1))))" 
            unfolding dn_km1 
            by (subst (1 2 3) rat, insert k k0 i * j, auto)
          also have "\<dots> = (?r (d\<mu> fs k (k - 1)) * ?r (d\<mu> fs i j) + ?r (d\<mu> fs i k) * ?r (d fs (k - 1))) 
              / ?r (d fs k)" 
            unfolding of_int_mult using dzero[of k] dzero[of "k - 1"] k k0 by (auto simp: field_simps)
          also have "\<dots> = ?r (d\<mu> fs k (k - 1) * d\<mu> fs i j + d\<mu> fs i k * d fs (k - 1)) / ?r (d fs k)" 
            (is "_ = of_int ?x / _" )
            by simp
          finally have "?r start = ?r ?x / ?r (d fs k)" .
          from division_to_div[OF this]
          have id: "?start = (d\<mu> fs k (k - 1) * d\<mu> fs i j + d\<mu> fs i k * d fs (k - 1)) div (d fs k)" 
            unfolding start_def .
          show ?thesis unfolding id using * jim1 k0 by auto
        qed
      qed
    qed
  }
qed
end


subsubsection \<open>Implementation of LLL via Integer Operations and Arrays\<close>


hide_fact (open) Word.inc_i

type_synonym LLL_dmu_d_state = "int vec list_repr \<times> int iarray iarray \<times> int iarray"

fun fi_state :: "LLL_dmu_d_state \<Rightarrow> int vec" where
  "fi_state (f,mu,d) = get_nth_i f"

fun fim1_state :: "LLL_dmu_d_state \<Rightarrow> int vec" where
  "fim1_state (f,mu,d) = get_nth_im1 f"

fun d_state :: "LLL_dmu_d_state \<Rightarrow> nat \<Rightarrow> int" where
  "d_state (f,mu,d) i = d !! i"

fun fs_state :: "LLL_dmu_d_state \<Rightarrow> int vec list" where
  "fs_state (f,mu,d) = of_list_repr f"

fun upd_fi_mu_state :: "LLL_dmu_d_state \<Rightarrow> nat \<Rightarrow> int vec \<Rightarrow> int iarray \<Rightarrow> LLL_dmu_d_state" where
  "upd_fi_mu_state (f,mu,d) i fi mu_i = (update_i f fi, iarray_update mu i mu_i,d)"

fun small_fs_state :: "LLL_dmu_d_state \<Rightarrow> int vec list" where
  "small_fs_state (f,_) = fst f"

fun dmu_ij_state :: "LLL_dmu_d_state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "dmu_ij_state (f,mu,_) i j = mu !! i !! j"

fun inc_state :: "LLL_dmu_d_state \<Rightarrow> LLL_dmu_d_state" where
  "inc_state (f,mu,d) = (inc_i f, mu, d)"

fun basis_reduction_add_rows_loop where
  "basis_reduction_add_rows_loop n state i j [] = state"
| "basis_reduction_add_rows_loop n state i sj (fj # fjs) = (
     let fi = fi_state state;
         dsj = d_state state sj;
         j = sj - 1;
         c = round_num_denom (dmu_ij_state state i j) dsj;
         state' = (if c = 0 then state else upd_fi_mu_state state i (vec n (\<lambda> i. fi $ i - c * fj $ i))
             (IArray.of_fun (\<lambda> jj. let mu = dmu_ij_state state i jj in
                  if jj < j then mu - c * dmu_ij_state state j jj else
                  if jj = j then mu - dsj * c else mu) i))
      in basis_reduction_add_rows_loop n state' i j fjs)"

text \<open>More efficient code which breaks abstraction of state.\<close>

lemma basis_reduction_add_rows_loop_code:
  "basis_reduction_add_rows_loop n state i sj (fj # fjs) = (
     case state of ((f1,f2),mus,ds) \<Rightarrow>
     let fi = hd f2;
         j = sj - 1;
         dsj = ds !! sj;
         mui = mus !! i;
         c = round_num_denom (mui !! j) dsj
      in (if c = 0 then
          basis_reduction_add_rows_loop n state i j fjs
         else
             let muj = mus !! j in
           basis_reduction_add_rows_loop n
                ((f1,  vec n (\<lambda> i. fi $ i - c * fj $ i) # tl f2), iarray_update mus i
             (IArray.of_fun (\<lambda> jj. let mu = mui !! jj in
                  if jj < j then mu - c * muj !! jj else
                  if jj = j then mu - dsj * c else mu) i),
                  ds) i j fjs))"
proof -
  obtain f1 f2 mus ds where state: "state = ((f1,f2),mus, ds)" by (cases state, auto)
  show ?thesis unfolding basis_reduction_add_rows_loop.simps Let_def
     state split dmu_ij_state.simps fi_state.simps get_nth_i_def update_i_def upd_fi_mu_state.simps
     d_state.simps
    by simp
qed

lemmas basis_reduction_add_rows_loop_code_equations =
  basis_reduction_add_rows_loop.simps(1) basis_reduction_add_rows_loop_code

declare basis_reduction_add_rows_loop_code_equations[code]


definition basis_reduction_add_rows where
  "basis_reduction_add_rows n upw i state =
     (if upw
        then basis_reduction_add_rows_loop n state i i (small_fs_state state)
        else state)"

context
  fixes \<alpha> :: rat and n m :: nat and fs_init :: "int vec list"
begin

definition swap_mu :: "int iarray iarray \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int iarray iarray" where
  "swap_mu dmu i dmu_i_im1 dim1 di dsi = (let im1 = i - 1 in
       IArray.of_fun (\<lambda> ii. if ii < im1 then dmu !! ii else
       if ii > i then let dmu_ii = dmu !! ii in
           IArray.of_fun (\<lambda> j. let dmu_ii_j = dmu_ii !! j in
               if j = i then (dsi * dmu_ii !! im1 - dmu_i_im1 * dmu_ii_j) div di
               else if j = im1 then (dmu_i_im1 * dmu_ii_j + dmu_ii !! i * dim1) div di
               else dmu_ii_j) ii else
       if ii = i then let mu_im1 = dmu !! im1 in
           IArray.of_fun (\<lambda> j. if j = im1 then dmu_i_im1 else mu_im1 !! j) ii
         else IArray.of_fun (\<lambda> j. dmu !! i !! j) ii) \<comment> \<open>ii = i - 1\<close>
       m)"

definition basis_reduction_swap where
  "basis_reduction_swap i state = (let
       di = d_state state i;
       dsi = d_state state (Suc i);
       dim1 = d_state state (i - 1);
       fi = fi_state state;
       fim1 = fim1_state state;
       dmu_i_im1 = dmu_ij_state state i (i - 1);
       fi' = fim1;
       fim1' = fi
     in (case state of (f,dmus,djs) \<Rightarrow>
         (False, i - 1,
           (dec_i (update_im1 (update_i f fi') fim1'),
            swap_mu dmus i dmu_i_im1 dim1 di dsi,
            iarray_update djs i ((dsi * dim1 + dmu_i_im1 * dmu_i_im1) div di)))))"

text \<open>More efficient code which breaks abstraction of state.\<close>

lemma basis_reduction_swap_code[code]:
  "basis_reduction_swap i ((f1,f2), dmus, ds) = (let
       di = ds !! i;
       dsi = ds !! (Suc i);
       im1 = i - 1;
       dim1 = ds !! im1;
       fi = hd f2;
       fim1 = hd f1;
       dmu_i_im1 = dmus !! i !! im1;
       fi' = fim1;
       fim1' = fi
     in (False, im1,
           ((tl f1,fim1' # fi' # tl f2),
            swap_mu dmus i dmu_i_im1 dim1 di dsi,
            iarray_update ds i ((dsi * dim1 + dmu_i_im1 * dmu_i_im1) div di))))"
proof -
  show ?thesis unfolding basis_reduction_swap_def split Let_def fi_state.simps fim1_state.simps
    d_state.simps get_nth_im1_def get_nth_i_def update_i_def update_im1_def dec_i_def
    by simp
qed

definition basis_reduction_step where
  "basis_reduction_step upw i state = (if i = 0 then (True, Suc i, inc_state state)
     else let
       state' = basis_reduction_add_rows n upw i state;
       di = d_state state' i;
       dsi = d_state state' (Suc i);
       dim1 = d_state state' (i - 1);
       (num,denom) = quotient_of \<alpha>
    in if di * di * denom \<le> num * dim1 * dsi then
          (True, Suc i, inc_state state')
        else basis_reduction_swap i state')"

partial_function (tailrec) basis_reduction_main where
  [code]: "basis_reduction_main upw i state = (if i < m
     then case basis_reduction_step upw i state of (upw',i',state') \<Rightarrow>
       basis_reduction_main upw' i' state' else
       state)"

definition "initial_state = (let
  dmus = d\<mu>_impl fs_init;
  ds = IArray.of_fun (\<lambda> i. if i = 0 then 1 else let i1 = i - 1 in dmus !! i1 !! i1) (Suc m);
  dmus' = IArray.of_fun (\<lambda> i. let row_i = dmus !! i in
       IArray.of_fun (\<lambda> j. row_i !! j) i) m
  in (([], fs_init), dmus', ds) :: LLL_dmu_d_state)"

end

definition "basis_reduction \<alpha> n fs = (let m = length fs in
  basis_reduction_main \<alpha> n m True 0 (initial_state m fs))"

definition "reduce_basis \<alpha> fs = (case fs of Nil \<Rightarrow> fs | Cons f _ \<Rightarrow> fs_state (basis_reduction \<alpha> (dim_vec f) fs))"

definition "short_vector \<alpha> fs = hd (reduce_basis \<alpha> fs)"

lemma map_rev_Suc: "map f (rev [0..<Suc j]) = f j # map f (rev [0..< j])" by simp

context LLL
begin

definition mu_repr :: "int iarray iarray \<Rightarrow> int vec list \<Rightarrow> bool" where
  "mu_repr mu fs = (mu = IArray.of_fun (\<lambda> i. IArray.of_fun (d\<mu> fs i) i) m)"

definition d_repr :: "int iarray \<Rightarrow> int vec list \<Rightarrow> bool" where
  "d_repr ds fs = (ds = IArray.of_fun (d fs) (Suc m))"

fun LLL_impl_inv :: "LLL_dmu_d_state \<Rightarrow> nat \<Rightarrow> int vec list \<Rightarrow> bool" where
  "LLL_impl_inv (f,mu,ds) i fs = (list_repr i f (map (\<lambda> j. fs ! j) [0..<m])
    \<and> d_repr ds fs
    \<and> mu_repr mu fs)"

context fixes state i fs upw f mu ds
  assumes impl: "LLL_impl_inv state i fs"
  and inv: "LLL_invariant upw i fs"
  and state: "state = (f,mu,ds)"
begin
lemma to_list_repr: "list_repr i f (map ((!) fs) [0..<m])"
  using impl[unfolded state] by auto

lemma to_mu_repr: "mu_repr mu fs" using impl[unfolded state] by auto
lemma to_d_repr: "d_repr ds fs" using impl[unfolded state] by auto

lemma dmu_ij_state: assumes j: "j < ii"
  and ii: "ii < m"
shows "dmu_ij_state state ii j = d\<mu> fs ii j"
  unfolding to_mu_repr[unfolded mu_repr_def] state using ii j by auto

lemma fi_state: "i < m \<Longrightarrow> fi_state state = fs ! i"
  using get_nth_i[OF to_list_repr(1)] unfolding state by auto

lemma fim1_state: "i < m \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> fim1_state state = fs ! (i - 1)"
  using get_nth_im1[OF to_list_repr(1)] unfolding state by auto

lemma d_state: "ii \<le> m \<Longrightarrow> d_state state ii = d fs ii"
  using to_d_repr[unfolded d_repr_def] state
  unfolding state by (auto simp: nth_append)

lemma fs_state: "length fs = m \<Longrightarrow> fs_state state = fs"
  using of_list_repr[OF to_list_repr(1)] unfolding state by (auto simp: o_def intro!: nth_equalityI)

lemma LLL_state_inc_state: assumes i: "i < m"
shows "LLL_impl_inv (inc_state state) (Suc i) fs"
  "fs_state (inc_state state) = fs_state state"
proof -
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  note inc = inc_i[OF to_list_repr(1)]
  from inc i impl show "LLL_impl_inv (inc_state state) (Suc i) fs"
    unfolding state by auto
  from of_list_repr[OF inc(1)] of_list_repr[OF to_list_repr(1)] i
  show "fs_state (inc_state state) = fs_state state" unfolding state by auto
qed
end
end

context LLL_with_assms
begin

lemma basis_reduction_add_rows_loop_impl: assumes
    impl: "LLL_impl_inv state i fs"
  and inv: "LLL_invariant True i fs"
  and mu_small: "\<mu>_small_row i fs j"
  and res: "LLL_Impl.basis_reduction_add_rows_loop n state i j
    (map ((!) fs) (rev [0 ..< j])) = state'"
    (is "LLL_Impl.basis_reduction_add_rows_loop n state i j (?mapf fs j) = _")
  and j: "j \<le> i"
  and i: "i < m"
  and fs': "fs' = fs_state state'"
shows
  "LLL_impl_inv state' i fs'"
  "basis_reduction_add_rows_loop i fs j = fs'" 
proof (atomize(full), insert assms(1-6), induct j arbitrary: fs state)
  case (0 fs state)
  from LLL_invD[OF 0(2)] have len: "length fs = m" by auto
  from fs_state[OF 0(1-2) _ len] have "fs_state state = fs" by (cases state, auto)
  thus ?case using 0 i fs' by auto
next
  case (Suc j fs state)
  hence j: "j < i" and jj: "j \<le> i" and id: "(j < i) = True" by auto
  obtain f mu ds where state: "state = (f,mu,ds)" by (cases state, auto)
  note Linv = Suc(3)
  note inv = LLL_invD[OF Linv]
  note impl = Suc(2)
  from fi_state[OF impl Linv state i] have fi: "fi_state state = fs ! i" by auto
  have id: "Suc j - 1 = j" by simp
  note mu = dmu_ij_state[OF impl Linv state j i]
  let ?c = "round (\<mu> fs i j)"
  interpret fs: fs_int' n m fs_init \<alpha> True i fs
    by standard (use Linv in auto)
  have floor: "round_num_denom (d\<mu> fs i j) (d fs (Suc j)) = round (fs.gs.\<mu> i j)"
    using jj i inv unfolding d\<mu>_def d_def
    by (intro fs.round_num_denom_d\<mu>_d[unfolded fs.d\<mu>_def fs.d_def]) auto
  from LLL_d_pos[OF Linv] j i have dj: "d fs (Suc j) > 0" by auto
  note updates = d_d\<mu>_add_row[OF Linv i j refl]
  note d_state = d_state[OF impl Linv state]
  from d_state[of "Suc j"] j i have djs: "d_state state (Suc j) = d fs (Suc j)" by auto
  note res = Suc(5)[unfolded floor map_rev_Suc djs append.simps LLL_Impl.basis_reduction_add_rows_loop.simps
      fi Let_def mu id int_times_rat_def]
  show ?case
  proof (cases "?c = 0")
    case True
    from res[unfolded True]
    have res: "LLL_Impl.basis_reduction_add_rows_loop n state i j (?mapf fs j) = state'"
      by simp
    note step = Linv basis_reduction_add_row_main_0[OF Linv i j True Suc(4)]
    show ?thesis using Suc(1)[OF impl step(1-2) res _ i] j True by auto
  next
    case False
    hence id: "(?c = 0) = False" by auto
    from i j have jm: "j < m" by auto
    have idd: "vec n (\<lambda>ia. fs ! i $ ia - ?c * fs ! j $ ia) =
      fs ! i - ?c \<cdot>\<^sub>v fs ! j"
      by (intro eq_vecI, insert inv(4)[OF i] inv(4)[OF jm], auto)
    define fi' where "fi' = fs ! i - ?c \<cdot>\<^sub>v fs ! j"
    obtain fs'' where fs'': "fs[i := fs ! i - ?c \<cdot>\<^sub>v fs ! j] = fs''" by auto
    note step = basis_reduction_add_row_main[OF Linv i j fs''[symmetric]]
    note updates = updates[where c = ?c, unfolded fs'']
    have map_id_f: "?mapf fs j = ?mapf fs'' j"
      by (rule nth_equalityI, insert j i, auto simp: rev_nth fs''[symmetric])
    have nth_id: "[0..<m] ! i = i" using i by auto
    note res = res[unfolded False map_id_f id if_False idd]
    have fi: "fi' = fs'' ! i" unfolding fs''[symmetric] fi'_def using inv(6) i by auto
    let ?fn = "\<lambda> fs i. (fs ! i, sq_norm (gso fs i))"
    let ?d = "\<lambda> fs i. d fs (Suc i)"
    let ?mu' = "IArray.of_fun
       (\<lambda>jj. if jj < j then dmu_ij_state state i jj - ?c * dmu_ij_state state j jj
             else if jj = j then dmu_ij_state state i jj - ?d fs j * ?c else dmu_ij_state state i jj) i"
    have mu': "?mu' = IArray.of_fun (d\<mu> fs'' i) i" (is "_ = ?mu'i")
    proof (rule iarray_cong', goal_cases)
      case (1 jj)
      from 1 j i have jm: "j < m" by auto
      show ?case unfolding dmu_ij_state[OF impl Linv state 1 i] using dmu_ij_state[OF impl Linv state _ jm]
        by (subst updates(2)[OF i 1], auto)
    qed
    {
      fix ii
      assume ii: "ii < m" "ii \<noteq> i"
      hence "(IArray.of_fun (\<lambda>i. IArray.of_fun (d\<mu> fs i) i) m) !! ii
        = IArray.of_fun (d\<mu> fs ii) ii" by auto
      also have "\<dots> = IArray.of_fun (d\<mu> fs'' ii) ii"
      proof (rule iarray_cong', goal_cases)
        case (1 j)
        with ii have j: "Suc j \<le> m" by auto
        show ?case unfolding updates(2)[OF ii(1) 1] using ii by auto
      qed
      finally have "(IArray.of_fun (\<lambda>i. IArray.of_fun (d\<mu> fs i) i) m) !! ii
         = IArray.of_fun (d\<mu> fs'' ii) ii" by auto
    } note ii = this
    let ?mu'' = "iarray_update mu i (IArray.of_fun (d\<mu> fs'' i) i)"
    have new_array: "?mu'' = IArray.of_fun (\<lambda> i. IArray.of_fun (d\<mu> fs'' i) i) m"
      unfolding iarray_update_of_fun to_mu_repr[OF impl Linv state, unfolded mu_repr_def]
      by (rule iarray_cong', insert ii, auto)
    have d': "(map (?d fs) (rev [0..<j])) = (map (?d fs'') (rev [0..<j]))"
      by (rule nth_equalityI, force, simp, subst updates(1), insert j i, auto
        simp: nth_rev)
    have repr_id:
      "(map ((!) fs) [0..<m])[i := (fs'' ! i)] = map ((!) fs'') [0..<m]" (is "?xs = ?ys")
    proof (rule nth_equalityI, force)
      fix j
      assume "j < length ?xs"
      thus "?xs ! j = ?ys ! j" unfolding fs''[symmetric] i by (cases "j = i", auto)
    qed
    have repr_id_d:
      "map (d fs) [0..<Suc m] = map (d fs'') [0..<Suc m]"
      by (rule nth_equalityI, force, insert step(4,6), auto simp: nth_append)
    have mu: "fs ! i - ?c \<cdot>\<^sub>v fs ! j = fs'' ! i" unfolding fs''[symmetric] using inv(6) i by auto
    note res = res[unfolded mu' mu d']
    show ?thesis unfolding basis_reduction_add_rows_loop.simps Let_def id if_False fs''
    proof (rule Suc(1)[OF _ step(1,2) res _ i])
      note list_repr = to_list_repr[OF impl Linv state]
      from i have ii: "i < length [0..<m]" by auto
      show "LLL_impl_inv (upd_fi_mu_state state i (fs'' ! i) ?mu'i) i fs''"
        unfolding upd_fi_mu_state.simps state LLL_impl_inv.simps new_array
      proof (intro conjI)
        show "list_repr i (update_i f (fs'' ! i)) (map ((!) fs'') [0..<m])"
          using update_i[OF list_repr(1), unfolded length_map, OF ii] unfolding repr_id[symmetric] .
        show "d_repr ds fs''" unfolding to_d_repr[OF impl Linv state, unfolded d_repr_def] d_repr_def
          by (rule iarray_cong', subst step(6), auto)
      qed (auto simp: mu_repr_def)
    qed (insert i j, auto simp: Suc(4))
  qed
qed

lemma basis_reduction_add_rows_loop: assumes
    impl: "LLL_impl_inv state i fs"
  and inv: "LLL_invariant True i fs"
  and mu_small: "\<mu>_small_row i fs j"
  and res: "LLL_Impl.basis_reduction_add_rows_loop n state i j
    (map ((!) fs) (rev [0 ..< j])) = state'"
    (is "LLL_Impl.basis_reduction_add_rows_loop n state i j (?mapf fs j) = _")
  and j: "j \<le> i"
  and i: "i < m"
  and fs': "fs' = fs_state state'"
shows
  "LLL_impl_inv state' i fs'"
  "LLL_invariant False i fs'"
  "LLL_measure i fs' = LLL_measure i fs"
  "basis_reduction_add_rows_loop i fs j = fs'"
  using basis_reduction_add_rows_loop_impl[OF assms]
    basis_reduction_add_rows_loop[OF inv mu_small _ i j] by blast+

lemma basis_reduction_add_rows_impl: assumes
     impl: "LLL_impl_inv state i fs"
  and inv: "LLL_invariant upw i fs"
  and res: "LLL_Impl.basis_reduction_add_rows n upw i state = state'"
  and i: "i < m"
  and fs': "fs' = fs_state state'"
shows
  "LLL_impl_inv state' i fs'"
  "basis_reduction_add_rows upw i fs = fs'" 
proof (atomize(full), goal_cases)
  case 1
  obtain f mu ds where state: "state = (f,mu,ds)" by (cases state, auto)
  note def = LLL_Impl.basis_reduction_add_rows_def basis_reduction_add_rows_def
  show ?case
  proof (cases upw)
    case False
    from LLL_invD[OF inv] have len: "length fs = m" by auto
    from fs_state[OF impl inv state len] have "fs_state state = fs" by auto
    with assms False show ?thesis by (auto simp: def)
  next
    case True
    with inv have "LLL_invariant True i fs" by auto
    note start = this \<mu>_small_row_refl[of i fs]
    have id: "small_fs_state state = map (\<lambda> i. fs ! i) (rev [0..<i])"
      unfolding state using to_list_repr[OF impl inv state] i
      unfolding list_repr_def by (auto intro!: nth_equalityI simp: nth_rev min_def)
    from i have mm: "[0..<m] = [0 ..< i] @ [i] @ [Suc i ..< m]"
      by (intro nth_equalityI, auto simp: nth_append nth_Cons split: nat.splits)
    from res[unfolded def] True
    have "LLL_Impl.basis_reduction_add_rows_loop n state i i (small_fs_state state) = state'" by auto
    from basis_reduction_add_rows_loop_impl[OF impl start(1-2) this[unfolded id] le_refl i fs']
    show ?thesis unfolding def using True by auto
  qed
qed

lemma basis_reduction_add_rows: assumes
     impl: "LLL_impl_inv state i fs"
  and inv: "LLL_invariant upw i fs"
  and res: "LLL_Impl.basis_reduction_add_rows n upw i state = state'"
  and i: "i < m"
  and fs': "fs' = fs_state state'"
shows
  "LLL_impl_inv state' i fs'"
  "LLL_invariant False i fs'"
  "LLL_measure i fs' = LLL_measure i fs"
  "basis_reduction_add_rows upw i fs = fs'" 
  using basis_reduction_add_rows_impl[OF impl inv res i fs']
    basis_reduction_add_rows[OF inv _ i] by blast+

lemma basis_reduction_swap_impl: assumes
  impl: "LLL_impl_inv state i fs"
  and inv: "LLL_invariant False i fs"
  and res: "LLL_Impl.basis_reduction_swap m i state = (upw',i',state')"
  and cond: "sq_norm (gso fs (i - 1)) > \<alpha> * sq_norm (gso fs i)"
  and i: "i < m" and i0: "i \<noteq> 0"
  and fs': "fs' = fs_state state'"
shows
  "LLL_impl_inv state' i' fs'" (is ?g1)
  "basis_reduction_swap i fs = (upw',i',fs')" (is ?g2)
proof -
  from i i0 have ii: "i - 1 < i" and le_m: "i - 1 \<le> m" "i \<le> m" "Suc i \<le> m" by auto
  obtain f mu ds where state: "state = (f,mu,ds)" by (cases state, auto)
  note dmu_ij_state = dmu_ij_state[OF impl inv state]
  note d_state = d_state[OF impl inv state]
  note res = res[unfolded LLL_Impl.basis_reduction_swap_def Let_def split state, folded state,
    unfolded fi_state[OF impl inv state i] fim1_state[OF impl inv state i i0]]
  note state_id = dmu_ij_state[OF ii i]
  note d_state_i = d_state[OF le_m(1)] d_state[OF le_m(2)] d_state[OF le_m(3)]
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  from fs_state[OF impl inv state len] have fs: "fs_state state = fs" by auto
  obtain fs'' where fs'': "fs[i := fs ! (i - 1), i - 1 := fs ! i] = fs''" by auto
  let ?r = rat_of_int
  let ?d = "d fs"
  let ?d' = "d fs''"
  let ?dmus = "dmu_ij_state state"
  let ?ds = "d_state state"
  note swap = basis_reduction_swap_main[OF inv i i0 cond refl, unfolded fs'']
  interpret fs: fs_int' n m fs_init \<alpha> False i fs
    by standard (use inv in auto)
  interpret fs'': fs_int' n m fs_init \<alpha> False "i - 1" fs''
    by standard (use swap in auto)
  note dmu = fs.d\<mu>
  note dmu' = fs''.d\<mu>
  note inv' = LLL_invD[OF inv]
  have fi: "fs ! (i - 1) = fs'' ! i" "fs ! i = fs'' ! (i - 1)"
    unfolding fs''[symmetric] using inv'(6) i i0 by auto
  from res have upw': "upw' = False" "i' = i - 1" by auto
  let ?dmu_repr' = "swap_mu m mu i (?dmus i (i - 1)) (?d (i - 1)) (?d i) (?d (Suc i))"
  let ?d'i = "(?d (Suc i) * ?d (i - 1) + ?dmus i (i - 1) * ?dmus i (i - 1)) div (?d i)"
  from res[unfolded fi d_state_i]
  have res: "upw' = False" "i' = i - 1"
    "state' = (dec_i (update_im1 (update_i f (fs'' ! i)) (fs'' ! (i - 1))),
       ?dmu_repr', iarray_update ds i ?d'i)" by auto
  from i have ii: "i < length [0..<m]" and im1: "i - 1 < m" by auto
  note list_repr = to_list_repr[OF impl inv state]
  from dec_i[OF update_im1[OF update_i[OF list_repr(1)]], unfolded length_map, OF ii i0 i0]
  have
    "list_repr (i - 1) (dec_i (update_im1 (update_i f (fs'' ! i)) (fs'' ! (i - 1)))) ((map ((!) fs) [0..<m])[i := (fs'' ! i),
       i - 1 := (fs'' ! (i - 1))])" (is "list_repr _ ?fr ?xs") .
  also have "?xs = map ((!) fs'') [0..<m]" unfolding fs''[symmetric]
    by (intro nth_equalityI, insert i i0 len, auto simp: nth_append, rename_tac ii, case_tac "ii \<in> {i-1,i}", auto)
  finally have f_repr: "list_repr (i - 1) ?fr (map ((!) fs'') [0..<m])" .
  from i0 have sim1: "Suc (i - 1) = i" by simp
  from LLL_d_Suc[OF inv im1, unfolded sim1]
  have "length fs'' = m"
    using fs'' inv'(6) by auto
  hence fs_id: "fs' = fs''" unfolding fs' res fs_state.simps using of_list_repr[OF f_repr]
    by (intro nth_equalityI, auto simp: o_def)
  from to_mu_repr[OF impl inv state] have mu: "mu_repr mu fs" by auto
  from to_d_repr[OF impl inv state] have d_repr: "d_repr ds fs" by auto
  note mu_def = mu[unfolded mu_repr_def]
  note updates = d_d\<mu>_swap[OF inv i i0 cond fs''[symmetric]]
  note dmu_ii = dmu_ij_state[OF \<open>i - 1 < i\<close> i]
  show ?g1 unfolding fs_id LLL_impl_inv.simps res
  proof (intro conjI f_repr)
    show "d_repr (iarray_update ds i ?d'i) fs''"
      unfolding d_repr[unfolded d_repr_def] d_repr_def iarray_update_of_fun dmu_ii
      by (rule iarray_cong', subst updates(1), auto simp: nth_append intro: arg_cong)
    show "mu_repr ?dmu_repr' fs''" unfolding mu_repr_def swap_mu_def Let_def dmu_ii
    proof (rule iarray_cong', goal_cases)
      case ii: (1 ii)
      show ?case
      proof (cases "ii < i - 1")
        case small: True
        hence id: "(ii = i) = False" "(ii = i - 1) = False" "(i < ii) = False" "(ii < i - 1) = True" by auto
        have mu: "mu !! ii = IArray.of_fun (d\<mu> fs ii) ii"
          using ii unfolding mu_def by auto
        show ?thesis unfolding id if_True if_False mu
          by (rule iarray_cong', insert small ii i i0, subst updates(2), simp_all, linarith)
      next
        case False
        hence iFalse: "(ii < i - 1) = False" by auto
        show ?thesis unfolding iFalse if_False if_distrib[of "\<lambda> f. IArray.of_fun f ii", symmetric]
          dmu_ij_state.simps[of f mu ds, folded state, symmetric]
        proof (rule iarray_cong', goal_cases)
          case j: (1 j)
          note upd = updates(2)[OF ii j] dmu_ii dmu_ij_state[OF j ii] if_distrib[of "\<lambda> x. x j"]
          note simps = dmu_ij_state[OF _ ii] dmu_ij_state[OF _ im1] dmu_ij_state[OF _ i]
          from False consider (I) "ii = i" "j = i - 1" | (Is) "ii = i" "j \<noteq> i - 1" |
            (Im1) "ii = i - 1" | (large) "ii > i" by linarith
          thus ?case
          proof (cases)
            case (I)
            show ?thesis unfolding upd using I by auto
          next
            case (Is)
            show ?thesis unfolding upd using Is j simps by auto
          next
            case (Im1)
            hence id: "(i < ii) = False" "(ii = i) = False" "(ii = i - 1) = True" using i0 by auto
            show ?thesis unfolding upd unfolding id if_False if_True by (rule simps, insert j Im1, auto)
          next
            case (large)
            hence "i - 1 < ii" "i < ii" by auto
            note simps = simps(1)[OF this(1)] simps(1)[OF this(2)]
            from large have id: "(i < ii) = True" "(ii = i - 1) = False" "\<And> x. (ii = i \<and> x) = False" by auto
            show ?thesis unfolding id if_True if_False upd simps by auto
          qed
        qed
      qed
    qed
  qed
  show ?g2 unfolding fs_id fs''[symmetric] basis_reduction_swap_def unfolding res ..
qed

lemma basis_reduction_swap: assumes
  impl: "LLL_impl_inv state i fs"
  and inv: "LLL_invariant False i fs"
  and res: "LLL_Impl.basis_reduction_swap m i state = (upw',i',state')"
  and cond: "sq_norm (gso fs (i - 1)) > \<alpha> * sq_norm (gso fs i)"
  and i: "i < m" and i0: "i \<noteq> 0"
  and fs': "fs' = fs_state state'"
shows
  "LLL_impl_inv state' i' fs'" 
  "LLL_invariant upw' i' fs'" 
  "LLL_measure i' fs' < LLL_measure i fs"
  "basis_reduction_swap i fs = (upw',i',fs')"
  using basis_reduction_swap_impl[OF assms] basis_reduction_swap[OF inv _ cond i i0] by blast+

lemma basis_reduction_step_impl: assumes
  impl: "LLL_impl_inv state i fs"
  and inv: "LLL_invariant upw i fs"
  and res: "LLL_Impl.basis_reduction_step \<alpha> n m upw i state = (upw',i',state')"
  and i: "i < m"
  and fs': "fs' = fs_state state'"
shows
  "LLL_impl_inv state' i' fs'"
  "basis_reduction_step upw i fs = (upw',i',fs')" 
proof (atomize(full), goal_cases)
  case 1
  obtain f mu ds where state: "state = (f,mu,ds)" by (cases state, auto)
  note def = LLL_Impl.basis_reduction_step_def basis_reduction_step_def
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  from fs_state[OF impl inv state len] have fs: "fs_state state = fs" by auto
  show ?case
  proof (cases "i = 0")
    case True
    from LLL_state_inc_state[OF impl inv state i] i
      assms increase_i[OF inv i True] True
      res fs' fs
    show ?thesis by (auto simp: def)
  next
    case False
    hence id: "(i = 0) = False" by auto
    obtain state'' where state'': "LLL_Impl.basis_reduction_add_rows n upw i state = state''" by auto
    define fs'' where fs'': "fs'' = fs_state state''"
    obtain f mu ds where state: "state'' = (f,mu,ds)" by (cases state'', auto)
    from basis_reduction_add_rows[OF impl inv state'' i fs'']
    have inv: "LLL_invariant False i fs''"
      and meas: "LLL_measure i fs = LLL_measure i fs''"
      and impl: "LLL_impl_inv state'' i fs''"
      and impl': "basis_reduction_add_rows upw i fs = fs''" 
      by auto
    obtain num denom where quot: "quotient_of \<alpha> = (num,denom)" by force
    note d_state = d_state[OF impl inv state]
    from i have le: "i - 1 \<le> m" " i \<le> m" "Suc i \<le> m" by auto
    note d_state = d_state[OF le(1)] d_state[OF le(2)] d_state[OF le(3)]
    interpret fs'': fs_int' n m fs_init \<alpha> False i fs''
      by standard (use inv in auto)
    have "i < length fs''"
      using LLL_invD[OF inv] i by auto
    note d_sq_norm_comparison = fs''.d_sq_norm_comparison[OF quot this False]
    note res = res[unfolded def id if_False Let_def state'' quot split d_state this]
    note pos = LLL_d_pos[OF inv le(1)] LLL_d_pos[OF inv le(2)] quotient_of_denom_pos[OF quot]
    from False have sim1: "Suc (i - 1) = i" by simp
    let ?r = "rat_of_int"
    let ?x = "sq_norm (gso fs'' (i - 1))"
    let ?y = "\<alpha> * sq_norm (gso fs'' i)"
    show ?thesis
    proof (cases "?x \<le> ?y")
      case True
      from increase_i[OF inv i _ True] True res meas LLL_state_inc_state[OF impl inv state i] fs' fs''
        d_def d_sq_norm_comparison fs''.d_def impl' False
      show ?thesis by (auto simp: def)
    next
      case F: False
      hence gt: "?x > ?y" and id: "(?x \<le> ?y) = False" by auto
      from res[unfolded id if_False] d_def d_sq_norm_comparison fs''.d_def id
      have "LLL_Impl.basis_reduction_swap m i state'' = (upw', i', state')"
        by auto
      from basis_reduction_swap[OF impl inv this gt i False fs'] show ?thesis using meas F False
        by (auto simp: def Let_def impl')
    qed
  qed
qed

lemma basis_reduction_step: assumes
  impl: "LLL_impl_inv state i fs"
  and inv: "LLL_invariant upw i fs"
  and res: "LLL_Impl.basis_reduction_step \<alpha> n m upw i state = (upw',i',state')"
  and i: "i < m"
  and fs': "fs' = fs_state state'"
shows
  "LLL_impl_inv state' i' fs'"
  "LLL_invariant upw' i' fs'"
  "LLL_measure i' fs' < LLL_measure i fs"
  "basis_reduction_step upw i fs = (upw',i',fs')" 
  using basis_reduction_step_impl[OF assms] basis_reduction_step[OF inv _ i] by blast+ 

lemma basis_reduction_main_impl: assumes
  impl: "LLL_impl_inv state i fs"
  and inv: "LLL_invariant upw i fs"
  and res: "LLL_Impl.basis_reduction_main \<alpha> n m upw i state = state'"
  and fs': "fs' = fs_state state'"
shows "LLL_impl_inv state' m fs'"
  "basis_reduction_main (upw,i,fs) = fs'" 
proof (atomize(full), insert assms(1-3), induct "LLL_measure i fs" arbitrary: i fs upw state rule: less_induct)
  case (less i fs upw)
  have id: "LLL_invariant upw i fs = True" using less by auto
  note res = less(4)[unfolded LLL_Impl.basis_reduction_main.simps[of _ _ _ upw]]
  note inv = less(3)
  note impl = less(2)
  note IH = less(1)
  show ?case
  proof (cases "i < m")
    case i: True
    obtain i'' state'' upw'' where step: "LLL_Impl.basis_reduction_step \<alpha> n m upw i state = (upw'',i'',state'')"
      (is "?step = _") by (cases ?step, auto)
    with res i have res: "LLL_Impl.basis_reduction_main \<alpha> n m upw'' i'' state'' = state'" by auto
    note main = basis_reduction_step[OF impl inv step i refl]
    from IH[OF main(3,1,2) res] main(4) step res
    show ?thesis by (simp add: i inv basis_reduction_main.simps)
  next
    case False
    from LLL_invD[OF inv] have len: "length fs = m" by auto
    obtain f mu ds where state: "state = (f,mu,ds)" by (cases state, auto)
    from fs_state[OF impl inv state len] have fs: "fs_state state = fs" by auto
    from False fs res fs' have fs_id: "fs = fs'" by simp
    from False LLL_invD[OF inv] have i: "i = m" by auto
    with False res inv impl fs have "LLL_invariant upw m fs' \<and> LLL_impl_inv state' m fs'" 
      by (auto simp: fs')
    thus ?thesis unfolding basis_reduction_main.simps[of upw i fs] using False 
      by (auto simp: LLL_invariant_def fs_id)
  qed
qed

lemma basis_reduction_main: assumes
  impl: "LLL_impl_inv state i fs"
  and inv: "LLL_invariant upw i fs"
  and res: "LLL_Impl.basis_reduction_main \<alpha> n m upw i state = state'"
  and fs': "fs' = fs_state state'"
shows 
  "LLL_invariant True m fs'"
  "LLL_impl_inv state' m fs'"
  "basis_reduction_main (upw,i,fs) = fs'" 
  using basis_reduction_main_impl[OF assms] basis_reduction_main[OF inv] by blast+

lemma initial_state: "LLL_impl_inv (initial_state m fs_init) 0 fs_init" (is ?g1)
  "fs_state (initial_state m fs_init) = fs_init" (is ?g2)
proof -
  have f_repr: "list_repr 0 ([], fs_init) (map ((!) fs_init) [0..<m])"
    unfolding list_repr_def by (simp, intro nth_equalityI, auto simp: len)
  from fs_init have Rn: "set (RAT fs_init) \<subseteq> Rn" by auto
  have 1: "1 = d fs_init 0" unfolding d_def by simp
  define j where "j = m"
  have jm: "j \<le> m" unfolding j_def by auto
  have 0: "0 = m - j" unfolding j_def by auto
  interpret fs_init: fs_int_indpt n fs_init
    by (standard) (use lin_dep in auto)
  have mu_repr: "mu_repr (IArray.of_fun (\<lambda>i. IArray.of_fun ((!!) (d\<mu>_impl fs_init !! i)) i) m) fs_init"
    unfolding fs_init.d\<mu>_impl mu_repr_def fs_init.d\<mu>_def d\<mu>_def fs_init.d_def d_def
    apply(rule iarray_cong')
    unfolding len[symmetric] by (auto simp add: nth_append)
  have d_repr: "d_repr (IArray.of_fun (\<lambda>i. if i = 0 then 1 else d\<mu>_impl fs_init !! (i - 1) !! (i - 1)) (Suc m)) fs_init"
    unfolding fs_init.d\<mu>_impl d_repr_def
  proof (intro iarray_cong', goal_cases)
    case (1 i)
    show ?case
    proof (cases "i = 0")
      case False
      hence le: "i - 1 < length fs_init" "i - 1 < i" and id: "(i = 0) = False" "Suc (i - 1) = i"
        using 1 len by auto
      show ?thesis unfolding of_fun_nth[OF le(1)] of_fun_nth[OF le(2)] id if_False
        d\<mu>_def fs_init.d\<mu>_def fs_init.d_def d_def
        by (auto simp add: gs.\<mu>.simps )
    next
      case True
      have "d fs_init 0 = 1" unfolding d_def gs.Gramian_determinant_0 by simp
      thus ?thesis unfolding True by simp
    qed
  qed
  show ?g1 unfolding initial_state_def Let_def LLL_impl_inv.simps id
    by (intro conjI f_repr mu_repr d_repr)
  from fs_state[OF this LLL_inv_initial_state]
  show ?g2 unfolding initial_state_def Let_def by (simp add: of_list_repr_def)
qed

lemma basis_reduction: assumes res: "basis_reduction \<alpha> n fs_init = state"
  and fs: "fs = fs_state state"
shows "LLL_invariant True m fs"
  "LLL_impl_inv state m fs"
  "basis_reduction_main (True, 0, fs_init) = fs"
  using basis_reduction_main[OF initial_state(1) LLL_inv_initial_state res[unfolded basis_reduction_def len Let_def] fs]
  by auto

lemma reduce_basis_impl: "LLL_Impl.reduce_basis \<alpha> fs_init = reduce_basis"
proof -
  obtain fs where res: "LLL_Impl.reduce_basis \<alpha> fs_init = fs" by blast
  have "reduce_basis = fs" 
  proof (cases fs_init)
    case (Cons f)
    from fs_init[unfolded Cons] have "dim_vec f = n" by auto
    from res[unfolded LLL_Impl.reduce_basis_def Cons list.simps this, folded Cons]
    have "fs_state (LLL_Impl.basis_reduction \<alpha> n fs_init) = fs" by auto
    from basis_reduction(3)[OF refl refl, unfolded this] 
    show "reduce_basis = fs" unfolding reduce_basis_def .
  next
    case Nil
    with len have m0: "m = 0" by auto
    show ?thesis using res 
      unfolding reduce_basis_def LLL_Impl.reduce_basis_def basis_reduction_main.simps using Nil m0
      by simp
  qed
  with res show ?thesis by simp
qed

lemma reduce_basis: assumes "LLL_Impl.reduce_basis \<alpha> fs_init = fs"
  shows "lattice_of fs = L" 
  "reduced fs m" 
  "lin_indep fs" 
  "length fs = m" 
  "LLL_invariant True m fs" 
  using reduce_basis_impl assms reduce_basis reduce_basis_inv by metis+

lemma short_vector_impl: "LLL_Impl.short_vector \<alpha> fs_init = short_vector" 
  using reduce_basis_impl unfolding LLL_Impl.short_vector_def short_vector_def by simp

lemma short_vector: assumes res: "LLL_Impl.short_vector \<alpha> fs_init = v"
  and m0: "m \<noteq> 0"
shows 
  "v \<in> carrier_vec n"
  "v \<in> L - {0\<^sub>v n}"
  "h \<in> L - {0\<^sub>v n} \<Longrightarrow> rat_of_int (sq_norm v) \<le> \<alpha> ^ (m - 1) * rat_of_int (sq_norm h)"
  "v \<noteq> 0\<^sub>v j"
  using short_vector[OF assms[unfolded short_vector_impl]] by metis+

end
end
