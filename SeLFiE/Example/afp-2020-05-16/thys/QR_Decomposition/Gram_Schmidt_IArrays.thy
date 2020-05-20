(*  
    Title:      Gram_Schmidt_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Gram Schmidt over IArrays\<close>

theory Gram_Schmidt_IArrays
imports 
  QR_Decomposition   
  Matrix_To_IArray_QR 
begin

subsection\<open>Some previous definitions, lemmas and instantiations about iarrays\<close>

definition iarray_of_iarray_to_list_of_list :: "'a iarray iarray => 'a list list"
  where "iarray_of_iarray_to_list_of_list A = map IArray.list_of (map ((!!) A) [0..<IArray.length A])"

instantiation iarray :: (scaleR) scaleR
begin 
definition "scaleR_iarray k A = IArray.of_fun (\<lambda>i. k *\<^sub>R (A !! i)) (IArray.length A)"
instance proof qed 
end


instantiation iarray :: (times) times
begin 
definition "times_iarray A B = IArray.of_fun (\<lambda>i. A!!i * B !! i) (IArray.length A)"
instance proof qed 
end


lemma plus_iarray_component:
  assumes iA: "i<IArray.length A"
  and iB: "i<IArray.length B"
  shows "(A+B) !! i = A!!i + B!!i"
proof (unfold plus_iarray_def Let_def )
  have "IArray.of_fun
    (\<lambda>a. IArray.of_fun (\<lambda>a. if a < IArray.length A then A !! a else 0) (max (IArray.length A) (IArray.length B)) !! a +
    IArray.of_fun (\<lambda>a. if a < IArray.length B then B !! a else 0) (max (IArray.length A) (IArray.length B)) !! a)
    (max (IArray.length A) (IArray.length B)) !!
    i = IArray.of_fun (\<lambda>a. if a < IArray.length A then A !! a else 0) (max (IArray.length A) (IArray.length B)) !! i +
    IArray.of_fun (\<lambda>a. if a < IArray.length B then B !! a else 0) (max (IArray.length A) (IArray.length B)) !! i"
    by (rule of_fun_nth, metis iB less_max_iff_disj)
  also have "...= (\<lambda>a. if a < IArray.length A then A !! a else 0) i + 
    (\<lambda>a. if a < IArray.length B then B !! a else 0) i"
    using of_fun_nth[of i "(max (IArray.length A) (IArray.length B))"] using iB by simp
  also have "...= A!!i + B !! i" using iA iB by simp
  finally show "IArray.of_fun
    (\<lambda>a. IArray.of_fun (\<lambda>a. if a < IArray.length A then A !! a else 0) (max (IArray.length A) (IArray.length B)) !! a +
    IArray.of_fun (\<lambda>a. if a < IArray.length B then B !! a else 0) (max (IArray.length A) (IArray.length B)) !! a)
    (max (IArray.length A) (IArray.length B)) !!
    i =
    A !! i + B !! i" .
qed

lemma minus_iarray_component:
  assumes iA: "i<IArray.length A"
  and iB: "i<IArray.length B"
  shows "(A-B) !! i = A!!i - B!!i" 
proof (unfold minus_iarray_def Let_def )
  have "IArray.of_fun
    (\<lambda>a. IArray.of_fun (\<lambda>a. if a < IArray.length A then A !! a else 0) (max (IArray.length A) (IArray.length B)) !! a -
    IArray.of_fun (\<lambda>a. if a < IArray.length B then B !! a else 0) (max (IArray.length A) (IArray.length B)) !! a)
    (max (IArray.length A) (IArray.length B)) !!
    i = IArray.of_fun (\<lambda>a. if a < IArray.length A then A !! a else 0) (max (IArray.length A) (IArray.length B)) !! i -
    IArray.of_fun (\<lambda>a. if a < IArray.length B then B !! a else 0) (max (IArray.length A) (IArray.length B)) !! i"
    by (rule of_fun_nth, metis iB less_max_iff_disj)
  also have "...= (\<lambda>a. if a < IArray.length A then A !! a else 0) i - 
    (\<lambda>a. if a < IArray.length B then B !! a else 0) i"
    using of_fun_nth[of i "(max (IArray.length A) (IArray.length B))"] using iB by simp
  also have "...= A!!i - B !! i" using iA iB by simp
  finally show "IArray.of_fun
    (\<lambda>a. IArray.of_fun (\<lambda>a. if a < IArray.length A then A !! a else 0) (max (IArray.length A) (IArray.length B)) !! a -
    IArray.of_fun (\<lambda>a. if a < IArray.length B then B !! a else 0) (max (IArray.length A) (IArray.length B)) !! a)
    (max (IArray.length A) (IArray.length B)) !! i = A !! i - B !! i" .
qed


lemma length_plus_iarray:
  "IArray.length (A+B)=max (IArray.length A) (IArray.length B)"
  unfolding plus_iarray_def Let_def by auto

lemma length_sum_iarray:
  assumes "finite S" and "S\<noteq>{}"
  shows "IArray.length (sum f S) = Max {IArray.length (f x)| x. x \<in> S}"
  using assms
proof (induct S,simp)
  case (insert x F)
    show?case
proof (cases "F={}")
  case True show ?thesis unfolding True by auto
next
  case False
  have rw: "IArray.length (sum f F) = Max {IArray.length (f x) |x. x \<in> F}"
    by (rule insert.hyps, simp add: False)
  have set_rw: "(insert (IArray.length (f x)) {IArray.length (f x) |x. x \<in> F}) = {IArray.length (f a) |a. a \<in> insert x F}"
    by auto
  have "IArray.length (sum f (insert x F)) = IArray.length (f x + sum f F)"
    by (metis insert.hyps(1) insert.hyps(2) sum_clauses(2))
  also have "... = max (IArray.length (f x)) (IArray.length (sum f F))" 
    unfolding length_plus_iarray ..
  also have "... = max (IArray.length (f x)) (Max {IArray.length (f a) |a. a \<in> F})" unfolding rw by simp
  also have "... =  Max (insert (IArray.length (f x)) {IArray.length (f a) |a. a \<in> F})" 
  proof(rule Max_insert[symmetric])
    show "finite {IArray.length (f x) |x. x \<in> F}" using insert.hyps(1) by auto
    show "{IArray.length (f x) |x. x \<in> F} \<noteq> {}" by (metis (lifting, mono_tags) False empty_Collect_eq ex_in_conv)
  qed
  also have "...=  Max {IArray.length (f a) |a. a \<in> insert x F}" unfolding set_rw ..
  finally show ?thesis .
  qed
qed


lemma sum_component_iarray:
  assumes a: "\<forall>x\<in>S. i<IArray.length (f x)"
  and f: "finite S"
  and S: "S\<noteq>{}" \<comment> \<open>If S is empty, then the sum will return the empty 
  iarray and it makes no sense to access the component i\<close>
  shows "sum f S !! i = (\<Sum>x\<in>S. f x !! i)"
  using f a S
proof (induct S, simp)
  case (insert x F)
  have finite_F: "finite F" by (metis insert.hyps(1))
  show ?case
  proof (cases "F={}")
    case True
    have "sum f (insert x F) !! i = f x !! i" unfolding True by auto
    also have "... = (\<Sum>x\<in>insert x F. f x !! i)" unfolding True by auto
    finally show ?thesis .
  next
    case False
    have hyp: "(sum f F !! i)=(\<Sum>x\<in>F. f x !! i)" 
    proof  (rule insert.hyps)
      show "\<forall>x\<in>F. i < IArray.length (f x)" by (metis insert.prems(1) insertCI)
      show "F \<noteq> {}" using False .
    qed
    have "sum f (insert x F) !! i = (f x + sum f F) !! i" 
      by (metis insert.hyps(1) insert.hyps(2) sum_clauses(2))
    also have "... = (f x) !! i + (sum f F !! i)" 
    proof (rule plus_iarray_component)
      obtain a where a: "a\<in>F" using False by auto
      have finite_C: "finite {IArray.length (f x) |x. x \<in> F}" using finite_F by auto
      have not_empty_C: "{IArray.length (f x) |x. x \<in> F} \<noteq>{}" using False by simp    
      show "i < IArray.length (f x)" by (metis insert.prems(1) insertI1)
      show "i < IArray.length (sum f F)" 
        unfolding length_sum_iarray[OF finite_F False]
        unfolding Max_gr_iff[OF finite_C not_empty_C]
      proof (rule bexI[of _ "IArray.length (f a)"])
        show "i < IArray.length (f a)" using insert.prems(1) a by auto
        show "IArray.length (f a) \<in> {IArray.length (f x) |x. x \<in> F}" using a by auto
      qed
    qed
    also have "...= (f x) !! i + (\<Sum>x\<in>F. f x !! i)" unfolding hyp ..
    also have "...= (\<Sum>x\<in>insert x F. f x !! i)"
      by (metis (mono_tags) insert.hyps(1) insert.hyps(2) sum_clauses(2))
    finally show "sum f (insert x F) !! i = (\<Sum>x\<in>insert x F. f x !! i)" .
  qed
qed

lemma length_zero_iarray: "IArray.length 0 = 0"
  unfolding zero_iarray_def by simp

lemma minus_zero_iarray:
  fixes A::"'a::{group_add} iarray"
  shows "A - 0 = A" 
proof (unfold iarray_exhaust2 list_eq_iff_nth_eq, auto, unfold IArray.length_def[symmetric] IArray.sub_def[symmetric])
  have max_eq: "(max (IArray.length A) (IArray.length 0))= IArray.length A"
    unfolding zero_iarray_def by auto
  show length_eq: "IArray.length (A - 0) = IArray.length A"
    unfolding minus_iarray_def Let_def unfolding max_eq by auto
  fix i assume i: "i < IArray.length (A - 0)"
  hence i2: "i< (IArray.length A)" unfolding length_eq .
  have "A - 0 = IArray.of_fun
    (\<lambda>a. IArray.of_fun (\<lambda>a. if a < IArray.length A then A !! a else 0) (IArray.length A) !! a -
    IArray.of_fun (\<lambda>a. if a < IArray.length (0::'a iarray) then 0 !! a else 0) (IArray.length A) !! a) 
    (IArray.length A)"
    unfolding minus_iarray_def Let_def unfolding max_eq ..
  also have "... !! i = A !! i" unfolding of_fun_nth[OF i2] length_zero_iarray using i2 by auto  
  finally show "(A - 0) !! i = A !! i" . 
qed


subsection\<open>Inner mult over real iarrays\<close>

definition inner_iarray :: "real iarray => real iarray => real"  (infixl "\<bullet>i" 70)
  where "inner_iarray A B = sum (\<lambda>n. A !! n * B !! n) {0..<IArray.length A}"

lemma vec_to_iarray_inner:
  "a \<bullet> b = vec_to_iarray a \<bullet>i vec_to_iarray b" 
proof (unfold inner_iarray_def inner_vec_def, auto, unfold IArray.sub_def[symmetric] IArray.length_def[symmetric])
  have set_rw: "{0..<IArray.length (vec_to_iarray a)}  = (to_nat)`(UNIV::'a set)"
    unfolding vec_to_iarray_def 
    using to_nat_less_card using bij_to_nat[where ?'a='a]
    unfolding bij_betw_def by auto
  have inj: "inj_on (to_nat::'a=>nat) (UNIV::'a set)"
    by (metis strict_mono_imp_inj_on strict_mono_to_nat)
  have "(\<Sum>n = 0..<IArray.length (vec_to_iarray a). vec_to_iarray a !! n * vec_to_iarray b !! n) 
    = (\<Sum>n\<in>range (to_nat::'a=>nat). vec_to_iarray a !! n * vec_to_iarray b !! n)"
    unfolding set_rw ..
  also have "... = (\<Sum>x\<in>(UNIV::'a set). vec_to_iarray a !! to_nat x * vec_to_iarray b !! to_nat x)"
    unfolding sum.reindex[OF inj] o_def ..
  also have "...= (\<Sum>x\<in>UNIV. a $ x * b $ x)" unfolding vec_to_iarray_nth' ..
  finally show "(\<Sum>i\<in>UNIV. a $ i * b $ i) 
    = (\<Sum>n = 0..<IArray.length (vec_to_iarray a). vec_to_iarray a !! n * vec_to_iarray b !! n)" ..
qed


lemma vec_to_iarray_scaleR: 
  "vec_to_iarray (a *\<^sub>R x) = a *\<^sub>R (vec_to_iarray x)"
  unfolding scaleR_vec_def scaleR_iarray_def vec_to_iarray_def by auto

subsection\<open>Gram Schmidt over IArrays\<close>

definition "Gram_Schmidt_column_k_iarrays A k
  = tabulate2 (nrows_iarray A) (ncols_iarray A) (\<lambda>a b. (if b = k
  then (column_iarray b A - sum (\<lambda>x. (((column_iarray b A) \<bullet>i x) / (x \<bullet>i x)) *\<^sub>R x) 
  (set (List.map (\<lambda>n. column_iarray n A) [0..<b])))
  else (column_iarray b A)) !! a)"

definition "Gram_Schmidt_upt_k_iarrays A k = List.foldl Gram_Schmidt_column_k_iarrays A [0..<(Suc k)]"
definition "Gram_Schmidt_matrix_iarrays A = Gram_Schmidt_upt_k_iarrays A (ncols_iarray A - 1)"

lemma matrix_to_iarray_Gram_Schmidt_column_k:
  fixes A::"real^'cols::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A"
  shows "matrix_to_iarray (Gram_Schmidt_column_k A k) = Gram_Schmidt_column_k_iarrays (matrix_to_iarray A) k"
proof (unfold iarray_exhaust2 list_eq_iff_nth_eq, rule conjI, auto, unfold IArray.sub_def[symmetric] IArray.length_def[symmetric])
  show "IArray.length (matrix_to_iarray (Gram_Schmidt_column_k A k)) = IArray.length (Gram_Schmidt_column_k_iarrays (matrix_to_iarray A) k)"
    unfolding matrix_to_iarray_def Gram_Schmidt_column_k_iarrays_def tabulate2_def unfolding nrows_iarray_def by auto
  fix i assume i: "i < IArray.length (matrix_to_iarray (Gram_Schmidt_column_k A k))"
  show "IArray.length (matrix_to_iarray (Gram_Schmidt_column_k A k) !! i) 
    = IArray.length (Gram_Schmidt_column_k_iarrays (matrix_to_iarray A) k !! i)"
    unfolding matrix_to_iarray_def Gram_Schmidt_column_k_iarrays_def tabulate2_def 
    unfolding nrows_iarray_def ncols_iarray_def o_def
  proof (auto)
    have f1: "i < card (UNIV::'rows set)"
      by (metis i length_eq_card_rows)
    have f2: "\<And>x\<^sub>5. IArray.list_of (vec_to_iarray x\<^sub>5) 
      = List.map (\<lambda>uua. x\<^sub>5 $ (from_nat uua::'cols)::real) [0..<card (UNIV::'cols set)]"
      by (metis list_of.simps IArray.of_fun_def vec_to_iarray_def)
    thus "length (IArray.list_of (List.map (\<lambda>x. vec_to_iarray (Gram_Schmidt_column_k A k $ from_nat x)) [0..<card (UNIV::'rows set)] ! i)) 
    = length (IArray.list_of (List.map (\<lambda>i. IArray (List.map (\<lambda>b. IArray.list_of (if b = k then column_iarray b (IArray (List.map (\<lambda>x. vec_to_iarray (A $ from_nat x)) [0..<card (UNIV::'rows set)])) 
    - (\<Sum>x\<in>set (List.map (\<lambda>n. column_iarray n (IArray (List.map (\<lambda>x. vec_to_iarray (A $ from_nat x)) [0..<card (UNIV::'rows set)]))) [0..< b]). (column_iarray b (IArray (List.map (\<lambda>x. vec_to_iarray (A $ from_nat x)) [0..<card (UNIV::'rows set)])) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x) else column_iarray b (IArray (List.map (\<lambda>x. vec_to_iarray (A $ from_nat x)) [0..<card (UNIV::'rows set)]))) ! i) [0..< length (IArray.list_of (vec_to_iarray (A $ from_nat 0)))])) [0..<card (UNIV::'rows set)] ! i))"
      using f1 by auto
  qed
next
  fix i ia
  assume i: "i < IArray.length (matrix_to_iarray (Gram_Schmidt_column_k A k))"
    and ia: "ia < IArray.length (matrix_to_iarray (Gram_Schmidt_column_k A k) !! i)"
  have i_nrows: "i<nrows A" using i unfolding matrix_to_iarray_def nrows_def by auto
  have ia_ncols: "ia<ncols A" using ia unfolding matrix_to_iarray_def o_def vec_to_iarray_def ncols_def
    by (auto, metis (no_types) Ex_list_of_length i_nrows length_map list_of.simps map_nth nrows_def nth_map)
  have i_nrows_iarray: "i<nrows_iarray (matrix_to_iarray A)" using i_nrows by (metis matrix_to_iarray_nrows)
  have ia_ncols_iarray: "ia<ncols_iarray (matrix_to_iarray A)" using ia_ncols by (metis matrix_to_iarray_ncols)
  show "matrix_to_iarray (Gram_Schmidt_column_k A k) !! i !! ia = Gram_Schmidt_column_k_iarrays (matrix_to_iarray A) k !! i !! ia"
    unfolding Gram_Schmidt_column_k_def Gram_Schmidt_column_k_iarrays_def 
    unfolding matrix_to_iarray_nth[of _ "from_nat i::'rows" "from_nat ia::'cols",
      unfolded to_nat_from_nat_id[OF i_nrows[unfolded nrows_def]]
      to_nat_from_nat_id[OF ia_ncols[unfolded ncols_def]]]
    unfolding tabulate2_def
    unfolding of_fun_nth[OF i_nrows_iarray]
    unfolding of_fun_nth[OF ia_ncols_iarray]
  proof (unfold proj_onto_def proj_def[abs_def], auto, unfold IArray.sub_def[symmetric])
    have inj: "inj_on vec_to_iarray {column i A |i. i < from_nat k}" unfolding inj_on_def
      by (auto, metis vec_to_iarray_morph)
    have set_rw: "{column i A |i. i < from_nat k} = (\<lambda>n. column n A)` {0..<from_nat k}"
    proof (unfold image_def, auto)
      fix a::'cols assume a: "a < from_nat k" 
      show "\<exists>x\<in>{0..<from_nat k}. column a A = column x A"
        by (rule bexI[of _ a], auto simp add: a least_mod_type)
    qed
    have set_rw2: "vec_to_iarray` {column i A |i. i < from_nat k} 
      = (\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}"
    proof (unfold image_def, auto)
      fix a::'cols assume a: "a < from_nat k"
      show "\<exists>x\<in>{0..<k}. vec_to_iarray (column a A) = column_iarray x (matrix_to_iarray A)"
        by (rule bexI[of _ "to_nat a"], auto simp add:  a to_nat_le vec_to_iarray_column)
    next
      fix xa assume xa: "xa < k"
      have xa': "(from_nat xa::'cols) < from_nat k" by (rule from_nat_mono[OF xa k[unfolded ncols_def]])
      show "\<exists>x. (\<exists>i. x = column i A \<and> i < from_nat k) \<and> column_iarray xa (matrix_to_iarray A) =  vec_to_iarray x"
        apply (rule exI[of _ "column (from_nat xa) A"])
        apply auto apply (rule exI[of _ "from_nat xa"]) 
        apply (auto simp add: xa' vec_to_iarray_column)
        by (metis k order.strict_trans vec_to_iarray_column vec_to_iarray_column' xa)
    qed
    show "column (from_nat k) A $ from_nat i -
      (\<Sum>x\<in>{column i A |i. i < from_nat k}. column (from_nat k) A \<bullet> x * x $ from_nat i / (x \<bullet> x)) =
      (column_iarray k (matrix_to_iarray A) -
      (\<Sum>x\<in>(\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}. (column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x)) !! i"
    proof (cases "k=0")
      case True
      have set_rw_empty: "{column i A |i. i < from_nat k}={}" 
        unfolding True from_nat_0 using least_mod_type not_le by auto
      have "column (from_nat k) A $ from_nat i -
        (\<Sum>x\<in>{column i A |i. i < from_nat k}. column (from_nat k) A \<bullet> x
        * x $ from_nat i / (x \<bullet> x)) =
        column (from_nat k) A $ from_nat i - 0" unfolding set_rw_empty by simp
      also have "...= column (from_nat k) A $ from_nat i" by simp
      also have "...= (column_iarray k (matrix_to_iarray A) - 0) !! i"
        unfolding minus_zero_iarray 
        unfolding vec_to_iarray_column'[OF k, symmetric]
        unfolding vec_to_iarray_nth[OF i_nrows[unfolded nrows_def]] ..
      also have "...= (column_iarray k (matrix_to_iarray A) - 
        (\<Sum>x\<in>(\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}. (column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x))
        !! i" unfolding True by auto
      finally show ?thesis .
    next
      case False    
      have "(\<Sum>x\<in>(\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}. (column_iarray k (matrix_to_iarray A) \<bullet>i x/ (x \<bullet>i x)) *\<^sub>R x) !! i = 
        (\<Sum>x\<in>(\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}. 
        (( column_iarray k (matrix_to_iarray A) \<bullet>i x/ (x \<bullet>i x)) *\<^sub>R x) !! i)" 
      proof (rule sum_component_iarray)
        show "\<forall>x\<in>(\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}. i < IArray.length ((column_iarray k (matrix_to_iarray A) \<bullet>i x/ (x \<bullet>i x)) *\<^sub>R x)"
        proof (unfold column_iarray_def, auto)
          fix x :: nat
          have "i < length (IArray.list_of (IArray (map (vec_to_iarray \<circ> ($) A \<circ> mod_type_class.from_nat) [0..<card (UNIV::'rows set)])))"
            by (metis i_nrows_iarray IArray.length_def matrix_to_iarray_def nrows_iarray_def)
          thus "i < length (IArray.list_of ((IArray (map (\<lambda>n. IArray.list_of (IArray.list_of (matrix_to_iarray A) ! n) ! k) [0..<length (IArray.list_of (matrix_to_iarray A))]) \<bullet>i IArray (map (\<lambda>n. IArray.list_of (IArray.list_of (matrix_to_iarray A) ! n) ! x) [0..<length (IArray.list_of (matrix_to_iarray A))]) / (IArray (map (\<lambda>n. IArray.list_of (IArray.list_of (matrix_to_iarray A) ! n) ! x) [0..<length (IArray.list_of (matrix_to_iarray A))]) \<bullet>i IArray (map (\<lambda>n. IArray.list_of (IArray.list_of (matrix_to_iarray A) ! n) ! x) [0..<length (IArray.list_of (matrix_to_iarray A))]))) *\<^sub>R IArray (map (\<lambda>n. IArray.list_of (IArray.list_of (matrix_to_iarray A) ! n) ! x) [0..<length (IArray.list_of (matrix_to_iarray A))])))"
            by (simp add: matrix_to_iarray_def scaleR_iarray_def)
        qed
        show "finite ((\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k})" by auto
        show "(\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k} \<noteq> {}" using False by auto
      qed
      also have "... = (\<Sum>x\<in>(\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}. 
        (column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x !! i)"
      proof (rule sum.cong)
        fix x assume "x \<in> (\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}"
        from this obtain n where x: "x = column_iarray n (matrix_to_iarray A)" and n: "n<k" by auto
        have n_ncols: "n<ncols A" by (metis k n order.strict_trans)
        have c_eq: "column_iarray k (matrix_to_iarray A) = vec_to_iarray (column (from_nat k::'cols) A)"
          by (metis k vec_to_iarray_column')
        show "((column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x) !! i 
          = (column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x !! i"
          unfolding x 
          unfolding vec_to_iarray_column[symmetric, of "from_nat n::'cols", 
            unfolded to_nat_from_nat_id[OF n_ncols[unfolded ncols_def]]]
          unfolding c_eq
          unfolding vec_to_iarray_inner[symmetric] 
          unfolding vec_to_iarray_nth[OF i_nrows[unfolded nrows_def]]
          unfolding vector_scaleR_component[symmetric]
          unfolding vec_to_iarray_nth'[symmetric]
          unfolding to_nat_from_nat_id[OF i_nrows[unfolded nrows_def]]
          unfolding vec_to_iarray_scaleR ..
      qed (simp)
      also have "... =  (\<Sum>x\<in>vec_to_iarray ` {column i A |i. i < from_nat k}. (column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x !! i)" 
        unfolding set_rw2[symmetric] ..
      also have "...= 
        (\<Sum>x\<in>{column i A |i. i < from_nat k}. (column (from_nat k) A \<bullet> x / (x \<bullet> x)) *\<^sub>R vec_to_iarray x !! i)" 
        unfolding sum.reindex[OF inj] o_def 
        unfolding vec_to_iarray_column[of "from_nat k::'cols",symmetric,unfolded to_nat_from_nat_id[OF k[unfolded ncols_def]]]
        unfolding vec_to_iarray_inner[symmetric] .. 
      also have "... 
        = (\<Sum>x\<in>{column i A |i. i < from_nat k}. column (from_nat k) A \<bullet> x * x $ from_nat i / (x \<bullet> x))"
        unfolding vec_to_iarray_nth[OF i_nrows[unfolded nrows_def]] by auto
      finally have *: "(\<Sum>x\<in>(\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}. (column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x) !! i 
        = (\<Sum>x\<in>{column i A |i. i < from_nat k}. column (from_nat k) A \<bullet> x * x $ from_nat i / (x \<bullet> x))" .    
      have "(column_iarray k (matrix_to_iarray A) -
        (\<Sum>x\<in>(\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}. (column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x)) !! i =
        (column_iarray k (matrix_to_iarray A) !! i -
        (\<Sum>x\<in>(\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}. (column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x) !! i)"
      proof (rule minus_iarray_component)
        have finite: "finite ((\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k})"
          using False by auto
        have not_empty: "(\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k} \<noteq> {}"
          by (metis False atLeastLessThan_empty_iff2 empty_is_image neq0_conv)
        let ?C="{IArray.length ((column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x) |x. x \<in> (\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}}"
        have finite_C: "finite ?C" by auto
        have not_empty_C: "?C \<noteq> {}" using False by auto
        let ?x="(column_iarray 0 (matrix_to_iarray A))"
        let ?c="IArray.length ((column_iarray k (matrix_to_iarray A) \<bullet>i ?x / (?x \<bullet>i ?x)) *\<^sub>R ?x)"
        show "i < IArray.length (column_iarray k (matrix_to_iarray A))"
          unfolding column_iarray_def
          by (auto, metis i_nrows_iarray IArray.length_def nrows_iarray_def)
        show "i < IArray.length (\<Sum>x\<in>(\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}. (column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x)"
          unfolding length_sum_iarray[OF finite not_empty]
          unfolding Max_gr_iff[OF finite_C not_empty_C]
        proof (rule bexI[of _ "?c"])
          show "i < ?c"           
          proof (unfold column_iarray_def, auto)
            have "i < card (UNIV::'rows set)"
              by (metis (no_types) i_nrows nrows_def)
            thus "i < length (IArray.list_of ((IArray (map (\<lambda>n. IArray.list_of (IArray.list_of (matrix_to_iarray A) ! n) ! k) [0..<length (IArray.list_of (matrix_to_iarray A))]) \<bullet>i IArray (map (\<lambda>n. IArray.list_of (IArray.list_of (matrix_to_iarray A) ! n) ! 0) [0..<length (IArray.list_of (matrix_to_iarray A))]) / (IArray (map (\<lambda>n. IArray.list_of (IArray.list_of (matrix_to_iarray A) ! n) ! 0) [0..<length (IArray.list_of (matrix_to_iarray A))]) \<bullet>i IArray (map (\<lambda>n. IArray.list_of (IArray.list_of (matrix_to_iarray A) ! n) ! 0) [0..<length (IArray.list_of (matrix_to_iarray A))]))) *\<^sub>R IArray (map (\<lambda>n. IArray.list_of (IArray.list_of (matrix_to_iarray A) ! n) ! 0) [0..<length (IArray.list_of (matrix_to_iarray A))])))"
              by (simp add: matrix_to_iarray_def scaleR_iarray_def)
          qed
          show "?c \<in> {IArray.length ((column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x) 
            |x. x \<in> (\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}}"
            using False by auto 
        qed
      qed
      also have "... = column_iarray k (matrix_to_iarray A) !! i -
        (\<Sum>x\<in>{column i A |i. i < from_nat k}. column (from_nat k) A \<bullet> x * x $ from_nat i / (x \<bullet> x))"    
        unfolding * ..
      also have "... = column (from_nat k) A $ from_nat i -
        (\<Sum>x\<in>{column i A |i. i < from_nat k}. column (from_nat k) A \<bullet> x * x $ from_nat i / (x \<bullet> x))"
        unfolding vec_to_iarray_column[of "from_nat k::'cols",symmetric,unfolded to_nat_from_nat_id[OF k[unfolded ncols_def]]]
        unfolding vec_to_iarray_nth[OF i_nrows[unfolded nrows_def]] ..
      finally show "column (from_nat k) A $ from_nat i -
        (\<Sum>x\<in>{column i A |i. i < from_nat k}. column (from_nat k) A \<bullet> x * x $ from_nat i / (x \<bullet> x)) =
        (column_iarray k (matrix_to_iarray A) -
        (\<Sum>x\<in>(\<lambda>n. column_iarray n (matrix_to_iarray A)) ` {0..<k}. (column_iarray k (matrix_to_iarray A) \<bullet>i  x/ (x \<bullet>i x)) *\<^sub>R x)) !! i"
        ..
    qed
    show "column (from_nat ia) A $ from_nat i = column_iarray ia (matrix_to_iarray A) !! i"
      unfolding vec_to_iarray_nth[symmetric, OF i_nrows[unfolded nrows_def]]
      unfolding vec_to_iarray_column'[symmetric, OF ia_ncols] ..
    assume ia_not_k: "ia \<noteq> k"
      and eq: "from_nat ia = (from_nat k::'cols)"
    have "ia=k" by (rule from_nat_eq_imp_eq[OF eq ia_ncols[unfolded ncols_def] k[unfolded ncols_def]])
    thus "column (from_nat k) A $ from_nat i 
      - (\<Sum>x\<in>{column i A |i. i < from_nat k}. 
      column (from_nat k) A \<bullet> x * x $ from_nat i / (x \<bullet> x)) 
      = column_iarray ia (matrix_to_iarray A) !! i"
      using ia_not_k by contradiction
  qed
qed


lemma matrix_to_iarray_Gram_Schmidt_upt_k:
  fixes A::"real^'cols::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A"
  shows "matrix_to_iarray (Gram_Schmidt_upt_k A k) = Gram_Schmidt_upt_k_iarrays (matrix_to_iarray A) k"
  using k
proof (induct k)
  case 0
  show ?case unfolding Gram_Schmidt_upt_k_def Gram_Schmidt_upt_k_iarrays_def
    by (simp add: matrix_to_iarray_Gram_Schmidt_column_k[OF "0.prems"])
next
  case (Suc k)
  have k: "k<ncols (Gram_Schmidt_upt_k A k)" using Suc.prems unfolding ncols_def by simp
  have k2: "Suc k < ncols (Gram_Schmidt_upt_k A k)" using Suc.prems unfolding ncols_def .
  have list_rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [(Suc k)]" by simp
  have hyp: "matrix_to_iarray (Gram_Schmidt_upt_k A k) = Gram_Schmidt_upt_k_iarrays (matrix_to_iarray A) k"
    by (metis Suc.hyps Suc.prems Suc_lessD)
  show "matrix_to_iarray (Gram_Schmidt_upt_k A (Suc k)) = Gram_Schmidt_upt_k_iarrays (matrix_to_iarray A) (Suc k)"
    unfolding Gram_Schmidt_upt_k_def Gram_Schmidt_upt_k_iarrays_def 
    unfolding list_rw
    unfolding foldl_append
    unfolding foldl.simps
    unfolding Gram_Schmidt_upt_k_def[symmetric] Gram_Schmidt_upt_k_iarrays_def[symmetric]
    unfolding hyp[symmetric]
    by (rule matrix_to_iarray_Gram_Schmidt_column_k[OF k2])
qed


lemma matrix_to_iarray_Gram_Schmidt_matrix[code_unfold]:
  fixes A::"real^'cols::{mod_type}^'rows::{mod_type}"
  shows "matrix_to_iarray (Gram_Schmidt_matrix A) = Gram_Schmidt_matrix_iarrays (matrix_to_iarray A)"
  unfolding Gram_Schmidt_matrix_def Gram_Schmidt_matrix_iarrays_def 
  unfolding matrix_to_iarray_ncols[symmetric]
  by (rule matrix_to_iarray_Gram_Schmidt_upt_k, simp add: ncols_def)


text\<open>Examples:\<close>

value"let A = list_of_list_to_matrix [[4,5],[8,1],[-1,5]]::real^2^3
  in iarray_of_iarray_to_list_of_list (matrix_to_iarray (Gram_Schmidt_matrix A))"

value "let A = IArray[IArray[4,5],IArray[8,1],IArray[-1,5]]
  in iarray_of_iarray_to_list_of_list (Gram_Schmidt_matrix_iarrays A)"

end

