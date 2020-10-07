(*  
    Title:      System_Of_Equations_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Solving systems of equations using the Gauss Jordan algorithm over nested IArrays\<close>

theory System_Of_Equations_IArrays
imports 
  System_Of_Equations
  Bases_Of_Fundamental_Subspaces_IArrays
begin

subsection\<open>Previous definitions and properties\<close>

definition greatest_not_zero :: "'a::{zero} iarray => nat"
  where "greatest_not_zero A = the (List.find (\<lambda>n. A !! n \<noteq> 0) (rev [0..<IArray.length A]))"

lemma vec_to_iarray_exists:
shows "(\<exists>b. A $ b \<noteq> 0) = IArray.exists (\<lambda>b. (vec_to_iarray A) !! b \<noteq> 0) (IArray[0..<IArray.length (vec_to_iarray A)])"
proof (unfold IArray.exists_def length_vec_to_iarray, auto simp del: IArray.sub_def)
  fix b assume Ab: "A $ b \<noteq> 0"
  show "\<exists>b\<in>{0..<CARD('a)}. vec_to_iarray A !! b \<noteq> 0"
    by (rule bexI[of _ "to_nat b"], unfold vec_to_iarray_nth', auto simp add: Ab to_nat_less_card[of b])
next
   fix b assume b: "b < CARD('a)" and Ab_vec: "vec_to_iarray A !! b \<noteq> 0"
   show "\<exists>b. A $ b \<noteq> 0" by (rule exI[of _ "from_nat b"], metis Ab_vec vec_to_iarray_nth[OF b])
qed

corollary vec_to_iarray_exists':
shows "(\<exists>b. A $ b \<noteq> 0) = IArray.exists (\<lambda>b. (vec_to_iarray A) !! b \<noteq> 0) (IArray (rev [0..<IArray.length (vec_to_iarray A)]))"
by (simp add: vec_to_iarray_exists Option.is_none_def find_None_iff)

lemma not_is_zero_iarray_eq_iff: "(\<exists>b. A $ b \<noteq> 0) = (\<not> is_zero_iarray (vec_to_iarray A))"
by (metis (full_types) is_zero_iarray_eq_iff vec_eq_iff zero_index)

lemma vec_to_iarray_greatest_not_zero:
assumes ex_b: "(\<exists>b. A $ b \<noteq> 0)"
shows "greatest_not_zero (vec_to_iarray A) = to_nat (GREATEST b. A $ b \<noteq> 0)"
proof -
let ?P="(\<lambda>n. (vec_to_iarray A) !! n \<noteq> 0)"
let ?xs="(rev [0..<IArray.length (vec_to_iarray A)])"
have "\<exists>a. (List.find ?P ?xs) = Some a"
  proof(rule ccontr, simp, unfold find_None_iff)
    assume "\<not> (\<exists>x. x \<in> set (rev [0..<length (IArray.list_of (vec_to_iarray A))]) \<and> IArray.list_of (vec_to_iarray A) ! x \<noteq> 0)"
    thus False using ex_b 
    unfolding set_rev by (auto, unfold IArray.length_def[symmetric] IArray.sub_def[symmetric] length_vec_to_iarray,metis to_nat_less_card vec_to_iarray_nth')
  qed
from this obtain a where a: "(List.find ?P ?xs) = Some a" by blast
from this obtain ia where ia_less_length: "ia<length ?xs"
and P_xs_ia: "?P (?xs!ia)" and a_eq: "a = ?xs!ia" and all_zero: "(\<forall>j<ia. \<not> ?P (?xs!j))"
unfolding find_Some_iff by auto
have ia_less_card: "ia < CARD('a)" using ia_less_length by (metis diff_zero length_rev length_upt length_vec_to_iarray)
have ia_less_length': "ia < length ([0..<IArray.length (vec_to_iarray A)])" using ia_less_length unfolding length_rev .
have a_less_card: "a < CARD('a)" unfolding a_eq unfolding rev_nth[OF ia_less_length']
  using nth_upt[of 0 "(length [0..<IArray.length (vec_to_iarray A)] - Suc ia)" "(length [0..<IArray.length (vec_to_iarray A)])" ]
  by (metis diff_less length_upt length_vec_to_iarray minus_nat.diff_0 plus_nat.add_0 zero_less_Suc zero_less_card_finite)
have "(GREATEST b. A $ b \<noteq> 0) = from_nat a"
  proof (rule Greatest_equality)
    have "A $ from_nat a = (vec_to_iarray A) !! a" by (rule vec_to_iarray_nth[symmetric,OF a_less_card])
    also have "... \<noteq> 0"  using P_xs_ia unfolding a_eq[symmetric] .
    finally show "A $ from_nat a \<noteq> 0" .
    next
    fix y assume Ay: "A $ y \<noteq> 0"
    show "y \<le> from_nat a"
    proof (rule ccontr)
      assume "\<not> y \<le> from_nat a" hence y_greater_a: "y > from_nat a" by simp
      have y_greater_a': "to_nat y > a" using y_greater_a using to_nat_mono[of "from_nat a" y] using to_nat_from_nat_id by (metis a_less_card)
      have "a = ?xs ! ia" using a_eq .
      also have "... = [0..<IArray.length (vec_to_iarray A)] ! (length [0..<IArray.length (vec_to_iarray A)] - Suc ia)" by (rule rev_nth[OF ia_less_length'])
      also have "... = 0 + (length [0..<IArray.length (vec_to_iarray A)] - Suc ia)" apply (rule nth_upt) using ia_less_length' by fastforce
      also have "... = (length [0..<IArray.length (vec_to_iarray A)] - Suc ia)" by simp
      finally have "a = (length [0..<IArray.length (vec_to_iarray A)] - Suc ia)" .
      hence ia_eq: "ia = length [0..<IArray.length (vec_to_iarray A)] - (Suc a)"
        by (metis Suc_diff_Suc Suc_eq_plus1_left diff_diff_cancel less_imp_le ia_less_length length_rev)      
      define ja where "ja = length [0..<IArray.length (vec_to_iarray A)] - to_nat y - 1"
      have ja_less_length: "ja < length [0..<IArray.length (vec_to_iarray A)]" unfolding ja_def 
        using ia_eq ia_less_length' by (simp add: algebra_simps )
      have suc_i_le: "IArray.length (vec_to_iarray A)\<ge>Suc (to_nat y)" unfolding vec_to_iarray_def  using to_nat_less_card[of y] by auto
      have "?xs ! ja = [0..<IArray.length (vec_to_iarray A)] ! (length [0..<IArray.length (vec_to_iarray A)] - Suc ja)" unfolding rev_nth[OF ja_less_length] ..
      also have "... = 0 + (length [0..<IArray.length (vec_to_iarray A)] - Suc ja)" apply (rule nth_upt, auto simp del: IArray.length_def) unfolding ja_def     
      by (metis diff_Suc_less ia_less_length' length_upt less_nat_zero_code minus_nat.diff_0 neq0_conv)
      also have "... = (length [0..<IArray.length (vec_to_iarray A)] - Suc ja)" by simp
      also have "... = to_nat y" unfolding ja_def using suc_i_le by force
      finally have xs_ja_eq_y: "?xs ! ja = to_nat y" .
      have ja_less_ia: "ja < ia" unfolding ja_def ia_eq by (auto simp del: IArray.length_def, metis Suc_leI suc_i_le diff_less_mono2 le_imp_less_Suc less_le_trans y_greater_a')
      hence eq_0: "vec_to_iarray A !! (?xs ! ja) = 0" using all_zero by simp
      hence "A $ y = 0" using vec_to_iarray_nth'[of A y] unfolding xs_ja_eq_y by simp
      thus False using Ay by contradiction
    qed
qed
thus ?thesis unfolding greatest_not_zero_def a unfolding to_nat_eq[symmetric] 
  unfolding to_nat_from_nat_id[OF a_less_card] by simp
qed

subsection\<open>Consistency and inconsistency\<close>

definition "consistent_iarrays A b = (let GJ=Gauss_Jordan_iarrays_PA A; 
                                           rank_A = length [x\<leftarrow>IArray.list_of (snd GJ) . \<not> is_zero_iarray x];
                                           P_mult_b = fst(GJ) *iv b
                                           in (rank_A \<ge> (if  (\<not> is_zero_iarray P_mult_b) 
                                           then (greatest_not_zero P_mult_b + 1) else 0)))"

definition "inconsistent_iarrays A b = (\<not> consistent_iarrays A b)"

lemma matrix_to_iarray_consistent[code]: "consistent A b = consistent_iarrays (matrix_to_iarray A) (vec_to_iarray b)"
unfolding consistent_eq_rank_ge_code
unfolding consistent_iarrays_def Let_def
unfolding Gauss_Jordan_PA_eq
unfolding rank_Gauss_Jordan_code[symmetric, unfolded Let_def]
unfolding snd_Gauss_Jordan_iarrays_PA_eq
unfolding rank_iarrays_code[symmetric]
unfolding matrix_to_iarray_rank
unfolding matrix_to_iarray_fst_Gauss_Jordan_PA[symmetric]
unfolding vec_to_iarray_matrix_matrix_mult[symmetric]
unfolding not_is_zero_iarray_eq_iff
using vec_to_iarray_greatest_not_zero[unfolded not_is_zero_iarray_eq_iff]
by force

lemma matrix_to_iarray_inconsistent[code]: "inconsistent A b = inconsistent_iarrays (matrix_to_iarray A) (vec_to_iarray b)"
unfolding inconsistent_def inconsistent_iarrays_def
unfolding matrix_to_iarray_consistent ..


definition "solve_consistent_rref_iarrays A b 
  = IArray.of_fun (\<lambda>j. if (IArray.exists (\<lambda>i. A !! i !! j = 1 \<and> j=least_non_zero_position_of_vector (row_iarray i A)) (IArray[0..<nrows_iarray A]))
  then b !! (least_non_zero_position_of_vector (column_iarray j A)) else 0) (ncols_iarray A)"


lemma exists_solve_consistent_rref:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
assumes rref: "reduced_row_echelon_form A"
shows "(\<exists>i. A $ i $ j = 1 \<and> j = (LEAST n. A $ i $ n \<noteq> 0)) 
  = (IArray.exists (\<lambda>i. (matrix_to_iarray A) !! i !! (to_nat j) = 1
  \<and> (to_nat j)=least_non_zero_position_of_vector (row_iarray i (matrix_to_iarray A))) (IArray[0..<nrows_iarray (matrix_to_iarray A)]))"
proof (rule)
assume "\<exists>i. A $ i $ j = 1 \<and> j = (LEAST n. A $ i $ n \<noteq> 0)"
from this obtain i where Aij: "A $ i $ j = 1" and j_eq: "j = (LEAST n. A $ i $ n \<noteq> 0)" by blast    
show "IArray.exists (\<lambda>i. matrix_to_iarray A !! i !! to_nat j = 1 \<and> to_nat j = least_non_zero_position_of_vector (row_iarray i (matrix_to_iarray A)))
     (IArray [0..<nrows_iarray (matrix_to_iarray A)])"
     unfolding IArray.exists_def find_Some_iff
     apply (rule bexI[of _ "to_nat i"])+
     proof (auto, unfold IArray.sub_def[symmetric])
      show "to_nat i < nrows_iarray (matrix_to_iarray A)" unfolding matrix_to_iarray_nrows[symmetric] nrows_def using to_nat_less_card by fast
               have "to_nat j = to_nat (LEAST n. A $ i $ n \<noteq> 0)" unfolding j_eq by simp
         also have "... = to_nat (LEAST n. A $ i $ n \<noteq> 0 \<and> 0\<le>n)" by (metis least_mod_type)
         also have "...= least_non_zero_position_of_vector_from_index (vec_to_iarray (row i A)) (to_nat (0::'cols))" 
           proof (rule vec_to_iarray_least_non_zero_position_of_vector_from_index''[symmetric, of "0::'cols" i A])
              show "\<not> vector_all_zero_from_index (to_nat (0::'cols), vec_to_iarray (row i A))"
                unfolding vector_all_zero_from_index_eq[symmetric, of "0::'cols" "row i A"] unfolding row_def vec_nth_inverse using Aij least_mod_type[of j] by fastforce
          qed
          also have "... = least_non_zero_position_of_vector (row_iarray (to_nat i) (matrix_to_iarray A))" unfolding vec_to_iarray_row least_non_zero_position_of_vector_def
          unfolding to_nat_0 ..
         finally show "to_nat j = least_non_zero_position_of_vector (row_iarray (to_nat i) (matrix_to_iarray A))" .
         show "matrix_to_iarray A !! mod_type_class.to_nat i !! mod_type_class.to_nat j = 1" unfolding matrix_to_iarray_nth using Aij .
         qed
next
assume ex_eq: "IArray.exists (\<lambda>i. matrix_to_iarray A !! i !! to_nat j = 1 \<and> to_nat j = least_non_zero_position_of_vector (row_iarray i (matrix_to_iarray A)))
     (IArray [0..<nrows_iarray (matrix_to_iarray A)])"
have "\<exists>y. List.find (\<lambda>i. matrix_to_iarray A !! i !! to_nat j = 1 \<and> to_nat j = least_non_zero_position_of_vector (row_iarray i (matrix_to_iarray A)))
         [0..<nrows_iarray (matrix_to_iarray A)] = Some y"
         proof (rule ccontr, simp del: IArray.length_def IArray.sub_def, unfold find_None_iff)
         assume" \<not> (\<exists>x. x \<in> set [0..<nrows_iarray (matrix_to_iarray A)] \<and>
            matrix_to_iarray A !! x !! mod_type_class.to_nat j = 1 \<and> mod_type_class.to_nat j = least_non_zero_position_of_vector (row_iarray x (matrix_to_iarray A)))"
            thus False using ex_eq unfolding IArray.exists_def by auto
         qed
from this obtain y where y: "List.find (\<lambda>i. matrix_to_iarray A !! i !! to_nat j = 1 \<and> to_nat j = least_non_zero_position_of_vector (row_iarray i (matrix_to_iarray A)))
         [0..<nrows_iarray (matrix_to_iarray A)] = Some y" by blast
from this obtain i where i_less_length: "i<length [0..<nrows_iarray (matrix_to_iarray A)]" and
     Aij_1: "matrix_to_iarray A !! ([0..<nrows_iarray (matrix_to_iarray A)] ! i) !! to_nat j = 1"
and j_eq: "to_nat j = least_non_zero_position_of_vector (row_iarray ([0..<nrows_iarray (matrix_to_iarray A)] ! i) (matrix_to_iarray A))" and 
  y_eq: "y = [0..<nrows_iarray (matrix_to_iarray A)] ! i"
    and least: "(\<forall>ja<i. \<not> (matrix_to_iarray A !! ([0..<nrows_iarray (matrix_to_iarray A)] ! ja) !! to_nat j = 1 \<and>
                to_nat j = least_non_zero_position_of_vector (row_iarray ([0..<nrows_iarray (matrix_to_iarray A)] ! ja) (matrix_to_iarray A))))"
unfolding find_Some_iff by blast
show "\<exists>i. A $ i $ j = 1 \<and> j = (LEAST n. A $ i $ n \<noteq> 0)"
  proof (rule exI[of _ "from_nat i"], rule conjI)
    have i_rw: "[0..<nrows_iarray (matrix_to_iarray A)] ! i = i" using nth_upt[of 0 i "nrows_iarray (matrix_to_iarray A)"] using i_less_length by auto 
    have i_less_card: "i < CARD ('rows)" using i_less_length unfolding nrows_iarray_def matrix_to_iarray_def by auto
    show A_ij: "A $ from_nat i $ j = 1"
      using Aij_1 unfolding i_rw using matrix_to_iarray_nth[of A "from_nat i" j] unfolding to_nat_from_nat_id[OF i_less_card] by simp
    have "to_nat j = least_non_zero_position_of_vector (row_iarray ([0..<nrows_iarray (matrix_to_iarray A)] ! i) (matrix_to_iarray A))" using j_eq .
    also have "... = least_non_zero_position_of_vector_from_index (row_iarray i (matrix_to_iarray A)) 0"
      unfolding least_non_zero_position_of_vector_def i_rw ..
    also have "... = least_non_zero_position_of_vector_from_index (vec_to_iarray (row (from_nat i) A)) (to_nat (0::'cols))" unfolding vec_to_iarray_row
    unfolding to_nat_from_nat_id[OF i_less_card] unfolding to_nat_0 ..
    also have "... = to_nat (LEAST n. A $ (from_nat i) $ n \<noteq> 0 \<and> 0 \<le> n)" 
        proof (rule vec_to_iarray_least_non_zero_position_of_vector_from_index'')
           show "\<not> vector_all_zero_from_index (to_nat (0::'cols), vec_to_iarray (row (from_nat i) A))"
           unfolding vector_all_zero_from_index_eq[symmetric] using A_ij by (metis iarray_to_vec_vec_to_iarray least_mod_type vec_matrix vec_to_iarray_row' zero_neq_one)
        qed
    also have "... = to_nat (LEAST n. A $ (from_nat i) $ n \<noteq> 0)" using least_mod_type by metis
    finally show "j = (LEAST n. A $ from_nat i $ n \<noteq> 0)" unfolding to_nat_eq .
    qed
qed
     

lemma to_nat_the_solve_consistent_rref: 
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
assumes rref: "reduced_row_echelon_form A"
and exists: "(\<exists>i. A $ i $ j = 1 \<and> j = (LEAST n. A $ i $ n \<noteq> 0))"
shows "to_nat (THE i. A $ i $ j = 1) = least_non_zero_position_of_vector (column_iarray (to_nat j) (matrix_to_iarray A))"
proof -
obtain i where Aij: "A $ i $ j = 1" and j:"j = (LEAST n. A $ i $ n \<noteq> 0)" using exists by blast
have "least_non_zero_position_of_vector (column_iarray (to_nat j) (matrix_to_iarray A)) = 
    least_non_zero_position_of_vector (vec_to_iarray (column j A))" unfolding vec_to_iarray_column ..
    also have "... = least_non_zero_position_of_vector_from_index (vec_to_iarray (column j A)) (to_nat (0::'rows))" unfolding least_non_zero_position_of_vector_def to_nat_0 ..
    also have "... = to_nat (LEAST n. A $ n $ j \<noteq> 0 \<and> 0 \<le> n)"
      proof (rule vec_to_iarray_least_non_zero_position_of_vector_from_index')
        show "\<not> vector_all_zero_from_index (to_nat (0::'rows), vec_to_iarray (column j A))"
          unfolding vector_all_zero_from_index_eq[symmetric] column_def using Aij least_mod_type[of i] by fastforce
      qed
    also have "... = to_nat (LEAST n. A $ n $ j \<noteq> 0)" using least_mod_type by metis
    finally have least_eq: "least_non_zero_position_of_vector (column_iarray (to_nat j) (matrix_to_iarray A)) = to_nat (LEAST n. A $ n $ j \<noteq> 0)" .
    have i_eq_least: "i=(LEAST n. A $ n $ j \<noteq> 0)"
      proof (rule Least_equality[symmetric])
         show "A $ i $ j \<noteq> 0" by (metis Aij zero_neq_one)
         show "\<And>y. A $ y $ j \<noteq> 0 \<Longrightarrow> i \<le> y" by (metis (mono_tags) Aij is_zero_row_def' j order_refl rref rref_condition4 zero_neq_one)
     qed
have the_eq_least_pos: "(THE i. A $ i $ j = 1) = from_nat (least_non_zero_position_of_vector (column_iarray (to_nat j) (matrix_to_iarray A)))"
  proof (rule the_equality)
      show " A $ from_nat (least_non_zero_position_of_vector (column_iarray (to_nat j) (matrix_to_iarray A))) $ j = 1"
    unfolding least_eq from_nat_to_nat_id i_eq_least[symmetric] using Aij .
    fix a assume a: "A $ a $ j = 1"
    show "a = from_nat (least_non_zero_position_of_vector (column_iarray (to_nat j) (matrix_to_iarray A)))"
      unfolding least_eq from_nat_to_nat_id
      by (metis Aij a i_eq_least is_zero_row_def' j rref rref_condition4_explicit zero_neq_one)
qed
have "to_nat (THE i. A $ i $ j = 1) = to_nat (from_nat (least_non_zero_position_of_vector (column_iarray (to_nat j) (matrix_to_iarray A)))::'rows)" using the_eq_least_pos by auto
also have "... = (least_non_zero_position_of_vector (column_iarray (to_nat j) (matrix_to_iarray A)))" by (rule to_nat_from_nat_id, unfold least_eq, simp add: to_nat_less_card)
also have "... = to_nat (LEAST n. A $ n $ j \<noteq> 0)" unfolding least_eq from_nat_to_nat_id ..
finally have "(THE i. A $ i $ j = 1) = (LEAST n. A $ n $ j \<noteq> 0)" unfolding to_nat_eq .
thus ?thesis unfolding least_eq from_nat_to_nat_id unfolding to_nat_eq .
qed

lemma iarray_exhaust2: 
"(xs = ys) = (IArray.list_of xs = IArray.list_of ys)"
by (metis iarray.exhaust list_of.simps)


lemma vec_to_iarray_solve_consistent_rref:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
assumes rref: "reduced_row_echelon_form A"
shows "vec_to_iarray (solve_consistent_rref A b) = solve_consistent_rref_iarrays (matrix_to_iarray A) (vec_to_iarray b)"
proof(unfold iarray_exhaust2 list_eq_iff_nth_eq IArray.length_def[symmetric] IArray.sub_def[symmetric], rule conjI)
  show "IArray.length (vec_to_iarray (solve_consistent_rref A b)) = IArray.length (solve_consistent_rref_iarrays (matrix_to_iarray A) (vec_to_iarray b))"
  unfolding solve_consistent_rref_def solve_consistent_rref_iarrays_def 
  unfolding ncols_iarray_def matrix_to_iarray_def by (simp add: vec_to_iarray_def)
show "\<forall>i<IArray.length (vec_to_iarray (solve_consistent_rref A b)). vec_to_iarray (solve_consistent_rref A b) !! i = solve_consistent_rref_iarrays (matrix_to_iarray A) (vec_to_iarray b) !! i"
proof (clarify)
fix i assume i: "i < IArray.length (vec_to_iarray (solve_consistent_rref A b))"
hence i_less_card: "i<CARD('cols)" unfolding vec_to_iarray_def by auto
hence i_less_ncols: "i<(ncols_iarray (matrix_to_iarray A))" unfolding ncols_eq_card_columns .
show "vec_to_iarray (solve_consistent_rref A b) !! i = solve_consistent_rref_iarrays (matrix_to_iarray A) (vec_to_iarray b) !! i"
unfolding vec_to_iarray_nth[OF i_less_card]
unfolding solve_consistent_rref_def
unfolding vec_lambda_beta
unfolding solve_consistent_rref_iarrays_def
unfolding of_fun_nth[OF i_less_ncols]
unfolding exists_solve_consistent_rref[OF rref, of "from_nat i", symmetric, unfolded to_nat_from_nat_id[OF i_less_card]]
using to_nat_the_solve_consistent_rref[OF rref, of "from_nat i", symmetric, unfolded to_nat_from_nat_id[OF i_less_card]]
using vec_to_iarray_nth' by metis
qed
qed

subsection\<open>Independence and dependence\<close>

definition "independent_and_consistent_iarrays A b = 
  (let GJ = Gauss_Jordan_iarrays_PA A; 
      rank_A = length [x\<leftarrow>IArray.list_of (snd GJ) . \<not> is_zero_iarray x];
      P_mult_b = fst GJ *iv b;
      consistent_A = ((if \<not> is_zero_iarray P_mult_b then greatest_not_zero P_mult_b + 1 else 0) \<le> rank_A);
      dim_solution_set = ncols_iarray A - rank_A
      in consistent_A \<and> dim_solution_set = 0)"

definition "dependent_and_consistent_iarrays A b = 
  (let GJ = Gauss_Jordan_iarrays_PA A; 
      rank_A = length [x\<leftarrow>IArray.list_of (snd GJ) . \<not> is_zero_iarray x];
      P_mult_b = fst GJ *iv b;
      consistent_A = ((if \<not> is_zero_iarray P_mult_b then greatest_not_zero P_mult_b + 1 else 0) \<le> rank_A);
      dim_solution_set = ncols_iarray A - rank_A
      in consistent_A \<and> dim_solution_set > 0)"

lemma matrix_to_iarray_independent_and_consistent[code]:
shows "independent_and_consistent A b = independent_and_consistent_iarrays (matrix_to_iarray A) (vec_to_iarray b)"
unfolding independent_and_consistent_def
unfolding independent_and_consistent_iarrays_def
unfolding dim_solution_set_homogeneous_eq_dim_null_space
unfolding matrix_to_iarray_consistent
unfolding consistent_iarrays_def
unfolding dim_null_space_iarray
unfolding rank_iarrays_code
unfolding snd_Gauss_Jordan_iarrays_PA_eq[symmetric]
unfolding Let_def ..


lemma matrix_to_iarray_dependent_and_consistent[code]:
shows "dependent_and_consistent A b = dependent_and_consistent_iarrays (matrix_to_iarray A) (vec_to_iarray b)"
unfolding dependent_and_consistent_def
unfolding dependent_and_consistent_iarrays_def
unfolding dim_solution_set_homogeneous_eq_dim_null_space
unfolding matrix_to_iarray_consistent
unfolding consistent_iarrays_def
unfolding dim_null_space_iarray
unfolding rank_iarrays_code
unfolding snd_Gauss_Jordan_iarrays_PA_eq[symmetric]
unfolding Let_def ..


subsection\<open>Solve a system of equations over nested IArrays\<close>

definition "solve_system_iarrays A b = (let A' = Gauss_Jordan_iarrays_PA A in (snd A', fst A' *iv b))"

lemma matrix_to_iarray_fst_solve_system: "matrix_to_iarray (fst (solve_system A b)) = fst (solve_system_iarrays (matrix_to_iarray A) (vec_to_iarray b))"
unfolding solve_system_def solve_system_iarrays_def Let_def fst_conv
by (metis matrix_to_iarray_snd_Gauss_Jordan_PA)

lemma vec_to_iarray_snd_solve_system: "vec_to_iarray (snd (solve_system A b)) = snd (solve_system_iarrays (matrix_to_iarray A) (vec_to_iarray b))"
unfolding solve_system_def solve_system_iarrays_def Let_def snd_conv
by (metis matrix_to_iarray_fst_Gauss_Jordan_PA vec_to_iarray_matrix_matrix_mult)

definition "solve_iarrays A b = (let GJ_P=Gauss_Jordan_iarrays_PA A; 
                        P_mult_b = fst GJ_P *iv b;
                        rank_A = length [x\<leftarrow>IArray.list_of (snd GJ_P) . \<not> is_zero_iarray x];
                        consistent_Ab = (if \<not> is_zero_iarray P_mult_b then greatest_not_zero P_mult_b + 1 else 0) \<le> rank_A;
                        GJ_transpose = Gauss_Jordan_iarrays_PA (transpose_iarray A);
                        basis =  set (map (\<lambda>i. row_iarray i (fst GJ_transpose)) [rank_A..<ncols_iarray A])
                        in (if consistent_Ab then Some (solve_consistent_rref_iarrays (snd GJ_P) P_mult_b,basis) else None))"


definition "pair_vec_vecset A = (if Option.is_none A then None else Some (vec_to_iarray (fst (the A)), vec_to_iarray` (snd (the A))))"

lemma pair_vec_vecset_solve[code_unfold]:
shows "pair_vec_vecset (solve A b) = solve_iarrays (matrix_to_iarray A) (vec_to_iarray b)"
unfolding pair_vec_vecset_def 
proof (auto)
assume none_solve_Ab: "Option.is_none (solve A b)"
show "None = solve_iarrays (matrix_to_iarray A) (vec_to_iarray b)"
    proof -
      define GJ_P where "GJ_P = Gauss_Jordan_iarrays_PA (matrix_to_iarray A)"
      define P_mult_b where "P_mult_b = fst GJ_P *iv vec_to_iarray b"
      define rank_A where "rank_A = length [x\<leftarrow>IArray.list_of (snd GJ_P). \<not> is_zero_iarray x]"
      have "\<not> consistent A b" using none_solve_Ab unfolding solve_def unfolding Option.is_none_def by auto
      hence "\<not> consistent_iarrays (matrix_to_iarray A) (vec_to_iarray b)" using matrix_to_iarray_consistent by auto
      hence "\<not> (if \<not> is_zero_iarray P_mult_b then greatest_not_zero P_mult_b + 1 else 0) \<le> rank_A"
        unfolding GJ_P_def P_mult_b_def rank_A_def
        using consistent_iarrays_def unfolding Let_def by fast
      thus ?thesis unfolding solve_iarrays_def Let_def unfolding GJ_P_def P_mult_b_def rank_A_def by presburger
    qed
next
assume not_none: "\<not> Option.is_none (solve A b)"
show "Some (vec_to_iarray (fst (the (solve A b))), vec_to_iarray ` snd (the (solve A b))) = solve_iarrays (matrix_to_iarray A) (vec_to_iarray b)"
proof -
  define GJ_P where "GJ_P = Gauss_Jordan_iarrays_PA (matrix_to_iarray A)"
  define P_mult_b where "P_mult_b = fst GJ_P *iv vec_to_iarray b"
  define rank_A where "rank_A = length [x\<leftarrow>IArray.list_of (snd GJ_P) . \<not> is_zero_iarray x]"
  define GJ_transpose where "GJ_transpose = Gauss_Jordan_iarrays_PA (transpose_iarray (matrix_to_iarray A))"
  define basis where "basis = set (map (\<lambda>i. row_iarray i (fst GJ_transpose)) [rank_A..<ncols_iarray (matrix_to_iarray A)])"
  define P_mult_b where "P_mult_b = fst GJ_P *iv vec_to_iarray b"
  have consistent_Ab: "consistent A b" using not_none unfolding solve_def unfolding Option.is_none_def by metis
  hence "consistent_iarrays (matrix_to_iarray A) (vec_to_iarray b)" using matrix_to_iarray_consistent by auto
  hence "(if \<not> is_zero_iarray P_mult_b then greatest_not_zero P_mult_b + 1 else 0) \<le> rank_A"
      unfolding GJ_P_def P_mult_b_def rank_A_def
      using consistent_iarrays_def unfolding Let_def by fast
  hence solve_iarrays_rw: "solve_iarrays (matrix_to_iarray A) (vec_to_iarray b) = Some (solve_consistent_rref_iarrays (snd GJ_P) P_mult_b, basis)"
  unfolding solve_iarrays_def Let_def P_mult_b_def GJ_P_def rank_A_def basis_def GJ_transpose_def by auto
  have snd_rw: "vec_to_iarray ` basis_null_space A = basis" unfolding basis_def GJ_transpose_def rank_A_def GJ_P_def
       unfolding vec_to_iarray_basis_null_space unfolding basis_null_space_iarrays_def Let_def
       unfolding snd_Gauss_Jordan_iarrays_PA_eq
       unfolding rank_iarrays_code[symmetric]
       unfolding matrix_to_iarray_transpose[symmetric]
       unfolding matrix_to_iarray_rank[symmetric]
       unfolding rank_transpose[symmetric, of A] ..
  have fst_rw: "vec_to_iarray (solve_consistent_rref (fst (solve_system A b)) (snd (solve_system A b))) = solve_consistent_rref_iarrays (snd GJ_P) P_mult_b"
    using vec_to_iarray_solve_consistent_rref[OF rref_Gauss_Jordan, of A "fst (Gauss_Jordan_PA A) *v b"]
    unfolding solve_system_def Let_def fst_conv
    unfolding Gauss_Jordan_PA_eq snd_conv
    unfolding GJ_P_def P_mult_b_def
    unfolding vec_to_iarray_matrix_matrix_mult
    unfolding matrix_to_iarray_fst_Gauss_Jordan_PA[symmetric]
    unfolding matrix_to_iarray_snd_Gauss_Jordan_PA[symmetric]
    unfolding Gauss_Jordan_PA_eq .
  show ?thesis unfolding solve_iarrays_rw
    unfolding solve_def if_P[OF consistent_Ab] option.sel fst_conv snd_conv
    unfolding fst_rw snd_rw ..
qed
qed

end
