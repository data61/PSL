(*  
    Title:      System_Of_Equations.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Solving systems of equations using the Gauss Jordan algorithm\<close>

theory System_Of_Equations
imports
 Gauss_Jordan_PA
 Bases_Of_Fundamental_Subspaces
begin

subsection\<open>Definitions\<close>

text\<open>Given a system of equations @{term "A *v x = b"}, the following function returns the pair @{term "(P ** A,P *v b)"}, where P is the matrix
      which states @{term "Gauss_Jordan A = P ** A"}. That matrix is computed by means of @{term "Gauss_Jordan_PA"}.\<close>

definition solve_system :: "('a::{field}^'cols::{mod_type}^'rows::{mod_type}) \<Rightarrow> ('a^'rows::{mod_type}) 
  \<Rightarrow> (('a^'cols::{mod_type}^'rows::{mod_type}) \<times> ('a^'rows::{mod_type}))"
  where "solve_system A b = (let A' = Gauss_Jordan_PA A in (snd A', (fst A') *v b))"

definition is_solution where "is_solution x A b = (A *v x = b)"

subsection\<open>Relationship between @{term "is_solution_def"} and @{term "solve_system_def"}\<close>

lemma is_solution_imp_solve_system:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  assumes xAb:"is_solution x A b"
  shows "is_solution x (fst (solve_system A b)) (snd (solve_system A b))"
proof -
  have "(fst (Gauss_Jordan_PA A)*v(A *v x) = fst (Gauss_Jordan_PA A) *v b)"
    using xAb unfolding is_solution_def by fast
  hence "(snd (Gauss_Jordan_PA A) *v x = fst (Gauss_Jordan_PA A) *v b)"
    unfolding matrix_vector_mul_assoc
    unfolding fst_Gauss_Jordan_PA[of A] .
  thus "is_solution x (fst (solve_system A b)) (snd (solve_system A b))"
    unfolding is_solution_def solve_system_def Let_def by simp
qed


lemma solve_system_imp_is_solution:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  assumes xAb: "is_solution x (fst (solve_system A b)) (snd (solve_system A b))"
  shows "is_solution x A b" 
proof -
  have "fst (solve_system A b) *v x = snd (solve_system A b)" 
    using xAb unfolding is_solution_def .
  hence "snd (Gauss_Jordan_PA A) *v x = fst (Gauss_Jordan_PA A) *v b" 
    unfolding solve_system_def Let_def fst_conv snd_conv .
  hence "(fst (Gauss_Jordan_PA A) ** A) *v x = fst (Gauss_Jordan_PA A) *v b" 
    unfolding fst_Gauss_Jordan_PA .
  hence "fst (Gauss_Jordan_PA A) *v (A *v x) = fst (Gauss_Jordan_PA A) *v b" 
    unfolding matrix_vector_mul_assoc .
  hence "matrix_inv (fst (Gauss_Jordan_PA A)) *v (fst (Gauss_Jordan_PA A) *v (A *v x)) 
  = matrix_inv (fst (Gauss_Jordan_PA A)) *v (fst (Gauss_Jordan_PA A) *v b)" by simp
  hence "(A *v x) = b"
    unfolding matrix_vector_mul_assoc[of "matrix_inv (fst (Gauss_Jordan_PA A))"]
    unfolding matrix_inv_left[OF invertible_fst_Gauss_Jordan_PA]
    unfolding matrix_vector_mul_lid .
  thus ?thesis unfolding is_solution_def .
qed

lemma is_solution_solve_system:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  shows "is_solution x A b = is_solution x (fst (solve_system A b)) (snd (solve_system A b))"
  using solve_system_imp_is_solution is_solution_imp_solve_system by blast

subsection\<open>Consistent and inconsistent systems of equations\<close>

definition consistent :: "'a::{field}^'cols::{mod_type}^'rows::{mod_type} \<Rightarrow> 'a::{field}^'rows::{mod_type} \<Rightarrow> bool"
  where "consistent A b = (\<exists>x. is_solution x A b)"

definition inconsistent where "inconsistent A b =  (\<not> (consistent A b))"

lemma inconsistent: "inconsistent A b = (\<not> (\<exists>x. is_solution x A b))"
  unfolding inconsistent_def consistent_def by simp

text\<open>The following function will be use to solve consistent systems which are already in the reduced row echelon form.\<close>

definition solve_consistent_rref :: "'a::{field}^'cols::{mod_type}^'rows::{mod_type} \<Rightarrow> 'a::{field}^'rows::{mod_type} \<Rightarrow> 'a::{field}^'cols::{mod_type}"
  where "solve_consistent_rref A b = (\<chi> j. if (\<exists>i. A $ i $ j = 1 \<and> j=(LEAST n. A $ i $ n \<noteq> 0)) then b $ (THE i. A $ i $ j = 1) else 0)"

lemma solve_consistent_rref_code[code abstract]:
  shows "vec_nth (solve_consistent_rref A b) = (% j. if (\<exists>i. A $ i $ j = 1 \<and> j=(LEAST n. A $ i $ n \<noteq> 0)) then b $ (THE i. A $ i $ j = 1) else 0)"
  unfolding solve_consistent_rref_def by auto


lemma rank_ge_imp_is_solution:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  assumes con: "rank A \<ge> (if (\<exists>a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) 
                                            then (to_nat (GREATEST a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) + 1) else 0)"
  shows "is_solution (solve_consistent_rref (Gauss_Jordan A) (P_Gauss_Jordan A *v b)) A b"
proof -
  have "is_solution (solve_consistent_rref (Gauss_Jordan A) (P_Gauss_Jordan A *v b)) (Gauss_Jordan A) (P_Gauss_Jordan A *v b)"
  proof (unfold is_solution_def solve_consistent_rref_def, subst matrix_vector_mult_def, vector, auto)
    fix a
    let ?f="\<lambda>j. Gauss_Jordan A $ a $ j *
      (if \<exists>i. Gauss_Jordan A $ i $ j = 1 \<and> j = (LEAST n. Gauss_Jordan A $ i $ n \<noteq> 0) 
        then (P_Gauss_Jordan A *v b) $ (THE i. Gauss_Jordan A $ i $ j = 1) else 0)"
    show "sum ?f UNIV = (P_Gauss_Jordan A *v b) $ a"
    proof (cases "A=0")
      case True
      hence rank_A_eq_0:"rank A = 0" using rank_0 by simp
      have "(P_Gauss_Jordan A *v b) = 0"
      proof (rule ccontr)
        assume not_zero: "P_Gauss_Jordan A *v b \<noteq> 0"
        hence ex_a: "\<exists>a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0" by (metis vec_eq_iff zero_index)
        show False using con unfolding if_P[OF ex_a] unfolding rank_A_eq_0 by auto
      qed

      thus ?thesis unfolding A_0_imp_Gauss_Jordan_0[OF True] by force
    next
      case False note A_not_zero=False
      define not_zero_positions_row_a where "not_zero_positions_row_a = {j. Gauss_Jordan A $ a $ j \<noteq> 0}"
      define zero_positions_row_a where "zero_positions_row_a = {j. Gauss_Jordan A $ a $ j = 0}"
      have UNIV_rw: "UNIV = not_zero_positions_row_a \<union> zero_positions_row_a" 
        unfolding zero_positions_row_a_def not_zero_positions_row_a_def by auto
      have disj: "not_zero_positions_row_a \<inter> zero_positions_row_a = {}" 
        unfolding zero_positions_row_a_def not_zero_positions_row_a_def by fastforce
      have sum_zero: "(sum ?f zero_positions_row_a) = 0" 
        by (unfold zero_positions_row_a_def, rule sum.neutral, fastforce)
      have "sum ?f (UNIV::'cols set)=sum ?f (not_zero_positions_row_a \<union> zero_positions_row_a)" 
        unfolding UNIV_rw ..
      also have "... = sum ?f (not_zero_positions_row_a) + (sum ?f zero_positions_row_a)" 
        by (rule sum.union_disjoint[OF _ _ disj], simp+)
      also have "... = sum ?f (not_zero_positions_row_a)" unfolding sum_zero by simp
      also have "... = (P_Gauss_Jordan A *v b) $ a"
      proof (cases "not_zero_positions_row_a = {}")
        case True note zero_row_a=True    
        show ?thesis 
        proof (cases "\<exists>a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0")
          case False hence "(P_Gauss_Jordan A *v b) $ a = 0" by simp
          thus ?thesis unfolding True by auto
        next
          case True
          have rank_not_0: "rank A \<noteq> 0" by (metis A_not_zero less_not_refl3 rank_Gauss_Jordan rank_greater_zero)
          have greatest_less_a: "(GREATEST a. \<not> is_zero_row a (Gauss_Jordan A)) < a"
          proof (unfold is_zero_row_def, rule greatest_less_zero_row)
            show " reduced_row_echelon_form_upt_k (Gauss_Jordan A) (ncols (Gauss_Jordan A))"
              using rref_Gauss_Jordan unfolding reduced_row_echelon_form_def .
            show "is_zero_row_upt_k a (ncols (Gauss_Jordan A)) (Gauss_Jordan A)"
              by (metis (mono_tags) Collect_empty_eq is_zero_row_upt_ncols not_zero_positions_row_a_def zero_row_a)
            show "\<not> (\<forall>a. is_zero_row_upt_k a (ncols (Gauss_Jordan A)) (Gauss_Jordan A))"
              by (metis False Gauss_Jordan_not_0 is_zero_row_upt_ncols vec_eq_iff zero_index)
          qed
          hence "to_nat (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A)) < to_nat a" using to_nat_mono by fast
          hence rank_le_to_nat_a: "rank A \<le> to_nat a" unfolding rank_eq_suc_to_nat_greatest[OF A_not_zero] by simp
          have "to_nat (GREATEST a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) < to_nat a" 
            using con unfolding consistent_def unfolding if_P[OF True] using rank_le_to_nat_a by simp 
          hence "(GREATEST a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) < a" by (metis not_le to_nat_mono')
          hence "(P_Gauss_Jordan A *v b) $ a = 0" using not_greater_Greatest by blast
          thus ?thesis unfolding zero_row_a by simp
        qed    
      next
        case False note not_empty=False
        have not_zero_positions_row_a_rw: "not_zero_positions_row_a = {LEAST j. (Gauss_Jordan A) $ a $ j \<noteq> 0} \<union> (not_zero_positions_row_a - {LEAST j. (Gauss_Jordan A) $ a $ j \<noteq> 0})"
          unfolding not_zero_positions_row_a_def
          by (metis (mono_tags) Collect_cong False LeastI_ex bot_set_def empty_iff insert_Diff_single insert_absorb insert_is_Un mem_Collect_eq not_zero_positions_row_a_def)  
        have sum_zero': "sum ?f (not_zero_positions_row_a - {LEAST j. (Gauss_Jordan A) $ a $ j \<noteq> 0}) = 0"
          by (rule sum.neutral, auto, metis is_zero_row_def' rref_Gauss_Jordan rref_condition4_explicit zero_neq_one)    
        have "sum ?f (not_zero_positions_row_a) = sum ?f {LEAST j. (Gauss_Jordan A) $ a $ j \<noteq> 0} + sum ?f (not_zero_positions_row_a - {LEAST j. (Gauss_Jordan A) $ a $ j \<noteq> 0})"
          by (subst not_zero_positions_row_a_rw, rule sum.union_disjoint[OF _ _ _], simp+)
        also have "... = ?f (LEAST j. (Gauss_Jordan A) $ a $ j \<noteq> 0)" using sum_zero' by force
        also have "... = (P_Gauss_Jordan A *v b) $ a"
        proof (cases "\<exists>i. (Gauss_Jordan A) $ i $ (LEAST j. (Gauss_Jordan A) $ a $ j \<noteq> 0) = 1 \<and> (LEAST j. (Gauss_Jordan A) $ a $ j \<noteq> 0) = (LEAST n. (Gauss_Jordan A) $ i $ n \<noteq> 0)")
          case True
          have A_least_eq_1: "(Gauss_Jordan A) $ a $ (LEAST j. (Gauss_Jordan A) $ a $ j \<noteq> 0) = 1"
            by (metis (mono_tags) empty_Collect_eq is_zero_row_def' not_empty not_zero_positions_row_a_def rref_Gauss_Jordan rref_condition2_explicit)
          moreover have "(THE i. (Gauss_Jordan A) $ i $ (LEAST j. (Gauss_Jordan A) $ a $ j \<noteq> 0) = 1) = a"
          proof (rule the_equality)
            show "(Gauss_Jordan A) $ a $ (LEAST j. (Gauss_Jordan A) $ a $ j \<noteq> 0) = 1" using A_least_eq_1 .
            show "\<And>i. (Gauss_Jordan A) $ i $ (LEAST j. (Gauss_Jordan A) $ a $ j \<noteq> 0) = 1 \<Longrightarrow> i = a"
              by (metis calculation is_zero_row_def' rref_Gauss_Jordan rref_condition4_explicit zero_neq_one)
          qed    
          ultimately show ?thesis unfolding if_P[OF True] by simp
        next
          case False 
          have "is_zero_row a (Gauss_Jordan A)" using False rref_Gauss_Jordan rref_condition2 by blast
          hence "(P_Gauss_Jordan A *v b) $ a = 0" 
            by (metis (mono_tags) IntI disj empty_iff insert_compr insert_is_Un is_zero_row_def' mem_Collect_eq not_zero_positions_row_a_rw zero_positions_row_a_def)
          thus ?thesis unfolding if_not_P[OF False] by fastforce
        qed
        finally show ?thesis .
      qed
      finally show "sum ?f UNIV = (P_Gauss_Jordan A *v b) $ a" .
    qed
  qed
  thus ?thesis apply (subst is_solution_solve_system)
    unfolding solve_system_def Let_def snd_conv fst_conv unfolding Gauss_Jordan_PA_eq P_Gauss_Jordan_def .
qed

corollary rank_ge_imp_consistent:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
assumes "rank A \<ge> (if (\<exists>a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) then (to_nat (GREATEST a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) + 1) else 0)"
shows "consistent A b"
using rank_ge_imp_is_solution assms unfolding consistent_def by auto


lemma inconsistent_imp_rank_less:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  assumes inc: "inconsistent A b"
  shows "rank A < (if (\<exists>a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) then (to_nat (GREATEST a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) + 1) else 0)"
proof (rule ccontr)
  assume "\<not> rank A < (if \<exists>a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0 then to_nat (GREATEST a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) + 1 else 0)"
  hence "(if \<exists>a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0 then to_nat (GREATEST a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) + 1 else 0) \<le> rank A" by simp
  hence "consistent A b" using rank_ge_imp_consistent by auto
  thus False using inc unfolding inconsistent_def by contradiction
qed


lemma rank_less_imp_inconsistent:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  assumes inc: "rank A < (if (\<exists>a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) then (to_nat (GREATEST a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) + 1) else 0)"
  shows "inconsistent A b"
proof (rule ccontr)
  define i where "i = (GREATEST a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0)"
  define j where "j = (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))"
  assume "\<not> inconsistent A b"
  hence ex_solution: "\<exists>x. is_solution x A b" unfolding inconsistent_def consistent_def by auto
  from this obtain x where "is_solution x A b"  by auto
  hence is_solution_solve: "is_solution x (Gauss_Jordan A) (P_Gauss_Jordan A *v b)"
    using is_solution_solve_system
    by (metis Gauss_Jordan_PA_eq P_Gauss_Jordan_def fst_conv snd_conv solve_system_def)
  show False 
  proof (cases "A=0")
    case True
    hence rank_eq_0: "rank A = 0" using rank_0 by simp
    hence exists_not_0:"(\<exists>a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0)" 
      using inc unfolding inconsistent
      using to_nat_plus_1_set[of "(GREATEST a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0)"]
      by presburger
    show False
      using True \<open>is_solution x A b\<close> exists_not_0 is_solution_def by force 
  next
    case False
    have j_less_i: "j<i"
    proof -
      have rank_less_greatest_i: "rank A < to_nat i + 1"
        using inc unfolding i_def inconsistent by presburger
      moreover have rank_eq_greatest_A: "rank A = to_nat j + 1" unfolding j_def by (rule rank_eq_suc_to_nat_greatest[OF False])
      ultimately have "to_nat j + 1 < to_nat i + 1" by simp
      hence "to_nat j < to_nat i" by auto
      thus "j<i" by (metis (full_types) not_le to_nat_mono')
    qed
    have is_zero_i: "is_zero_row i (Gauss_Jordan A)" by (metis (full_types) j_def j_less_i not_greater_Greatest)
    have "(Gauss_Jordan A *v x) $ i = 0" 
    proof (unfold matrix_vector_mult_def, auto, rule sum.neutral,clarify)
      fix a::'cols
      show "Gauss_Jordan A $ i $ a * x $ a = 0" using is_zero_i unfolding is_zero_row_def' by simp
    qed
    moreover have "(Gauss_Jordan A *v x) $ i \<noteq> 0"
    proof -
      have "Gauss_Jordan A *v x = P_Gauss_Jordan A *v b" using is_solution_def is_solution_solve by blast
      also have "... $ i \<noteq> 0"
        unfolding i_def
      proof (rule GreatestI_ex)
        show "\<exists>x. (P_Gauss_Jordan A *v b) $ x \<noteq> 0" using inc unfolding i_def inconsistent by presburger
      qed
      finally show ?thesis .
    qed
    ultimately show "False" by contradiction
  qed
qed


corollary consistent_imp_rank_ge:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  assumes "consistent A b"
  shows "rank A \<ge> (if (\<exists>a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) then (to_nat (GREATEST a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) + 1) else 0)"
  using rank_less_imp_inconsistent by (metis assms inconsistent_def not_less)

lemma inconsistent_eq_rank_less:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  shows "inconsistent A b = (rank A < (if (\<exists>a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) 
                                            then (to_nat (GREATEST a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) + 1) else 0))"
  using inconsistent_imp_rank_less rank_less_imp_inconsistent by blast

lemma consistent_eq_rank_ge:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  shows "consistent A b = (rank A \<ge> (if (\<exists>a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) 
                                            then (to_nat (GREATEST a. (P_Gauss_Jordan A *v b) $ a \<noteq> 0) + 1) else 0))"
  using consistent_imp_rank_ge rank_ge_imp_consistent by blast

corollary consistent_imp_is_solution:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  assumes "consistent A b"
  shows "is_solution (solve_consistent_rref (Gauss_Jordan A) (P_Gauss_Jordan A *v b)) A b"
  by (rule rank_ge_imp_is_solution[OF assms[unfolded consistent_eq_rank_ge]])


corollary consistent_imp_is_solution':
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  assumes "consistent A b"
  shows "is_solution (solve_consistent_rref (fst (solve_system A b)) (snd (solve_system A b))) A b"
  using consistent_imp_is_solution[OF assms] unfolding solve_system_def Let_def snd_conv fst_conv
  unfolding Gauss_Jordan_PA_eq P_Gauss_Jordan_def .


text\<open>Code equations optimized using Lets\<close>

lemma inconsistent_eq_rank_less_code[code]:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "inconsistent A b = (let GJ_P=Gauss_Jordan_PA A; 
                                P_mult_b = (fst(GJ_P) *v b);
                                rank_A = (if A = 0 then 0 else to_nat (GREATEST a. row a (snd GJ_P) \<noteq> 0) + 1)  in (rank_A < (if (\<exists>a. P_mult_b $ a \<noteq> 0) 
                                            then (to_nat (GREATEST a. P_mult_b $ a \<noteq> 0) + 1) else 0)))"
unfolding inconsistent_eq_rank_less Let_def rank_Gauss_Jordan_code
unfolding Gauss_Jordan_PA_eq P_Gauss_Jordan_def ..


lemma consistent_eq_rank_ge_code[code]:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "consistent A b = (let GJ_P=Gauss_Jordan_PA A; 
                              P_mult_b = (fst(GJ_P) *v b);
                              rank_A = (if A = 0 then 0 else to_nat (GREATEST a. row a (snd GJ_P) \<noteq> 0) + 1) in (rank_A \<ge> (if (\<exists>a. P_mult_b $ a \<noteq> 0) 
                                            then (to_nat (GREATEST a. P_mult_b $ a \<noteq> 0) + 1) else 0)))"
unfolding consistent_eq_rank_ge Let_def rank_Gauss_Jordan_code
unfolding Gauss_Jordan_PA_eq P_Gauss_Jordan_def ..


subsection\<open>Solution set of a system of equations. Dependent and independent systems.\<close>

definition solution_set where "solution_set A b = {x. is_solution x A b}"

lemma null_space_eq_solution_set: 
shows "null_space A = solution_set A 0" unfolding null_space_def solution_set_def is_solution_def ..

corollary dim_solution_set_homogeneous_eq_dim_null_space[code_unfold]:
shows "vec.dim (solution_set A 0) = vec.dim (null_space A)" using null_space_eq_solution_set[of A] by simp

lemma zero_is_solution_homogeneous_system:
shows "0 \<in> (solution_set A 0)"
unfolding solution_set_def is_solution_def
using matrix_vector_mult_0_right by fast

lemma homogeneous_solution_set_subspace:
fixes A::"'a::{field}^'n^'rows"
shows "vec.subspace (solution_set A 0)"
using subspace_null_space[of A] unfolding null_space_eq_solution_set .


lemma solution_set_rel:
fixes A::"'a::{field}^'n^'rows"
assumes p: "is_solution p A b"
shows "solution_set A b = {p} + (solution_set A 0)" 
proof (unfold set_plus_def, auto)
fix ba
assume ba: "ba \<in> solution_set A 0"
have "A *v (p + ba) = (A *v p) + (A *v ba)" unfolding matrix_vector_right_distrib ..
also have "... = b" using p ba unfolding solution_set_def is_solution_def by simp
finally show "p + ba \<in> solution_set A b" unfolding solution_set_def is_solution_def by simp
next
fix x
assume x: "x \<in> solution_set A b"
show "\<exists>b\<in>solution_set A 0. x = p + b"
proof (rule bexI[of _ "x-p"], simp)
have "A *v (x - p) = (A *v x) - (A *v p)" by (metis (no_types) add_diff_cancel diff_add_cancel matrix_vector_right_distrib)
also have "... = 0" using x p unfolding solution_set_def is_solution_def by simp
finally show  "x - p \<in> solution_set A 0"  unfolding solution_set_def is_solution_def by simp
qed
qed


lemma independent_and_consistent_imp_uniqueness_solution:
fixes A::"'a::{field}^'n::{mod_type}^'rows::{mod_type}"
assumes dim_0: "vec.dim (solution_set A 0) = 0"
and con: "consistent A b"
shows "\<exists>!x. is_solution x A b"
proof -
obtain p where p: "is_solution p A b" using con unfolding consistent_def by blast
have solution_set_0: "solution_set A 0 = {0}"
  using vec.dim_zero_eq[OF dim_0] zero_is_solution_homogeneous_system by blast
show "\<exists>!x. is_solution x A b"
  proof (rule ex_ex1I)
    show "\<exists>x. is_solution x A b" using p by auto
    fix x y assume x: "is_solution x A b" and y: "is_solution y A b"
    have "solution_set A b = {p} + (solution_set A 0)" unfolding solution_set_rel[OF p] ..
    also have "... = {p}" unfolding solution_set_0 set_plus_def by force
    finally show "x = y" using x y unfolding solution_set_def by (metis (full_types) mem_Collect_eq singleton_iff)
qed
qed

(*TODO: Maybe move. Until Isabelle2013-2 this lemma was part of the library.*)
lemma card_1_exists: "card s = 1 \<longleftrightarrow> (\<exists>!x. x \<in> s)"
  unfolding One_nat_def
  apply rule apply(drule card_eq_SucD) defer apply(erule ex1E) 
proof-
 fix x assume as:"x \<in> s" "\<forall>y. y \<in> s \<longrightarrow> y = x"
 have *:"s = insert x {}" apply - apply(rule,rule) unfolding singleton_iff     
 apply(rule as(2)[rule_format]) using as(1) by auto
 show "card s = Suc 0" unfolding * using card_insert by auto 
qed auto
 

corollary independent_and_consistent_imp_card_1:
fixes A::"'a::{field}^'n::{mod_type}^'rows::{mod_type}"
assumes dim_0: "vec.dim (solution_set A 0) = 0"
and con: "consistent A b"
shows "card (solution_set A b) = 1"
using independent_and_consistent_imp_uniqueness_solution[OF assms] unfolding solution_set_def 
using card_1_exists by auto

lemma uniqueness_solution_imp_independent:
fixes A::"'a::{field}^'n^'rows"
assumes ex1_sol: "\<exists>!x. is_solution x A b"
shows "vec.dim (solution_set A 0) = 0"
proof -
obtain x where x: "is_solution x A b" using ex1_sol by blast
have solution_set_homogeneous_zero: "solution_set A 0 = {0}"
    proof (rule ccontr)
    assume not_zero_set: "solution_set A 0 \<noteq> {0}"
    have homogeneous_not_empty: "solution_set A 0 \<noteq> {}" by (metis empty_iff zero_is_solution_homogeneous_system)
    obtain y where y: "y \<in> solution_set A 0" and y_not_0: "y \<noteq> 0" using not_zero_set homogeneous_not_empty by blast
   have "{x} = solution_set A b" unfolding solution_set_def using x ex1_sol by blast      
   also have "... = {x} + solution_set A 0" unfolding solution_set_rel[OF x] ..
   finally show False 
    by (metis (hide_lams, mono_tags) add_left_cancel monoid_add_class.add.right_neutral empty_iff insert_iff set_plus_intro y y_not_0)
   qed
thus ?thesis using vec.dim_zero_eq' by blast
qed


corollary uniqueness_solution_eq_independent_and_consistent:
fixes A::"'a::{field}^'n::{mod_type}^'rows::{mod_type}"
shows "(\<exists>!x. is_solution x A b) = (consistent A b \<and> vec.dim (solution_set A 0) = 0)"
using independent_and_consistent_imp_uniqueness_solution uniqueness_solution_imp_independent consistent_def
by metis


lemma consistent_homogeneous: 
shows "consistent A 0" unfolding consistent_def is_solution_def using matrix_vector_mult_0_right by fast

lemma dim_solution_set_0:
  fixes A::"'a::{field}^'n::{mod_type}^'rows::{mod_type}"
  shows "(vec.dim (solution_set A 0) = 0) = (solution_set A 0 = {0})"
  using homogeneous_solution_set_subspace vec.dim_zero_subspace_eq by auto


text\<open>We have to impose the restriction \<open>semiring_char_0\<close> in the following lemma,
because it may not hold over a general field (for instance, in Z2 there is a finite number of elements, so the solution
set can't be infinite.\<close>

lemma dim_solution_set_not_zero_imp_infinite_solutions_homogeneous:
fixes A::"'a::{field, semiring_char_0}^'n::{mod_type}^'rows::{mod_type}"
assumes dim_not_zero: "vec.dim (solution_set A 0) > 0"
shows "infinite (solution_set A 0)" 
proof -
have "solution_set A 0 \<noteq> {0}" using vec.dim_zero_subspace_eq[of "solution_set A 0"] dim_not_zero
  by (metis less_numeral_extra(3) vec.dim_zero_eq')
from this obtain x where x: "x \<in> solution_set A 0" and x_not_0: "x \<noteq> 0" using vec.subspace_0[OF homogeneous_solution_set_subspace, of A] by auto
define f where "f = (\<lambda>n::nat. (of_nat n) *s x)"
show ?thesis
  proof (unfold infinite_iff_countable_subset, rule exI[of _ f], rule conjI)
    show "inj f" unfolding inj_on_def unfolding f_def using x_not_0
      by (auto simp: vec_eq_iff)
    show "range f \<subseteq> solution_set A 0" using homogeneous_solution_set_subspace using x unfolding vec.subspace_def image_def f_def by fast
  qed
qed

lemma infinite_solutions_homogeneous_imp_dim_solution_set_not_zero:
  fixes A::"'a::{field}^'n::{mod_type}^'rows::{mod_type}"
  assumes i: "infinite (solution_set A 0)"
  shows "vec.dim (solution_set A 0) > 0"
  by (metis dim_solution_set_0 finite.simps gr0I i)

corollary infinite_solution_set_homogeneous_eq:
fixes A::"'a::{field,semiring_char_0}^'n::{mod_type}^'rows::{mod_type}"
shows "infinite (solution_set A 0) = (vec.dim (solution_set A 0) > 0)"
using infinite_solutions_homogeneous_imp_dim_solution_set_not_zero
using dim_solution_set_not_zero_imp_infinite_solutions_homogeneous by metis


corollary infinite_solution_set_homogeneous_eq':
fixes A::"'a::{field,semiring_char_0}^'n::{mod_type}^'rows::{mod_type}"
shows "(\<exists>\<^sub>\<infinity>x. is_solution x A 0) = (vec.dim (solution_set A 0) > 0)"
unfolding infinite_solution_set_homogeneous_eq[symmetric] INFM_iff_infinite unfolding solution_set_def ..

lemma infinite_solution_set_imp_consistent:
  "infinite (solution_set A b) \<Longrightarrow> consistent A b"
  by (auto dest!: infinite_imp_nonempty simp: solution_set_def consistent_def)

lemma dim_solution_set_not_zero_imp_infinite_solutions_no_homogeneous:
fixes A::"'a::{field, semiring_char_0}^'n::{mod_type}^'rows::{mod_type}"
assumes dim_not_0: "vec.dim (solution_set A 0) > 0"
and con: "consistent A b"
shows "infinite (solution_set A b)"
proof -
have "solution_set A 0 \<noteq> {0}" using vec.dim_zero_subspace_eq[of "solution_set A 0"] dim_not_0
  by (metis less_numeral_extra(3) vec.dim_zero_eq')
from this obtain x where x: "x \<in> solution_set A 0" and x_not_0: "x \<noteq> 0" using vec.subspace_0[OF homogeneous_solution_set_subspace, of A] by auto
obtain y where y: "is_solution y A b" using con unfolding consistent_def by blast
define f where "f = (\<lambda>n::nat. y + (of_nat n) *s x)"
show ?thesis 
  proof (unfold infinite_iff_countable_subset, rule exI[of _ f], rule conjI)
    show "inj f" unfolding inj_on_def unfolding f_def using x_not_0
      by (auto simp: vec_eq_iff)
    show "range f \<subseteq> solution_set A b"
      unfolding solution_set_rel[OF y] 
      using homogeneous_solution_set_subspace using x unfolding vec.subspace_def image_def f_def by fast
  qed
qed

lemma infinite_solutions_no_homogeneous_imp_dim_solution_set_not_zero_imp:
  fixes A::"'a::{field}^'n::{mod_type}^'rows::{mod_type}"
  assumes i: "infinite (solution_set A b)"
  shows "vec.dim (solution_set A 0) > 0"
  using i independent_and_consistent_imp_card_1 infinite_solution_set_imp_consistent by fastforce

corollary infinite_solution_set_no_homogeneous_eq:
fixes A::"'a::{field, semiring_char_0}^'n::{mod_type}^'rows::{mod_type}"
shows "infinite (solution_set A b) = (consistent A b \<and> vec.dim (solution_set A 0) > 0)"
using dim_solution_set_not_zero_imp_infinite_solutions_no_homogeneous
using infinite_solutions_no_homogeneous_imp_dim_solution_set_not_zero_imp
using infinite_solution_set_imp_consistent by blast

corollary infinite_solution_set_no_homogeneous_eq':
fixes A::"'a::{field, semiring_char_0}^'n::{mod_type}^'rows::{mod_type}"
shows "(\<exists>\<^sub>\<infinity>x. is_solution x A b) = (consistent A b \<and> vec.dim (solution_set A 0) > 0)"
unfolding infinite_solution_set_no_homogeneous_eq[symmetric] INFM_iff_infinite unfolding solution_set_def ..

definition "independent_and_consistent A b = (consistent A b \<and> vec.dim (solution_set A 0) = 0)"
definition "dependent_and_consistent A b = (consistent A b \<and> vec.dim (solution_set A 0) > 0)"

subsection\<open>Solving systems of linear equations\<close>

text\<open>The following function will solve any system of linear equations. Given a matrix \<open>A\<close> and a vector \<open>b\<close>, 
Firstly it makes use of the funcion @{term "solve_system"} to transform the original matrix \<open>A\<close> and the vector \<open>b\<close> 
into another ones in reduced row echelon form. Then, that system will have the same solution than the original one but it is easier to be solved.
So we make use of the function @{term "solve_consistent_rref"} to obtain one solution of the system.

We will prove that any solution of the system can be rewritten as a linear combination of elements of a basis of the null space plus a particular solution of the system.
So the function @{term "solve"} will return an option type, depending on the consistency of the system:
\begin{itemize}
\item If the system is consistent (so there exists at least one solution), the function will return the \<open>Some\<close> of a pair.
      In the first component of that pair will be one solution of the system and the second one will be a basis of the null space of the matrix. Hence:
    \begin{enumerate}
        \item If the system is consistent and independent (so there exists one and only one solution), the pair will consist of the solution and the empty set (this empty set is 
              the basis of the null space).
        \item If the system is consistent and dependent (so there exists more than one solution, maybe an infinite number), 
              the pair will consist of one particular solution and a basis of the null space (which will not be the empty set).
    \end{enumerate}
\item If the system is inconsistent (so there exists no solution), the function will return \<open>None\<close>.
\end{itemize}
\<close>

definition "solve A b = (if consistent A b then 
    Some (solve_consistent_rref (fst (solve_system A b)) (snd (solve_system A b)), basis_null_space A) 
    else None)"

lemma solve_code[code]:
  shows "solve A b = (let GJ_P=Gauss_Jordan_PA A; 
                        P_times_b=fst(GJ_P) *v b;
                        rank_A = (if A = 0 then 0 else to_nat (GREATEST a. row a (snd GJ_P) \<noteq> 0) + 1);
                        consistent_Ab = (rank_A \<ge> (if (\<exists>a. (P_times_b) $ a \<noteq> 0) then (to_nat (GREATEST a. (P_times_b) $ a \<noteq> 0) + 1) else 0));
                        GJ_transpose = Gauss_Jordan_PA (transpose A); 
                        basis = {row i (fst GJ_transpose) | i. to_nat i \<ge> rank_A}
                        in (if consistent_Ab then Some (solve_consistent_rref (snd GJ_P) P_times_b,basis) else None))"
  unfolding Let_def solve_def
  unfolding consistent_eq_rank_ge_code[unfolded Let_def,symmetric]
  unfolding basis_null_space_def Let_def
  unfolding P_Gauss_Jordan_def
  unfolding rank_Gauss_Jordan_code Let_def Gauss_Jordan_PA_eq
  unfolding solve_system_def Let_def fst_conv snd_conv
  unfolding Gauss_Jordan_PA_eq ..

lemma consistent_imp_is_solution_solve:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  assumes con: "consistent A b"
  shows "is_solution (fst (the (solve A b))) A b"
  unfolding solve_def unfolding if_P[OF con] fst_conv using consistent_imp_is_solution'[OF con] 
  by simp

corollary consistent_eq_solution_solve:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  shows "consistent A b = is_solution (fst (the (solve A b))) A b"
  by (metis consistent_def consistent_imp_is_solution_solve)

lemma inconsistent_imp_solve_eq_none:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  assumes con: "inconsistent A b"
  shows "solve A b = None" unfolding solve_def unfolding if_not_P[OF con[unfolded inconsistent_def]] ..

corollary inconsistent_eq_solve_eq_none:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  shows "inconsistent A b = (solve A b = None)"
  unfolding solve_def unfolding inconsistent_def by force

text\<open>We demonstrate that all solutions of a system of linear equations can be expressed as a linear combination of the basis of the null space plus a particular solution
obtained. The basis and the particular solution are obtained by means of the function @{term "solve A b"}\<close>

lemma solution_set_rel_solve:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  assumes con: "consistent A b"
  shows "solution_set A b = {fst (the (solve A b))} + vec.span (snd (the (solve A b)))"
proof -
  have s: "is_solution (fst (the (solve A b))) A b" using consistent_imp_is_solution_solve[OF con] by simp
  have "solution_set A b = {fst (the (solve A b))} + solution_set A 0" using solution_set_rel[OF s] .
  also have "... = {fst (the (solve A b))} + vec.span (snd (the (solve A b)))"
    unfolding set_plus_def solve_def unfolding if_P[OF con] snd_conv fst_conv 
  proof (safe, simp_all)
    fix b assume "b \<in> solution_set A 0"
    thus "b \<in> vec.span (basis_null_space A)" unfolding null_space_eq_solution_set[symmetric] using basis_null_space[of A] by fast
  next
    fix b
    assume b: "b \<in> vec.span (basis_null_space A)"
    thus "b \<in> solution_set A 0" unfolding null_space_eq_solution_set[symmetric] using basis_null_space by blast
  qed
  finally show "solution_set A b = {fst (the (solve A b))} + vec.span (snd (the (solve A b)))" .
qed

lemma is_solution_eq_in_span_solve:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  assumes con: "consistent A b"
  shows "(is_solution x A b) = (x \<in> {fst (the (solve A b))} + vec.span (snd (the (solve A b))))"
  using solution_set_rel_solve[OF con] unfolding solution_set_def by auto

end
