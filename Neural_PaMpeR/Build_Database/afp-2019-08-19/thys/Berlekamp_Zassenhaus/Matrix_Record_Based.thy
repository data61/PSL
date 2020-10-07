(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Matrix Operations in Fields\<close>

text \<open>We use our record based description of a field to perform matrix operations.\<close>

theory Matrix_Record_Based
imports 
  Jordan_Normal_Form.Gauss_Jordan_Elimination
  Jordan_Normal_Form.Gauss_Jordan_IArray_Impl
  Arithmetic_Record_Based   
begin


definition mat_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> 'b mat \<Rightarrow> bool" where
  "mat_rel R A B \<equiv> dim_row A = dim_row B \<and> dim_col A = dim_col B \<and> 
     (\<forall> i j. i < dim_row B \<longrightarrow> j < dim_col B \<longrightarrow> R (A $$ (i,j)) (B $$ (i,j)))"

lemma right_total_mat_rel: "right_total R \<Longrightarrow> right_total (mat_rel R)" 
  unfolding right_total_def
proof
  fix B
  assume "\<forall> y. \<exists> x. R x y"
  from choice[OF this] obtain f where f: "\<And> x. R (f x) x" by auto
  show "\<exists> A. mat_rel R A B"
    by (rule exI[of _ "map_mat f B"], unfold mat_rel_def, auto simp: f)
qed

lemma left_unique_mat_rel: "left_unique R \<Longrightarrow> left_unique (mat_rel R)"
  unfolding left_unique_def mat_rel_def mat_eq_iff by (auto, blast)

lemma right_unique_mat_rel: "right_unique R \<Longrightarrow> right_unique (mat_rel R)"
  unfolding right_unique_def mat_rel_def mat_eq_iff by (auto, blast)

lemma bi_unique_mat_rel: "bi_unique R \<Longrightarrow> bi_unique (mat_rel R)"
  using left_unique_mat_rel[of R] right_unique_mat_rel[of R]
  unfolding bi_unique_def left_unique_def right_unique_def by blast

lemma mat_rel_eq: "((R ===> R ===> (=))) (=) (=) \<Longrightarrow> 
  ((mat_rel R ===> mat_rel R ===> (=))) (=) (=)"
  unfolding mat_rel_def rel_fun_def mat_eq_iff by (auto, blast+)

definition vec_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a vec \<Rightarrow> 'b vec \<Rightarrow> bool" where
  "vec_rel R A B \<equiv> dim_vec A = dim_vec B \<and> (\<forall> i. i < dim_vec B \<longrightarrow> R (A $ i) (B $ i))"

lemma right_total_vec_rel: "right_total R \<Longrightarrow> right_total (vec_rel R)" 
  unfolding right_total_def
proof
  fix B
  assume "\<forall> y. \<exists> x. R x y"
  from choice[OF this] obtain f where f: "\<And> x. R (f x) x" by auto
  show "\<exists> A. vec_rel R A B"
    by (rule exI[of _ "map_vec f B"], unfold vec_rel_def, auto simp: f)
qed

lemma left_unique_vec_rel: "left_unique R \<Longrightarrow> left_unique (vec_rel R)"
  unfolding left_unique_def vec_rel_def vec_eq_iff by auto

lemma right_unique_vec_rel: "right_unique R \<Longrightarrow> right_unique (vec_rel R)"
  unfolding right_unique_def vec_rel_def vec_eq_iff by auto

lemma bi_unique_vec_rel: "bi_unique R \<Longrightarrow> bi_unique (vec_rel R)"
  using left_unique_vec_rel[of R] right_unique_vec_rel[of R]
  unfolding bi_unique_def left_unique_def right_unique_def by blast

lemma vec_rel_eq: "((R ===> R ===> (=))) (=) (=) \<Longrightarrow> 
  ((vec_rel R ===> vec_rel R ===> (=))) (=) (=)"
  unfolding vec_rel_def rel_fun_def vec_eq_iff by (auto, blast+)

lemma multrow_transfer[transfer_rule]: "((R ===> R ===> R) ===> (=) ===> R
  ===> mat_rel R ===> mat_rel R) mat_multrow_gen mat_multrow_gen"
  unfolding mat_rel_def[abs_def] mat_multrow_gen_def[abs_def]
  by (intro rel_funI conjI allI impI eq_matI, auto simp: rel_fun_def) 

(* we need index restrictions, TODO: can this be incorporated into transfer rule? *)
lemma swap_rows_transfer: "mat_rel R A B \<Longrightarrow> i < dim_row B \<Longrightarrow> j < dim_row B \<Longrightarrow> 
  mat_rel R (mat_swaprows i j A) (mat_swaprows i j B)"
  unfolding mat_rel_def mat_swaprows_def
  by (intro rel_funI conjI allI impI eq_matI, auto)

lemma pivot_positions_gen_transfer: assumes [transfer_rule]: "(R ===> R ===> (=)) (=) (=)" 
  shows 
  "(R ===> mat_rel R ===> (=)) pivot_positions_gen pivot_positions_gen" 
proof (intro rel_funI, goal_cases)
  case (1 ze ze' A A')
  note trans[transfer_rule] = 1  
  from 1 have dim: "dim_row A = dim_row A'" "dim_col A = dim_col A'" unfolding mat_rel_def by auto
  obtain i j where id: "i = 0" "j = 0" and ij: "i \<le> dim_row A'" "j \<le> dim_col A'" by auto
  have "pivot_positions_main_gen ze A (dim_row A) (dim_col A) i j =
    pivot_positions_main_gen ze' A' (dim_row A') (dim_col A') i j"
    using ij
  proof (induct i j rule: pivot_positions_main_gen.induct[of "dim_row A'" "dim_col A'" A' ze'])
    case (1 i j)    
    note simps[simp] = pivot_positions_main_gen.simps[of _ _ _ _ i j]
    show ?case 
    proof (cases "i < dim_row A' \<and> j < dim_col A'")
      case False
      with dim show ?thesis by auto
    next
      case True
      hence ij: "i < dim_row A'" "j < dim_col A'" and j: "Suc j \<le> dim_col A'" by auto
      note IH = 1(1-2)[OF ij _ _ j]
      from ij True trans have [transfer_rule]:"R (A $$ (i,j)) (A' $$ (i,j))" 
        unfolding mat_rel_def by auto
      have eq: "(A $$ (i,j) = ze) = (A' $$ (i,j) = ze')" by transfer_prover
      show ?thesis
      proof (cases "A' $$ (i,j) = ze'")
        case True
        from ij have "i \<le> dim_row A'" by auto
        note IH = IH(1)[OF True this]
        thus ?thesis using True ij dim eq by simp
      next
        case False
        from ij have "Suc i \<le> dim_row A'" by auto
        note IH = IH(2)[OF False this]
        thus ?thesis using False ij dim eq by simp
      qed
    qed
  qed
  thus "pivot_positions_gen ze A = pivot_positions_gen ze' A'"
    unfolding pivot_positions_gen_def id .
qed

lemma set_pivot_positions_main_gen: 
  "set (pivot_positions_main_gen ze A nr nc i j) \<subseteq> {0 ..< nr} \<times> {0 ..< nc}"
proof (induct i j rule: pivot_positions_main_gen.induct[of nr nc A ze])
  case (1 i j)
  note [simp] = pivot_positions_main_gen.simps[of _ _ _ _ i j]
  from 1 show ?case
    by (cases "i < nr \<and> j < nc", auto)
qed
  
lemma find_base_vectors_transfer: assumes [transfer_rule]: "(R ===> R ===> (=)) (=) (=)"
  shows "((R ===> R) ===> R ===> R ===> mat_rel R 
  ===> list_all2 (vec_rel R)) find_base_vectors_gen find_base_vectors_gen"
proof (intro rel_funI, goal_cases)
  case (1 um um' ze ze' on on' A A')
  note trans[transfer_rule] = 1 pivot_positions_gen_transfer[OF assms]
  from 1(4) have dim: "dim_row A = dim_row A'" "dim_col A = dim_col A'" unfolding mat_rel_def by auto
  have id: "pivot_positions_gen ze A = pivot_positions_gen ze' A'" by transfer_prover
  obtain xs where xs: "map snd (pivot_positions_gen ze' A') = xs" by auto
  obtain ys where ys: "[j\<leftarrow>[0..<dim_col A'] . j \<notin> set xs] = ys" by auto
  show "list_all2 (vec_rel R) (find_base_vectors_gen um ze on A) 
    (find_base_vectors_gen um' ze' on' A')"
    unfolding find_base_vectors_gen_def Let_def id xs list_all2_conv_all_nth length_map ys dim
  proof (intro conjI[OF refl] allI impI)
    fix i
    assume i: "i < length ys" 
    define y where "y = ys ! i" 
    from i have y: "y < dim_col A'" unfolding y_def ys[symmetric] using nth_mem by fastforce
    let ?map = "map_of (map prod.swap (pivot_positions_gen ze' A'))"
    {
      fix i
      assume i: "i < dim_col A'"
      and neq: "i \<noteq> y" 
      have "R (case ?map i of None \<Rightarrow> ze | Some j \<Rightarrow> um (A $$ (j, y)))
          (case ?map i of None \<Rightarrow> ze' | Some j \<Rightarrow> um' (A' $$ (j, y)))"
      proof (cases "?map i")
        case None
        with trans(2) show ?thesis by auto
      next 
        case (Some j)
        from map_of_SomeD[OF this] have "(j,i) \<in> set (pivot_positions_gen ze' A')" by auto
        from subsetD[OF set_pivot_positions_main_gen this[unfolded pivot_positions_gen_def]]
        have j: "j < dim_row A'" by auto
        with trans(4) y have [transfer_rule]: "R (A $$ (j,y)) (A' $$ (j,y))" unfolding mat_rel_def by auto
        show ?thesis unfolding Some by (simp, transfer_prover)
      qed
    } note main = this
    show "vec_rel R (map (non_pivot_base_gen um ze on A (pivot_positions_gen ze' A')) ys ! i)
          (map (non_pivot_base_gen um' ze' on' A' (pivot_positions_gen ze' A')) ys ! i)"
      unfolding y_def[symmetric] nth_map[OF i]
      unfolding non_pivot_base_gen_def Let_def dim vec_rel_def
      by (intro conjI allI impI, force, insert main, auto simp: trans(3))
  qed
qed
  

lemma eliminate_entries_gen_transfer: assumes *[transfer_rule]: "(R ===> R ===> R) ad ad'"
  "(R ===> R ===> R) mul mul'"
  and vs: "\<And> j. j < dim_row B' \<Longrightarrow> R (vs j) (vs' j)" 
  and i: "i < dim_row B'"  
  and B: "mat_rel R B B'"
  shows "mat_rel R 
   (eliminate_entries_gen ad mul vs B i j) 
   (eliminate_entries_gen ad' mul' vs' B' i j)"
proof - 
  note BB = B[unfolded mat_rel_def]  
  show ?thesis unfolding mat_rel_def dim_eliminate_entries_gen
  proof (intro conjI impI allI)
    fix i' j'
    assume ij': "i' < dim_row B'" "j' < dim_col B'"
    with BB have ij: "i'< dim_row B" "j' < dim_col B" by auto
    have [transfer_rule]: "R (B $$ (i', j')) (B' $$ (i', j'))" using BB ij' by auto
    have [transfer_rule]: "R (B $$ (i, j')) (B' $$ (i, j'))" using BB ij' i by auto
    have [transfer_rule]: "R (vs i') (vs' i')" using ij' vs[of i'] by auto
    show "R (eliminate_entries_gen ad mul vs B i j $$ (i', j'))
        (eliminate_entries_gen ad' mul' vs' B' i j $$ (i', j'))" 
      unfolding eliminate_entries_gen_def index_mat(1)[OF ij] index_mat(1)[OF ij'] split
      by transfer_prover
  qed (insert BB, auto)
qed

context
  fixes ops :: "'i arith_ops_record" (structure)
begin
private abbreviation (input) zero where "zero \<equiv> arith_ops_record.zero ops"
private abbreviation (input) one where "one \<equiv> arith_ops_record.one ops"
private abbreviation (input) plus where "plus \<equiv> arith_ops_record.plus ops"
private abbreviation (input) times where "times \<equiv> arith_ops_record.times ops"
private abbreviation (input) minus where "minus \<equiv> arith_ops_record.minus ops"
private abbreviation (input) uminus where "uminus \<equiv> arith_ops_record.uminus ops"
private abbreviation (input) divide where "divide \<equiv> arith_ops_record.divide ops"
private abbreviation (input) inverse where "inverse \<equiv> arith_ops_record.inverse ops"
private abbreviation (input) modulo where "modulo \<equiv> arith_ops_record.modulo ops"
private abbreviation (input) normalize where "normalize \<equiv> arith_ops_record.normalize ops"

definition eliminate_entries_gen_zero :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> (integer \<Rightarrow> 'a) \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "eliminate_entries_gen_zero minu time z v A I J = mat (dim_row A) (dim_col A) (\<lambda> (i, j).
     if v (integer_of_nat i) \<noteq> z \<and> i \<noteq> I then minu (A $$ (i,j)) (time (v (integer_of_nat i)) (A $$ (I,j))) else A $$ (i,j))" 
  
definition eliminate_entries_i where "eliminate_entries_i \<equiv> eliminate_entries_gen_zero minus times zero"
definition multrow_i where "multrow_i \<equiv> mat_multrow_gen times"
  
lemma dim_eliminate_entries_gen_zero[simp]:
  "dim_row (eliminate_entries_gen_zero mm tt z v B i as) = dim_row B"
  "dim_col (eliminate_entries_gen_zero mm tt z v B i as) = dim_col B"
  unfolding eliminate_entries_gen_zero_def by auto

partial_function (tailrec) gauss_jordan_main_i :: "nat \<Rightarrow> nat \<Rightarrow> 'i mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'i mat" where
  [code]: "gauss_jordan_main_i nr nc A i j = (
    if i < nr \<and> j < nc then let aij = A $$ (i,j) in if aij = zero then
      (case [ i' . i' <- [Suc i ..< nr],  A $$ (i',j) \<noteq> zero] 
        of [] \<Rightarrow> gauss_jordan_main_i nr nc A i (Suc j)
         | (i' # _) \<Rightarrow> gauss_jordan_main_i nr nc (swaprows i i' A) i j)
      else if aij = one then let 
        v = (\<lambda> i. A $$ (nat_of_integer i,j)) in
        gauss_jordan_main_i nr nc
        (eliminate_entries_i v A i j) (Suc i) (Suc j)
      else let iaij = inverse aij; A' = multrow_i i iaij A;
        v = (\<lambda> i. A' $$ (nat_of_integer i,j))
        in gauss_jordan_main_i nr nc (eliminate_entries_i v A' i j) (Suc i) (Suc j)
    else A)"

definition gauss_jordan_single_i :: "'i mat \<Rightarrow> 'i mat" where
  "gauss_jordan_single_i A \<equiv> gauss_jordan_main_i (dim_row A) (dim_col A) A 0 0"

definition find_base_vectors_i :: "'i mat \<Rightarrow> 'i vec list" where
  "find_base_vectors_i A \<equiv> find_base_vectors_gen uminus zero one A"
end

(* **************************************************************************** *)
(* subsection \<open>Proofs\<close> *)

context field_ops
begin

lemma right_total_poly_rel[transfer_rule]: "right_total (mat_rel R)"
  using right_total_mat_rel[of R] right_total .

lemma bi_unique_poly_rel[transfer_rule]: "bi_unique (mat_rel R)"
  using bi_unique_mat_rel[of R] bi_unique .

lemma eq_mat_rel[transfer_rule]: "(mat_rel R ===> mat_rel R ===> (=)) (=) (=)"
  by (rule mat_rel_eq[OF eq])

lemma multrow_i[transfer_rule]: "((=) ===> R ===> mat_rel R ===> mat_rel R)
  (multrow_i ops) multrow" 
  using multrow_transfer[of R] times unfolding multrow_i_def rel_fun_def by blast  

lemma eliminate_entries_gen_zero[simp]:
  assumes "mat_rel R A A'" "I < dim_row A'" shows
  "eliminate_entries_gen_zero minus times zero v A I J = eliminate_entries_gen minus times (v o integer_of_nat) A I J"
  unfolding eliminate_entries_gen_def eliminate_entries_gen_zero_def
proof(standard,goal_cases)
  case (1 i j)
  have d1:"DP (A $$ (I, j))" and d2:"DP (A $$ (i, j))" using assms DPR 1
    unfolding mat_rel_def dim_col_mat dim_row_mat
    by (metis Domainp.DomainI)+
  have e1:"\<And> x. (0::'a) * x = 0" and e2:"\<And> x. x - (0::'a) = x" by auto
  from e1[untransferred,OF d1] e2[untransferred,OF d2] 1 show ?case by auto
qed auto

lemma eliminate_entries_i: assumes  
  vs: "\<And> j. j < dim_row B' \<Longrightarrow> R (vs (integer_of_nat j)) (vs' j)" 
  and i: "i < dim_row B'"  
  and B: "mat_rel R B B'"  
  shows "mat_rel R (eliminate_entries_i ops vs B i j) 
    (eliminate_entries vs' B' i j)"
  unfolding eliminate_entries_i_def eliminate_entries_gen_zero[OF B i]
  by (rule eliminate_entries_gen_transfer, insert assms, auto simp: plus times minus)

lemma gauss_jordan_main_i:  
  "nr = dim_row A' \<Longrightarrow> nc = dim_col A' \<Longrightarrow> mat_rel R A A' \<Longrightarrow> i \<le> nr \<Longrightarrow> j \<le> nc \<Longrightarrow>
    mat_rel R (gauss_jordan_main_i ops nr nc A i j) (fst (gauss_jordan_main A' B' i j))"
proof -
  obtain P where P: "P = (A',i,j)" by auto
  let ?Rel = "measures [\<lambda> (A' :: 'a mat,i,j). nc - j, \<lambda> (A',i,j). if A' $$ (i,j) = 0 then 1 else 0]"
  have wf: "wf ?Rel" by simp
  show "nr = dim_row A' \<Longrightarrow> nc = dim_col A' \<Longrightarrow> mat_rel R A A' \<Longrightarrow> i \<le> nr \<Longrightarrow> j \<le> nc \<Longrightarrow>
    mat_rel R (gauss_jordan_main_i ops nr nc A i j) (fst (gauss_jordan_main A' B' i j))"
    using P
  proof (induct P arbitrary: A' B' A i j rule: wf_induct[OF wf])
    case (1 P A' B' A i j)
    note prems = 1(2-6)
    note P = 1(7)
    note A[transfer_rule] = prems(3)
    note IH = 1(1)[rule_format, OF _ _ _ _ _ _ refl]
    note simps = gauss_jordan_main_code[of A' B' i j, unfolded Let_def, folded prems(1-2)] 
      gauss_jordan_main_i.simps[of ops nr nc A i j] Let_def if_True if_False
    show ?case
    proof (cases "i < nr \<and> j < nc")
      case False
      hence id: "(i < nr \<and> j < nc) = False" by simp
      show ?thesis unfolding simps id by simp transfer_prover
    next
      case True note ij' = this
      hence id: "(i < nr \<and> j < nc) = True" "\<And> x y z. (if x = x then y else z) = y" by auto
      from True prems have ij [transfer_rule]:"R (A $$ (i,j)) (A' $$ (i,j))" 
        unfolding mat_rel_def by auto
      from True prems have i: "i < dim_row A'" "j < dim_col A'" and i': "i < nr" "j < nc" by auto
      {
        fix i
        assume "i < dim_row A'"
        with i True prems have R[transfer_rule]:"R (A $$ (i,j)) (A' $$ (i,j))" 
          unfolding mat_rel_def by auto
        have "(A $$ (i,j) = zero) = (A' $$ (i,j) = 0)" by transfer_prover
        note this R
      } note eq_gen = this    
      have eq: "(A $$ (i,j) = zero) = (A' $$ (i,j) = 0)"
        "(A $$ (i,j) = one) = (A' $$ (i,j) = 1)"
        by transfer_prover+
      show ?thesis
      proof (cases "A' $$ (i, j) = 0")
        case True
        hence eq: "A $$ (i,j) = zero" using eq by auto
        let ?is = "[ i' . i' <- [Suc i ..< nr],  A $$ (i',j) \<noteq> zero]"
        let ?is' = "[ i' . i' <- [Suc i ..< nr],  A' $$ (i',j) \<noteq> 0]"
        define xs where "xs = [Suc i..<nr]" 
        have xs: "set xs \<subseteq> {0 ..< dim_row A'}" unfolding xs_def using prems by auto
        hence id': "?is = ?is'" unfolding xs_def[symmetric]
          by (induct xs, insert eq_gen, auto)
        show ?thesis
        proof (cases ?is')
          case Nil
          have "?thesis = (mat_rel R (gauss_jordan_main_i ops nr nc A i (Suc j)) 
            (fst (gauss_jordan_main A' B' i (Suc j))))" 
            unfolding True simps id eq unfolding Nil id'[unfolded Nil] by simp
          also have "\<dots>"
            by (rule IH, insert i prems P, auto)
          finally show ?thesis .
        next
          case (Cons i' idx')
          from arg_cong[OF this, of set] i 
          have i': "i' < nr" "A' $$ (i', j) \<noteq> 0" by auto
          with ij' prems(1-2) have *: "i' < dim_row A'" "i < dim_row A'" "j < dim_col A'" by auto
          have rel: "((swaprows i i' A', i, j), P) \<in> ?Rel"
            by (simp add: P True * i')
          have "?thesis = (mat_rel R (gauss_jordan_main_i ops nr nc (swaprows i i' A) i j)
            (fst (gauss_jordan_main (swaprows i i' A') (swaprows i i' B') i j)))"
             unfolding True simps id eq Cons id'[unfolded Cons] by simp
          also have "\<dots>" 
            by (rule IH[OF rel _ _ swap_rows_transfer], insert i i' prems P True, auto)
          finally show ?thesis .
        qed
      next
        case False
        from False eq have neq: "(A $$ (i, j) = zero) = False" "(A' $$ (i, j) = 0) = False" by auto
        {
          fix B B' i
          assume B[transfer_rule]: "mat_rel R B B'" and dim: "dim_col B' = nc" and i: "i < dim_row B'"
          from dim i True have "j < dim_col B'" by simp
          with B i have "R (B $$ (i,j)) (B' $$ (i,j))"
            by (simp add: mat_rel_def)
        } note vec_rel = this        
        from prems have dim: "dim_row A = dim_row A'" unfolding mat_rel_def by auto
        show ?thesis 
        proof (cases "A' $$ (i, j) = 1")
          case True
          from True eq have eq: "(A $$ (i,j) = one) = True" "(A' $$ (i,j) = 1) = True" by auto
          note rel = vec_rel[OF A]
          show ?thesis unfolding simps id neq eq
            by (rule IH[OF _ _ _ eliminate_entries_i], insert rel prems ij i P dim, auto)
        next
          case False
          from False eq have eq: "(A $$ (i,j) = one) = False" "(A' $$ (i,j) = 1) = False" by auto
          show ?thesis unfolding simps id neq eq 
          proof (rule IH, goal_cases)
            case 4
            have A': "mat_rel R (multrow_i ops i (inverse (A $$ (i, j))) A)
              (multrow i (inverse_class.inverse (A' $$ (i, j))) A')" by transfer_prover
            note rel = vec_rel[OF A']
            show ?case 
              by (rule eliminate_entries_i[OF _ _ A'], insert rel prems i dim, auto)
          qed (insert prems i P, auto)
        qed
      qed
    qed
  qed   
qed

lemma gauss_jordan_i[transfer_rule]:  
  "(mat_rel R ===> mat_rel R) (gauss_jordan_single_i ops) gauss_jordan_single"
proof (intro rel_funI)
  fix A A'
  assume A: "mat_rel R A A'"
  show "mat_rel R (gauss_jordan_single_i ops A) (gauss_jordan_single A')"
    unfolding gauss_jordan_single_def gauss_jordan_single_i_def gauss_jordan_def
    by (rule gauss_jordan_main_i[OF _ _ A], insert A, auto simp: mat_rel_def)
qed

lemma find_base_vectors_i[transfer_rule]:  
  "(mat_rel R ===> list_all2 (vec_rel R)) (find_base_vectors_i ops) find_base_vectors"
  unfolding find_base_vectors_i_def[abs_def] 
  using find_base_vectors_transfer[OF eq] uminus zero one 
  unfolding rel_fun_def by blast
  
end

lemma list_of_vec_transfer[transfer_rule]: "(vec_rel A ===> list_all2 A) list_of_vec list_of_vec"
  unfolding rel_fun_def vec_rel_def vec_eq_iff list_all2_conv_all_nth
  by auto

lemma IArray_sub'[simp]: "i < IArray.length a \<Longrightarrow> IArray.sub' (a, integer_of_nat i) = IArray.sub a i" 
  by auto

lift_definition eliminate_entries_i2 ::
  "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (integer \<Rightarrow> 'a) \<Rightarrow> 'a mat_impl \<Rightarrow> integer \<Rightarrow> 'a mat_impl" is
  "\<lambda> z mminus ttimes v (nr, nc, a) i'.
   (nr,nc,let ai' = IArray.sub' (a, i') in (IArray.tabulate (integer_of_nat nr, \<lambda> i. let ai = IArray.sub' (a, i) in
     if i = i' then ai else 
     let vi'j = v i 
     in if vi'j = z then ai
        else 
             IArray.tabulate (integer_of_nat nc, \<lambda> j. mminus (IArray.sub' (ai, j)) (ttimes vi'j 
               (IArray.sub' (ai', j))))
       )))" 
proof(goal_cases)
  case (1 z mm tt  vec prod nat2)
  thus ?case by(cases prod;cases "snd (snd prod)";auto simp:Let_def)
qed

lemma eliminate_entries_gen_zero [simp]:
  assumes "i<(dim_row A)" "j<(dim_col A)" shows
  "eliminate_entries_gen_zero mminus ttimes z v A I J $$ (i, j) =
   (if v (integer_of_nat i) = z \<or> i = I then A $$ (i,j) else mminus (A $$ (i,j)) (ttimes (v (integer_of_nat i)) (A $$ (I,j))))"
using assms unfolding eliminate_entries_gen_zero_def by auto


lemma eliminate_entries_gen [simp]:
  assumes "i<(dim_row A)" "j<(dim_col A)" shows
  "eliminate_entries_gen mminus ttimes v A I J $$ (i, j) =
   (if i = I then A $$ (i,j) else mminus (A $$ (i,j)) (ttimes (v i) (A $$ (I,j))))"
using assms unfolding eliminate_entries_gen_def by auto

lemma dim_mat_impl [simp]:
  "dim_row (mat_impl x) = dim_row_impl x"
  "dim_col (mat_impl x) = dim_col_impl x"
  by (cases "Rep_mat_impl x";auto simp:mat_impl.rep_eq dim_row_def dim_col_def dim_row_impl.rep_eq dim_col_impl.rep_eq)+

lemma dim_eliminate_entries_i2 [simp]:
  "dim_row_impl (eliminate_entries_i2 z mm tt v m i) = dim_row_impl m"
  "dim_col_impl (eliminate_entries_i2 z mm tt v m i) = dim_col_impl m"
  by (transfer, auto)+

lemma tabulate_nth: "i < n \<Longrightarrow> IArray.tabulate (integer_of_nat n, f) !! i = f (integer_of_nat i)" 
  using of_fun_nth[of i n] by auto

lemma eliminate_entries_i2[code]:"eliminate_entries_gen_zero mm tt z v (mat_impl m) i j
   = (if i < dim_row_impl m 
     then mat_impl (eliminate_entries_i2 z mm tt v m (integer_of_nat i))
     else (Code.abort (STR ''index out of range in eliminate_entries'') 
       (\<lambda> _. eliminate_entries_gen_zero mm tt z v (mat_impl m) i j)))"
proof (cases "i < dim_row_impl m")
  case True
  hence id: "(i < dim_row_impl m) = True" by simp
  show ?thesis unfolding id if_True
  proof (standard;goal_cases)
    case (1 i j)
    have dims: "i < dim_row (mat_impl m)" "j < dim_col (mat_impl m)" using 1 by (auto simp:eliminate_entries_i2.rep_eq)
    then show ?case unfolding eliminate_entries_gen_zero[OF dims] using True
    proof(transfer, goal_cases)
      case (1 i m j ia v z mm tt)
      obtain nr nc M where m: "m = (nr,nc,M)" by (cases m) 
      note 1 = 1[unfolded m, simplified]
      have mk: "\<And> f. mk_mat nr nc f (i,j) = f (i,j)" 
         "\<And> f. mk_mat nr nc f (ia,j) = f (ia,j)" 
        using 1 unfolding mk_mat_def mk_vec_def by auto
      note of_fun = of_fun_nth[OF 1(2)] of_fun_nth[OF 1(3)] tabulate_nth[OF 1(2)] tabulate_nth[OF 1(3)]
      let ?c1 = "v (integer_of_nat i) = z" 
      show ?case
      proof (cases "?c1 \<or> i = ia")
        case True
        hence id: "(if ?c1 \<or> i = ia then x else y) = x" 
          "(if integer_of_nat i = integer_of_nat ia then x else if ?c1 then x else y) = x" for x y 
          by auto
        show ?thesis unfolding id m o_def Let_def split snd_conv mk of_fun by (auto simp: 1)
      next
        case False
        hence id: "?c1 = False " "(integer_of_nat i = integer_of_nat ia) = False" "(False \<or> i = ia) = False" 
          by (auto simp add: integer_of_nat_eq_of_nat)
        show ?thesis unfolding m o_def Let_def split snd_conv mk of_fun id if_False 
          by (auto simp: 1)
      qed
    qed  
  qed (auto simp:eliminate_entries_i2.rep_eq)
qed auto

end
