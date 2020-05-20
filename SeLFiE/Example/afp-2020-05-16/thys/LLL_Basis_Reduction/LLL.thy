(*
    Authors:    Jose Divasón
                Maximilian Haslbeck
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>The LLL Algorithm\<close>

text \<open>Soundness of the LLL algorithm is proven in four steps. 
  In the basic version, we do recompute the Gram-Schmidt ortogonal (GSO) basis 
  in every step. This basic version will have a full functional soundness proof, 
  i.e., termination and the property that the returned basis is reduced.
  Then in LLL-Number-Bounds we will strengthen the invariant and prove that
  all intermediate numbers stay polynomial in size.
  Moreover, in LLL-Impl we will refine the basic version, so that
  the GSO does not need to be recomputed in every step. 
  Finally, in LLL-Complexity, we develop an cost-annotated version
  of the refined algorithm and prove a polynomial upper bound on the 
  number of arithmetic operations.\<close> 


text \<open>This theory provides a basic implementation and a soundness proof of the LLL algorithm
      to compute a "short" vector in a lattice.\<close> 

theory LLL
  imports 
    Gram_Schmidt_2 
    Missing_Lemmas 
    Jordan_Normal_Form.Determinant 
    "Abstract-Rewriting.SN_Order_Carrier"
begin

subsection \<open>Core Definitions, Invariants, and Theorems for Basic Version\<close>

(* Note/TODO by Max Haslbeck:
  Up to here I refactored the code in Gram_Schmidt_2 and Gram_Schmidt_Int which now makes heavy
  use of locales. In the future I would also like to do this here (instead of using LLL_invariant
  everywhere). *)

locale LLL =
  fixes n :: nat (* n-dimensional vectors, *)
    and m :: nat (* number of vectors *)
    and fs_init :: "int vec list" (* initial basis *)
    and \<alpha> :: rat (* approximation factor *)

begin

sublocale vec_module "TYPE(int)" n.




abbreviation RAT where "RAT \<equiv> map (map_vec rat_of_int)" 
abbreviation SRAT where "SRAT xs \<equiv> set (RAT xs)" 
abbreviation Rn where "Rn \<equiv> carrier_vec n :: rat vec set" 

sublocale gs: gram_schmidt_fs n "RAT fs_init" .

abbreviation lin_indep where "lin_indep fs \<equiv> gs.lin_indpt_list (RAT fs)" 
abbreviation gso where "gso fs \<equiv> gram_schmidt_fs.gso n (RAT fs)"
abbreviation \<mu> where "\<mu> fs \<equiv> gram_schmidt_fs.\<mu> n (RAT fs)"

abbreviation reduced where "reduced fs \<equiv> gram_schmidt_fs.reduced n (RAT fs) \<alpha>" 
abbreviation weakly_reduced where "weakly_reduced fs \<equiv> gram_schmidt_fs.weakly_reduced n (RAT fs) \<alpha>" 
  
text \<open>lattice of initial basis\<close>
definition "L = lattice_of fs_init" 

text \<open>maximum squared norm of initial basis\<close>
definition "N = max_list (map (nat \<circ> sq_norm) fs_init)" 

text \<open>maximum absolute value in initial basis\<close>
definition "M = Max ({abs (fs_init ! i $ j) | i j. i < m \<and> j < n} \<union> {0})" 

text \<open>This is the core invariant which enables to prove functional correctness.\<close>

definition "\<mu>_small fs i = (\<forall> j < i. abs (\<mu> fs i j) \<le> 1/2)" 

definition LLL_invariant :: "bool \<Rightarrow> nat \<Rightarrow> int vec list \<Rightarrow> bool" where 
  "LLL_invariant upw i fs = ( 
    gs.lin_indpt_list (RAT fs) \<and> 
    lattice_of fs = L \<and>
    reduced fs i \<and>
    i \<le> m \<and> 
    length fs = m \<and>
    (upw \<or> \<mu>_small fs i)    
  )" 

lemma LLL_invD: assumes "LLL_invariant upw i fs"
  shows 
  "lin_indep fs" 
  "length (RAT fs) = m" 
  "set fs \<subseteq> carrier_vec n"
  "\<And> i. i < m \<Longrightarrow> fs ! i \<in> carrier_vec n" 
  "\<And> i. i < m \<Longrightarrow> gso fs i \<in> carrier_vec n" 
  "length fs = m"
  "lattice_of fs = L" 
  "weakly_reduced fs i"
  "i \<le> m"
  "reduced fs i" 
  "upw \<or> \<mu>_small fs i"
proof (atomize (full), goal_cases)
  case 1
  interpret gs': gram_schmidt_fs_lin_indpt n "RAT fs"
    by (standard) (use assms LLL_invariant_def gs.lin_indpt_list_def in auto)
  show ?case
    using assms gs'.fs_carrier gs'.f_carrier gs'.gso_carrier
    by (auto simp add: LLL_invariant_def gram_schmidt_fs.reduced_def)
qed

lemma LLL_invI: assumes  
  "set fs \<subseteq> carrier_vec n"
  "length fs = m"
  "lattice_of fs = L" 
  "i \<le> m"
  "lin_indep fs" 
  "reduced fs i" 
  "upw \<or> \<mu>_small fs i" 
shows "LLL_invariant upw i fs" 
  unfolding LLL_invariant_def Let_def split using assms by auto



end

locale fs_int' =
  fixes n m fs_init \<alpha> upw i fs 
  assumes LLL_inv: "LLL.LLL_invariant n m fs_init \<alpha> upw i fs"

sublocale fs_int' \<subseteq> fs_int_indpt
   using LLL_inv unfolding LLL.LLL_invariant_def by (unfold_locales) blast

context LLL
begin

lemma gso_cong: assumes "\<And> i. i \<le> x \<Longrightarrow> f1 ! i = f2 ! i"
   "x < length f1" "x < length f2" 
  shows "gso f1 x = gso f2 x"
  by (rule gs.gso_cong, insert assms, auto)
  
lemma \<mu>_cong: assumes "\<And> k. j < i \<Longrightarrow> k \<le> j \<Longrightarrow> f1 ! k = f2 ! k"
  and i: "i < length f1" "i < length f2" 
  and "j < i \<Longrightarrow> f1 ! i = f2 ! i" 
  shows "\<mu> f1 i j = \<mu> f2 i j"
  by (rule gs.\<mu>_cong, insert assms, auto)
    
definition reduction where "reduction = (4+\<alpha>)/(4*\<alpha>)"


definition d :: "int vec list \<Rightarrow> nat \<Rightarrow> int" where "d fs k = gs.Gramian_determinant fs k"
definition D :: "int vec list \<Rightarrow> nat" where "D fs = nat (\<Prod> i < m. d fs i)" 

definition "d\<mu> gs i j = int_of_rat (of_int (d gs (Suc j)) * \<mu> gs i j)" 

definition logD :: "int vec list \<Rightarrow> nat"
  where "logD fs = (if \<alpha> = 4/3 then (D fs) else nat (floor (log (1 / of_rat reduction) (D fs))))" 

definition LLL_measure :: "nat \<Rightarrow> int vec list \<Rightarrow> nat" where 
  "LLL_measure i fs = (2 * logD fs + m - i)" 

context
  fixes upw i fs
  assumes Linv: "LLL_invariant upw i fs"
begin

interpretation fs: fs_int' n m fs_init \<alpha> upw i fs
  by (standard) (use Linv in auto)

lemma Gramian_determinant:
  assumes k: "k \<le> m" 
shows "of_int (gs.Gramian_determinant fs k) = (\<Prod> j<k. sq_norm (gso fs j))" (is ?g1)
  "gs.Gramian_determinant fs k > 0" (is ?g2)
  using assms fs.Gramian_determinant LLL_invD[OF Linv]  by auto
   
lemma LLL_d_pos [intro]: assumes k: "k \<le> m" 
shows "d fs k > 0"
  unfolding d_def using fs.Gramian_determinant k LLL_invD[OF Linv] by auto

lemma LLL_d_Suc: assumes k: "k < m" 
shows "of_int (d fs (Suc k)) = sq_norm (gso fs k) * of_int (d fs k)" 
  using assms fs.fs_int_d_Suc  LLL_invD[OF Linv] unfolding fs.d_def d_def by auto

lemma LLL_D_pos:
  shows "D fs > 0"
  using fs.fs_int_D_pos LLL_invD[OF Linv] unfolding D_def fs.D_def fs.d_def d_def by auto

text \<open>Condition when we can increase the value of $i$\<close>

lemma increase_i:
  assumes i: "i < m" 
  and upw: "upw \<Longrightarrow> i = 0" 
  and red_i: "i \<noteq> 0 \<Longrightarrow> sq_norm (gso fs (i - 1)) \<le> \<alpha> * sq_norm (gso fs i)"
shows "LLL_invariant True (Suc i) fs" "LLL_measure i fs > LLL_measure (Suc i) fs" 
proof -
  note inv = LLL_invD[OF Linv]
  from inv(8,10) have red: "weakly_reduced fs i" 
    and sred: "reduced fs i" by (auto)
  from red red_i i have red: "weakly_reduced fs (Suc i)" 
    unfolding gram_schmidt_fs.weakly_reduced_def
    by (intro allI impI, rename_tac ii, case_tac "Suc ii = i", auto)
  from inv(11) upw have sred_i: "\<And> j. j < i \<Longrightarrow> \<bar>\<mu> fs i j\<bar> \<le> 1 / 2" 
    unfolding \<mu>_small_def by auto
  from sred sred_i have sred: "reduced fs (Suc i)"
    unfolding gram_schmidt_fs.reduced_def
    by (intro conjI[OF red] allI impI, rename_tac ii j, case_tac "ii = i", auto)
  show "LLL_invariant True (Suc i) fs" 
    by (intro LLL_invI, insert inv red sred i, auto)
  show "LLL_measure i fs > LLL_measure (Suc i) fs" unfolding LLL_measure_def using i by auto
qed

end

text \<open>Standard addition step which makes $\mu_{i,j}$ small\<close>

definition "\<mu>_small_row i fs j = (\<forall> j'. j \<le> j' \<longrightarrow> j' < i \<longrightarrow> abs (\<mu> fs i j') \<le> inverse 2)"

lemma basis_reduction_add_row_main: assumes Linv: "LLL_invariant True i fs"
  and i: "i < m"  and j: "j < i" 
  and fs': "fs' = fs[ i := fs ! i - c \<cdot>\<^sub>v fs ! j]" 
shows "LLL_invariant True i fs'"
  "c = round (\<mu> fs i j) \<Longrightarrow> \<mu>_small_row i fs (Suc j) \<Longrightarrow> \<mu>_small_row i fs' j" (* mu-value at position i j gets small *)
  "LLL_measure i fs' = LLL_measure i fs" 
  (* new values of gso: no change *)
  "\<And> i. i < m \<Longrightarrow> gso fs' i = gso fs i" 
  (* new values of mu *)
  "\<And> i' j'. i' < m \<Longrightarrow> j' < m \<Longrightarrow>       
     \<mu> fs' i' j' = (if i' = i \<and> j' \<le> j then \<mu> fs i j' - of_int c * \<mu> fs j j' else \<mu> fs i' j')"
  (* new values of d *)
  "\<And> ii. ii \<le> m \<Longrightarrow> d fs' ii = d fs ii" 
proof -
  define bnd :: rat where bnd: "bnd = 4 ^ (m - 1 - Suc j) * of_nat (N ^ (m - 1) * m)" 
  define M where "M = map (\<lambda>i. map (\<mu> fs i) [0..<m]) [0..<m]"
  note inv = LLL_invD[OF Linv]
  note Gr = inv(1)
  have ji: "j \<le> i" "j < m" and jstrict: "j < i" 
    and add: "set fs \<subseteq> carrier_vec n" "i < length fs" "j < length fs" "i \<noteq> j" 
    and len: "length fs = m" and red: "weakly_reduced fs i"
    and indep: "lin_indep fs" 
    using inv j i by auto 
  let ?R = rat_of_int
  let ?RV = "map_vec ?R"   
  from inv i j
  have Fij: "fs ! i \<in> carrier_vec n" "fs ! j \<in> carrier_vec n" by auto
  let ?x = "fs ! i - c \<cdot>\<^sub>v fs ! j"  
  let ?g = "gso fs"
  let ?g' = "gso fs'"
  let ?mu = "\<mu> fs"
  let ?mu' = "\<mu> fs'"
  from inv j i 
  have Fi:"\<And> i. i < length (RAT fs) \<Longrightarrow> (RAT fs) ! i \<in> carrier_vec n"
    and gs_carr: "?g j \<in> carrier_vec n"
                "?g i \<in> carrier_vec n"
                "\<And> i. i < j \<Longrightarrow> ?g i \<in> carrier_vec n"
                "\<And> j. j < i \<Longrightarrow> ?g j \<in> carrier_vec n" 
    and len': "length (RAT fs) = m"
    and add':"set (map ?RV fs) \<subseteq> carrier_vec n"
    by auto 
  have RAT_F1: "RAT fs' = (RAT fs)[i := (RAT fs) ! i - ?R c \<cdot>\<^sub>v (RAT fs) ! j]" 
    unfolding fs'
  proof (rule nth_equalityI[rule_format], goal_cases)
    case (2 k)
    show ?case 
    proof (cases "k = i")
      case False
      thus ?thesis using 2 by auto
    next
      case True
      hence "?thesis = (?RV (fs ! i - c \<cdot>\<^sub>v fs ! j) =
          ?RV (fs ! i) - ?R c \<cdot>\<^sub>v ?RV (fs ! j))" 
        using 2 add by auto
      also have "\<dots>" by (rule eq_vecI, insert Fij, auto)
      finally show ?thesis by simp
    qed
  qed auto
  hence RAT_F1_i:"RAT fs' ! i = (RAT fs) ! i - ?R c \<cdot>\<^sub>v (RAT fs) ! j" (is "_ = _ - ?mui")
    using i len by auto
  have uminus: "fs ! i - c \<cdot>\<^sub>v fs ! j = fs ! i + -c \<cdot>\<^sub>v fs ! j" 
    by (subst minus_add_uminus_vec, insert Fij, auto)
  have "lattice_of fs' = lattice_of fs" unfolding fs' uminus
    by (rule lattice_of_add[OF add, of _ "- c"], auto)
  with inv have lattice: "lattice_of fs' = L" by auto
  from add len
  have "k < length fs \<Longrightarrow> \<not> k \<noteq> i \<Longrightarrow> fs' ! k \<in> carrier_vec n" for k
    unfolding fs'
    by (metis (no_types, lifting) nth_list_update nth_mem subset_eq carrier_dim_vec index_minus_vec(2) 
        index_smult_vec(2))
  hence "k < length fs \<Longrightarrow> fs' ! k \<in> carrier_vec n" for k
    unfolding fs' using add len by (cases "k \<noteq> i",auto)
  with len have F1: "set fs' \<subseteq> carrier_vec n" "length fs' = m" unfolding fs' by (auto simp: set_conv_nth)
  hence F1': "length (RAT fs') = m" "SRAT fs' \<subseteq> Rn" by auto
  from indep have dist: "distinct (RAT fs)" by (auto simp: gs.lin_indpt_list_def)
  have Fij': "(RAT fs) ! i \<in> Rn" "(RAT fs) ! j \<in> Rn" using add'[unfolded set_conv_nth] i \<open>j < m\<close> len by auto
  have uminus': "(RAT fs) ! i - ?R c \<cdot>\<^sub>v (RAT fs) ! j = (RAT fs) ! i + - ?R c \<cdot>\<^sub>v (RAT fs) ! j" 
    by (subst minus_add_uminus_vec[where n = n], insert Fij', auto) 
  have span_F_F1: "gs.span (SRAT fs) = gs.span (SRAT fs')" unfolding RAT_F1 uminus' 
    by (rule gs.add_vec_span, insert len add, auto)
  have **: "?RV (fs ! i) + - ?R c \<cdot>\<^sub>v (RAT fs) ! j =  ?RV (fs ! i - c \<cdot>\<^sub>v fs ! j)"
    by (rule eq_vecI, insert Fij len i j, auto)
  from i j len have "j < length (RAT fs)" "i < length (RAT fs)" "i \<noteq> j" by auto
  from gs.lin_indpt_list_add_vec[OF this indep, of "- of_int c"]
  have "gs.lin_indpt_list ((RAT fs) [i := (RAT fs) ! i + - ?R c \<cdot>\<^sub>v (RAT fs) ! j])" (is "gs.lin_indpt_list ?F1") .
  also have "?F1 = RAT fs'" unfolding fs' using i len Fij' **
    by (auto simp: map_update)
  finally have indep_F1: "lin_indep fs'" .
  have conn1: "set (RAT fs) \<subseteq> carrier_vec n"  "length (RAT fs) = m" "distinct (RAT fs)"
    "gs.lin_indpt (set (RAT fs))"
    using inv unfolding gs.lin_indpt_list_def by auto
  have conn2: "set (RAT fs') \<subseteq> carrier_vec n"  "length (RAT fs') = m" "distinct (RAT fs')"
    "gs.lin_indpt (set (RAT fs'))"
    using indep_F1 F1' unfolding gs.lin_indpt_list_def by auto
  interpret gs1: gram_schmidt_fs_lin_indpt n "RAT fs"
    by (standard) (use LLL_invD[OF assms(1)] gs.lin_indpt_list_def in auto)
  interpret gs2: gram_schmidt_fs_lin_indpt n "RAT fs'"
    by (standard) (use indep_F1 F1' gs.lin_indpt_list_def in auto)
  let ?G = "map ?g [0 ..< m]" 
  let ?G' = "map ?g' [0 ..< m]" 
  from gs1.span_gso gs2.span_gso gs1.gso_carrier gs2.gso_carrier conn1 conn2 span_F_F1 len 
  have span_G_G1: "gs.span (set ?G) = gs.span (set ?G')"
   and lenG: "length ?G = m" 
   and Gi: "i < length ?G \<Longrightarrow> ?G ! i \<in> Rn"
   and G1i: "i < length ?G' \<Longrightarrow> ?G' ! i \<in> Rn" for i
    by auto
  have eq: "x \<noteq> i \<Longrightarrow> RAT fs' ! x = (RAT fs) ! x" for x unfolding RAT_F1 by auto
  hence eq_part: "x < i \<Longrightarrow> ?g' x = ?g x" for x
    by (intro gs.gso_cong, insert len, auto)
  have G: "i < m \<Longrightarrow> (RAT fs) ! i \<in> Rn"
       "i < m \<Longrightarrow> fs ! i \<in> carrier_vec n" for i by(insert add len', auto)
  note carr1[intro] = this[OF i] this[OF ji(2)]
  have "x < m \<Longrightarrow> ?g x \<in> Rn" 
       "x < m \<Longrightarrow> ?g' x \<in> Rn"
       "x < m \<Longrightarrow> dim_vec (gso fs x) = n"
       "x < m \<Longrightarrow> dim_vec (gso fs' x) = n"
       for x using inv G1i by (auto simp:o_def Gi G1i)
  hence carr2[intro!]:"?g i \<in> Rn" "?g' i \<in> Rn"
                 "?g ` {0..<i} \<subseteq> Rn"
                 "?g ` {0..<Suc i} \<subseteq> Rn" using i by auto
  have F1_RV: "?RV (fs' ! i) = RAT fs' ! i" using i F1 by auto
  have F_RV: "?RV (fs ! i) = (RAT fs) ! i" using i len by auto
  from eq_part 
  have span_G1_G: "gs.span (?g' ` {0..<i}) = gs.span (?g ` {0..<i})" (is "?ls = ?rs")
    apply(intro cong[OF refl[of "gs.span"]],rule image_cong[OF refl]) using eq by auto
  have "(RAT fs') ! i - ?g' i = ((RAT fs) ! i - ?g' i) - ?mui"
    unfolding RAT_F1_i using carr1 carr2
    by (intro eq_vecI, auto)
  hence in1:"((RAT fs) ! i - ?g' i) - ?mui \<in> ?rs"
    using gs2.oc_projection_exist[of i] conn2 i unfolding span_G1_G by auto
  from \<open>j < i\<close> have Gj_mem: "(RAT fs) ! j \<in> (\<lambda> x. ((RAT fs) ! x)) ` {0 ..< i}" by auto  
  have id1: "set (take i (RAT fs)) = (\<lambda>x. ?RV (fs ! x)) ` {0..<i}"
    using \<open>i \<le> m\<close> len
    by (subst nth_image[symmetric], force+)
  have "(RAT fs) ! j \<in> ?rs \<longleftrightarrow> (RAT fs) ! j \<in> gs.span ((\<lambda>x. ?RV (fs ! x)) ` {0..<i})"
    using gs1.partial_span  \<open>i \<le> m\<close> id1 inv by auto
  also have "(\<lambda>x. ?RV (fs ! x)) ` {0..<i} = (\<lambda>x. ((RAT fs) ! x)) ` {0..<i}" using \<open>i < m\<close> len by force
  also have "(RAT fs) ! j \<in> gs.span \<dots>"
    by (rule gs.span_mem[OF _ Gj_mem], insert \<open>i < m\<close> G, auto)
  finally have "(RAT fs) ! j \<in> ?rs" .
  hence in2:"?mui \<in> ?rs"
    apply(intro gs.prod_in_span) by force+
  have ineq:"((RAT fs) ! i - ?g' i) + ?mui - ?mui = ((RAT fs) ! i - ?g' i)"
    using carr1 carr2 by (intro eq_vecI, auto)
  have cong': "A = B \<Longrightarrow> A \<in> C \<Longrightarrow> B \<in> C" for A B :: "'a vec" and C by auto
  have *: "?g ` {0..<i} \<subseteq> Rn" by auto
  have in_span: "(RAT fs) ! i - ?g' i \<in> ?rs"
    by (rule cong'[OF eq_vecI gs.span_add1[OF * in1 in2,unfolded ineq]], insert carr1 carr2, auto)
  { 
    fix x assume x:"x < i" hence "x < m" "i \<noteq> x" using i by auto
    from gs2.orthogonal this inv assms
    have "?g' i \<bullet> ?g' x = 0" by auto
  }
  hence G1_G: "?g' i = ?g i"
    by (intro gs1.oc_projection_unique) (use inv i eq_part in_span in auto)
  show eq_fs:"x < m \<Longrightarrow> ?g' x = ?g x"
    for x proof(induct x rule:nat_less_induct[rule_format])
    case (1 x)
    hence ind: "m < x \<Longrightarrow> ?g' m = ?g m"
       for m by auto
    { assume "x > i"
      hence ?case unfolding gs2.gso.simps[of x] gs1.gso.simps[of x] unfolding gs1.\<mu>.simps gs2.\<mu>.simps
        using ind eq by (auto intro: cong[OF _ cong[OF refl[of "gs.sumlist"]]])
    } note eq_rest = this
    show ?case by (rule linorder_class.linorder_cases[of x i],insert G1_G eq_part eq_rest,auto)
  qed
  hence Hs:"?G' = ?G" by (auto simp:o_def)
  have red: "weakly_reduced fs' i" using red using eq_fs \<open>i < m\<close>
    unfolding gram_schmidt_fs.weakly_reduced_def by simp
  let ?Mi = "M ! i ! j"  
  have Gjn: "dim_vec (fs ! j) = n" using Fij(2) carrier_vecD by blast
  define E where "E = addrow_mat m (- ?R c) i j"
  define M' where "M' = gs1.M m"
  define N' where "N' = gs2.M m"
  have E: "E \<in> carrier_mat m m" unfolding E_def by simp
  have M: "M' \<in> carrier_mat m m" unfolding gs1.M_def M'_def by auto
  have N: "N' \<in> carrier_mat m m" unfolding gs2.M_def N'_def by auto
  let ?mat = "mat_of_rows n" 
  let ?GsM = "?mat ?G" 
  have Gs: "?GsM \<in> carrier_mat m n" by auto
  hence GsT: "?GsM\<^sup>T \<in> carrier_mat n m" by auto
  have Gnn: "?mat (RAT fs) \<in> carrier_mat m n" unfolding mat_of_rows_def using len by auto
  have "?mat (RAT fs') = addrow (- ?R c) i j (?mat (RAT fs))" 
    unfolding RAT_F1 by (rule eq_matI, insert Gjn ji(2), auto simp: len mat_of_rows_def)
  also have "\<dots> = E * ?mat (RAT fs)" unfolding E_def
    by (rule addrow_mat, insert j i, auto simp: mat_of_rows_def len)
  finally have HEG: "?mat (RAT fs') = E * ?mat (RAT fs)" . (* lemma 16.12(i), part 1 *)
  have "(E * M') * ?mat ?G = E * (M' * ?mat ?G)" 
    by (rule assoc_mult_mat[OF E M Gs])
  also have "M' * ?GsM = ?mat (RAT fs)" using gs1.matrix_equality conn1 M'_def by simp
  also have "E * \<dots> = ?mat (RAT fs')" unfolding HEG ..
  also have "\<dots> = N' * ?mat ?G'" using gs2.matrix_equality conn2 unfolding N'_def by simp
  also have "?mat ?G' = ?GsM" unfolding Hs ..
  finally have "(E * M') * ?GsM = N' * ?GsM" .
  from arg_cong[OF this, of "\<lambda> x. x * ?GsM\<^sup>T"] E M N 
  have EMN: "(E * M') * (?GsM * ?GsM\<^sup>T) = N' * (?GsM * ?GsM\<^sup>T)" 
    by (subst (1 2) assoc_mult_mat[OF _ Gs GsT, of _ m, symmetric], auto)
  have "det (?GsM * ?GsM\<^sup>T) = gs.Gramian_determinant ?G m" 
    unfolding gs.Gramian_determinant_def
    by (subst gs.Gramian_matrix_alt_def, auto simp: Let_def)
  also have "\<dots> > 0" 
  proof -
    have 1: "gs.lin_indpt_list ?G"
      using conn1 gs1.orthogonal_gso gs1.gso_carrier by (intro gs.orthogonal_imp_lin_indpt_list) (auto)
    interpret G: gram_schmidt_fs_lin_indpt n ?G
      by  (standard) (use 1 gs.lin_indpt_list_def in auto)
    show ?thesis
      by (intro G.Gramian_determinant) auto
  qed
  finally have "det (?GsM * ?GsM\<^sup>T) \<noteq> 0" by simp
  from vec_space.det_nonzero_congruence[OF EMN this _ _ N] Gs E M
  have EMN: "E * M' = N'" by auto (* lemma 16.12(i), part 2 *) 
  from inv have sred: "reduced fs i" by auto
  {
    fix i' j'
    assume ij: "i' < m" "j' < m" and choice: "i' \<noteq> i \<or> j < j'" 
    have "?mu' i' j' 
      = N' $$ (i',j')" using ij F1 unfolding N'_def gs2.M_def by auto
    also have "\<dots> = addrow (- ?R c) i j M' $$ (i',j')" unfolding EMN[symmetric] E_def
      by (subst addrow_mat[OF M], insert ji, auto)
    also have "\<dots> = (if i = i' then - ?R c * M' $$ (j, j') + M' $$ (i', j') else M' $$ (i', j'))" 
      by (rule index_mat_addrow, insert ij M, auto)
    also have "\<dots> = M' $$ (i', j')"
    proof (cases "i = i'")
      case True
      with choice have jj: "j < j'" by auto
      have "M' $$ (j, j') = ?mu j j'" 
        using ij ji len unfolding M'_def gs1.M_def by auto
      also have "\<dots> = 0" unfolding gs1.\<mu>.simps using jj by auto
      finally show ?thesis using True by auto
    qed auto
    also have "\<dots> = ?mu i' j'"
      using ij len unfolding M'_def gs1.M_def by auto
    also note calculation
  } note mu_no_change = this
  {
    fix j'
    assume jj': "j' \<le> j" with j i have j': "j' < m" by auto
    have "?mu' i j' 
      = N' $$ (i,j')" using jj' j i F1 unfolding N'_def gs2.M_def by auto
    also have "\<dots> = addrow (- ?R c) i j M' $$ (i,j')" unfolding EMN[symmetric] E_def
      by (subst addrow_mat[OF M], insert ji, auto)
    also have "\<dots> = - ?R c * M' $$ (j, j') + M' $$ (i, j')" 
      by (rule index_mat_addrow, insert j' i M, auto)
    also have "\<dots> = M' $$ (i, j') - ?R c * M' $$ (j, j')" by simp
    also have "M' $$ (i, j') = ?mu i j'"
      using i j' len unfolding M'_def gs1.M_def by auto
    also have "M' $$ (j, j') = ?mu j j'" 
      using i j j' len unfolding M'_def gs1.M_def by auto
    finally have "?mu' i j' = ?mu i j' - ?R c * ?mu j j'" by auto
  } note mu_change = this  
  show mu_update: "i' < m \<Longrightarrow> j' < m \<Longrightarrow> 
    ?mu' i' j' = (if i' = i \<and> j' \<le> j then ?mu i j' - ?R c * ?mu j j' else ?mu i' j')" 
    for i' j' using mu_change[of j'] mu_no_change[of i' j']
    by auto
  have sred: "reduced fs' i"
    unfolding gram_schmidt_fs.reduced_def 
  proof (intro conjI[OF red] impI allI, goal_cases)
    case (1 i' j)
    with mu_no_change[of i' j] sred[unfolded gram_schmidt_fs.reduced_def, THEN conjunct2, rule_format, of i' j] i 
    show ?case by auto
  qed

  have mudiff:"?mu i j - of_int c = ?mu' i j"
    by (subst mu_change, auto simp: gs1.\<mu>.simps)
  have lin_indpt_list_fs: "gs.lin_indpt_list (RAT fs')"
    unfolding gs.lin_indpt_list_def using conn2 by auto
  { 
    assume c: "c = round (\<mu> fs i j)" 
    assume mu_small: "\<mu>_small_row i fs (Suc j)" 
    have small: "abs (?mu i j - of_int c) \<le> inverse 2" unfolding j c
      using of_int_round_abs_le by (auto simp add: abs_minus_commute)
    from this[unfolded mudiff] 
    have mu'_2: "abs (?mu' i j) \<le> inverse 2" .

    show "\<mu>_small_row i fs' j" 
      unfolding \<mu>_small_row_def 
    proof (intro allI, goal_cases)
      case (1 j')
      show ?case using mu'_2 mu_small[unfolded \<mu>_small_row_def, rule_format, of j'] 
        by (cases "j' > j", insert mu_update[of i j'] i, auto)
    qed
  }

  show Linv': "LLL_invariant True i fs'" 
    by (intro LLL_invI[OF F1 lattice \<open>i \<le> m\<close> lin_indpt_list_fs sred], auto)
  {
    fix i
    assume i: "i \<le> m"
    have "rat_of_int (d fs' i) = of_int (d fs i)" 
      unfolding d_def Gramian_determinant(1)[OF Linv i] Gramian_determinant(1)[OF Linv' i]
      by (rule prod.cong[OF refl], subst eq_fs, insert i, auto)
    thus "d fs' i = d fs i" by simp
  } note d = this 
  have D: "D fs' = D fs" 
    unfolding D_def
    by (rule arg_cong[of _ _ nat], rule prod.cong[OF refl], auto simp: d)
  show "LLL_measure i fs' = LLL_measure i fs" 
    unfolding LLL_measure_def logD_def D ..
qed

text \<open>Addition step which can be skipped since $\mu$-value is already small\<close>

lemma basis_reduction_add_row_main_0: assumes Linv: "LLL_invariant True i fs"
  and i: "i < m"  and j: "j < i" 
  and 0: "round (\<mu> fs i j) = 0" 
  and mu_small: "\<mu>_small_row i fs (Suc j)"
shows "\<mu>_small_row i fs j" (is ?g1)
proof -
  note inv = LLL_invD[OF Linv]
  from inv(5)[OF i] inv(5)[of j] i j
  have id: "fs[i := fs ! i - 0 \<cdot>\<^sub>v fs ! j] = fs" 
    by (intro nth_equalityI, insert inv i, auto)
  show ?g1
    using basis_reduction_add_row_main[OF Linv i j _, of fs] 0 id mu_small by auto
qed

lemma \<mu>_small_row_refl: "\<mu>_small_row i fs i" 
  unfolding \<mu>_small_row_def by auto

lemma basis_reduction_add_row_done: assumes Linv: "LLL_invariant True i fs"
  and i: "i < m" 
  and mu_small: "\<mu>_small_row i fs 0" 
shows "LLL_invariant False i fs"
proof -
  note inv = LLL_invD[OF Linv]
  from mu_small 
  have mu_small: "\<mu>_small fs i" unfolding \<mu>_small_row_def \<mu>_small_def by auto
  show ?thesis
    using i mu_small by (intro LLL_invI[OF inv(3,6,7,9,1,10)], auto)
qed     

(* lemma 16.16 (ii), one case *)
lemma d_swap_unchanged: assumes len: "length F1 = m" 
  and i0: "i \<noteq> 0" and i: "i < m" and ki: "k \<noteq> i" and km: "k \<le> m"   
  and swap: "F2 = F1[i := F1 ! (i - 1), i - 1 := F1 ! i]"
shows "d F1 k = d F2 k"
proof -
  let ?F1_M = "mat k n (\<lambda>(i, y). F1 ! i $ y)" 
  let ?F2_M = "mat k n (\<lambda>(i, y). F2 ! i $ y)" 
  have "\<exists> P. P \<in> carrier_mat k k \<and> det P \<in> {-1, 1} \<and> ?F2_M = P * ?F1_M" 
  proof cases
    assume ki: "k < i" 
    hence H: "?F2_M = ?F1_M" unfolding swap
      by (intro eq_matI, auto)
    let ?P = "1\<^sub>m k" 
    have "?P \<in> carrier_mat k k" "det ?P \<in> {-1, 1}" "?F2_M = ?P * ?F1_M" unfolding H by auto
    thus ?thesis by blast
  next
    assume "\<not> k < i" 
    with ki have ki: "k > i" by auto
    let ?P = "swaprows_mat k i (i - 1)" 
    from i0 ki have neq: "i \<noteq> i - 1" and kmi: "i - 1 < k" by auto
    have *: "?P \<in> carrier_mat k k" "det ?P \<in> {-1, 1}" using det_swaprows_mat[OF ki kmi neq] ki by auto
    from i len have iH: "i < length F1" "i - 1 < length F1" by auto 
    have "?P * ?F1_M = swaprows i (i - 1) ?F1_M" 
      by (subst swaprows_mat[OF _ ki kmi], auto)
    also have "\<dots> = ?F2_M" unfolding swap
      by (intro eq_matI, rename_tac ii jj, 
          case_tac "ii = i", (insert iH, simp add: nth_list_update)[1],
          case_tac "ii = i - 1", insert iH neq ki, auto simp: nth_list_update)
    finally show ?thesis using * by metis
  qed
  then obtain P where P: "P \<in> carrier_mat k k" and detP: "det P \<in> {-1, 1}" and H': "?F2_M = P * ?F1_M" by auto
  have "d F2 k = det (gs.Gramian_matrix F2 k)" 
    unfolding d_def gs.Gramian_determinant_def by simp
  also have "\<dots> = det (?F2_M * ?F2_M\<^sup>T)" unfolding gs.Gramian_matrix_def Let_def by simp
  also have "?F2_M * ?F2_M\<^sup>T = ?F2_M * (?F1_M\<^sup>T * P\<^sup>T)" unfolding H'
    by (subst transpose_mult[OF P], auto)
  also have "\<dots> = P * (?F1_M * (?F1_M\<^sup>T * P\<^sup>T))" unfolding H' 
    by (subst assoc_mult_mat[OF P], auto)
  also have "det \<dots> = det P * det (?F1_M * (?F1_M\<^sup>T * P\<^sup>T))" 
    by (rule det_mult[OF P], insert P, auto)
  also have "?F1_M * (?F1_M\<^sup>T * P\<^sup>T) = (?F1_M * ?F1_M\<^sup>T) * P\<^sup>T" 
    by (subst assoc_mult_mat, insert P, auto)
  also have "det \<dots> = det (?F1_M * ?F1_M\<^sup>T) * det P" 
    by (subst det_mult, insert P, auto simp: det_transpose)
  also have "det (?F1_M * ?F1_M\<^sup>T) = det (gs.Gramian_matrix F1 k)" unfolding gs.Gramian_matrix_def Let_def by simp
  also have "\<dots> = d F1 k" 
    unfolding d_def gs.Gramian_determinant_def by simp
  finally have "d F2 k = (det P * det P) * d F1 k" by simp
  also have "det P * det P = 1" using detP by auto
  finally show "d F1 k = d F2 k" by simp
qed

definition base where "base = real_of_rat ((4 * \<alpha>) / (4 + \<alpha>))" 

definition g_bound :: "int vec list \<Rightarrow> bool" where 
  "g_bound fs = (\<forall> i < m. sq_norm (gso fs i) \<le> of_nat N)" 

end

locale LLL_with_assms = LLL + 
  assumes \<alpha>: "\<alpha> \<ge> 4/3"
    and lin_dep: "lin_indep fs_init" 
    and len: "length fs_init = m" 
begin
lemma \<alpha>0: "\<alpha> > 0" "\<alpha> \<noteq> 0" 
  using \<alpha> by auto

lemma fs_init: "set fs_init \<subseteq> carrier_vec n" 
  using lin_dep[unfolded gs.lin_indpt_list_def] by auto


lemma reduction: "0 < reduction" "reduction \<le> 1" 
  "\<alpha> > 4/3 \<Longrightarrow> reduction < 1" 
  "\<alpha> = 4/3 \<Longrightarrow> reduction = 1" 
  using \<alpha> unfolding reduction_def by auto

lemma base: "\<alpha> > 4/3 \<Longrightarrow> base > 1" using reduction(1,3) unfolding reduction_def base_def by auto

lemma basis_reduction_swap_main: assumes Linv: "LLL_invariant False i fs"
  and i: "i < m"
  and i0: "i \<noteq> 0" 
  and norm_ineq: "sq_norm (gso fs (i - 1)) > \<alpha> * sq_norm (gso fs i)" 
  and fs'_def: "fs' = fs[i := fs ! (i - 1), i - 1 := fs ! i]" 
shows "LLL_invariant False (i - 1) fs'" 
  and "LLL_measure i fs > LLL_measure (i - 1) fs'" 
  (* new values of gso *)
  and "\<And> k. k < m \<Longrightarrow> gso fs' k = (if k = i - 1 then
         gso fs i + \<mu> fs i (i - 1) \<cdot>\<^sub>v gso fs (i - 1) 
      else if k = i then
         gso fs (i - 1) - (RAT fs ! (i - 1) \<bullet> gso fs' (i - 1) / sq_norm (gso fs' (i - 1))) \<cdot>\<^sub>v gso fs' (i - 1)
      else gso fs k)" (is "\<And> k. _ \<Longrightarrow> _ = ?newg k")
  (* new values of norms of gso *)
  and "\<And> k. k < m \<Longrightarrow> sq_norm (gso fs' k) = (if k = i - 1 then
          sq_norm (gso fs i) + (\<mu> fs i (i - 1) * \<mu> fs i (i - 1)) * sq_norm (gso fs (i - 1))
      else if k = i then
         sq_norm (gso fs i) * sq_norm (gso fs (i - 1)) / sq_norm (gso fs' (i - 1))
      else sq_norm (gso fs k))" (is "\<And> k. _ \<Longrightarrow> _ = ?new_norm k")
  (* new values of \<mu>-values *)
  and "\<And> ii j. ii < m \<Longrightarrow> j < ii \<Longrightarrow> \<mu> fs' ii j = (
        if ii = i - 1 then 
           \<mu> fs i j
        else if ii = i then 
          if j = i - 1 then 
             \<mu> fs i (i - 1) * sq_norm (gso fs (i - 1)) / sq_norm (gso fs' (i - 1))
          else 
             \<mu> fs (i - 1) j
        else if ii > i \<and> j = i then
           \<mu> fs ii (i - 1) - \<mu> fs i (i - 1) * \<mu> fs ii i
        else if ii > i \<and> j = i - 1 then 
           \<mu> fs ii (i - 1) * \<mu> fs' i (i - 1) + \<mu> fs ii i * sq_norm (gso fs i) / sq_norm (gso fs' (i - 1))
        else \<mu> fs ii j)" (is "\<And> ii j. _ \<Longrightarrow> _ \<Longrightarrow> _ = ?new_mu ii j")
  (* new d-values *)
  and "\<And> ii. ii \<le> m \<Longrightarrow> of_int (d fs' ii) = (if ii = i then 
       sq_norm (gso fs' (i - 1)) / sq_norm (gso fs (i - 1)) * of_int (d fs i)
       else of_int (d fs ii))" 
proof -
  note inv = LLL_invD[OF Linv]
  interpret fs: fs_int' n m fs_init \<alpha> False i fs
    by (standard) (use Linv in auto)
  let ?mu1 = "\<mu> fs" 
  let ?mu2 = "\<mu> fs'" 
  let ?g1 = "gso fs" 
  let ?g2 = "gso fs'" 
  from inv(11)[unfolded \<mu>_small_def]
  have mu_F1_i: "\<And> j. j<i \<Longrightarrow> \<bar>?mu1 i j\<bar> \<le> 1 / 2" by auto
  from mu_F1_i[of "i-1"] have m12: "\<bar>?mu1 i (i - 1)\<bar> \<le> inverse 2" using i0
    by auto
  note d = d_def  
  note Gd = Gramian_determinant(1)
  note Gd12 = Gd[OF Linv]
  let ?x = "?g1 (i - 1)" let ?y = "?g1 i" 
  let ?cond = "\<alpha> * sq_norm ?y < sq_norm ?x" 
  from inv have red: "weakly_reduced fs i" 
    and len: "length fs = m" and HC: "set fs \<subseteq> carrier_vec n" 
    and L: "lattice_of fs = L" 
    using i by auto 
  from i0 inv i have swap: "set fs \<subseteq> carrier_vec n" "i < length fs" "i - 1 < length fs" "i \<noteq> i - 1" 
    unfolding Let_def by auto
  have RAT_fs': "RAT fs' = (RAT fs)[i := (RAT fs) ! (i - 1), i - 1 := (RAT fs) ! i]" 
    unfolding fs'_def using swap by (intro nth_equalityI, auto simp: nth_list_update)
  have span': "gs.span (SRAT fs) = gs.span (SRAT fs')" unfolding fs'_def
    by (rule arg_cong[of _ _ gs.span], insert swap, auto)
  have lfs': "lattice_of fs' = lattice_of fs" unfolding fs'_def
    by (rule lattice_of_swap[OF swap refl])
  with inv have lattice: "lattice_of fs' = L" by auto
  have len': "length fs' = m" using inv unfolding fs'_def by auto
  have fs': "set fs' \<subseteq> carrier_vec n" using swap unfolding fs'_def set_conv_nth
    by (auto, rename_tac k, case_tac "k = i", force, case_tac "k = i - 1", auto)
  let ?rv = "map_vec rat_of_int" 
  from inv(1) have indepH: "lin_indep fs" .
  from i i0 len have "i < length (RAT fs)" "i - 1 < length (RAT fs)" by auto
  with distinct_swap[OF this] len have "distinct (RAT fs') = distinct (RAT fs)" unfolding RAT_fs'
    by (auto simp: map_update)
  with len' fs' span' indepH have indepH': "lin_indep fs'" unfolding fs'_def using i i0
    by (auto simp: gs.lin_indpt_list_def)
  have lenR': "length (RAT fs') = m" using len' by auto
  have conn1: "set (RAT fs) \<subseteq> carrier_vec n"  "length (RAT fs) = m" "distinct (RAT fs)"
    "gs.lin_indpt (set (RAT fs))"
    using inv unfolding gs.lin_indpt_list_def by auto
  have conn2: "set (RAT fs') \<subseteq> carrier_vec n"  "length (RAT fs') = m" "distinct (RAT fs')"
    "gs.lin_indpt (set (RAT fs'))"
    using indepH' lenR'  unfolding gs.lin_indpt_list_def by auto
  interpret gs2: gram_schmidt_fs_lin_indpt n "RAT fs'"
    by (standard) (use indepH' lenR' gs.lin_indpt_list_def in auto)
  have fs'_fs: "k < i - 1 \<Longrightarrow> fs' ! k = fs ! k" for k unfolding fs'_def by auto
  { 
    fix k
    assume ki: "k < i - 1" 
    with i have kn: "k < m" by simp
    have "?g2 k = ?g1 k" 
      by (rule gs.gso_cong, insert ki kn len, auto simp: fs'_def)
  } note G2_G = this
  have take_eq: "take (Suc i - 1 - 1) fs' = take (Suc i - 1 - 1) fs" 
    by (intro nth_equalityI, insert len len' i swap(2-), auto intro!: fs'_fs) 
  from inv have "weakly_reduced fs i" by auto
  hence "weakly_reduced fs (i - 1)" unfolding gram_schmidt_fs.weakly_reduced_def by auto
  hence red: "weakly_reduced fs' (i - 1)"
    unfolding gram_schmidt_fs.weakly_reduced_def using i G2_G by simp
  have i1n: "i - 1 < m" using i by auto
  let ?R = rat_of_int
  let ?RV = "map_vec ?R"  
  let ?f1 = "\<lambda> i. RAT fs ! i"
  let ?f2 = "\<lambda> i. RAT fs' ! i" 
  let ?n1 = "\<lambda> i. sq_norm (?g1 i)" 
  let ?n2 = "\<lambda> i. sq_norm (?g2 i)" 
  have heq:"fs ! (i - 1) = fs' ! i" "take (i-1) fs = take (i-1) fs'"
           "?f2 (i - 1) = ?f1 i" "?f2 i = ?f1 (i - 1)"
    unfolding fs'_def using i len i0 by auto
  have norm_pos2: "j < m \<Longrightarrow> ?n2 j > 0" for j 
    using gs2.sq_norm_pos len' by simp
  have norm_pos1: "j < m \<Longrightarrow> ?n1 j > 0" for j 
    using fs.gs.sq_norm_pos inv by simp
  have norm_zero2: "j < m \<Longrightarrow> ?n2 j \<noteq> 0" for j using norm_pos2[of j] by linarith
  have norm_zero1: "j < m \<Longrightarrow> ?n1 j \<noteq> 0" for j using norm_pos1[of j] by linarith
  have gs: "\<And> j. j < m \<Longrightarrow> ?g1 j \<in> Rn" using inv by blast
  have gs2: "\<And> j. j < m \<Longrightarrow> ?g2 j \<in> Rn" using fs.gs.gso_carrier conn2 by auto
  have g: "\<And> j. j < m \<Longrightarrow> ?f1 j \<in> Rn" using inv by auto
  have g2: "\<And> j. j < m \<Longrightarrow> ?f2 j \<in> Rn" using gs2.f_carrier conn2 by blast
  let ?fs1 = "?f1 ` {0..< (i - 1)}" 
  have G: "?fs1 \<subseteq> Rn" using g i by auto
  let ?gs1 = "?g1 ` {0..< (i - 1)}" 
  have G': "?gs1 \<subseteq> Rn" using gs i by auto
  let ?S = "gs.span ?fs1" 
  let ?S' = "gs.span ?gs1" 
  have S'S: "?S' = ?S" 
    by (rule fs.gs.partial_span', insert conn1 i, auto)
  have "gs.is_oc_projection (?g2 (i - 1)) (gs.span (?g2 ` {0..< (i - 1)})) (?f2 (i - 1))" 
    using i len' by (intro  gs2.gso_oc_projection_span(2)) auto
  also have "?f2 (i - 1) = ?f1 i" unfolding fs'_def using len i by auto
  also have "gs.span (?g2 ` {0 ..< (i - 1)}) = gs.span (?f2 ` {0 ..< (i - 1)})" 
    using i len' by (intro gs2.partial_span') auto
  also have "?f2 ` {0 ..< (i - 1)} = ?fs1" 
    by (rule image_cong[OF refl], insert len i, auto simp: fs'_def)
  finally have claim1: "gs.is_oc_projection (?g2 (i - 1)) ?S (?f1 i)" .
  have list_id: "[0..<Suc (i - 1)] = [0..< i - 1] @ [i - 1]" 
    "[0..< Suc i] = [0..< i] @ [i]" "map f [x] = [f x]" for f x using i by auto
  (* f1i_sum is claim 2 *)
  have f1i_sum: "?f1 i = gs.sumlist (map (\<lambda>j. ?mu1 i j \<cdot>\<^sub>v ?g1 j) [0 ..< i]) + ?g1 i" (is "_ = ?sum + _") 
    apply(subst fs.gs.fi_is_sum_of_mu_gso, insert len i, force)
    unfolding map_append list_id
    by (subst gs.M.sumlist_snoc, insert i gs conn1, auto simp: fs.gs.\<mu>.simps)
  have f1im1_sum: "?f1 (i - 1) = gs.sumlist (map (\<lambda>j. ?mu1 (i - 1) j \<cdot>\<^sub>v ?g1 j) [0..<i - 1]) + ?g1 (i - 1)" (is "_ = ?sum1 + _")
    apply(subst fs.gs.fi_is_sum_of_mu_gso, insert len i, force)
    unfolding map_append list_id
    by (subst gs.M.sumlist_snoc, insert i gs, auto simp: fs.gs.\<mu>.simps)

  have sum: "?sum \<in> Rn" by (rule gs.sumlist_carrier, insert gs i, auto)
  have sum1: "?sum1 \<in> Rn" by (rule gs.sumlist_carrier, insert gs i, auto)
  from gs.span_closed[OF G] have S: "?S \<subseteq> Rn" by auto
  from gs i have gs': "\<And> j. j < i - 1 \<Longrightarrow> ?g1 j \<in> Rn" and gsi: "?g1 (i - 1) \<in> Rn" by auto
  have "[0 ..< i] = [0 ..< Suc (i - 1)]" using i0 by simp
  also have "\<dots> = [0 ..< i - 1] @ [i - 1]" by simp
  finally have list: "[0 ..< i] = [0 ..< i - 1] @ [i - 1]" .

  { (* d does not change for k \<noteq> i *)
    fix k
    assume kn: "k \<le> m" and ki: "k \<noteq> i" 
    from d_swap_unchanged[OF len i0 i ki kn fs'_def]  
    have "d fs k = d fs' k" by simp
  } note d = this

  (* new value of g (i-1) *)
  have g2_im1: "?g2 (i - 1) = ?g1 i + ?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1)" (is "_ = _ + ?mu_f1")
  proof (rule gs.is_oc_projection_eq[OF  claim1 _ S g[OF i]])
    show "gs.is_oc_projection (?g1 i + ?mu_f1) ?S (?f1 i)" unfolding gs.is_oc_projection_def
    proof (intro conjI allI impI)
      let ?sum' = "gs.sumlist (map (\<lambda>j. ?mu1 i j \<cdot>\<^sub>v ?g1 j) [0 ..< i - 1])" 
      have sum': "?sum' \<in> Rn" by (rule gs.sumlist_carrier, insert gs i, auto)
      show inRn: "(?g1 i + ?mu_f1) \<in> Rn" using gs[OF i] gsi i by auto
      have carr: "?sum \<in> Rn" "?g1 i \<in> Rn" "?mu_f1 \<in> Rn" "?sum' \<in> Rn" using sum' sum gs[OF i] gsi i by auto
      have "?f1 i - (?g1 i + ?mu_f1) = (?sum + ?g1 i) - (?g1 i + ?mu_f1)"
        unfolding f1i_sum by simp
      also have "\<dots> = ?sum - ?mu_f1" using carr by auto
      also have "?sum = gs.sumlist (map (\<lambda>j. ?mu1 i j \<cdot>\<^sub>v ?g1 j) [0 ..< i - 1] @ [?mu_f1])" 
        unfolding list by simp 
      also have "\<dots> = ?sum' + ?mu_f1" 
        by (subst gs.sumlist_append, insert gs' gsi, auto)
      also have "\<dots> - ?mu_f1 = ?sum'" using sum' gsi by auto
      finally have id: "?f1 i - (?g1 i + ?mu_f1) = ?sum'" .
      show "?f1 i - (?g1 i + ?mu_f1) \<in> gs.span ?S" unfolding id gs.span_span[OF G]
      proof (rule gs.sumlist_in_span[OF G])
        fix v
        assume "v \<in> set (map (\<lambda>j. ?mu1 i j \<cdot>\<^sub>v ?g1 j) [0 ..< i - 1])" 
        then obtain j where j: "j < i - 1" and v: "v = ?mu1 i j \<cdot>\<^sub>v ?g1 j" by auto
        show "v \<in> ?S" unfolding v
          by (rule gs.smult_in_span[OF G], unfold S'S[symmetric], rule gs.span_mem, insert gs i j, auto)
      qed
      fix x
      assume "x \<in> ?S"
      hence x: "x \<in> ?S'" using S'S by simp
      show "(?g1 i + ?mu_f1) \<bullet> x = 0"
      proof (rule gs.orthocompl_span[OF _ G' inRn x])
        fix x
        assume "x \<in> ?gs1"
        then obtain j where j: "j < i - 1" and x_id: "x = ?g1 j" by auto
        from j i x_id gs[of j] have x: "x \<in> Rn" by auto
        {
          fix k
          assume k: "k > j" "k < m" 
          have "?g1 k \<bullet> x = 0" unfolding x_id 
            by (rule fs.gs.orthogonal, insert conn1 k, auto)
        }
        from this[of i] this[of "i - 1"] j i 
        have main: "?g1 i \<bullet> x = 0" "?g1 (i - 1) \<bullet> x = 0" by auto
        have "(?g1 i + ?mu_f1) \<bullet> x = ?g1 i \<bullet> x + ?mu_f1 \<bullet> x" 
          by (rule add_scalar_prod_distrib[OF gs[OF i] _ x], insert gsi, auto)
        also have "\<dots> = 0" using main
          by (subst smult_scalar_prod_distrib[OF gsi x], auto)
        finally show "(?g1 i + ?mu_f1) \<bullet> x = 0" .
      qed
    qed
  qed
  { (* 16.13 (i): for g, only g_i and g_{i-1} can change *)
    fix k
    assume kn: "k < m" 
      and ki: "k \<noteq> i" "k \<noteq> i - 1"
    have "?g2 k = gs.oc_projection (gs.span (?g2 ` {0..<k})) (?f2 k)" 
      by (rule gs2.gso_oc_projection_span, insert kn conn2, auto)
    also have "gs.span (?g2 ` {0..<k}) = gs.span (?f2 ` {0..<k})" 
      by (rule gs2.partial_span', insert conn2 kn, auto)
    also have "?f2 ` {0..<k} = ?f1 ` {0..<k}"
    proof(cases "k\<le>i")
      case True hence "k < i - 1" using ki by auto
      then show ?thesis apply(intro image_cong) unfolding fs'_def using len i by auto
    next
      case False 
      have "?f2 ` {0..<k} = Fun.swap i (i - 1) ?f1 ` {0..<k}"
        unfolding Fun.swap_def fs'_def o_def using len i 
        by (intro image_cong, insert len kn, force+)
      also have "\<dots> = ?f1 ` {0..<k}"
        apply(rule swap_image_eq) using False by auto
      finally show ?thesis.
    qed
    also have "gs.span \<dots> = gs.span (?g1 ` {0..<k})" 
      by (rule sym, rule fs.gs.partial_span', insert conn1 kn, auto)
    also have "?f2 k = ?f1 k" using ki kn len unfolding fs'_def by auto
    also have "gs.oc_projection (gs.span (?g1 ` {0..<k})) \<dots> = ?g1 k" 
      by (subst fs.gs.gso_oc_projection_span, insert kn conn1, auto)
    finally have "?g2 k = ?g1 k" . 
  } note g2_g1_identical = this

  (* calculation of new mu-values *)
  { (* no change of mu for lines before line i - 1 *)
    fix jj ii
    assume ii: "ii < i - 1"  
    have "?mu2 ii jj = ?mu1 ii jj" using ii i len
      by (subst gs.\<mu>_cong[of _ _ "RAT fs" "RAT fs'"], auto simp: fs'_def)
  } note mu'_mu_small_i = this
  { (* swap of mu-values in lines i - 1 and i for j < i - 1 *)
    fix jj
    assume jj: "jj < i - 1"  
    hence id1: "jj < i - 1 \<longleftrightarrow> True" "jj < i \<longleftrightarrow> True" by auto
    have id2: "?g2 jj = ?g1 jj" by (subst g2_g1_identical, insert jj i, auto)       
    have "?mu2 i jj = ?mu1 (i - 1) jj" "?mu2 (i - 1) jj = ?mu1 i jj" 
      unfolding gs2.\<mu>.simps fs.gs.\<mu>.simps id1 id2 if_True using len i i0 by (auto simp: fs'_def)
  } note mu'_mu_i_im1_j = this

  have im1: "i - 1 < m" using i by auto

  (* calculation of new value of g_i *)
  let ?g2_im1 = "?g2 (i - 1)" 
  have g2_im1_Rn: "?g2_im1 \<in> Rn" using i conn2 by (auto intro!: fs.gs.gso_carrier)
  {
    let ?mu2_f2 = "\<lambda> j. - ?mu2 i j \<cdot>\<^sub>v ?g2 j" 
    let ?sum = "gs.sumlist (map (\<lambda>j. - ?mu1 (i - 1) j \<cdot>\<^sub>v ?g1 j) [0 ..< i - 1])" 
    have mhs: "?mu2_f2 (i - 1) \<in> Rn" using i conn2 by (auto intro!: fs.gs.gso_carrier)
    have sum': "?sum \<in> Rn" by (rule gs.sumlist_carrier, insert gs i, auto)
    have gim1: "?f1 (i - 1) \<in> Rn" using g i by auto
    have "?g2 i = ?f2 i + gs.sumlist (map ?mu2_f2 [0 ..< i-1] @ [?mu2_f2 (i-1)])" 
      unfolding gs2.gso.simps[of i] list by simp
    also have "?f2 i = ?f1 (i - 1)" unfolding fs'_def using len i i0 by auto
    also have "map ?mu2_f2 [0 ..< i-1] = map (\<lambda>j. - ?mu1 (i - 1) j \<cdot>\<^sub>v ?g1 j) [0 ..< i - 1]"
      by (rule map_cong[OF refl], subst g2_g1_identical, insert i, auto simp: mu'_mu_i_im1_j)
    also have "gs.sumlist (\<dots> @ [?mu2_f2 (i - 1)]) = ?sum + ?mu2_f2 (i - 1)" 
      by (subst gs.sumlist_append, insert gs i mhs, auto)
    also have "?f1 (i - 1) + \<dots> = (?f1 (i - 1) + ?sum) + ?mu2_f2 (i - 1)"
      using gim1 sum' mhs by auto
    also have "?f1 (i - 1) + ?sum = ?g1 (i - 1)" unfolding fs.gs.gso.simps[of "i - 1"] by simp
    also have "?mu2_f2 (i - 1) = - (?f2 i \<bullet> ?g2_im1 / sq_norm ?g2_im1) \<cdot>\<^sub>v ?g2_im1" unfolding gs2.\<mu>.simps using i0 by simp
    also have "\<dots> = - ((?f2 i \<bullet> ?g2_im1 / sq_norm ?g2_im1) \<cdot>\<^sub>v ?g2_im1)" by auto
    also have "?g1 (i - 1) + \<dots> = ?g1 (i - 1) - ((?f2 i \<bullet> ?g2_im1 / sq_norm ?g2_im1) \<cdot>\<^sub>v ?g2_im1)"
      by (rule sym, rule minus_add_uminus_vec[of _ n], insert gsi g2_im1_Rn, auto)
    also have "?f2 i = ?f1 (i - 1)" by fact
    finally have "?g2 i = ?g1 (i - 1) - (?f1 (i - 1) \<bullet> ?g2 (i - 1) / sq_norm (?g2 (i - 1))) \<cdot>\<^sub>v ?g2 (i - 1)" .
  } note g2_i = this

  let ?n1 = "\<lambda> i. sq_norm (?g1 i)" 
  let ?n2 = "\<lambda> i. sq_norm (?g2 i)" 

  (* calculation of new norms *)
  { (* norm of g (i - 1) *)
    have "?n2 (i - 1) = sq_norm (?g1 i + ?mu_f1)" unfolding g2_im1 by simp
    also have "\<dots> = (?g1 i + ?mu_f1) \<bullet> (?g1 i + ?mu_f1)" 
      by (simp add: sq_norm_vec_as_cscalar_prod)
    also have "\<dots> = (?g1 i + ?mu_f1) \<bullet> ?g1 i + (?g1 i + ?mu_f1) \<bullet> ?mu_f1" 
      by (rule scalar_prod_add_distrib, insert gs i, auto)
    also have "(?g1 i + ?mu_f1) \<bullet> ?g1 i = ?g1 i \<bullet> ?g1 i + ?mu_f1 \<bullet> ?g1 i" 
      by (rule add_scalar_prod_distrib, insert gs i, auto)
    also have "(?g1 i + ?mu_f1) \<bullet> ?mu_f1 = ?g1 i \<bullet> ?mu_f1 + ?mu_f1 \<bullet> ?mu_f1" 
      by (rule add_scalar_prod_distrib, insert gs i, auto)
    also have "?mu_f1 \<bullet> ?g1 i = ?g1 i \<bullet> ?mu_f1"
      by (rule comm_scalar_prod, insert gs i, auto)
    also have "?g1 i \<bullet> ?g1 i = sq_norm (?g1 i)" 
      by (simp add: sq_norm_vec_as_cscalar_prod)
    also have "?g1 i \<bullet> ?mu_f1 = ?mu1 i (i - 1) * (?g1 i \<bullet> ?g1 (i - 1))" 
      by (rule scalar_prod_smult_right, insert gs[OF i] gs[OF \<open>i - 1 < m\<close>], auto)
    also have "?g1 i \<bullet> ?g1 (i - 1) = 0" 
      using orthogonalD[OF fs.gs.orthogonal_gso, of i "i - 1"] i len i0  
      by (auto simp: o_def)
    also have "?mu_f1 \<bullet> ?mu_f1 = ?mu1 i (i - 1) * (?mu_f1 \<bullet> ?g1 (i - 1))" 
      by (rule scalar_prod_smult_right, insert gs[OF i] gs[OF \<open>i - 1 < m\<close>], auto)
    also have "?mu_f1 \<bullet> ?g1 (i - 1) = ?mu1 i (i - 1) * (?g1 (i - 1) \<bullet> ?g1 (i - 1))" 
      by (rule scalar_prod_smult_left, insert gs[OF i] gs[OF \<open>i - 1 < m\<close>], auto)
    also have "?g1 (i - 1) \<bullet> ?g1 (i - 1) = sq_norm (?g1 (i - 1))" 
      by (simp add: sq_norm_vec_as_cscalar_prod)
    finally have "?n2 (i - 1) = ?n1 i + (?mu1 i (i - 1) * ?mu1 i (i - 1)) * ?n1 (i - 1)" 
      by (simp add: ac_simps o_def)
  } note sq_norm_g2_im1 = this

  from norm_pos1[OF i] norm_pos1[OF im1] norm_pos2[OF i] norm_pos2[OF im1]
  have norm0: "?n1 i \<noteq> 0" "?n1 (i - 1) \<noteq> 0" "?n2 i \<noteq> 0" "?n2 (i - 1) \<noteq> 0" by auto
  hence norm0': "?n2 (i - 1) \<noteq> 0" using i by auto

  { (* new norm of g i *)
    have si: "Suc i \<le> m" and im1: "i - 1 \<le> m" using i by auto
    have det1: "gs.Gramian_determinant (RAT fs) (Suc i) = (\<Prod>j<Suc i. \<parallel>fs.gs.gso j\<parallel>\<^sup>2)"
      using fs.gs.Gramian_determinant si len by auto
    have det2: "gs.Gramian_determinant (RAT fs') (Suc i) = (\<Prod>j<Suc i. \<parallel>gs2.gso j\<parallel>\<^sup>2)"
      using gs2.Gramian_determinant si len' by auto
    from norm_zero1[OF less_le_trans[OF _ im1]] have 0: "(\<Prod>j < i-1. ?n1 j) \<noteq> 0" 
      by (subst prod_zero_iff, auto)
    have "rat_of_int (d fs' (Suc i)) = rat_of_int (d fs (Suc i))" 
      using d_swap_unchanged[OF len i0 i _ si fs'_def] by auto
    also have "rat_of_int (d fs' (Suc i)) = gs.Gramian_determinant (RAT fs') (Suc i)" unfolding d_def 
      by (subst fs.of_int_Gramian_determinant[symmetric], insert conn2 i g fs', auto simp: set_conv_nth)
    also have "\<dots> = (\<Prod>j<Suc i. ?n2 j)" unfolding det2 by (rule prod.cong, insert i, auto)
    also have "rat_of_int (d fs (Suc i)) = gs.Gramian_determinant (RAT fs) (Suc i)" unfolding d_def 
      by (subst fs.of_int_Gramian_determinant[symmetric], insert conn1 i g, auto)
    also have "\<dots> = (\<Prod>j<Suc i. ?n1 j)" unfolding det1 by (rule prod.cong, insert i, auto)
    also have "{..<Suc i} = insert i (insert (i-1) {..<i-1})" (is "_ = ?set") by auto
    also have "(\<Prod>j\<in> ?set. ?n2 j) = ?n2 i * ?n2 (i - 1) * (\<Prod>j < i-1. ?n2 j)" using i0
      by (subst prod.insert; (subst prod.insert)?; auto)
    also have "(\<Prod>j\<in> ?set. ?n1 j) = ?n1 i * ?n1 (i - 1) * (\<Prod>j < i-1. ?n1 j)" using i0
      by (subst prod.insert; (subst prod.insert)?; auto)
    also have "(\<Prod>j < i-1. ?n2 j) = (\<Prod>j < i-1. ?n1 j)" 
      by (rule prod.cong, insert G2_G, auto)
    finally have "?n2 i = ?n1 i * ?n1 (i - 1) / ?n2 (i - 1)" 
      using 0 norm0' by (auto simp: field_simps)
  } note sq_norm_g2_i = this

  (* mu values in rows > i do not change with j \<notin> {i, i - 1} *)
  {
    fix ii j
    assume ii: "ii > i" "ii < m" 
     and ji: "j \<noteq> i" "j \<noteq> i - 1" 
    {
      assume j: "j < ii" 
      have "?mu2 ii j = (?f2 ii \<bullet> ?g2 j) / sq_norm (?g2 j)" 
        unfolding gs2.\<mu>.simps using j by auto
      also have "?f2 ii = ?f1 ii" using ii len unfolding fs'_def by auto
      also have "?g2 j = ?g1 j" using g2_g1_identical[of j] j ii ji by auto
      finally have "?mu2 ii j = ?mu1 ii j" 
        unfolding fs.gs.\<mu>.simps using j by auto
    }
    hence "?mu2 ii j = ?mu1 ii j" by (cases "j < ii", auto simp: gs2.\<mu>.simps fs.gs.\<mu>.simps)
  } note mu_no_change_large_row = this

  { (* the new value of mu i (i - 1) *)
    have "?mu2 i (i - 1) = (?f2 i \<bullet> ?g2 (i - 1)) / ?n2 (i - 1)" 
      unfolding gs2.\<mu>.simps using i0 by auto
    also have "?f2 i \<bullet> ?g2 (i - 1) = ?f1 (i - 1) \<bullet> ?g2 (i - 1)" 
      using len i i0 unfolding fs'_def by auto
    also have "\<dots> = ?f1 (i - 1) \<bullet> (?g1 i + ?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1))" 
      unfolding g2_im1 by simp
    also have "\<dots> = ?f1 (i - 1) \<bullet> ?g1 i + ?f1 (i - 1) \<bullet> (?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1))" 
      by (rule scalar_prod_add_distrib[of _ n], insert i gs g, auto)
    also have "?f1 (i - 1) \<bullet> ?g1 i = 0" 
      by (subst fs.gs.fi_scalar_prod_gso, insert conn1 im1 i i0, auto simp: fs.gs.\<mu>.simps fs.gs.\<mu>.simps)
    also have "?f1 (i - 1) \<bullet> (?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1)) = 
       ?mu1 i (i - 1) * (?f1 (i - 1) \<bullet> ?g1 (i - 1))"  
      by (rule scalar_prod_smult_distrib, insert gs g i, auto)
    also have "?f1 (i - 1) \<bullet> ?g1 (i - 1) = ?n1 (i - 1)" 
      by (subst fs.gs.fi_scalar_prod_gso, insert conn1 im1, auto simp: fs.gs.\<mu>.simps)
    finally 
    have "?mu2 i (i - 1) = ?mu1 i (i - 1) * ?n1 (i - 1) / ?n2 (i - 1)" 
      by (simp add: sq_norm_vec_as_cscalar_prod)
  } note mu'_mu_i_im1 = this

  { (* the new values of mu ii (i - 1) for ii > i *)
    fix ii assume iii: "ii > i" and ii: "ii < m" 
    hence iii1: "i - 1 < ii" by auto
    have "?mu2 ii (i - 1) = (?f2 ii \<bullet> ?g2 (i - 1)) / ?n2 (i - 1)" 
      unfolding gs2.\<mu>.simps using i0 iii1 by auto
    also have "?f2 ii \<bullet> ?g2 (i-1) = ?f1 ii \<bullet> ?g2 (i - 1)" 
      using len i i0 iii ii unfolding fs'_def by auto
    also have "\<dots> = ?f1 ii \<bullet> (?g1 i + ?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1))" 
      unfolding g2_im1 by simp
    also have "\<dots> = ?f1 ii \<bullet> ?g1 i + ?f1 ii \<bullet> (?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1))" 
      by (rule scalar_prod_add_distrib[of _ n], insert i ii gs g, auto)
    also have "?f1 ii \<bullet> ?g1 i = ?mu1 ii i * ?n1 i" 
      by (rule fs.gs.fi_scalar_prod_gso, insert conn1 ii i, auto)
    also have "?f1 ii \<bullet> (?mu1 i (i - 1) \<cdot>\<^sub>v ?g1 (i - 1)) = 
       ?mu1 i (i - 1) * (?f1 ii \<bullet> ?g1 (i - 1))"  
      by (rule scalar_prod_smult_distrib, insert gs g i ii, auto)
    also have "?f1 ii \<bullet> ?g1 (i - 1) = ?mu1 ii (i - 1) * ?n1 (i - 1)" 
      by (rule fs.gs.fi_scalar_prod_gso, insert conn1 ii im1, auto)
    finally have "?mu2 ii (i - 1) = ?mu1 ii (i - 1) * ?mu2 i (i - 1) + ?mu1 ii i * ?n1 i / ?n2 (i - 1)" 
      unfolding mu'_mu_i_im1 using norm0 by (auto simp: field_simps)
  } note mu'_mu_large_row_im1 = this    

  { (* the new values of mu ii i for ii > i *)
    fix ii assume iii: "ii > i" and ii: "ii < m" 
    have "?mu2 ii i = (?f2 ii \<bullet> ?g2 i) / ?n2 i" 
      unfolding gs2.\<mu>.simps using i0 iii by auto
    also have "?f2 ii \<bullet> ?g2 i = ?f1 ii \<bullet> ?g2 i" 
      using len i i0 iii ii unfolding fs'_def by auto
    also have "\<dots> = ?f1 ii \<bullet> (?g1 (i - 1) - (?f1 (i - 1) \<bullet> ?g2 (i - 1) / ?n2 (i - 1)) \<cdot>\<^sub>v ?g2 (i - 1))" 
      unfolding g2_i by simp
    also have "?f1 (i - 1) = ?f2 i" using i i0 len unfolding fs'_def by auto
    also have "?f2 i \<bullet> ?g2 (i - 1) / ?n2 (i - 1) = ?mu2 i (i - 1)" 
      unfolding gs2.\<mu>.simps using i i0 by auto
    also have "?f1 ii \<bullet> (?g1 (i - 1) - ?mu2 i (i - 1) \<cdot>\<^sub>v ?g2 (i - 1))
       = ?f1 ii \<bullet> ?g1 (i - 1) - ?f1 ii \<bullet> (?mu2 i (i - 1) \<cdot>\<^sub>v ?g2 (i - 1))" 
      by (rule scalar_prod_minus_distrib[OF g gs], insert gs2 ii i, auto)
    also have "?f1 ii \<bullet> ?g1 (i - 1) = ?mu1 ii (i - 1) * ?n1 (i - 1)" 
      by (rule fs.gs.fi_scalar_prod_gso, insert conn1 ii im1, auto)
    also have "?f1 ii \<bullet> (?mu2 i (i - 1) \<cdot>\<^sub>v ?g2 (i - 1)) = 
       ?mu2 i (i - 1) * (?f1 ii \<bullet> ?g2 (i - 1))" 
      by (rule scalar_prod_smult_distrib, insert gs gs2 g i ii, auto)
    also have "?f1 ii \<bullet> ?g2 (i - 1) = (?f1 ii \<bullet> ?g2 (i - 1) / ?n2 (i - 1)) * ?n2 (i - 1)" 
      using norm0 by (auto simp: field_simps)
    also have "?f1 ii \<bullet> ?g2 (i - 1) = ?f2 ii \<bullet> ?g2 (i - 1)" 
      using len ii iii unfolding fs'_def by auto
    also have "\<dots> / ?n2 (i - 1) = ?mu2 ii (i - 1)" unfolding gs2.\<mu>.simps using iii by auto
    finally 
    have "?mu2 ii i = 
       (?mu1 ii (i - 1) * ?n1 (i - 1) - ?mu2 i (i - 1) * ?mu2 ii (i - 1) * ?n2 (i - 1)) / ?n2 i" by simp
    also have "\<dots> = (?mu1 ii (i - 1) - ?mu1 i (i - 1) * ?mu2 ii (i - 1)) * ?n2 (i - 1) / ?n1 i" 
      unfolding sq_norm_g2_i mu'_mu_i_im1 using norm0 by (auto simp: field_simps)
    also have "\<dots> = (?mu1 ii (i - 1) * ?n2 (i - 1) - 
      ?mu1 i (i - 1) * ((?mu1 ii i * ?n1 i + ?mu1 i (i - 1) * ?mu1 ii (i - 1) * ?n1 (i - 1)))) / ?n1 i" 
      unfolding mu'_mu_large_row_im1[OF iii ii] mu'_mu_i_im1 using norm0 by (auto simp: field_simps)
    also have "\<dots> = ?mu1 ii (i - 1) - ?mu1 i (i - 1) * ?mu1 ii i" 
      unfolding sq_norm_g2_im1 using norm0 by (auto simp: field_simps)
    finally have "?mu2 ii i = ?mu1 ii (i - 1) - ?mu1 i (i - 1) * ?mu1 ii i" .
  } note mu'_mu_large_row_i = this


  {
    fix k assume k: "k < m" 
    show "?g2 k = ?newg k" 
      unfolding g2_i[symmetric] 
      unfolding g2_im1[symmetric]
      using g2_g1_identical[OF k] by auto
    show "?n2 k = ?new_norm k" 
      unfolding sq_norm_g2_i[symmetric]
      unfolding sq_norm_g2_im1[symmetric]
      using g2_g1_identical[OF k] by auto
    fix j assume jk: "j < k" hence j: "j < m" using k by auto
    have "k < i - 1 \<or> k = i - 1 \<or> k = i \<or> k > i" by linarith
    thus "?mu2 k j = ?new_mu k j" 
      unfolding mu'_mu_i_im1[symmetric]
      using
        mu'_mu_large_row_i[OF _ k]
        mu'_mu_large_row_im1 [OF _ k]
        mu_no_change_large_row[OF _ k, of j]
        mu'_mu_small_i
        mu'_mu_i_im1_j jk j k
      by auto
  } note new_g = this

  (* stay reduced *)
  from inv have sred: "reduced fs i" by auto
  have sred: "reduced fs' (i - 1)"
    unfolding gram_schmidt_fs.reduced_def
  proof (intro conjI[OF red] allI impI, goal_cases)
    case (1 i' j)
    with sred have "\<bar>?mu1 i' j\<bar> \<le> 1 / 2" unfolding gram_schmidt_fs.reduced_def by auto
    thus ?case using mu'_mu_small_i[OF 1(1)] by simp
  qed

  { (* 16.13 (ii) : norm of g (i - 1) decreases by reduction factor *)
    note sq_norm_g2_im1
    also have "?n1 i + (?mu1 i (i - 1) * ?mu1 i (i - 1)) * ?n1 (i - 1)
      < 1/\<alpha> * (?n1 (i - 1)) + (1/2 * 1/2) * (?n1 (i - 1))"
    proof (rule add_less_le_mono[OF _ mult_mono])
      from norm_ineq[unfolded mult.commute[of \<alpha>],
          THEN linordered_field_class.mult_imp_less_div_pos[OF \<alpha>0(1)]]
      show "?n1 i < 1/\<alpha> * ?n1 (i - 1)" using len i by auto
      from m12 have abs: "abs (?mu1 i (i - 1)) \<le> 1/2" by auto
      have "?mu1 i (i - 1) * ?mu1 i (i - 1) \<le> abs (?mu1 i (i - 1)) * abs (?mu1 i (i - 1))" by auto
      also have "\<dots> \<le> 1/2 * 1/2" using mult_mono[OF abs abs] by auto
      finally show "?mu1 i (i - 1) * ?mu1 i (i - 1) \<le> 1/2 * 1/2" by auto
    qed auto
    also have "\<dots> = reduction * sq_norm (?g1 (i - 1))" unfolding reduction_def  
      using \<alpha>0 by (simp add: ring_distribs add_divide_distrib)
    finally have "?n2 (i - 1) < reduction * ?n1 (i - 1)" .
  } note g_reduction = this (* Lemma 16.13 (ii) *)

  have lin_indpt_list_fs': "gs.lin_indpt_list (RAT fs')"
    unfolding gs.lin_indpt_list_def using conn2 by auto

  have mu_small: "\<mu>_small fs' (i - 1)" 
    unfolding \<mu>_small_def
  proof (intro allI impI, goal_cases)
    case (1 j)
    thus ?case using inv(11) unfolding mu'_mu_i_im1_j[OF 1] \<mu>_small_def by auto
  qed      
      
  (* invariant is established *)
  show newInv: "LLL_invariant False (i - 1) fs'"
    by (rule LLL_invI, insert lin_indpt_list_fs' conn2 mu_small span' lattice fs' sred i, auto)

  (* show decrease in measure *)
  { (* 16.16 (ii), the decreasing case *)
    have ile: "i \<le> m" using i by auto
    from Gd[OF newInv, folded d_def, OF ile] 
    have "?R (d fs' i) = (\<Prod>j<i. ?n2 j )" by auto
    also have "\<dots> = prod ?n2 ({0 ..< i-1} \<union> {i - 1})" 
      by (rule sym, rule prod.cong, (insert i0, auto)[1], insert i, auto)
    also have "\<dots> = ?n2 (i - 1) * prod ?n2 ({0 ..< i-1})" 
      by simp
    also have "prod ?n2 ({0 ..< i-1}) = prod ?n1 ({0 ..< i-1})" 
      by (rule prod.cong[OF refl], subst g2_g1_identical, insert i, auto)
    also have "\<dots> = (prod ?n1 ({0 ..< i-1} \<union> {i - 1})) / ?n1 (i - 1)" 
      by (subst prod.union_disjoint, insert norm_pos1[OF im1], auto)
    also have "prod ?n1 ({0 ..< i-1} \<union> {i - 1}) = prod ?n1 {0..<i}"
      by (rule arg_cong[of _ _ "prod ?n1"], insert i0, auto)
    also have "\<dots> = (\<Prod>j<i. ?n1 j)"
      by (rule prod.cong, insert i0, auto)
    also have "\<dots> = ?R (d fs i)" unfolding d_def Gd[OF Linv ile]
      by (rule prod.cong[OF refl], insert i, auto)
    finally have new_di: "?R (d fs' i) = ?n2 (i - 1) / ?n1 (i - 1) * ?R (d fs i)" by simp
    also have "\<dots> < (reduction * ?n1 (i - 1)) / ?n1 (i - 1) * ?R (d fs i)"
      by (rule mult_strict_right_mono[OF divide_strict_right_mono[OF g_reduction norm_pos1[OF im1]]],
        insert LLL_d_pos[OF Linv] i, auto)  
    also have "\<dots> = reduction * ?R (d fs i)" using norm_pos1[OF im1] by auto
    finally have "d fs' i < real_of_rat reduction * d fs i" 
      using of_rat_less of_rat_mult of_rat_of_int_eq by metis
    note this new_di
  } note d_i = this
  show "ii \<le> m \<Longrightarrow> ?R (d fs' ii) = (if ii = i then ?n2 (i - 1) / ?n1 (i - 1) * ?R (d fs i) else ?R (d fs ii))" 
    for ii using d_i d by auto
  have pos: "k < m \<Longrightarrow> 0 < d fs' k" "k < m \<Longrightarrow> 0 \<le> d fs' k" for k 
    using LLL_d_pos[OF newInv, of k] by auto
  have prodpos:"0< (\<Prod>i<m. d fs' i)" apply (rule prod_pos)
    using LLL_d_pos[OF newInv] by auto
  have prod_pos':"0 < (\<Prod>x\<in>{0..<m} - {i}. real_of_int (d fs' x))" apply (rule prod_pos)
    using LLL_d_pos[OF newInv] pos by auto
  have prod_nonneg:"0 \<le> (\<Prod>x\<in>{0..<m} - {i}. real_of_int (d fs' x))" apply (rule prod_nonneg)
    using LLL_d_pos[OF newInv] pos by auto
  have prodpos2:"0<(\<Prod>ia<m. d fs ia)" apply (rule prod_pos)
    using LLL_d_pos[OF assms(1)] by auto
  have "D fs' = real_of_int (\<Prod>i<m. d fs' i)" unfolding D_def using prodpos by simp
  also have "(\<Prod>i<m. d fs' i) = (\<Prod> j \<in> {0 ..< m} - {i} \<union> {i}. d fs' j)"
    by (rule prod.cong, insert i, auto)
  also have "real_of_int \<dots> = real_of_int (\<Prod> j \<in> {0 ..< m} - {i}. d fs' j) * real_of_int (d fs' i)" 
    by (subst prod.union_disjoint, auto)
  also have "\<dots> < (\<Prod> j \<in> {0 ..< m} - {i}. d fs' j) * (of_rat reduction * d fs i)"
    by(rule mult_strict_left_mono[OF d_i(1)],insert prod_pos',auto)
  also have "(\<Prod> j \<in> {0 ..< m} - {i}. d fs' j) = (\<Prod> j \<in> {0 ..< m} - {i}. d fs j)"
    by (rule prod.cong, insert d, auto)
  also have "\<dots> * (of_rat reduction * d fs i) 
    = of_rat reduction * (\<Prod> j \<in> {0 ..< m} - {i} \<union> {i}. d fs j)" 
    by (subst prod.union_disjoint, auto)
  also have "(\<Prod> j \<in> {0 ..< m} - {i} \<union> {i}. d fs j) = (\<Prod> j<m. d fs j)" 
    by (subst prod.cong, insert i, auto)
  finally have D: "D fs' < real_of_rat reduction * D fs"
    unfolding D_def using prodpos2 by auto
  have logD: "logD fs' < logD fs" 
  proof (cases "\<alpha> = 4/3")
    case True
    show ?thesis using D unfolding reduction(4)[OF True] logD_def unfolding True by simp
  next
    case False
    hence False': "\<alpha> = 4/3 \<longleftrightarrow> False" by simp
    from False \<alpha> have "\<alpha> > 4/3" by simp
    with reduction have reduction1: "reduction < 1" by simp
    let ?new = "real (D fs')" 
    let ?old = "real (D fs)" 
    let ?log = "log (1/of_rat reduction)" 
    note pos = LLL_D_pos[OF newInv] LLL_D_pos[OF assms(1)]
    from reduction have "real_of_rat reduction > 0" by auto
    hence gediv:"1/real_of_rat reduction > 0" by auto
    have "(1/of_rat reduction) * ?new \<le> ((1/of_rat reduction) * of_rat reduction) * ?old"
      unfolding mult.assoc real_mult_le_cancel_iff2[OF gediv] using D by simp
    also have "(1/of_rat reduction) * of_rat reduction = 1" using reduction by auto
    finally have "(1/of_rat reduction) * ?new \<le> ?old" by auto
    hence "?log ((1/of_rat reduction) * ?new) \<le> ?log ?old"
      by (subst log_le_cancel_iff, auto simp: pos reduction1 reduction)
    hence "floor (?log ((1/of_rat reduction) * ?new)) \<le> floor (?log ?old)" 
      by (rule floor_mono)
    hence "nat (floor (?log ((1/of_rat reduction) * ?new))) \<le> nat (floor (?log ?old))" by simp
    also have "\<dots> = logD fs" unfolding logD_def False' by simp
    also have "?log ((1/of_rat reduction) * ?new) = 1 + ?log ?new" 
      by (subst log_mult, insert reduction reduction1, auto simp: pos )
    also have "floor (1 + ?log ?new) = 1 + floor (?log ?new)" by simp
    also have "nat (1 + floor (?log ?new)) = 1 + nat (floor (?log ?new))" 
      by (subst nat_add_distrib, insert pos reduction reduction1, auto)
    also have "nat (floor (?log ?new)) = logD fs'" unfolding logD_def False' by simp
    finally show "logD fs' < logD fs" by simp
  qed
  show "LLL_measure i fs > LLL_measure (i - 1) fs'" unfolding LLL_measure_def 
    using i logD by simp
qed

lemma LLL_inv_initial_state: "LLL_invariant True 0 fs_init" 
proof - 
  from lin_dep[unfolded gs.lin_indpt_list_def]
  have "set (RAT fs_init) \<subseteq> Rn" by auto
  hence fs_init: "set fs_init \<subseteq> carrier_vec n" by auto
  show ?thesis 
    by (rule LLL_invI[OF fs_init len _ _ lin_dep], auto simp: L_def gs.reduced_def gs.weakly_reduced_def)
qed

lemma LLL_inv_m_imp_reduced: assumes "LLL_invariant True m fs" 
  shows "reduced fs m" 
  using LLL_invD[OF assms] by blast

lemma basis_reduction_short_vector: assumes LLL_inv: "LLL_invariant True m fs" 
  and v: "v = hd fs" 
  and m0: "m \<noteq> 0"
shows "v \<in> carrier_vec n"
  "v \<in> L - {0\<^sub>v n}"  
  "h \<in> L - {0\<^sub>v n} \<Longrightarrow> rat_of_int (sq_norm v) \<le> \<alpha> ^ (m - 1) * rat_of_int (sq_norm h)" 
  "v \<noteq> 0\<^sub>v j" 
proof -
  let ?L = "lattice_of fs_init" 
  have a1: "\<alpha> \<ge> 1" using \<alpha> by auto 
  from LLL_invD[OF LLL_inv] have
    L: "lattice_of fs = L" 
    and red: "gram_schmidt_fs.weakly_reduced n (RAT fs) \<alpha> (length (RAT fs))" 
    and basis: "lin_indep fs" 
    and lenH: "length fs = m" 
    and H: "set fs \<subseteq> carrier_vec n" 
    by (auto simp: gs.lin_indpt_list_def gs.reduced_def)
  from lin_dep have G: "set fs_init \<subseteq> carrier_vec n" unfolding gs.lin_indpt_list_def by auto
  with m0 len have "dim_vec (hd fs_init) = n" by (cases fs_init, auto)
  from v m0 lenH v have v: "v = fs ! 0" by (cases fs, auto)
  interpret gs1: gram_schmidt_fs_lin_indpt n "RAT fs"
    by (standard) (use assms LLL_invariant_def gs.lin_indpt_list_def in auto)
  let ?r = "rat_of_int" 
  let ?rv = "map_vec ?r" 
  let ?F = "RAT fs" 
  let ?h = "?rv h" 
  { assume h:"h \<in> L - {0\<^sub>v n}" (is ?h_req)
    from h[folded L] have h: "h \<in> lattice_of fs" "h \<noteq> 0\<^sub>v n" by auto
    {
      assume f: "?h = 0\<^sub>v n" 
      have "?h = ?rv (0\<^sub>v n)" unfolding f by (intro eq_vecI, auto)
      hence "h = 0\<^sub>v n"
        using of_int_hom.vec_hom_zero_iff[of h] of_int_hom.vec_hom_inj by auto
      with h have False by simp
    } hence h0: "?h \<noteq> 0\<^sub>v n" by auto
    with lattice_of_of_int[OF H h(1)]
    have "?h \<in> gs.lattice_of ?F - {0\<^sub>v n}" by auto
  } 
  from gs1.weakly_reduced_imp_short_vector[OF red this a1] lenH
  show "h \<in> L - {0\<^sub>v n} \<Longrightarrow> ?r (sq_norm v) \<le> \<alpha> ^ (m - 1) * ?r (sq_norm h)"
    using basis unfolding L v gs.lin_indpt_list_def  by (auto simp: sq_norm_of_int)
  from m0 H lenH show vn: "v \<in> carrier_vec n" unfolding v by (cases fs, auto)
  have vL: "v \<in> L" unfolding L[symmetric] v using m0 H lenH
    by (intro basis_in_latticeI, cases fs, auto)
  {
    assume "v = 0\<^sub>v n" 
    hence "hd ?F = 0\<^sub>v n" unfolding v using m0 lenH by (cases fs, auto)
    with gs.lin_indpt_list_nonzero[OF basis] have False using m0 lenH by (cases fs, auto)
  }
  with vL show v: "v \<in> L - {0\<^sub>v n}" by auto
  have jn:"0\<^sub>v j \<in> carrier_vec n \<Longrightarrow> j = n" unfolding zero_vec_def carrier_vec_def by auto
  with v vn show "v \<noteq> 0\<^sub>v j" by auto
qed


lemma LLL_mu_d_Z: assumes inv: "LLL_invariant upw i fs" 
  and j: "j \<le> ii" and ii: "ii < m" 
shows "of_int (d fs (Suc j)) * \<mu> fs ii j \<in> \<int>"
proof -
  interpret fs: fs_int' n m fs_init \<alpha> upw i fs
    by standard (use inv in auto)
  show ?thesis
    using assms fs.fs_int_mu_d_Z LLL_invD[OF inv] unfolding d_def fs.d_def by auto
qed

context fixes upw i fs
  assumes Linv: "LLL_invariant upw i fs" and gbnd: "g_bound fs" 
begin

interpretation gs1: gram_schmidt_fs_lin_indpt n "RAT fs"
  by (standard) (use Linv LLL_invariant_def gs.lin_indpt_list_def in auto)

lemma LLL_inv_N_pos: assumes m: "m \<noteq> 0" 
shows "N > 0" 
proof -
  let ?r = rat_of_int
  note inv = LLL_invD[OF Linv]
  from inv have F: "RAT fs ! 0 \<in> Rn" "fs ! 0 \<in> carrier_vec n" using m by auto
  from m have upt: "[0..< m] = 0 # [1 ..< m]" using upt_add_eq_append[of 0 1 "m - 1"] by auto
  from inv(6) m have "map_vec ?r (fs ! 0) \<noteq> 0\<^sub>v n" using gs.lin_indpt_list_nonzero[OF inv(1)]
    unfolding set_conv_nth by force
  hence F0: "fs ! 0 \<noteq> 0\<^sub>v n" by auto
  hence "sq_norm (fs ! 0) \<noteq> 0" using F by simp
  hence 1: "sq_norm (fs ! 0) \<ge> 1" using sq_norm_vec_ge_0[of "fs ! 0"] by auto
  from gbnd m have "sq_norm (gso fs 0) \<le> of_nat N" unfolding g_bound_def by auto
  also have "gso fs 0 = RAT fs ! 0" unfolding upt using F by (simp add: gs1.gso.simps[of 0])
  also have "RAT fs ! 0 = map_vec ?r (fs ! 0)" using inv(6) m by auto
  also have "sq_norm \<dots> = ?r (sq_norm (fs ! 0))" by (simp add: sq_norm_of_int)
  finally show ?thesis using 1 by (cases N, auto)
qed


(* equation (3) in front of Lemma 16.18 *)
lemma d_approx_main: assumes i: "ii \<le> m" "m \<noteq> 0" 
shows "rat_of_int (d fs ii) \<le> rat_of_nat (N^ii)" 
proof -
  note inv = LLL_invD[OF Linv]
  from LLL_inv_N_pos i have A: "0 < N" by auto
  note main = inv(2)[unfolded gram_schmidt_int_def gram_schmidt_wit_def]
  have "rat_of_int (d fs ii) = (\<Prod>j<ii. \<parallel>gso fs j\<parallel>\<^sup>2)" unfolding d_def using i
    by (auto simp: Gramian_determinant [OF Linv])
  also have "\<dots> \<le> (\<Prod>j<ii. of_nat N)" using i
    by (intro prod_mono ballI conjI prod_nonneg, insert gbnd[unfolded g_bound_def], auto)
  also have "\<dots> = (of_nat N)^ii" unfolding prod_constant by simp
  also have "\<dots> = of_nat (N^ii)" by simp
  finally show ?thesis by simp
qed

lemma d_approx: assumes i: "ii < m"  
  shows "rat_of_int (d fs ii) \<le> rat_of_nat (N^ii)" 
  using d_approx_main[of ii] assms by auto


lemma d_bound: assumes i: "ii < m" 
  shows "d fs ii \<le> N^ii" 
  using d_approx[OF assms] unfolding d_def by linarith


lemma D_approx: "D fs \<le> N ^ (m * m)" 
proof - 
  note inv = LLL_invD[OF Linv]
  from LLL_inv_N_pos have N: "m \<noteq> 0 \<Longrightarrow> 0 < N" by auto
  note main = inv(2)[unfolded gram_schmidt_int_def gram_schmidt_wit_def]
  have "rat_of_int (\<Prod>i<m. d fs i) = (\<Prod>i<m. rat_of_int (d fs i))" by simp
  also have "\<dots> \<le> (\<Prod>i<m. (of_nat N) ^ i)" 
    by (rule prod_mono, insert d_approx LLL_d_pos[OF Linv], auto simp: less_le)
  also have "\<dots> \<le> (\<Prod>i<m. (of_nat N ^ m))" 
    by (rule prod_mono, insert N, auto intro: pow_mono_exp)
  also have "\<dots> = (of_nat N)^(m * m)" unfolding prod_constant power_mult by simp
  also have "\<dots> = of_nat (N ^ (m * m))" by simp
  finally have "(\<Prod>i<m. d fs i) \<le> N ^ (m * m)" by linarith
  also have "(\<Prod>i<m. d fs i) = D fs" unfolding D_def 
    by (subst nat_0_le, rule prod_nonneg, insert LLL_d_pos[OF Linv], auto simp: le_less)  
  finally show "D fs \<le> N ^ (m * m)" by linarith 
qed


lemma LLL_measure_approx: assumes "\<alpha> > 4/3" "m \<noteq> 0" 
shows "LLL_measure i fs \<le> m + 2 * m * m * log base N"
proof -   
  have b1: "base > 1" using base assms by auto
  have id: "base = 1 / real_of_rat reduction" unfolding base_def reduction_def using \<alpha>0 by
    (auto simp: field_simps of_rat_divide)
  from LLL_D_pos[OF Linv] have D1: "real (D fs) \<ge> 1" by auto
  note invD = LLL_invD[OF Linv]  
  from invD
  have F: "set fs \<subseteq> carrier_vec n" and len: "length fs = m" by auto
  have N0: "N > 0" using LLL_inv_N_pos[OF assms(2)] .
  from D_approx 
  have D: "D fs \<le> N ^ (m * m)" .
  hence "real (D fs) \<le> real (N ^ (m * m))" by linarith
  also have "\<dots> = real N ^ (m * m)" by simp
  finally have log: "log base (real (D fs)) \<le> log base (real N ^ (m * m))"   
    by (subst log_le_cancel_iff[OF b1], insert D1 N0, auto)

  have "real (logD fs) = real (nat \<lfloor>log base (real (D fs))\<rfloor>)" 
    unfolding logD_def id using assms by auto
  also have "\<dots> \<le> log base (real (D fs))" using b1 D1 by auto
  also have "\<dots> \<le> log base (real N ^ (m * m))" by fact
  also have "\<dots> = (m * m) * log base (real N)" 
    by (rule log_nat_power, insert N0, auto)
  finally have main: "logD fs \<le> m * m * log base N" by simp

  have "real (LLL_measure i fs) = real (2 * logD fs + m - i)"
    unfolding LLL_measure_def split invD(1) by simp
  also have "\<dots> \<le> 2 * real (logD fs) + m" using invD by simp
  also have "\<dots> \<le> 2 * (m * m * log base N) + m" using main by auto
  finally show ?thesis by simp
qed
end

lemma g_bound_fs_init: "g_bound fs_init" 
proof -
  {
    fix i
    assume i: "i < m" 
    let ?N = "map (nat o sq_norm) fs_init"
    let ?r = rat_of_int
    from i have mem: "nat (sq_norm (fs_init ! i)) \<in> set ?N" using fs_init len unfolding set_conv_nth by force
    interpret gs: gram_schmidt_fs_lin_indpt n "RAT fs_init"
      by (standard) (use len lin_dep LLL_invariant_def gs.lin_indpt_list_def in auto)
    from mem_set_imp_le_max_list[OF _ mem]
    have FN: "nat (sq_norm (fs_init ! i)) \<le> N" unfolding N_def by force
    hence "\<parallel>fs_init ! i\<parallel>\<^sup>2 \<le> int N" using i by auto
    also have "\<dots> \<le> int (N * m)" using i by fastforce
    finally have f_bnd:  "\<parallel>fs_init ! i\<parallel>\<^sup>2 \<le> int (N * m)" .
    from FN have "rat_of_nat (nat (sq_norm (fs_init ! i))) \<le> rat_of_nat N" by simp
    also have "rat_of_nat (nat (sq_norm (fs_init ! i))) = ?r (sq_norm (fs_init ! i))" 
      using sq_norm_vec_ge_0[of "fs_init ! i"] by auto
    also have "\<dots> = sq_norm (RAT fs_init ! i)" unfolding sq_norm_of_int[symmetric] using fs_init len i by auto
    finally have "sq_norm (RAT fs_init ! i) \<le> rat_of_nat N" .
    with gs.sq_norm_gso_le_f i len lin_dep
    have g_bnd: "\<parallel>gs.gso i\<parallel>\<^sup>2 \<le> rat_of_nat N"
      unfolding gs.lin_indpt_list_def by fastforce
    note f_bnd g_bnd
  }
  thus "g_bound fs_init" unfolding g_bound_def by auto
qed

lemma LLL_measure_approx_fs_init: 
  "LLL_invariant upw i fs_init \<Longrightarrow> 4 / 3 < \<alpha> \<Longrightarrow> m \<noteq> 0 \<Longrightarrow> 
  real (LLL_measure i fs_init) \<le> real m + real (2 * m * m) * log base (real N)" 
  using LLL_measure_approx[OF _ g_bound_fs_init] .

lemma N_le_MMn: assumes m0: "m \<noteq> 0" 
  shows "N \<le> nat M * nat M * n" 
  unfolding N_def
proof (rule max_list_le, unfold set_map o_def)
  fix ni
  assume "ni \<in> (\<lambda>x. nat \<parallel>x\<parallel>\<^sup>2) ` set fs_init" 
  then obtain fi where ni: "ni = nat (\<parallel>fi\<parallel>\<^sup>2)" and fi: "fi \<in> set fs_init" by auto
  from fi len obtain i where fii: "fi = fs_init ! i" and i: "i < m" unfolding set_conv_nth by auto
  from fi fs_init have fi: "fi \<in> carrier_vec n" by auto
  let ?set = "{\<bar>fs_init ! i $ j\<bar> |i j. i < m \<and> j < n} \<union> {0}" 
  have id: "?set = (\<lambda> (i,j). abs (fs_init ! i $ j)) ` ({0..<m} \<times> {0..<n}) \<union> {0}" 
    by force
  have fin: "finite ?set" unfolding id by auto
  { 
    fix j assume "j < n" 
    hence "M \<ge> \<bar>fs_init ! i $ j\<bar>" unfolding M_def using i
      by (intro Max_ge[of _ "abs (fs_init ! i $ j)"], intro fin, auto)
  } note M = this
  from Max_ge[OF fin, of 0] have M0: "M \<ge> 0" unfolding M_def by auto
  have "ni = nat (\<parallel>fi\<parallel>\<^sup>2)" unfolding ni by auto
  also have "\<dots> \<le> nat (int n * \<parallel>fi\<parallel>\<^sub>\<infinity>\<^sup>2)" using sq_norm_vec_le_linf_norm[OF fi]
    by (intro nat_mono, auto)
  also have "\<dots> = n * nat (\<parallel>fi\<parallel>\<^sub>\<infinity>\<^sup>2)"
    by (simp add: nat_mult_distrib)
  also have "\<dots> \<le> n * nat (M^2)" 
  proof (rule mult_left_mono[OF nat_mono])
    have fi: "\<parallel>fi\<parallel>\<^sub>\<infinity> \<le> M" unfolding linf_norm_vec_def    
    proof (rule max_list_le, unfold set_append set_map, rule ccontr)
      fix x
      assume "x \<in> abs ` set (list_of_vec fi) \<union> set [0]" and xM: "\<not> x \<le> M"  
      with M0 obtain fij where fij: "fij \<in> set (list_of_vec fi)" and x: "x = abs fij" by auto
      from fij fi obtain j where j: "j < n" and fij: "fij = fi $ j" 
        unfolding set_list_of_vec vec_set_def by auto
      from M[OF j] xM[unfolded x fij fii] show False by auto
    qed auto                
    show "\<parallel>fi\<parallel>\<^sub>\<infinity>\<^sup>2 \<le> M^2" unfolding abs_le_square_iff[symmetric] using fi 
      using linf_norm_vec_ge_0[of fi] by auto
  qed auto
  finally show "ni \<le> nat M * nat M * n" using M0 
    by (subst nat_mult_distrib[symmetric], auto simp: power2_eq_square ac_simps)
qed (insert m0 len, auto)



subsection \<open>Basic LLL implementation based on previous results\<close>

text \<open>We now assemble a basic implementation of the LLL algorithm,
  where only the lattice basis is updated, and where the GSO and the $\mu$-values
  are always computed from scratch. This enables a simple soundness proof 
  and permits to separate an efficient implementation from the soundness reasoning.\<close>

fun basis_reduction_add_rows_loop where
  "basis_reduction_add_rows_loop i fs 0 = fs" 
| "basis_reduction_add_rows_loop i fs (Suc j) = (
     let c = round (\<mu> fs i j);
         fs' = (if c = 0 then fs else fs[ i := fs ! i - c \<cdot>\<^sub>v fs ! j])
      in basis_reduction_add_rows_loop i fs' j)" 

definition basis_reduction_add_rows where
  "basis_reduction_add_rows upw i fs = 
     (if upw then basis_reduction_add_rows_loop i fs i else fs)" 

definition basis_reduction_swap where
  "basis_reduction_swap i fs = (False, i - 1, fs[i := fs ! (i - 1), i - 1 := fs ! i])" 

definition basis_reduction_step where
  "basis_reduction_step upw i fs = (if i = 0 then (True, Suc i, fs)
     else let 
       fs' = basis_reduction_add_rows upw i fs
     in if sq_norm (gso fs' (i - 1)) \<le> \<alpha> * sq_norm (gso fs' i) then
          (True, Suc i, fs') 
        else basis_reduction_swap i fs')" 

function basis_reduction_main where
  "basis_reduction_main (upw,i,fs) = (if i < m \<and> LLL_invariant upw i fs
     then basis_reduction_main (basis_reduction_step upw i fs) else
     fs)"
  by pat_completeness auto

definition "reduce_basis = basis_reduction_main (True, 0, fs_init)" 

definition "short_vector = hd reduce_basis" 

text \<open>Soundness of this implementation is easily proven\<close>

lemma basis_reduction_add_rows_loop: assumes 
  inv: "LLL_invariant True i fs" 
  and mu_small: "\<mu>_small_row i fs j"
  and res: "basis_reduction_add_rows_loop i fs j = fs'" 
  and i: "i < m" 
  and j: "j \<le> i" 
shows "LLL_invariant False i fs'" "LLL_measure i fs' = LLL_measure i fs" 
proof (atomize(full), insert assms, induct j arbitrary: fs)
  case (0 fs)
  thus ?case using basis_reduction_add_row_done[of i fs] by auto
next
  case (Suc j fs)
  hence j: "j < i" by auto
  let ?c = "round (\<mu> fs i j)" 
  show ?case
  proof (cases "?c = 0")
    case True
    thus ?thesis using Suc(1)[OF Suc(2) basis_reduction_add_row_main_0[OF Suc(2) i j True Suc(3)]]
      Suc(2-) by auto
  next
    case False
    note step = basis_reduction_add_row_main[OF Suc(2) i j refl]
    show ?thesis using Suc(1)[OF step(1-2)] False Suc(2-) step(3) by auto
  qed
qed

lemma basis_reduction_add_rows: assumes 
  inv: "LLL_invariant upw i fs" 
  and res: "basis_reduction_add_rows upw i fs = fs'" 
  and i: "i < m" 
shows "LLL_invariant False i fs'" "LLL_measure i fs' = LLL_measure i fs" 
proof (atomize(full), goal_cases)
  case 1
  note def = basis_reduction_add_rows_def
  show ?case
  proof (cases upw)
    case False
    with res inv show ?thesis by (simp add: def)
  next
    case True
    with inv have "LLL_invariant True i fs" by auto
    note start = this \<mu>_small_row_refl[of i fs]
    from res[unfolded def] True have "basis_reduction_add_rows_loop i fs i = fs'" by auto
    from basis_reduction_add_rows_loop[OF start this i]
    show ?thesis by auto
  qed
qed

lemma basis_reduction_swap: assumes 
  inv: "LLL_invariant False i fs" 
  and res: "basis_reduction_swap i fs = (upw',i',fs')" 
  and cond: "sq_norm (gso fs (i - 1)) > \<alpha> * sq_norm (gso fs i)" 
  and i: "i < m" "i \<noteq> 0" 
shows "LLL_invariant upw' i' fs'" (is ?g1)
  "LLL_measure i' fs' < LLL_measure i fs" (is ?g2)
proof -
  note def = basis_reduction_swap_def
  from res[unfolded basis_reduction_swap_def]
  have id: "upw' = False" "i' = i - 1" "fs' = fs[i := fs ! (i - 1), i - 1 := fs ! i]" by auto
  from basis_reduction_swap_main(1-2)[OF inv i cond id(3)] show ?g1 ?g2 unfolding id by auto
qed

lemma basis_reduction_step: assumes 
  inv: "LLL_invariant upw i fs" 
  and res: "basis_reduction_step upw i fs = (upw',i',fs')" 
  and i: "i < m" 
shows "LLL_invariant upw' i' fs'" "LLL_measure i' fs' < LLL_measure i fs" 
proof (atomize(full), goal_cases)
  case 1
  note def = basis_reduction_step_def
  obtain fs'' where fs'': "basis_reduction_add_rows upw i fs = fs''" by auto
  show ?case
  proof (cases "i = 0")
    case True
    from increase_i[OF inv i True] True
      res show ?thesis by (auto simp: def)
  next
    case False
    hence id: "(i = 0) = False" by auto
    note res = res[unfolded def id if_False fs'' Let_def]
    let ?x = "sq_norm (gso fs'' (i - 1))" 
    let ?y = "\<alpha> * sq_norm (gso fs'' i)" 
    from basis_reduction_add_rows[OF inv fs'' i]
    have inv: "LLL_invariant False i fs''"
      and meas: "LLL_measure i fs'' = LLL_measure i fs" by auto
    show ?thesis
    proof (cases "?x \<le> ?y")
      case True
      from increase_i[OF inv i _ True] True res meas
      show ?thesis by auto
    next
      case gt: False
      hence "?x > ?y" by auto
      from basis_reduction_swap[OF inv _ this i False] gt res meas
      show ?thesis by auto
    qed
  qed
qed

termination by (relation "measure (\<lambda> (upw,i,fs). LLL_measure i fs)", insert basis_reduction_step, auto split: prod.splits)

declare basis_reduction_main.simps[simp del]

lemma basis_reduction_main: assumes "LLL_invariant upw i fs" 
  and res: "basis_reduction_main (upw,i,fs) = fs'" 
shows "LLL_invariant True m fs'" 
  using assms
proof (induct "LLL_measure i fs" arbitrary: i fs upw rule: less_induct)
  case (less i fs upw)
  have id: "LLL_invariant upw i fs = True" using less by auto
  note res = less(3)[unfolded basis_reduction_main.simps[of upw i fs] id]
  note inv = less(2)
  note IH = less(1)
  show ?case
  proof (cases "i < m")
    case i: True
    obtain i' fs' upw' where step: "basis_reduction_step upw i fs = (upw',i',fs')" 
      (is "?step = _") by (cases ?step, auto)
    from IH[OF basis_reduction_step(2,1)[OF inv step i]] res[unfolded step] i
    show ?thesis by auto
  next
    case False
    with LLL_invD[OF inv] have i: "i = m" by auto
    with False res inv have "LLL_invariant upw m fs'" by auto
    thus "LLL_invariant True m fs'" unfolding LLL_invariant_def by auto
  qed
qed

lemma reduce_basis_inv: assumes res: "reduce_basis = fs" 
  shows "LLL_invariant True m fs" 
  using basis_reduction_main[OF LLL_inv_initial_state res[unfolded reduce_basis_def]] .

lemma reduce_basis: assumes res: "reduce_basis = fs"
  shows "lattice_of fs = L" 
  "reduced fs m" 
  "lin_indep fs" 
  "length fs = m" 
  using LLL_invD[OF reduce_basis_inv[OF res]] by blast+
  
lemma short_vector: assumes res: "short_vector = v" 
  and m0: "m \<noteq> 0"
shows "v \<in> carrier_vec n"
  "v \<in> L - {0\<^sub>v n}"  
  "h \<in> L - {0\<^sub>v n} \<Longrightarrow> rat_of_int (sq_norm v) \<le> \<alpha> ^ (m - 1) * rat_of_int (sq_norm h)" 
  "v \<noteq> 0\<^sub>v j" 
  using basis_reduction_short_vector[OF reduce_basis_inv[OF refl] res[symmetric, unfolded short_vector_def] m0] 
  by blast+
end

end
