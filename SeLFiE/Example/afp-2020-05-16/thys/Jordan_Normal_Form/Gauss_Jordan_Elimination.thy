(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Gauss-Jordan Algorithm\<close>

text \<open>We define the elementary row operations and use them to implement the
  Gauss-Jordan algorithm to transform matrices into row-echelon-form. 
  This algorithm is used to implement the inverse of a matrix and to derive
  certain results on determinants, as well as determine a basis of the kernel
  of a matrix.\<close> 

theory Gauss_Jordan_Elimination
imports Matrix
begin

subsection \<open>Row Operations\<close>

definition mat_multrow_gen :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "mat_multrow_gen mul k a A = mat (dim_row A) (dim_col A) 
     (\<lambda> (i,j). if k = i then mul a (A $$ (i,j)) else A $$ (i,j))"

abbreviation mat_multrow :: "nat \<Rightarrow> 'a :: semiring_1 \<Rightarrow> 'a mat \<Rightarrow> 'a mat" ("multrow") where
  "multrow \<equiv> mat_multrow_gen ((*))"

lemmas mat_multrow_def = mat_multrow_gen_def

definition multrow_mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: semiring_1 \<Rightarrow> 'a mat" where
  "multrow_mat n k a = mat n n 
     (\<lambda> (i,j). if k = i \<and> k = j then a else if i = j then 1 else 0)"

definition mat_swaprows :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" ("swaprows")where
  "swaprows k l A = mat (dim_row A) (dim_col A) 
    (\<lambda> (i,j). if k = i then A $$ (l,j) else if l = i then A $$ (k,j) else A $$ (i,j))"

definition swaprows_mat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a :: semiring_1 mat" where
  "swaprows_mat n k l = mat n n
    (\<lambda> (i,j). if k = i \<and> l = j \<or> k = j \<and> l = i \<or> i = j \<and> i \<noteq> k \<and> i \<noteq> l then 1 else 0)"

definition mat_addrow_gen :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "mat_addrow_gen ad mul a k l A = mat (dim_row A) (dim_col A) 
    (\<lambda> (i,j). if k = i then ad (mul a (A $$ (l,j))) (A $$ (i,j)) else A $$ (i,j))"

abbreviation mat_addrow :: "'a :: semiring_1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" ("addrow") where
  "addrow \<equiv> mat_addrow_gen (+) ((*))"

lemmas mat_addrow_def = mat_addrow_gen_def

definition addrow_mat :: "nat \<Rightarrow> 'a :: semiring_1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "addrow_mat n a k l = mat n n (\<lambda> (i,j). 
    (if k = i \<and> l = j then (+) a else id) (if i = j then 1 else 0))"

lemma index_mat_multrow[simp]: 
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> mat_multrow_gen mul k a A $$ (i,j) = (if k = i then mul a (A $$ (i,j)) else A $$ (i,j))"
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> mat_multrow_gen mul i a A $$ (i,j) = mul a (A $$ (i,j))"
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> k \<noteq> i \<Longrightarrow> mat_multrow_gen mul k a A $$ (i,j) = A $$ (i,j)"
  "dim_row (mat_multrow_gen mul k a A) = dim_row A" "dim_col (mat_multrow_gen mul k a A) = dim_col A"
  unfolding mat_multrow_def by auto

lemma index_mat_multrow_mat[simp]:
  "i < n \<Longrightarrow> j < n \<Longrightarrow> multrow_mat n k a $$ (i,j) = (if k = i \<and> k = j then a else if i = j 
     then 1 else 0)"
  "dim_row (multrow_mat n k a) = n" "dim_col (multrow_mat n k a) = n"
  unfolding multrow_mat_def by auto

lemma index_mat_swaprows[simp]: 
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> swaprows k l A $$ (i,j) = (if k = i then A $$ (l,j) else 
    if l = i then A $$ (k,j) else A $$ (i,j))"
  "dim_row (swaprows k l A) = dim_row A" "dim_col (swaprows k l A) = dim_col A"
  unfolding mat_swaprows_def by auto

lemma index_mat_swaprows_mat[simp]:
  "i < n \<Longrightarrow> j < n \<Longrightarrow> swaprows_mat n k l $$ (i,j) = 
    (if k = i \<and> l = j \<or> k = j \<and> l = i \<or> i = j \<and> i \<noteq> k \<and> i \<noteq> l then 1 else 0)"
  "dim_row (swaprows_mat n k l) = n" "dim_col (swaprows_mat n k l) = n"
  unfolding swaprows_mat_def by auto

lemma index_mat_addrow[simp]: 
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> mat_addrow_gen ad mul a k l A $$ (i,j) = (if k = i then 
    ad (mul a (A $$ (l,j))) (A $$ (i,j)) else A $$ (i,j))"
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> mat_addrow_gen ad mul a i l A $$ (i,j) = ad (mul a (A $$ (l,j))) (A $$ (i,j))"
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> k \<noteq> i \<Longrightarrow> mat_addrow_gen ad mul a k l A $$ (i,j) = A $$(i,j)"
  "dim_row (mat_addrow_gen ad mul a k l A) = dim_row A" "dim_col (mat_addrow_gen ad mul a k l A) = dim_col A"
  unfolding mat_addrow_def by auto

lemma index_mat_addrow_mat[simp]:
  "i < n \<Longrightarrow> j < n \<Longrightarrow> addrow_mat n a k l $$ (i,j) = 
    (if k = i \<and> l = j then (+) a else id) (if i = j then 1 else 0)"
  "dim_row (addrow_mat n a k l) = n" "dim_col (addrow_mat n a k l) = n"
  unfolding addrow_mat_def by auto

lemma multrow_carrier[simp]: "(mat_multrow_gen mul k a A \<in> carrier_mat n nc) = (A \<in> carrier_mat n nc)"
  unfolding carrier_mat_def by fastforce

lemma multrow_mat_carrier[simp]: "multrow_mat n k a \<in> carrier_mat n n"
  unfolding carrier_mat_def by auto

lemma addrow_mat_carrier[simp]: "addrow_mat n a k l \<in> carrier_mat n n"
  unfolding carrier_mat_def by auto

lemma swaprows_mat_carrier[simp]: "swaprows_mat n k l \<in> carrier_mat n n"
  unfolding carrier_mat_def by auto

lemma swaprows_carrier[simp]: "(swaprows k l A \<in> carrier_mat n nc) = (A \<in> carrier_mat n nc)"
  unfolding carrier_mat_def by fastforce

lemma addrow_carrier[simp]: "(mat_addrow_gen ad mul a k l A \<in> carrier_mat n nc) = (A \<in> carrier_mat n nc)"
  unfolding carrier_mat_def by fastforce

lemma row_multrow:  "k \<noteq> i \<Longrightarrow> i < n \<Longrightarrow> row (multrow_mat n k a) i = unit_vec n i"
  "k < n \<Longrightarrow> row (multrow_mat n k a) k = a \<cdot>\<^sub>v unit_vec n k"
  by (rule eq_vecI, auto)

lemma multrow_mat: assumes A: "A \<in> carrier_mat n nc"
  shows "multrow k a A = multrow_mat n k a * A"
  by (rule eq_matI, insert A, auto simp: row_multrow smult_scalar_prod_distrib[of _ n])

lemma row_addrow: 
  "k \<noteq> i \<Longrightarrow> i < n \<Longrightarrow> row (addrow_mat n a k l) i = unit_vec n i"
  "k < n \<Longrightarrow> l < n \<Longrightarrow> row (addrow_mat n a k l) k = a \<cdot>\<^sub>v unit_vec n l + unit_vec n k"
  by (rule eq_vecI, auto)

lemma addrow_mat: assumes A: "A \<in> carrier_mat n nc" 
  and l: "l < n"
  shows "addrow a k l A = addrow_mat n a k l * A"
  by (rule eq_matI, insert l A, auto simp: row_addrow 
  add_scalar_prod_distrib[of _ n] smult_scalar_prod_distrib[of _ n])

lemma row_swaprows: 
  "l < n \<Longrightarrow> row (swaprows_mat n l l) l = unit_vec n l"
  "i \<noteq> k \<Longrightarrow> i \<noteq> l \<Longrightarrow> i < n \<Longrightarrow> row (swaprows_mat n k l) i = unit_vec n i"
  "k < n \<Longrightarrow> l < n \<Longrightarrow> row (swaprows_mat n k l) l = unit_vec n k"
  "k < n \<Longrightarrow> l < n \<Longrightarrow> row (swaprows_mat n k l) k = unit_vec n l"
  by (rule eq_vecI, auto)

lemma swaprows_mat: assumes A: "A \<in> carrier_mat n nc" and k: "k < n" "l < n"
  shows "swaprows k l A = swaprows_mat n k l * A"
  by (rule eq_matI, insert A k, auto simp: row_swaprows)

lemma swaprows_mat_inv: assumes k: "k < n" and l: "l < n"
  shows "swaprows_mat n k l * swaprows_mat n k l = 1\<^sub>m n"
proof -
  have "swaprows_mat n k l * swaprows_mat n k l = 
    swaprows_mat n k l * (swaprows_mat n k l * 1\<^sub>m n)"
    by (simp add: right_mult_one_mat[of _ n])
  also have "swaprows_mat n k l * 1\<^sub>m n = swaprows k l (1\<^sub>m n)"
    by (rule swaprows_mat[symmetric, OF _ k l, of _ n], simp)
  also have "swaprows_mat n k l * \<dots> = swaprows k l \<dots>"
    by (rule swaprows_mat[symmetric, of _ _ n], insert k l, auto)
  also have "\<dots> = 1\<^sub>m n"
    by (rule eq_matI, insert k l, auto)
  finally show ?thesis .
qed

lemma swaprows_mat_Unit: assumes k: "k < n" and l: "l < n"
  shows "swaprows_mat n k l \<in> Units (ring_mat TYPE('a :: semiring_1) n b)"
proof -
  interpret m: semiring "ring_mat TYPE('a) n b" by (rule semiring_mat)
  show ?thesis unfolding Units_def
    by (rule, rule conjI[OF _ bexI[of _ "swaprows_mat n k l"]],
    auto simp: ring_mat_def swaprows_mat_inv[OF k l] swaprows_mat_inv[OF l k])
qed

lemma addrow_mat_inv: assumes k: "k < n" and l: "l < n" and neq: "k \<noteq> l"
  shows "addrow_mat n a k l * addrow_mat n (- (a :: 'a :: comm_ring_1)) k l = 1\<^sub>m n"
proof -
  have "addrow_mat n a k l * addrow_mat n (- a) k l = 
    addrow_mat n a k l * (addrow_mat n (- a) k l * 1\<^sub>m n)"
    by (simp add: right_mult_one_mat[of _ n])
  also have "addrow_mat n (- a) k l * 1\<^sub>m n = addrow (- a) k l (1\<^sub>m n)"
    by (rule addrow_mat[symmetric, of _ _ n], insert k l, auto)
  also have "addrow_mat n a k l * \<dots> = addrow a k l \<dots>"
    by (rule addrow_mat[symmetric, of _ _ n], insert k l, auto)
  also have "\<dots> = 1\<^sub>m n"
    by (rule eq_matI, insert k l neq, auto, algebra)
  finally show ?thesis .
qed

lemma addrow_mat_Unit: assumes k: "k < n" and l: "l < n" and neq: "k \<noteq> l"
  shows "addrow_mat n a k l \<in> Units (ring_mat TYPE('a :: comm_ring_1) n b)"
proof -
  interpret m: semiring "ring_mat TYPE('a) n b" by (rule semiring_mat)
  show ?thesis unfolding Units_def
    by (rule, rule conjI[OF _ bexI[of _ "addrow_mat n (- a) k l"]], insert neq,
    auto simp: ring_mat_def addrow_mat_inv[OF k l neq], 
    rule trans[OF _ addrow_mat_inv[OF k l neq, of "- a"]], auto)
qed

lemma multrow_mat_inv: assumes k: "k < n" and a: "(a :: 'a :: division_ring) \<noteq> 0"
  shows "multrow_mat n k a * multrow_mat n k (inverse a) = 1\<^sub>m n"
proof -
  have "multrow_mat n k a * multrow_mat n k (inverse a) = 
    multrow_mat n k a * (multrow_mat n k (inverse a) * 1\<^sub>m n)"
    using k by (simp add: right_mult_one_mat[of _ n])
  also have "multrow_mat n k (inverse a) * 1\<^sub>m n = multrow k (inverse a) (1\<^sub>m n)"
    by (rule multrow_mat[symmetric, of _ _ n], insert k, auto)
  also have "multrow_mat n k a * \<dots> = multrow k a \<dots>"
    by (rule multrow_mat[symmetric, of _ _ n], insert k, auto)
  also have "\<dots> = 1\<^sub>m n"
    by (rule eq_matI, insert a k a, auto)
  finally show ?thesis .
qed

lemma multrow_mat_Unit: assumes k: "k < n" and a: "(a :: 'a :: division_ring) \<noteq> 0"
  shows "multrow_mat n k a \<in> Units (ring_mat TYPE('a) n b)"
proof -
  from a have ia: "inverse a \<noteq> 0" by auto
  interpret m: semiring "ring_mat TYPE('a) n b" by (rule semiring_mat)
  show ?thesis unfolding Units_def
    by (rule, rule conjI[OF _ bexI[of _ "multrow_mat n k (inverse a)"]], insert a,
    auto simp: ring_mat_def multrow_mat_inv[OF k],
    rule trans[OF _ multrow_mat_inv[OF k ia]], insert a, auto)
qed

subsection \<open>Gauss-Jordan Elimination\<close>

fun eliminate_entries_rec where
  "eliminate_entries_rec B i [] = B"
| "eliminate_entries_rec B i ((ai'j,i') # is) = ( 
  eliminate_entries_rec (mat_addrow_gen ((+) :: 'b :: ring_1 \<Rightarrow> 'b \<Rightarrow> 'b) (*) ai'j i' i B) i is)"

context
  fixes minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

definition eliminate_entries_gen :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "eliminate_entries_gen v A I J = mat (dim_row A) (dim_col A) (\<lambda> (i, j).
     if i \<noteq> I then minus (A $$ (i,j)) (times (v i) (A $$ (I,j))) else A $$ (i,j))" 

lemma dim_eliminate_entries_gen[simp]: "dim_row (eliminate_entries_gen v B i as) = dim_row B"
  "dim_col (eliminate_entries_gen v B i as) = dim_col B"
  unfolding eliminate_entries_gen_def by auto
  
lemma dimc_eliminate_entries_rec[simp]: "dim_col (eliminate_entries_rec B i as) = dim_col B"
  by (induct as arbitrary: B, auto simp: Let_def)

lemma dimr_eliminate_entries_rec[simp]: "dim_row (eliminate_entries_rec B i as) = dim_row B"
  by (induct as arbitrary: B, auto simp: Let_def)

lemma carrier_eliminate_entries: "A \<in> carrier_mat nr nc \<Longrightarrow> eliminate_entries_gen v A i bs \<in> carrier_mat nr nc"
  "B \<in> carrier_mat nr nc \<Longrightarrow> eliminate_entries_rec B i as \<in> carrier_mat nr nc"
  unfolding carrier_mat_def by auto
end

abbreviation "eliminate_entries \<equiv> eliminate_entries_gen (-) ((*) :: 'a :: ring_1 \<Rightarrow> 'a \<Rightarrow> 'a)"

lemma eliminate_entries_convert: 
  assumes jA: "J < dim_col A" and *: "I < dim_row A" "dim_row B = dim_row A" 
  shows "eliminate_entries (\<lambda> i. A $$ (i,J)) B I J = 
    eliminate_entries_rec B I (map (\<lambda> i. (- A $$ (i, J), i)) (filter (\<lambda> i. i \<noteq> I) [0 ..< dim_row A]))"
proof -
  let ?ais = "\<lambda> is. map (\<lambda> i. (- A $$ (i, J), i)) (filter (\<lambda> i. i \<noteq> I) is)" 
  define one_go where "one_go = (\<lambda> B is. mat (dim_row B) (dim_col B) (\<lambda> (i, j).
    if i \<noteq> I \<and> i \<in> set is then B $$ (i,j) - (A $$ (i,J))  * B $$ (I,j) else B $$ (i,j)))"
  {
    fix "is" :: "nat list" 
    assume "distinct is"     
    from * this have "eliminate_entries_rec B I (?ais is) = one_go B is" 
    proof (induct "is" arbitrary: B)
      case Nil
      show ?case unfolding one_go_def
        by (rule eq_matI, auto)
    next
      case (Cons i "is")
      note I = Cons(2) note dim = Cons(3)      
      note II = Cons(2)[folded dim]
      let ?B = "addrow (- A $$ (i, J)) i I B" 
      from Cons(4) I dim have "I < dim_row A" "dim_row ?B = dim_row A" and dist: "distinct is" by auto
      note IH = Cons(1)[OF this]
      from Cons(4) have i: "i \<notin> set is" by auto
      show ?case 
      proof (cases "i = I")
        case False
        hence id: "?ais (i # is) = (- A $$ (i, J), i) # ?ais is" by simp
        show ?thesis unfolding id eliminate_entries_rec.simps IH
          unfolding one_go_def index_mat_addrow
        proof (rule eq_matI, goal_cases)
          case (1 ii jj)
          hence ii: "ii < dim_row B" and jj: "jj < dim_col B" and iiA: "ii < dim_row A" using dim by auto
          show ?case unfolding index_mat[OF ii jj] split
            index_mat_addrow(1)[OF ii jj] index_mat_addrow(1)[OF II jj]
            using i False by auto 
        qed auto
      next
        case True
        hence id: "?ais (i # is) = ?ais is" by simp        
        show ?thesis unfolding id Cons(1)[OF I dim dist]
          unfolding one_go_def True by auto
      qed
    qed
  } note main = this
  show ?thesis
    by (subst main, force, unfold one_go_def eliminate_entries_gen_def, rule eq_matI, 
    insert *, auto)
qed

lemma Unit_prod_eliminate_entries: "i < nr \<Longrightarrow> (\<And> a i'. (a, i') \<in> set is \<Longrightarrow> i' < nr \<and> i' \<noteq> i)
  \<Longrightarrow> \<exists> P \<in> Units (ring_mat TYPE('a :: comm_ring_1) nr b) . \<forall> B nc. B \<in> carrier_mat nr nc \<longrightarrow> eliminate_entries_rec B i is = P * B" 
proof (induct "is")
  case Nil
  thus ?case by (intro bexI[of _ "1\<^sub>m nr"], auto simp: Units_def ring_mat_def)
next
  case (Cons ai' "is")
  obtain a i' where ai': "ai' = (a,i')" by force
  let ?U = "Units (ring_mat TYPE('a) nr b)"
  interpret m: ring "ring_mat TYPE('a) nr b" by (rule ring_mat)
  from Cons(1)[OF Cons(2-3)] 
  obtain P where P: "P \<in> ?U" and id: "\<And> B nc . B \<in> carrier_mat nr nc \<Longrightarrow> 
    eliminate_entries_rec B i is = P * B" by force
  let ?Add = "addrow_mat nr a i' i"
  have Add: "?Add \<in> ?U"
    by (rule addrow_mat_Unit, insert Cons ai', auto)
  from m.Units_m_closed[OF P Add] have PI: "P * ?Add \<in> ?U" unfolding ring_mat_def by simp
  from m.Units_closed[OF P] have P: "P \<in> carrier_mat nr nr" unfolding ring_mat_def by simp
  show ?case
  proof (rule bexI[OF _ PI], intro allI impI)
    fix B :: "'a mat" and nc
    assume BB: "B \<in> carrier_mat nr nc"
    let ?B = "addrow a i' i B"
    from BB have B: "?B \<in> carrier_mat nr nc" by simp
    from id[OF B] have id: "eliminate_entries_rec ?B i is = P * ?B" .
    have id2: "eliminate_entries_rec B i (ai' # is) = eliminate_entries_rec ?B i is" unfolding ai' by simp
    show "eliminate_entries_rec B i (ai' # is) = P * ?Add * B"
      unfolding id2 id unfolding addrow_mat[OF BB Cons(2)]
      by (rule assoc_mult_mat[symmetric, OF P _ BB], auto)
  qed
qed

function gauss_jordan_main :: "'a :: field mat \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<times> 'a mat" where
  "gauss_jordan_main A B i j = (let nr = dim_row A; nc = dim_col A in
    if i < nr \<and> j < nc then let aij = A $$ (i,j) in if aij = 0 then
      (case [ i' . i' <- [Suc i ..< nr],  A $$ (i',j) \<noteq> 0] 
        of [] \<Rightarrow> gauss_jordan_main A B i (Suc j)
         | (i' # _) \<Rightarrow> gauss_jordan_main (swaprows i i' A) (swaprows i i' B) i j)
      else if aij = 1 then let 
        v = (\<lambda> i. A $$ (i,j)) in
        gauss_jordan_main 
        (eliminate_entries v A i j) (eliminate_entries v B i j) (Suc i) (Suc j)
      else let iaij = inverse aij in gauss_jordan_main (multrow i iaij A) (multrow i iaij B) i j
    else (A,B))"
  by pat_completeness auto

termination
proof -
  let ?R = "measures [\<lambda> (A :: 'a :: field mat,B,i,j). dim_col A - j, 
    \<lambda> (A,B,i,j). if A $$ (i,j) = 0 then 2 else if A $$ (i,j) = 1 then 0 else 1]"
  show ?thesis
  proof
    show "wf ?R" by auto
  next
    fix A B :: "'a mat" and i j nr nc a i' "is"
    assume *: "nr = dim_row A" "nc = dim_col A" "i < nr \<and> j < nc" "a = A $$ (i, j)" "a = 0"
      and ne: "[ i' . i' <- [Suc i ..< nr],  A $$ (i',j) \<noteq> 0] = i' # is"
    from ne have "i' \<in> set ([ i' . i' <- [Suc i ..< nr],  A $$ (i',j) \<noteq> 0])" by auto
    with *
    show "((swaprows i i' A, swaprows i i' B, i, j), A, B, i, j) \<in> ?R" by auto
  qed auto
qed

declare gauss_jordan_main.simps[simp del]

definition "gauss_jordan A B \<equiv> gauss_jordan_main A B 0 0"

lemma gauss_jordan_transform: assumes A: "A \<in> carrier_mat nr nc" and B: "B \<in> carrier_mat nr nc'"
  and res: "gauss_jordan (A :: 'a :: field mat) B = (A',B')"
  shows "\<exists> P \<in> Units (ring_mat TYPE('a) nr b). A' = P * A \<and> B' = P * B"
proof -
  let ?U = "Units (ring_mat TYPE('a) nr b)"
  interpret m: ring "ring_mat TYPE('a) nr b" by (rule ring_mat)
  {
    fix i j :: nat
    assume "gauss_jordan_main A B i j = (A',B')"
    with A B
    have "\<exists> P \<in> ?U. A' = P * A \<and> B' = P * B"
    proof (induction A B i j rule: gauss_jordan_main.induct)
      case (1 A B i j)
      note A = 1(5)
      hence dim: "dim_row A = nr" "dim_col A = nc" by auto
      note B = 1(6)
      hence dimB: "dim_row B = nr" "dim_col B = nc'" by auto
      note IH = 1(1-4)[OF dim[symmetric]]
      note res = 1(7)
      note simp = gauss_jordan_main.simps[of A B i j] Let_def
      let ?g = "gauss_jordan_main A B i j"
      show ?case 
      proof (cases "i < nr \<and> j < nc")
        case False
        with res have res: "A' = A" "B' = B" unfolding simp dim by auto
        show ?thesis unfolding res
          by (rule bexI[of _ "1\<^sub>m nr"], insert A B, auto simp: Units_def ring_mat_def)
      next
        case True note valid = this
        note IH = IH[OF valid refl]
        show ?thesis 
        proof (cases "A $$ (i,j) = 0")
          case False note nZ = this
          note IH = IH(3-4)[OF nZ]
          show ?thesis
          proof (cases "A $$ (i,j) = 1")
            case False note nO = this
            let ?inv = "inverse (A $$ (i,j))"
            from nO nZ valid res 
            have "gauss_jordan_main (multrow i ?inv A) (multrow i ?inv B) i j = (A',B')"
              unfolding simp dim by simp
            note IH = IH(2)[OF nO refl, unfolded multrow_carrier, OF A B this]
            from IH obtain P where P: "P \<in> ?U" and
              id: "A' = P * multrow i ?inv A" "B' = P * multrow i ?inv B" by blast
            let ?Inv = "multrow_mat nr i ?inv"
            from nZ valid have "i < nr" "?inv \<noteq> 0" by auto
            from multrow_mat_Unit[OF this]
            have Inv: "?Inv \<in> ?U" .
            from m.Units_m_closed[OF P Inv] have PI: "P * ?Inv \<in> ?U" unfolding ring_mat_def by simp
            from m.Units_closed[OF P] have P: "P \<in> carrier_mat nr nr" unfolding ring_mat_def by simp
            show ?thesis unfolding id unfolding multrow_mat[OF A] multrow_mat[OF B]
              by (rule bexI[OF _ PI], intro conjI, 
                rule assoc_mult_mat[symmetric, OF P _ A], simp, 
                rule assoc_mult_mat[symmetric, OF P _ B], simp)
          next
            case True note O = this
            let ?is = "filter (\<lambda> i'. i' \<noteq> i) [0 ..< nr]" 
            let ?ais = "map (\<lambda> i'. (-A $$ (i',j), i')) ?is" 
            let ?E = "\<lambda> B. eliminate_entries (\<lambda> i. A $$ (i,j)) B i j"
            let ?EE = "\<lambda> B. eliminate_entries_rec B i ?ais"
            let ?A = "?E A"
            let ?B = "?E B"
            let ?AA = "?EE A"
            let ?BB = "?EE B"
            from O nZ valid res have "gauss_jordan_main ?A ?B (Suc i) (Suc j) = (A',B')"
              unfolding simp dim by simp
            note IH = IH(1)[OF O refl carrier_eliminate_entries(1)[OF A] carrier_eliminate_entries(1)[OF B] this]
            from IH obtain P where P: "P \<in> ?U" and id: "A' = P * ?A" "B' = P * ?B" by blast
            have *: "j < dim_col A" "i < dim_row A" by (auto simp add: dim valid)
            have "\<exists>P\<in>?U. \<forall> B nc. B \<in> carrier_mat nr nc \<longrightarrow> ?EE B = P * B"
              by (rule Unit_prod_eliminate_entries, insert valid, auto)
            then obtain Q where Q: "Q \<in> ?U" and QQ: "\<And> B nc. B \<in> carrier_mat nr nc \<Longrightarrow> ?EE B = Q * B" by auto
            {
              fix B :: "'a mat" and nc
              assume B: "B \<in> carrier_mat nr nc" 
              with dim have "dim_row B = dim_row A" by auto
              from eliminate_entries_convert[OF * this]
              have "?E B = ?EE B" using dim by simp
              also have "\<dots> = Q * B" using QQ[OF B] by simp
              finally have "?E B = Q * B" .
            } note QQ = this              
            have id3: "?A = Q * A" by (rule QQ[OF A])
            have id4: "?B = Q * B" by (rule QQ[OF B])
            from m.Units_closed[OF P] have Pc: "P \<in> carrier_mat nr nr" unfolding ring_mat_def by simp
            from m.Units_closed[OF Q] have Qc: "Q \<in> carrier_mat nr nr" unfolding ring_mat_def by simp
            from m.Units_m_closed[OF P Q] have PQ: "P * Q \<in> ?U" unfolding ring_mat_def by simp
            show ?thesis unfolding id unfolding id3 id4 
              by (rule bexI[OF _ PQ], rule conjI, 
              rule assoc_mult_mat[symmetric, OF Pc Qc A],
              rule assoc_mult_mat[symmetric, OF Pc Qc B])
          qed
        next
          case True note Z = this
          note IH = IH(1-2)[OF Z]
          let ?is = "[ i' . i' <- [Suc i ..< nr],  A $$ (i',j) \<noteq> 0]"
          show ?thesis
          proof (cases ?is)
            case Nil 
            from Z valid res have id: "gauss_jordan_main A B i (Suc j) = (A',B')" unfolding simp dim Nil by simp
            from IH(1)[OF Nil A B this] show ?thesis unfolding id .
          next
            case (Cons i' iis)
            from Z valid res have "gauss_jordan_main (swaprows i i' A) (swaprows i i' B) i j = (A',B')" 
              unfolding simp dim Cons by simp
            from IH(2)[OF Cons, unfolded swaprows_carrier, OF A B this]
            obtain P where P: "P \<in> ?U" and
              id: "A' = P * swaprows i i' A" "B' = P * swaprows i i' B" by blast
            let ?Swap = "swaprows_mat nr i i'"
            from Cons have "i' \<in> set ?is" by auto
            with valid have i': "i < nr" "i' < nr" by auto
            from swaprows_mat_Unit[OF this] have Swap: "?Swap \<in> ?U" .
            from m.Units_m_closed[OF P Swap] have PI: "P * ?Swap \<in> ?U" unfolding ring_mat_def by simp
            from m.Units_closed[OF P] have P: "P \<in> carrier_mat nr nr" unfolding ring_mat_def by simp
            show ?thesis unfolding id swaprows_mat[OF A i'] swaprows_mat[OF B i']
              by (rule bexI[OF _ PI], rule conjI, 
              rule assoc_mult_mat[symmetric, OF P _ A], simp,
              rule assoc_mult_mat[symmetric, OF P _ B], simp)
          qed
        qed
      qed
    qed
  }
  from this[of 0 0, folded gauss_jordan_def, OF res] show ?thesis .
qed

lemma gauss_jordan_carrier: assumes A: "(A :: 'a :: field mat) \<in> carrier_mat nr nc"
  and B: "B \<in> carrier_mat nr nc'" 
  and res: "gauss_jordan A B = (A',B')"
  shows "A' \<in> carrier_mat nr nc" "B' \<in> carrier_mat nr nc'"
proof -
  from gauss_jordan_transform[OF A B res, of undefined]
  obtain P where P: "P \<in> Units (ring_mat TYPE('a) nr undefined)"
    and id: "A' = P * A" "B' = P * B" by auto
  from P have P: "P \<in> carrier_mat nr nr" unfolding Units_def ring_mat_def by auto
  show "A' \<in> carrier_mat nr nc" "B' \<in> carrier_mat nr nc'" unfolding id
    using P A B by auto
qed


definition pivot_fun :: "'a :: {zero,one} mat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "pivot_fun A f nc \<equiv> let nr = dim_row A in 
    (\<forall> i < nr. f i \<le> nc \<and> 
      (f i < nc \<longrightarrow> A $$ (i, f i) = 1 \<and> (\<forall> i' < nr. i' \<noteq> i \<longrightarrow> A $$ (i',f i) = 0)) \<and> 
      (\<forall> j < f i. A $$ (i, j) = 0) \<and>
      (Suc i < nr \<longrightarrow> f (Suc i) > f i \<or> f (Suc i) = nc))"

lemma pivot_funI: assumes d: "dim_row A = nr"
  and *: "\<And> i. i < nr \<Longrightarrow> f i \<le> nc"
      "\<And> i j. i < nr \<Longrightarrow> j < f i \<Longrightarrow> A $$ (i,j) = 0"
      "\<And> i. i < nr \<Longrightarrow> Suc i < nr \<Longrightarrow> f (Suc i) > f i \<or> f (Suc i) = nc"
      "\<And> i. i < nr \<Longrightarrow> f i < nc \<Longrightarrow> A $$ (i, f i) = 1"
      "\<And> i i'. i < nr \<Longrightarrow> f i < nc \<Longrightarrow> i' < nr \<Longrightarrow> i' \<noteq> i \<Longrightarrow> A $$ (i',f i) = 0"
  shows "pivot_fun A f nc"
  unfolding pivot_fun_def Let_def d using * by blast

lemma pivot_funD: assumes d: "dim_row A = nr"
  and p: "pivot_fun A f nc"
  shows "\<And> i. i < nr \<Longrightarrow> f i \<le> nc"
      "\<And> i j. i < nr \<Longrightarrow> j < f i \<Longrightarrow> A $$ (i,j) = 0"
      "\<And> i. i < nr \<Longrightarrow> Suc i < nr \<Longrightarrow> f (Suc i) > f i \<or> f (Suc i) = nc"
      "\<And> i. i < nr \<Longrightarrow> f i < nc \<Longrightarrow> A $$ (i, f i) = 1"
      "\<And> i i'. i < nr \<Longrightarrow> f i < nc \<Longrightarrow> i' < nr \<Longrightarrow> i' \<noteq> i \<Longrightarrow> A $$ (i',f i) = 0"
  using p unfolding pivot_fun_def Let_def d by blast+

lemma pivot_fun_multrow: assumes p: "pivot_fun A f jj"
  and d: "dim_row A = nr" "dim_col A = nc"
  and fi: "f i0 = jj"
  and jj: "jj \<le> nc"
  shows "pivot_fun (multrow i0 a A) f jj"
proof -
  note p = pivot_funD[OF d(1) p]
  let ?A = "multrow i0 a A"
  have "dim_row ?A = nr" using d by simp
  thus ?thesis
  proof (rule pivot_funI)
    fix i
    assume i: "i < nr"
    note p = p[OF i]
    show "f i \<le> jj" by fact
    show "Suc i < nr \<Longrightarrow> f i < f (Suc i) \<or> f (Suc i) = jj" by fact
    {
      fix i'
      assume *: "f i < jj" "i' < nr" "i' \<noteq> i" 
      from p(5)[OF this]
      show "?A $$ (i', f i) = 0"
        by (subst index_mat_multrow(1), insert * d jj, auto)
    }
    {
      assume *: "f i < jj"
      from p(4)[OF this] have A: "A $$ (i, f i) = 1" by auto
      show "?A $$ (i, f i) = 1"
        by (subst index_mat_multrow(1), insert * d i A jj fi, auto)
    }
    {
      fix j
      assume j: "j < f i"
      from p(2)[OF j]
      show "?A $$ (i, j) = 0"
        by (subst index_mat_multrow(1), insert j d i p jj fi, auto)
    }
  qed
qed

lemma pivot_fun_swaprows: assumes p: "pivot_fun A f jj"
  and d: "dim_row A = nr" "dim_col A = nc"
  and flk: "f l = jj" "f k = jj"
  and nr: "l < nr" "k < nr"
  and jj: "jj \<le> nc"
  shows "pivot_fun (swaprows l k A) f jj"
proof -
  note pivot = pivot_funD[OF d(1) p]
  let ?A = "swaprows l k A"
  have "dim_row ?A = nr" using d by simp
  thus ?thesis
  proof (rule pivot_funI)
    fix i
    assume i: "i < nr"
    note p = pivot[OF i]
    show "f i \<le> jj" by fact
    show "Suc i < nr \<Longrightarrow> f i < f (Suc i) \<or> f (Suc i) = jj" by fact
    {
      fix i'
      assume *: "f i < jj" "i' < nr" "i' \<noteq> i" 
      from *(1) flk have diff: "l \<noteq> i" "k \<noteq> i" by auto
      from p(5)[OF *] p(5)[OF *(1) nr(1) diff(1)] p(5)[OF *(1) nr(2) diff(2)]
      show "?A $$ (i', f i) = 0"  
        by (subst index_mat_swaprows(1), insert * d jj, auto)
    }
    {
      assume *: "f i < jj"
      from p(4)[OF this] have A: "A $$ (i, f i) = 1" by auto
      show "?A $$ (i, f i) = 1"
        by (subst index_mat_swaprows(1), insert * d i A jj flk, auto)
    }
    {
      fix j
      assume j: "j < f i"
      with p(1) flk have le: "j < f l" "j < f k" by auto
      from p(2)[OF j] pivot(2)[OF nr(1) le(1)] pivot(2)[OF nr(2) le(2)]
      show "?A $$ (i, j) = 0" 
        by (subst index_mat_swaprows(1), insert j d i p jj, auto) 
    }
  qed
qed

lemma pivot_fun_eliminate_entries: assumes p: "pivot_fun A f jj"
  and d: "dim_row A = nr" "dim_col A = nc"
  and fl: "f l = jj"
  and nr: "l < nr"
  and jj: "jj \<le> nc"
shows "pivot_fun (eliminate_entries vs A l j) f jj" 
proof -
  note pD = pivot_funD[OF d(1) p]
  {
    fix i j
    assume *: "i < nr" "j < f i"
    from pD(1)[OF this(1)] this(2) jj have j: "j < nc" by auto
    from pD nr fl * j have "A $$ (l, j) = 0" by (meson less_le_trans)
    note j this
  } note hint = this
  show ?thesis by (rule pivot_funI, insert fl nr jj pD, auto simp: eliminate_entries_gen_def d hint)
qed
    
definition row_echelon_form :: "'a :: {zero,one} mat \<Rightarrow> bool" where
  "row_echelon_form A \<equiv> \<exists> f. pivot_fun A f (dim_col A)"

lemma pivot_fun_init: "pivot_fun A (\<lambda> _. 0) 0"
  by (rule pivot_funI, auto)

lemma gauss_jordan_main_row_echelon: 
  assumes 
    "A \<in> carrier_mat nr nc"
    "gauss_jordan_main A B i j = (A',B')"
    "pivot_fun A f j" 
    "\<And> i'. i' < i \<Longrightarrow> f i' < j" "\<And> i'. i' \<ge> i \<Longrightarrow> f i' = j"
    "i \<le> nr" "j \<le> nc"
  shows "row_echelon_form A'"
proof -
  fix b
  interpret m: ring "ring_mat TYPE('a) nr b" by (rule ring_mat)
  show ?thesis
    using assms
  proof (induct A B i j arbitrary: f rule: gauss_jordan_main.induct)
    case (1 A B i j f)
    note A = 1(5)
    hence dim: "dim_row A = nr" "dim_col A = nc" by auto
    note res = 1(6)
    note pivot = 1(7)
    note f = 1(8-9)
    note ij = 1(10-11)
    note IH = 1(1-4)[OF dim[symmetric]]
    note simp = gauss_jordan_main.simps[of A B i j] Let_def
    let ?g = "gauss_jordan_main A B i j"
    show ?case 
    proof (cases "i < nr \<and> j < nc")
      case False note nij = this
      with res have id: "A' = A" unfolding simp dim by auto
      have "pivot_fun A f nc"
      proof (cases "j \<ge> nc")
        case True
        with ij have j: "j = nc" by auto
        with pivot show "pivot_fun A f nc" by simp
      next
        case False
        hence j: "j < nc" by simp
        from False nij ij have i: "i = nr" by auto
        note f = f[unfolded i]
        note p = pivot_funD[OF dim(1) pivot]
        show ?thesis
        proof (rule pivot_funI[OF dim(1)])
          fix i
          assume i: "i < nr"
          note p = p[OF i]
          from p(1) j show "f i \<le> nc" by simp
          from f(1)[OF i] have fij: "f i < j" .
          from p(4)[OF fij] show "A $$ (i, f i) = 1" .
          from p(5)[OF fij] show "\<And> i'. i' < nr \<Longrightarrow> i' \<noteq> i \<Longrightarrow> A $$ (i', f i) = 0" .
          show "\<And> j. j < f i \<Longrightarrow> A $$ (i, j) = 0" by (rule p(2))
          assume "Suc i < nr"
          with p(3)[OF this] f
          show "f i < f (Suc i) \<or> f (Suc i) = nc" by auto
        qed          
      qed
      thus ?thesis using pivot unfolding id row_echelon_form_def dim by blast
    next
      case True note valid = this
      hence sij: "Suc i \<le> nr" "Suc j \<le> nc" by auto
      note IH = IH[OF valid refl]
      show ?thesis 
      proof (cases "A $$ (i,j) = 0")
        case False note nZ = this
        note IH = IH(3-4)[OF nZ]
        show ?thesis
        proof (cases "A $$ (i,j) = 1")
          case False note nO = this
          let ?inv = "inverse (A $$ (i,j))"
          let ?A = "multrow i ?inv A"
          from nO nZ valid res have id: "gauss_jordan_main (multrow i ?inv A) (multrow i ?inv B) i j = (A', B')"
            unfolding simp dim by simp
          have "pivot_fun ?A f j"
            by (rule pivot_fun_multrow[OF pivot dim f(2) ij(2)], auto)
          note IH = IH(2)[OF nO refl, unfolded multrow_carrier, OF A id this f ij]
          show ?thesis unfolding id using IH .
        next
          case True note O = this
          let ?E = "\<lambda> B. eliminate_entries (\<lambda> i. A $$ (i,j)) B i j" 
          let ?A = "?E A"
          let ?B = "?E B"
          define E where "E = ?A"
          let ?f = "\<lambda> i'. if i' = i then j else if i' > i then Suc j else f i'"
          have pivot: "pivot_fun E f j" unfolding E_def          
            by (rule pivot_fun_eliminate_entries[OF pivot dim f(2)], insert valid, auto)
          {
            fix i'
            assume i': "i' < nr"
            have "E $$ (i', j) = (if i' = i then 1 else 0)"
              unfolding E_def eliminate_entries_gen_def using dim O i' valid by auto
          } note Ej = this
          have E: "E \<in> carrier_mat nr nc" unfolding E_def by (rule carrier_eliminate_entries[OF A])
          hence dimE: "dim_row E = nr" "dim_col E = nc" by auto
          note pivot = pivot_funD[OF dimE(1) pivot]
          have "pivot_fun E ?f (Suc j)"
          proof (rule pivot_funI[OF dimE(1)])
            fix ii
            assume ii: "ii < nr"
            note p = pivot[OF ii]
            show "?f ii \<le> Suc j" using p(1) by simp
            {
              fix jj
              assume jj: "jj < ?f ii"
              show "E $$ (ii,jj) = 0"
              proof (cases "ii < i")
                case True
                with jj have "jj < f ii" by auto
                from p(2)[OF this] show ?thesis .
              next
                case False note ge = this
                with f have fiij: "f ii = j" by simp 
                show ?thesis
                proof (cases "i < ii")
                  case True
                  with jj have jj: "jj \<le> j" by auto
                  show ?thesis
                  proof (cases "jj < j")
                    case True
                    with p(2)[of jj] fiij show ?thesis by auto
                  next
                    case False
                    with jj have jj: "jj = j" by auto
                    with Ej[OF ii] True show ?thesis by auto
                  qed
                next
                  case False
                  with ge have ii: "ii = i" by simp
                  with jj have jj: "jj < j" by simp
                  from p(2)[of jj] ii jj fiij show ?thesis by auto
                qed
              qed
            }
            {
              assume "Suc ii < nr"
              from p(3)[OF this] f
              show "?f (Suc ii) > ?f ii \<or> ?f (Suc ii) = Suc j" by auto
            }
            {
              assume fii: "?f ii < Suc j"
              show "E $$ (ii, ?f ii) = 1"
              proof (cases "ii = i")
                case True
                with Ej[of i] valid show ?thesis by auto
              next
                case False
                with fii have ii: "ii < i" by (auto split: if_splits)
                from f(1)[OF this] have "f ii < j" by auto
                from p(4)[OF this] ii show ?thesis by simp
              qed
            }
            {
               fix i'
               assume *: "?f ii < Suc j" "i' < nr" "i' \<noteq> ii"
               show "E $$ (i', ?f ii) = 0"
               proof (cases "ii = i")
                 case False
                 with *(1) have iii: "ii < i" by (auto split: if_splits)
                 from f(1)[OF this] have "f ii < j" by auto
                 from p(5)[OF this *(2-3)] show ?thesis using iii by simp
               next
                 case True
                 with *(2-3) Ej[of i'] show ?thesis by auto
               qed
            }
          qed 
          note IH = IH(1)[OF O refl, folded E_def, OF E _ this _ _ sij]     
          from O nZ valid res have "gauss_jordan_main E ?B (Suc i) (Suc j) = (A', B')"
            unfolding E_def simp dim by simp
          note IH = IH[OF this]
          show ?thesis  
          proof (rule IH)
            fix i'
            assume "i' < Suc i"
            thus "?f i' < Suc j" using f[of i'] by (cases "i' < i", auto)
          qed auto
        qed
      next
        case True note Z = this
        note IH = IH(1-2)[OF Z]
        let ?is = "[ i' . i' <- [Suc i ..< nr],  A $$ (i',j) \<noteq> 0]"
        show ?thesis
        proof (cases ?is)
          case Nil
          {
            fix i'
            assume "i \<le> i'" and "i' < nr"
            hence "i' = i \<or> i' \<in> {Suc i ..< nr}" by auto
            from this arg_cong[OF Nil, of set] Z have "A $$ (i',j) = 0" by auto
          } note zero = this
          let ?f = "\<lambda> i'. if i' < i then f i' else Suc j"
          note p = pivot_funD[OF dim(1) pivot]
          have "pivot_fun A ?f (Suc j)"
          proof (rule pivot_funI[OF dim(1)])
            fix ii
            assume ii: "ii < nr"
            note p = p[OF this]
            show "?f ii \<le> Suc j" using p(1) by simp
            {
              fix jj
              assume jj: "jj < ?f ii"              
              show "A $$ (ii,jj) = 0"
              proof (cases "ii < i")
                case True
                with jj have "jj < f ii" by auto
                from p(2)[OF this] show ?thesis .
              next
                case False
                with jj have ii': "ii \<ge> i" and jjj: "jj \<le> j" by auto
                from zero[OF ii' ii] have Az: "A $$ (ii,j) = 0" .
                show ?thesis
                proof (cases "jj < j")
                  case False
                  with jjj have "jj = j" by auto
                  with Az show ?thesis by simp
                next
                  case True
                  show ?thesis
                    by (rule p(2), insert True False f, auto)
                qed
              qed
            }
            {
              assume sii: "Suc ii < nr"
              show "?f ii < ?f (Suc ii) \<or> ?f (Suc ii) = Suc j"
                using p(3)[OF sii] f by auto
            }
            {
              assume fii: "?f ii < Suc j"
              thus "A $$ (ii, ?f ii) = 1"
                using p(4) f by (cases "ii < i", auto)
              fix i'
              assume "i' < nr" "i' \<noteq> ii"
              from p(5)[OF _ this] f fii
              show "A $$ (i', ?f ii) = 0" 
                by (cases "ii < i", auto)
            }
          qed
          note IH = IH(1)[OF Nil A _ this _ _ ij(1) sij(2)]
          from Z valid res have "gauss_jordan_main A B i (Suc j) = (A',B')" unfolding simp dim Nil by simp
          note IH = IH[OF this]
          show ?thesis  
            by (rule IH, insert f, force+)
        next
          case (Cons i' iis)
          from arg_cong[OF this, of set] have i': "i' \<ge> Suc i" "i' < nr" by auto
          from f[of i] f[of "i'"] i' have fij: "f i = j" "f i' = j" by auto 
          let ?A = "swaprows i i' A"
          let ?B = "swaprows i i' B"
          have "pivot_fun ?A f j"
            by (rule pivot_fun_swaprows[OF pivot dim fij], insert i' ij, auto)
          note IH = IH(2)[OF Cons, unfolded swaprows_carrier, OF A _ this f ij]
          from Z valid res have id: "gauss_jordan_main ?A ?B i j = (A', B')" unfolding simp dim Cons by simp
          note IH = IH[OF this]
          show ?thesis using IH .
        qed
      qed
    qed
  qed
qed

lemma gauss_jordan_row_echelon: 
  assumes A: "A \<in> carrier_mat nr nc" 
  and res: "gauss_jordan A B = (A', B')"
  shows "row_echelon_form A'"
  by (rule gauss_jordan_main_row_echelon[OF A res[unfolded gauss_jordan_def] pivot_fun_init], auto)

lemma pivot_bound: assumes dim: "dim_row A = nr"
  and pivot: "pivot_fun A f n"
  shows "i + j < nr \<Longrightarrow> f (i + j) = n \<or> f (i + j) \<ge> j + f i"
proof (induct j)
  case (Suc j)
  hence IH: "f (i + j) = n \<or> j + f i \<le> f (i + j)" 
    and lt: "i + j < nr" "Suc (i + j) < nr" by auto
  note p = pivot_funD[OF dim pivot]
  from p(3)[OF lt] IH p(1)[OF lt(2)] show ?case by auto
qed simp

context
  fixes zero :: 'a
  and A :: "'a mat"
  and nr nc :: nat
begin
function pivot_positions_main_gen :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "pivot_positions_main_gen i j = (
     if i < nr then
       if j < nc then 
         if A $$ (i,j) = zero then 
           pivot_positions_main_gen i (Suc j)
         else (i,j) # pivot_positions_main_gen (Suc i) (Suc j)
       else []
     else [])" by pat_completeness auto

termination by (relation "measures [(\<lambda> (i,j). Suc nr - i), (\<lambda> (i,j). Suc nc - j)]", auto)

declare pivot_positions_main_gen.simps[simp del]
end

context
  fixes A :: "'a :: semiring_1 mat"
  and nr nc :: nat
begin

abbreviation "pivot_positions_main \<equiv> pivot_positions_main_gen (0 :: 'a) A nr nc"

lemma pivot_positions_main: assumes A: "A \<in> carrier_mat nr nc"
  and pivot: "pivot_fun A f nc"
  shows "j \<le> f i \<or> i \<ge> nr \<Longrightarrow> 
    set (pivot_positions_main i j) = {(i', f i') | i'. i \<le> i' \<and> i' < nr} - UNIV \<times> {nc}
    \<and> distinct (map snd (pivot_positions_main i j))
    \<and> distinct (map fst (pivot_positions_main i j))"
proof (induct i j rule: pivot_positions_main_gen.induct[of nr nc A 0])
  case (1 i j)
  let ?a = "A $$ (i,j)"
  let ?pivot = "\<lambda> i j. pivot_positions_main i j"
  let ?set = "\<lambda> i. {(i',f i') | i'. i \<le> i' \<and> i' < nr}"
  let ?s = "?set i"
  let ?set = "\<lambda> i. {(i',f i') | i'. i \<le> i' \<and> i' < nr}"
  let ?s = "?set i"
  let ?p = "?pivot i j"
  from A have dA: "dim_row A = nr" by simp
  note [simp] = pivot_positions_main_gen.simps[of 0 A nr nc i j]
  show ?case
  proof (cases "i < nr")
    case True note i = this
    note IH = 1(1-2)[OF True]
    have jfi: "j \<le> f i" using 1(3) i by auto
    note pivotB = pivot_bound[OF dA pivot]
    note pivot' = pivot_funD[OF dA pivot]
    note pivot = pivot'[OF True]
    have id1: "[i ..< nr] = i # [Suc i ..< nr]" using i by (rule upt_conv_Cons)
    show ?thesis
    proof (cases "j < nc")
      case True note j = this
      note IH = IH(1-2)[OF True]
      show ?thesis
      proof (cases "?a = 0")
        case True note a = this
        from i j a have p: "?p = ?pivot i (Suc j)" by simp
        {
          assume "f i = j"
          with pivot(4) j have "?a = 1" by simp
          with a have False by simp
        }
        with jfi have "Suc j \<le> f i \<or> i \<ge> nr" by fastforce
        note IH = IH(1)[OF True this]
        thus ?thesis unfolding p .
      next
        case False note a = this
        from i j a have p: "?p = (i,j) # ?pivot (Suc i) (Suc j)" by simp
        from pivot(2)[of j] jfi a have jfi: "j = f i" by force
        from pivotB[of i "Suc 0"] jfi have "Suc j \<le> f (Suc i) \<or> nr \<le> Suc i" 
          using Suc_le_eq j leI by auto
        note IH = IH(2)[OF False this]
        {
          fix i'
          assume *: "f i = f i'" "Suc i \<le> i'" "i' < nr" 
          hence "i + (i' - i) = i'" by auto
          from pivotB[of i "i' - i", unfolded this] * jfi j have False by auto
        } note distinct = this
        have id2: "?s = insert (i,j) (?set (Suc i))" using i jfi not_less_eq_eq
          by fastforce
        show ?thesis using IH j jfi i unfolding p id1 id2 by (auto intro: distinct)
      qed
    next
      case False note j = this
      from pivot(1) j jfi have *: "f i = nc" "nc = j" by auto
      from i j have p: "?p = []" by simp
      from pivotB[of i "Suc 0"] * have "j \<le> f (Suc i) \<or> nr \<le> Suc i" by auto
      {
        fix i'
        assume **: "i \<le> i'" "i' < nr" 
        hence "i + (i' - i) = i'" by auto
        from pivotB[of i "i' - i", unfolded this] ** * have "nc \<le> f i'" by auto
        with pivot'(1)[OF \<open>i' < nr\<close>] have "f i' = nc" by auto
      }
      thus ?thesis using IH unfolding p id1 by auto
    qed
  qed auto
qed
end

lemma pivot_fun_zero_row_iff: assumes pivot: "pivot_fun (A :: 'a :: semiring_1 mat) f nc"
  and A: "A \<in> carrier_mat nr nc"
  and i: "i < nr"
  shows "f i = nc \<longleftrightarrow> row A i = 0\<^sub>v nc"
proof -
  from A have dim: "dim_row A = nr" by auto
  note pivot = pivot_funD[OF dim pivot i]
  {
    assume "f i = nc"
    from pivot(2)[unfolded this]
    have "row A i = 0\<^sub>v nc"
      by (intro eq_vecI, insert A, auto simp: row_def)
  }
  moreover
  {
    assume row: "row A i = 0\<^sub>v nc"
    assume "f i \<noteq> nc"
    with pivot(1) have "f i < nc" by auto
    with pivot(4)[OF this] i A arg_cong[OF row, of "\<lambda> v. v $ f i"] have False by auto
  }
  ultimately show ?thesis by auto
qed

definition pivot_positions_gen :: "'a \<Rightarrow> 'a mat \<Rightarrow> (nat \<times> nat) list" where
  "pivot_positions_gen zer A \<equiv> pivot_positions_main_gen zer A (dim_row A) (dim_col A) 0 0"

abbreviation pivot_positions :: "'a :: semiring_1 mat \<Rightarrow> (nat \<times> nat) list" where
  "pivot_positions \<equiv> pivot_positions_gen 0"

lemmas pivot_positions_def = pivot_positions_gen_def

lemma pivot_positions: assumes A: "A \<in> carrier_mat nr nc"
  and pivot: "pivot_fun A f nc"
  shows 
    "set (pivot_positions A) = {(i, f i) | i. i < nr \<and> f i \<noteq> nc}"
    "distinct (map fst (pivot_positions A))"
    "distinct (map snd (pivot_positions A))"
    "length (pivot_positions A) = card { i. i < nr \<and> row A i \<noteq> 0\<^sub>v nc}"
proof -
  from A have dim: "dim_row A = nr" by auto
  let ?pp = "pivot_positions A"
  show id: "set ?pp = {(i, f i) | i. i < nr \<and> f i \<noteq> nc}"
    and dist: "distinct (map fst ?pp)"
    and "distinct (map snd ?pp)"  
  using pivot_positions_main[OF A pivot, of 0 0] A
  unfolding pivot_positions_def by auto
  have "length ?pp = length (map fst ?pp)" by simp
  also have "\<dots> = card (fst ` set ?pp)" using distinct_card[OF dist] by simp
  also have "fst ` set ?pp = { i. i < nr \<and> f i \<noteq> nc}" unfolding id by force
  also have "\<dots> = { i. i < nr \<and> row A i \<noteq> 0\<^sub>v nc}"
    using pivot_fun_zero_row_iff[OF pivot A] by auto
  finally show "length ?pp = card {i. i < nr \<and> row A i \<noteq> 0\<^sub>v nc}" .
qed

context 
  fixes uminus :: "'a \<Rightarrow> 'a"
  and zero :: 'a
  and one :: 'a
begin
definition non_pivot_base_gen :: "'a mat \<Rightarrow> (nat \<times> nat)list \<Rightarrow> nat \<Rightarrow> 'a vec" where
  "non_pivot_base_gen A pivots \<equiv> let nr = dim_row A; nc = dim_col A; 
     invers = map_of (map prod.swap pivots)
     in (\<lambda> qj. vec nc (\<lambda> i. 
     if i = qj then one else (case invers i of Some j => uminus (A $$ (j,qj)) | None \<Rightarrow> zero)))"

definition find_base_vectors_gen :: "'a mat \<Rightarrow> 'a vec list" where
  "find_base_vectors_gen A \<equiv> 
    let 
      pp = pivot_positions_gen zero A;     
      cands = filter (\<lambda> j. j \<notin> set (map snd pp)) [0 ..< dim_col A]
    in map (non_pivot_base_gen A pp) cands"
end

abbreviation "non_pivot_base \<equiv> non_pivot_base_gen uminus 0 (1 :: 'a :: comm_ring_1)"
abbreviation "find_base_vectors \<equiv> find_base_vectors_gen uminus 0 (1 :: 'a :: comm_ring_1)"

lemmas non_pivot_base_def = non_pivot_base_gen_def
lemmas find_base_vectors_def = find_base_vectors_gen_def

text \<open>The soundness of @{const find_base_vectors} is proven in theory Matrix-Kern,
  where it is shown that @{const find_base_vectors} is a basis of the kern of $A$.\<close>

definition find_base_vector :: "'a :: comm_ring_1 mat \<Rightarrow> 'a vec" where
  "find_base_vector A \<equiv> 
    let 
      pp = pivot_positions A;     
      cands = filter (\<lambda> j. j \<notin> set (map snd pp)) [0 ..< dim_col A]
    in non_pivot_base A pp (hd cands)"

context
  fixes A :: "'a :: field mat" and nr nc :: nat and p :: "nat \<Rightarrow> nat"
  assumes ref: "row_echelon_form A"
  and A: "A \<in> carrier_mat nr nc"
begin

lemma non_pivot_base:
  defines pp: "pp \<equiv> pivot_positions A"
  assumes qj: "qj < nc" "qj \<notin> snd ` set pp" 
  shows "non_pivot_base A pp qj \<in> carrier_vec nc"
    "non_pivot_base A pp qj $ qj = 1"
    "A *\<^sub>v non_pivot_base A pp qj = 0\<^sub>v nr"
    "\<And> qj'. qj' < nc \<Longrightarrow> qj' \<notin> snd ` set pp \<Longrightarrow> qj \<noteq> qj' \<Longrightarrow> non_pivot_base A pp qj $ qj' = 0"
proof -
  from A have dim: "dim_row A = nr" "dim_col A = nc" by auto
  from ref[unfolded row_echelon_form_def] obtain p 
  where pivot: "pivot_fun A p nc" using dim by auto
  note pivot' = pivot_funD[OF dim(1) pivot]
  note pp = pivot_positions[OF A pivot, folded pp]
  let ?p = "\<lambda> i. i < nr \<and> p i = nc \<or> i = nr"
  let ?spp = "map prod.swap pp"
  let ?map = "map_of ?spp"
  define I where "I = (\<lambda> i. case map_of (map prod.swap pp) i of Some j \<Rightarrow> - A $$ (j,qj) | None \<Rightarrow> 0)"
  have d: "non_pivot_base A pp qj = vec nc (\<lambda> i. if i = qj then 1 else I i)"
    unfolding non_pivot_base_def Let_def dim I_def ..
  from pp have dist: "distinct (map fst ?spp)" 
    unfolding map_map o_def prod.swap_def by auto
  let ?r = "set (map snd pp)"
  have r: "?r = p ` {0 ..< nr} - {nc}" unfolding set_map pp by force
  let ?l = "set (map fst pp)"
  from qj have qj': "qj \<notin> p ` {0 ..< nr}" using r by auto
  let ?v = "non_pivot_base A pp qj"
  let ?P = "p ` {0 ..< nr}"
  have dimv: "dim_vec ?v = nc" unfolding d by simp
  thus "?v \<in> carrier_vec nc" unfolding carrier_vec_def by auto
  show vqj: "?v $ qj = 1" unfolding d using qj by auto
  { 
    fix qj'
    assume *: "qj' < nc" "qj \<noteq> qj'" "qj' \<notin> snd ` set pp"
    hence "?map qj' = None" unfolding map_of_eq_None_iff by force
    hence "I qj' = 0" unfolding I_def by simp
    with * show "non_pivot_base A pp qj $ qj' = 0" 
      unfolding d by simp
  }    
  {
    fix i
    assume i: "i < nr"
    let ?I = "{j. ?map j = Some i}"
    have "row A i \<bullet> ?v = 0" 
    proof -
      have id: "({0..<nc} \<inter> ?P) \<union> ({0..<nc} - ?P) = {0..<nc}" by auto
      let ?e = "\<lambda> j. row A i $ j * ?v $ j"
      let ?e' = "\<lambda> j. (if ?map j = Some i then - A $$ (i, qj) else 0)"
      {
        fix j
        assume j: "j < nc" "j \<in> ?P"
        then obtain ii where ii: "ii < nr" and jpi: "j = p ii" and pii: "p ii < nc" by auto
        hence mem: "(ii,j) \<in> set pp" and "(j,ii) \<in> set ?spp" by (auto simp: pp)        
        from map_of_is_SomeI[OF dist this(2)] 
        have map: "?map j = Some ii" by auto
        from mem j qj have jqj: "j \<noteq> qj" by force
        note p = pivot'(4-5)[OF ii pii]
        define start where "start = ?e j"
        have "start = A $$ (i,j) * ?v $ j" using j i A by (auto simp: start_def)
        also have "A $$ (i,j) = A $$ (i, p ii)" unfolding jpi ..
        also have "\<dots> = (if i = ii then 1 else 0)" using p(1) p(2)[OF i] by auto
        also have "\<dots> * ?v $ j = (if i = ii then ?v $ j else 0)" by simp
        also have "?v $ j = I j" unfolding d 
          using j jqj A by auto
        also have "I j = - A $$ (ii, qj)" unfolding I_def map by simp
        finally have "?e j = ?e' j" 
          unfolding start_def map by auto
      } note piv = this
      have "row A i \<bullet> ?v = (\<Sum> j = 0..<nc. ?e j)" unfolding row_def scalar_prod_def dimv ..
      also have "\<dots> = sum ?e ({0..<nc} \<inter> ?P) + sum ?e ({0..<nc} - ?P)"
        by (subst sum.union_disjoint[symmetric], auto simp: id)
      also have "sum ?e ({0..<nc} - ?P) = ?e qj + sum ?e ({0 ..<nc} - ?P - {qj})"
        by (rule sum.remove, insert qj qj', auto)
      also have "?e qj = row A i $ qj" unfolding vqj by simp
      also have "row A i $ qj = A $$ (i, qj)" using i A qj by auto
      also have "sum ?e ({0 ..<nc} - ?P - {qj}) = 0"
      proof (rule sum.neutral, intro ballI)
        fix j
        assume "j \<in> {0 ..<nc} - ?P - {qj}"
        hence j: "j < nc" "j \<notin> ?P" "j \<noteq> qj" "j \<notin> ?r" unfolding r by auto
        hence id: "map_of ?spp j = None" unfolding map_of_eq_None_iff by force
        have "?v $ j = I j" unfolding d using j by simp
        also have "\<dots> = 0" unfolding I_def id by simp 
        finally show "row A i $ j * ?v $ j = 0" by simp
      qed
      also have "A $$ (i, qj) + 0 = A $$ (i, qj)" by simp
      also have "sum ?e ({0..<nc} \<inter> ?P) = sum ?e' ({0..<nc} \<inter> ?P)"
        by (rule sum.cong, insert piv, auto)
      also have "{0..<nc} \<inter> ?P = {0..<nc} \<inter> ?I \<inter> ?P \<union> ({0..<nc} - ?I) \<inter> ?P" by auto
      also have "sum ?e' ({0..<nc} \<inter> ?I \<inter> ?P \<union> ({0..<nc} - ?I) \<inter> ?P)
        = sum ?e' ({0..<nc} \<inter> ?I \<inter> ?P) + sum ?e' (({0..<nc} - ?I) \<inter> ?P)"
        by (rule sum.union_disjoint, auto)
      also have "sum ?e' (({0..<nc} - ?I) \<inter> ?P) = 0"
        by (rule sum.neutral, auto)
      also have "sum ?e' ({0..<nc} \<inter> ?I \<inter> ?P) = 
        sum (\<lambda> _. - A $$ (i, qj)) ({0..<nc} \<inter> ?I \<inter> ?P)"
        by (rule sum.cong, auto)
      also have "\<dots> + 0 = \<dots>" by simp
      also have "sum (\<lambda> _. - A $$ (i, qj)) ({0..<nc} \<inter> ?I \<inter> ?P) + A $$ (i, qj) = 0" 
      proof (cases "i \<in> ?l")
        case False
        with pp(1) i have "p i = nc" by force
        from pivot'(2)[OF i, unfolded this, OF qj(1)] have z: "A $$ (i, qj) = 0" .
        show ?thesis 
          by (subst sum.neutral, auto simp: z)
      next
        case True
        then obtain j where mem: "(i,j) \<in> set pp" and id: "(j,i) \<in> set ?spp" by auto
        from map_of_is_SomeI[OF dist this(2)] have map: "?map j = Some i" .
        from pivot'(1)[OF i] have pi: "p i \<le> nc" .
        with mem[unfolded pp] have j: "j = p i" "j < nc" by auto
        {
          fix j'
          assume "j' \<in> ?I"
          hence "?map j' = Some i" by auto
          from map_of_SomeD[OF this] have "(i, j') \<in> set pp" by auto
          with mem pp(2) have "j' = j" using map_of_is_SomeI by fastforce
        }
        with map have II: "?I = {j}" by blast
        have II: "{0..<nc} \<inter> ?I \<inter> ?P = {j}" unfolding II using mem[unfolded pp] i j by auto
        show ?thesis unfolding II by simp
      qed
      finally show "row A i \<bullet> ?v = 0" .
    qed
  } note main = this
  show "A *\<^sub>v ?v = 0\<^sub>v nr"  
    by (rule eq_vecI, auto simp: dim main)
qed

lemma find_base_vector: assumes "snd ` set (pivot_positions A) \<noteq> {0 ..< nc}"
  shows 
    "find_base_vector A \<in> carrier_vec nc"
    "find_base_vector A \<noteq> 0\<^sub>v nc"
    "A *\<^sub>v find_base_vector A = 0\<^sub>v nr"
proof -
  define cands where "cands = filter (\<lambda> j. j \<notin> snd ` set (pivot_positions A)) [0 ..< nc]"
  from A have dim: "dim_row A = nr" "dim_col A = nc" by auto
  from ref[unfolded row_echelon_form_def] obtain p 
  where pivot: "pivot_fun A p nc" using dim by auto
  note piv = pivot_funD[OF dim(1) pivot]
  have "set cands \<noteq> {}" using assms piv unfolding cands_def  pivot_positions[OF A pivot]
    by (auto simp: le_neq_implies_less)
  then obtain c cs where cands: "cands = c # cs" by (cases cands, auto)
  hence res: "find_base_vector A = non_pivot_base A (pivot_positions A) c"
    unfolding find_base_vector_def Let_def cands_def dim by auto
  from cands have "c \<in> set cands" by auto
  hence c: "c < nc" "c \<notin> snd ` set (pivot_positions A)"
    unfolding cands_def by auto
  from non_pivot_base[OF this, folded res] c show
    "find_base_vector A \<in> carrier_vec nc"
    "find_base_vector A \<noteq> 0\<^sub>v nc"
    "A *\<^sub>v find_base_vector A = 0\<^sub>v nr"
  by auto
qed
end

lemma row_echelon_form_imp_1_or_0_row: assumes A: "A \<in> carrier_mat n n"
  and row: "row_echelon_form A"
  shows "A = 1\<^sub>m n \<or> (n > 0 \<and> row A (n - 1) = 0\<^sub>v n)"
proof -
  from A have dim: "dim_row A = n" "dim_col A = n" by auto
  from row[unfolded row_echelon_form_def] A
  obtain f where pivot: "pivot_fun A f n" by auto
  note p = pivot_funD[OF dim(1) this]
  show ?thesis
  proof (cases "\<exists> i < n. f i \<noteq> i")
    case True
    then obtain i where i: "i < n" and fi: "f i \<noteq> i" by auto
    note pb = pivot_bound[OF dim(1) pivot]
    from pb[of 0 i] i have "f i = n \<or> i \<le> f i" by auto
    with fi have fi: "f i = n \<or> i < f i" by auto
    from i have n: "n - 1 = i + (n - i - 1)" by auto
    from pb[of i "n - i - 1", folded n] fi i p(1)[of "n - 1"] 
    have fn: "f (n - 1) = n" by auto
    from i have n0: "n > 0" and n1: "n - 1 < n" by auto
    from p(2)[OF n1, unfolded fn] have zero: "\<And> j. j < n \<Longrightarrow> A $$ (n - 1, j) = 0" by auto
    show ?thesis
      by (rule disjI2[OF conjI[OF n0]], rule eq_vecI, insert zero A, auto)
  next
    case False
    {
      fix j
      assume j: "j < n"
      with False have id: "f j = j" by auto
      note pj = p[OF j, unfolded id]
      from pj(5)[OF j] pj(4)[OF j] 
      have "\<And> i. i < n \<Longrightarrow> A $$ (i,j) = (if i = j then 1 else 0)" by auto
    } note id = this
    show ?thesis
      by (rule disjI1, rule eq_matI, subst id, insert A, auto)
  qed
qed

context
  fixes A :: "'a :: field mat" and n :: nat and p :: "nat \<Rightarrow> nat"
  assumes ref: "row_echelon_form A"
  and A: "A \<in> carrier_mat n n"
  and 1: "A \<noteq> 1\<^sub>m n"
begin

lemma find_base_vector_not_1_pivot_positions: "snd ` set (pivot_positions A) \<noteq> {0 ..< n}"
proof 
  let ?pp = "pivot_positions A"
  assume id: "snd ` set ?pp = {0 ..< n}"
  from A have dim: "dim_row A = n" "dim_col A = n" by auto
  let ?n = "n - 1"
  from row_echelon_form_imp_1_or_0_row[OF A ref] 1
  have *: "0 < n" and row: "row A ?n = 0\<^sub>v n" by auto
  from ref[unfolded row_echelon_form_def] obtain p 
    where pivot: "pivot_fun A p n" using dim by auto
  note pp = pivot_positions[OF A pivot]
  note piv = pivot_funD[OF dim(1) pivot]
  from * have n: "?n < n" by auto
  {
    
    assume "p ?n < n"
    with piv(4)[OF n this] row n A have False
      by (metis dim index_row(1) index_zero_vec(1) zero_neq_one)
  }
  with piv(1)[OF n] have pn: "p ?n = n" by fastforce
  hence "?n \<notin> fst ` set ?pp" unfolding pp by auto
  hence "fst ` set ?pp \<subseteq> {0 ..< n} - {?n}" unfolding pp by force
  also have "\<dots> \<subseteq> {0 ..< n - 1}" by auto
  finally have "card (fst ` set ?pp) \<le> card {0 ..< n - 1}" using card_mono by blast
  also have "\<dots> = n - 1" by auto
  also have "card (fst ` set ?pp) = card (snd ` set ?pp)"
    unfolding set_map[symmetric] distinct_card[OF pp(2)] distinct_card[OF pp(3)] by simp
  also have "\<dots> = n" unfolding id by simp
  finally show False using n by simp
qed
  
lemma find_base_vector_not_1: 
    "find_base_vector A \<in> carrier_vec n"
    "find_base_vector A \<noteq> 0\<^sub>v n"
    "A *\<^sub>v find_base_vector A = 0\<^sub>v n"
  using find_base_vector[OF ref A find_base_vector_not_1_pivot_positions] .
end

lemma gauss_jordan: assumes A: "A \<in> carrier_mat nr nc"
  and B: "B \<in> carrier_mat nr nc2"
  and gauss: "gauss_jordan A B = (C,D)"
  shows "x \<in> carrier_vec nc \<Longrightarrow> (A *\<^sub>v x = 0\<^sub>v nr) = (C *\<^sub>v x = 0\<^sub>v nr)" (is "_ \<Longrightarrow> ?l = ?r")
    "X \<in> carrier_mat nc nc2  \<Longrightarrow> (A * X = B) = (C * X = D)" (is " _ \<Longrightarrow> ?l2 = ?r2")
    "C \<in> carrier_mat nr nc"
    "D \<in> carrier_mat nr nc2"
proof -
  from gauss_jordan_transform[OF A B gauss, unfolded ring_mat_def Units_def, simplified]
  obtain P Q where P: "P \<in> carrier_mat nr nr" and Q: "Q \<in> carrier_mat nr nr"
    and inv: "Q * P = 1\<^sub>m nr" 
    and CPA: "C = P * A" 
    and DPB: "D = P * B" by auto
  from CPA P A show C: "C \<in> carrier_mat nr nc" by auto
  from DPB P B show D: "D \<in> carrier_mat nr nc2" by auto
  have "A = 1\<^sub>m nr * A" using A by simp
  also have "\<dots> = Q * C" unfolding inv[symmetric] CPA using Q P A by simp
  finally have AQC: "A = Q * C" .
  have "B = 1\<^sub>m nr * B" using B by simp
  also have "\<dots> = Q * D" unfolding inv[symmetric] DPB using Q P B by simp
  finally have BQD: "B = Q * D" .
  {
    assume x: "x \<in> carrier_vec nc"
    {
      assume ?l
      from arg_cong[OF this, of "\<lambda> v. P *\<^sub>v v"] P A x have ?r unfolding CPA by auto
    }
    moreover
    {
      assume ?r
      from arg_cong[OF this, of "\<lambda> v. Q *\<^sub>v v"] Q C x have ?l unfolding AQC by auto
    }
    ultimately show "?l = ?r" by auto
  }
  {
    assume X: "X \<in> carrier_mat nc nc2"
    {
      assume ?l2
      from arg_cong[OF this, of "\<lambda> X. P * X"] P A X have ?r2 unfolding CPA DPB by simp
    }
    moreover
    {
      assume ?r2
      from arg_cong[OF this, of "\<lambda> X. Q * X"] Q C X have ?l2 unfolding AQC BQD by simp
    }
    ultimately show "?l2 = ?r2" by auto
  }
qed

definition gauss_jordan_single :: "'a :: field mat \<Rightarrow> 'a mat" where
  "gauss_jordan_single A = fst (gauss_jordan A (0\<^sub>m (dim_row A) 0))"

lemma gauss_jordan_single: assumes A: "A \<in> carrier_mat nr nc"
  and gauss: "gauss_jordan_single A = C"
  shows "x \<in> carrier_vec nc \<Longrightarrow> (A *\<^sub>v x = 0\<^sub>v nr) = (C *\<^sub>v x = 0\<^sub>v nr)" 
    "C \<in> carrier_mat nr nc"
    "row_echelon_form C"
    "\<exists> P Q. C = P * A \<and> P \<in> carrier_mat nr nr \<and> Q \<in> carrier_mat nr nr \<and> P * Q = 1\<^sub>m nr \<and> Q * P = 1\<^sub>m nr" (is "?ex")
proof -
  from A gauss[unfolded gauss_jordan_single_def] obtain D where gauss: "gauss_jordan A (0\<^sub>m nr 0) = (C,D)"
    by (cases "gauss_jordan A (0\<^sub>m nr 0)", auto)
  from gauss_jordan[OF A zero_carrier_mat gauss] gauss_jordan_row_echelon[OF A gauss]
    gauss_jordan_transform[OF A zero_carrier_mat gauss, of "()"]
  show "x \<in> carrier_vec nc \<Longrightarrow> (A *\<^sub>v x = 0\<^sub>v nr) = (C *\<^sub>v x = 0\<^sub>v nr)" 
    "C \<in> carrier_mat nr nc" "row_echelon_form C" ?ex unfolding Units_def ring_mat_def by auto
qed



lemma gauss_jordan_inverse_one_direction: 
  assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n nc"
  and res: "gauss_jordan A B = (1\<^sub>m n, B')"
  shows "A \<in> Units (ring_mat TYPE('a :: field) n b)"
  "B = 1\<^sub>m n \<Longrightarrow> A * B' = 1\<^sub>m n \<and> B' * A = 1\<^sub>m n"
proof -
  let ?R = "ring_mat TYPE('a) n b"
  let ?U = "Units ?R"
  interpret m: ring ?R by (rule ring_mat)
  from gauss_jordan_transform[OF A B res, of b]
  obtain P where P: "P \<in> ?U" and id: "P * A = 1\<^sub>m n" and B': "B' = P * B" by auto
  from P have Pc: "P \<in> carrier_mat n n" unfolding Units_def ring_mat_def by auto
  from m.Units_one_side_I(1)[of A P] A P id show Au: "A \<in> ?U" unfolding ring_mat_def by auto
  assume B: "B = 1\<^sub>m n" 
  from B'[unfolded this] Pc have B': "B' = P" by auto
  show "A * B' = 1\<^sub>m n \<and> B' * A = 1\<^sub>m n" unfolding B' 
    using m.Units_inv_comm[OF _ P Au] id by (auto simp: ring_mat_def)
qed

lemma gauss_jordan_inverse_other_direction: 
  assumes AU: "A \<in> Units (ring_mat TYPE('a :: field) n b)" and B: "B \<in> carrier_mat n nc"
  shows "fst (gauss_jordan A B) = 1\<^sub>m n"
proof -
  let ?R = "ring_mat TYPE('a) n b"
  let ?U = "Units ?R"
  interpret m: ring ?R by (rule ring_mat)
  from AU have A: "A \<in> carrier_mat n n" unfolding Units_def ring_mat_def by auto
  obtain A' B' where res: "gauss_jordan A B = (A',B')" by force
  from gauss_jordan_transform[OF A B res, of b]
  obtain P where P: "P \<in> ?U" and id: "A' = P * A" by auto
  from m.Units_m_closed[OF P AU]  have A': "A' \<in> ?U" unfolding id ring_mat_def by auto
  hence A'c: "A' \<in> carrier_mat n n" unfolding Units_def ring_mat_def by auto
  from A'[unfolded Units_def ring_mat_def] obtain IA' where IA': "IA' \<in> carrier_mat n n"
    and IA: "A' * IA' = 1\<^sub>m n" by auto
  from row_echelon_form_imp_1_or_0_row[OF gauss_jordan_carrier(1)[OF A B res] gauss_jordan_row_echelon[OF A res]] 
  have choice: "A' = 1\<^sub>m n \<or> 0 < n \<and> row A' (n - 1) = 0\<^sub>v n" .
  hence "A' = 1\<^sub>m n"
  proof 
    let ?n = "n - 1"
    assume "0 < n \<and> row A' ?n = 0\<^sub>v n" 
    hence n: "?n < n" and row: "row A' ?n =  0\<^sub>v n" by auto
    have "1 = 1\<^sub>m n $$ (?n,?n)" using n by simp
    also have "1\<^sub>m n = A' * IA'" unfolding IA ..
    also have "(A' * IA') $$ (?n, ?n) = row A' ?n \<bullet> col IA' ?n"
      using n IA' A'c by simp
    also have "row A' ?n = 0\<^sub>v n" unfolding row ..
    also have "0\<^sub>v n \<bullet> col IA' ?n = 0" using IA' n by simp
    finally have "1 = (0 :: 'a)" by simp
    thus ?thesis by simp
  qed 
  with res show ?thesis by simp
qed

lemma gauss_jordan_compute_inverse:
  assumes A: "A \<in> carrier_mat n n"
  and res: "gauss_jordan A (1\<^sub>m n) = (1\<^sub>m n, B')"
  shows "A * B' = 1\<^sub>m n" "B' * A = 1\<^sub>m n" "B' \<in> carrier_mat n n"
proof -
  from gauss_jordan_inverse_one_direction(2)[OF A _ res refl, of n]
  show "A * B' = 1\<^sub>m n" "B' * A = 1\<^sub>m n" by auto
  from gauss_jordan_carrier(2)[OF A _ res, of n] show "B' \<in> carrier_mat n n" by auto
qed

lemma gauss_jordan_check_invertable: assumes A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n nc"
  shows "(A \<in> Units (ring_mat TYPE('a :: field) n b)) \<longleftrightarrow> fst (gauss_jordan A B) = 1\<^sub>m n"
  (is "?l = ?r")
proof 
  assume ?l
  show ?r
    by (rule gauss_jordan_inverse_other_direction[OF \<open>?l\<close> B])
next
  let ?g = "gauss_jordan A B"
  assume ?r
  then obtain B' where "?g = (1\<^sub>m n, B')" by (cases ?g, auto)
  from gauss_jordan_inverse_one_direction(1)[OF A B this]
  show ?l .
qed

definition mat_inverse :: "'a :: field mat \<Rightarrow> 'a mat option" where 
  "mat_inverse A = (if dim_row A = dim_col A then
    let one = 1\<^sub>m (dim_row A) in
    (case gauss_jordan A one of
      (B, C) \<Rightarrow> if B = one then Some C else None) else None)"

lemma mat_inverse: assumes A: "A \<in> carrier_mat n n"
  shows "mat_inverse A = None \<Longrightarrow> A \<notin> Units (ring_mat TYPE('a :: field) n b)"
    "mat_inverse A = Some B \<Longrightarrow> A * B = 1\<^sub>m n \<and> B * A = 1\<^sub>m n \<and> B \<in> carrier_mat n n"
proof -
  let ?one = "1\<^sub>m n"
  obtain BB C where res: "gauss_jordan A ?one = (BB,C)" by force
  {
    assume "mat_inverse A = None"
    with res have "BB \<noteq> ?one" unfolding mat_inverse_def using A by auto
    thus "A \<notin> Units (ring_mat TYPE('a :: field) n b)"
      using gauss_jordan_check_invertable[OF A, of ?one n] res by force
  }
  {
    assume "mat_inverse A = Some B"
    with res A have "BB = ?one" "C = B" unfolding mat_inverse_def
      by (auto split: if_splits option.splits)
    from gauss_jordan_compute_inverse[OF A res[unfolded this]]
    show "A * B = 1\<^sub>m n \<and> B * A = 1\<^sub>m n \<and> B \<in> carrier_mat n n" by auto
  }
qed
end
