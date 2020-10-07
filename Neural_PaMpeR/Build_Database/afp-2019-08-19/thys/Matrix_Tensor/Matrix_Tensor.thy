(*  Title:       Tensor Product of Matrices
    Author:      T. V. H. Prathamesh (prathamesh@imsc.res.in)
    Maintainer:  T. V. H. Prathamesh
*)

text\<open>
We define Tensor Product of Matrics and prove properties such as associativity and mixed product 
property(distributivity) of the tensor product.\<close>

section\<open>Tensor Product of Matrices\<close>

theory Matrix_Tensor
imports Matrix.Utility Matrix.Matrix_Legacy
begin


subsection\<open>Defining the Tensor Product\<close>



text\<open>We define a multiplicative locale here - mult, 
where the multiplication satisfies commutativity, 
associativity and contains a left and right identity\<close>

locale mult = 
 fixes id::"'a"
 fixes f::" 'a \<Rightarrow> 'a \<Rightarrow> 'a " (infixl "*" 60)
 assumes comm:" f a  b = f b  a "
 assumes assoc:" (f (f a b) c) = (f a (f b c))"
 assumes left_id:" f id x = x"
 assumes right_id:"f x id = x"
 
context mult
begin   


text\<open>times a v , gives us the product of the vector v with 
multiplied pointwise with a\<close>

primrec times:: "'a \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
where
"times n [] = []"|
"times n (y#ys) = (f n y)#(times n ys)"

lemma times_scalar_id: "times id v = v"
 by(induction v)(auto simp add:left_id)

lemma times_vector_id: "times v [id] = [v]"
 by(simp add:right_id)

lemma preserving_length: "length (times n y) = (length y)"
 by(induction y)(auto)

text\<open>vec$\_$vec$\_$Tensor is the tensor product of two vectors. It is 
illustrated by the following relation
 
$vec\_vec\_Tensor (v_1,v_2,...v_n) (w_1,w_2,...w_m) 
                 = (v_1 \cdot w_1,...,v_1 \cdot w_m,...
                          , v_n \cdot w_1 , ..., v_n \cdot w_m)$\<close>

primrec vec_vec_Tensor:: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
where
"vec_vec_Tensor [] ys = []"|
"vec_vec_Tensor (x#xs) ys = (times x ys)@(vec_vec_Tensor xs ys)"


lemma vec_vec_Tensor_left_id: "vec_vec_Tensor [id] v = v"
 by(induction v)(auto simp add:left_id)

lemma vec_vec_Tensor_right_id: "vec_vec_Tensor v [id] = v"
 by(induction v)(auto simp add:right_id)

theorem vec_vec_Tensor_length : 
 "(length(vec_vec_Tensor x y)) = (length x)*(length y)"
 by(induction x)(auto simp add: preserving_length)

theorem vec_length: assumes "vec m x" and "vec n y"
shows "vec (m*n) (vec_vec_Tensor x y)"
 apply(simp add:vec_def)
 apply(simp add:vec_vec_Tensor_length)
 apply (metis assms(1) assms(2) vec_def)
 done


text\<open>vec$\_$mat$\_$Tensor is the tensor product of two vectors. It is 
illusstrated by the following relation
 
vec\_mat\_Tensor ($v_1,v_2,...v_n) (C_1,C_2,...C_m) 
                 = (v_1 \cdot C_1,...,v_n \cdot C_1,
                               ...,v_1 \cdot C_m , ..., v_n \cdot C_m$)\<close>


primrec vec_mat_Tensor::"'a vec \<Rightarrow> 'a mat \<Rightarrow>'a mat"
where
"vec_mat_Tensor xs []  = []"|
"vec_mat_Tensor xs (ys#yss) = (vec_vec_Tensor xs ys)#(vec_mat_Tensor xs yss)"


lemma vec_mat_Tensor_vector_id: "vec_mat_Tensor [id] v = v"
 by(induction v)(auto simp add: times_scalar_id)

lemma vec_mat_Tensor_matrix_id: "vec_mat_Tensor  v [[id]] = [v]"
 by(induction v)(auto simp add: right_id)

theorem vec_mat_Tensor_length: 
 "length(vec_mat_Tensor xs ys) = length ys"
 by(induction ys)(auto)

theorem length_matrix: 
 assumes "mat nr nc (y#ys)" and "length v = k"
     and "(vec_mat_Tensor v (y#ys) = x#xs)" 
 shows "(vec (nr*k) x)" 
proof-
 have "vec_mat_Tensor v (y#ys) = (vec_vec_Tensor v y)#(vec_mat_Tensor v ys)"  
       using vec_mat_Tensor_def assms by auto
 also have "(vec_vec_Tensor v y) = x" using assms by auto
 also have "length y = nr" using assms mat_def 
       by (metis in_set_member member_rec(1) vec_def)
 from this
   have "length (vec_vec_Tensor v y) = nr*k" 
       using assms vec_vec_Tensor_length  by auto
 from this 
   have "length x = nr*k" by (simp add: \<open>vec_vec_Tensor v y = x\<close>)
 from this 
   have "vec (nr*k) x" using vec_def by auto
 from this 
   show ?thesis by auto
qed

lemma matrix_set_list: 
 assumes "mat nr nc M" 
     and "length v = k"
     and " x \<in> set M" 
 shows "\<exists>ys.\<exists>zs.(ys@x#zs = M)" 
 using assms set_def in_set_conv_decomp by metis

primrec reduct :: "'a mat \<Rightarrow> 'a mat"
where
"reduct [] = []"
|"reduct (x#xs) = xs"

lemma length_reduct: 
 assumes "m \<noteq> []"
 shows "length (reduct m) +1  = (length m)"
 apply(auto)
 by (metis One_nat_def Suc_eq_plus1 assms list.size(4) neq_Nil_conv reduct.simps(2))

lemma mat_empty_column_length: assumes "mat nr nc M" and "M = []"
shows "nc = 0" 
proof-
 have "(length M = nc)" using mat_def assms by metis
 from this 
   have "nc = 0" using assms by auto
 from this 
   show ?thesis by simp
qed

lemma vec_uniqueness: 
 assumes "vec m v" 
     and "vec n v" 
 shows "m = n"
 using vec_def assms(1) assms(2)  by metis

lemma mat_uniqueness: 
 assumes "mat nr1 nc M" 
 and "mat nr2 nc M" and "z = hd M" and "M \<noteq> []"
 shows "(\<forall>x\<in>(set M).(nr1 = nr2))" 
proof-
 have A:"z \<in> set M" using assms(1) assms(3) assms(4) set_def mat_def 
           by (metis hd_in_set)
 have "Ball (set M) (vec nr1)" using mat_def assms(1) by auto 
 then have step1: "((x \<in> (set M)) \<longrightarrow> (vec nr1 x))" using Ball_def assms by auto
 have "Ball (set M) (vec nr2)" using mat_def assms(2) by auto
 then have step2: "((x \<in> (set M)) \<longrightarrow> (vec nr2 x))" using Ball_def assms by auto
 from step1 and step2 
   have step3:"\<forall>x.((x \<in> (set M))\<longrightarrow> ((vec nr1 x)\<and> (vec nr2 x)))"
   by (metis \<open>Ball (set M) (vec nr1)\<close> \<open>Ball (set M) (vec nr2)\<close>)
 have "((vec nr1 x)\<and> (vec nr2 x)) \<longrightarrow> (nr1 = nr2)" using vec_uniqueness by auto
 with step3  
   have "(\<forall>x.((x \<in> (set M)) \<longrightarrow>((nr1 = nr2))))" by (metis vec_uniqueness) 
 then
   have "(\<forall>x\<in>(set M).(nr1 = nr2))" by auto 
 then 
     show ?thesis by auto
qed

 
lemma mat_empty_row_length: assumes "mat nr nc M" and "M = []"
shows "mat 0 nc M" 
proof-
 have "set M = {}" using mat_def assms  empty_set  by auto
 then have "Ball (set M) (vec 0)" using Ball_def by auto
 then have "mat 0 nc M" using mat_def assms(1) assms(2) gen_length_code(1) length_code
 by (metis (full_types) )
 then show ?thesis by auto
qed

abbreviation null_matrix::"'a list list"
where
"null_matrix \<equiv> [Nil] "

lemma null_mat:"null_matrix = [[]]"
 by auto

lemma zero_matrix:" mat 0 0 []" using mat_def in_set_insert insert_Nil list.size(3) not_Cons_self2
 by (metis (full_types))

text\<open>row\_length gives the length of the first row of a matrix. For a `valid'
matrix, it is equal to the number of rows\<close>

definition row_length:: "'a mat \<Rightarrow> nat"
where
"row_length xs \<equiv> if (xs = []) then 0 else (length (hd xs))"

lemma row_length_Nil: 
 "row_length [] =0" 
 using row_length_def by (metis )

lemma row_length_Null: 
 "row_length [[]] =0" 
 using row_length_def by auto

lemma row_length_vect_mat: 
 "row_length (vec_mat_Tensor v m)  = length v*(row_length m)"
proof(induct m)
 case Nil
  have "row_length [] = 0" 
       using row_length_Nil by simp
  moreover have "vec_mat_Tensor v [] = []" 
       using vec_mat_Tensor.simps(1) by auto 
  ultimately have 
   "row_length (vec_mat_Tensor v [])  = length v*(row_length [])" 
       using mult_0_right by (metis )
  then show ?case by metis
 next  
  fix a m
  assume A:"row_length (vec_mat_Tensor v m) = length v * row_length m"
  let ?case = 
         "row_length (vec_mat_Tensor v (a#m)) = (length v)*(row_length (a#m))" 
  have A:"row_length (a # m) = length a" 
              using row_length_def   list.distinct(1)
              by auto
  have "(vec_mat_Tensor v  (a#m)) = (vec_vec_Tensor v a)#(vec_mat_Tensor v m)" 
              using vec_mat_Tensor_def vec_mat_Tensor.simps(2)
              by auto
  from this have 
       "row_length (vec_mat_Tensor v (a#m)) = length (vec_vec_Tensor v a)" 
              using row_length_def   list.distinct(1)  vec_mat_Tensor.simps(2)
              by auto
  from this and vec_vec_Tensor_length have 
          "row_length (vec_mat_Tensor v (a#m)) = (length v)*(length a)" 
              by auto
  from this and A  have 
         "row_length (vec_mat_Tensor v (a#m)) = (length v)*(row_length (a#m))"
              by auto
  from this show ?case by auto
qed

text\<open>Tensor is the tensor product of matrices\<close>

primrec Tensor::" 'a mat \<Rightarrow> 'a mat \<Rightarrow>'a mat" (infixl "\<otimes>" 63)
where
"Tensor [] xs = []"|
"Tensor (x#xs) ys = (vec_mat_Tensor x ys)@(Tensor xs ys)"

lemma Tensor_null: "xs \<otimes>[] = []" 
 by(induction xs)(auto)

text\<open>Tensor commutes with left and right identity\<close>

lemma Tensor_left_id: "  [[id]] \<otimes> xs = xs"
 by(induction xs)(auto simp add:times_scalar_id)

lemma Tensor_right_id: "  xs \<otimes> [[id]] = xs"
 by(induction xs)(auto simp add: vec_vec_Tensor_right_id)

text\<open>row$\_$length of tensor product of matrices is the product of 
their respective row lengths\<close>

lemma row_length_mat: 
    "(row_length (m1\<otimes>m2)) = (row_length m1)*(row_length m2)"
proof(induct m1)
 case Nil
  have "row_length ([]\<otimes>m2) = 0" 
    using Tensor.simps(1) row_length_def 
    by metis
  from this 
   have "row_length ([]\<otimes>m2) = (row_length [])*(row_length m2)" 
    using  row_length_Nil   
    by auto
   then show ?case by metis
 next
  fix a m1 
  assume "row_length (m1 \<otimes> m2) = row_length m1 * row_length m2"
  let ?case = 
    "row_length ((a # m1) \<otimes> m2) = row_length (a # m1) * row_length m2"
  have B: "row_length (a#m1) = length a" 
    using row_length_def   list.distinct(1)
    by auto
  have "row_length ((a # m1) \<otimes> m2) = row_length (a # m1) * row_length m2"
  proof(induct m2)
   case Nil
       show ?case using Tensor_null row_length_def  mult_0_right by (metis)
   next
    fix aa m2
    assume "row_length (a # m1 \<otimes> m2) = row_length (a # m1) * row_length m2"
     let ?case= 
      "row_length (a # m1 \<otimes> aa # m2) 
                  = row_length (a # m1) * row_length (aa # m2)"
     have "aa#m2 \<noteq> []" 
          by auto
     from this have non_zero:"(vec_mat_Tensor a (aa#m2)) \<noteq> []" 
          using vec_mat_Tensor_def by auto
     from this have 
            "hd ((vec_mat_Tensor a (aa#m2))@(m1\<otimes>m2))
                  = hd (vec_mat_Tensor a (aa#m2))" 
          by auto
     from this have 
            "hd ((a#m1)\<otimes>(aa#m2)) = hd (vec_mat_Tensor a (aa#m2))" 
          using Tensor.simps(2) by auto
     from this have s1: "row_length ((a#m1)\<otimes>(aa#m2)) 
                       = row_length (vec_mat_Tensor a (aa#m2))" 
          using row_length_def  Nil_is_append_conv non_zero Tensor.simps(2)
          by auto
     have "row_length (vec_mat_Tensor a (aa#m2)) 
                    = (length a)*row_length(aa#m2)" 
          using row_length_vect_mat by metis   
     from this and s1  
     have "row_length (vec_mat_Tensor a (aa#m2)) 
                             = (length a)*row_length(aa#m2)"
          by auto
     from this and B 
             have "row_length (vec_mat_Tensor a (aa#m2)) 
                           = (row_length (a#m1))*row_length(aa#m2)"    
          by auto
     from this  and s1 show ?case  by auto
  qed
  from this show ?case by auto
 qed


lemma hd_set:assumes "x \<in> set (a#M)" shows "(x = a) \<or> (x\<in>(set M))"
 using set_def assms set_ConsD  by auto

text\<open>for every valid matrix can also be written in the following form\<close>

theorem matrix_row_length: 
 assumes "mat nr nc M" 
 shows "mat (row_length M) (length M) M"
proof(cases M)
 case Nil
  have "row_length M= 0 " 
       using row_length_def by (metis Nil)
  moreover have "length M = 0" 
       by (metis Nil list.size(3))
  moreover  have "mat 0 0 M" 
       using zero_matrix Nil by auto 
  ultimately show ?thesis  
       using mat_empty_row_length row_length_def mat_def  by metis
 next
 case (Cons a N) 
  have 1: "mat nr nc (a#N)" 
       using assms Cons by auto
  from this have "(x \<in> set (a #N)) \<longrightarrow> (x = a) \<or> (x \<in> (set N))" 
       using hd_set by auto
  from this and 1 have 2:"vec nr a" 
       using mat_def by (metis Ball_set_list_all list_all_simps(1))
  have "row_length (a#N) = length a" 
       using row_length_def Cons  list.distinct(1) by auto
  from this have " vec (row_length (a#N)) a" 
        using vec_def by auto
  from this and 2 have 3:"(row_length M)  = nr" 
        using vec_uniqueness Cons by auto
  have " nc = (length M)" 
        using 1 and mat_def and assms by metis
  with 3 
        have "mat (row_length M) (length M) M" 
        using assms by auto 
  from this show ?thesis by auto
qed


lemma reduct_matrix: 
 assumes "mat (row_length (a#M)) (length (a#M)) (a#M)"
 shows "mat (row_length M) (length M) M"
proof(cases M)
 case Nil
   show ?thesis 
         using row_length_def zero_matrix Nil  list.size(3)  by (metis)
 next   
 case (Cons b N)
  fix x
  have 1: "b \<in> (set M)" 
         using set_def  Cons ListMem_iff elem  by auto
  have "mat (row_length (a#M)) (length (a#M)) (a#M)" 
         using assms by auto
  then have "(x \<in> (set (a#M))) \<longrightarrow> ((x = a) \<or> (x \<in> set M))" 
         by auto
  then have " (x \<in> (set (a#M))) \<longrightarrow> (vec (row_length (a#M)) x)" 
         using mat_def Ball_def assms 
         by metis
  then have "(x \<in> (set (a#M))) \<longrightarrow> (vec (length a) x)" 
         using row_length_def  list.distinct(1) 
         by auto
  then have 2:"x \<in> (set M) \<longrightarrow> (vec (length a) x)" 
         by auto
  with 1 have 3:"(vec (length a) b)"
         using assms in_set_member mat_def member_rec(1) vec_def
         by metis 
  have 5: "(vec (length b) b)" 
         using vec_def by auto
  with 3 have "(length a) = (length b)" 
         using vec_uniqueness by auto
  with 2 have 4: "x \<in> (set M) \<longrightarrow> (vec (length b) x)" 
         by auto
  have 6: "row_length M = (length b)" 
         using row_length_def   Cons list.distinct(1)
         by auto
  with 4 have "x \<in> (set M) \<longrightarrow> (vec (row_length M) x)" 
         by auto
  then have "(\<forall>x. (x \<in> (set M) \<longrightarrow> (vec (row_length M) x)))" 
         using Cons 5 6 assms in_set_member mat_def member_rec(1) 
         vec_uniqueness
         by metis
  then have "Ball (set M) (vec (row_length M))" 
         using Ball_def by auto
  then have "(mat (row_length M) (length M) M)" 
         using mat_def by auto
  then show ?thesis by auto
 qed 


theorem well_defined_vec_mat_Tensor:
"(mat (row_length M) (length M) M) \<Longrightarrow>
                  (mat 
                    ((row_length M)*(length v)) 
                    (length M) 
                           (vec_mat_Tensor v M))"
proof(induct M) 
 case Nil
  have "(vec_mat_Tensor v []) = []" 
      using vec_mat_Tensor.simps(1) Nil  
      by simp
  moreover have "(row_length [] = 0)"  
      using row_length_def Nil 
      by metis
  moreover have "(length []) = 0" 
      using Nil by simp
  ultimately have 
       "mat ((row_length [])*(length v)) (length []) (vec_mat_Tensor v [])" 
      using zero_matrix by (metis mult_zero_left)
  then show ?case by simp
 next
 fix a M
 assume hyp :
   "(mat (row_length M) (length M) M 
           \<Longrightarrow> mat (row_length M * length v) (length M) (vec_mat_Tensor v M))"
   "mat (row_length (a#M)) (length (a#M)) (a#M)"                      
  let ?case = 
   "mat (row_length (a#M) * length v) (length (a#M)) (vec_mat_Tensor v (a#M))"
  have step1: "mat (row_length M) (length M) M" 
          using hyp(2) reduct_matrix by auto
  then have step2:
    "mat (row_length M * length v) (length M) (vec_mat_Tensor v M)" 
          using hyp(1) by auto 
  have 
   "mat 
        (row_length (a#M) * length v) 
        (length (a#M)) 
             (vec_mat_Tensor v (a#M))" 
  proof (cases M)
   case Nil 
    fix x
    have 1:"(vec_mat_Tensor v (a#M)) = [vec_vec_Tensor v a]" 
           using vec_mat_Tensor.simps Nil by auto
    have   "(x \<in> (set [vec_vec_Tensor v a])) \<longrightarrow>  x = (vec_vec_Tensor v a)" 
           using set_def by auto
    then have 2:
        "(x \<in> (set [vec_vec_Tensor v a])) 
                    \<longrightarrow> (vec (length (vec_vec_Tensor v a)) x)" 
           using vec_def by metis 
    have 3:"length (vec_vec_Tensor v a) = (length v)*(length a)" 
           using vec_vec_Tensor_length by auto 
    then have 4:
        "length (vec_vec_Tensor v a) = (length v)*(row_length (a#M))" 
           using row_length_def  list.distinct(1) 
           by auto
    have 6: "length (vec_mat_Tensor v (a#M)) = (length (a#M))" 
           using vec_mat_Tensor_length by auto
    hence "mat (length (vec_vec_Tensor v a)) (length (a # M)) [vec_vec_Tensor v a]"
      by (simp add: Nil mat_def vec_def)
    hence
        "mat (row_length (a#M) * length v) 
             (length (vec_mat_Tensor v (a#M))) 
             (vec_mat_Tensor v (a#M))"
      using 1 4 6 by (simp add: mult.commute)
    then show ?thesis using 6 by auto
   next 
   case (Cons b L)
    fix x
    have 1:"x \<in> (set (a#M)) \<longrightarrow> ((x=a) \<or> (x \<in> (set M)))" 
           using hd_set by auto
    have "mat (row_length (a#M)) (length (a#M)) (a#M)" 
           using hyp by auto
    then have "x\<in> (set (a#M)) \<longrightarrow> (vec (row_length (a#M)) x)" 
           using mat_def Ball_def by metis
    then have "x\<in> (set (a#M))\<longrightarrow> (vec (length a) x)" 
           using row_length_def  list.distinct(1)
           by auto
    with 1 have "x\<in> (set M)\<longrightarrow> (vec (length a) x)" 
           by auto
    moreover have " b \<in> (set M)" 
           using Cons by auto
    ultimately have "vec (length a) b"
           using  hyp(2) in_set_member mat_def member_rec(1) vec_def  by (metis) 
    then have "(length b) = (length a)" 
           using vec_def vec_uniqueness by auto
    then have 2:"row_length M = (length a)" 
           using row_length_def   Cons list.distinct(1) by auto     
    have "mat (row_length M * length v) (length M) (vec_mat_Tensor v M)" 
           using step2 by auto 
    then have 3:
          "Ball (set (vec_mat_Tensor v M)) (vec ((row_length M)*(length v)))" 
           using mat_def by auto
    then have "(x \<in> set (vec_mat_Tensor v M)) 
                        \<longrightarrow> (vec ((row_length M)*(length v)) x)" 
           using mat_def Ball_def by auto
    then have 4:"(x \<in> set (vec_mat_Tensor v M)) 
                          \<longrightarrow> (vec ((length a)*(length v)) x)" 
           using 2 by auto  
    have 5:"length (vec_vec_Tensor v a) = (length a)*(length v)" 
           using   vec_vec_Tensor_length by auto  
    then have 6:" vec ((length a)*(length v)) (vec_vec_Tensor v a)" 
           using vec_vec_Tensor_length vec_def by (metis (full_types))
    have 7:"(length a) = (row_length (a#M))" 
           using row_length_def   list.distinct(1) by auto 
    have "vec_mat_Tensor v (a#M) 
                   = (vec_vec_Tensor v a)#(vec_mat_Tensor v M)" 
           using vec_mat_Tensor.simps(2) by auto
    then have "(x \<in> set (vec_mat_Tensor v (a#M)))
                      \<longrightarrow> ((x = (vec_vec_Tensor v a)) 
                           \<or> (x \<in> (set (vec_mat_Tensor v M))))"
           using  hd_set by auto
    with 4 6 have "(x \<in> set (vec_mat_Tensor v (a#M)))
                             \<longrightarrow>  vec ((length a)*(length v)) x" 
           by auto
    with 7 have "(x \<in> set (vec_mat_Tensor v (a#M)))
                                \<longrightarrow>  vec ((row_length (a#M))*(length v)) x" 
           by auto
    then have "\<forall>x.((x \<in> set (vec_mat_Tensor v (a#M)))
                                \<longrightarrow>  vec ((row_length (a#M))*(length v)) x)"
           using "2" "3" "6" "7" hd_set vec_mat_Tensor.simps(2) by auto
    then have 7: 
      "Ball 
            (set (vec_mat_Tensor v (a#M))) 
            (vec ((row_length (a#M))*(length v)))" 
           using Ball_def  by auto
    have 8: "length (vec_mat_Tensor v (a#M)) = length (a#M)" 
           using vec_mat_Tensor_length by auto   
    with 6  7 have 
               "mat 
                 ((row_length (a#M))*(length v)) 
                 (length (a#M)) 
                           (vec_mat_Tensor v (a#M))"
           using mat_def  "5" length_code
           by (metis (hide_lams, no_types))
    then show ?thesis by auto
    qed
    with  hyp  show ?case by auto  
 qed

text\<open>The following theorem  gives length of tensor product of two matrices\<close>

lemma length_Tensor:" (length (M1\<otimes>M2)) = (length M1)*(length M2)"
proof(induct M1)
 case Nil
  show ?case by auto
 next
 case (Cons a M1)
  have "((a # M1) \<otimes> M2) = (vec_mat_Tensor a M2)@(M1 \<otimes> M2)" 
               using Tensor.simps(2) by auto
  then have 1:
          "length ((a # M1) \<otimes> M2) = length ((vec_mat_Tensor a M2)@(M1 \<otimes> M2))" 
               by auto
  have 2:"length ((vec_mat_Tensor a M2)@(M1 \<otimes> M2)) 
              = length (vec_mat_Tensor a M2)+ length (M1 \<otimes> M2)" 
               using append_def
               by auto
  have 3:"(length (vec_mat_Tensor a M2)) = length M2" 
               using vec_mat_Tensor_length by (auto)
  have 4:"length (M1 \<otimes> M2) = (length M1)*(length M2)" 
               using  Cons.hyps by auto
  with 2 3 have "length ((vec_mat_Tensor a M2)@(M1 \<otimes> M2)) 
                              = (length M2) + (length M1)*(length M2)"
               by auto
  then have 5:
    "length ((vec_mat_Tensor a M2)@(M1 \<otimes> M2)) = (1 + (length M1))*(length M2)" 
               by auto
  with 1  have "length ((a # M1) \<otimes> M2) = ((length (a # M1)) * (length M2))" 
          by auto
  then show ?case by auto
qed



lemma append_reduct_matrix: 
"(mat (row_length (M1@M2)) (length (M1@M2)) (M1@M2))
\<Longrightarrow>(mat (row_length M2) (length M2) M2)"
proof(induct M1)
 case Nil
  show ?thesis using Nil append.simps(1) by auto
 next
 case (Cons a M1)
  have "mat (row_length (M1 @ M2)) (length (M1 @ M2)) (M1 @ M2)" 
    using reduct_matrix Cons.prems append_Cons by metis
  from this have "(mat (row_length M2) (length M2) M2)" 
    using Cons.hyps by auto
  from this show?thesis by simp
qed

text\<open>The following theorem proves that tensor product of two valid matrices
is a valid matrix\<close>

theorem well_defined_Tensor:
 "(mat (row_length M1) (length M1) M1) 
\<and> (mat (row_length M2) (length M2) M2)
\<Longrightarrow>(mat ((row_length M1)*(row_length M2)) ((length M1)*(length M2)) (M1\<otimes>M2))"
proof(induct M1)
 case Nil
   have "(row_length []) * (row_length M2) = 0" 
            using row_length_def  mult_zero_left  by (metis)
   moreover have "(length []) * (length M2) = 0" 
            using  mult_zero_left list.size(3) by auto 
   moreover have "[] \<otimes> M2 = []" 
            using Tensor.simps(1) by auto
   ultimately have 
       "mat (row_length []*row_length M2) (length []*length M2) ([] \<otimes> M2)"
            using zero_matrix by metis
   then show ?case by simp
 next
 case (Cons a M1)
  have step1: "mat (row_length (a # M1)) (length (a # M1)) (a # M1)" 
             using Cons.prems by auto
  then have "mat (row_length (M1)) (length (M1)) (M1)" 
             using reduct_matrix by auto
  moreover have "mat (row_length (M2)) (length (M2)) (M2)" 
             using Cons.prems by auto
  ultimately have step2:
      "mat (row_length M1 * row_length M2) (length M1 * length M2) (M1 \<otimes> M2)"
             using Cons.hyps by auto
  have 0:"row_length (a#M1) = length a" 
             using row_length_def  list.distinct(1) by auto
  have "mat 
           (row_length (a # M1)*row_length M2) 
           (length (a # M1)*length M2) 
                           (a # M1 \<otimes> M2)"
  proof(cases M1)
   case Nil 
    have "(mat ((row_length M2)*(length a)) (length M2) (vec_mat_Tensor a M2))" 
          using Cons.prems well_defined_vec_mat_Tensor by auto
    moreover have "(length (a # M1)) * (length M2) = length M2" 
          using Nil by auto
    moreover have "(a#M1)\<otimes>M2 = (vec_mat_Tensor a M2)" 
          using Nil Tensor.simps append.simps(1) by auto
    ultimately have 
        "(mat 
            ((row_length M2)*(row_length (a#M1))) 
            ((length (a # M1)) * (length M2))
               ((a#M1)\<otimes>M2))" 
          using 0 by auto
    then show ?thesis by (simp add: mult.commute)
   next
   case (Cons b N1)
    fix x
    have 1:"x \<in> (set (a#M1)) \<longrightarrow> ((x=a) \<or> (x \<in> (set M1)))" 
               using hd_set by auto
    have "mat (row_length (a#M1)) (length (a#M1)) (a#M1)" 
               using Cons.prems by auto
    then have "x\<in> (set (a#M1)) \<longrightarrow> (vec (row_length (a#M1)) x)" 
               using mat_def Ball_def by metis
    then have "x\<in> (set (a#M1))\<longrightarrow> (vec (length a) x)" 
               using row_length_def  list.distinct(1)
               by auto 
    with 1 have "x\<in> (set M1)\<longrightarrow> (vec (length a) x)" 
               by auto
    moreover have " b \<in> (set M1)" 
               using Cons by auto
    ultimately have "vec (length a) b" 
               using  Cons.prems in_set_member mat_def member_rec(1) vec_def
               by metis
    then have "(length b) = (length a)" 
               using vec_def vec_uniqueness by auto
    then have 2:"row_length M1 = (length a)" 
               using row_length_def Cons by auto 
    then have "mat 
                    ((length a) * row_length M2) 
                    (length M1 * length M2) 
                                    (M1 \<otimes> M2)" 
                using step2 by auto
    then have "Ball (set (M1\<otimes>M2)) (vec ((length a)*(row_length M2))) " 
                using mat_def by auto     
    from this have 3:
         "\<forall>x. x \<in> (set (M1 \<otimes> M2)) \<longrightarrow> (vec ((length a)*(row_length M2)) x)" 
                using Ball_def by auto    
    have "mat 
              ((row_length M2)*(length a)) 
              (length M2) 
                 (vec_mat_Tensor a M2)" 
                 using well_defined_vec_mat_Tensor Cons.prems 
                 by auto
    then have "Ball 
                    (set (vec_mat_Tensor a M2)) 
                    (vec ((row_length M2)*(length a)))" 
                 using mat_def
                 by auto
    then have 4:
              "\<forall>x. x \<in> (set (vec_mat_Tensor a M2)) 
                        \<longrightarrow> (vec ((length a)*(row_length M2)) x)"
                 using mult.commute by metis

    with 3 have 5: "\<forall>x. (x \<in> (set (vec_mat_Tensor a M2)))
                          \<or>(x \<in> (set (M1 \<otimes> M2))) 
                                 \<longrightarrow> (vec ((length a)*(row_length M2)) x)"  
                  by auto  
    have 6:"(a # M1 \<otimes> M2) = (vec_mat_Tensor a M2)@(M1 \<otimes>M2)" 
                  using Tensor.simps(2) by auto 
    then have "x \<in> (set (a # M1 \<otimes> M2)) 
                 \<longrightarrow> (x \<in> (set (vec_mat_Tensor a M2)))\<or>(x \<in> (set (M1 \<otimes> M2)))"
                  using set_def append_def by auto
    with 5 have 7:"\<forall>x. (x \<in>  (set (a # M1 \<otimes> M2)))
                         \<longrightarrow> (vec ((length a)*(row_length M2)) x)" 
                  by auto
    then have 8:
        "Ball (set (a # M1 \<otimes> M2)) (vec ((row_length (a#M1))*(row_length M2)))" 
                  using Ball_def 0 by auto   
    have "(length ((a#M1)\<otimes>M2)) = (length (a#M1))*(length M2)" 
                  using length_Tensor by metis
    with 7 8
       have "mat 
                     (row_length (a # M1) * row_length M2) 
                       (length (a # M1) * length M2) 
                                (a # M1 \<otimes> M2)"
                  using mat_def by (metis "0"  length_Tensor)
    then show ?thesis by auto
  qed
 then show ?case by auto
qed

theorem effective_well_defined_Tensor:
 assumes "(mat (row_length M1) (length M1) M1)" 
     and "(mat (row_length M2) (length M2) M2)"
 shows "mat 
            ((row_length M1)*(row_length M2)) 
            ((length M1)*(length M2)) 
                               (M1\<otimes>M2)"
 using well_defined_Tensor assms by auto


definition natmod::"nat \<Rightarrow> nat \<Rightarrow> nat" (infixl "nmod" 50)
where
 "natmod x y = nat ((int x) mod (int y))"

theorem times_elements:
 "\<forall>i.((i<(length v)) \<longrightarrow> (times a v)!i = f a (v!i))"
 apply(rule allI)
 proof(induct v)
  case Nil
   have "(length [] = 0)" 
          by auto
   then have "i <(length []) \<Longrightarrow> False" 
          by auto
   moreover have "(times a []) = []" 
          using times.simps(1) by auto 
   ultimately have "(i<(length [])) \<longrightarrow> (times a [])!i = f a ([]!i)" 
          by auto
   then have "\<forall>i. ((i<(length [])) \<longrightarrow> (times a [])!i = f a ([]!i))" 
          by auto
   then show ?case  by auto
  next   
  case (Cons x xs)
   have "\<forall>i.((x#xs)!(i+1) = (xs)!i)" 
          by auto
   have 0:"((i<length (x#xs))\<longrightarrow> ((i<(length xs)) \<or> (i = (length xs))))" 
          by auto
   have 1:" ((i<length xs) \<longrightarrow>((times a xs)!i = f a (xs!i)))" 
         by (metis Cons.hyps)
   have "\<forall>i.((x#xs)!(i+1) = (xs)!i)" by auto
   have "((i <length (x#xs)) \<longrightarrow>(times a (x#xs))!i = f a ((x#xs)!i))"  
   proof(cases i)
    case 0
     have "((times a (x#xs))!i) = f a x" 
          using 0 times.simps(2) by auto
     then have "(times a (x#xs))!i = f a ((x#xs)!i)" 
          using 0 by auto
     then show ?thesis by auto
    next
    case (Suc j)
     have 1:"(times a (x#xs))!i = ((f a x)#(times a xs))!i" 
          using times.simps(2) by auto 
     have 2:"((f a x)#(times a xs))!i = (times a xs)!j" 
          using Suc by auto
     have 3:"(i <length (x#xs)) \<longrightarrow> (j<length xs)" 
          using One_nat_def Suc Suc_eq_plus1 list.size(4) not_less_eq 
          by metis
     have 4:"(j<length xs) \<longrightarrow> ((times a xs)!j = (f a (xs!j)))" 
          using 1 by (metis Cons.hyps)
     have 5:"(x#xs)!i = (xs!j)" 
          using Suc by (metis nth_Cons_Suc)
     with 1 2 4  have "(j<length xs) 
                            \<longrightarrow> ((times a (x#xs))!i = (f a ((x#xs)!i)))" 
          by auto
     with 3 have "(i <length (x#xs)) 
                            \<longrightarrow> ((times a (x#xs))!i = (f a ((x#xs)!i)))" 
          by auto
     then show ?thesis  by auto
   qed
   then show ?case by auto
 qed

lemma simpl_times_elements:
 assumes "(i<length xs)" 
 shows "((i<(length v)) \<longrightarrow> (times a v)!i = f a (v!i))"
 using times_elements by auto

(*some lemmas which are used to prove theorems*)
lemma append_simpl: "i<(length xs) \<longrightarrow> (xs@ys)!i = (xs!i)" 
 using nth_append  by metis

lemma append_simpl2: "i \<ge>(length xs) \<longrightarrow> (xs@ys)!i = (ys!(i- (length xs)))" 
 using nth_append less_asym  leD  by metis

lemma append_simpl3: 
 assumes "i > (length y)"
 shows " (i <((length (z#zs))*(length y))) 
                  \<longrightarrow> (i - (length y))< (length zs)*(length y)"
proof-
 have "length (z#zs) = (length zs)+1" 
       by auto
 then have "i <((length (z#zs))*(length y)) 
                   \<longrightarrow> i <((length zs)+1)*(length y)"
       by auto
 then have 1: "i <((length (z#zs))*(length y)) 
                  \<longrightarrow> (i <((length zs)*(length y)+ (length y)))" 
       by auto
 have "i <((length zs)*(length y)+ (length y)) 
                   = ((i - (length y)) <((length zs)*(length y)))"
       using assms by auto
 then have "(i <((length (z#zs))*(length y))) 
                  \<longrightarrow> ((i - (length y)) <((length zs)*(length y)))"
       by auto
 then show ?thesis by auto
qed

lemma append_simpl4: 
"(i > (length y))
         \<longrightarrow> ((i <((length (z#zs))*(length y)))) 
                \<longrightarrow> ((i - (length y))< (length zs)*(length y))"
    using append_simpl3 by auto

lemma vec_vec_Tensor_simpl: 
   "i<(length y) \<longrightarrow> (vec_vec_Tensor (z#zs) y)!i = (times z y)!i" 
proof-
 have a: "vec_vec_Tensor (z#zs) y = (times z y)@(vec_vec_Tensor zs y)" 
      by auto
 have b: "length (times z y) = (length y)" using preserving_length by auto
 have "i<(length (times z y)) 
          \<longrightarrow> ((times z y)@(vec_vec_Tensor zs y))!i = (times z y)!i" 
      using append_simpl by metis
 with b have "i<(length y) 
          \<longrightarrow> ((times z y)@(vec_vec_Tensor zs y))!i = (times z y)!i" 
      by auto
 with  a have "i<(length y) 
          \<longrightarrow> (vec_vec_Tensor (z#zs) y)!i = (times z y)!i" 
      by auto
 then show ?thesis by auto
qed


lemma vec_vec_Tensor_simpl2: 
  "(i \<ge> (length y)) 
  \<longrightarrow> ((vec_vec_Tensor (z#zs) y)!i = (vec_vec_Tensor zs y)!(i- (length y)))" 
 using vec_vec_Tensor.simps(2) append_simpl2  preserving_length 
 by metis

lemma division_product: 
 assumes "(b::int)>0"
 and "a \<ge>b"
 shows " (a div b) = ((a - b) div b) + 1"
proof-
 fix c
 have "a -b \<ge>0" 
     using assms(2) by auto
 have 1: "a - b = a + (-1)*b" 
     by auto
 have "(b \<noteq> 0) \<longrightarrow> ((a + b * (-1)) div b = (-1) + a div b)" 
     using div_mult_self2 by metis
 with 1 assms(1) have "((a - b) div b) = (-1) + a div b" 
     using less_int_code(1) by auto
 then  have "(a div b) = ((a - b) div b) + 1" 
     by auto
 then show ?thesis 
     by auto
qed

lemma int_nat_div: 
   "(int a) div (int b) = int ((a::nat) div b)"
 by (metis zdiv_int)

lemma int_nat_eq: 
 assumes "int (a::nat) = int b"
 shows "a = b" 
 using  assms of_nat_eq_iff by auto

lemma nat_div: 
 assumes "(b::nat) > 0" 
     and "a > b"
 shows "(a div b) = ((a - b) div b) + 1"
proof-
 fix x
 have 1:"(int b)>0" 
      using assms(1) division_product by auto
 moreover have "(int a)>(int b)" 
      using assms(2) by auto
 with 1 have 2: "((int a) div (int b)) 
                   = (((int a) - (int b)) div (int b)) + 1" 
      using division_product by auto
 from int_nat_div have 3: "((int a) div (int b)) = int ( a div b)" 
      by auto
 from int_nat_div assms(2) have 4: 
        "(((int a) - (int b)) div (int b)) = int ((a - b) div b)" 
      by (metis (full_types) less_asym not_less of_nat_diff)
 have "(int x) + 1 = int (x +1)" 
      by auto
 with 2 3 4 have "int (a div b) = int (((a - b) div b) + 1)" 
      by auto
 with int_nat_eq have "(a div b) = ((a - b) div b) + 1" 
      by auto 
 then show ?thesis by auto
qed

lemma mod_eq:
 "(m::int) mod n = (m + (-1)*n) mod n"
 using mod_mult_self1 by metis

lemma nat_mod_eq: "int m mod int n = int (m mod n)"
  by (simp add: of_nat_mod)

lemma nat_mod: 
 assumes  "(m::nat) > n"
 shows "(m::nat) mod n = (m -n) mod n"
 using assms mod_if not_less_iff_gr_or_eq by auto 

lemma logic: 
 assumes "A \<longrightarrow> B" 
     and "\<not>A \<longrightarrow> B" 
 shows "B" 
 using assms(1) assms(2) by auto

theorem vec_vec_Tensor_elements:
 assumes " (y \<noteq> [])"
 shows 
   "\<forall>i.((i<((length x)*(length y)))
       \<longrightarrow> ((vec_vec_Tensor x y)!i) 
             = f (x!(i div (length y))) (y!(i mod (length y))))"
 apply(rule allI)
 proof(induct x)
 case Nil
  have "(length [] = 0)" 
      by auto
  also have "length (vec_vec_Tensor [] y) = 0" 
      using vec_vec_Tensor.simps(1) by auto
  then have "i <(length (vec_vec_Tensor [] y)) \<Longrightarrow> False" 
      by auto
  moreover have "(vec_vec_Tensor [] y) = []" 
      by auto 
  moreover have 
   "(i<(length (vec_vec_Tensor [] y))) \<longrightarrow> 
   ((vec_vec_Tensor x y)!i) = f (x!(i div (length y))) (y!(i mod (length y)))"  
      by auto
  then show ?case  
      by auto
 next
 case (Cons z zs)
  have 1:"vec_vec_Tensor (z#zs) y = (times z y)@(vec_vec_Tensor zs y)" 
      by auto
  have 2:"i<(length y)\<longrightarrow>((times z y)!i = f z (y!i))" 
      using times_elements by auto
  moreover have 3:
        "i<(length y) 
           \<longrightarrow> (vec_vec_Tensor (z#zs) y)!i = (times z y)!i" 
      using vec_vec_Tensor_simpl by auto
  moreover  have 35:
           "i<(length y) \<longrightarrow> (vec_vec_Tensor (z#zs) y)!i = f z (y!i)" 
      using calculation(1) calculation(2) by metis 
  have 4:"(y \<noteq> []) \<longrightarrow> (length y) >0 " 
      by auto 
  have "(i <(length y)) \<longrightarrow>  ((i div (length y)) = 0)" 
      by auto
  then have  6:"(i <(length y)) \<longrightarrow> (z#zs)!(i div (length y)) = z" 
      using nth_Cons_0 by auto
  then have 7:"(i <(length y)) \<longrightarrow> (i mod (length y)) = i" 
      by auto
  with 2 6  
     have "(i < (length y)) 
        \<longrightarrow> (times z y)!i 
                 = f  ((z#zs)!(i div (length y))) (y! (i mod (length y)))" 
      by auto 
  with 3 have step1:
      "((i < (length y)) 
          \<longrightarrow> ((i<((length x)*(length y)) 
          \<longrightarrow> ((vec_vec_Tensor (z#zs) y)!i 
                      =  f  
                             ((z#zs)!(i div (length y))) 
                              (y! (i mod (length y)))))))"
      by auto
  have "((length y) \<le> i) \<longrightarrow> (i - (length y)) \<ge> 0" 
      by auto
  have step2: 
        "((length y) < i) 
           \<longrightarrow> ((i < (length (z#zs)*(length y)))
           \<longrightarrow>((vec_vec_Tensor (z#zs) y)!i) 
                          = f 
                              ((z#zs)!(i div (length y))) 
                              (y!(i mod (length y))))"
  proof-
   have "(length y)>0" 
       using assms by auto
   then have 1: 
           "(i > (length y))
               \<longrightarrow>(i div (length y)) = ((i-(length y)) div (length y)) + 1" 
       using nat_div by auto
   have "zs!j = (z#zs)!(j+1)" 
       by auto
   then have 
            "(zs!((i - (length y)) div (length y))) 
                     = (z#zs)!(((i - (length y)) div (length y))+1)"
       by auto
   with 1 have 2: 
           "(i > (length y))
              \<longrightarrow> (zs!((i - (length y)) div (length y)) 
                     = (z#zs)!(i div (length y)))"
       by auto
   have "(i > (length y))
               \<longrightarrow>((i mod (length y)) 
                                 = ((i - (length y)) mod (length y)))" 
       using nat_mod by auto
   then have 3:
          "(i > (length y))
                  \<longrightarrow>((y! (i mod (length y))) 
                                = (y! ((i - (length y)) mod (length y))))" 
       by auto
   have 4:"(i > (length y))
                       \<longrightarrow>(vec_vec_Tensor (z#zs) y)!i 
                                = (vec_vec_Tensor zs y)!(i- (length y))" 
       using vec_vec_Tensor_simpl2  by auto
   have 5: "(i > (length y)) 
                 \<longrightarrow>((i <((length (z#zs))*(length y)))) 
                          = (i - (length y)< (length zs)*(length y))"
       by auto
   then have 6:
             "\<forall>i.((i<((length zs)*(length y)))
                       \<longrightarrow> ((vec_vec_Tensor zs y)!i) 
                                 = f 
                                    (zs!(i div (length y))) 
                                    (y!(i mod (length y))))" 
       using Cons.hyps by auto
   with 5 have "(i > (length y))
                       \<longrightarrow> ((i<((length (z#zs))*(length y)))
                       \<longrightarrow> ((vec_vec_Tensor zs y)!(i -(length y))) 
                               = f 
                                  (zs!((i -(length y)) div (length y))) 
                                  (y!((i -(length y)) mod (length y))))
                                   = ((i<((length zs)*(length y)))
                                      \<longrightarrow> ((vec_vec_Tensor zs y)!i) 
                                                = f 
                                                    (zs!(i div (length y))) 
                                                    (y!(i mod (length y))))"
       by auto
   with 6 have 
           "(i > (length y))
                \<longrightarrow>((i<((length (z#zs))*(length y)))
                \<longrightarrow> ((vec_vec_Tensor zs y)!(i -(length y))) 
                            = f 
                               (zs!((i -(length y)) div (length y))) 
                               (y!((i -(length y))  mod (length y))))" 
       by auto
   with 2 3 4 have  
            "(i > (length y))
                \<longrightarrow>((i<((length (z#zs))*(length y)))
                \<longrightarrow>((vec_vec_Tensor (z#zs) y)!i) 
                         =  f 
                               ((z#zs)!(i div (length y))) 
                               (y!(i mod (length y))))"
       by auto
    then show ?thesis  by auto
  qed
  have "((length y) = i) 
                     \<longrightarrow> ((i < (length (z#zs)*(length y)))
                     \<longrightarrow> ((vec_vec_Tensor (z#zs) y)!i) 
                                          = f 
                                              ((z#zs)!(i div (length y))) 
                                              (y!(i mod (length y))))"
  proof-
    have 1:"(i = (length y)) 
                  \<longrightarrow> ((vec_vec_Tensor (z#zs) y)!i) 
                                        = (vec_vec_Tensor zs y)!0" 
           using vec_vec_Tensor_simpl2   by auto
    have 2:"(i = length y) \<longrightarrow> (i mod (length y)) = 0" 
           by auto
    have 3:"(i = length y) \<longrightarrow> (i div (length y)) = 1" 
           using 4 assms div_self less_numeral_extra(3)
           by auto
    have 4: "(i = length y) 
                  \<longrightarrow> ((i < (length (z#zs))*(length y)) 
                               = (0 < (length zs)*(length y)))" 
           by auto
    have "(z#zs)!1 = (zs!0)" 
           by auto
    with 3 have 5:" (i = length y) 
                              \<longrightarrow> ((z#zs)!(i div (length y))) = (zs!0)" 
           by auto 
    have " \<forall>i.((i < (length zs)*(length y))
                               \<longrightarrow>((vec_vec_Tensor (zs) y)!i) 
                                             = f 
                                                 ((zs)!(i div (length y))) 
                                                 (y!(i mod (length y))))" 
           using Cons.hyps by auto  
    with 4 have 6:"(i = length y) 
                           \<longrightarrow> ((0 < ((length zs)*(length y)))
                              \<longrightarrow> (((vec_vec_Tensor (zs) y)!0) 
                                       = f ((zs)!0) (y!0))) 
                                         = ((i < ((length zs)*(length y)))
                                               \<longrightarrow>(((vec_vec_Tensor zs y)!i) 
                                                = f 
                                                    ((zs)!(i div (length y)))
                                                    (y!(i mod (length y)))))" 
           by auto
    have 7: "(0 div (length y)) = 0" 
           by auto
    have 8: " (0 mod (length y)) = 0" 
           by auto
    have 9: "(0 < ((length zs)*(length y))) 
                       \<longrightarrow> ((vec_vec_Tensor zs y)!0) 
                                           = f (zs!0) (y!0)" 
           using 7 8 Cons.hyps by auto
    with  4 5 8 have "(i = length y) 
                            \<longrightarrow> ((i < (length (z#zs))*(length y)) 
                                     \<longrightarrow> (((vec_vec_Tensor (zs) y)!0) 
                                             = f ((zs)!0) (y!0)))" 
           by auto
    with 1 2 5 have "(i = length y) 
                             \<longrightarrow> ((i < (length (z#zs))*(length y)) 
                                 \<longrightarrow> (((vec_vec_Tensor ((z#zs)) y)!i) 
                                            = f 
                                                 ((z#zs)!(i div (length y))) 
                                                 (y!(i mod (length y)))))" 
           by auto
    then show ?thesis by auto
  qed
  with step2 have step4: 
            "(i \<ge> (length y)) 
                      \<longrightarrow>  ((i < (length (z#zs))*(length y)) 
                       \<longrightarrow> (((vec_vec_Tensor ((z#zs)) y)!i) 
                                    = f 
                                         ((z#zs)!(i div (length y))) 
                                         (y!(i mod (length y)))))" 
         by auto
  have "(i < (length y)) \<or> (i \<ge> (length y))" 
         by auto
  with step1 step4 have 
            "((i < (length (z#zs))*(length y)) 
                       \<longrightarrow> (((vec_vec_Tensor ((z#zs)) y)!i) 
                                = f 
                                    ((z#zs)!(i div (length y))) 
                                     (y!(i mod (length y)))))" 
         using logic by (metis "6" "7" 35) 
  then show ?case by auto
qed

text\<open>a few more results that will be used later on\<close>

lemma nat_int:  "nat (int x + int y) = x + y"
 using nat_int of_nat_add by auto

lemma int_nat_equiv: "(x > 0) \<longrightarrow> (nat ((int x) + -1)+1) = x"
proof-
 have "1 = nat (int 1)" 
   by auto
 have "-1 = -int 1" 
   by auto
 then have 1:"(nat ((int x) + -1)+1) 
                      = (nat ((int x) + -1) + (nat (int 1)))" 
   by auto
 then have 2:"(x > 0) 
                 \<longrightarrow> nat ((int x) + -1 ) + (nat (int 1)) 
                                 =  (nat (((int x)  + -1) + (int 1)))" 
   using of_nat_add nat_int by auto
 have "(nat (((int x)  + -1) + (int 1))) = (nat ((int x) + -1 + (int 1)))" 
   by auto
 then have "(nat (((int x)  + -1) + (int 1))) = (nat ((int x)))" 
   by auto
 then have "(nat (((int x)  + -1) + (int 1))) = x" 
   by auto
 with 1 2 have " (x > 0) \<longrightarrow> nat ((int x) + -1 ) + 1 = x" 
   by auto
 then show ?thesis by auto
qed 

lemma list_int_nat: "(k>0) \<longrightarrow> ((x#xs)!k = xs!(nat ((int k)+-1)))"  
proof-
 fix  j
 have " ((x#xs)!(k+1) = xs!k)" 
      by auto
 have "j = (k+1) \<longrightarrow> (nat ((int j)+-1)) = k" 
      by auto
 moreover have "(nat ((int j)+-1)) = k 
                  \<longrightarrow> ((nat ((int j)+-1)) + 1) = (k +1)" 
      by auto
 moreover have "(j>0)\<longrightarrow>(((nat ((int j)+-1)) + 1) = j)" 
      using  int_nat_equiv by (auto)
 moreover have "(k>0) \<longrightarrow> ((x#xs)!k = xs!(nat ((int k)+-1)))" 
      using Suc_eq_plus1 int_nat_equiv nth_Cons_Suc by (metis)
  from this show ?thesis by auto
qed



lemma row_length_eq:
 "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) 
   \<longrightarrow> 
    (row_length (a#b#N) = (row_length (b#N)))" 
proof-
 have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) 
                        \<longrightarrow> (b \<in> set (a#b#M))" 
           by auto
 moreover have 
         "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) 
                 \<longrightarrow> (Ball (set (a#b#N)) (vec (row_length (a#b#N))))"
           using mat_def by metis
 moreover have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) 
                  \<longrightarrow> (b \<in> (set (a#b#N)))
                    \<longrightarrow> (vec (row_length (a#b#N)) b)"  
           by (metis calculation(2))
 then have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) 
                         \<longrightarrow> (length b) = (row_length (a#b#N))" 
            using vec_def by auto
 then have "(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) 
                          \<longrightarrow> (row_length (b#N)) 
                                       = (row_length (a#b#N))" 
            using row_length_def by auto
 then show ?thesis by auto
qed

text\<open>The following theorem tells us the relationship between entries of 
vec\_mat\_Tensor v M and entries of v and M respectivety\<close>

theorem vec_mat_Tensor_elements: 
 "\<forall>i.\<forall>j.
  (((i<((length v)*(row_length M)))
  \<and>(j < (length M)))
  \<and>(mat (row_length M) (length M) M)
   \<longrightarrow> ((vec_mat_Tensor v M)!j!i) 
               = f (v!(i div (row_length M))) (M!j!(i mod (row_length M))))"
 apply(rule allI)
 apply(rule allI)
 proof(induct M)
  case Nil
   have "row_length [] = 0" 
       using row_length_def by auto
   from this 
      have "(length v)*(row_length []) = 0" 
       by auto
   from this 
      have "((i<((length v)*(row_length [])))\<and>(j < (length []))) \<longrightarrow> False" 
       by auto
   moreover have "vec_mat_Tensor v [] = []" 
       by auto 
   moreover have "(((i<((length v)*(row_length [])))\<and>(j < (length [])))
                  \<longrightarrow> ((vec_mat_Tensor v [])!j!i) 
                                = f (v!(i div (row_length []))) ([]!j!(i mod (row_length []))))"
       by auto
   from this 
       show ?case by auto
  next
  case (Cons a M)
   have "(((i<((length v)*(row_length (a#M))))
       \<and>(j < (length (a#M))))
       \<and>(mat (row_length (a#M)) (length (a#M)) (a#M))
           \<longrightarrow> ((vec_mat_Tensor v (a#M))!j!i) 
                  = f 
                      (v!(i div (row_length (a#M)))) 
                      ((a#M)!j!(i mod (row_length (a#M)))))"
   proof(cases a)
    case Nil
     have "row_length ([]#M) = 0" 
          using row_length_def by auto
     then have 1:"(length v)*(row_length ([]#M)) = 0" 
          by auto
     then have "((i<((length v)*(row_length ([]#M))))
                \<and>(j < (length ([]#M)))) \<longrightarrow> False" 
          by auto
     moreover have 
                 "(((i<((length v)*(row_length ([]#M))))
                  \<and>(j < (length ([]#M))))
                     \<longrightarrow> ((vec_mat_Tensor v ([]#M))!j!i) = 
                                   f 
                                        (v!(i div (row_length ([]#M)))) 
                                        ([]!j!(i mod (row_length ([]#M)))))"
          using calculation by auto 
     then show ?thesis using Nil 1 less_nat_zero_code by (metis )
    next
    case (Cons x xs)
     have 1:"(a#M)!(j+1) = M!j" by auto
     have "(((i<((length v)*(row_length M)))
           \<and>(j < (length M)))
           \<and>(mat (row_length M) (length M) M)
             \<longrightarrow> ((vec_mat_Tensor v M)!j!i) = f 
                                               (v!(i div (row_length M))) 
                                               (M!j!(i mod (row_length M))))" 
          using Cons.hyps by auto
     have 2: "(row_length (a#M)) = (length a)" 
          using row_length_def by auto
     then have 3:"(i< (row_length (a#M))*(length v)) 
                              = (i < (length a)*(length v))" 
          by auto
     have "a \<noteq> []" 
          using Cons by auto
     then have 4:
         "\<forall>i.((i < (length a)*(length v)) 
              \<longrightarrow>  ((vec_vec_Tensor v a)!i) = f 
                                               (v!(i div (length a))) 
                                               (a!(i mod (length a))))" 
          using vec_vec_Tensor_elements Cons.hyps mult.commute 
          by (simp add: mult.commute vec_vec_Tensor_elements)
     have "(vec_mat_Tensor v (a#M))!0 = (vec_vec_Tensor v a)" 
          using vec_mat_Tensor.simps(2) by auto
     with 2 4 have 5: 
       "\<forall>i.((i < (row_length (a#M))*(length v)) 
          \<longrightarrow>  ((vec_mat_Tensor v (a#M))!0!i) 
                                   = f 
                                       (v!(i div (row_length (a#M)))) 
                                       ((a#M)!0!(i mod (row_length (a#M)))))" 
          by auto 
     have "length (a#M)>0" 
          by auto
     with 5 have 6: 
       "(j = 0)\<longrightarrow>
                    ((((i < (row_length (a#M))*(length v)) 
                    \<and>(j < (length (a#M))))
                    \<and>(mat (row_length (a#M)) (length (a#M)) (a#M))  
                         \<longrightarrow>  ((vec_mat_Tensor v (a#M))!j!i) 
                               = f 
                                    (v!(i div (row_length (a#M)))) 
                                    ((a#M)!j!(i mod (row_length (a#M))))))" 
          by auto 
     have "(((i < (row_length (a#M))*(length v))
         \<and>(j < (length (a#M))))
         \<and>(mat (row_length (a#M)) (length (a#M)) (a#M)) 
          \<longrightarrow>  
           ((vec_mat_Tensor v (a#M))!j!i) = 
                                f 
                                         (v!(i div (row_length (a#M)))) 
                                         ((a#M)!j!(i mod (row_length (a#M)))))" 
     proof(cases M)
      case Nil
       have "(length (a#[])) = 1" 
              by auto
       then have "(j<(length (a#[]))) = (j = 0)" 
              by auto
       then have "((((i < (row_length (a#[]))*(length v)) 
               \<and>(j < (length (a#[]))))
               \<and> (mat (row_length (a#[])) (length (a#[])) (a#[]))   
                  \<longrightarrow>  ((vec_mat_Tensor v (a#[]))!j!i) 
                                 = f 
                                    (v!(i div (row_length (a#[])))) 
                                     ((a#[])!j!(i mod (row_length (a#[]))))))" 
              using 6 Nil by auto
       then show ?thesis using Nil by auto 
      next
      case (Cons b N)
       have 7:"(mat  (row_length (a#b#N))  (length (a#b#N)) (a#b#N)) 
               \<longrightarrow> row_length (a#b#N) = (row_length (b#N))" 
              using row_length_eq by metis
       have 8: "(j>0) 
            \<longrightarrow> ((vec_mat_Tensor v (b#N))!(nat ((int j)+-1))) 
                                  = (vec_mat_Tensor v (a#b#N))!j"
              using vec_mat_Tensor.simps(2) using list_int_nat by metis
       have 9: "(j>0) 
                 \<longrightarrow> (((i < (row_length (b#N))*(length v))
                    \<and>((nat ((int j)+-1)) < (length (b#N))))
                    \<and>(mat (row_length (b#N)) (length (b#N)) (b#N)) 
                      \<longrightarrow>  
             ((vec_mat_Tensor v (b#N))!(nat ((int j)+-1))!i) 
                    = f 
                      (v!(i div (row_length (b#N)))) 
                      ((b#N)!(nat ((int j)+-1))!(i mod (row_length (b#N)))))"
              using Cons.hyps Cons mult.commute by metis
       have "(j>0) \<longrightarrow> ((nat ((int j) + -1)) < (length (b#N))) 
                           \<longrightarrow> ((nat ((int j) + -1) + 1) < length (a#b#N))"
              by auto
       then have 
           "(j>0) 
                 \<longrightarrow> ((nat ((int j) + -1)) < (length (b#N))) = (j < length (a#b#N))"
              by auto
       then have  
         "(j>0) 
          \<longrightarrow> (((i < (row_length (b#N))*(length v)) \<and> (j < length (a#b#N)))
              \<and>(mat (row_length (b#N)) (length (b#N)) (b#N))   \<longrightarrow>  
                    ((vec_mat_Tensor v (b#N))!(nat ((int j)+-1))!i) 
            = f 
                (v!(i div (row_length (b#N)))) 
                ((b#N)!(nat ((int j)+-1))!(i mod (row_length (b#N)))))"
              using Cons.hyps Cons mult.commute by metis
       with 8 have "(j>0) 
                 \<longrightarrow> (((i < (row_length (b#N))*(length v)) 
                     \<and> (j < length (a#b#N)))
                     \<and> (mat (row_length (b#N)) (length (b#N)) (b#N))   
                      \<longrightarrow>  
         ((vec_mat_Tensor v (a#b#N))!j!i) 
                = f 
                    (v!(i div (row_length (b#N)))) 
                    ((b#N)!(nat ((int j)+-1))!(i mod (row_length (b#N)))))"
              by auto
       also have "(j>0) \<longrightarrow> (b#N)!(nat ((int j)+-1)) = (a#b#N)!j" 
              using list_int_nat by metis
       moreover have " (j>0) \<longrightarrow> 
                    (((i < (row_length (b#N))*(length v)) 
                   \<and> (j < length (a#b#N)))
                   \<and> (mat (row_length (b#N)) (length (b#N)) (b#N))   
                     \<longrightarrow>  
                         ((vec_mat_Tensor v (a#b#N))!j!i) 
                                  = f 
                                      (v!(i div (row_length (b#N)))) 
                                      ((a#b#N)!j!(i mod (row_length (b#N)))))"
              by (metis calculation(1) calculation(2))
       then have  
           "(j>0) 
             \<longrightarrow> (((i < (row_length (b#N))*(length v)) 
                 \<and> (j < length (a#b#N)))
                 \<and> (mat (row_length (a#b#N)) (length (a#b#N)) (a#b#N))   
                 \<longrightarrow>  
                        ((vec_mat_Tensor v (a#b#N))!j!i) 
                              = f 
                                    (v!(i div (row_length (b#N)))) 
                                    ((a#b#N)!j!(i mod (row_length (b#N)))))"
              using reduct_matrix by (metis)
       moreover  have "(mat (row_length (a#b#N)) (length (a#b#N)) (a#b#N))
                   \<longrightarrow>(row_length (b#N)) = (row_length (a#b#N))" 
              by (metis "7" Cons)
       moreover have 10:"(j>0) 
                     \<longrightarrow> (((i < (row_length (a#b#N))*(length v)) 
                        \<and>(j < length (a#b#N)))
                        \<and>(mat (row_length (a#b#N)) (length (a#b#N)) (a#b#N))   \<longrightarrow>  
                         ((vec_mat_Tensor v (a#b#N))!j!i) 
                                = f (v!(i div (row_length (a#b#N)))) 
                                    ((a#b#N)!j!(i mod (row_length (a#b#N)))))"
              by (metis calculation(3) calculation(4))
       have "(j = 0) \<or> (j > 0)" 
              by auto
       with 6 10 logic have 
            "(((i < (row_length (a#b#N))*(length v)) 
            \<and> (j < length (a#b#N)))
            \<and> (mat (row_length (a#b#N)) (length (a#b#N)) (a#b#N))   
            \<longrightarrow>  
                ((vec_mat_Tensor v (a#b#N))!j!i) 
                      = f 
                          (v!(i div (row_length (a#b#N)))) 
                          ((a#b#N)!j!(i mod (row_length (a#b#N)))))"
              using  Cons by metis
       from this show ?thesis by (metis Cons)
     qed
     from this show ?thesis by (metis mult.commute)
   qed
 from this show ?case by auto
 qed

text\<open>The following theorem tells us about the relationship between
entries of tensor products of two matrices and the entries of matrices\<close>

theorem matrix_Tensor_elements: 
 fixes M1 M2
shows
 "\<forall>i.\<forall>j.(((i<((row_length M1)*(row_length M2)))
       \<and>(j < (length M1)*(length M2)))
       \<and>(mat (row_length M1) (length M1) M1)
       \<and>(mat (row_length M2) (length M2) M2)
            \<longrightarrow> ((M1 \<otimes> M2)!j!i) = 
                     f  
                        (M1!(j div (length M2))!(i div (row_length M2))) 
                        (M2!(j mod length M2)!(i mod (row_length M2))))"
 apply(rule allI)
 apply(rule allI)
 proof(induct M1)
 case Nil
  have "(row_length []) = 0" 
          using row_length_def by auto
  then have "(i< ((row_length [])*(row_length M2))) \<longrightarrow> False" 
          by auto
  from this have "((i<((row_length [])*(row_length M2)))
                 \<and>(j < (length [])*(length M2)))
                 \<and>(mat (row_length []) (length []) [])
                 \<and>(mat (row_length M2) (length M2) M2) 
                                                 \<longrightarrow> False" 
          by auto
  moreover have "([] \<otimes> M2) = []" 
          by auto
  moreover have 
          "((i<((row_length [])*(row_length M2)))
           \<and>(j < (length [])*(length M2)))
           \<and>(mat (row_length []) (length []) [])
           \<and>(mat (row_length M2) (length M2) M2) 
               \<longrightarrow> (([] \<otimes> M2)!j!i) = 
                           f  
                             ([]!(j div (length []))!(i div (row_length M2))) 
                              (M2!(j mod length [])!(i mod (row_length M2)))" 
          by auto
  then show ?case by auto
 next
 case (Cons v M)
  fix a
  have 0:"(v#M) \<otimes> M2 = (vec_mat_Tensor v M2)@(Tensor M M2)" 
          by auto
  then have 1:
        "(j<(length M2)) \<longrightarrow> ( ((v#M) \<otimes> M2)!j = (vec_mat_Tensor v M2)!j)" 
          using append_simpl vec_mat_Tensor_length by metis
  have " (((i<((length a)*(row_length M2)))
      \<and>(j < (length M2)))\<and>(mat (row_length M2) (length M2) M2)
  \<longrightarrow> ((vec_mat_Tensor a M2)!j!i) = f (a!(i div (row_length M2))) (M2!j!(i mod (row_length M2))))"
          using vec_mat_Tensor_elements by auto
  have "(j < (length M2)) \<longrightarrow> (j div (length M2)) = 0" 
          by auto
  then have 2:"(j < (length M2)) \<longrightarrow> (v#M)!(j div (length M2)) = v" 
          by auto
  have "(j < (length M2)) \<longrightarrow> (j mod (length M2)) = j" 
          by auto
  moreover have "(j < (length M2)) \<longrightarrow> (v#M)!(j mod (length M2)) = (v#M)!j" 
          by auto
  have step0:
    "(j < (length M2)) \<longrightarrow> 
               (((i<((length v)*(row_length M2)))
              \<and>(j < (length M2) * (length (v#M))))
              \<and>(mat (row_length M2) (length M2) M2)
                  \<longrightarrow> ((Tensor (v#M) M2)!j!i)  
                     = f 
                         ((v#M)!(j div (length M2))!(i div (row_length M2))) 
                         (M2!(j mod (length M2))!(i mod (row_length M2))))" 
          using 2 1  calculation(1) vec_mat_Tensor_elements by auto
  have step1: 
     "(j < (length M2)) 
        \<longrightarrow> (((i<((row_length (v#M))*(row_length M2)))
            \<and>(j <  (length (v#M))*(length M2)))
            \<and>(mat (row_length (v#M)) (length (v#M)) (v#M))
            \<and>(mat (row_length M2) (length M2) M2)
                 \<longrightarrow> ((Tensor (v#M) M2)!j!i) =
                   f 
                     ((v#M)!(j div (length M2))!(i div (row_length M2))) 
                     (M2!(j mod (length M2))!(i mod (row_length M2))))" 
          using row_length_def  step0 by auto
  from 0 have 3: 
        "(j \<ge> (length M2)) \<longrightarrow> ((v#M) \<otimes> M2)!j = (M \<otimes> M2)!(j - (length M2))" 
          using vec_mat_Tensor_length add.commute append_simpl2 by metis
  have 4:
      "(j \<ge> (length M2)) \<longrightarrow>
                 (((i<((row_length M)*(row_length M2)))
                 \<and>((j-(length M2)) < (length M)*(length M2)))
                 \<and>(mat (row_length M) (length M) M)
                 \<and>(mat (row_length M2) (length M2) M2)
               \<longrightarrow> ((M \<otimes> M2)!(j-(length M2))!i) 
              = f 
                 (M!((j-(length M2)) div (length M2))!(i div (row_length M2))) 
                 (M2!((j-(length M2)) mod length M2)!(i mod (row_length M2))))" 
          using Cons.hyps by auto
  moreover have "(mat (row_length (v#M)) (length (v#M)) (v#M))
                              \<longrightarrow>(mat (row_length M) (length M) M)"
          using reduct_matrix by auto
  moreover have 5:
      "(j \<ge> (length M2)) 
        \<longrightarrow> (((i<((row_length M)*(row_length M2)))
         \<and>((j-(length M2)) < (length M)*(length M2)))
         \<and>(mat (row_length (v#M)) (length (v#M)) (v#M))
         \<and>(mat (row_length M2) (length M2) M2)
         \<longrightarrow> ((M \<otimes> M2)!(j-(length M2))!i) 
              = f 
                (M!((j-(length M2)) div (length M2))!(i div (row_length M2))) 
                (M2!((j-(length M2)) mod length M2)!(i mod (row_length M2))))"
          using 4 calculation(3) by metis
  have "(((j-(length M2)) < (length M)*(length M2))) 
                        \<longrightarrow> (j < ((length M)+1)*(length M2))" 
          by auto
  then have 6:
        "(((j-(length M2)) < (length M)*(length M2))) 
              \<longrightarrow> 
               (j < ((length (v#M))*(length M2)))" 
          by auto
  have 7: 
      "(j \<ge> (length M2)) 
        \<longrightarrow> 
          ((j-(length M2)) div (length M2)) = ((j div (length M2)) - 1)"
          using  add_diff_cancel_left' div_add_self1 div_by_0 
                 le_imp_diff_is_add add.commute zero_diff
          by metis
  then have 8:
      "(j \<ge> (length M2)) 
         \<longrightarrow> 
          M!((j-(length M2)) div (length M2)) 
                      = M!((j div (length M2)) - 1)" 
          by auto
  have step2:
   "(j \<ge> (length M2)) 
      \<longrightarrow>
       (((i<((row_length (v#M))*(row_length M2)))
       \<and>(j < (length (v#M))*(length M2)))
       \<and>(mat (row_length (v#M)) (length (v#M)) (v#M))
       \<and>(mat (row_length M2) (length M2) M2))
      \<longrightarrow>(((v#M) \<otimes> M2)!j!i) = 
                          f 
                         ((v#M)!(j div (length M2))!(i div (row_length M2))) 
                         (M2!(j mod length M2)!(i mod (row_length M2)))"
  proof(cases M2)
   case Nil
    have "(0 = ((row_length (v#M))*(row_length M2)))" 
          using row_length_def Nil mult_0_right by auto
    then have "(i < ((row_length (v#M))*(row_length M2))) \<longrightarrow> False" 
          by auto
    then have " (j \<ge> (length M2)) 
                 \<longrightarrow>(((i<((row_length (v#M))*(row_length M2)))
                    \<and>(j < (length (v#M))*(length M2)))
                    \<and>(mat (row_length (v#M)) (length (v#M)) (v#M))
                    \<and>(mat (row_length M2) (length M2) M2)) 
                            \<longrightarrow> False"
          by auto
    then show ?thesis by auto
   next
   case (Cons w N)
    fix k
    have "(k < (length M))\<and> (k \<ge> 1) \<longrightarrow> M!(k - 1)  = (v#M)!k" 
          using   not_one_le_zero nth_Cons' by auto
    have "(j \<ge> (length (w#N))) \<longrightarrow> (j div (length (w#N))) \<ge> 1"
          using  div_le_mono div_self length_0_conv neq_Nil_conv  by metis
    moreover have "(j \<ge> (length (w#N))) \<longrightarrow> (j div (length (w#N)))- 1  \<ge> 0" 
          by auto
    moreover have "(j \<ge> (length (w#N))) 
                          \<longrightarrow> M!((j div (length (w#N)))- 1 ) 
                                 = (v#M)!(j div (length (w#N)))" 
          using calculation(1) not_one_le_zero nth_Cons' by auto
    from this 7 have 9:" (j \<ge> (length (w#N))) 
                         \<longrightarrow>  M!((j-(length (w#N))) div (length (w#N))) 
                                   = (v#M)!(j div (length (w#N)))" 
          using Cons by auto
    have 10: "(j \<ge> (length (w#N))) 
                     \<longrightarrow>  ((j-(length (w#N))) mod (length (w#N))) 
                                   = (j mod(length (w#N)))" 
          using mod_if not_less by auto 
    with 5 9  have 
     "(j \<ge> (length (w#N))) \<longrightarrow>
     ((i<((row_length M)*(row_length (w#N))))
     \<and>((j-(length (w#N))) < (length M)*(length (w#N)))
     \<and>(mat (row_length (v#M)) (length (v#M)) (v#M)) 
     \<and>(mat (row_length (w#N)) (length (w#N)) (w#N)))
     \<longrightarrow> (((M \<otimes> (w#N))!(j-(length (w#N)))!i) 
          = f 
              ((v#M)!(j div (length (w#N)))!(i div (row_length (w#N))))
              ((w#N)!(j mod length (w#N))!(i mod (row_length (w#N)))))" 
          using Cons by auto 
    then have 
      "(j \<ge> (length (w#N))) \<longrightarrow>
                ((i<((row_length M)*(row_length (w#N))))
                \<and>(j <(length (v#M))*(length (w#N)))
                \<and>(mat (row_length (v#M)) (length (v#M)) (v#M)) 
                \<and>(mat (row_length (w#N)) (length (w#N)) (w#N)))
                \<longrightarrow> (((M \<otimes> (w#N))!(j-(length (w#N)))!i) 
                 = f 
                    ((v#M)!(j div (length (w#N)))!(i div (row_length (w#N))))
                    ((w#N)!(j mod length (w#N))!(i mod (row_length (w#N)))))" 
          using 6 by auto
    then have 11: 
     "(j \<ge> (length (w#N))) \<longrightarrow>
            ((i<((row_length M)*(row_length (w#N))))
            \<and>(j <(length (v#M))*(length (w#N)))
            \<and>(mat (row_length (v#M)) (length (v#M)) (v#M))
            \<and>(mat (row_length (w#N)) (length (w#N)) (w#N)))
            \<longrightarrow> (((v#M) \<otimes> (w#N))!j!i) = 
                    f 
                    ((v#M)!(j div (length (w#N)))!(i div (row_length (w#N))))
                    ((w#N)!(j mod length (w#N))!(i mod (row_length (w#N))))" 
          using 3 Cons by auto
    have 
      "(j \<ge> (length (w#N))) \<longrightarrow>
              ((i<((row_length (v#M))*(row_length (w#N))))
              \<and>(j <(length (v#M))*(length (w#N)))
              \<and>(mat (row_length (v#M)) (length (v#M)) (v#M))
              \<and>(mat (row_length (w#N)) (length (w#N)) (w#N)))
                     \<longrightarrow> (((v#M) \<otimes> (w#N))!j!i) 
                = f 
                    ((v#M)!(j div (length (w#N)))!(i div (row_length (w#N))))
                    ((w#N)!(j mod length (w#N))!(i mod (row_length (w#N))))"
    proof(cases M)
     case Nil 
      have Nil0:"(length (v#[])) = 1" 
                by auto
      then have Nil1:
             "(j <(length (v#[]))*(length (w#N))) = (j< (length (w#N)))" 
                by (metis Nil nat_mult_1) 
      have 
              "row_length (v#[]) = (length v)" 
                using row_length_def by auto
      then have Nil2:
              "(i<((row_length (v#M))*(row_length (w#N)))) 
                                 = (i<((length v)*(row_length (w#N))))"
                using Nil by auto
      then have "(j< (length (w#N))) \<longrightarrow> (j div (length (w#N))) = 0" 
                by auto
      from this have Nil3:
                 "(j< (length (w#N))) \<longrightarrow> (v#M)!(j div (length (w#N))) = v" 
                using Nil by auto
      then have Nil4:
                 "(j< (length (w#N))) \<longrightarrow> (j mod (length (w#N))) = j" 
                by auto
      then have Nil5:"(v#M) \<otimes> (w#N) = vec_mat_Tensor v (w#N)" 
                using Nil Tensor.simps(2) Tensor.simps(1)
                by auto
      from vec_mat_Tensor_elements have 
                      "(((i<((length v)*(row_length (w#N))))
                       \<and>(j < (length (w#N))))
                       \<and>(mat (row_length (w#N)) (length (w#N)) (w#N))
                          \<longrightarrow> ((vec_mat_Tensor v (w#N))!j!i) 
                                    = f 
                                       (v!(i div (row_length (w#N)))) 
                                       ((w#N)!j!(i mod (row_length (w#N)))))" 
                 by metis
      then have 
            "((i<((row_length (v#M))*(row_length (w#N))))
             \<and>(j < ((length (v#M))*(length (w#N))))
             \<and>(mat (row_length (w#N)) (length (w#N)) (w#N))
         \<longrightarrow> ((vec_mat_Tensor v (w#N))!j!i) 
                    = f (v!(i div (row_length (w#N)))) 
                        ((w#N)!j!(i mod (row_length (w#N)))))"
                using Nil1 Nil2 Nil by auto
      then have  
            "((i<((row_length (v#M))*(row_length (w#N))))
             \<and>(j < ((length (v#M))*(length (w#N))))
             \<and>(mat (row_length (w#N)) (length (w#N)) (w#N))
          \<longrightarrow> (((v#M)\<otimes>(w#N))!j!i) 
                     = f 
                        ((v#M)!(j div (length (w#N)))!(i div (row_length (w#N)))) 
                        ((w#N)!(j mod (length (w#N)))!(i mod (row_length (w#N)))))"
                using Nil3 Nil4  Nil5 Nil by auto
      then have 
             "((i<((row_length (v#M))*(row_length (w#N))))
             \<and>(j < ((length (v#M))*(length (w#N))))
             \<and>(mat (row_length (v#M)) (length (v#M)) (v#M))
             \<and>(mat (row_length (w#N)) (length (w#N)) (w#N))
                  \<longrightarrow> (((v#M)\<otimes>(w#N))!j!i) 
                       = f 
                         ((v#M)!(j div (length (w#N)))!(i div (row_length (w#N)))) 
                         ((w#N)!(j mod (length (w#N)))!(i mod (row_length (w#N)))))" by auto
      from this show ?thesis by auto
     next
     case (Cons u P)
      have "(mat (row_length (v#M)) (length (v#M)) (v#M)) \<longrightarrow> (row_length (v#M)) = (row_length M)"
          using Cons row_length_eq by metis
      from this 11 show ?thesis by auto
    qed
    from this show ?thesis using Cons by auto 
   qed 
   have "(j<(length M2)) \<or> (j \<ge> (length M2))" by auto
   from this step1 step2 logic have  
     "(((i<((row_length (v#M))*(row_length M2)))
      \<and>(j < (length M2) * (length (v#M))))
      \<and>(mat (row_length (v#M)) (length (v#M)) (v#M))
      \<and>(mat (row_length M2) (length M2) M2)        
      \<longrightarrow> ( ((v#M) \<otimes> M2)!j!i) 
                 = f 
                     ((v#M)!(j div (length M2))!(i div (row_length M2))) 
                     (M2!(j mod (length M2))!(i mod (row_length M2))))" 
          using  mult.commute by metis
   from this show ?case by (metis mult.commute)
 qed
   

text\<open>we restate the theorem in two different forms for convenience 
of reuse\<close>

theorem effective_matrix_tensor_elements:
  " (((i<((row_length M1)*(row_length M2))) 
  \<and>(j < (length M1)*(length M2)))
  \<and>(mat (row_length M1) (length M1) M1)
  \<and>(mat (row_length M2) (length M2) M2)
 \<Longrightarrow> ((M1 \<otimes> M2)!j!i) 
   = f (M1!(j div (length M2))!(i div (row_length M2))) 
       (M2!(j mod length M2)!(i mod (row_length M2))))"
 using matrix_Tensor_elements by auto

theorem effective_matrix_tensor_elements2:
 assumes  " i<(row_length M1)*(row_length M2)"
 and "j < (length M1)*(length M2)"
 and "mat (row_length M1) (length M1) M1"
 and "mat (row_length M2) (length M2) M2"
 shows "(M1 \<otimes> M2)!j!i = 
             (M1!(j div (length M2))!(i div (row_length M2)))
              * (M2!(j mod length M2)!(i mod (row_length M2)))"
 using assms matrix_Tensor_elements by auto

text\<open>the following lemmas are useful in proving associativity of tensor
products\<close>

lemma div_left_ineq:
 assumes "(x::nat) < y*z" 
 shows " (x div z) < y"
proof(rule ccontr)
 assume 0: " \<not>((x div z) < y)"
 then have 1:" x div z \<ge> y"
          by auto
 then have 2:"(x div z)*z \<ge> y*z"
          by auto
 then have 3:"(x div z)*z + (x mod z) = z"
          using div_mult_mod_eq 
          add_leD1 assms minus_mod_eq_div_mult [symmetric] le_diff_conv2 mod_less_eq_dividend not_less
          by metis 
 then have 4:"(x div z)*z \<le> z"
          by auto
 then have 5:"z \<ge> y*z"
          using 2 by auto
 then have 6:"z div z \<ge> (y*z) div z"
          by auto
 then have "(y*z) div z \<le> 1"
          by auto                
 with 6 have "1 \<ge> y"
          using 1 3 assms div_self less_nat_zero_code mult_zero_left 
          mult.commute mod_div_mult_eq
          by auto
 then have 7:"(y = 0) \<or> (y = 1)"
          by auto
 have "(y = 0 ) \<Longrightarrow> x<0"
          using assms by auto
 moreover have "x \<ge> 0"
          by auto
 then have 8:"(y = 0) \<Longrightarrow> False"
          using calculation  less_nat_zero_code by auto
 moreover have "(y = 1) \<Longrightarrow> ( x < z)"
          using assms by auto
 then have "(y = 1) \<Longrightarrow> (x div z) = 0"
          by (metis div_less) 
 then have "(y = 1) \<Longrightarrow>(x div z) < y"
          by auto
 then have "(y = 1) \<Longrightarrow> False"
          using 0 by auto
 then show False using 7 8 by auto
qed

lemma div_right_ineq:
 assumes "(x::nat) < y*z" 
 shows " (x div y) < z"
 using assms div_left_ineq mult.commute   by (metis)

text\<open>In the following theorem, we obtain columns of vec$\_$mat$\_$Tensor of 
a vector v and a matrix M in terms of the vector v and columns of the 
matrix M\<close>

lemma col_vec_mat_Tensor_prelim:
 " \<forall>j.(j < (length M) 
     \<longrightarrow>
      col (vec_mat_Tensor v M) j = vec_vec_Tensor v (col M j))"
 unfolding col_def 
 apply(rule allI)
 proof(induct M)
  case Nil
   show ?case using Nil by auto
  next
  case (Cons w N)
   have Cons_1:"vec_mat_Tensor v (w#N) 
                        = (vec_vec_Tensor v w)#(vec_mat_Tensor v N)"
              using vec_mat_Tensor.simps Cons by auto
   then show ?case
   proof(cases j)
    case 0
     have "vec_mat_Tensor v (w#N)!0 =  (vec_vec_Tensor v w)"
              by auto
     then show ?thesis using 0 by auto
    next
    case (Suc k) 
     have " vec_mat_Tensor v (w#N)!j = (vec_mat_Tensor v N)!(k)"  
              using Cons_1 Suc by auto
     moreover have "j < length (w#N) \<Longrightarrow> k < length N"
              using Suc  by (metis length_Suc_conv not_less_eq)
     moreover then have "k < length (N) 
                  \<Longrightarrow> (vec_mat_Tensor v N)!k =   vec_vec_Tensor v (N!k)"
              using Cons.hyps  by auto
     ultimately show ?thesis using Suc by auto
   qed
 qed

lemma col_vec_mat_Tensor:fixes j M v
 assumes "j < (length M)" 
 shows "col (vec_mat_Tensor v M) j = vec_vec_Tensor v (col M j)"
  using col_vec_mat_Tensor_prelim assms by auto

lemma  col_formula:
 fixes M1 and M2
 shows "\<forall>j.((j < (length M1)*(length M2)) 
         \<and> (mat (row_length M1) (length M1) M1)
         \<and> (mat (row_length M2) (length M2) M2)
         \<longrightarrow> col (M1 \<otimes> M2) j 
                =  vec_vec_Tensor 
                        (col M1 (j div length M2)) 
                        (col M2 (j mod length M2)))"
 apply (rule allI)
 proof(induct M1)
  case Nil
   show ?case using Nil by auto
  next
  case (Cons v M)
   have "j < (length (v#M))*(length M2) 
       \<and> mat (row_length (v # M)) (length (v # M)) (v # M) 
       \<and> mat (row_length M2) (length M2) M2 \<Longrightarrow>
       (col (v # M \<otimes> M2) j 
                 = vec_vec_Tensor 
                            (col (v # M) (j div length M2)) 
                            (col M2 (j mod length M2)))"
   proof-
    fix k
    assume 0:"j < (length (v#M))*(length M2) 
              \<and> mat (row_length (v # M)) (length (v # M)) (v # M) 
              \<and> mat (row_length M2) (length M2) M2"
    then have 1:"mat (row_length M) (length M) M"
             by (metis reduct_matrix)
    have "j < (1+ length M)*(length M2)"
             using 0 by auto
    then have "j < (length M2)+  (length M)*(length M2)"
             by auto   
    then have 2:"j \<ge> (length M2) 
                          \<Longrightarrow> j- (length M2) < (length M)*(length M2)"
             using add_0_iff add_diff_inverse diff_is_0_eq 
                   less_diff_conv less_imp_le linorder_cases add.commute 
                   neq0_conv
             by (metis (hide_lams, no_types))
    have 3:"(v#M)\<otimes>M2 = (vec_mat_Tensor v M2)@(M \<otimes> M2)"
             using Tensor.simps by auto
    have "(col ((v#M)\<otimes>M2) j) = (col ((vec_mat_Tensor v M2)@(M \<otimes> M2)) j)"
             using col_def by auto
    then have "j < length (vec_mat_Tensor v M2) 
                   \<Longrightarrow> (col ((v#M)\<otimes>M2) j) = (col (vec_mat_Tensor v M2) j)"
             unfolding col_def using append_simpl by auto 
    then have 4:"j < length M2 \<Longrightarrow>
                        (col ((v#M)\<otimes>M2) j) = (col (vec_mat_Tensor v M2) j)"
             using vec_mat_Tensor_length by simp 
    then have "j < length M2 \<Longrightarrow>  
                  (col (vec_mat_Tensor v M2) j) 
                                      =  vec_vec_Tensor v (col M2 j)"
             using col_vec_mat_Tensor by auto
    then have 
           "j< length M2 \<Longrightarrow> 
                 (col (vec_mat_Tensor v M2) j) 
                            =  vec_vec_Tensor 
                                            ((v#M)!(j div length M2)) 
                                            (col M2 (j mod (length M2)))"
             by auto
    then have step_1:"j< length M2 \<Longrightarrow> 
                 (col ((v#M)\<otimes> M2) j) 
                             =  vec_vec_Tensor 
                                             ((v#M)!(j div length M2)) 
                                             (col M2 (j mod (length M2)))"
             using 4 by auto
    have 4:"j \<ge> length M2 
                  \<Longrightarrow> (col ((v#M)\<otimes>M2) j)= (M \<otimes> M2)!(j- (length M2))"
             unfolding col_def  using 3 append_simpl2 vec_mat_Tensor_length 
             by metis
    then have 5:
         "j \<ge> length M2 \<Longrightarrow> 
              col (M \<otimes> M2) (j-length M2) 
                     = vec_vec_Tensor 
                                (col M ((j-length M2) div length M2)) 
                                (col M2 ((j- length M2) mod length M2))"
             using 1 0 2 Cons by auto
    then have 6:
         "j \<ge> length M2 \<Longrightarrow> 
                 (j - length M2) div (length M2) + 1 = j div (length M2)"
             using 2  div_0 div_self 
                   le_neq_implies_less less_nat_zero_code 
                   monoid_add_class.add.right_neutral mult_0 mult_cancel2 
                   add.commute nat_div neq0_conv div_add_self1 le_add_diff_inverse      
             by metis
    then have 
           "j \<ge> length M2 \<Longrightarrow> 
                    ((j- length M2) mod length M2) = j mod (length M2)"
             using le_mod_geq by metis 
    with 6  have 7:
         "j \<ge> length M2 \<Longrightarrow> 
              col (M \<otimes> M2) (j-length M2) 
                     = vec_vec_Tensor (col M ((j-length M2) div length M2)) 
                                (col M2 (j mod length M2))"
             using 5 by auto
    moreover have "k<(length M) \<Longrightarrow> (col M k) = (col (v#M) (k+1))"
             unfolding col_def by auto
    ultimately have "j \<ge> length M2 \<Longrightarrow> 
              col (M \<otimes> M2) (j-length M2) 
                     = vec_vec_Tensor (col (v#M) (j div length M2)) 
                                (col M2 (j mod length M2))"
    proof-
     assume temp:"j \<ge> length M2 "
     have " j- (length M2) < (length M)*(length M2)"    
             using 2 temp by auto
     then have "(j- (length M2)) div (length M2) < (length M)"
             using div_right_ineq mult.commute by metis
     moreover have 
                 "((j- (length M2)) div (length M2)<(length M) 
                     \<longrightarrow> (col M ((j- (length M2)) div (length M2))) 
                          = (col (v#M) ((j- (length M2)) div (length M2)+1)))"
             unfolding col_def by auto
     ultimately have temp1:
                      "(col (v#M) (((j-length M2) div length M2)+1)) 
                                  = (col M (((j-length M2) div length M2)))"
             by auto
     then have "(col (v#M) (((j-length M2) div length M2)+1)) 
                                   = (col (v#M) (j div length M2))"
             using 6 temp by auto
     then show ?thesis using temp1 7 by (metis temp) 
    qed
    then have "j \<ge> length M2 \<Longrightarrow> 
              col ((v#M) \<otimes> M2) j 
                     = vec_vec_Tensor (col (v#M) (j div length M2)) 
                                (col M2 (j mod length M2))"
             using col_def 4 by metis
    then show ?thesis 
             using step_1  col_def le_refl nat_less_le nat_neq_iff
             by (metis)
   qed
   then show ?case by auto
 qed

lemma row_Cons:"row (v#M) i = (v!i)#(row M i)"
 unfolding row_def map_def by auto

lemma row_append:"row (A@B)i = (row A i)@(row B i)"
 unfolding row_def map_append by auto 

lemma row_empty:"row [] i = []"
 unfolding row_def by auto

lemma vec_vec_Tensor_right_empty:"vec_vec_Tensor x [] = []"
 using vec_vec_Tensor.simps times.simps  length_0_conv mult_0_right vec_vec_Tensor_length  
 by (metis)

lemma "vec_mat_Tensor v ([]#[]) = [[]] "
 using vec_mat_Tensor.simps by (metis vec_vec_Tensor_right_empty)

lemma "i<0 \<longrightarrow> [[]!i] = []"
 by auto

lemma row_vec_mat_Tensor_prelim:
 "\<forall>i.
     ((i < (length v)*(row_length M))\<and>(mat nr (length M) M) 
      \<longrightarrow> row (vec_mat_Tensor v M) i 
            = times (v!(i div row_length M)) (row M (i mod row_length M)))"
 apply(rule allI)
 proof(induct M)
  case Nil
   show ?case using Nil by (metis less_nat_zero_code mult_0_right row_length_Nil)
  next
  case (Cons w N) 
   have "row (vec_mat_Tensor v (w#N)) i 
                      =  row ((vec_vec_Tensor v w)#(vec_mat_Tensor v N)) i"
           using vec_mat_Tensor.simps by auto
   then have 1:"...   = ((vec_vec_Tensor v w)!i)#(row (vec_mat_Tensor v N) i)"
           using row_Cons by auto
   have 2:"row_length (w#N) = length w"
           using row_length_def by auto
   then have 3:"(mat nr (length (w#N)) (w#N)) \<Longrightarrow> nr = length w"
           using hd_in_set list.distinct(1) mat_uniqueness matrix_row_length by metis
   then have   "((i < (length v)*(row_length (w#N))) 
               \<and> (mat nr (length (w#N)) (w#N)) 
                 \<Longrightarrow> row (vec_mat_Tensor v (w#N)) i 
                           = times 
                                 (v!(i div row_length (w#N))) 
                                 (row (w#N) (i mod row_length (w#N))))" 
   proof-
    assume assms: "i < (length v)*(row_length (w#N)) 
                     \<and> (mat nr (length (w#N)) (w#N))"   
    show ?thesis    
    proof(cases N)
     case Nil
      have "row (vec_mat_Tensor v (w#N)) i = [(vec_vec_Tensor v w)!i]"
            using 1 vec_mat_Tensor.simps  Nil row_empty by auto  
      then show ?thesis
      proof(cases w)
       case Nil
        have "(vec_vec_Tensor v w) = []"
             using Nil vec_vec_Tensor_right_empty by auto
        moreover have " (length v)*(row_length (w#N)) = 0"
             using Nil row_length_def  by auto
        then have " [(vec_vec_Tensor v [])!i] = []"
             using assms less_nat_zero_code by metis
        ultimately show ?thesis 
             using vec_vec_Tensor.simps row_empty Nil assms list.distinct(1) by (metis)
       next
       case (Cons a w1)
        have 1:"w \<noteq> []"
             using Cons by auto
        then have "i < (length v)*(length w)"
             using assms row_length_def by auto
        then have "(vec_vec_Tensor v w)!i  
                                       = f 
                                           (v!(i div (length w))) 
                                           (w!(i mod (length w)))"
             using vec_vec_Tensor_elements 1 allI by auto
        then have "(row (vec_mat_Tensor v (w#N)) i)
                                = times 
                                      (v!(i div row_length (w#N))) 
                                      (row (w#N) (i mod (length w)))"
             using Cons vec_mat_Tensor.simps row_def  row_length_def 2 Nil row_Cons 
                   row_empty times.simps(1) times.simps(2)  by metis
        then show ?thesis using row_def 2 by metis
      qed
     next
     case (Cons w1 N1)
      have Cons_0:"row_length N = length w1"
             using Cons row_length_def by auto
      have "mat nr (length (w#w1#N1)) (w#w1#N1)"
             using assms Cons by auto
      then have Cons_1:
                     "mat (row_length (w#w1#N1)) (length (w#w1#N1)) (w#w1#N1)" 
             by (metis matrix_row_length)
      then have Cons_2:
                     "mat (row_length (w1#N1)) (length (w1#N1)) (w1#N1)" 
             by (metis reduct_matrix)
      then have Cons_3:"(length w1 = length w)"
             using Cons_1 
             unfolding mat_def row_length_def Ball_def vec_def 
             by (metis "2" Cons_0 Cons_1 local.Cons row_length_eq)  
      then have Cons_4:"mat nr (length (w1#N1)) (w1#N1)"                
             using 3 Cons_2 assms hd_conv_nth list.distinct(1) nth_Cons_0 row_length_def
             by metis  
      moreover have "i < (length v)*(row_length (w1#N1))"
             using assms Cons_3 row_length_def by auto
      ultimately have Cons_5:"row (vec_mat_Tensor v N) i 
                                  = times 
                                      (v ! (i div row_length N)) 
                                      (row N (i mod row_length N))"
             using Cons  Cons.hyps by auto 
      then show ?thesis
      proof(cases w)
       case Nil
        have "(vec_vec_Tensor v w) = []"
              using Nil vec_vec_Tensor_right_empty by auto
        moreover have " (length v)*(row_length (w#N)) = 0"
              using Nil row_length_def  by auto
        then have " [(vec_vec_Tensor v [])!i] = []"
              using assms   by (metis less_nat_zero_code)
        ultimately show ?thesis 
              using vec_vec_Tensor.simps row_empty Nil assms
              by (metis list.distinct(1))               
       next
       case (Cons a w2)
        have 1:"w \<noteq> []"
              using Cons by auto
        then have "i < (length v)*(length w)"
              using assms row_length_def by auto
        then have ConsCons_2:
                     "(vec_vec_Tensor v w)!i = f 
                                                 (v!(i div (length w))) 
                                                 (w!(i mod (length w)))"
              using vec_vec_Tensor_elements 1 allI by auto
        moreover have 
                      "times 
                              (v!(i div row_length (w#N))) 
                              (row (w#N) (i mod row_length (w#N))) 
                             = (f 
                                 (v!(i div (length w))) 
                                 (w!(i mod (length w))))
                                  #(times (v ! (i div row_length N)) 
                                          (row N (i mod row_length N)))"
        proof-
         have temp:"row_length (w#N) = (row_length N)"
                    using row_length_def 2 Cons_3 Cons_0 by auto
         have "(row (w#N) (i mod row_length (w#N))) 
                              = (w!(i mod (row_length (w#N))))
                                       #(row N (i mod row_length (w#N)))"
                     unfolding row_def  by auto                     
         then have "...
                              = (w!(i mod (length w)))
                                        #(row N (i mod row_length N))"
                     using Cons_3 3 assms 2 neq_Nil_conv row_Cons row_empty 
                           row_length_eq by (metis (hide_lams, no_types))
         then have "times 
                           (v!(i div row_length (w#N)))  
                           ((w!(i mod (length w)))
                             #(row N (i mod row_length N)))
                               = (f  
                                     (v!(i div row_length (w#N))) 
                                     (w!(i mod (length w))))
                                         #(times  (v!(i div row_length (w#N)))
                                                      (row N (i mod row_length N)))"
                     by auto
         then have "... =  (f  
                                       (v!(i div length w)) 
                                       (w!(i mod (length w))))
                                         #(times  (v!(i div row_length N))
                                                  (row N (i mod row_length N)))"         
                     using 3 Cons_3 assms temp row_length_def by auto 
                   then show ?thesis using times.simps 2 row_Cons temp by metis
                 qed
         then show ?thesis using Cons_5 ConsCons_2 1 
                                row_Cons vec_mat_Tensor.simps(2) by (metis)         
        qed
      qed
    qed             
    then show ?case by auto
 qed

text\<open>The following lemma gives us a formula for the row of a tensor of 
two matrices\<close>

lemma  row_formula:
 fixes M1 and M2
 shows "\<forall>i.((i < (row_length M1)*(row_length M2))
          \<and>(mat (row_length M1) (length M1) M1)
          \<and>(mat (row_length M2) (length M2) M2)
             \<longrightarrow> row (M1 \<otimes> M2) i 
                        =  vec_vec_Tensor 
                                 (row M1 (i div row_length M2)) 
                                 (row M2 (i mod row_length M2)))"
 apply(rule allI)
 proof(induct M1)
  case Nil
   show ?case using Nil by (metis less_nat_zero_code mult_0 row_length_Nil)
  next
  case (Cons v M)
   have 
    "((i < (row_length (v#M))*(row_length M2))  
    \<and> (mat (row_length (v#M)) (length (v#M)) (v#M))
    \<and> (mat (row_length M2) (length M2) M2)
     \<Longrightarrow> row ((v#M) \<otimes> M2) i =  vec_vec_Tensor 
                                    (row (v#M) (i div row_length M2)) 
                                    (row M2 (i mod row_length M2)))"
   proof-
    assume assms:
                 "(i < (row_length (v#M))*(row_length M2)) 
                 \<and>(mat (row_length (v#M)) (length (v#M)) (v#M))
                 \<and>(mat (row_length M2) (length M2) M2)"
    have 0:"i < (length v)*(row_length M2)"
             using assms row_length_def by auto  
    have 1:"mat (row_length M) (length M) M"
             using assms  reduct_matrix by (metis)
    have "row ((v#M)\<otimes>M2) i = row ((vec_mat_Tensor v M2)@(M \<otimes> M2)) i"
             by auto
    then have 2:"... = (row (vec_mat_Tensor v M2) i)@(row (M \<otimes> M2) i)"
             using row_append by auto 
    then show ?thesis
    proof(cases M)
     case Nil
      have "row ((v#M)\<otimes>M2) i = (row (vec_mat_Tensor v M2) i)"
                 using Nil 2 by auto
      moreover have "row (vec_mat_Tensor v M2) i =  times 
                                                (v!(i div row_length M2)) 
                                                (row M2 (i mod row_length M2))"
                 using row_vec_mat_Tensor_prelim assms 0 by auto
      ultimately show ?thesis using vec_vec_Tensor_def 
             Nil append_Nil2 vec_vec_Tensor.simps(1) 
             vec_vec_Tensor.simps(2) row_Cons row_empty  by (metis)
     next
     case (Cons w N)
      have Cons_Cons_1:"mat (row_length M) (length M) M"
                        using assms reduct_matrix by auto
      then have "row_length (w#N) = row_length (v#M)"
                        using assms Cons unfolding mat_def Ball_def vec_def  
                        using append_Cons  hd_in_set list.distinct(1) 
                        rotate1.simps(2) set_rotate1
                        by auto
      then have Cons_Cons_2:"i < (row_length M)*(row_length M2)"
                        using assms Cons by auto
      then have Cons_Cons_3:"(row (M \<otimes> M2) i) =  vec_vec_Tensor 
                                          (row M (i div row_length M2)) 
                                           (row M2 (i mod row_length M2))"
                        using Cons.hyps Cons_Cons_1 assms by auto
      moreover have "row (vec_mat_Tensor v M2) i   
                                            =  times 
                                               (v!(i div row_length M2)) 
                                               (row M2 (i mod row_length M2))"
                        using row_vec_mat_Tensor_prelim assms 0 by auto
      then have "row ((v#M)\<otimes>M2) i = 
                           (times 
                                   (v!(i div row_length M2)) 
                                    (row M2 (i mod row_length M2)))
                                      @(vec_vec_Tensor 
                                          (row M (i div row_length M2)) 
                                           (row M2 (i mod row_length M2)))"   
                        using 2 Cons_Cons_3 by auto
      moreover have "... = (vec_vec_Tensor 
                                        ((v!(i div row_length M2))
                                             #(row M (i div row_length M2)))
                                        (row M2 (i mod row_length M2)))"
                        using vec_vec_Tensor.simps(2) by auto
      moreover have "... = (vec_vec_Tensor (row (v#M) (i div row_length M2))
                                           (row M2 (i mod row_length M2)))" 
                        using row_Cons by metis
      ultimately show ?thesis by metis
    qed
   qed
   then show ?case by auto
 qed  

lemma  effective_row_formula:
 fixes M1 and M2
 assumes "i < (row_length M1)*(row_length M2)" 
     and "(mat (row_length M1) (length M1) M1)"
     and "(mat (row_length M2) (length M2) M2)"
 shows "row (M1 \<otimes> M2) i 
               =  vec_vec_Tensor 
                       (row M1 (i div row_length M2)) 
                       (row M2 (i mod row_length M2))"
  using assms row_formula by auto

lemma alt_effective_matrix_tensor_elements:
 " (((i<((row_length M2)*(row_length M3)))
 \<and>(j < (length M2)*(length M3)))
 \<and>(mat (row_length M2) (length M2) M2)
 \<and>(mat (row_length M3) (length M3) M3)
 \<Longrightarrow> ((M2 \<otimes> M3)!j!i) = f (M2!(j div (length M3))!(i div (row_length M3))) 
(M3!(j mod length M3)!(i mod (row_length M3))))"
  using matrix_Tensor_elements by auto
            

lemma trans_impl:"(\<forall> i j.(P i j \<longrightarrow> Q i j))\<and>(\<forall> i j. (Q i j \<longrightarrow> R i j)) 
        \<Longrightarrow> (\<forall> i j. (P i j \<longrightarrow> R i j))"
  by auto

lemma "((x::nat) div y) div z = (x div (y*z))"
  using div_mult2_eq by auto

lemma "(\<not>((a::nat) < b)) \<Longrightarrow> (a \<ge> b)"
   by auto

lemma not_null: "xs \<noteq> [] \<Longrightarrow> \<exists>y ys. xs = y#ys"
   by (metis neq_Nil_conv)

lemma "(y::nat) \<noteq> 0 \<Longrightarrow> (x mod y) < y"
   using mod_less_divisor by auto


lemma mod_prop1:"((a::nat) mod (b*c)) mod c = (a mod c)"
 proof(cases "c = 0")
 case True
  have "b*c = 0"
       by (metis True mult_0_right)
  then have "(a::nat) mod (b*c) = a"
         by auto
  then have "((a::nat) mod (b*c)) mod c = a mod c"
         by auto
  then show ?thesis by auto
 next
 case False
  let ?x = "(a::nat) mod (b*c)"
  let ?z = "?x mod c"
  have "\<exists>m. a = m*(b*c) + ?x"
         by (metis div_mult_mod_eq)  
  then obtain m1 where "a = m1*(b*c) + ?x"
         by auto
  then have "?x = (a - m1*(b*c))"
         by auto
  then have "\<exists>m.( ?x = m*c + ?z)"
         using mod_div_decomp by blast
  then obtain m where "( ?x = m*c + ?z)"
         by auto
  then have "(a - m1*(b*c)) = m*c + ?z"
        using  \<open>a mod (b * c) = a - m1 * (b * c)\<close>   by (metis)
  then have "a = m1*b*c + m*c + ?z"
        using \<open>a = m1 * (b * c) + a mod (b * c)\<close> \<open>a mod (b * c) 
        = m * c + a mod (b * c) mod c\<close>
        by (metis  ab_semigroup_add_class.add_ac(1) 
        ab_semigroup_mult_class.mult_ac(1))
  then have 1:"a = (m1*b + m)*c + ?z"
        by (metis add_mult_distrib2 mult.commute) 
  let ?y = "(a mod c)"
  have "\<exists>n. a = n*(c) + ?y"
        by (metis "1" \<open>a mod (b * c) = m * c + a mod (b * c) mod c\<close> mod_mult_self3)  
  then obtain n where "a = n*(c) + ?y"
        by auto
  with 1 have "(m1*b + m)*c + ?z = n*c + ?y"
        by auto
  then have "(m1*b + m)*c - (n*c) = ?y - ?z"
        by auto
  then have "(m1*b + m - n)*c = (?y - ?z)"
        by (metis diff_mult_distrib2 mult.commute)     
  then have "c dvd (?y - ?z)"
        by (metis dvd_triv_right)
  moreover have "?y < c"
        using mod_less_divisor False by auto  
  moreover have "?z < c"
        using mod_less_divisor False by auto  
  moreover have "?y - ?z < c"
        using calculation(2) less_imp_diff_less by blast
  ultimately have "?y - ?z = 0"
        by (metis dvd_imp_mod_0 mod_less)
  then show ?thesis using False 
        by (metis "1" mod_add_right_eq mod_mult_self2 add.commute mult.commute)
qed

lemma mod_div_relation:"((a::nat) mod (b*c)) div c = (a div c) mod b"
proof(cases "b*c = 0")
 case True
  have T_1:"(b = 0)\<or>(c = 0)"
       using True by auto
  show ?thesis
  proof(cases "(b = 0)")
   case True
    have "a mod (b*c) = a"
        using True by auto
    then show ?thesis using True by auto
   next
   case False
    have "c = 0"
        using T_1 False by auto
    then show ?thesis by auto
  qed
  next
  case False
   have F_1:"(b > 0)\<and> (c > 0)"
       using False by auto
   have "\<exists>x. a = x*(b*c) + (a mod (b*c))"
       using mod_div_decomp by blast
   then obtain x where "a = x*(b*c) + (a mod (b*c))"
       by auto
   then have "a div c = ((x*(b*c)) div c) + ((a mod (b*c)) div c)"
       using  div_add1_eq mod_add_self1 mod_add_self2 
       mod_by_0 mod_div_trivial mod_prop1 mod_self
       by (metis)
   then have "a div c = (((x*b)*c) div c) + ((a mod (b*c)) div c)"
       by auto
   then have F_2:"a div c = (x*b) + ((a mod (b*c)) div c)"    
       by (metis F_1 nonzero_mult_div_cancel_left mult.commute neq0_conv)
   have "\<exists>y. a div c = (y*b) + ((a div c) mod b)"
       by (metis add.commute mod_div_mult_eq)
   then obtain y where "a div c = (y*b) + ((a div c) mod b)"
       by auto
   with F_2 have F_3:" (x*b) + ((a mod (b*c)) div c) = (y*b) + ((a div c) mod b)"
       by auto
   then have "(x*b) - (y * b) = ((a div c) mod b) - ((a mod (b*c)) div c) "
      by auto
   then have "(x - y) * b = ((a div c) mod b) - ((a mod (b*c)) div c)"
      by (metis diff_mult_distrib2 mult.commute)
   then have F_4:"b dvd (((a div c) mod b) - ((a mod (b*c)) div c))"
      by (metis dvd_eq_mod_eq_0 mod_mult_self1_is_0 mult.commute)
   have F_5:"b >  ((a div c) mod b)"
      by (metis F_1 mod_less_divisor)
   have "b*c > (a mod (b*c))"
      by (metis False mod_less_divisor neq0_conv)
   moreover then have "(b*c) div c > (a mod (b*c)) div c"
      by (metis F_1 div_left_ineq nonzero_mult_div_cancel_right neq0_conv)
   then have "b > (a mod (b*c)) div c"
      by (metis calculation div_right_ineq mult.commute)
   with F_4 F_5 
    have F_6:"((a div c) mod b)-((a mod (b*c)) div c) = 0"
      using less_imp_diff_less nat_dvd_not_less by blast
   from F_3 have "(y * b) - (x*b) 
                      = ((a mod (b*c)) div c) - ((a div c) mod b) "
     by auto
   then have "(y - x) * b = ((a mod (b*c)) div c) - ((a div c) mod b)"
     by (metis diff_mult_distrib2 mult.commute)
   then have F_7:"b dvd (((a mod (b*c)) div c) - ((a div c) mod b))"
     by (metis dvd_eq_mod_eq_0 mod_mult_self1_is_0  mult.commute)
   have F_8:"b >  ((a div c) mod b)"
     by (metis F_1 mod_less_divisor)
   have "b*c > (a mod (b*c))"
     by (metis False mod_less_divisor neq0_conv)
   moreover then have "(b*c) div c > (a mod (b*c)) div c"
     by (metis F_1 div_left_ineq  nonzero_mult_div_cancel_right neq0_conv)
   then have "b > (a mod (b*c)) div c"
     by (metis calculation div_right_ineq  mult.commute)
   with F_7 F_8 
    have "((a mod (b*c)) div c) - ((a div c) mod b) = 0"
      by (metis F_2 cancel_comm_monoid_add_class.diff_cancel mod_if mod_mult_self3)
   with F_6 have "((a mod (b*c)) div c) = ((a div c) mod b)"
     by auto         
   then show ?thesis using False by auto 
qed

text\<open>The following lemma proves that the tensor product of matrices
is associative\<close>

lemma associativity:
 fixes M1 M2 M3
 shows
      " (mat (row_length M1) (length M1) M1) 
      \<and> (mat (row_length M2) (length M2) M2)
      \<and> (mat (row_length M3) (length M3) M3)
        \<Longrightarrow>
           M1 \<otimes> (M2 \<otimes> M3) = (M1 \<otimes> M2) \<otimes> M3" (is "?x \<Longrightarrow>?l = ?r")
proof-
 fix j
 assume 0:"  (mat (row_length M1) (length M1) M1) 
           \<and> (mat (row_length M2) (length M2) M2)
           \<and> (mat (row_length M3) (length M3) M3)" 
 have 1:"length ((M1 \<otimes> M2) \<otimes> M3) 
                    = (length M1)*(length M2)* (length M3)"
 proof- 
   have "length (M2 \<otimes> M3) = (length M2)* (length M3)"
        by (metis length_Tensor)
   then have "length (M1 \<otimes> (M2 \<otimes> M3)) 
                  = (length M1)*(length M2)* (length M3)"
        using mult.assoc length_Tensor by auto 
   moreover have " length (M1 \<otimes> M2) = (length M1)* (length M2)"
        by (metis length_Tensor)
   ultimately  show ?thesis using mult.assoc length_Tensor by auto
  qed
  have 2:"row_length ((M1 \<otimes> M2) \<otimes> M3) 
                    = (row_length M1)*(row_length M2)* (row_length M3)"
  proof-
   have "row_length (M2 \<otimes> M3) = (row_length M2)* (row_length M3)"
              using row_length_mat assoc by auto
   then have "row_length (M1 \<otimes> (M2 \<otimes> M3)) 
                   = (row_length M1)*(row_length M2)* (row_length M3)"
              using row_length_mat assoc by auto
   moreover have " row_length (M1 \<otimes> M2) 
                                   = (row_length M1)* (row_length M2)"
               using row_length_mat  by auto
   ultimately show ?thesis  using row_length_mat assoc by auto
  qed
  have 3:
      "\<forall>i.\<forall>j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
                \<longrightarrow> 
            (((M1 \<otimes> M2) \<otimes> M3)!j!i) 
                = f 
                   ((M1 \<otimes> M2)!(j div (length M3))!(i div (row_length M3))) 
                   (M3!(j mod length M3)!(i mod (row_length M3))))"
       using 0 matrix_Tensor_elements 1 2 effective_well_defined_Tensor 
             length_Tensor row_length_mat
       by auto
  moreover have 
       "\<forall>j.(j < (length M1)*(length M2)*(length M3))  
                          \<longrightarrow> (j div (length M3)) < (length M1)*(length M2)"
       apply(rule allI)
       apply(simp add:div_left_ineq)
       done
  moreover have "\<forall>i.(i < (row_length M1)*(row_length M2)*(row_length M3)) 
                       \<longrightarrow> (i div (row_length M3)) 
                                         < (row_length M1)*(row_length M2)"
       apply(rule allI)
       apply(simp add:div_left_ineq)
       done
 ultimately have 4:"\<forall>i.\<forall>j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
          \<longrightarrow> 
                ((i div (row_length M3)) < (row_length M1)*(row_length M2))
                \<and> ((j div (length M3)) < (length M1)*(length M2)))"
       using allI 0  by auto
 have " (mat (row_length M1) (length M1) M1) 
           \<and> (mat (row_length M2) (length M2) M2)"
       using 0 by auto
 then have "\<forall>i.\<forall>j.(((i div (row_length M3)) < (row_length M1)*(row_length M2))
         \<and> ((j div (length M3)) < (length M1)*(length M2))
          \<longrightarrow>
       (((M1 \<otimes> M2))!(j div (length M3))!(i div row_length M3)) 
                = f 
          ((M1)!((j div (length M3)) div (length M2))
               !((i div (row_length M3)) div (row_length M2))) 
          (M2!((j div (length M3)) mod (length M2))
             !((i div (row_length M3)) mod (row_length M2))))"
       using  effective_matrix_tensor_elements by auto            
 with 4 have 5:"\<forall>i j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
          \<longrightarrow>  (((M1 \<otimes> M2))!(j div (length M3))!(i div row_length M3)) 
                = f 
       ((M1)!((j div (length M3)) div (length M2))
            !((i div (row_length M3)) div (row_length M2))) 
        (M2!((j div (length M3)) mod (length M2))
            !((i div (row_length M3)) mod (row_length M2))))"
       by auto
 with 3 have 6:
      "\<forall>i.\<forall>j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
                \<longrightarrow> 
            (((M1 \<otimes> M2) \<otimes> M3)!j!i) 
                = f 
                   (f 
                     ((M1)!((j div (length M3)) div (length M2))
                             !((i div (row_length M3)) div (row_length M2))) 
                     (M2!((j div (length M3)) mod (length M2))
                           !((i div (row_length M3)) mod (row_length M2)))) 
                   (M3!(j mod length M3)!(i mod (row_length M3))))"
       by auto 
 have "(j div (length M3))div (length M2) = (j div ((length M3)*(length M2)))"
       using div_mult2_eq by auto  
 moreover have "((i div (row_length M3)) div (row_length M2)) = (i div ((row_length M3)*(row_length M2)))"
       using div_mult2_eq by auto
 ultimately have step1:"\<forall>i.\<forall>j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
                \<longrightarrow> 
            (((M1 \<otimes> M2) \<otimes> M3)!j!i) 
                = f 
                   (f 
       ((M1)!(j div ((length M3)*(length M2)))! (i div ((row_length M3)*(row_length M2)))) 
          (M2!((j div (length M3)) mod (length M2))!((i div (row_length M3)) mod (row_length M2)))) 
                   (M3!(j mod length M3)!(i mod (row_length M3))))"
       using 6  by (metis "3" "5" div_mult2_eq)
 then have step1:"\<forall>i j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
                \<longrightarrow> 
            (((M1 \<otimes> M2) \<otimes> M3)!j!i) 
                = f 
                   (f 
       ((M1)!(j div ((length M2)*(length M3)))! (i div ((row_length M2)*(row_length M3)))) 
          (M2!((j div (length M3)) mod (length M2))!((i div (row_length M3)) mod (row_length M2)))) 
                   (M3!(j mod length M3)!(i mod (row_length M3))))"
       by (metis mult.commute)
 have 7:
      "\<forall>i.\<forall>j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
                \<longrightarrow> 
            ((M1 \<otimes> (M2 \<otimes> M3))!j!i) 
                = f 
                   ((M1)!(j div (length (M2 \<otimes>  M3)))!(i div (row_length (M2 \<otimes> M3)))) 
                   ((M2 \<otimes> M3)!(j mod length (M2 \<otimes>M3))!(i mod (row_length (M2 \<otimes> M3)))))"
       using 0 matrix_Tensor_elements 1 2 effective_well_defined_Tensor 
             length_Tensor row_length_mat
       by auto
 then have 
      "\<forall>i.\<forall>j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
                \<longrightarrow> 
            ((M1 \<otimes> (M2 \<otimes> M3))!j!i) 
                = f 
                   ((M1)!(j div ((length M2)*(length M3)))!(i div ((row_length M2)*(row_length M3)))) 
                   ((M2 \<otimes> M3)!(j mod length (M2 \<otimes>M3))!(i mod (row_length (M2 \<otimes> M3)))))"
       using length_Tensor row_length_mat by auto
 then have 
      "\<forall>i.\<forall>j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
                \<longrightarrow> 
            ((M1 \<otimes> (M2 \<otimes> M3))!j!i) 
                = f 
                   ((M1)!(j div ((length M3)*(length M2)))
                        !(i div ((row_length M3)*(row_length M2)))) 
                   ((M2 \<otimes> M3)!(j mod length (M2 \<otimes>M3))
                             !(i mod (row_length (M2 \<otimes> M3)))))"
       using mult.commute by (metis)
 have 8:
       "\<forall>j.((j < (length M1)*(length M2)*(length M3)))
                \<longrightarrow> (j mod (length (M2 \<otimes> M3))) < (length (M2 \<otimes> M3))"
 proof(cases "length (M2 \<otimes> M3) = 0")
  case True
   have "(length M2)*(length M3) = 0"
            using length_Tensor True by auto
   then have "(length M1)*(length M2)*(length M3) = 0"
            by auto
   then show ?thesis  by (metis  less_nat_zero_code)
  next
  case False
   have "length (M2 \<otimes> M3)  > 0"
           using False by auto
   then show ?thesis using mod_less_divisor by auto
 qed
 then have 9:
        "\<forall>i.((i < (row_length M1)*(row_length M2)*(row_length M3)))
                \<longrightarrow> (i mod (row_length (M2 \<otimes> M3))) < (row_length (M2 \<otimes> M3))"
 proof(cases "row_length (M2 \<otimes> M3) = 0")
  case True
   have "(row_length M2)*(row_length M3) = 0"
           using  True by (metis row_length_mat)
   then have "(row_length M1)*(row_length M2)*(row_length M3) = 0"
           by auto
   then show ?thesis by (metis less_nat_zero_code)
  next
  case False
   have "row_length (M2 \<otimes> M3)  > 0"
           using False by auto
   then show ?thesis using mod_less_divisor by auto
 qed
 with 8 have 10:"\<forall>i.\<forall>j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
             \<longrightarrow> 
                (i mod (row_length (M2 \<otimes> M3))) < (row_length (M2 \<otimes> M3))
              \<and> (j mod (length (M2 \<otimes> M3))) < (length (M2 \<otimes> M3)))"
           by auto
 then have 11:"\<forall> i j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
             \<longrightarrow> 
                (i mod (row_length (M2 \<otimes> M3))) 
                              < (row_length M2)*(row_length M3)
                \<and>(j mod (length (M2 \<otimes> M3))) < (length M2)*(length  M3))"
           using length_Tensor row_length_mat by auto
 have "(mat (row_length M2) (length M2) M2) 
           \<and> (mat (row_length M3) (length M3) M3)"
           using 0 by auto
 then have "\<forall> i j.(((i mod (row_length (M2 \<otimes> M3))) 
                                 < (row_length M2)*(row_length M3))
                  \<and>((j mod (length (M2\<otimes>M3))) < (length M2)*(length M3))
       \<longrightarrow>
       (((M2 \<otimes> M3))!(j mod (length (M2 \<otimes> M3)))!(i mod row_length (M2 \<otimes> M3))) 
                = f 
                  ((M2)!((j mod (length (M2 \<otimes> M3))) div (length M3))
                        !((i mod (row_length (M2 \<otimes> M3))) div (row_length M3))) 
                  (M3!((j mod (length (M2 \<otimes> M3))) mod (length M3))
                     !((i mod (row_length (M2 \<otimes> M3))) mod (row_length M3))))"
           using matrix_Tensor_elements by auto 
 then have "\<forall> i j.
         ((i < (row_length M1)*(row_length M2)*(row_length M3))
       \<and>(j < (length M1)*(length M2)*(length M3) )
             \<longrightarrow> 
           (((M2 \<otimes> M3))!(j mod (length (M2 \<otimes> M3)))
                       !(i mod row_length (M2 \<otimes> M3))) 
                = 
       f 
       ((M2)!((j mod (length (M2 \<otimes> M3))) div (length M3))
            !((i mod (row_length (M2 \<otimes> M3))) div (row_length M3))) 
        (M3!((j mod (length (M2 \<otimes> M3))) mod (length M3))
           !((i mod (row_length (M2 \<otimes> M3))) mod (row_length M3))))"   
           using 11 by auto 
 moreover then have "\<forall>j.(j mod (length (M2 \<otimes> M3))) mod (length M3)
                         = j mod (length M3)"
 proof                  
  have "\<forall>j.((j mod (length (M2 \<otimes> M3))) 
                         = (j mod ((length M2) *(length M3))))"
            using length_Tensor by auto
  moreover have 
         "\<forall>j.((j mod ((length M2) *(length M3))) mod (length M3)
                                 = (j mod (length M3)))"   
            using mod_prop1 by auto 
  ultimately show ?thesis by auto
 qed
 moreover then have "\<forall>i.(i mod (row_length (M2 \<otimes> M3))) mod (row_length M3)
                         = i mod (row_length M3)"
 proof                  
  have "\<forall>i.((i mod (row_length (M2 \<otimes> M3))) 
                         = (i mod ((row_length M2) *(row_length M3))))"
            using row_length_mat by auto
  moreover have "\<forall>i.((i mod ((row_length M2)*(row_length M3))) 
                                       mod (row_length M3)
                                 = (i mod (row_length M3)))"   
            using mod_prop1 by auto 
  ultimately show ?thesis by auto
 qed
 ultimately have 12:"\<forall> i j.((i < (row_length M1)
                            *(row_length M2)
                            *(row_length M3))
                            \<and>(j < (length M1)*(length M2)*(length M3) )
                       \<longrightarrow> 
                          (((M2 \<otimes> M3))!(j mod (length (M2 \<otimes> M3)))
                                       !(i mod row_length (M2 \<otimes> M3))) 
                = f 
                   ((M2)!((j mod (length (M2 \<otimes> M3))) div (length M3))
                        !((i mod (row_length (M2 \<otimes> M3))) div (row_length M3))) 
                   (M3!(j mod  (length M3))!(i mod (row_length M3))))"   
            by auto 
 moreover have "\<forall>j.(j mod (length (M2 \<otimes> M3))) div (length M3)
                    = (j div (length M3)) mod (length M2)"
 proof-
  have "\<forall>j.((j mod (length (M2 \<otimes> M3))) 
                    = (j mod ((length M2)*(length M3))))"
            using length_Tensor by auto
  then show ?thesis using mod_div_relation by auto
 qed
 moreover have "\<forall>i.(i mod (row_length (M2 \<otimes> M3))) div (row_length M3)
                    = (i div (row_length M3)) mod (row_length M2)"
 proof-
  have "\<forall>i.((i mod (row_length (M2 \<otimes> M3))) 
                    = (i mod ((row_length M2)*(row_length M3))))"
            using row_length_mat by auto
  then show ?thesis using mod_div_relation by auto
 qed
 ultimately have "\<forall> i j.
                      ((i < (row_length M1)*(row_length M2)*(row_length M3))
                      \<and>(j < (length M1)*(length M2)*(length M3) )
             \<longrightarrow> 
                 (((M2 \<otimes> M3))!(j mod (length (M2 \<otimes> M3)))
                             !(i mod row_length (M2 \<otimes> M3))) 
                       = f 
                          ((M2)!((j div (length M3)) mod (length M2))
                               !((i div (row_length M3)) mod (row_length M2)))
                           (M3!(j mod  (length M3))!(i mod (row_length M3))))"   
            by auto 
 with 7 have 13:"\<forall>i j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
                \<longrightarrow> 
            ((M1 \<otimes> (M2 \<otimes> M3))!j!i) 
                = f 
                   ((M1)!(j div ((length M2)*(length  M3)))
                        !(i div ((row_length M2)*(row_length M3)))) 
                  (f 
       ((M2)!((j div (length M3)) mod (length M2))!((i div (row_length M3)) mod (row_length M2)))
       (M3!(j mod  (length M3))
           !(i mod (row_length M3)))))"  
                    using length_Tensor row_length_mat  by auto
 moreover have "\<forall> i j.( f 
                    ((M1)!(j div ((length M2)*(length  M3)))
                        !(i div ((row_length M2)*(row_length M3)))) 
                  (f 
                   ((M2)!((j div (length M3)) mod (length M2))!((i div (row_length M3)) mod (row_length M2)))
       (M3!(j mod  (length M3))
           !(i mod (row_length M3)))))
           = f (f 
                    ((M1)!(j div ((length M2)*(length  M3)))
                        !(i div ((row_length M2)*(row_length M3))))                  
                    ((M2)!((j div (length M3)) mod (length M2))
                         !((i div (row_length M3)) mod (row_length M2))))
                (M3!(j mod  (length M3))
                   !(i mod (row_length M3)))"
            using assoc by auto
 with 13 have "\<forall>i j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
                \<longrightarrow> 
            ((M1 \<otimes> (M2 \<otimes> M3))!j!i) 
                = f (f 
                    ((M1)!(j div ((length M2)*(length  M3)))
                        !(i div ((row_length M2)*(row_length M3))))                  
                    ((M2)!((j div (length M3)) mod (length M2))
                         !((i div (row_length M3)) mod (row_length M2))))
                (M3!(j mod  (length M3))
                   !(i mod (row_length M3))))"
            by auto
 with step1 have step2: 
       "\<forall>i j.(((i<((row_length M1)*(row_length M2)*(row_length M3)))
       \<and>(j < (length M1)*(length M2)*(length M3)))
                \<longrightarrow> 
            ((M1 \<otimes> (M2 \<otimes> M3))!j!i) = (((M1 \<otimes> M2) \<otimes> M3)!j!i))"
            by auto
 moreover have "mat ((row_length M1)*(row_length M2)*(row_length M3))
           ((length M1)*(length M2)*(length M3))
               (M1 \<otimes> (M2 \<otimes> M3))"
 proof-
  have "mat ((row_length M2)*(row_length M3)) ((length M2)*(length M3)) (M2 \<otimes> M3)"
            using 0 effective_well_defined_Tensor  row_length_mat length_Tensor 
            by auto
  moreover have  "mat ((row_length M1)*((row_length (M2 \<otimes> M3))))
           ((length M1)*((length (M2 \<otimes> M3))))
               (M1 \<otimes> (M2 \<otimes> M3))"
            using  0 effective_well_defined_Tensor row_length_mat length_Tensor 
            by metis
  ultimately show ?thesis using row_length_mat length_Tensor mult.assoc 
            by (simp add: length_Tensor row_length_mat  semigroup_mult_class.mult.assoc)
 qed
 moreover have "mat ((row_length M1)*(row_length M2)*(row_length M3))
           ((length M1)*(length M2)*(length M3))
               ((M1 \<otimes> M2) \<otimes> M3)"
 proof-
  have "mat ((row_length M1)*(row_length M2)) ((length M1)*(length M2)) (M1 \<otimes> M2)"
            using 0 effective_well_defined_Tensor row_length_mat length_Tensor by auto
  moreover have  "mat ((row_length (M1 \<otimes> M2))*(row_length M3))
           ((length (M1 \<otimes> M2))*(length M3))
               ((M1 \<otimes> M2 )\<otimes> M3)"
            using  0 effective_well_defined_Tensor  row_length_mat length_Tensor by metis 
  ultimately show ?thesis using row_length_mat length_Tensor by (metis mult.assoc)
 qed
 ultimately show ?thesis using mat_eqI by blast
qed     
  
end

lemma " \<And>(a::nat) b.(times  a  b) =(times  b  a)"
 by auto

subsection\<open>Associativity and Distributive properties\<close>

locale plus_mult = 
 mult + 
 fixes zer::"'a"
 fixes g::" 'a \<Rightarrow> 'a \<Rightarrow> 'a " (infixl "+" 60)
 fixes inver::"'a \<Rightarrow>  'a"
 assumes plus_comm:" g a  b = g b a "
 assumes plus_assoc:" (g (g a b) c) = (g a (g b c))"
 assumes plus_left_id:" g zer x = x"
 assumes plus_right_id:"g x zer = x"
 assumes plus_left_distributivity: "f a (g b c) = g (f a b) (f a c)"
 assumes plus_right_distributivity: "f (g a b) c = g (f a c) (f b c)"
  assumes plus_left_inverse: "(g x (inver x)) = zer"
 assumes plus_right_inverse: "(g (inver x) x) = zer"
 

context plus_mult
begin

lemma fixes M1 M2 M3
      shows "(mat (row_length M1) (length M1) M1) 
            \<and>(mat (row_length M2) (length M2) M2)
            \<and>(mat (row_length M3) (length M3) M3)
             \<Longrightarrow> (M1 \<otimes> (M2 \<otimes> M3)) = ((M1 \<otimes> M2) \<otimes> M3)"
        using associativity by auto


text\<open>matrix$\_$mult refers to multiplication of matrices in the locale 
plus\_mult\<close>

abbreviation matrix_mult::"'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" (infixl "\<circ>" 65)
 where
"matrix_mult M1 M2 \<equiv> (mat_multI zer g f (row_length M1) M1 M2)"

definition scalar_product :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a" where
 "scalar_product v w = scalar_prodI zer g f v w"

lemma ma :
 assumes wf1: "mat nr n m1"
     and wf2: "mat n nc m2"
        and i: "i < nr"
        and j: "j < nc"
 shows "mat_multI zer g f nr m1 m2 ! j ! i 
                  = scalar_prodI zer g f (row m1 i) (col m2 j)"
 using mat_mult_index i j wf1 wf2 by metis

lemma matrix_index:
  assumes wf1: "mat (row_length m1) n m1"
      and wf2: "mat n nc m2"
        and i: "i < (row_length m1)"
        and j: "j < nc"
 shows  "matrix_mult  m1 m2 ! j ! i 
                 = scalar_product  (row m1 i) (col m2 j)"
 using wf1 wf2 i j ma scalar_product_def by auto


lemma unique_row_col:
 assumes "mat nr1 nc1 M" and "mat nr2 nc2 M" and "M \<noteq> []"
 shows "nr1 = nr2" and "nc1 = nc2"
proof(cases M)
 case Nil
  show "nr1 = nr2" using assms(3) Nil by auto
 next
 case (Cons v M)
  have 1:"v \<in> set (v#M)"
        using Cons by auto
  then have "length v = nr1"
        using assms(1) mat_def Ball_def vec_def  Cons by metis 
  moreover then have "length v = nr2"
        using 1 assms(2) mat_def Ball_def vec_def  Cons by metis
  ultimately show "nr1 = nr2"
        by auto
 next
  have "length M = nc1"
        using mat_def assms(1) by auto
  moreover have "length M = nc2"
        using mat_def assms(2) by auto
  ultimately show "nc1 = nc2"
        by auto
qed

lemma matrix_mult_index: 
 assumes "m1 \<noteq> []"
  and  wf1: "mat nr n m1"
  and wf2: "mat n nc m2"
    and i: "i < nr"
    and j: "j < nc"
 shows  "matrix_mult  m1 m2 ! j ! i = scalar_product  (row m1 i) (col m2 j)"
 using matrix_index unique_row_col assms by (metis matrix_row_length)

text\<open>the following definition checks if the given four matrices
 are such that the compositions in the mixed-product property which
 will be proved, hold true. It further checks that the matrices are 
 non empty and valid\<close>

definition matrix_match::"'a mat \<Rightarrow> 'a mat \<Rightarrow>'a mat \<Rightarrow> 'a mat  \<Rightarrow> bool"
where 
"matrix_match A1 A2 B1 B2 \<equiv> 
    (mat (row_length A1) (length A1) A1)
   \<and>(mat (row_length A2) (length A2) A2)
   \<and>(mat (row_length B1) (length B1) B1)
   \<and>(mat (row_length B2) (length B2) B2)
   \<and> (length A1 = row_length A2)
   \<and> (length B1 = row_length B2)
   \<and>(A1 \<noteq> [])\<and>(A2 \<noteq> [])\<and>(B1 \<noteq> [])\<and>(B2 \<noteq> [])"


lemma non_empty_mat_mult:
 assumes wf1:"mat nr n A"
     and wf2:"mat n nc B"
         and "A \<noteq> []" and " B \<noteq> []"
 shows  "A \<circ> B \<noteq> []"
proof-
 have "mat nr nc (A \<circ> B)"
         using assms(1) assms(2) mat_mult  assms(3) matrix_row_length unique_row_col(1) by (metis)
 then have "length (A \<circ> B) = nc"
         using mat_def by auto
 moreover have "nc > 0"
 proof-
  have "length B = nc"
                    using assms(2) mat_def by auto
  then show ?thesis using assms(4) by auto
 qed
 moreover then have "length (A \<circ> B) > 0"
          by (metis calculation(1))  
 then show ?thesis by auto
qed

lemma tensor_compose_distribution1:
assumes wf1:"mat (row_length A1) (length A1) A1"
    and wf2:"mat (row_length A2) (length A2) A2"
    and wf3:"mat (row_length B1) (length B1) B1"
    and wf4:"mat (row_length B2) (length B2) B2"
    and matchAA:"length A1 = row_length A2" 
    and matchBB:"length B1 = row_length B2"
    and non_Nil:"(A1 \<noteq> [])\<and>(A2 \<noteq> [])\<and>(B1 \<noteq> [])\<and>(B2 \<noteq> [])" 
 shows "mat ((row_length A1)*(row_length B1)) 
            ((length A2)*(length B2)) 
                    ((A1\<circ>A2)\<otimes>(B1\<circ>B2))"
proof-
 have 0:"mat (row_length A1) (length A2) (matrix_mult A1 A2)"
          using wf1 wf2  mat_mult matchAA  by auto
 then have 1:"mat (row_length (A1 \<circ> A2)) (length (A1 \<circ> A2)) (matrix_mult A1 A2)"
          by (metis matrix_row_length)
 then have 2: "(row_length (A1 \<circ> A2)) = (row_length A1)" and "length (A1 \<circ> A2) = length A2"
          using non_empty_mat_mult unique_row_col 0  
          apply (metis length_0_conv mat_empty_column_length non_Nil)
          by (metis "0" "1" mat_empty_column_length unique_row_col(2))
 moreover have 3:"mat (row_length B1) (length B2) (matrix_mult B1 B2)"
          using wf3 wf4 matchBB mat_mult by auto 
 then have 4:"mat (row_length (B1 \<circ> B2)) (length (B1 \<circ> B2)) (matrix_mult B1 B2)"
          by (metis matrix_row_length) 
 then have 5: "(row_length (B1 \<circ> B2)) = (row_length B1)" and "length (B1 \<circ> B2) = length B2"
          using non_empty_mat_mult unique_row_col 3
          apply (metis length_0_conv mat_empty_column_length non_Nil) 
          by (metis "3" "4" mat_empty_column_length unique_row_col(2))
 then show ?thesis  using 1 4 5 well_defined_Tensor 
          by (metis "2" calculation(2))
qed     

lemma effective_tensor_compose_distribution1:
 "matrix_match A1 A2 B1 B2 \<Longrightarrow> mat ((row_length A1)*(row_length B1)) 
            ((length A2)*(length B2)) 
                    ((A1\<circ>A2)\<otimes>(B1\<circ>B2))"
  using tensor_compose_distribution1 unfolding matrix_match_def by auto


lemma tensor_compose_distribution2:
 assumes wf1:"mat (row_length A1) (length A1) A1"
    and wf2:"mat (row_length A2) (length A2) A2"
    and wf3:"mat (row_length B1) (length B1) B1"
    and wf4:"mat (row_length B2) (length B2) B2"
    and matchAA:"length A1 = row_length A2"
    and matchBB:"length B1 = row_length B2"
    and non_Nil:"(A1 \<noteq> [])\<and>(A2 \<noteq> [])\<and>(B1 \<noteq> [])\<and>(B2 \<noteq> [])" 
 shows "mat ((row_length A1)*(row_length B1)) 
            ((length A2)*(length B2)) 
                    ((A1 \<otimes> B1) \<circ>(A2 \<otimes>B2))"
proof-
 have "mat 
           ((row_length A1)*(row_length B1))  
           ((length A1)*(length B1)) 
             (A1 \<otimes> B1)"
          using wf1 wf3 well_defined_Tensor by auto
 moreover have "mat 
                   ((row_length A2)*(row_length B2))  
                   ((length A2)*(length B2)) 
                      (A2\<otimes> B2)"
          using wf2 wf4 well_defined_Tensor by auto
 moreover have "((length A1)*(length B1)) 
                        = ((row_length A2)*(row_length B2))"
          using matchAA matchBB by auto
 ultimately show ?thesis using mat_mult row_length_mat by simp
qed    

theorem tensor_non_empty: assumes "A \<noteq> []" and "B \<noteq> []"
 shows "A \<otimes> B \<noteq> []"
 using  assms(1) assms(2) length_0_conv length_Tensor mult_is_0 by metis

theorem non_empty_distribution:
 assumes "mat nr1 n1 A1" 
     and "mat n1 nc1 A2" 
     and "mat nr2 n2 B1" 
     and "mat n2 nc2 B2" 
     and "A1 \<noteq> []" and "B1 \<noteq> []" and "A2 \<noteq> []" and "B2 \<noteq> []" 
 shows "((A1\<circ>A2)\<otimes>(B1\<circ>B2)) \<noteq> []"
proof-
 have "A1 \<circ> A2 \<noteq> []"
       using assms  non_empty_mat_mult by auto
 moreover have "B1 \<circ> B2 \<noteq> []"
       using assms  non_empty_mat_mult by auto
 ultimately show ?thesis using tensor_non_empty by auto 
qed

lemma effective_tensor_compose_distribution2:"matrix_match A1 A2 B1 B2 \<Longrightarrow> 
   mat ((row_length A1)*(row_length B1)) 
            ((length A2)*(length B2)) 
                    ((A1 \<otimes> B1) \<circ>(A2 \<otimes>B2))"
      using tensor_compose_distribution2 unfolding matrix_match_def by auto

theorem effective_matrix_Tensor_elements: 
 fixes M1 M2 i j 
 assumes "i<((row_length M1)*(row_length M2))"
     and "j < (length M1)*(length M2)"
     and "mat (row_length M1) (length M1) M1"
     and "mat (row_length M2) (length M2) M2"
 shows
 "((M1 \<otimes> M2)!j!i) = f (M1!(j div (length M2))!(i div (row_length M2))) 
(M2!(j mod length M2)!(i mod (row_length M2)))"
 using matrix_Tensor_elements assms by auto

theorem effective_matrix_Tensor_elements2: 
 fixes M1 M2 
 assumes "mat (row_length M1) (length M1) M1"
     and "mat (row_length M2) (length M2) M2"
 shows
  "(\<forall>i <((row_length M1)*(row_length M2)).
    \<forall>j < ((length M1)*(length M2))
       .((M1 \<otimes> M2)!j!i) = f (M1!(j div (length M2))!(i div (row_length M2))) 
                             (M2!(j mod length M2)!(i mod (row_length M2))))"
 using matrix_Tensor_elements assms by auto

definition matrix_compose_cond::"'a mat \<Rightarrow> 'a mat \<Rightarrow>'a mat \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where 
"matrix_compose_cond A1 A2 B1 B2 i j \<equiv> 
     (mat (row_length A1) (length A1) A1)
      \<and>(mat (row_length A2) (length A2) A2)
   \<and>(mat (row_length B1) (length B1) B1)
    \<and>(mat (row_length B2) (length B2) B2)

   \<and> (length A1 = row_length A2)
   \<and> (length B1 = row_length B2)
   \<and>(A1 \<noteq> [])\<and>(A2 \<noteq> [])\<and>(B1 \<noteq> [])\<and>(B2 \<noteq> []) 
\<and>(i<(row_length A1)*(row_length B1))\<and>(j< (length A2)*(length B2))"



theorem elements_matrix_distribution_1:
assumes wf1:"mat (row_length A1) (length A1) A1"
   and wf2:"mat (row_length A2) (length A2) A2"
   and wf3:"mat (row_length B1) (length B1) B1"
   and wf4:"mat (row_length B2) (length B2) B2"
   and matchAA:"length A1 = row_length A2"
   and matchBB:"length B1 = row_length B2"
   and non_Nil:"(A1 \<noteq> [])\<and>(A2 \<noteq> [])\<and>(B1 \<noteq> [])\<and>(B2 \<noteq> [])" 
   and "i<(row_length A1)*(row_length B1)" and "j< (length A2)*(length B2)"
shows
"((matrix_mult A1  A2)\<otimes>(matrix_mult B1  B2))!j!i
  =  f (scalar_product (row A1 (i div (row_length B1))) 
                        (col A2  (j div (length B2))))
       (scalar_product (row B1 (i mod (row_length B1))) 
                       (col B2 (j mod (length B2))))"
proof-
 have 0:"((matrix_mult A1  A2)\<otimes>(matrix_mult B1  B2)) \<noteq> []"
       using non_empty_distribution assms by auto
 then have 1:"mat ((row_length A1)*(row_length B1)) 
            ((length A2)*(length B2)) 
                    ((A1\<circ>A2)\<otimes>(B1\<circ>B2))"
       using tensor_compose_distribution1 assms by auto
 then have 2:"mat (row_length  ((A1\<circ>A2)\<otimes>(B1\<circ>B2))) 
            (length  ((A1\<circ>A2)\<otimes>(B1\<circ>B2))) 
                    ((A1\<circ>A2)\<otimes>(B1\<circ>B2))"
       by (metis matrix_row_length)
 then have 3:"((row_length A1)*(row_length B1)) 
                         = (row_length  ((A1\<circ>A2)\<otimes>(B1\<circ>B2))) "
        and "((length A2)*(length B2)) = (length  ((A1\<circ>A2)\<otimes>(B1\<circ>B2)))"
       using 0 1 unique_row_col 
       apply metis
       using 0 1 2 unique_row_col by metis  
 then have i:"(i < ((row_length A1)*(row_length B1))) 
                             = (i < (row_length  ((A1\<circ>A2)\<otimes>(B1\<circ>B2))))"
       by auto
 moreover have j:"(j < ((length A2)*(length B2))) 
                         = (j < (length  ((A1\<circ>A2)\<otimes>(B1\<circ>B2))))"
       using 3 \<open>length A2 * length B2 = length (A1 \<circ> A2 \<otimes> B1 \<circ> B2)\<close> 
       by (metis)
 have 4:"mat (row_length A1) (length A2) (A1 \<circ> A2)"
       using assms mat_mult by auto
 then have 5:"mat (row_length (A1 \<circ> A2)) (length (A1 \<circ> A2)) (A1 \<circ> A2)"
       using  matrix_row_length  by (metis)
 with 4 have 6:"row_length A1 = row_length (A1 \<circ> A2)"
       by (metis "0" Tensor.simps(1) unique_row_col(1))
 with 4 5 have 7:"length A2 = length (A1 \<circ> A2)"  
       by (metis  mat_empty_column_length unique_row_col(2))           
 then have 8:"mat (row_length B1) (length B2) (B1 \<circ> B2)"
       using assms mat_mult by auto
 then have 9:"mat (row_length (B1 \<circ> B2)) (length (B1 \<circ> B2)) (B1 \<circ> B2)"
       using  matrix_row_length  by (metis)
 with 7 8 have 10:"row_length B1 = row_length (B1 \<circ> B2)"
       by (metis "3" "6" assms(8) less_nat_zero_code mult_cancel2 mult_is_0 mult.commute row_length_mat)
 with 7 8 9  have 11:"length B2 = length (B1 \<circ> B2)"  
       by (metis  mat_empty_column_length unique_row_col(2))                    
 from 6 10 have 12:
               "(i < ((row_length A1)*(row_length B1))) 
                         = (i < (row_length  (A1\<circ>A2))*(row_length (B1\<circ>B2)))"
       by auto   
 then have 13:" (i < (row_length  (A1\<circ>A2))*(row_length (B1\<circ>B2)))"
       using assms by auto
 from 7 11 have 14:   
            "(j < ((length A2)*(length B2))) 
                         = (j < (length  (A1\<circ>A2))*(length (B1\<circ>B2)))"
       by auto
 then have 15:"(j < (length  (A1\<circ>A2))*(length (B1\<circ>B2)))"
       using assms by auto
 then have step_1:"((A1\<circ>A2)\<otimes>(B1\<circ>B2))!j!i
            =  f ((A1\<circ>A2)!(j div (length (B1\<circ>B2)))
                         !(i div (row_length (B1\<circ>B2)))) 
                 ((B1\<circ>B2)!(j mod length (B1\<circ>B2))
                         !(i mod (row_length (B1\<circ>B2))))"
       using 5 9 13 15 effective_matrix_Tensor_elements by auto 
 then have "((A1\<circ>A2)\<otimes>(B1\<circ>B2))!j!i
            =  f ((A1\<circ>A2)!(j div (length B2))!(i div (row_length B1))) 
                 ((B1\<circ>B2)!(j mod length B2)!(i mod (row_length B1)))"
       using 10 11 by auto
 moreover have " ((A1\<circ>A2)!(j div (length B2))!(i div (row_length B1))) 
               = (scalar_product (row A1 (i div (row_length B1)) ) (col A2 (j div (length B2)) ))"
 proof-
  have "j div (length B2) < (length A2)"
        using div_left_ineq assms by auto
  moreover have "i div (row_length B1) < (row_length A1)"
        using assms div_left_ineq by auto   
  moreover have "mat (length A1) (length A2) A2"
                             using wf2 matchAA by auto   
  ultimately show ?thesis   using wf1  non_Nil matrix_mult_index  by blast
 qed
 moreover have " ((B1\<circ>B2)!(j mod (length B2))!(i mod (row_length B1))) 
               = (scalar_product 
                                 (row B1 (i mod (row_length B1)) ) 
                                 (col B2 (j mod (length B2))))"
 proof-
  have "j <(length A2)*(length B2)"
                    using assms by auto
  then have "j mod (length B2) < (length B2)"
                    by (metis calculation less_nat_zero_code mod_less_divisor mult_is_0 neq0_conv)
  moreover have "i mod (row_length B1) < (row_length B1)"
                    by (metis assms(8) less_nat_zero_code mod_less_divisor mult_is_0 neq0_conv)
  moreover have "mat (length B1) (length B2) B2"
                    using wf4 matchBB by auto
  ultimately show ?thesis  
                   using wf3 non_Nil matrix_mult_index by blast
 qed
 ultimately show ?thesis by auto
qed

lemma effective_elements_matrix_distribution1:
 "matrix_compose_cond A1 A2 B1 B2 i j \<Longrightarrow>
 ((matrix_mult A1  A2)\<otimes>(matrix_mult B1  B2))!j!i
  =  f (scalar_product (row A1 (i div (row_length B1))) (col A2  (j div (length B2))))
       (scalar_product (row B1 (i mod (row_length B1))) (col B2 (j mod (length B2))))"
      using  elements_matrix_distribution_1 matrix_compose_cond_def by auto      

lemma matrix_match_condn_1:
"matrix_match A1 A2 B1 B2 
      \<and>((i<(row_length A1)*(row_length B1))
      \<and>(j<(length A2)*(length B2)))
       \<Longrightarrow>  ((matrix_mult A1  A2)\<otimes>(matrix_mult B1  B2))!j!i
  =  f
       (scalar_product 
                 (row A1 (i div (row_length B1))) 
                 (col A2  (j div (length B2))))
       (scalar_product 
                 (row B1 (i mod (row_length B1))) 
                 (col B2 (j mod (length B2))))"
 using elements_matrix_distribution_1 unfolding matrix_match_def by auto

lemma effective_matrix_match_condn_1: 
 assumes "(matrix_match A1 A2 B1 B2) "
 shows "\<forall>i j.((i<(row_length A1)*(row_length B1))
             \<and>(j<(length A2)*(length B2))
              \<longrightarrow>   ((A1 \<circ>  A2)\<otimes>(B1 \<circ> B2))!j!i
                        =  f 
                            (scalar_product 
                                  (row A1 (i div (row_length B1))) 
                                  (col A2  (j div (length B2))))
                            (scalar_product 
                                  (row B1 (i mod (row_length B1))) 
                                  (col B2 (j mod (length B2)))))"
   using assms matrix_match_condn_1 unfolding matrix_match_def 
       by auto 

theorem elements_matrix_distribution2:
fixes A1 A2 B1 B2 i j
assumes wf1:"mat (row_length A1) (length A1) A1"
   and wf2:"mat (row_length A2) (length A2) A2"
   and wf3:"mat (row_length B1) (length B1) B1"
   and wf4:"mat (row_length B2) (length B2) B2"
   and matchAA:"length A1 = row_length A2"
   and matchBB:"length B1 = row_length B2"
   and non_Nil:"(A1 \<noteq> [])\<and>(A2 \<noteq> [])\<and>(B1 \<noteq> [])\<and>(B2 \<noteq> [])"    
         and i:"i<(row_length A1)*(row_length B1)" and j:"j< (length A2)*(length B2)" 
shows
"((A1 \<otimes> B1)\<circ>(A2 \<otimes> B2))!j!i
  =  scalar_product 
          (vec_vec_Tensor 
                    (row A1 (i div row_length B1)) 
                    (row B1 (i mod row_length B1))) 
          (vec_vec_Tensor 
                    (col A2 (j div length B2)) 
                    (col B2 (j mod length B2)))" 
proof-
 have 1:"mat 
              ((row_length A1)*(row_length B1)) 
              ((length A1)*(length B1)) 
                                   (A1 \<otimes> B1)"
              using wf1 wf3 well_defined_Tensor by auto
 moreover have 2:"mat 
                   ((row_length A2)*(row_length B2)) 
                   ((length A2)*(length B2)) 
                                   (A2 \<otimes> B2)"
              using wf2 wf4 well_defined_Tensor by auto
 moreover have 3:"((length A1)*(length B1)) 
                           = ((row_length A2)*(row_length B2))"
              using matchAA matchBB by auto
 ultimately have 4:"((A1\<otimes>B1)\<circ>(A2\<otimes>B2))!j!i 
                        = scalar_product (row (A1 \<otimes> B1) i) (col (A2 \<otimes> B2) j)"
              using i j matrix_mult_index non_Nil mat_mult_index 
                    row_length_mat scalar_product_def
              by auto
 moreover have "(row (A1 \<otimes> B1) i)
                  =  vec_vec_Tensor 
                           (row A1 (i div row_length B1)) 
                           (row B1 (i mod row_length B1))"
              using  wf1 wf3 i effective_row_formula by auto
 moreover have " col (A2 \<otimes> B2) j =  vec_vec_Tensor (col A2 (j div length B2)) (col B2 (j mod length B2))"
              using wf2 wf4 j col_formula by auto
 ultimately show ?thesis by auto
 qed

lemma matrix_match_condn_2:
"matrix_match A1 A2 B1 B2 
 \<and>((i<(row_length A1)*(row_length B1))
 \<and>(j<(length A2)*(length B2)))
  \<Longrightarrow> ((A1 \<otimes> B1)\<circ>(A2 \<otimes> B2))!j!i
          =  scalar_product 
                (vec_vec_Tensor 
                        (row A1 (i div row_length B1)) 
                        (row B1 (i mod row_length B1))) 
                (vec_vec_Tensor 
                        (col A2 (j div length B2)) 
                        (col B2 (j mod length B2)))" 
 using elements_matrix_distribution2 unfolding matrix_match_def by auto


lemma effective_matrix_match_condn_2: 
 assumes "(matrix_match A1 A2 B1 B2) "
 shows "\<forall>i j.((i<(row_length A1)*(row_length B1))
         \<and>(j<(length A2)*(length B2))
            \<longrightarrow> ((A1 \<otimes> B1)\<circ>(A2 \<otimes> B2))!j!i
           =  scalar_product 
                  (vec_vec_Tensor 
                           (row A1 (i div row_length B1)) 
                           (row B1 (i mod row_length B1))) 
                  (vec_vec_Tensor 
                           (col A2 (j div length B2)) 
                           (col B2 (j mod length B2))))" 
 using assms matrix_match_condn_2 unfolding matrix_match_def by auto


lemma zip_Nil:"zip [] [] = []"
 using zip_def by auto

lemma zer_left_mult:"f zer x = zer"
proof-
 have "g zer zer = zer"
      using plus_left_id by auto
 then have "f zer x = f (g zer zer) x"
      by auto
 then have "f zer x = (f zer x) + (f zer x)"
      using  plus_right_distributivity by auto
 then have "(f zer x) + (inver (f zer x)) = (f zer x) + (f zer x) + (inver (f zer x))"
      by auto
 then have "zer = (f zer x) + zer"
      using plus_left_inverse  plus_assoc by (metis)
 then show ?thesis
      using plus_right_id by simp
qed

lemma zip_Cons:"(length v = length w) \<Longrightarrow> zip (a#v) (b#w) = (a,b)#(zip v w)"
 unfolding zip_def by auto 

lemma scalar_product_times:
 "\<forall>w1 w2.(length w1 = length w2) \<and>(length w1 = n) \<longrightarrow> 
           (f (x*y) (scalar_product w1 w2)) 
                      = (scalar_product 
                               (times x w1) 
                               (times y w2))"
 apply(rule allI)
 apply (rule allI)
 proof(induct n)
  case 0
   have "(length w1 = length w2) \<and>(length w1 = 0)  \<Longrightarrow> ?case"
   proof-
    assume assms:"(length w1 = length w2) \<and>(length w1 = 0)"
    have 1:" w1 = []"
          using assms by auto
    moreover have 2:"(length w1 = length w2) \<and>(length w1 = 0) \<longrightarrow> w2 = []"
          by auto
    ultimately have "(length w1 = length w2) \<and>(length w1 = 0) 
                                   \<longrightarrow> scalar_product w1 w2 = zer"
          unfolding scalar_product_def scalar_prodI_def by auto
    then have 3:"(length w1 = length w2) \<and>(length w1 = 0) 
                                   \<longrightarrow> (f (x*y) (scalar_product w1 w2)) = zer"
          using comm zer_left_mult  by metis
    then have "times x w1 = []"
          using 1 by auto
    moreover have "times y w2 = []"
          using 2 assms by auto
    ultimately have "(scalar_product (times x w1) ( times y w2)) = zer"
          unfolding scalar_product_def scalar_prodI_def by auto
    with 3 show ?thesis by auto
   qed
  then show ?case by auto
  next
  case (Suc k)
   have "(length w1 = length w2) \<and>(length w1 = (Suc k))  \<Longrightarrow> ?case"
   proof-
    assume assms:"(length w1 = length w2) \<and>(length w1 = (Suc k))"
    have "\<exists>a1 u1.(w1 = a1#u1)\<and>(length u1 = k)"
          using assms by (metis length_Suc_conv)
    then obtain a1 u1 where "(w1 = a1#u1)\<and>(length u1 = k)"
          by auto
    then have Cons_1:"(w1 = a1#u1)\<and>(length u1 = k)"
          by auto
    have "length w2 = (Suc k)"
          using assms by auto
    then have "\<exists>a2 u2.(w2 = a2#u2)\<and>(length u2 = k)"
          using assms by (metis length_Suc_conv)
    then obtain a2 u2 where "(w2 = a2#u2)\<and>(length u2 = k)"
          by auto
    then have Cons_2:"(w2 = a2#u2)\<and>(length u2 = k)"
          by auto 
    then have "(length u1 = length u2)\<and>(length u1 = k)"
          using Cons_1 by auto
    then have Cons_3:"x * y * scalar_product u1 u2 
                        = scalar_product (times x u1) (times y u2)"
          using Suc assms by auto
    have "scalar_product (a1#u1) (a2#u2) = (a1*a2) + (scalar_product u1 u2)"
          unfolding scalar_product_def scalar_prodI_def zip_def by auto
    then have "scalar_product w1 w2 = (a1*a2) + (scalar_product u1 u2)"
          using Cons_1 Cons_2 by auto
    then have "(x*y)*(scalar_product w1 w2) 
                       = ((x*y)*(a1*a2)) + ((x*y)*(scalar_product u1 u2))" 
          using plus_right_distributivity by (metis plus_left_distributivity)
    then have Cons_4:"(x*y)*(scalar_product w1 w2) 
                       = (x*a1*y*a2)+ ((x*y)*(scalar_product u1 u2))"  
          using comm assoc by metis
    have "(times x w1) = (x*a1)#(times x u1)"
          using times.simps Cons_1 by auto
    moreover have "(times y w2) = (y*a2)#(times y u2)"
          using times.simps Cons_2 by auto
    ultimately have Cons_5:"scalar_product (times x w1) (times y w2) 
                            = scalar_product 
                                  ((x*a1)#(times x u1)) 
                                  ((y*a2)#(times y u2))"
          by auto  
    then have "... = ((x*a1)*(y*a2)) 
                             + scalar_product (times x u1) (times y u2)"
          unfolding scalar_product_def scalar_prodI_def zip_def by auto
    with Cons_3 Cons_4 Cons_5 show ?thesis using assoc by auto
   qed
   then show ?case by auto
 qed


lemma effective_scalar_product_times:
 assumes "(length w1 = length w2)"  
 shows "(f (x*y) (scalar_product w1 w2)) 
                       = (scalar_product (times x w1) ( times y w2))"
 using scalar_product_times assms by auto 


lemma zip_append:"(length zs = length ws)\<and>(length xs = length ys) 
                       \<Longrightarrow> (zip (xs@zs) (ys@ws)) = (zip xs ys)@(zip zs ws)"
 using zip_append1 zip_append2 by auto 


lemma scalar_product_append:
 "\<forall>xs ys zs ws.(length zs = length ws)
               \<and>(length xs = length ys) 
               \<and>(length xs = n)  \<longrightarrow> 
                     (scalar_product (xs@zs) (ys@ws))
                                   = (scalar_product xs ys)
                                         +(scalar_product zs ws)"
 apply(rule allI)
 apply(rule allI)
 apply(rule allI)
 apply(rule allI)
 proof(induct n)
  case 0
   have "(length zs = length ws) \<and>(length xs = length ys) \<and>(length xs = 0)
          \<Longrightarrow>
           (scalar_product (xs@zs) (ys@ws))
                                   = (scalar_product xs ys)
                                          +(scalar_product zs ws)"
   proof-
    assume assms:"(length zs = length ws)\<and>(length xs = length ys)
                                        \<and>(length xs = 0)"
    have 1:"xs = []"
       using assms by auto
    moreover have 2:"ys = []"
       using assms by auto
    ultimately have "scalar_product xs ys = zer"
       unfolding scalar_product_def scalar_prodI_def zip_def by auto
    then have "(scalar_product xs ys)+(scalar_product zs ws) 
                                       = (scalar_product zs ws)"
       using plus_left_id by auto 
    moreover have "(scalar_product (xs@zs) (ys@ws)) = (scalar_product zs ws)"
       using 1 2 by auto
    ultimately show ?thesis by auto
   qed
  then show ?case by auto
 next
 case (Suc k)
  have "(length zs = length ws)\<and>(length xs = length ys)\<and>(length xs = (Suc k))  \<Longrightarrow>
        (scalar_product (xs@zs) (ys@ws))
                                   = (scalar_product xs ys)
                                      +(scalar_product zs ws)" 
  proof-
   assume assms:"(length zs = length ws)
                   \<and>(length xs = length ys)
                   \<and>(length xs = (Suc k))"
   have "\<exists>x xss.(xs = x#xss)\<and>(length xss = k)"
       using assms by (metis Suc_length_conv)         
   then obtain x xss where "(xs = x#xss)\<and>(length xss = k)"
       by auto
   then have 1:"(xs = x#xss)\<and>(length xss = k)"
       by auto  
   have "\<exists>y yss.(ys = y#yss)\<and>(length yss = k)"
       using assms by (metis Suc_length_conv)         
   then obtain y yss where "(ys = y#yss)\<and>(length yss = k)"
       by auto
   then have 2:"(ys = y#yss)\<and>(length yss = k)"
       by auto  
   with 1 have "length xss = length yss \<and> length xss = k"
       by auto
   then have 3:"(scalar_product (xss@zs) (yss@ws))
                                   = (scalar_product xss yss)
                                    +(scalar_product zs ws)" 
       using 1 2 assms Suc by auto  
   then have 4:"(scalar_product ((x#xss)@zs) ((y#yss)@ws)) = 
                        (scalar_product (x#(xss@zs)) (y#(yss@ws)))"
       by auto
   then have "... =  (x*y) + (scalar_product (xss@zs) (yss@ws))"
       unfolding scalar_product_def scalar_prodI_def 
       using zip_Cons  scalar_prodI_def scalar_prod_cons 
       by (metis)
   with 4 have 5:"(scalar_product (xs@zs) ((ys)@ws))
                       =  (x*y) + (scalar_product (xss@zs) (yss@ws))"
       using 1 2  by auto
   moreover have "(scalar_product xs ys) = (x*y) + (scalar_product xss yss)"
       unfolding scalar_product_def scalar_prodI_def 
       using zip_Cons
       by (metis "1" "2" scalar_prodI_def scalar_prod_cons)
   moreover then have "(scalar_product xs ys)+(scalar_product zs ws)
                               =  (x*y) 
                                       + (scalar_product xss yss) 
                                       + (scalar_product zs ws)"
       by auto
   ultimately show ?thesis using 3 plus_assoc by auto 
  qed
  then show ?case by auto
 qed

lemma effective_scalar_product_append:
assumes "length zs = length ws" and  "(length xs = length ys)"   
 shows "(scalar_product (xs@zs) (ys@ws)) = (scalar_product xs ys)+(scalar_product zs ws)"
    using scalar_product_append assms by auto

lemma scalar_product_distributivity:
"\<forall>v1 v2 w1 w2.((length v1 = length v2)\<and>(length v1 = n)\<and> (length w1 = length w2)
           \<longrightarrow>  (scalar_product v1 v2)*(scalar_product w1 w2)
      = scalar_product (vec_vec_Tensor v1 w1) (vec_vec_Tensor v2 w2)) "
 apply (rule allI)
 apply (rule allI)
 apply (rule allI)
 apply (rule allI)
 proof(induct "n")
  case 0 
   have "((length v1 = length v2)\<and>(length v1 = 0)\<and> (length w1 = length w2))
           \<longrightarrow>length v1 = 0"
        using 0 by auto
   then have 1:"((length v1 = length v2)
                 \<and>(length v1 = 0)
                 \<and>(length w1 = length w2))
                        \<longrightarrow>v1 = []"
        by auto
   moreover have "((length v1 = length v2)
                   \<and>(length v1 = 0)
                   \<and>(length w1 = length w2))
           \<longrightarrow>length v2 = 0"
        using 0 by auto
   moreover then have 2:"((length v1 = length v2)
                          \<and>(length v1 = 0)
                          \<and>(length w1 = length w2))
                                    \<longrightarrow>v2 = []"
        by auto  
   ultimately have 3:
         "((length v1 = length v2)\<and>(length v1 = 0)\<and> (length w1 = length w2))
           \<longrightarrow>scalar_product v1 v2 = zer"
        unfolding scalar_product_def scalar_prodI_def using zip_Nil by auto 
   then have 4:"f zer (scalar_product w1 w2) = zer"
        using zer_left_mult by auto
   have "((length v1 = length v2)\<and>(length v1 = 0)\<and> (length w1 = length w2))
           \<longrightarrow>vec_vec_Tensor v1 w1 = []"
        using 1 by auto
   moreover have "((length v1 = length v2)
                   \<and>(length v1 = 0)
                   \<and>(length w1 = length w2))
                    \<longrightarrow>vec_vec_Tensor v2 w2 = []"
        using 2 by auto
   ultimately have "((length v1 = length v2)
                      \<and>(length v1 = 0)
                      \<and>(length w1 = length w2))
                         \<longrightarrow> scalar_product 
                                 (vec_vec_Tensor v1 w1) 
                                 (vec_vec_Tensor v2 w2)  = zer"
        unfolding scalar_product_def scalar_prodI_def using zip_Nil by auto
   with 3 4 show ?case by auto   
  next
  case (Suc k)
   have "((length v1 = length v2)\<and>(length v1 = Suc k)
                    \<and> (length w1 = length w2))
           \<Longrightarrow>  f (scalar_product v1 v2) (scalar_product w1 w2)
      = scalar_product (vec_vec_Tensor v1 w1) (vec_vec_Tensor v2 w2)"
   proof-
    assume assms:"((length v1 = length v2)\<and>(length v1 = Suc k)
                    \<and> (length w1 = length w2))"
    have "length v1 = Suc k"
          using Suc assms by auto
    then have "(\<exists>a1 u1.(v1 = a1#u1)\<and>(length u1 = k))"
          using assms Suc_length_conv by metis
    then obtain a1 u1 where "(v1 = a1#u1)\<and>(length u1 = k)"
          using assms    by auto
    then have Cons_1:"(v1 = a1#u1)\<and>(length u1 = k)"
          by auto
    moreover have "length v2 = Suc k"
          using assms Suc by auto
    then have "(\<exists>a2 u2.(v2 = a2#u2)\<and>(length u2 = k))"
          using  Suc_length_conv by metis
    then obtain a2 u2 where "(v2 = a2#u2)\<and>(length u2 = k)"
          by auto
    then have Cons_2: "(v2 = a2#u2)\<and>(length u2 = k)"
          by simp
    then have "length u1 = length u2"
          using Cons_1 by auto
    then have Cons_3:"(scalar_product u1 u2) * scalar_product w1 w2 =
         scalar_product (vec_vec_Tensor u1 w1) (vec_vec_Tensor u2 w2)"
          using Suc Cons_1 Cons_2 assms by auto
    then have "zip v1 v2 = (a1,a2)#(zip u1 u2)"
          using  zip_Cons Cons_1 Cons_2 by auto 
    then have Cons_4:"scalar_product v1 v2 =  (a1*a2)+ (scalar_product u1 u2)"  
          unfolding scalar_product_def scalar_prodI_def by auto
    then have "f (scalar_product v1 v2) (scalar_product w1 w2)
                      = ((a1*a2)+ (scalar_product u1 u2))*(scalar_product w1 w2)"
          by auto
    then have "... = ((a1*a2)*(scalar_product w1 w2)) 
                                     + ((scalar_product u1 u2)*(scalar_product w1 w2))"
          using plus_right_distributivity by auto
    then have Cons_5:"... = ((a1*a2)*(scalar_product w1 w2))
                       + scalar_product (vec_vec_Tensor u1 w1) (vec_vec_Tensor u2 w2)"
          using Cons_3 by auto
    then have Cons_6:"... = (scalar_product (times a1 w1) (times a2 w2))
                    +  scalar_product (vec_vec_Tensor u1 w1) (vec_vec_Tensor u2 w2)"
          using assms effective_scalar_product_times by auto  
    then have "scalar_product (vec_vec_Tensor v1 w1) (vec_vec_Tensor v2 w2)
                        = scalar_product (vec_vec_Tensor (a1#u1) w1) (vec_vec_Tensor (a2#u2) w2)"
          using Cons_1 Cons_2 by auto
    moreover have "(vec_vec_Tensor (a1#u1) w1) = (times a1 w1)@(vec_vec_Tensor u1 w1)"
          using vec_vec_Tensor.simps by auto
    moreover have "(vec_vec_Tensor (a2#u2) w2) = (times a2 w2)@(vec_vec_Tensor u2 w2)"
          using vec_vec_Tensor.simps by auto
    ultimately have Cons_7:"scalar_product (vec_vec_Tensor v1 w1) (vec_vec_Tensor v2 w2)
                      = scalar_product ((times a1 w1)@(vec_vec_Tensor u1 w1)) 
                                ((times a2 w2)@(vec_vec_Tensor u2 w2))"
          by auto 
    moreover have "length (vec_vec_Tensor u2 w2) = length (vec_vec_Tensor u1 w1)"
          using assms by (metis Cons_1 Cons_2 vec_vec_Tensor_length)
    moreover have "length (times a1 w1) = (length (times a2 w2))"
          using assms by (metis preserving_length)  
    ultimately have "scalar_product ((times a1 w1)@(vec_vec_Tensor u1 w1)) 
                                ((times a2 w2)@(vec_vec_Tensor u2 w2)) = 
                    (scalar_product (times a1 w1) (times a2 w2))
                    +  scalar_product (vec_vec_Tensor u1 w1) (vec_vec_Tensor u2 w2)"
          using effective_scalar_product_append by auto 
    then show ?thesis 
          using Cons_6 Cons_7 \<open>a1 * a2 + scalar_product u1 u2 * scalar_product w1 w2 
                 = a1 * a2 * scalar_product w1 w2 
                  + (scalar_product u1 u2 * scalar_product w1 w2)\<close> 
          by (metis Cons_3 Cons_4 )
   qed
   then show ?case by auto
 qed

lemma effective_scalar_product_distributivity:
 assumes "length v1 = length v2" and "length w1 = length w2"
 shows "(scalar_product v1 v2)*(scalar_product w1 w2)
      = scalar_product (vec_vec_Tensor v1 w1) (vec_vec_Tensor v2 w2) "
     using assms scalar_product_distributivity by auto


lemma row_length_constant:assumes "mat nr nc A" and "j < length A" 
         shows "length (A!j) = (row_length A)"
proof(cases A)
 case Nil
    have "length (A!j) = 0"
          using assms(2) Nil by auto
    then show ?thesis using assms(2) Nil row_length_Nil  by (metis)
 next
 case (Cons v B)
  have 1:"\<forall>x. ((x \<in> set A) \<longrightarrow> length x = nr)"
          using assms unfolding mat_def Ball_def vec_def by auto
  moreover have "(A!j) \<in> set A"
          using assms(2) by auto
  ultimately have 2:"length (A!j) = nr"
          by auto
  have "hd A \<in> set A"     
          using hd_def Cons by auto
  then have "row_length A = nr"
          using row_length_def 1 by auto
  then show ?thesis using 2 by auto
qed



theorem row_col_match:
 fixes A1 A2 B1 B2 i j
 assumes wf1:"mat (row_length A1) (length A1) A1"
    and wf2:"mat (row_length A2) (length A2) A2"
    and wf3:"mat (row_length B1) (length B1) B1"
    and wf4:"mat (row_length B2) (length B2) B2"
    and matchAA:"length A1 = row_length A2"
    and matchBB:"length B1 = row_length B2"
    and non_Nil:"(A1 \<noteq> [])\<and>(A2 \<noteq> [])\<and>(B1 \<noteq> [])\<and>(B2 \<noteq> [])"
    and i:"i<(row_length A1)*(row_length B1)" and j:"j< (length A2)*(length B2)"
 shows "length (row A1 (i div (row_length B1))) 
                 = length (col A2  (j div (length B2)))"
 and "length (row B1 (i mod (row_length B1))) 
                 = length (col B2 (j mod (length B2)))"
proof-
 have "i div (row_length B1) < row_length  A1" 
            using i by (metis div_left_ineq)
 then have 1:"length (row A1 (i div (row_length B1))) = length A1"
            unfolding row_def by auto
 have "j div (length B2)< length A2"
            using j by (metis div_left_ineq)
 then have 2:"length (col A2  (j div (length B2))) = row_length A2"
            using row_length_constant wf2  unfolding col_def by auto
 with 1 matchAA show "length (row A1 (i div (row_length B1)))=length (col A2  (j div (length B2)))"
            by auto
 have "i mod (row_length B1) < row_length B1"
            using i by (metis less_nat_zero_code mod_less_divisor mult_is_0 neq0_conv)
 then have 2:"length (row B1 (i mod (row_length B1))) = length B1"
            unfolding row_def by auto
 have "j mod (length B2) < length B2"
            using j by (metis less_nat_zero_code mod_less_divisor mult_is_0 neq0_conv)
 then have "length (col B2 (j mod (length B2))) = row_length B2"
            using row_length_constant wf4  unfolding col_def by auto
 with 2 matchBB show "length (row B1 (i mod (row_length B1))) = length (col B2 (j mod (length B2)))"
            by auto
qed


lemma effective_row_col_match: assumes "matrix_match A1 A2 B1 B2"
 shows "\<forall>i j. ((i<(row_length A1)*(row_length B1))\<and>(j<(length A2)*(length B2))) 
       \<longrightarrow>length (row A1 (i div (row_length B1))) = length (col A2  (j div (length B2)))"
  "\<forall>i j. ((i<(row_length A1)*(row_length B1))\<and>(j<(length A2)*(length B2))) 
           \<longrightarrow>length (row B1 (i mod (row_length B1))) = length (col B2 (j mod (length B2)))"
 using assms row_col_match unfolding matrix_match_def by auto 
       

theorem prelim_element_match:
 "matrix_match A1 A2 B1 B2 \<Longrightarrow> (\<forall>i j.((i<(row_length A1)*(row_length B1))
                              \<and>(j<(length A2)*(length B2))) 
         \<longrightarrow>
  (((A1 \<circ> A2)\<otimes>(B1 \<circ>  B2))!j!i
                  = ((A1 \<otimes> B1)\<circ>(A2 \<otimes> B2))!j!i))" 
proof- 
 assume assms:"matrix_match A1 A2 B1 B2 "
 have 1:"matrix_match A1 A2 B1 B2"
         using assms matrix_compose_cond_def by auto
 then have 2:
    "\<forall>i j. ((i<(row_length A1)*(row_length B1))\<and>(j<(length A2)*(length B2))) 
     \<longrightarrow>
      (((A1 \<circ> A2)\<otimes>(B1 \<circ>  B2))!j!i 
                = (scalar_product 
                    (row A1 (i div (row_length B1))) (col A2  (j div (length B2))))
                   *(scalar_product 
                      (row B1 (i mod (row_length B1))) (col B2 (j mod (length B2)))))"
         using effective_matrix_match_condn_1 assms  by metis
 moreover from 1 have 3:"\<forall>i j. ((i<(row_length A1)*(row_length B1))\<and>(j<(length A2)*(length B2))) \<longrightarrow>
           ((A1 \<otimes> B1)\<circ>(A2 \<otimes> B2))!j!i = 
                 scalar_product 
          (vec_vec_Tensor (row A1 (i div row_length B1)) (row B1 (i mod row_length B1))) 
          (vec_vec_Tensor (col A2 (j div length B2)) (col B2 (j mod length B2)))" 
         using effective_matrix_match_condn_2 by auto 
 have  "\<forall>i j. ((i<(row_length A1)*(row_length B1))\<and>(j<(length A2)*(length B2))) 
         \<longrightarrow>length (row A1 (i div (row_length B1))) 
                           = length (col A2  (j div (length B2)))"
 and "\<forall>i j. ((i<(row_length A1)*(row_length B1))\<and>(j<(length A2)*(length B2))) 
           \<longrightarrow> length (row B1 (i mod (row_length B1))) 
                             = length (col B2 (j mod (length B2)))"
         using assms effective_row_col_match by auto  
 then have " \<forall>i j. ((i<(row_length A1)*(row_length B1))\<and>(j<(length A2)*(length B2))) 
           \<longrightarrow>
           (scalar_product (row A1 (i div (row_length B1))) (col A2  (j div (length B2))))
                   *(scalar_product (row B1 (i mod (row_length B1))) (col B2 (j mod (length B2))))
             =  scalar_product 
          (vec_vec_Tensor (row A1 (i div row_length B1)) (row B1 (i mod row_length B1))) 
          (vec_vec_Tensor (col A2 (j div length B2)) (col B2 (j mod length B2)))" 
         using effective_scalar_product_distributivity by auto
 then show ?thesis using 2 3  by auto
qed

theorem element_match:
 "matrix_match A1 A2 B1 B2 \<Longrightarrow>(\<forall>i<((row_length A1)*(row_length B1)).
                              \<forall>j<((length A2)*(length B2)). 
(((A1 \<circ> A2)\<otimes>(B1 \<circ>  B2))!j!i
                  = ((A1 \<otimes> B1)\<circ>(A2 \<otimes> B2))!j!i))"
 using prelim_element_match by auto

lemma application: fixes m1 m2 
shows "\<forall>m1 m2.(mat nr nc m1)
              \<and>(mat nr nc m2)
              \<and>(\<forall> j < nc. \<forall> i < nr. m1 ! j ! i = m2 ! j ! i)
                  \<longrightarrow> (m1 = m2)"
 using mat_eqI by blast


theorem tensor_compose_condn: 
assumes wf1:"mat nr nc ((A1\<circ>A2)\<otimes>(B1\<circ>B2))"
   and wf2:"mat nr nc ((A1 \<otimes> B1)\<circ>(A2 \<otimes> B2))"
   and wf3:"\<forall>j<nc.\<forall>i<nr.(((A1 \<circ> A2)\<otimes>(B1 \<circ>B2))!j!i  
                              = ((A1 \<otimes> B1)\<circ>(A2 \<otimes> B2))!j!i)" 
 shows "((A1 \<circ> A2) \<otimes> (B1 \<circ> B2))  
                              = ((A1 \<otimes> B1)\<circ>(A2 \<otimes> B2))" 
 using application wf1 wf2 wf3 by blast
 

text\<open>The following theorem gives us the distributivity relation of tensor
product with matrix multiplication\<close>

theorem distributivity: 
 assumes  "matrix_match A1 A2 B1 B2"
 shows "((A1 \<circ> A2)\<otimes>(B1\<circ>B2)) = ((A1 \<otimes> B1)\<circ>(A2 \<otimes> B2))" 
proof-
 let ?nr = " ((row_length A1)*(row_length B1))"
 let ?nc = "((length A2)*(length B2))"
 have "mat ?nr ?nc ((A1\<circ>A2)\<otimes>(B1\<circ>B2))"
          by (metis assms effective_tensor_compose_distribution1)
 moreover have "mat ?nr ?nc ((A1 \<otimes> B1)\<circ>(A2 \<otimes> B2))"
          using assms by (metis effective_tensor_compose_distribution2)
 moreover have "\<forall>j<?nc.\<forall>i<?nr.
                   (((A1 \<circ> A2)\<otimes>(B1 \<circ>B2))!j!i 
                                = ((A1 \<otimes> B1)\<circ>(A2 \<otimes> B2))!j!i)" 
          using element_match assms by auto
 ultimately show ?thesis 
          using application by blast
qed   

end

end
