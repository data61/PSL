section\<open>Kauffman Matrix and Kauffman Bracket- Definitions and Properties\<close>
theory Kauffman_Matrix
imports
  Matrix_Tensor.Matrix_Tensor
  Link_Algebra
  "HOL-Computational_Algebra.Polynomial"
  "HOL-Computational_Algebra.Fraction_Field" 
begin


section\<open>Rational Functions\<close>

text\<open>intpoly is the type of integer polynomials\<close>
type_synonym intpoly = "int poly"

(*The following lemma tells us that (pCons 0 1) is an identity function 
on a given type, if it is a commutative ring*)

lemma eval_pCons: "poly (pCons 0 1) x = x"
 using poly_1 poly_pCons by auto

lemma pCons2:" (pCons 0 1) \<noteq> (1::int poly)"
 using eval_pCons poly_1 zero_neq_one by metis

definition var_def: "x = (pCons 0 1)"

lemma non_zero:"x \<noteq> 0"
 using var_def pCons_eq_0_iff zero_neq_one by (metis)

text\<open>rat$\_$poly is the fraction field of integer polynomials. In other
words, it is the type of rational functions\<close>

type_synonym rat_poly = "intpoly fract"

text\<open>A is defined to be x/1, while B is defined to be 1/x\<close>

definition var_def1:"A =  Fract x 1"
      
definition var_def2: "B = Fract 1 x"

lemma assumes "b \<noteq> 0" and "d \<noteq> 0"
      shows "Fract a b = Fract c d \<longleftrightarrow> a * d = c * b"
 using eq_fract assms by auto

lemma A_non_zero:"A \<noteq> (0::rat_poly)" 
 unfolding var_def1 
proof(rule ccontr)
 assume 0:" \<not> (Fract x 1 \<noteq> (0::rat_poly)) "
 then have "Fract x 1 = (0::rat_poly)"
           by auto
 moreover have "(0::rat_poly) = Fract (0::intpoly) (1::intpoly)"
           by (metis Zero_fract_def) 
 ultimately have "Fract x (1::intpoly) = Fract (0::intpoly) (1::intpoly)"
           by auto
 moreover have "(1::intpoly) \<noteq> 0"
           by auto
 ultimately have "x*(1::intpoly) = (0::intpoly)*(1::intpoly)"
           using eq_fract by metis
 then have "x = (0::intpoly)"
           by auto
 then show False using non_zero by auto
qed

lemma mult_inv_non_zero:
 assumes "(p::rat_poly) \<noteq> 0" 
     and "p*q = (1::rat_poly)"
 shows "q \<noteq> 0"
 using assms by auto


abbreviation rat_poly_times::"rat_poly \<Rightarrow> rat_poly \<Rightarrow> rat_poly"
where
"rat_poly_times p q \<equiv> p*q"

abbreviation rat_poly_plus::"rat_poly \<Rightarrow> rat_poly \<Rightarrow> rat_poly"
where
"rat_poly_plus p q \<equiv> p+q"

abbreviation rat_poly_inv::"rat_poly \<Rightarrow> rat_poly"
where
"rat_poly_inv p \<equiv> (- p)"


interpretation  rat_poly:semiring_0 "rat_poly_plus" 0 "rat_poly_times"
 by (unfold_locales)
  

interpretation  rat_poly:semiring_1 1 "rat_poly_times" "rat_poly_plus" 0
 by (unfold_locales)
 

lemma mat1_equiv:"mat1 (1::nat) = [[(1::rat_poly)]]"
 by (simp add:mat1I_def vec1I_def)



text\<open>rat$\_$poly is an interpretation of the locale plus\_mult\<close>

interpretation  rat_poly:plus_mult "1" "rat_poly_times"  0 "rat_poly_plus" 
                                  "rat_poly_inv"
 apply(unfold_locales)
 apply(auto)
 proof-
  fix p q r
  show "rat_poly_times p (rat_poly_plus q r) 
                    = rat_poly_plus (rat_poly_times p q) (rat_poly_times p r)"
         by (simp add: distrib_left)
  show "rat_poly_times (rat_poly_plus p q) r 
                    = rat_poly_plus (rat_poly_times p r) (rat_poly_times q r)"
         by (metis comm_semiring_class.distrib)
 qed


(*using matrix_multiplication *)
lemma  "rat_poly.matrix_mult [[A,1],[0,A]] [[A,0],[0,A]] = [[A*A,A],[0,A*A]] "
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)
 done
        

abbreviation 
   rat_polymat_tensor::"rat_poly mat \<Rightarrow> rat_poly mat \<Rightarrow> rat_poly mat" 
                                                          (infixl "\<otimes>" 65) 
where
"rat_polymat_tensor p q \<equiv> rat_poly.Tensor p q"

 
lemma assumes "(j::nat) div a = i div a"
          and "j mod a = i mod a"
      shows "j = i" 
proof-
 have "a*(j div a) + (j mod a) = j" 
    using mult_div_mod_eq by simp
 moreover have "a*(i div a) + (i mod a) = i"
    using mult_div_mod_eq by auto
 ultimately show ?thesis using assms by metis
qed  


lemma "[[1]] \<otimes>  M = M"
 by (metis rat_poly.Tensor_left_id)

lemma " M \<otimes> [[1]] = M"
 by (metis rat_poly.Tensor_right_id)

section\<open>Kauffman matrices\<close>
text\<open>We assign every brick to a matrix of rational polynmials\<close>

primrec brickmat::"brick \<Rightarrow> rat_poly mat"
where
"brickmat vert = [[1,0],[0,1]]"
|"brickmat cup  = [[0],[A],[-B],[0]]"
|"brickmat cap  = [[0,-A,B,0]]"
|"brickmat over = [[A,0,0,0],
                   [0,0,B,0],
                   [0,B,A-(B*B*B),0],
                   [0,0,0,A]]" 
|"brickmat under  = [[B,0,0,0],
                     [0,B-(A*A*A),A,0],
                     [0,A,0,0],
                     [0,0,0,B]]"

lemma inverse1:"rat_poly_times A B = 1"
 using non_zero  One_fract_def monoid_mult_class.mult.right_neutral 
       mult_fract mult_fract_cancel  var_def1 var_def2
 by (metis (hide_lams, no_types))

lemma inverse2:"rat_poly_times B A = 1"
 using  One_fract_def monoid_mult_class.mult.right_neutral mult_fract 
        mult_fract_cancel non_zero var_def1 var_def2
 by (metis (hide_lams, no_types))

lemma B_non_zero:"B \<noteq> 0"
 using A_non_zero mult_inv_non_zero inverse1 
       divide_fract div_0 fract_collapse(2) 
       monoid_mult_class.mult.left_neutral 
       mult_fract_cancel non_zero var_def2 zero_neq_one
 by (metis (hide_lams, mono_tags))

lemma "rat_poly_times p (q + r) 
                 = (rat_poly_times p q) + (rat_poly_times p r)"
 by (metis rat_poly.plus_left_distributivity)

lemma minus_left_distributivity:
      "rat_poly_times p (q - r) 
                  = (rat_poly_times p q) - (rat_poly_times p r)"
 using minus_mult_right right_diff_distrib by blast 
  
lemma minus_right_distributivity:
    "rat_poly_times (p - q) r = (rat_poly_times p r) - (rat_poly_times q r)"
 using  minus_left_distributivity rat_poly.comm by metis

lemma equation:
   "rat_poly_plus 
     (rat_poly_times B (B - rat_poly_times (rat_poly_times A A) A))
     (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A) 
              = 0"
proof-
 have " rat_poly_times (rat_poly_times A A) A
                       = ((A*A)*A)"
      by auto
 then have "rat_poly_times B (B - rat_poly_times (rat_poly_times A A) A)
                     = B*B - B*((A*A)*A)"
      using minus_left_distributivity by auto    
 moreover have "... = B*B - (B*(A*(A*A)))"
      by auto
 moreover have "... = B*B - ((B*A)*(A*A))"
      by auto
 moreover have "... = B*B - A*A"
      using inverse2 by auto
 ultimately have 1:
         "rat_poly_times B (B - rat_poly_times (rat_poly_times A A) A)
                               =  B*B - A*A"
      by auto
 have "rat_poly_times (rat_poly_times B B) B = (B*B)*B"
      by auto
 then have 
          "(rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A)
                  = (A*A) - ((B*B)*B)*A"
      using minus_right_distributivity by auto
 moreover have "... = (A*A) - ((B*B)*(B*A))"
                     by auto
 moreover have "... = (A*A) - (B*B)"
      using inverse2 by auto
 ultimately have 2:
          "(rat_poly_times (A - rat_poly_times (rat_poly_times B B) B) A)
                  = (A*A) - (B*B)"
      by auto
 have "B*B - A*A + (A*A) - (B*B) = 0"
      by auto
 with 1 2 show ?thesis by auto
qed

lemma  "rat_poly.matrix_mult (brickmat over) (brickmat under) 
   = [[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]] "
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)
 apply(auto simp add:inverse1 inverse2)
 apply(auto simp add:equation)
 done 


lemma "rat_poly_inv A = -A"
 by auto

lemma vert_dim:"rat_poly.row_length (brickmat vert) = 2 \<and>length (brickmat vert) = 2"
        using rat_poly.row_length_def by auto
lemma cup_dim:"rat_poly.row_length (brickmat cup) = 1" and "length (brickmat cup) = 4"
        using rat_poly.row_length_def by auto
lemma cap_dim:"rat_poly.row_length (brickmat cap) = 4" and "length (brickmat cap) = 1"
        using rat_poly.row_length_def by auto
lemma over_dim:"rat_poly.row_length (brickmat over) = 4" and "length (brickmat over) = 4"
        using rat_poly.row_length_def by auto
lemma under_dim:"rat_poly.row_length (brickmat under) = 4" and "length (brickmat under) = 4"
        using rat_poly.row_length_def by auto
lemma mat_vert:"mat 2 2 (brickmat vert)"
           unfolding mat_def Ball_def vec_def by auto
lemma mat_cup:"mat 1 4 (brickmat cup)"
           unfolding mat_def Ball_def vec_def by auto
lemma mat_cap:"mat 4 1 (brickmat cap)"
           unfolding mat_def Ball_def vec_def by auto
lemma mat_over:"mat 4 4 (brickmat over)"
           unfolding mat_def Ball_def vec_def by auto
lemma mat_under:"mat 4 4 (brickmat under)"
           unfolding mat_def Ball_def vec_def by auto

primrec rowlength::"nat \<Rightarrow> nat"
where
"rowlength 0 = 1"
|"rowlength (Suc k) = 2*(Suc k)"

lemma "(rat_poly.row_length (brickmat d)) =  (2^(nat (domain d))) "
 using vert_dim cup_dim cap_dim over_dim under_dim domain.simps 
 by (cases d) (auto)

lemma "rat_poly.row_length (brickmat cup) = 1"
 unfolding rat_poly.row_length_def by auto

lemma two:"(Suc (Suc 0)) = 2"
 by eval

text\<open>we assign every block to a matrix of rational function as follows\<close>

primrec blockmat::"block \<Rightarrow> rat_poly mat"
where
"blockmat [] = [[1]]"
|"blockmat (l#ls) = (brickmat l) \<otimes> (blockmat ls)"


lemma "blockmat [a] = brickmat a"
 unfolding blockmat.simps  rat_poly.Tensor_right_id by auto

lemma nat_sum:
 assumes "a \<ge> 0" and "b \<ge> 0"
 shows "nat (a+b) = (nat a) + (nat b)"
 using assms by auto

lemma "rat_poly.row_length (blockmat ls) = (2^ (nat ((domain_block ls))))"
proof(induct ls)
 case Nil
  show ?case unfolding blockmat.simps(1) rat_poly.row_length_def by auto
 next
 case (Cons l ls) 
  show ?case
   proof(cases l)
   case vert
    have "rat_poly.row_length (blockmat ls) = 2 ^ nat (domain_block ls)"
         using Cons by auto
    then have "rat_poly.row_length (blockmat (l#ls)) 
                        = (rat_poly.row_length (brickmat l))
                            *(rat_poly.row_length (blockmat ls))"
         using blockmat.simps  rat_poly.row_length_mat by auto
    moreover have "... = 2*(2 ^ nat (domain_block ls))"
         using rat_poly.row_length_def Cons vert by auto
    moreover have "... = 2^(1 + nat (domain_block ls))"
         using domain_block.simps  by auto
    moreover have "... = 2^(nat (domain l) + nat (domain_block ls))"
         using domain.simps vert by auto 
    moreover have "... = 2^(nat (domain l + domain_block ls))"
        using Suc_eq_plus1_left Suc_nat_eq_nat_zadd1 
              calculation(4) domain.simps(1) domain_block_non_negative 
              vert
        by (metis)
    moreover have "... = 2^(nat (domain_block (l#ls)))"
       using domain_block.simps by auto
    ultimately show ?thesis by metis  
   next
   case over
    have "rat_poly.row_length (blockmat ls) = 2 ^ nat (domain_block ls)"
       using Cons by auto
    then have "rat_poly.row_length (blockmat (l#ls)) 
                             = (rat_poly.row_length (brickmat l))
                               *(rat_poly.row_length (blockmat ls))"
       using blockmat.simps  rat_poly.row_length_mat by auto
    also have "... = 4*(2 ^ nat (domain_block ls))"
      using rat_poly.row_length_def Cons over by auto
    also have "... = 2^(2 + nat (domain_block ls))"
      using domain_block.simps by auto
    also have "... = 2^(nat (domain l) + nat (domain_block ls))"
      using domain.simps over by auto
    also have "... = 2^(nat (domain l + domain_block ls))"
      by (simp add: nat_add_distrib domain_block_nonnegative over)
    also have "... = 2^(nat (domain_block (l#ls)))"
      by simp
    finally show ?thesis .
   next
   case under
    have "rat_poly.row_length (blockmat ls) = 2 ^ nat (domain_block ls)"
       using Cons by auto
    then have "rat_poly.row_length (blockmat (l#ls)) 
                              = (rat_poly.row_length (brickmat l))
                                 *(rat_poly.row_length (blockmat ls))"
       using blockmat.simps  rat_poly.row_length_mat by auto
    also have "... = 4*(2 ^ nat (domain_block ls))"
      using rat_poly.row_length_def Cons under by auto
    also have "... = 2^(2 + nat (domain_block ls))"
      using domain_block.simps  by auto
    also have "... = 2^(nat (domain l) + nat (domain_block ls))"
      using domain.simps under by auto 
    also have "... = 2^(nat (domain l + domain_block ls))"
      by (simp add: nat_add_distrib domain_block_nonnegative under)
    also have "... = 2^(nat (domain_block (l#ls)))"
      using domain_block.simps by auto
    finally show ?thesis .
   next
   case cup 
    have "rat_poly.row_length (blockmat ls) = 2 ^ nat (domain_block ls)"
       using Cons by auto
    then have "rat_poly.row_length (blockmat (l#ls)) 
                              = (rat_poly.row_length (brickmat l))
                                *(rat_poly.row_length (blockmat ls))"
       using blockmat.simps  rat_poly.row_length_mat by auto
    moreover have "... = 1*(2 ^ nat (domain_block ls))"
       using rat_poly.row_length_def Cons cup by auto
    moreover have "... = 2^(0 + nat (domain_block ls))"
       using domain_block.simps  by auto
    moreover have "... = 2^(nat (domain l) + nat (domain_block ls))"
       using domain.simps cup by auto 
    moreover have "... = 2^(nat (domain l + domain_block ls))"
       using nat_sum cup  domain.simps(2) nat_0 plus_int_code(2) 
             plus_nat.add_0
             by (metis)
    moreover have "... = 2^(nat (domain_block (l#ls)))"
       using domain_block.simps by auto
    ultimately show ?thesis by metis 
   next
   case cap
    have "rat_poly.row_length (blockmat ls) = 2 ^ nat (domain_block ls)"
       using Cons by auto
    then have "rat_poly.row_length (blockmat (l#ls)) 
                             = (rat_poly.row_length (brickmat l))
                                *(rat_poly.row_length (blockmat ls))"
       using blockmat.simps  rat_poly.row_length_mat by auto
    moreover have "... = 4*(2 ^ nat (domain_block ls))"
       using rat_poly.row_length_def Cons cap by auto
    moreover have "... = 2^(2 + nat (domain_block ls))"
       using domain_block.simps  by auto
    moreover have "... = 2^(nat (domain l) + nat (domain_block ls))"
       using domain.simps cap by auto 
    moreover have "... = 2^(nat (domain l + domain_block ls))"
      by (simp add: cap domain_block_nonnegative nat_add_distrib)
    moreover have "... = 2^(nat (domain_block (l#ls)))"
       using domain_block.simps by auto
    ultimately show ?thesis by metis
  qed
qed


lemma row_length_domain_block:
 "rat_poly.row_length (blockmat ls) = (2^ (nat ((domain_block ls))))"
proof(induct ls)
 case Nil
  show ?case unfolding blockmat.simps(1) rat_poly.row_length_def by auto
 next
 case (Cons l ls) 
  show ?case
   proof(cases l)
    case vert
     have "rat_poly.row_length (blockmat ls) = 2 ^ nat (domain_block ls)"
          using Cons by auto
     then have "rat_poly.row_length (blockmat (l#ls)) 
                              = (rat_poly.row_length (brickmat l))
                                 *(rat_poly.row_length (blockmat ls))"
          using blockmat.simps  rat_poly.row_length_mat by auto
     moreover have "... = 2*(2 ^ nat (domain_block ls))"
          using rat_poly.row_length_def Cons vert by auto
     moreover have "... = 2^(1 + nat (domain_block ls))"
          using domain_block.simps  by auto
     moreover have "... = 2^(nat (domain l) + nat (domain_block ls))"
          using domain.simps vert by auto 
     moreover have "... = 2^(nat (domain l + domain_block ls))"
          using Suc_eq_plus1_left Suc_nat_eq_nat_zadd1 calculation(4) domain.simps(1) 
                domain_block_non_negative vert
                by metis 
     moreover have "... = 2^(nat (domain_block (l#ls)))"
          using domain_block.simps by auto
     ultimately show ?thesis by metis  
    next
    case over
     have "rat_poly.row_length (blockmat ls) = 2 ^ nat (domain_block ls)"
          using Cons by auto
     then have "rat_poly.row_length (blockmat (l#ls)) 
                      = (rat_poly.row_length (brickmat l))
                         *(rat_poly.row_length (blockmat ls))"
          using blockmat.simps  rat_poly.row_length_mat by auto
     moreover have "... = 4*(2 ^ nat (domain_block ls))"
          using rat_poly.row_length_def Cons over by auto
     moreover have "... = 2^(2 + nat (domain_block ls))"
          using domain_block.simps  by auto
     moreover have "... = 2^(nat (domain l) + nat (domain_block ls))"
          using domain.simps over by auto 
     moreover have "... = 2^(nat (domain l + domain_block ls))"
       by (simp add: over domain_block_nonnegative nat_add_distrib)
     moreover have "... = 2^(nat (domain_block (l#ls)))"
          using domain_block.simps by auto
     ultimately show ?thesis by metis
    next
    case under
     have "rat_poly.row_length (blockmat ls) = 2 ^ nat (domain_block ls)"
          using Cons by auto
     then have "rat_poly.row_length (blockmat (l#ls)) 
                        = (rat_poly.row_length (brickmat l))
                                *(rat_poly.row_length (blockmat ls))"
          using blockmat.simps  rat_poly.row_length_mat by auto
     moreover have "... = 4*(2 ^ nat (domain_block ls))"
          using rat_poly.row_length_def Cons under by auto
     moreover have "... = 2^(2 + nat (domain_block ls))"
          using domain_block.simps  by auto
     moreover have "... = 2^(nat (domain l) + nat (domain_block ls))"
          using domain.simps under by auto 
     moreover have "... = 2^(nat (domain l + domain_block ls))"
       by (simp add: under domain_block_nonnegative nat_add_distrib)
     moreover have "... = 2^(nat (domain_block (l#ls)))"
          using domain_block.simps by auto
     ultimately show ?thesis by metis 
    next
     case cup 
      have "rat_poly.row_length (blockmat ls) = 2 ^ nat (domain_block ls)"
          using Cons by auto
      then have "rat_poly.row_length (blockmat (l#ls)) 
                              = (rat_poly.row_length (brickmat l))
                                   *(rat_poly.row_length (blockmat ls))"
          using blockmat.simps  rat_poly.row_length_mat by auto
      moreover have "... = 1*(2 ^ nat (domain_block ls))"
          using rat_poly.row_length_def Cons cup by auto
      moreover have "... = 2^(0 + nat (domain_block ls))"
          using domain_block.simps  by auto
      moreover have "... = 2^(nat (domain l) + nat (domain_block ls))"
          using domain.simps cup by auto 
      moreover have "... = 2^(nat (domain l + domain_block ls))"
          using nat_sum cup  domain.simps(2) 
                nat_0 plus_int_code(2) plus_nat.add_0  by (metis)
      moreover have "... = 2^(nat (domain_block (l#ls)))"
          using domain_block.simps by auto
      ultimately show ?thesis by metis 
     next
     case cap
      have "rat_poly.row_length (blockmat ls) = 2 ^ nat (domain_block ls)"
          using Cons by auto
      then have "rat_poly.row_length (blockmat (l#ls)) 
                              = (rat_poly.row_length (brickmat l))
                                 *(rat_poly.row_length (blockmat ls))"
          using blockmat.simps  rat_poly.row_length_mat by auto
      moreover have "... = 4*(2 ^ nat (domain_block ls))"
          using rat_poly.row_length_def Cons cap by auto
      moreover have "... = 2^(2 + nat (domain_block ls))"
          using domain_block.simps  by auto
      moreover have "... = 2^(nat (domain l) + nat (domain_block ls))"
          using domain.simps cap by auto 
      moreover have "... = 2^(nat (domain l + domain_block ls))"
        by (simp add: cap domain_block_nonnegative nat_add_distrib)
      moreover have "... = 2^(nat (domain_block (l#ls)))"
          using domain_block.simps by auto
      ultimately show ?thesis by metis
    qed
qed 


lemma length_codomain_block:"length (blockmat ls) 
                                    = (2^ (nat ((codomain_block ls))))"
proof(induct ls)
 case Nil
  show ?case unfolding blockmat.simps(1) rat_poly.row_length_def by auto
 next
 case (Cons l ls) 
  show ?case
   proof(cases l)
    case vert
     have "length (blockmat ls) = 2 ^ nat (codomain_block ls)"
          using Cons by auto
     then have "length (blockmat (l#ls)) 
                              = (length (brickmat l))*(length (blockmat ls))"
          using blockmat.simps rat_poly.length_Tensor by auto  
     moreover have "... = 2*(2 ^ nat (codomain_block ls))"
          using  Cons vert by auto
     moreover have "... = 2^(1 + nat (codomain_block ls))"
          by auto
     moreover have "... = 2^(nat (codomain l) + nat (codomain_block ls))"
          using codomain.simps vert by auto 
     moreover have "... = 2^(nat (codomain l + codomain_block ls))"
          using nat_sum  Suc_eq_plus1_left Suc_nat_eq_nat_zadd1 
               codomain.simps(1)  codomain_block_nonnegative nat_numeral 
               numeral_One vert  by (metis)  
     moreover have "... = 2^(nat (codomain_block (l#ls)))"
          by auto
     ultimately show ?thesis by metis  
    next
    case over
     have "length (blockmat ls) = 2 ^ nat (codomain_block ls)"
          using Cons by auto
     then have "length (blockmat (l#ls)) 
                              = (length (brickmat l))*(length (blockmat ls))"
          using blockmat.simps rat_poly.length_Tensor by auto  
     moreover have "... = 4*(2 ^ nat (codomain_block ls))"
          using  Cons over by auto
     moreover have "... = 2^(2 + nat (codomain_block ls))"
          by auto
     moreover have "... = 2^(nat (codomain l) + nat (codomain_block ls))"
          using codomain.simps over by auto 
     moreover have "... = 2^(nat (codomain l + codomain_block ls))"
          using nat_sum  over codomain.simps codomain_block_nonnegative 
          by auto  
     moreover have "... = 2^(nat (codomain_block (l#ls)))"
          by auto
     ultimately show ?thesis by metis 
    next
    case under 
     have "length (blockmat ls) = 2 ^ nat (codomain_block ls)"
          using Cons by auto
     then have "length (blockmat (l#ls)) 
                              = (length (brickmat l))*(length (blockmat ls))"
          using blockmat.simps rat_poly.length_Tensor by auto  
     moreover have "... = 4*(2 ^ nat (codomain_block ls))"
          using  Cons under by auto
     moreover have "... = 2^(2 + nat (codomain_block ls))"
          by auto
     moreover have "... = 2^(nat (codomain l) + nat (codomain_block ls))"
          using codomain.simps under by auto 
     moreover have "... = 2^(nat (codomain l + codomain_block ls))"
          using nat_sum  under codomain.simps codomain_block_nonnegative 
          by auto  
     moreover have "... = 2^(nat (codomain_block (l#ls)))"
          by auto
     ultimately show ?thesis by metis 
    next
    case cup
     have "length (blockmat ls) = 2 ^ nat (codomain_block ls)"
          using Cons by auto
     then have "length (blockmat (l#ls)) 
                              = (length (brickmat l))*(length (blockmat ls))"
          using blockmat.simps rat_poly.length_Tensor by auto  
     moreover have "... = 4*(2 ^ nat (codomain_block ls))"
           using  Cons cup by auto
     moreover have "... = 2^(2 + nat (codomain_block ls))"
           by auto
     moreover have "... = 2^(nat (codomain l) + nat (codomain_block ls))"
           using codomain.simps cup by auto 
     moreover have "... = 2^(nat (codomain l + codomain_block ls))"
           using nat_sum  cup codomain.simps 
                 codomain_block_nonnegative 
           by auto  
     moreover have "... = 2^(nat (codomain_block (l#ls)))"
           by auto
     ultimately show ?thesis by metis 
    next
    case cap
     have "length (blockmat ls) = 2 ^ nat (codomain_block ls)"
           using Cons by auto
     then have "length (blockmat (l#ls)) 
                              = (length (brickmat l))*(length (blockmat ls))"
           using blockmat.simps rat_poly.length_Tensor by auto  
     moreover have "... = 1*(2 ^ nat (codomain_block ls))"
           using  Cons cap by auto
     moreover have "... = 2^(0 + nat (codomain_block ls))"
           by auto
     moreover have "... = 2^(nat (codomain l) + nat (codomain_block ls))"
           using codomain.simps cap by auto 
     moreover have "... = 2^(nat (codomain l + codomain_block ls))"
           using nat_sum cap codomain.simps codomain_block_nonnegative 
           by auto  
     moreover have "... = 2^(nat (codomain_block (l#ls)))"
           by auto
     ultimately show ?thesis by metis 
   qed
qed


lemma matrix_blockmat:
 "mat 
      (rat_poly.row_length (blockmat ls)) 
      (length (blockmat ls))  
                    (blockmat ls)"
 proof(induct ls) 
 case Nil 
  show ?case 
        using Nil 
        unfolding blockmat.simps(1) rat_poly.row_length_def mat_def 
        vec_def Ball_def by auto
 next
 case (Cons a ls)
  have Cons_1:"mat 
                 (rat_poly.row_length (blockmat ls)) 
                 (length (blockmat ls)) 
                                   (blockmat ls)"
        using Cons by auto
  have Cons_2:"(blockmat (a#ls)) = (brickmat a)\<otimes>(blockmat ls)"
        using blockmat.simps by auto
  moreover have "rat_poly.row_length (blockmat (a#ls)) 
                        = (rat_poly.row_length (brickmat a))
                                 *(rat_poly.row_length (blockmat ls))"  
        using calculation rat_poly.row_length_mat by (metis)        
  moreover have "length (blockmat (a#ls)) 
                             = (length (brickmat a))
                                      *(length (blockmat ls))" 
        using  blockmat.simps(2) rat_poly.length_Tensor by (metis)
  ultimately have Cons_3:"mat 
                            (rat_poly.row_length (brickmat a)) 
                            (length (brickmat a)) 
                                         (brickmat a)
                      \<Longrightarrow> ?case"
        using rat_poly.well_defined_Tensor Cons by auto
  then show ?case
  proof(cases a)
   case vert
    have "mat 
                (rat_poly.row_length (brickmat a)) 
                (length (brickmat a)) 
                    (brickmat a)"
        using vert_dim mat_vert rat_poly.matrix_row_length vert 
        by metis
    thus ?thesis using Cons_3 by auto
   next
   case over
    have "mat 
              (rat_poly.row_length (brickmat a)) 
              (length (brickmat a)) 
                         (brickmat a)"
        using mat_over rat_poly.matrix_row_length over 
        by metis
    thus ?thesis using Cons_3 by auto    
   next
   case under
    have "mat 
              (rat_poly.row_length (brickmat a)) 
              (length (brickmat a)) 
                         (brickmat a)"
        using  mat_under rat_poly.matrix_row_length under by metis
    thus ?thesis using Cons_3 by auto 
   next
   case cap
    have "mat 
              (rat_poly.row_length (brickmat a)) 
              (length (brickmat a)) 
                            (brickmat a)"
        using  mat_cap rat_poly.matrix_row_length cap by metis
    thus ?thesis using Cons_3 by auto
   next
   case cup
    have "mat 
             (rat_poly.row_length (brickmat a)) 
             (length (brickmat a)) 
                            (brickmat a)"
        using mat_cup rat_poly.matrix_row_length cup by metis
    thus ?thesis using Cons_3 by auto
  qed
qed


text\<open>The function kauff$\_$mat below associates every wall to a matrix. 
 We call this the kauffman matrix. When the wall represents a well defined
 tangle diagram, the Kauffman matrix is a 1 $\times$  1 matrix whose entry is the
 Kauffman bracket.\<close>       

primrec kauff_mat::"wall \<Rightarrow> rat_poly mat"
where 
"kauff_mat (basic w) = (blockmat w)"
|"kauff_mat (w*ws) = rat_poly.matrix_mult (blockmat w) (kauff_mat ws)"

text\<open>The following theorem tells us  that if a wall
represents a tangle diagram, then its Kauffman matrix is a `valid' matrix.\<close>
theorem matrix_kauff_mat:
"((is_tangle_diagram ws) 
 \<Longrightarrow> (rat_poly.row_length (kauff_mat ws)) = 2^(nat (domain_wall ws))
 \<and> (length (kauff_mat ws)) = 2^(nat (codomain_wall ws))
 \<and> (mat 
        (rat_poly.row_length (kauff_mat ws)) 
        (length (kauff_mat ws)) 
            (kauff_mat ws)))"
proof(induct ws)
 case (basic w)
  show ?case 
       using kauff_mat.simps(1) domain_wall.simps(1) 
             row_length_domain_block matrix_blockmat
             length_codomain_block basic by auto
 next
 case (prod w ws)
  have "is_tangle_diagram (w*ws)"
       using prod by auto
  moreover have prod_1:"is_tangle_diagram ws"
       using is_tangle_diagram.simps  prod.prems by metis
  ultimately have prod_2:"(codomain_block w) = domain_wall ws"
       using is_tangle_diagram.simps by auto
  from prod_1 have prod_3:
         "mat 
              (rat_poly.row_length (kauff_mat ws)) 
              (length (kauff_mat ws)) 
                           (kauff_mat ws)"
       using prod.hyps by auto 
  moreover have "(rat_poly.row_length (kauff_mat ws)) 
                                =  2^(nat (domain_wall ws))"
       using prod.hyps prod_1 by auto
  moreover have prod_4:"length (kauff_mat ws) 
                                = 2^(nat (codomain_wall ws))"
       using prod.hyps prod_1 by auto
  moreover have prod_5:
           "mat 
               (rat_poly.row_length (blockmat w)) 
               (length (blockmat w)) 
                            (blockmat w)"
       using matrix_blockmat by auto
  moreover have prod_6:
           "rat_poly.row_length (blockmat w) 
                             = 2^(nat (domain_block w))"
              and "length (blockmat w) = 2^(nat (codomain_block w))"
       using row_length_domain_block length_codomain_block 
       by auto
  ultimately have ad1:"length (blockmat w) 
                             = rat_poly.row_length (kauff_mat ws)"
       using prod_2 by auto
  then have "mat 
                 (rat_poly.row_length (blockmat w)) 
                 (length (kauff_mat ws)) 
                      (rat_poly.matrix_mult (blockmat w) (kauff_mat ws))"
       using prod_3 prod_5 mat_mult by auto 
  then have res1:"mat 
                     (rat_poly.row_length (blockmat w)) 
                     (length (kauff_mat ws)) 
                               (kauff_mat (w*ws))"
                 using kauff_mat.simps(2) by auto
  then have "rat_poly.row_length (kauff_mat (w*ws)) 
                               = (rat_poly.row_length (blockmat w))"
       using ad1 length_0_conv rat_poly.mat_empty_column_length 
             rat_poly.matrix_row_length rat_poly.row_length_def 
             rat_poly.unique_row_col(1) by (metis)
  moreover have "...  = 2^(nat (domain_wall (w*ws)))"
       using prod_6 domain_wall.simps by auto
  ultimately have res2:
                 "rat_poly.row_length (kauff_mat (w*ws)) 
                       = 2^(nat (domain_wall (w*ws)))"
       by auto
  have "length (kauff_mat (w*ws)) = length (kauff_mat ws)"
       using res1  rat_poly.mat_empty_column_length 
           rat_poly.matrix_row_length rat_poly.unique_row_col(2)
       by metis
  moreover have "... = 2^(nat (codomain_wall (w*ws)))"
       using prod_4 codomain_wall.simps(2) by auto
  ultimately have res3:"length (kauff_mat (w*ws))  
                               =  2^(nat (codomain_wall (w*ws)))"
       by auto
  with res1 res2 show ?case
    using  \<open>length (kauff_mat ws) = 2 ^ nat (codomain_wall (w * ws))\<close> 
           \<open>rat_poly.row_length (blockmat w) = 2 ^ nat (domain_wall (w * ws))\<close> 
       by (metis)
qed


theorem effective_matrix_kauff_mat:
 assumes "is_tangle_diagram ws" 
 shows "(rat_poly.row_length (kauff_mat ws)) = 2^(nat (domain_wall ws))"
 and "length (kauff_mat ws) = 2^(nat (codomain_wall ws))"
 and "mat (rat_poly.row_length (kauff_mat ws)) (length (kauff_mat ws))
                                           (kauff_mat ws) "
 apply (auto simp add:matrix_kauff_mat assms )
 using assms matrix_kauff_mat by metis

lemma mat_mult_equiv:
 "rat_poly.matrix_mult m1 m2 = mat_mult (rat_poly.row_length m1) m1 m2"
 by auto

theorem associative_rat_poly_mat:
 assumes "mat (rat_poly.row_length m1) (rat_poly.row_length m2) m1" 
     and "mat (rat_poly.row_length m2) (rat_poly.row_length m3) m2" 
     and "mat (rat_poly.row_length m3) nc m3"
 shows "rat_poly.matrix_mult m1 (rat_poly.matrix_mult m2 m3) 
                     = rat_poly.matrix_mult (rat_poly.matrix_mult m1  m2) m3"
proof-
 have "(rat_poly.matrix_mult m2 m3) 
                   = mat_mult (rat_poly.row_length m2) m2 m3"
      using mat_mult_equiv by auto  
 then have "rat_poly.matrix_mult m1 (rat_poly.matrix_mult m2 m3)
                   = mat_mult (rat_poly.row_length m1)  m1 
                                 (mat_mult (rat_poly.row_length m2) m2 m3)"
      using mat_mult_equiv by auto  
 moreover have "...  =    mat_mult (rat_poly.row_length m1) 
                           (mat_mult (rat_poly.row_length m1) m1 m2) m3"
      using assms mat_mult_assoc by metis 
 moreover have "... = rat_poly.matrix_mult (rat_poly.matrix_mult m1 m2) m3"
 proof-
  have "mat 
           (rat_poly.row_length m1) 
           (rat_poly.row_length m3) 
                     (rat_poly.matrix_mult m1 m2)"
      using assms(1) assms(2) mat_mult by (metis)
  then have "rat_poly.row_length (rat_poly.matrix_mult m1 m2) = 
                     (rat_poly.row_length m1)"
      using assms(1) assms(2) length_0_conv rat_poly.mat_empty_column_length 
            rat_poly.matrix_row_length rat_poly.row_length_Nil 
            rat_poly.unique_row_col(1) rat_poly.unique_row_col(2)   
        by (metis)    
  moreover have "rat_poly.matrix_mult (rat_poly.matrix_mult m1 m2) m3
                       = mat_mult (rat_poly.row_length 
                                      (rat_poly.matrix_mult m1 m2))
                                   (rat_poly.matrix_mult m1 m2) m3"
      using mat_mult_equiv by auto
  then  show ?thesis using mat_mult_equiv by (metis calculation)
 qed
 ultimately show ?thesis by auto
qed

text\<open>It follows from this result that the Kauffman Matrix of a wall representing a link
diagram, is a 1 $\times$ 1 matrix. 
 Thus it establishes a correspondence between links and
rational functions.\<close>

theorem link_diagram_matrix:
 assumes "is_link_diagram ws"
 shows "mat 1 1 (kauff_mat ws) "
 using assms effective_matrix_kauff_mat  unfolding is_link_diagram_def  
 by (metis Preliminaries.abs_zero abs_non_negative_sum(1) comm_monoid_add_class.add_0 nat_0 power_0)

theorem tangle_compose_matrix:
"((is_tangle_diagram ws1) \<and> (is_tangle_diagram ws2) 
\<and>(domain_wall ws2 = codomain_wall ws1)) \<Longrightarrow>
kauff_mat (ws1 \<circ> ws2) = rat_poly.matrix_mult (kauff_mat ws1) (kauff_mat ws2)"
proof(induct ws1)
 case (basic w1)
  have "(basic w1) \<circ> (ws2) = (w1)*(ws2)"
        using compose.simps by auto
  moreover have "kauff_mat ((basic w1) \<circ> ws2) =rat_poly.matrix_mult (blockmat w1) (kauff_mat ws2)" 
        using kauff_mat.simps(2) by auto
  then show ?case using kauff_mat.simps(1) by auto
 next
 case (prod w1 ws1)
  have 1:"is_tangle_diagram (w1*ws1)"
        using prod.prems by (rule conjE)
  then have 2:"(is_tangle_diagram ws1) 
                 \<and> (codomain_block w1 = domain_wall ws1)"
        using is_tangle_diagram.simps(2) by metis
  then have 
       "mat (2^(nat (domain_wall ws1))) (2^(nat (codomain_wall ws1))) (kauff_mat ws1)"
            and "mat (2^(nat (domain_block w1))) (2^(nat (codomain_block w1))) (blockmat w1)"
        using  effective_matrix_kauff_mat   matrix_blockmat  length_codomain_block 
               row_length_domain_block
        by (auto) (metis) 
   with 2 have 3:"mat 
                     (rat_poly.row_length (blockmat w1)) 
                     (2^(nat (domain_wall ws1)))
                               (blockmat w1)"
         and   "mat 
                   (2^(nat (domain_wall ws1))) 
                   (2^(nat (domain_wall ws2))) 
                               (kauff_mat ws1)"
         and "(2^(nat (domain_wall ws1))) 
                           = (rat_poly.row_length (kauff_mat ws1))"
         using  effective_matrix_kauff_mat prod.prems matrix_blockmat 
                row_length_domain_block by auto
  then have "mat 
                  (rat_poly.row_length (blockmat w1)) 
                  (rat_poly.row_length (kauff_mat ws1)) 
                       (blockmat w1)"
         and   "mat 
                 (rat_poly.row_length (kauff_mat ws1)) 
                 (2^(nat (domain_wall ws2))) 
                       (kauff_mat ws1)"
         by auto   
  moreover have "mat 
                     (2^(nat (domain_wall ws2))) 
                      (2^(nat (codomain_wall ws2))) 
                            (kauff_mat ws2)"
           and "(2^(nat (domain_wall ws2))) 
                    = rat_poly.row_length (kauff_mat ws2)"
         using prod.prems  effective_matrix_kauff_mat 
              effective_matrix_kauff_mat  
         by (auto) (metis prod.prems)
  ultimately have "mat 
                     (rat_poly.row_length (blockmat w1))
                     (rat_poly.row_length (kauff_mat ws1)) 
                               (blockmat w1)" 
             and  "mat 
                     (rat_poly.row_length (kauff_mat ws1)) 
                     (rat_poly.row_length (kauff_mat ws2))
                               (kauff_mat ws1)"
              and "mat 
                      (rat_poly.row_length (kauff_mat ws2)) 
                      (2^(nat (codomain_wall ws2))) 
                               (kauff_mat ws2)"
         by auto
  with 3 have "rat_poly.matrix_mult 
                         (blockmat w1) 
                          (rat_poly.matrix_mult (kauff_mat ws1) 
                                      (kauff_mat ws2))
                      = rat_poly.matrix_mult 
                             (rat_poly.matrix_mult 
                                     (blockmat w1)  
                                     (kauff_mat ws1)) 
                                           (kauff_mat ws2)"
         using associative_rat_poly_mat by auto
  then show ?case 
         using  "2" codomain_wall.simps(2) compose_Cons 
         prod.hyps prod.prems kauff_mat.simps(2) by (metis)     
qed

theorem left_mat_compose:
 assumes "is_tangle_diagram ws" 
     and "codomain_wall ws = 0"
 shows "kauff_mat ws = (kauff_mat (ws  \<circ> (basic [])))"
proof-
 have "mat (rat_poly.row_length (kauff_mat ws)) 1 (kauff_mat ws)"
      using effective_matrix_kauff_mat assms  nat_0 power_0  by metis
 moreover have "(kauff_mat (basic [])) = mat1 1"
      using kauff_mat.simps(1) blockmat.simps(1) mat1_equiv by auto
 moreover then have 1:"(kauff_mat (ws  \<circ> (basic []))) 
                              = rat_poly.matrix_mult 
                                          (kauff_mat ws) 
                                          (kauff_mat (basic []))"
      using tangle_compose_matrix assms is_tangle_diagram.simps by auto
 ultimately have "rat_poly.matrix_mult (kauff_mat ws) (kauff_mat (basic []))
                             = (kauff_mat ws)"
      using mat_mult_equiv mat1_mult_right by auto
 then show ?thesis using 1 by auto
qed 


theorem right_mat_compose:
 assumes "is_tangle_diagram ws" and "domain_wall ws = 0"
         shows "kauff_mat ws = (kauff_mat ((basic []) \<circ>ws))"
proof-
 have "mat 1 (length (kauff_mat ws)) (kauff_mat ws)"
       using effective_matrix_kauff_mat assms  nat_0 power_0  by metis
 moreover have "(kauff_mat (basic [])) = mat1 1"
       using kauff_mat.simps(1) blockmat.simps(1) mat1_equiv by auto
 moreover then have 1:"(kauff_mat ((basic []) \<circ>ws))
                              = rat_poly.matrix_mult 
                                           (kauff_mat (basic [])) 
                                           (kauff_mat ws) "
       using tangle_compose_matrix assms is_tangle_diagram.simps by auto
 ultimately have "rat_poly.matrix_mult (kauff_mat (basic [])) (kauff_mat ws) 
                             = (kauff_mat ws)"
       using effective_matrix_kauff_mat(3) is_tangle_diagram.simps(1) 
              mat1 mat1_mult_left one_neq_zero rat_poly.mat_empty_column_length 
              rat_poly.unique_row_col(1)
       by metis
 then show ?thesis using 1 by auto
qed 

lemma left_id_blockmat:"blockmat [] \<otimes> blockmat b = blockmat b"
 unfolding blockmat.simps(1) rat_poly.Tensor_left_id by auto 


lemma tens_assoc:
 "\<forall>a xs ys.(brickmat a \<otimes> (blockmat xs \<otimes> blockmat ys) 
                   = (brickmat a \<otimes> blockmat xs) \<otimes> blockmat ys)" 
proof-
 have "\<forall>a.(mat 
               (rat_poly.row_length (brickmat a)) 
               (length (brickmat a)) 
                         (brickmat a))"
      using brickmat.simps 
      unfolding mat_def rat_poly.row_length_def Ball_def vec_def 
      apply(auto)
      by (case_tac a) (auto)
 moreover have "\<forall>xs. (mat 
                           (rat_poly.row_length (blockmat xs)) 
                           (length (blockmat xs)) 
                                       (blockmat xs))"
      using matrix_blockmat by auto
 moreover have "\<forall>ys. mat 
                          (rat_poly.row_length (blockmat ys)) 
                          (length (blockmat ys)) 
                                        (blockmat ys)"
      using matrix_blockmat by auto
 ultimately show ?thesis using rat_poly.associativity by auto
qed

lemma kauff_mat_tensor_distrib:
"\<forall>xs.\<forall>ys.(kauff_mat (basic xs \<otimes> basic ys) 
 = kauff_mat (basic xs) \<otimes> kauff_mat (basic ys))"
 apply(rule allI)
 apply (rule allI)
 apply (induct_tac xs)
 apply(auto)
 apply (metis rat_poly.vec_mat_Tensor_vector_id)
 apply (simp add:tens_assoc)
 done

lemma blockmat_tensor_distrib:
 "(blockmat (a \<otimes> b)) = (blockmat a) \<otimes> (blockmat b)"
proof-
 have "blockmat (a \<otimes> b) = kauff_mat (basic (a \<otimes> b))"
       using kauff_mat.simps(1) by auto
 moreover have "... = kauff_mat (basic a) \<otimes> kauff_mat (basic b)"
       using kauff_mat_tensor_distrib by auto
 moreover have "... = (blockmat a) \<otimes> (blockmat b)"
       using kauff_mat.simps(1) by auto
 ultimately show ?thesis by auto
qed  

lemma blockmat_non_empty:"\<forall>bs.(blockmat bs \<noteq> [])"
 apply(rule allI)
 apply(induct_tac bs)
 apply(auto)
 apply(case_tac a)
 apply(auto)
 apply (metis length_0_conv rat_poly.vec_mat_Tensor_length)
 apply (metis length_0_conv rat_poly.vec_mat_Tensor_length)
 apply (metis length_0_conv rat_poly.vec_mat_Tensor_length)
 apply (metis length_0_conv rat_poly.vec_mat_Tensor_length)
 apply (metis length_0_conv rat_poly.vec_mat_Tensor_length)
 done

text\<open>The kauffman matrix of a wall representing a tangle diagram is 
         non empty\<close>
lemma  kauff_mat_non_empty:
 fixes ws
 assumes "is_tangle_diagram ws"
 shows "kauff_mat ws \<noteq> []"
proof-
 have "(length (kauff_mat ws) =  2^(nat (codomain_wall ws)))"
      using effective_matrix_kauff_mat assms by auto
 then have "(length (kauff_mat ws)) \<ge> 1"
      by auto
 then show ?thesis by auto
qed


lemma is_tangle_diagram_length_rowlength:
 assumes "is_tangle_diagram (w*ws)"
 shows "length (blockmat w) = rat_poly.row_length (kauff_mat ws)"
proof-
 have "(codomain_block w = domain_wall ws)"
      using assms is_tangle_diagram.simps by metis
 moreover have "rat_poly.row_length (kauff_mat ws) 
                                = 2^(nat (domain_wall ws))"
      using effective_matrix_kauff_mat by (metis assms is_tangle_diagram.simps(2))
 moreover have "length (blockmat w) 
                                = 2^(nat (codomain_block w))"
      using matrix_blockmat length_codomain_block by auto
 ultimately show ?thesis by auto
qed

lemma is_tangle_diagram_matrix_match:
 assumes "is_tangle_diagram (w1*ws1)"
    and "is_tangle_diagram (w2*ws2)"
 shows "rat_poly.matrix_match (blockmat w1) 
                      (kauff_mat ws1) (blockmat w2) (kauff_mat ws2)"
 unfolding rat_poly.matrix_match_def
 apply(auto)
 proof-
   show "mat (rat_poly.row_length (blockmat w1)) (length (blockmat w1)) (blockmat w1)"
       using matrix_blockmat by auto
  next
   have "is_tangle_diagram ws1"
       using assms(1) is_tangle_diagram.simps(2) by metis
   then show "mat (rat_poly.row_length (kauff_mat ws1)) (length (kauff_mat ws1)) (kauff_mat ws1)"
       using matrix_kauff_mat by metis
  next
   show "mat (rat_poly.row_length (blockmat w2)) (length (blockmat w2)) (blockmat w2)"
       using matrix_blockmat by auto
  next
   have "is_tangle_diagram ws2"
       using assms(2) is_tangle_diagram.simps(2) by metis
   then show "mat (rat_poly.row_length (kauff_mat ws2)) (length (kauff_mat ws2)) (kauff_mat ws2)"
       using matrix_kauff_mat by metis
  next
   show "length (blockmat w1) = rat_poly.row_length (kauff_mat ws1)"
       using is_tangle_diagram_length_rowlength assms(1) by auto
  next
   show  "length (blockmat w2) = rat_poly.row_length (kauff_mat ws2)"
       using is_tangle_diagram_length_rowlength assms(2) by auto   
  next
    assume 0:"blockmat w1 = [] "
    show False using 0
       by (metis blockmat_non_empty)
  next
    assume 1:"kauff_mat ws1 = [] "
    have "is_tangle_diagram ws1"
          using assms(1) is_tangle_diagram.simps(2) by metis
    then show False using 1 kauff_mat_non_empty by auto
  next
    assume 0:"blockmat w2 = [] "
    show False using 0
           by (metis blockmat_non_empty)
  next
    assume 1:"kauff_mat ws2 = [] "
    have "is_tangle_diagram ws2"
          using assms(2) is_tangle_diagram.simps(2) by metis
    then show False using 1 kauff_mat_non_empty by auto   
 qed


text\<open>The following function constructs a $2^n \times 2^n$ identity matrix
 for a given $n$\<close>

primrec make_vert_equiv::"nat \<Rightarrow> rat_poly mat"
where
"make_vert_equiv 0 = [[1]]"
|"make_vert_equiv (Suc k) = ((mat1 2)\<otimes>(make_vert_equiv k))"

lemma mve1:"make_vert_equiv 1 = (mat1 2)"
 using make_vert_equiv.simps brickmat.simps(1) 
       One_nat_def rat_poly.Tensor_right_id
 by (metis)

lemma
assumes "i<2" and "j<2"
shows "(make_vert_equiv 1)!i!j  = (if i = j then 1 else 0)"
 apply(simp add:mve1)
 apply(simp add:rat_poly.Tensor_right_id)
 using make_vert_equiv.simps mat1_index assms  by (metis)

lemma mat1_vert_equiv:"(mat1 2) = (brickmat vert)" (is "?l = ?r")
proof-
 have "?r = [[1,0],[0,1]]"
    using brickmat.simps by auto
 then have "rat_poly.row_length ?r = 2" and "length ?r = 2"
    using rat_poly.row_length_def by auto
 moreover then have 1:"mat 2 2 ?r"
    using mat_vert by metis
 ultimately have 2:"(\<forall> i < 2. \<forall> j < 2.  
                               ((?r) ! i ! j = (if i = j then 1 else 0)))"
 proof-
  have 1:"(?r ! 0! 0) = 1"
    by auto
  moreover have 2:"(?r ! 0! 1) = 0"
    by auto
  moreover have 3:"(?r ! 1! 0) = 0"
    by auto
  moreover have 5:"(?r ! 1! 1) = 1"
    by auto
  ultimately show ?thesis
    by (auto dest!: less_2_cases)
 qed
 have 3:"mat 2 2 (mat1 2)"
    by (metis mat1)
 have 4:"(\<forall> i < 2. \<forall> j < 2.  ((?l) ! i ! j = (if i = j then 1 else 0)))"
    by (metis mat1_index)
 then have "(\<forall> i < 2. \<forall> j < 2.  ((?l) ! i ! j = (?r !i !j)))"
    using 2 by auto
 with 1  3 have "?l = ?r"
    by (metis mat_eqI)
 then show ?thesis by auto
qed 

lemma blockmat_make_vert:
 "blockmat (make_vert_block n) = (make_vert_equiv n)"
 apply(induction n)
 apply(simp)
 unfolding make_vert_block.simps blockmat.simps make_vert_equiv.simps 
 using mat1_vert_equiv by auto

lemma prop_make_vert_equiv:
 shows "rat_poly.row_length (make_vert_equiv n) = 2^n"
   and "length (make_vert_equiv n) = 2^n"
   and "mat 
         (rat_poly.row_length (make_vert_equiv n)) 
         (length (make_vert_equiv n)) 
                       (make_vert_equiv n)" 
proof-
 have 1:"make_vert_equiv n = (blockmat (make_vert_block n))"
        using blockmat_make_vert  by auto 
 moreover have 2:"domain_block (make_vert_block n) = int n"
        using domain_make_vert by auto
 moreover have 3:"codomain_block (make_vert_block n) = int n"
        using codomain_make_vert by auto
 ultimately show "rat_poly.row_length (make_vert_equiv n) = 2^n" 
             and "length (make_vert_equiv n) = 2^n"
             and "mat 
                     (rat_poly.row_length (make_vert_equiv n)) 
                     (length (make_vert_equiv n)) 
                               (make_vert_equiv n)"
            apply (metis nat_int row_length_domain_block)
            using 1 2 3 apply (metis length_codomain_block nat_int)
            using 1 2 3 by (metis matrix_blockmat)
qed

abbreviation nat_mult::"nat \<Rightarrow> nat \<Rightarrow> nat"   (infixl "*n" 65)
where
"nat_mult a b \<equiv> ((a::nat)*b)"

lemma equal_div_mod:assumes "((j::nat) div a) = (i div a)"
            and "(j mod a) = (i mod a)"
        shows "j = i"
proof-
 have "j = a*(j div a) + (j mod a)"
       by auto
 then have "j = a*(i div a) + (i mod a)"
       using assms by auto
 then show ?thesis by auto
qed

lemma equal_div_mod2:"(((j::nat) div a)  = (i div a)
                      \<and> ((j mod a) = (i mod a))) = (j = i)"
 using equal_div_mod by metis

lemma impl_rule:
 assumes "(\<forall>i < m.\<forall>j < n. (P i) \<and> (Q j))" 
           and "\<forall> i j.(P i) \<and> (Q j) \<longrightarrow> R i j"
 shows  "(\<forall>i < m.\<forall>j < n. R i j)"
 using assms  by metis 

lemma implic:
 assumes "\<forall>i j.((P i j) \<longrightarrow> (Q i j))"
        and "\<forall>i j.((Q i j) \<longrightarrow> (R i j))"  
 shows "\<forall>i j.((P i j) \<longrightarrow> (R i j))"
 using assms by auto

lemma assumes "a < (b*c)"
      shows "((a::nat) div b) < c"
 using assms by (metis rat_poly.div_right_ineq)

lemma mult_if_then:"((v = (if P then 1 else 0)) 
                    \<and> (w = (if Q then 1 else 0)))
                       \<Longrightarrow> (rat_poly_times v w = (if (P\<and>Q) then 1 else 0))"
 by auto

lemma rat_poly_unity:"rat_poly_times 1 1 = 1"
 by auto

lemma "((P \<and> Q) \<longrightarrow> R) \<Longrightarrow> (P \<longrightarrow> Q  \<longrightarrow> R)"
 by auto
lemma "length (mat1 2) = 2"
 apply(simp add:mat1I_def)
 done

theorem make_vert_equiv_mat:
"make_vert_equiv n = (mat1 (2^n))"
proof(induction n)
 case 0
  show ?case using 0 mat1_equiv by auto 
 next
 case (Suc k)
  have 1:"make_vert_equiv k = mat1 (2 ^ k)"
          using Suc by auto
  moreover then have "make_vert_equiv (k+1) = (mat1 2)\<otimes>(mat1 (2^k))"
          using make_vert_equiv.simps(2) by auto
  then have "(mat1 2) \<otimes> (mat1 (2^k)) = mat1 (2^(k+1))"
  proof-
   have 1:"mat (2^(k+1)) (2^(k+1)) (mat1 (2^(k+1)))"
          using mat1 by auto
   have 2:"(\<forall> i < 2^(k+1). \<forall> j <2^(k+1). 
                  (mat1 (2^(k+1)) ! i ! j = (if i = j then 1 else 0)))"
          by (metis mat1_index)   
   have 3:"rat_poly.row_length (mat1 2) = 2"                               
         by (metis mat1_vert_equiv vert_dim)
   have 4:"length (mat1 2) = 2"
         by (simp add:mat1I_def)
   then have 5:"mat 
                      (rat_poly.row_length (mat1 2)) 
                      (length (mat1 2)) 
                                (mat1 2)"
        by (metis "4" mat1 mat1_vert_equiv vert_dim)
   moreover have 6:"rat_poly.row_length (mat1 (2^k)) = 2^k"
           and 7:"length ((mat1 (2^k))) = 2^k"
       using Suc 
       by (metis prop_make_vert_equiv(1)) (simp add:mat1I_def) 
       
   then have 8:"mat 
                         (rat_poly.row_length (mat1 (2^k))) 
                         (length (mat1 (2^k))) 
                              (mat1 (2^k))" 
      using Suc  mat1 by (metis) 
   then have 9:
           "(\<forall>i <(2^(k+1)). \<forall>j < (2^(k+1)).
               ((rat_poly.Tensor (mat1 2)  (mat1 (2^k))!j!i) 
                 =  rat_poly_times
                       ((mat1 2)!(j div (length (mat1 (2^k))))
                                !(i div (rat_poly.row_length (mat1 (2^k))))) 
                     ((mat1 (2^k))!(j mod length (mat1 (2^k)))
                              !(i mod (rat_poly.row_length (mat1 (2^k)))))))"
   proof-
    have "(\<forall>i <((rat_poly.row_length (mat1 2))
                                 *n (rat_poly.row_length (mat1 (2^k)))).
               \<forall>j < ((length (mat1 2))
                       *n (length (mat1 (2^k)))).
                   ((rat_poly.Tensor (mat1 2)  (mat1 (2^k))!j!i) 
            =  rat_poly_times
                ((mat1 2)!(j div (length (mat1 (2^k))))
                         !(i div (rat_poly.row_length (mat1 (2^k))))) 
                ((mat1 (2^k))!(j mod length (mat1 (2^k)))
                         !(i mod (rat_poly.row_length (mat1 (2^k)))))))"
                  using 5 8 rat_poly.effective_matrix_Tensor_elements2 
                  by (metis "3" "4" "6" "7" rat_poly.comm)
    moreover have "(rat_poly.row_length (mat1 2))
                           *n(rat_poly.row_length (mat1 (2^k))) 
                                       = 2^(k+1)"  
                  using 3 6 by auto
    moreover have "(length (mat1 2))
                           *n(length (mat1 (2^k))) 
                                       = 2^(k+1)" 
                  using 4 7 by (metis "3" "6" calculation(2))
    ultimately show ?thesis by metis
   qed
   have 10:"\<forall>i j.((i div (rat_poly.row_length (mat1 (2^k))) < 2)
                    \<and>(j div length (mat1 (2^k)) < 2)
                  \<longrightarrow> (((mat1 2)!(j div (length (mat1 (2^k))))
                                !(i div (rat_poly.row_length (mat1 (2^k))))) 
                      = (if 
                          ((j div (length (mat1 (2^k)))) 
                              = (i div (rat_poly.row_length (mat1 (2^k)))))
                         then 1 
                     else 0)))"
                  using mat1_index by (metis "6" "7")
   have 11:"\<forall>j.(j < (2^(k+1)) \<longrightarrow> j div (length (mat1 (2^k))) < 2)"
   proof-
    have "2^(k+1) = (2 *n (2^k))"
                 by auto
    then show ?thesis 
                    using 7 allI  Suc.IH prop_make_vert_equiv(1) 
                    rat_poly.div_left_ineq by (metis)
    qed
   moreover have 12:
                "\<forall>i.(i < (2^(k+1)) 
                      \<longrightarrow> (i div (rat_poly.row_length (mat1 (2^k)))) < 2)"
   proof-
    have "2^(k+1) = (2 *n (2^k))"
                 by auto
    then show ?thesis  using 7 allI by (metis Suc.IH prop_make_vert_equiv(1) rat_poly.div_left_ineq)
    qed     
   ultimately have 13:
                "\<forall>i j.((i < (2^(k+1)))\<and> j < (2^(k+1)) \<longrightarrow>
                         ((i div (rat_poly.row_length (mat1 (2^k)))) < 2)
                          \<and>((j div (length (mat1 (2^k)))) < 2))"
    by auto               
   have 14:"\<forall>i j.(i < (2^(k+1)))\<and> (j < (2^(k+1))) \<longrightarrow>
                  (((mat1 2)
                     !(j div (length (mat1 (2^k))))
                     !(i div (rat_poly.row_length (mat1 (2^k))))) 
                      = (if 
                         ((j div (length (mat1 (2^k)))) 
                              = (i div (rat_poly.row_length (mat1 (2^k)))))
                         then 1 
                         else 0))"
    apply(rule allI)
    apply(rule allI)         
    proof
     fix i j                   
     assume 0:"(i::nat) < 2 ^ (k + 1) \<and> (j::nat) < 2 ^ (k + 1)"
     have "((i div (rat_poly.row_length (mat1 (2^k)))) < 2)
                     \<and>((j div (length (mat1 (2^k)))) < 2)"
                 using 0 13 by auto
     then show "(((mat1 2)
                               !(j div (length (mat1 (2^k))))
                               !(i div (rat_poly.row_length (mat1 (2^k))))) 
                      = (if 
                        ((j div (length (mat1 (2^k)))) 
                              = (i div (rat_poly.row_length (mat1 (2^k)))))
                         then 1 
                         else 0))"
                             using 10 by (metis "6")      
    qed
   have 15:"\<forall>i j.((i mod (rat_poly.row_length (mat1 (2^k))) < 2^k)
                       \<and>  (j mod length (mat1 (2^k)) < 2^k)
                  \<longrightarrow> (((mat1 (2^k))
                             !(j mod (length (mat1 (2^k))))
                             !(i mod (rat_poly.row_length (mat1 (2^k))))) 
                      = (if 
                           ((j mod (length (mat1 (2^k)))) 
                                 = (i mod (rat_poly.row_length (mat1 (2^k)))))
                         then 1 
                         else 0)))"
                   using mat1_index by (metis "6" "7")
   have 16:"\<forall>j.(j < (2^(k+1)) \<longrightarrow> j mod (length (mat1 (2^k))) < 2^k)"
   proof-
    have "2^(k+1) = (2 *n (2^k))"
                 by auto
    then show ?thesis 
               using 7 allI  mod_less_divisor 
               nat_zero_less_power_iff zero_less_numeral by (metis)
   qed
   moreover have 17:"\<forall>i.(i < (2^(k+1)) 
                         \<longrightarrow> (i mod (rat_poly.row_length (mat1 (2^k)))) < 2^k)"
   proof-
    have "2^(k+1) = (2 *n (2^k))"
                 by auto
    then show ?thesis  using 7 allI by (metis "6" calculation)        
   qed     
   ultimately have 18:
             "\<forall>i j.((i < (2^(k+1)))\<and> j < (2^(k+1)) \<longrightarrow>
                         ((i mod (rat_poly.row_length (mat1 (2^k)))) < 2^k)
                          \<and>((j mod (length (mat1 (2^k)))) < 2^k))"
                 by (metis "7")          
   have 19:"\<forall>i j.(i < (2^(k+1)))\<and> (j < (2^(k+1))) \<longrightarrow>
                  (((mat1 (2^k))
                        !(j mod (length (mat1 (2^k))))
                        !(i mod (rat_poly.row_length (mat1 (2^k))))) 
                          = (if 
                              ((j mod (length (mat1 (2^k)))) 
                                 = (i mod (rat_poly.row_length (mat1 (2^k)))))
                         then 1 
                         else 0))"
    apply(rule allI)
    apply(rule allI)         
    proof
     fix i j                   
     assume 0:"(i::nat) < 2 ^ (k + 1) \<and> (j::nat) < 2 ^ (k + 1)"
     have "((i mod (rat_poly.row_length (mat1 (2^k)))) < 2^k)
                          \<and>((j mod (length (mat1 (2^k)))) < 2^k)"
                 using 0 18 by auto
     then show "(((mat1 (2^k))
                               !(j mod (length (mat1 (2^k))))
                               !(i mod(rat_poly.row_length (mat1 (2^k))))) 
                      = (if 
                          ((j mod (length (mat1 (2^k)))) 
                                = (i mod (rat_poly.row_length (mat1 (2^k)))))
                            then 1 
                            else 0))"
                             using 15 by (metis "6")      
    qed
   have "(\<forall>i. \<forall>j. 
              (i <(2^(k+1))) \<and> (j < (2^(k+1))) 
                \<longrightarrow> rat_poly_times
                              ((mat1 2)
                                  !(j div (length (mat1 (2^k))))
                                  !(i div (rat_poly.row_length (mat1 (2^k))))) 
                              ((mat1 (2^k))
                                  !(j mod length (mat1 (2^k)))
                                  !(i mod (rat_poly.row_length (mat1 (2^k)))))
                   =
                    (if 
                        (((j div (length (mat1 (2^k)))) 
                              = (i div (rat_poly.row_length (mat1 (2^k)))))
                        \<and>((j mod (length (mat1 (2^k)))) 
                              = (i mod (rat_poly.row_length (mat1 (2^k))))))                        
                         then 1 
                         else 0))"
    apply(rule allI)
    apply(rule allI)
    proof
     fix i j
     assume 0: "((i::nat) <(2^(k+1))) \<and> ((j::nat) < (2^(k+1)))"
     have s1: "((mat1 2)
                      !(j div (length (mat1 (2^k))))
                      !(i div (rat_poly.row_length (mat1 (2^k))))) 
                      =    (if 
                          ((j div (length (mat1 (2^k)))) 
                             = (i div (rat_poly.row_length (mat1 (2^k)))))
                          then 1 
                               else 0)"
               using 0 14 by metis
     moreover have s2:"((mat1 (2^k))
                              !(j mod (length (mat1 (2^k))))
                              !(i mod (rat_poly.row_length (mat1 (2^k))))) 
                         =  (if 
                          ((j mod (length (mat1 (2^k)))) 
                                = (i mod (rat_poly.row_length (mat1 (2^k)))))
                               then 1 
                               else 0)"
               using 0 19 by metis  
     show "rat_poly_times
                     ((mat1 2)
                             !(j div (length (mat1 (2^k))))
                             !(i div (rat_poly.row_length (mat1 (2^k))))) 
                             ((mat1 (2^k))
                                 !(j mod length (mat1 (2^k)))
                                 !(i mod (rat_poly.row_length (mat1 (2^k)))))
                             =
                           (if 
                             (((j div (length (mat1 (2^k)))) 
                                = (i div (rat_poly.row_length (mat1 (2^k)))))
                             \<and>((j mod (length (mat1 (2^k)))) 
                                = (i mod (rat_poly.row_length (mat1 (2^k))))))
                                  then 1 
                                  else 0)"
      apply(simp)
      apply(rule conjI)
      proof-
      show "j div length (mat1 (2 ^ k)) = i div rat_poly.row_length (mat1 (2 ^ k)) 
           \<and> (j mod length (mat1 (2 ^ k)) = i mod rat_poly.row_length (mat1 (2 ^ k)))
                        \<longrightarrow> rat_poly_times 
                              (mat1 2 
                                 !(j div length (mat1 (2 ^ k))) 
                                 !(i div rat_poly.row_length (mat1 (2 ^ k))))
                               (mat1 (2 ^ k) 
                                 !(j mod length (mat1 (2 ^ k))) 
                                 !(i mod rat_poly.row_length (mat1 (2 ^ k)))) 
                                         = 1"
      proof-
       have 
        "j div length (mat1 (2 ^ k)) 
                                  = i div rat_poly.row_length (mat1 (2 ^ k)) 
          \<and> j mod length (mat1 (2 ^ k)) = i mod rat_poly.row_length (mat1 (2 ^ k))  
         \<Longrightarrow> rat_poly_times 
              (mat1 2 ! (j div length (mat1 (2 ^ k))) ! (i div rat_poly.row_length (mat1 (2 ^ k))))
              (mat1 (2 ^ k) ! (j mod length (mat1 (2 ^ k))) 
                            ! (i mod rat_poly.row_length (mat1 (2 ^ k)))) =   1"                  
       proof-
        assume local_assms:
            "j div length (mat1 (2 ^ k)) = i div rat_poly.row_length (mat1 (2 ^ k)) 
           \<and> j mod length (mat1 (2 ^ k)) = i mod rat_poly.row_length (mat1 (2 ^ k)) "
        have "(mat1 2 ! (j div length (mat1 (2 ^ k))) ! (i div rat_poly.row_length (mat1 (2 ^ k))))
                               = 1"
             using s1 local_assms by metis
        moreover have "(mat1 (2 ^ k) 
                 ! (j mod length (mat1 (2 ^ k))) ! (i mod rat_poly.row_length (mat1 (2 ^ k)))) = 1"   
             using s2 local_assms by metis
        ultimately show ?thesis 
                by (metis "3" "6" "7" Suc.IH local_assms mve1 prop_make_vert_equiv(1) 
                          prop_make_vert_equiv(2) rat_poly.right_id)  
       qed
       then show ?thesis by auto 
      qed 
      show 
       "(j div length (mat1 (2 ^ k)) = i div rat_poly.row_length (mat1 (2 ^ k)) \<longrightarrow>
              j mod length (mat1 (2 ^ k)) \<noteq> i mod rat_poly.row_length (mat1 (2 ^ k))) \<longrightarrow>
          mat1 2 ! (j div length (mat1 (2 ^ k))) ! (i div rat_poly.row_length (mat1 (2 ^ k))) = 0 \<or>
      mat1 (2 ^ k) ! (j mod length (mat1 (2 ^ k))) ! (i mod rat_poly.row_length (mat1 (2 ^ k))) = 0"                         
      proof-
       have "(j div length (mat1 (2 ^ k)) = i div rat_poly.row_length (mat1 (2 ^ k))
            \<and>  j mod length (mat1 (2 ^ k)) \<noteq> i mod rat_poly.row_length (mat1 (2 ^ k))) \<Longrightarrow>
           mat1 2 ! (j div length (mat1 (2 ^ k))) ! (i div rat_poly.row_length (mat1 (2 ^ k))) = 0 
   \<or> mat1 (2 ^ k) ! (j mod length (mat1 (2 ^ k))) ! (i mod rat_poly.row_length (mat1 (2 ^ k))) = 0"
       proof-
        assume local_assms:
                "(j div length (mat1 (2 ^ k)) = i div rat_poly.row_length (mat1 (2 ^ k))
                 \<and> j mod length (mat1 (2 ^ k)) \<noteq> i mod rat_poly.row_length (mat1 (2 ^ k)))"
        have "mat1 (2 ^ k) ! (j mod length (mat1 (2 ^ k))) ! (i mod rat_poly.row_length (mat1 (2 ^ k))) = 0"
             using s2 local_assms by metis
        then show ?thesis by auto
       qed
       then have l:
     "(j div length (mat1 (2 ^ k)) = i div rat_poly.row_length (mat1 (2 ^ k))
       \<and> j mod length (mat1 (2 ^ k)) \<noteq> i mod rat_poly.row_length (mat1 (2 ^ k))) \<longrightarrow>
        mat1 2 ! (j div length (mat1 (2 ^ k))) ! (i div rat_poly.row_length (mat1 (2 ^ k))) = 0 
    \<or>mat1 (2 ^ k) ! (j mod length (mat1 (2 ^ k))) ! (i mod rat_poly.row_length (mat1 (2 ^ k))) = 0"
             by auto 
       show "(j div length (mat1 (2 ^ k)) = i div rat_poly.row_length (mat1 (2 ^ k)) \<longrightarrow>
     j mod length (mat1 (2 ^ k)) \<noteq> i mod rat_poly.row_length (mat1 (2 ^ k))) \<longrightarrow>
    mat1 2 ! (j div length (mat1 (2 ^ k))) ! (i div rat_poly.row_length (mat1 (2 ^ k))) = 0 \<or>
    mat1 (2 ^ k) ! (j mod length (mat1 (2 ^ k))) ! (i mod rat_poly.row_length (mat1 (2 ^ k))) = 0"
        proof-
        have 
         "(j div length (mat1 (2 ^ k)) = i div rat_poly.row_length (mat1 (2 ^ k)) \<longrightarrow>
          j mod length (mat1 (2 ^ k)) \<noteq> i mod rat_poly.row_length (mat1 (2 ^ k))) \<Longrightarrow>
      mat1 2 ! (j div length (mat1 (2 ^ k))) ! (i div rat_poly.row_length (mat1 (2 ^ k))) = 0 \<or>
      mat1 (2 ^ k) ! (j mod length (mat1 (2 ^ k))) ! (i mod rat_poly.row_length (mat1 (2 ^ k))) = 0"
        proof-
         assume local_assm1:
           "(j div length (mat1 (2 ^ k)) = i div rat_poly.row_length (mat1 (2 ^ k)) \<longrightarrow>
                    j mod length (mat1 (2 ^ k)) \<noteq> i mod rat_poly.row_length (mat1 (2 ^ k)))"
         have "(j div length (mat1 (2 ^ k)) = i div rat_poly.row_length (mat1 (2 ^ k)))
               \<Longrightarrow> 
                mat1 (2 ^ k) ! (j mod length (mat1 (2 ^ k))) 
                             ! (i mod rat_poly.row_length (mat1 (2 ^ k))) 
                           = 0"
               using s2 local_assm1 by (metis "7")
         then have l1:" (j div length (mat1 (2 ^ k)) = i div rat_poly.row_length (mat1 (2 ^ k)))
                     \<Longrightarrow> ?thesis" 
               by auto
         moreover have "\<not>(j div length (mat1 (2 ^ k)) = i div rat_poly.row_length (mat1 (2 ^ k)))
                         \<Longrightarrow>  mat1 2 ! (j div length (mat1 (2^k))) 
                                     ! (i div rat_poly.row_length (mat1 (2^k))) 
                                                = 0"
               using s1 by metis
         then have "\<not>(j div length (mat1 (2 ^ k)) = i div rat_poly.row_length (mat1 (2 ^ k)))
                        \<Longrightarrow> ?thesis"
               by auto
         then show ?thesis using l1 by auto
        qed
        then show ?thesis by auto
       qed
      qed
     qed
    qed
    then have "(\<forall>i. \<forall>j. (i <(2^(k+1))) \<and> (j < (2^(k+1))) \<longrightarrow>
         ((rat_poly.Tensor (mat1 2)  (mat1 (2^k))!j!i)  = (if 
                      (((j div (length (mat1 (2^k)))) = (i div (rat_poly.row_length (mat1 (2^k)))))
                     \<and>((j mod (length (mat1 (2^k)))) = (i mod (rat_poly.row_length (mat1 (2^k))))))
                        then 1 
                         else 0)))"
               using 9 by metis
    then have "(\<forall>i. \<forall>j. (i <(2^(k+1))) \<and> (j < (2^(k+1))) \<longrightarrow>
                ((rat_poly.Tensor (mat1 2)  (mat1 (2^k))!j!i)  = (if 
                         (((j div (2^k))) = (i div (2^k))
                       \<and>((j mod (2^k)) = (i mod (2^k))))
                        then 1 
                         else 0)))"
               by (metis (hide_lams, no_types) "6" "7")
    then have 20:"(\<forall>i. \<forall>j. (i <(2^(k+1))) \<and> (j < (2^(k+1))) \<longrightarrow>
                         ((rat_poly.Tensor (mat1 2)  (mat1 (2^k))!j!i)  = (if  (j = i)
                                                                                then 1 
                                                                                 else 0)))"    
               using equal_div_mod2 by auto
    with 2 have "(\<forall>i. \<forall>j. (i <(2^(k+1))) \<and> (j < (2^(k+1))) \<longrightarrow>
                      ((rat_poly.Tensor (mat1 2)  (mat1 (2^k))!j!i)  = (mat1 (2^(k+1)))!j!i))"
               by metis
    then have "(\<forall>i <(2^(k+1)).\<forall>j < (2^(k+1)). 
         ((rat_poly.Tensor (mat1 2)  (mat1 (2^k))!j!i)  = (mat1 (2^(k+1)))!j!i))"
                  by auto
    moreover have "mat (2^(k+1)) (2^(k+1)) (rat_poly.Tensor (mat1 2)  (mat1 (2^k)))"
               using  \<open>make_vert_equiv (k + 1) = mat1 2 \<otimes> mat1 (2 ^ k)\<close>      
               by (metis prop_make_vert_equiv(1) prop_make_vert_equiv(2) 
                  prop_make_vert_equiv(3))
    ultimately have "(rat_poly.Tensor (mat1 2)  (mat1 (2^k))) = (mat1 (2^(k+1)))"
              using 1 mat_eqI by metis
    then show ?thesis by auto
   qed
   then show ?case using make_vert_equiv.simps 
   using  \<open>make_vert_equiv (k + 1) = mat1 2 \<otimes> mat1 (2 ^ k)\<close>
   by (metis Suc_eq_plus1)
qed


theorem make_vert_block_map_blockmat:
 "blockmat (make_vert_block n) = (mat1 (2^n))"
          by (metis blockmat_make_vert make_vert_equiv_mat)


lemma  mat1_rt_mult:assumes "mat nr nc m1"
       shows "rat_poly.matrix_mult m1 (mat1 (nc)) = m1"
        using assms  mat1_mult_right rat_poly.mat_empty_row_length 
        rat_poly.matrix_row_length 
        rat_poly.row_length_def rat_poly.unique_row_col(1) by (metis)         

lemma mat1_vert_block: 
       "rat_poly.matrix_mult 
                   (blockmat b) 
                   (blockmat (make_vert_block (nat (codomain_block b))))
                           = (blockmat b)"
proof-
 have "mat 
          (rat_poly.row_length (blockmat b)) 
          (2^(nat (codomain_block b))) 
                            (blockmat b)"  
          using  length_codomain_block matrix_blockmat 
          by auto 
 moreover have "(blockmat (make_vert_block (nat (codomain_block b))))
                       = mat1 (2^(nat (codomain_block b)))"
          using make_vert_block_map_blockmat by auto
 ultimately show ?thesis using mat1_rt_mult by auto
qed 


text\<open>The following list of theorems deal with distributivity properties
of tensor product of matrices (with entries as rational functions) 
      and composition\<close>
definition weak_matrix_match::
              "rat_poly mat \<Rightarrow> rat_poly mat \<Rightarrow> rat_poly mat \<Rightarrow> bool"
where
"weak_matrix_match A1 A2 B1 \<equiv> (mat (rat_poly.row_length A1) (length A1) A1)
   \<and>(mat (rat_poly.row_length A2) (length A2) A2)
   \<and>(mat (rat_poly.row_length B1) 1 B1)
\<and>(A1 \<noteq> [])\<and>(A2 \<noteq> [])\<and>(B1 \<noteq> [])
  \<and> (length A1 = rat_poly.row_length A2)"

theorem weak_distributivity1:
 "weak_matrix_match A1 A2 B1
  \<Longrightarrow> ((rat_poly.matrix_mult A1  A2)\<otimes> B1) 
               = (rat_poly.matrix_mult (A1 \<otimes> B1) (A2))"
proof-
 assume assms:"weak_matrix_match A1 A2 B1"
 have 1:"length B1 = 1"
        using assms weak_matrix_match_def 
        by (metis rat_poly.matrix_row_length rat_poly.unique_row_col(2))
 have "[[1]] \<noteq> []" 
        by auto
 moreover have "mat 1 1 [[1]]"
        unfolding mat_def Ball_def vec_def by auto
 moreover have "rat_poly.row_length [[1]] = length B1"
        unfolding rat_poly.row_length_def 1 by auto
 ultimately have "rat_poly.matrix_match A1 A2 B1 [[1]]"
        unfolding rat_poly.matrix_match_def 
        using assms weak_matrix_match_def "1" blockmat.simps(1)
              matrix_blockmat by (metis (hide_lams, no_types))
 then have "((rat_poly.matrix_mult A1  A2)\<otimes>(rat_poly.matrix_mult B1  [[1]])) 
               = (rat_poly.matrix_mult (A1 \<otimes> B1) (A2 \<otimes> [[1]]))" 
        using rat_poly.distributivity by auto
 moreover have "(rat_poly.matrix_mult B1  [[1]]) = B1"
        using weak_matrix_match_def  assms mat1_equiv mat1_mult_right
        by (metis)
 moreover have "(A2 \<otimes> [[1]]) = A2"
        using  rat_poly.Tensor_right_id  by (metis)
 ultimately show ?thesis by auto
qed

definition weak_matrix_match2::
     "rat_poly mat \<Rightarrow> rat_poly mat \<Rightarrow> rat_poly mat \<Rightarrow> bool"
where
"weak_matrix_match2 A1 B1 B2 \<equiv> (mat (rat_poly.row_length A1) 1 A1)
   \<and>(mat (rat_poly.row_length B1) (length B1) B1)
   \<and>(mat (rat_poly.row_length B2) (length B2) B2)
\<and>(A1 \<noteq> [])\<and>(B1 \<noteq> [])\<and>(B2 \<noteq> [])
  \<and> (length B1 = rat_poly.row_length B2)"

theorem weak_distributivity2:
"weak_matrix_match2 A1 B1 B2
     \<Longrightarrow> (A1\<otimes> (rat_poly.matrix_mult B1 B2)) 
                                  = (rat_poly.matrix_mult (A1 \<otimes> B1) (B2))"
proof-
 assume assms:"weak_matrix_match2 A1 B1 B2"
 have 1:"length A1 = 1"
        using assms weak_matrix_match2_def 
        by (metis rat_poly.matrix_row_length rat_poly.unique_row_col(2))
 have "[[1]] \<noteq> []" 
        by auto
 moreover have "mat 1 1 [[1]]"
        unfolding mat_def Ball_def vec_def by auto
 moreover have "rat_poly.row_length [[1]] = length A1"
        unfolding rat_poly.row_length_def 1 by auto
 ultimately have "rat_poly.matrix_match A1 [[1]] B1 B2"
        unfolding rat_poly.matrix_match_def  
        using assms weak_matrix_match2_def  
             "1" blockmat.simps(1) matrix_blockmat
        by (metis (hide_lams, no_types))
 then have "((rat_poly.matrix_mult A1  [[1]])\<otimes>(rat_poly.matrix_mult B1 B2)) 
               = (rat_poly.matrix_mult (A1 \<otimes> B1) ([[1]] \<otimes> B2))" 
        using rat_poly.distributivity by auto
 moreover have "(rat_poly.matrix_mult A1  [[1]]) = A1"
        using weak_matrix_match2_def
              assms mat1_equiv mat1_mult_right
       by (metis)
 moreover have "([[1]] \<otimes> B2) = B2"
       by (metis rat_poly.Tensor_left_id)
 ultimately show ?thesis by auto
qed


lemma is_tangle_diagram_weak_matrix_match:
 assumes "is_tangle_diagram (w1*ws1)"
      and "codomain_block w2 = 0"
 shows "weak_matrix_match (blockmat w1) (kauff_mat ws1) (blockmat w2)"
 unfolding weak_matrix_match_def
 apply(auto)
 proof-
   show "mat 
          (rat_poly.row_length (blockmat w1)) 
          (length (blockmat w1)) 
                         (blockmat w1)"
       using matrix_blockmat by auto
  next
   have "is_tangle_diagram ws1"
       using assms(1) is_tangle_diagram.simps(2) by metis
   then show "mat 
                (rat_poly.row_length (kauff_mat ws1)) 
                (length (kauff_mat ws1)) 
                           (kauff_mat ws1)"
       using matrix_kauff_mat by metis
  next
   have "mat 
           (rat_poly.row_length (blockmat w2)) 
           (length (blockmat w2)) 
                          (blockmat w2)"
       using matrix_blockmat  by auto            
   then have "mat 
                (rat_poly.row_length (blockmat w2)) 1 (blockmat w2)"
       using assms(2) length_codomain_block by auto
   then show "mat (rat_poly.row_length (blockmat w2)) (Suc 0) (blockmat w2)"
       by auto 
  next
   show "length (blockmat w1) = rat_poly.row_length (kauff_mat ws1)"
       using is_tangle_diagram_length_rowlength assms(1) by auto
  next
   assume 0:"blockmat w1 = [] "
   show False using 0
       by (metis blockmat_non_empty)
  next
   assume 1:"kauff_mat ws1 = [] "
   have "is_tangle_diagram ws1"
       using assms(1) is_tangle_diagram.simps(2) by metis
   then show False using 1 kauff_mat_non_empty by auto
  next
   assume 0:"blockmat w2 = [] "
   show False using 0
       by (metis blockmat_non_empty)
qed


lemma is_tangle_diagram_weak_matrix_match2:
 assumes "is_tangle_diagram (w2*ws2)"
      and "codomain_block w1 = 0"
 shows "weak_matrix_match2 (blockmat w1) (blockmat w2) (kauff_mat ws2)"
 unfolding weak_matrix_match2_def
  apply(auto)
  proof-
    have "mat 
            (rat_poly.row_length (blockmat w1)) 
            (length (blockmat w1)) 
                           (blockmat w1)"
        using matrix_blockmat  by auto            
    then have "mat 
                 (rat_poly.row_length (blockmat w1)) 1 (blockmat w1)"
        using assms(2) length_codomain_block by auto
    then show "mat (rat_poly.row_length (blockmat w1)) (Suc 0) (blockmat w1)"
        by auto  
   next
    have "is_tangle_diagram ws2"
          using assms(1) is_tangle_diagram.simps(2) by metis
    then show "mat 
                (rat_poly.row_length (kauff_mat ws2)) 
                (length (kauff_mat ws2)) 
                               (kauff_mat ws2)"
          using matrix_kauff_mat by metis
   next
    show "mat 
           (rat_poly.row_length (blockmat w2)) 
           (length (blockmat w2)) 
                           (blockmat w2)"
         by (metis matrix_blockmat)
   next
    show "length (blockmat w2) = rat_poly.row_length (kauff_mat ws2)"
          using is_tangle_diagram_length_rowlength assms(1) by auto
   next
    assume 0:"blockmat w1 = [] "
    show False using 0
          by (metis blockmat_non_empty)
   next
    assume 1:"kauff_mat ws2 = [] "
    have "is_tangle_diagram ws2"
          using assms(1) is_tangle_diagram.simps(2) by metis
    then show False using 1 kauff_mat_non_empty by auto
    next
    assume 0:"blockmat w2 = [] "
    show False using 0
           by (metis blockmat_non_empty)
  qed


lemma is_tangle_diagram_vert_block:
  "is_tangle_diagram (b*(basic (make_vert_block (nat (codomain_block b)))))"
proof-
 have "domain_wall (basic (make_vert_block (nat (codomain_block b))))
                = (codomain_block b)"
      using domain_wall.simps make_vert_block.simps 
      by (metis codomain_block_nonnegative domain_make_vert int_nat_eq)      
 then show ?thesis using is_tangle_diagram.simps by auto
qed 


text\<open>The following theorem tells us that the the map kauff$\_$mat when 
 restricted to walls representing tangles preserves the tensor product\<close>

theorem Tensor_Invariance:
 "(is_tangle_diagram ws1) \<and> (is_tangle_diagram ws2)
 \<Longrightarrow> (kauff_mat (ws1 \<otimes> ws2) = (kauff_mat ws1) \<otimes> (kauff_mat ws2))"
proof(induction rule:tensor.induct)
 case 1
  show ?case using kauff_mat_tensor_distrib by auto
 next
  fix a b as bs
  assume hyps:"  is_tangle_diagram as \<and> is_tangle_diagram bs 
                \<Longrightarrow> (kauff_mat (as \<otimes> bs) = kauff_mat as \<otimes> kauff_mat bs)"
  assume prems:" is_tangle_diagram (a*as) \<and> is_tangle_diagram (b*bs) "
  let ?case =  "kauff_mat (a * as \<otimes> b * bs) 
                         = kauff_mat (a * as) \<otimes> kauff_mat (b * bs)"
  have 0:"rat_poly.matrix_match 
                         (blockmat a) 
                         (kauff_mat as) 
                         (blockmat b) 
                         (kauff_mat bs)"
         using prems is_tangle_diagram_matrix_match by auto          
  have 1:"is_tangle_diagram as \<and> is_tangle_diagram bs"
         using prems is_tangle_diagram.simps by metis  
  have "kauff_mat ((a * as) \<otimes> (b * bs)) 
                          = kauff_mat ((a \<otimes> b) * (as \<otimes> bs))"
        using tensor.simps by auto
  moreover have "... = rat_poly.matrix_mult 
                                   (blockmat (a \<otimes> b)) 
                                   (kauff_mat (as \<otimes> bs))"
        using kauff_mat.simps(2) by auto
  moreover have "... = rat_poly.matrix_mult 
                             ((blockmat a) \<otimes> (blockmat b)) 
                             ((kauff_mat as) \<otimes> (kauff_mat bs))"
        using hyps 1  kauff_mat_tensor_distrib by auto
  moreover have "... =(rat_poly.matrix_mult (blockmat a) (kauff_mat as))
                         \<otimes> (rat_poly.matrix_mult (blockmat b) (kauff_mat bs))" 
        using 0 rat_poly.distributivity by auto
  moreover have "... = kauff_mat (a*as) \<otimes> kauff_mat (b*bs)"
        by auto    
  ultimately show ?case by metis
 next
  fix a b as bs 
  assume hyps:"codomain_block b \<noteq> 0  
            \<Longrightarrow> is_tangle_diagram as 
               \<and> is_tangle_diagram 
                      (basic (make_vert_block (nat (codomain_block b)))) 
            \<Longrightarrow> kauff_mat 
                  (as \<otimes> basic (make_vert_block (nat (codomain_block b))))
                   = kauff_mat as 
                      \<otimes> kauff_mat 
                         (basic (make_vert_block (nat (codomain_block b))))"

  assume prems:"is_tangle_diagram (a * as) \<and> is_tangle_diagram (basic b)"

  let ?case = " kauff_mat (a * as \<otimes> basic b) 
                  = kauff_mat (a * as) \<otimes> kauff_mat (basic b)"                   
  show ?case
  proof(cases "codomain_block b = 0")
   case True 
    have "((a * as) \<otimes> (basic b)) =  ((a \<otimes>b) *  as)" 
         using tensor.simps True by auto
    then have "kauff_mat ((a * as) \<otimes> (basic b))
                           = kauff_mat ((a \<otimes>b) *  as)"
         by auto
    moreover have "... = 
                              rat_poly.matrix_mult 
                                   (blockmat (a \<otimes> b))  
                                   (kauff_mat as)"
         by auto
    moreover have "... = 
                           rat_poly.matrix_mult 
                                     ((blockmat a) \<otimes> (blockmat b)) 
                                     (kauff_mat as)"
         using  blockmat_tensor_distrib by (metis) 
    ultimately have T1:
                     "kauff_mat ((a * as) \<otimes> (basic b))
                             = rat_poly.matrix_mult 
                                     ((blockmat a) \<otimes> (blockmat b)) 
                               (kauff_mat as)"
         by auto
    then have "weak_matrix_match 
                            (blockmat a) 
                            (kauff_mat as) 
                            (blockmat b)"
         using is_tangle_diagram_weak_matrix_match True prems by auto
    then have "rat_poly.matrix_mult 
                        ((blockmat a) \<otimes> (blockmat b)) 
                        (kauff_mat as)
                              = ((rat_poly.matrix_mult 
                                           (blockmat a) 
                                            (kauff_mat as))
                                  \<otimes> (blockmat b))"
         using weak_distributivity1 by auto
     moreover have "... = (kauff_mat (a*as)) \<otimes> (kauff_mat (basic b))"
                               by auto
         ultimately show ?thesis using T1 by metis
    next
     case False
      let ?bs = "(basic (make_vert_block (nat (codomain_block b))))"
      have F0:"rat_poly.matrix_match 
                                 (blockmat a) 
                                 (kauff_mat as) 
                                  (blockmat b)
                                   (kauff_mat ?bs)"
            using prems is_tangle_diagram_vert_block 
                 is_tangle_diagram_matrix_match  by metis  
      have F1:"codomain_block b \<noteq> 0"
            using False by auto 
      have F2:" is_tangle_diagram as 
                     \<and> is_tangle_diagram ?bs"   
            using is_tangle_diagram.simps prems by metis
      then have F3:"kauff_mat 
                         (as\<otimes>basic (make_vert_block (nat (codomain_block b)))) =
                                     kauff_mat as \<otimes> kauff_mat ?bs"
           using F1 hyps by auto
      moreover have "((a*as) \<otimes> (basic b)) = (a \<otimes> b) * (as \<otimes> ?bs)"
           using False tensor.simps by auto
      moreover then have "kauff_mat ((a*as) \<otimes> (basic b)) 
                                     = kauff_mat((a \<otimes> b) * (as \<otimes> ?bs))"
           by auto
      moreover then have "... = rat_poly.matrix_mult 
                                             (blockmat (a \<otimes> b)) 
                                             (kauff_mat (as \<otimes> ?bs))"
          using kauff_mat.simps by auto
      moreover then have "... = rat_poly.matrix_mult 
                                            ((blockmat a)\<otimes>(blockmat b))
                                            ((kauff_mat as)\<otimes>(kauff_mat ?bs))"
          using F3  blockmat_tensor_distrib by (metis)  
      moreover then have 
               "...  
                    = (rat_poly.matrix_mult (blockmat a) (kauff_mat as))
                       \<otimes> (rat_poly.matrix_mult (blockmat b) (kauff_mat ?bs))" 
          using rat_poly.distributivity F0 by auto   
      moreover then have "... 
                                  =  (rat_poly.matrix_mult 
                                             (blockmat a) 
                                             (kauff_mat as))
                                       \<otimes> (blockmat b)"
          using mat1_vert_block by auto
      moreover then have "... = (kauff_mat (a*as)) 
                                           \<otimes> (kauff_mat (basic b))"
          using kauff_mat.simps by auto
      ultimately show ?thesis by metis
  qed
  next       
   fix a b as bs 
   assume hyps:
       "codomain_block b \<noteq> 0  
          \<Longrightarrow>  is_tangle_diagram 
                       (basic (make_vert_block (nat (codomain_block b)))) 
                 \<and>(is_tangle_diagram as) 
          \<Longrightarrow> kauff_mat (basic (make_vert_block (nat (codomain_block b)))\<otimes> as) 
            =  kauff_mat (basic (make_vert_block (nat (codomain_block b)))) 
         \<otimes> kauff_mat as "
   assume prems:"is_tangle_diagram (basic b) \<and> is_tangle_diagram (a * as) "
   let ?case = " kauff_mat ( (basic b) \<otimes>  (a * as)) 
                       = kauff_mat (basic b) \<otimes>  kauff_mat (a * as)"                   
   show ?case
   proof(cases "codomain_block b = 0")
    case True
     have "((basic b) \<otimes> (a * as)) =  ((b \<otimes> a) *  as)" 
          using tensor.simps True by auto
     then have "kauff_mat ((basic b) \<otimes> (a * as))
                           = kauff_mat ((b \<otimes>a ) *  as)"
          by auto
     moreover have "... = rat_poly.matrix_mult 
                                      (blockmat (b \<otimes> a))  
                                      (kauff_mat as)"
          by auto
     moreover have "... = rat_poly.matrix_mult 
                                         ((blockmat b) \<otimes> (blockmat a)) 
                                         (kauff_mat as)"
         using  blockmat_tensor_distrib by (metis) 
     ultimately have T1:"kauff_mat ((basic b) \<otimes> (a*as))
                                     = rat_poly.matrix_mult 
                                          ((blockmat b) \<otimes> (blockmat a)) 
                                          (kauff_mat as)"
         by auto
     then have "weak_matrix_match2 
                              (blockmat b) 
                               (blockmat a) 
                               (kauff_mat as)"
         using is_tangle_diagram_weak_matrix_match2 
               True prems by auto
     then have "rat_poly.matrix_mult 
                                ((blockmat b) \<otimes> (blockmat a)) 
                                (kauff_mat as)
                     = (blockmat b)  
                        \<otimes> (rat_poly.matrix_mult (blockmat a)(kauff_mat as))"
         using weak_distributivity2 by auto
     moreover have "... = (kauff_mat (basic b)) \<otimes> (kauff_mat (a*as)) "
         by auto
     ultimately show ?thesis using T1 by metis  
    next
    case False
     let ?bs = "(basic (make_vert_block (nat (codomain_block b))))"
     have F0:"rat_poly.matrix_match  
                                   (blockmat b)
                                   (kauff_mat ?bs) 
                                   (blockmat a) 
                                   (kauff_mat as)"
         using prems is_tangle_diagram_vert_block 
              is_tangle_diagram_matrix_match  by metis  
     have F1:"codomain_block b \<noteq> 0"
         using False by auto 
     have F2:" is_tangle_diagram as 
                     \<and> is_tangle_diagram ?bs"   
         using is_tangle_diagram.simps prems by metis
     then have F3:"kauff_mat (?bs \<otimes> as) = kauff_mat ?bs \<otimes> kauff_mat as"
         using F1 hyps by auto
     moreover have "((basic b) \<otimes> (a*as)) = (b \<otimes> a) * (?bs \<otimes> as)"
         using False tensor.simps by auto
     moreover then have 
                    "kauff_mat ((basic b) \<otimes> (a*as)) 
                                    = kauff_mat((b \<otimes> a) * (?bs \<otimes> as))"
         by auto
     moreover then have "... 
                                 = rat_poly.matrix_mult 
                                               (blockmat (b \<otimes> a)) 
                                               (kauff_mat (?bs \<otimes> as))"
         using kauff_mat.simps by auto
     moreover then have "... 
                          = rat_poly.matrix_mult 
                                    ((blockmat b)\<otimes>(blockmat a))
                                    ((kauff_mat ?bs)\<otimes>(kauff_mat as))"                      
         using F3 by (metis blockmat_tensor_distrib)  
     moreover then have "...  
                                 = (rat_poly.matrix_mult 
                                          (blockmat b) 
                                          (kauff_mat ?bs))
                          \<otimes> (rat_poly.matrix_mult  
                                              (blockmat a) 
                                              (kauff_mat as))" 
         using rat_poly.distributivity F0 by auto   
     moreover then have "... = (blockmat b) 
                                      \<otimes> (rat_poly.matrix_mult 
                                                   (blockmat a) 
                                                   (kauff_mat as))"
         using mat1_vert_block by auto
     moreover then have "... = (kauff_mat (basic b)) 
                                           \<otimes> (kauff_mat (a*as))"
         using kauff_mat.simps by auto
     ultimately show ?thesis by metis
   qed  
qed



end

