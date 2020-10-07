section\<open>Tangle\_Algebra: Tensor product of tangles and its properties\<close>
theory Tangle_Algebra
imports Tangles
begin

section\<open>Definition of tensor product of walls\<close>

text\<open>the following definition is used to construct a block of n vert strands\<close>
primrec make_vert_block:: "nat \<Rightarrow> block"
where
"make_vert_block 0 = []"
|"make_vert_block (Suc n) = vert#(make_vert_block n)"
 

lemma domain_make_vert:"domain_block (make_vert_block n) = int n"
 by (induction n) (auto)


lemma codomain_make_vert:"codomain_block (make_vert_block n) = int n"
  by (induction n) (auto)

  
(*we defined the tensor of wall as described in the standard tangle algebra*)
fun tensor::"wall => wall => wall" (infixr "\<otimes>" 65)
where
1:"tensor (basic x) (basic y) = (basic (x \<otimes> y))"
|2:"tensor (x*xs) (basic y) = (
                  if (codomain_block y = 0)
                  then (x \<otimes> y)*xs 
                   else 
                    (x \<otimes> y)
                     *(xs\<otimes>(basic (make_vert_block (nat (codomain_block y))))))"
|3:"tensor (basic x) (y*ys) = (
                  if (codomain_block x = 0) 
                   then (x \<otimes> y)*ys 
                   else 
                    (x \<otimes> y)
                    *((basic (make_vert_block (nat (codomain_block x))))\<otimes> ys))"
|4:"tensor (x*xs) (y*ys) = (x \<otimes> y)* (xs \<otimes> ys)"


section\<open>Properties of tensor product of tangles\<close>

lemma Nil_left_tensor:"xs \<otimes> (basic ([])) = xs"
 by (cases xs) (auto simp add:empty_concatenate)


lemma Nil_right_tensor:"(basic ([])) \<otimes> xs = xs"
 by (cases xs) (auto)

 

text\<open>The definition of tensors is extended to diagrams by using the 
following function\<close>
definition tensor_Tangle ::"Tangle_Diagram \<Rightarrow> Tangle_Diagram \<Rightarrow> Tangle_Diagram" (infixl "\<otimes>" 65)
where
"tensor_Tangle x y = Abs_Tangle_Diagram ((Rep_Tangle_Diagram x) \<otimes> (Rep_Tangle_Diagram y))" 

(*some lemmas*)
lemma "tensor (basic [vert]) (basic ([vert])) = (basic (([vert]) \<otimes> ([vert])))"
 by simp

text\<open>domain\_wall of a tensor product of two walls is the sum of 
the domain\_wall of each of the tensor
 products\<close>

lemma tensor_domain_wall_additivity:
 "domain_wall (xs \<otimes> ys) = domain_wall xs + domain_wall ys"
proof(cases xs)
 fix x
 assume A:"xs = basic x"
 then have "domain_wall (xs \<otimes> ys) = domain_wall xs + domain_wall ys"
  proof(cases ys)
   fix y
   assume B:"ys = basic y"
   have "domain_block (x \<otimes> y) = domain_block x + domain_block y"
       using domain_additive by auto
   then have "domain_wall (xs \<otimes> ys) = domain_wall xs + domain_wall ys"
       using tensor.simps(1) A B by auto
   thus ?thesis by auto
 next
  fix z zs 
  assume C:"ys = (z*zs)"
  have "domain_wall (xs \<otimes> ys) = domain_wall xs + domain_wall ys"
   proof(cases "(codomain_block x) = 0")  
     assume "codomain_block x = 0"
     then have "(xs \<otimes> ys) = (x \<otimes> z)*zs" 
          using A C tensor.simps(4) by auto
     then have "domain_wall (xs \<otimes> ys) = domain_block (x \<otimes> z)" 
          by auto
     moreover have "domain_wall ys = domain_block z"
          unfolding domain_wall_def C by auto
     moreover have "domain_wall xs = domain_block x"
          unfolding domain_wall_def A by auto
     moreover have "domain_block (x \<otimes> z) = domain_block x + domain_block z" 
          using domain_additive by auto
     ultimately show ?thesis by auto
    next
     assume "codomain_block x \<noteq> 0"
     have "(xs \<otimes> ys)  
                 = (x \<otimes> z)
                    *((basic (make_vert_block (nat (codomain_block x))))\<otimes> zs)"
          using tensor.simps(3) A C \<open>codomain_block x \<noteq> 0\<close>  by auto
     then have "domain_wall (xs \<otimes> ys) = domain_block (x \<otimes> z)"
          by auto   
     moreover have "domain_wall ys = domain_block z"
          unfolding domain_wall_def C by auto
     moreover have "domain_wall xs = domain_block x"
          unfolding domain_wall_def A by auto
     moreover have "domain_block (x \<otimes> z) = domain_block x + domain_block z" 
          using domain_additive by auto
     ultimately show ?thesis by auto
   qed
   then show ?thesis by auto
 qed
 then show ?thesis by auto
 next
  fix z zs
  assume D:"xs = z * zs"
  then have "domain_wall (xs \<otimes> ys) = domain_wall xs + domain_wall ys"
   proof(cases ys)
    fix y
    assume E:"ys = basic y"
    then have "domain_wall (xs \<otimes> ys) = domain_wall xs + domain_wall ys"
    proof(cases "codomain_block y = 0")
      assume "codomain_block y = 0"
      have "(xs \<otimes> ys) = (z \<otimes> y)*zs"  
          using tensor.simps(2)  D E \<open>codomain_block y = 0\<close> by auto 
      then have "domain_wall (xs \<otimes> ys) = domain_block (z \<otimes> y)" 
          by auto
      moreover have "domain_wall xs = domain_block z"
          unfolding domain_wall_def D by auto
      moreover have "domain_wall ys = domain_block y"
          unfolding domain_wall_def E by auto
      moreover have "domain_block (z \<otimes> y) = domain_block z + domain_block y" 
          using domain_additive by auto
      ultimately show ?thesis by auto
    next
     assume "codomain_block y \<noteq> 0"
     have "(xs \<otimes> ys) 
               = 
                (z \<otimes> y)
                  *(zs\<otimes>(basic (make_vert_block (nat (codomain_block y)))))"
          using tensor.simps(3) D E \<open>codomain_block y \<noteq> 0\<close>  by auto
     then have "domain_wall (xs \<otimes> ys) = domain_block (z \<otimes> y)"
          by auto   
     moreover have "domain_wall ys = domain_block y"
          unfolding domain_wall_def E by auto
     moreover have "domain_wall xs = domain_block z"
          unfolding domain_wall_def D by auto
     moreover have "domain_block (z \<otimes> y) = domain_block z + domain_block y" 
          using domain_additive by auto
     ultimately show ?thesis by auto
   qed
   then show ?thesis by auto
  next
   fix w ws
   assume F:"ys = w*ws"  
   have "(xs \<otimes> ys) = (z \<otimes> w) * (zs \<otimes> ws)" 
          using D F by auto
   then have "domain_wall (xs \<otimes> ys) = domain_block (z \<otimes> w)" 
          by auto 
   moreover have "domain_wall ys = domain_block w"
          unfolding domain_wall_def F by auto
   moreover have "domain_wall xs = domain_block z"
          unfolding domain_wall_def D by auto
   moreover have "domain_block (z \<otimes> w) = domain_block z + domain_block w" 
          using domain_additive by auto
   ultimately show ?thesis by auto
  qed
  then show ?thesis by auto
qed

text\<open>codomain of tensor of two walls is the sum of the respective
codomain's is shown by the following theorem\<close>

lemma tensor_codomain_wall_additivity:
 "codomain_wall (xs \<otimes> ys) = codomain_wall xs + codomain_wall ys"
proof(induction xs ys  rule:tensor.induct)
 fix xs ys
 let ?case = "(codomain_wall ((basic xs) \<otimes> (basic ys)) 
                       = (codomain_wall (basic (xs))) 
                              + (codomain_wall (basic ys)))"
 show ?case using codomain_wall.simps codomain_block.simps tensor.simps
                     by (metis codomain_additive)
next
 fix x xs y
 assume case_2:
         "codomain_block y \<noteq> 0 
           \<Longrightarrow> codomain_wall 
                (xs \<otimes> basic (make_vert_block (nat (codomain_block y)))) 
                  = codomain_wall xs 
                     + codomain_wall 
                          (basic (make_vert_block (nat (codomain_block y))))"
    
 let ?case = "codomain_wall ((x*xs)\<otimes> (basic y))
                  = (codomain_wall (x*xs)) + (codomain_wall (basic y))"
 show ?case
 proof(cases "(codomain_block y = 0)")
  case True
   have "((x*xs)\<otimes> (basic y)) =  (x \<otimes> y)*xs "
                using "Tangle_Algebra.2" True by auto 
   then have "codomain_wall ((x*xs)\<otimes> (basic y)) 
                                = codomain_wall ((x \<otimes> y)*xs)"
                by auto
   then have "... = codomain_wall xs"
                using codomain_wall.simps by auto
   then have "... = codomain_wall xs + codomain_wall (basic y)"
                using True codomain_wall.simps(1) by auto
   then show ?thesis by auto
  next
  case False
   have "(x*xs) \<otimes> (basic y) 
                 = (x \<otimes> y)
                     *(xs\<otimes>(basic (make_vert_block (nat (codomain_block y)))))"
                using False by (metis "Tangle_Algebra.2")
   moreover then have "codomain_wall ((x*xs) \<otimes> (basic y))
                      = codomain_wall(...)"
                 by auto
   moreover have "... 
                  = codomain_wall 
                      (xs\<otimes>(basic (make_vert_block (nat (codomain_block y)))))"
                 using domain_wall.simps by auto
   moreover have "... 
                  = codomain_wall xs 
                     + codomain_wall 
                          (basic (make_vert_block (nat (codomain_block y))))"
                 using case_2 False by auto
   moreover have "... = codomain_wall (x*xs)
                       + codomain_block y"
                 using codomain_wall.simps 
                 by (metis codomain_block_nonnegative   codomain_make_vert int_nat_eq)
   moreover have "... = codomain_wall (x*xs) + codomain_wall (basic y)"
                  using codomain_wall.simps(1) by auto  
   ultimately show ?thesis by auto
 qed
 next
  fix x y ys
  assume case_3:"(codomain_block x \<noteq> 0 \<Longrightarrow>
        codomain_wall 
             (basic (make_vert_block (nat (codomain_block x))) \<otimes> ys)
            = codomain_wall 
               (basic (make_vert_block (nat (codomain_block x)))) 
                  + codomain_wall ys)"
  let ?case = "codomain_wall ((basic x) \<otimes> (y*ys))
                  = codomain_wall (basic x) + codomain_wall (y*ys)"
  show ?case
   proof(cases "codomain_block x = 0")
    case True
     have "(basic x)\<otimes>(y*ys) = (x \<otimes> y)*ys"
                using True 3 by auto
     then have "codomain_wall (...) = codomain_wall (...)"
                by auto
     then have "... = codomain_wall ys"
                by auto 
     then have "... = codomain_wall ys + codomain_wall (basic x)"
                using codomain_wall.simps(1) True by auto
     then show ?thesis by auto
    next
    case False
     have "(basic x) \<otimes> (y*ys) 
                 = (x \<otimes> y)
                    *((basic (make_vert_block (nat (codomain_block x))))\<otimes> ys)"
                using False 3 by auto
     then have "codomain_wall (...) = codomain_wall (...)"
                by auto
     then have "... 
                 = codomain_wall 
                     ((basic (make_vert_block (nat (codomain_block x))))\<otimes> ys)"
                using codomain_wall.simps(2) by auto
     then have "... = codomain_block x + codomain_wall ys"
                using codomain_wall.simps case_3 False
                      codomain_block_nonnegative codomain_make_vert int_nat_eq
                by auto
     then have "... = codomain_wall (basic x) + codomain_wall (y*ys)"
                using codomain_wall.simps by auto
        then show ?thesis by (metis \<open>basic x \<otimes> y * ys = (x \<otimes> y) * (basic (make_vert_block (nat (codomain_block x))) \<otimes> ys)\<close> \<open>codomain_wall ((x \<otimes> y) * (basic (make_vert_block (nat (codomain_block x))) \<otimes> ys)) = codomain_wall (basic (make_vert_block (nat (codomain_block x))) \<otimes> ys)\<close> \<open>codomain_wall (basic (make_vert_block (nat (codomain_block x))) \<otimes> ys) = codomain_block x + codomain_wall ys\<close>)   
   qed
   next
    fix x xs y ys
    assume case_4:"codomain_wall (xs \<otimes> ys) = codomain_wall xs + codomain_wall ys "
    let ?case = "codomain_wall ((x*xs) \<otimes> (y*ys)) 
                      = codomain_wall (x*xs) + codomain_wall (y*ys)" 
    have " ((x*xs) \<otimes> (y*ys)) = (x \<otimes> y)*(xs \<otimes> ys)"
                using 4 by auto
    then have "codomain_wall (...) = codomain_wall (...)"
                by auto
    then have "... = codomain_wall (xs \<otimes> ys)"
                using codomain_wall.simps(2) by auto
    then have "... = codomain_wall xs + codomain_wall ys"
                using case_4 by auto
    then have "... = codomain_wall (x*xs) + (codomain_wall (y*ys))"
         using codomain_wall.simps(2) by auto
    then show ?case by (metis \<open>codomain_wall ((x \<otimes> y) * (xs \<otimes> ys)) = codomain_wall (xs \<otimes> ys)\<close> \<open>x * xs \<otimes> y * ys = (x \<otimes> y) * (xs \<otimes> ys)\<close> case_4)
qed

(*the following theorem tells us that 
given a tensor product of a tangle diagram with a block consisting of 
only vertical strands, it gives a tangle diagram*)

theorem is_tangle_make_vert_right:
 "(is_tangle_diagram xs) 
          \<Longrightarrow> is_tangle_diagram (xs \<otimes> (basic (make_vert_block n)))"
proof(induct xs)
 case (basic xs)
  show ?case by auto
 next
 case (prod x xs)
  have ?case 
   proof(cases n)
    case 0
     have 
        "codomain_block (x \<otimes> (make_vert_block 0)) 
               = (codomain_block x) + codomain_block(make_vert_block 0)"
            using  codomain_additive by auto
     moreover have "codomain_block (make_vert_block 0) = 0" 
            by auto
     ultimately have "codomain_block (x \<otimes> (make_vert_block 0)) = codomain_block (x)"
            by auto
     moreover have "is_tangle_diagram xs" 
          using prod.prems by (metis is_tangle_diagram.simps(2))
     then have "is_tangle_diagram ((x \<otimes> (make_vert_block 0))*xs)" 
          using is_tangle_diagram.simps(2) by (metis calculation prod.prems)
     then  have "is_tangle_diagram ((x*xs) \<otimes> (basic (make_vert_block 0)))" 
          by auto
     then show ?thesis using  "0" by (metis)
    next
    case (Suc k)
     have "codomain_block (make_vert_block (k+1)) = int (k+1)" 
         using codomain_make_vert  by auto
     then have "(nat (codomain_block (make_vert_block (k+1)))) = k+1" 
         by auto
     then have "make_vert_block (nat (codomain_block (make_vert_block (k+1)))) 
                             = make_vert_block (k+1)"
          by auto
     moreover have "codomain_wall (basic (make_vert_block (k+1)))>0" 
       using make_vert_block.simps codomain_wall.simps  Suc_eq_plus1 
       codomain_make_vert of_nat_0_less_iff zero_less_Suc
       by metis
     ultimately have 1: "(x*xs) \<otimes> (basic (make_vert_block (k+1))) 
             =  (x\<otimes>(make_vert_block (k+1)))*(xs\<otimes>(basic (make_vert_block (k+1))))" 
        using tensor.simps(2) by simp
     have "domain_wall (xs\<otimes>(basic (make_vert_block (k+1)))) 
                 = domain_wall xs + domain_wall (basic (make_vert_block (k+1)))"
            using tensor_domain_wall_additivity by auto
     then have 2: 
          "domain_wall (xs\<otimes>(basic (make_vert_block (k+1)))) 
                  = (domain_wall xs) + int (k+1)"
             using domain_make_vert domain_wall.simps(1) by auto 
     moreover have 3: "codomain_block (x \<otimes> (make_vert_block (k+1))) 
                 = codomain_block x + int (k+1)"
             using  codomain_additive codomain_make_vert by (metis)
     have "is_tangle_diagram (x*xs)"
            using prod.prems by auto
     then have 4:"codomain_block x = domain_wall xs"
            using is_tangle_diagram.simps(2) by metis
     from 2 3 4 have 
       "domain_wall (xs\<otimes>(basic (make_vert_block (k+1)))) 
               = codomain_block (x \<otimes> (make_vert_block (k+1))) "
            by auto
     moreover have "is_tangle_diagram (xs\<otimes>(basic (make_vert_block (k+1))))"
            using prod.hyps prod.prems by (metis Suc Suc_eq_plus1 is_tangle_diagram.simps(2))
     ultimately have "is_tangle_diagram ((x*xs) \<otimes> (basic (make_vert_block (k+1))))"
                using 1 by auto
     then show ?thesis using  Suc Suc_eq_plus1 by metis
   qed
   then show ?case by auto
 qed

(*the following theorem tells us that given a tensor product of a vertical strand block with a 
tangle diagram, it gives a tangle diagram. If the above result can be treated as right product, 
this can be treated as the left product*)

theorem is_tangle_make_vert_left:
 "(is_tangle_diagram xs) \<Longrightarrow> is_tangle_diagram ((basic (make_vert_block n)) \<otimes> xs)"
proof(induct xs)
 case (basic xs)
  show ?case by auto
 next
 case (prod x xs)
  have ?case 
  proof(cases n)
   case 0
    have 
        "codomain_block ( (make_vert_block 0) \<otimes> x) 
               = (codomain_block x) + codomain_block(make_vert_block 0)"
            using  codomain_additive by auto
    moreover have "codomain_block (make_vert_block 0) = 0" 
            by auto
    ultimately have "codomain_block ( (make_vert_block 0) \<otimes> x) = codomain_block (x)"
            by auto
    moreover have "is_tangle_diagram xs" 
          using prod.prems by (metis is_tangle_diagram.simps(2))
    then have "is_tangle_diagram (( (make_vert_block 0) \<otimes> x)*xs)" 
          using is_tangle_diagram.simps(2) by (metis calculation prod.prems)
    then  have "is_tangle_diagram ((basic (make_vert_block 0)) \<otimes> (x*xs) )" 
          by auto
    then show ?thesis using  "0" by (metis)
   next
   case (Suc k)
    have "codomain_block (make_vert_block (k+1)) = int (k+1)" 
         using codomain_make_vert  by auto
    then have "(nat (codomain_block (make_vert_block (k+1)))) = k+1" 
         by auto
    then have "make_vert_block (nat (codomain_block (make_vert_block (k+1)))) 
                             = make_vert_block (k+1)"
         by auto
    moreover have "codomain_wall (basic (make_vert_block (k+1)))>0" 
        using make_vert_block.simps codomain_wall.simps  Suc_eq_plus1 
              codomain_make_vert of_nat_0_less_iff zero_less_Suc
        by metis
    ultimately have 1: "  (basic (make_vert_block (k+1))) \<otimes> (x*xs)
             =  ((make_vert_block (k+1)) \<otimes> x)*((basic (make_vert_block (k+1))) \<otimes> xs)" 
        using tensor.simps(3) by simp
    have "domain_wall ((basic (make_vert_block (k+1))) \<otimes> xs) 
                 = domain_wall xs + domain_wall (basic (make_vert_block (k+1)))"
        using tensor_domain_wall_additivity by auto
    then have 2: 
          "domain_wall ((basic (make_vert_block (k+1))) \<otimes> xs) 
                  = (domain_wall xs) + int (k+1)"
        using domain_make_vert domain_wall.simps(1) by auto 
    moreover have 3: "codomain_block ( (make_vert_block (k+1)) \<otimes> x) 
                 = codomain_block x + int (k+1)"
         using  codomain_additive codomain_make_vert
         by (simp add: codomain_additive)
    have "is_tangle_diagram (x*xs)"
         using prod.prems by auto
    then have 4:"codomain_block x = domain_wall xs"
            using is_tangle_diagram.simps(2) by metis
    from 2 3 4 have 
       "domain_wall ((basic (make_vert_block (k+1))) \<otimes> xs) 
               = codomain_block ((make_vert_block (k+1)) \<otimes> x)"
            by auto
    moreover have "is_tangle_diagram ((basic (make_vert_block (k+1))) \<otimes> xs)"
            using prod.hyps prod.prems by (metis Suc Suc_eq_plus1 is_tangle_diagram.simps(2))
    ultimately have "is_tangle_diagram ((basic (make_vert_block (k+1))) \<otimes> (x*xs))"
                using 1 by auto
    then show ?thesis using  Suc Suc_eq_plus1 by metis
  qed
  then show ?case by auto
qed


(*We prove that tensor product of two tangle diagrams is a tangle diagram . 
The following lemmas are used in the process of proving each of the 
inductive cases*)
lemma simp1: "(codomain_block y) \<noteq> 0 \<Longrightarrow>
       is_tangle_diagram (xs) 
\<and> is_tangle_diagram ((basic (make_vert_block (nat (codomain_block y))))) \<longrightarrow>
               is_tangle_diagram (xs \<otimes>  ((basic (make_vert_block (nat (codomain_block y)))))) \<Longrightarrow>
(is_tangle_diagram (x * xs) \<and> is_tangle_diagram (basic y) \<longrightarrow> is_tangle_diagram (x * xs \<otimes> basic y))
"
proof-
 assume A: "(codomain_block y) \<noteq> 0"
 assume B: 
     " is_tangle_diagram (xs) 
     \<and> is_tangle_diagram ((basic (make_vert_block (nat (codomain_block y))))) 
      \<longrightarrow>
       is_tangle_diagram (xs \<otimes>  ((basic (make_vert_block (nat (codomain_block y))))))"
 have " is_tangle_diagram (x * xs) \<and> is_tangle_diagram (basic y) \<longrightarrow> is_tangle_diagram xs"
        by (metis is_tangle_diagram.simps(2))
 moreover have "(is_tangle_diagram (basic (make_vert_block (nat (codomain_block y))))) "
        using is_tangle_diagram.simps(1) by auto
 ultimately have 
   " ((is_tangle_diagram xs)
   \<and>(is_tangle_diagram (basic (make_vert_block (nat (codomain_block y))))) 
    \<longrightarrow> is_tangle_diagram (xs \<otimes> basic (make_vert_block (nat (codomain_block y)))))
      \<Longrightarrow>     
       is_tangle_diagram (x * xs) \<and> is_tangle_diagram (basic y) \<longrightarrow>
       is_tangle_diagram (xs \<otimes> basic (make_vert_block (nat (codomain_block y))))"
        by metis
  moreover have 1:"codomain_block y = domain_wall (basic (make_vert_block (nat (codomain_block y))))"
        using codomain_block_nonnegative domain_make_vert domain_wall.simps(1) int_nat_eq by auto
  moreover have 2:"is_tangle_diagram (x * xs) \<and> is_tangle_diagram (basic y) \<longrightarrow>
                 codomain_block x = domain_wall xs"
        using is_tangle_diagram.simps(2) by metis
 moreover have "codomain_block (x \<otimes> y) = codomain_block x +codomain_block y"
        using codomain_additive by auto
 moreover have "domain_wall (xs \<otimes> (basic (make_vert_block (nat (codomain_block y)))))
                 = domain_wall xs + domain_wall (basic (make_vert_block (nat (codomain_block y))))"
        using tensor_domain_wall_additivity by auto
 moreover then have " is_tangle_diagram (x * xs) \<and> is_tangle_diagram (basic y) \<longrightarrow>
          domain_wall (xs \<otimes> (basic (make_vert_block (nat (codomain_block y)))))
                   = codomain_block (x \<otimes> y)"
        by (metis "1" "2" calculation(4))
 ultimately have 
      "(is_tangle_diagram xs)
      \<and> (is_tangle_diagram (basic (make_vert_block (nat (codomain_block y))))) 
       \<longrightarrow> is_tangle_diagram (xs \<otimes> basic (make_vert_block (nat (codomain_block y))))
       \<Longrightarrow> 
         is_tangle_diagram (x * xs) \<and> is_tangle_diagram (basic y) \<longrightarrow>
         is_tangle_diagram ((x \<otimes> y)* (xs \<otimes> (basic (make_vert_block (nat (codomain_block y))))))"
        using is_tangle_diagram.simps(2)  by auto
 then have "
       is_tangle_diagram (x * xs) \<and> is_tangle_diagram (basic y) \<longrightarrow>
               is_tangle_diagram ((x*xs) \<otimes> (basic y))"
        by (metis "Tangle_Algebra.2" \<open>
        codomain_block y \<noteq> 0\<close> is_tangle_make_vert_right)           
 then show ?thesis by auto
qed


lemma simp2: 
 "(codomain_block x) \<noteq> 0 
 \<Longrightarrow>
   is_tangle_diagram  (basic (make_vert_block (nat (codomain_block x)))) 
 \<and> is_tangle_diagram (ys)
    \<longrightarrow>
      is_tangle_diagram ((basic (make_vert_block (nat (codomain_block x)))) \<otimes> ys) 
     \<Longrightarrow>
    (is_tangle_diagram (basic x) 
   \<and> is_tangle_diagram (y*ys) 
         \<longrightarrow> is_tangle_diagram ((basic x) \<otimes> (y*ys)))"
proof-
 assume A: "(codomain_block x) \<noteq> 0"
 assume B: "is_tangle_diagram  (basic (make_vert_block (nat (codomain_block x)))) 
            \<and> is_tangle_diagram (ys) \<longrightarrow>
              is_tangle_diagram 
                            ((basic (make_vert_block (nat (codomain_block x)))) \<otimes> ys)"
 have " is_tangle_diagram (basic x) \<and> is_tangle_diagram (y*ys) 
                                               \<longrightarrow> is_tangle_diagram ys"
        by (metis is_tangle_diagram.simps(2))
 moreover have "(is_tangle_diagram 
                          (basic (make_vert_block (nat (codomain_block x))))) "
        using is_tangle_diagram.simps(1) by auto
 ultimately have 
      " ((is_tangle_diagram ys)
               \<and>(is_tangle_diagram (basic (make_vert_block (nat (codomain_block x))))) 
    \<longrightarrow> is_tangle_diagram ((basic (make_vert_block (nat (codomain_block x)))) \<otimes> ys))
    \<Longrightarrow>     
     is_tangle_diagram (basic x) \<and> is_tangle_diagram (y*ys) \<longrightarrow>
                is_tangle_diagram 
                        (( basic (make_vert_block (nat (codomain_block x)))) \<otimes> ys)"
        by metis
 moreover have 1:"codomain_block x 
                         = domain_wall (basic (make_vert_block (nat (codomain_block x))))"
        using codomain_block_nonnegative domain_make_vert domain_wall.simps(1) 
              int_nat_eq by auto
 moreover have 2:"is_tangle_diagram (basic x) \<and> is_tangle_diagram (y*ys) \<longrightarrow>
                 codomain_block y = domain_wall ys"
        using is_tangle_diagram.simps(2) by metis
 moreover have "codomain_block (x \<otimes> y) = codomain_block x +codomain_block y"
        using codomain_additive by auto
 moreover have "domain_wall ((basic (make_vert_block (nat (codomain_block x)))) \<otimes> ys)
                 = domain_wall (basic (make_vert_block (nat (codomain_block x)))) 
                   + domain_wall ys"
        using tensor_domain_wall_additivity by auto
 moreover then have " is_tangle_diagram (basic x) \<and> is_tangle_diagram (y*ys) \<longrightarrow>
          domain_wall ((basic (make_vert_block (nat (codomain_block x)))) \<otimes> ys)
                   = codomain_block (x \<otimes> y)"
        by (metis "1" "2" calculation(4))
 ultimately have 
      "(is_tangle_diagram ys)
      \<and> (is_tangle_diagram (basic (make_vert_block (nat (codomain_block x))))) 
        \<longrightarrow> is_tangle_diagram ((basic (make_vert_block (nat (codomain_block x))))\<otimes> ys)
         \<Longrightarrow>
          is_tangle_diagram (basic x) \<and> is_tangle_diagram (y*ys) 
          \<longrightarrow>
          is_tangle_diagram ((x \<otimes> y)*((basic (make_vert_block (nat (codomain_block x)))) \<otimes> ys))"
        using is_tangle_diagram.simps(2)  by auto
 then have "
       is_tangle_diagram (basic x) \<and> is_tangle_diagram (y*ys) \<longrightarrow>
               is_tangle_diagram ((basic x) \<otimes> (y*ys))"
        by (metis "Tangle_Algebra.3" A B)
 then show ?thesis by auto
qed

lemma simp3: 
 "is_tangle_diagram xs \<and> is_tangle_diagram ys \<longrightarrow> is_tangle_diagram (xs \<otimes> ys) 
 \<Longrightarrow>
     is_tangle_diagram (x * xs) \<and> is_tangle_diagram (y * ys) 
     \<longrightarrow> is_tangle_diagram (x * xs \<otimes> y * ys)"
proof-
 assume A: "is_tangle_diagram xs \<and> is_tangle_diagram ys \<longrightarrow> is_tangle_diagram (xs \<otimes> ys)"
 have "is_tangle_diagram (x*xs) \<longrightarrow> (codomain_block x = domain_wall xs)"
       using is_tangle_diagram.simps(2) by auto
 moreover have "is_tangle_diagram (y*ys) \<longrightarrow> (codomain_block y = domain_wall ys)"
       using is_tangle_diagram.simps(2) by auto
 ultimately have "is_tangle_diagram (x*xs)\<and> is_tangle_diagram (y*ys)
              \<longrightarrow> codomain_block (x \<otimes> y) = domain_wall (xs \<otimes> ys)"
       using codomain_additive tensor_domain_wall_additivity by auto
 moreover have "is_tangle_diagram (x*xs)\<and> is_tangle_diagram (y*ys)
              \<longrightarrow> is_tangle_diagram (xs \<otimes> ys)"
       using A is_tangle_diagram.simps(2) by auto
 moreover  have "(x*xs) \<otimes> (y*ys) = (x \<otimes> y)*(xs \<otimes> ys)" 
      using tensor.simps(4) by auto 
 ultimately have "is_tangle_diagram (x*xs)\<and> is_tangle_diagram (y*ys)
              \<longrightarrow> is_tangle_diagram ((x*xs) \<otimes> (y*ys))"
      by auto
 then show ?thesis by simp
qed

(*tensor product of two tangle diagrams is a tangle diagram*)

theorem is_tangle_diagramness:
 shows"(is_tangle_diagram x)\<and>(is_tangle_diagram y) \<longrightarrow>is_tangle_diagram (tensor x y)"
proof(induction x y  rule:tensor.induct)
 fix z w
 let ?case = "(is_tangle_diagram (basic z))\<and>(is_tangle_diagram (basic w))
                  \<longrightarrow>is_tangle_diagram ((basic z) \<otimes> (basic w))"
  show ?case by auto
 next
 fix x xs y
 let ?case = "(is_tangle_diagram (x*xs))\<and>(is_tangle_diagram (basic y))
                  \<longrightarrow>is_tangle_diagram ((x*xs) \<otimes> (basic y))"
  from simp1 show ?case 
      by (metis "Tangle_Algebra.2" add.commute codomain_additive comm_monoid_add_class.add_0 
                is_tangle_diagram.simps(2) is_tangle_make_vert_right)
 next 
 fix x y ys
 let ?case = "(is_tangle_diagram (basic x))\<and>(is_tangle_diagram (y*ys))
                  \<longrightarrow>is_tangle_diagram ((basic x) \<otimes> (y*ys))"
  from simp2 show ?case 
        by (metis "Tangle_Algebra.3" codomain_additive comm_monoid_add_class.add_0 
                   is_tangle_diagram.simps(2) is_tangle_make_vert_left)
 next
 fix x y xs ys
 assume A:"  is_tangle_diagram xs \<and> is_tangle_diagram ys \<longrightarrow> is_tangle_diagram (xs \<otimes> ys)"
 let ?case =    
    "is_tangle_diagram (x * xs) \<and> is_tangle_diagram (y * ys) \<longrightarrow> is_tangle_diagram (x * xs \<otimes> y * ys)"
  from simp3 show ?case using A by auto
qed
   
theorem tensor_preserves_is_tangle: 
 assumes "is_tangle_diagram x"
     and "is_tangle_diagram y"
 shows "is_tangle_diagram (x \<otimes> y)"
  using assms  is_tangle_diagramness by auto

definition Tensor_Tangle::"Tangle_Diagram \<Rightarrow> Tangle_Diagram \<Rightarrow> Tangle_Diagram" 
          (infixl "\<circ>" 65)
 where
"Tensor_Tangle x y = 
     Abs_Tangle_Diagram ((Rep_Tangle_Diagram x) \<otimes> (Rep_Tangle_Diagram y))"


theorem well_defined_compose: 
 assumes "is_tangle_diagram x" 
     and "is_tangle_diagram y"
 shows "(Abs_Tangle_Diagram x) \<otimes> (Abs_Tangle_Diagram y) = (Abs_Tangle_Diagram (x \<otimes> y))"
     using  Abs_Tangle_Diagram_inverse assms(1) assms(2) 
      mem_Collect_eq tensor_preserves_is_tangle
     tensor_Tangle_def 
     by auto


end
