(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>Arithmetics via Records\<close>

text \<open>We create a locale for rings and fields based on a record 
  that includes all the necessary operations.\<close>

theory Arithmetic_Record_Based
imports 
  "HOL-Library.More_List"
  "HOL-Computational_Algebra.Euclidean_Algorithm"
begin
datatype 'a arith_ops_record = Arith_Ops_Record
  (zero : 'a)
  (one  : 'a)
  (plus : "'a \<Rightarrow> 'a \<Rightarrow> 'a")
  (times : "'a \<Rightarrow> 'a \<Rightarrow> 'a")
  (minus : "'a \<Rightarrow> 'a \<Rightarrow> 'a")
  (uminus : "'a \<Rightarrow> 'a")
  (divide : "'a \<Rightarrow> 'a \<Rightarrow> 'a")
  (inverse : "'a \<Rightarrow> 'a")
  ("modulo" : "'a \<Rightarrow> 'a \<Rightarrow> 'a")
  (normalize : "'a \<Rightarrow> 'a")
  (unit_factor : "'a \<Rightarrow> 'a")
  (of_int : "int \<Rightarrow> 'a")
  (to_int : "'a \<Rightarrow> int")
  (DP : "'a \<Rightarrow> bool")

hide_const (open) 
  zero 
  one  
  plus 
  times
  minus
  uminus 
  divide
  inverse
  modulo
  normalize
  unit_factor
  of_int
  to_int
  DP

fun listprod_i :: "'i arith_ops_record \<Rightarrow> 'i list \<Rightarrow> 'i" where
  "listprod_i ops (x # xs) = arith_ops_record.times ops x (listprod_i ops xs)"
| "listprod_i ops [] = arith_ops_record.one ops"

locale arith_ops = fixes ops :: "'i arith_ops_record" (structure)
begin

abbreviation (input) zero where "zero \<equiv> arith_ops_record.zero ops"
abbreviation (input) one where "one \<equiv> arith_ops_record.one ops"
abbreviation (input) plus where "plus \<equiv> arith_ops_record.plus ops"
abbreviation (input) times where "times \<equiv> arith_ops_record.times ops"
abbreviation (input) minus where "minus \<equiv> arith_ops_record.minus ops"
abbreviation (input) uminus where "uminus \<equiv> arith_ops_record.uminus ops"
abbreviation (input) divide where "divide \<equiv> arith_ops_record.divide ops"
abbreviation (input) inverse where "inverse \<equiv> arith_ops_record.inverse ops"
abbreviation (input) modulo where "modulo \<equiv> arith_ops_record.modulo ops"
abbreviation (input) normalize where "normalize \<equiv> arith_ops_record.normalize ops"
abbreviation (input) unit_factor where "unit_factor \<equiv> arith_ops_record.unit_factor ops"
abbreviation (input) DP where "DP \<equiv> arith_ops_record.DP ops"


partial_function (tailrec) gcd_eucl_i :: "'i \<Rightarrow> 'i \<Rightarrow> 'i" where
  "gcd_eucl_i a b = (if b = zero 
    then normalize a else gcd_eucl_i b (modulo a b))"

partial_function (tailrec) euclid_ext_aux_i :: "'i \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> ('i \<times> 'i) \<times> 'i" where
  "euclid_ext_aux_i s' s t' t r' r = (
     if r = zero then let c = divide one (unit_factor r') in ((times s' c, times t' c), normalize r')
     else let q = divide r' r
          in  euclid_ext_aux_i s (minus s' (times q s)) t (minus t' (times q t)) r (modulo r' r))"

abbreviation (input) euclid_ext_i :: "'i \<Rightarrow> 'i \<Rightarrow> ('i \<times> 'i) \<times> 'i" where 
  "euclid_ext_i \<equiv> euclid_ext_aux_i one zero zero one" 

end

declare arith_ops.gcd_eucl_i.simps[code]
declare arith_ops.euclid_ext_aux_i.simps[code]
 
unbundle lifting_syntax
                                                       
locale ring_ops = arith_ops ops for ops :: "'i arith_ops_record" +
  fixes R :: "'i \<Rightarrow> 'a :: comm_ring_1 \<Rightarrow> bool" 
  assumes bi_unique[transfer_rule]: "bi_unique R" 
  and right_total[transfer_rule]: "right_total R"
  and zero[transfer_rule]: "R zero 0"
  and one[transfer_rule]: "R one 1"
  and plus[transfer_rule]: "(R ===> R ===> R) plus (+)"
  and minus[transfer_rule]: "(R ===> R ===> R) minus (-)"
  and uminus[transfer_rule]: "(R ===> R) uminus Groups.uminus"
  and times[transfer_rule]: "(R ===> R ===> R) times ((*))"
  and eq[transfer_rule]: "(R ===> R ===> (=)) (=) (=)"
  and DPR[transfer_domain_rule]: "Domainp R = DP" 
begin
lemma left_right_unique[transfer_rule]: "left_unique R" "right_unique R"
  using bi_unique unfolding bi_unique_def left_unique_def right_unique_def by auto

lemma listprod_i[transfer_rule]: "(list_all2 R ===> R) (listprod_i ops) prod_list"
proof (intro rel_funI, goal_cases)
  case (1 xs ys)
  thus ?case 
  proof (induct xs ys rule: list_all2_induct)
    case (Cons x xs y ys)
    note [transfer_rule] = this
    show ?case by simp transfer_prover
  qed (simp add: one)
qed
end

locale idom_ops = ring_ops ops R for ops :: "'i arith_ops_record" and
  R :: "'i \<Rightarrow> 'a :: idom \<Rightarrow> bool"

locale idom_divide_ops = idom_ops ops R for ops :: "'i arith_ops_record" and
  R :: "'i \<Rightarrow> 'a :: idom_divide \<Rightarrow> bool" +
  assumes divide[transfer_rule]: "(R ===> R ===> R) divide Rings.divide"  

locale euclidean_semiring_ops = idom_ops ops R for ops :: "'i arith_ops_record" and
  R :: "'i \<Rightarrow> 'a :: {idom,normalization_euclidean_semiring} \<Rightarrow> bool"  +
  assumes modulo[transfer_rule]: "(R ===> R ===> R) modulo (mod)"
    and normalize[transfer_rule]: "(R ===> R) normalize Rings.normalize"
    and unit_factor[transfer_rule]: "(R ===> R) unit_factor Rings.unit_factor"
begin
lemma gcd_eucl_i [transfer_rule]: "(R ===> R ===> R) gcd_eucl_i Euclidean_Algorithm.gcd" 
proof (intro rel_funI, goal_cases)
  case (1 x X y Y)
  thus ?case
  proof (induct X Y arbitrary: x y rule: Euclidean_Algorithm.gcd.induct)
    case (1 X Y x y)
    note [transfer_rule] = 1(2-)
    note simps = gcd_eucl_i.simps[of x y] Euclidean_Algorithm.gcd.simps[of X Y]
    have eq: "(y = zero) = (Y = 0)" by transfer_prover
    show ?case
    proof (cases "Y = 0")
      case True
      hence *: "y = zero" using eq by simp
      have "R (normalize x) (Rings.normalize X)" by transfer_prover
      thus ?thesis unfolding simps unfolding True * by simp
    next
      case False
      with eq have yz: "y \<noteq> zero" by simp
      have "R (gcd_eucl_i y (modulo x y)) (Euclidean_Algorithm.gcd Y (X mod Y))"
        by (rule 1(1)[OF False], transfer_prover+)
      thus ?thesis unfolding simps using False yz by simp
    qed
  qed
qed
end

locale euclidean_ring_ops = euclidean_semiring_ops ops R for ops :: "'i arith_ops_record" and
  R :: "'i \<Rightarrow> 'a :: {idom,euclidean_ring_gcd} \<Rightarrow> bool"  +
  assumes divide[transfer_rule]: "(R ===> R ===> R) divide (div)"
begin
lemma euclid_ext_aux_i[transfer_rule]: 
  "(R ===> R ===> R ===> R ===> R ===> R ===> rel_prod (rel_prod R R) R) euclid_ext_aux_i euclid_ext_aux"
proof (intro rel_funI, goal_cases)
  case (1 z Z a A b B c C x X y Y)
  thus ?case
  proof (induct Z A B C X Y arbitrary: z a b c x y rule: euclid_ext_aux.induct)
    case (1 Z A B C X Y z a b c x y)
    note [transfer_rule] = 1(2-)
    note simps = euclid_ext_aux_i.simps[of z a b c x y] euclid_ext_aux.simps[of Z A B C X Y]
    have eq: "(y = zero) = (Y = 0)" by transfer_prover
    show ?case
    proof (cases "Y = 0")
      case True
      hence *: "(y = zero) = True" "(Y = 0) = True" using eq by auto
      show ?thesis unfolding simps unfolding * if_True
        by transfer_prover
    next
      case False
      hence *: "(y = zero) = False" "(Y = 0) = False" using eq by auto
      have XY: "R (modulo x y) (X mod Y)" by transfer_prover
      have YA: "R (minus z (times (divide x y) a)) (Z - X div Y * A)" by transfer_prover
      have YC: "R (minus b (times (divide x y) c)) (B - X div Y * C)" by transfer_prover
      note [transfer_rule] = 1(1)[OF False refl 1(3) YA 1(5) YC 1(7) XY]

      show ?thesis unfolding simps * if_False Let_def by transfer_prover
    qed
  qed
qed

lemma euclid_ext_i [transfer_rule]:
  "(R ===> R ===> rel_prod (rel_prod R R) R) euclid_ext_i euclid_ext"
  by transfer_prover

end

locale field_ops = idom_divide_ops ops R + euclidean_semiring_ops ops R for ops :: "'i arith_ops_record" and
  R :: "'i \<Rightarrow> 'a :: {field, normalization_euclidean_semiring, euclidean_ring, factorial_ring_gcd} \<Rightarrow> bool" +
  assumes inverse[transfer_rule]: "(R ===> R) inverse Fields.inverse"
  

lemma nth_default_rel[transfer_rule]: "(S ===> list_all2 S ===> (=) ===> S) nth_default nth_default"
proof (intro rel_funI, clarify, goal_cases)
  case (1 x y xs ys _ n)
  from 1(2) show ?case
  proof (induct arbitrary: n)
    case Nil
    thus ?case using 1(1) by simp
  next
    case (Cons x y xs ys n)
    thus ?case by (cases n, auto)
  qed
qed

lemma strip_while_rel[transfer_rule]: 
  "((A ===> (=)) ===> list_all2 A ===> list_all2 A) strip_while strip_while"
  unfolding strip_while_def[abs_def] by transfer_prover

lemma list_all2_last[simp]: "list_all2 A (xs @ [x]) (ys @ [y]) \<longleftrightarrow> list_all2 A xs ys \<and> A x y"
proof (cases "length xs = length ys")
  case True
  show ?thesis by (simp add: list_all2_append[OF True])
next
  case False
  note len = list_all2_lengthD[of A]
  from len[of xs ys] len[of "xs @ [x]" "ys @ [y]"] False
  show ?thesis by auto 
qed  


end
