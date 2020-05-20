(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Finite Fields\<close>

text \<open>We provide four implementations for $GF(p)$ -- the field with $p$ elements for some
  prime $p$ -- one by int, one by integers, one by 32-bit numbers and one 64-bit implementation. 
  Correctness of the implementations is proven by
  transfer rules to the type-based version of $GF(p)$.\<close>

theory Finite_Field_Record_Based
imports
  Finite_Field
  Arithmetic_Record_Based
  Native_Word.Uint32 
  Native_Word.Uint64
  Native_Word.Code_Target_Bits_Int
  "HOL-Library.Code_Target_Numeral"  
begin

(* mod on standard case which can immediately be mapped to 
   target languages without considering special cases *)
definition mod_nonneg_pos :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "x \<ge> 0 \<Longrightarrow> y > 0 \<Longrightarrow> mod_nonneg_pos x y = (x mod y)"
  
code_printing \<comment> \<open>FIXME illusion of partiality\<close>
  constant mod_nonneg_pos \<rightharpoonup>
        (SML) "IntInf.mod/ ( _,/ _ )"
    and (Eval) "IntInf.mod/ ( _,/ _ )"
    and (OCaml) "Z.rem"
    and (Haskell) "Prelude.mod/ ( _ )/ ( _ )"
    and (Scala) "!((k: BigInt) => (l: BigInt) =>/ (k '% l))"

definition mod_nonneg_pos_int :: "int \<Rightarrow> int \<Rightarrow> int" where
  "mod_nonneg_pos_int x y = int_of_integer (mod_nonneg_pos (integer_of_int x) (integer_of_int y))" 

lemma mod_nonneg_pos_int[simp]: "x \<ge> 0 \<Longrightarrow> y > 0 \<Longrightarrow> mod_nonneg_pos_int x y = (x mod y)" 
  unfolding mod_nonneg_pos_int_def using mod_nonneg_pos_def by simp

context
  fixes p :: int
begin
definition plus_p :: "int \<Rightarrow> int \<Rightarrow> int" where
  "plus_p x y \<equiv> let z = x + y in if z \<ge> p then z - p else z"

definition minus_p :: "int \<Rightarrow> int \<Rightarrow> int" where
  "minus_p x y \<equiv> if y \<le> x then x - y else x + p - y"

definition uminus_p :: "int \<Rightarrow> int" where
  "uminus_p x = (if x = 0 then 0 else p - x)"

definition mult_p :: "int \<Rightarrow> int \<Rightarrow> int" where
  "mult_p x y = (mod_nonneg_pos_int (x * y) p)"

fun power_p :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "power_p x n = (if n = 0 then 1 else
    let (d,r) = Divides.divmod_nat n 2;
       rec = power_p (mult_p x x) d in
    if r = 0 then rec else mult_p rec x)"

text \<open>In experiments with Berlekamp-factorization (where the prime $p$ is usually small),
  it turned out that taking the below implementation of inverse via exponentiation
  is faster than the one based on the extended Euclidean algorithm.\<close>

definition inverse_p :: "int \<Rightarrow> int" where
  "inverse_p x = (if x = 0 then 0 else power_p x (nat (p - 2)))"

definition divide_p :: "int \<Rightarrow> int \<Rightarrow> int"  where
  "divide_p x y = mult_p x (inverse_p y)"

definition finite_field_ops_int :: "int arith_ops_record" where
  "finite_field_ops_int \<equiv> Arith_Ops_Record
      0
      1
      plus_p
      mult_p
      minus_p
      uminus_p
      divide_p
      inverse_p
      (\<lambda> x y . if y = 0 then x else 0)
      (\<lambda> x . if x = 0 then 0 else 1)
      (\<lambda> x . x)
      (\<lambda> x . x)
      (\<lambda> x . x)
      (\<lambda> x. 0 \<le> x \<and> x < p)"

end

context
  fixes p :: uint32
begin
definition plus_p32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" where
  "plus_p32 x y \<equiv> let z = x + y in if z \<ge> p then z - p else z"

definition minus_p32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" where
  "minus_p32 x y \<equiv> if y \<le> x then x - y else (x + p) - y"

definition uminus_p32 :: "uint32 \<Rightarrow> uint32" where
  "uminus_p32 x = (if x = 0 then 0 else p - x)"

definition mult_p32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" where
  "mult_p32 x y = (x * y mod p)"

lemma int_of_uint32_shift: "int_of_uint32 (shiftr n k) = (int_of_uint32 n) div (2 ^ k)" 
  by (transfer, rule shiftr_div_2n) 

lemma int_of_uint32_0_iff: "int_of_uint32 n = 0 \<longleftrightarrow> n = 0" 
  by (transfer, rule uint_0_iff)
  
lemma int_of_uint32_0: "int_of_uint32 0 = 0" unfolding int_of_uint32_0_iff by simp

lemma int_of_uint32_ge_0: "int_of_uint32 n \<ge> 0" 
  by (transfer, auto)

lemma two_32: "2 ^ LENGTH(32) = (4294967296 :: int)" by simp

lemma int_of_uint32_plus: "int_of_uint32 (x + y) = (int_of_uint32 x + int_of_uint32 y) mod 4294967296" 
  by (transfer, unfold uint_word_ariths two_32, rule refl)  

lemma int_of_uint32_minus: "int_of_uint32 (x - y) = (int_of_uint32 x - int_of_uint32 y) mod 4294967296" 
  by (transfer, unfold uint_word_ariths two_32, rule refl)  

lemma int_of_uint32_mult: "int_of_uint32 (x * y) = (int_of_uint32 x * int_of_uint32 y) mod 4294967296" 
  by (transfer, unfold uint_word_ariths two_32, rule refl)  

lemma int_of_uint32_mod: "int_of_uint32 (x mod y) = (int_of_uint32 x mod int_of_uint32 y)" 
  by (transfer, unfold uint_mod two_32, rule refl)  

lemma int_of_uint32_inv: "0 \<le> x \<Longrightarrow> x < 4294967296 \<Longrightarrow> int_of_uint32 (uint32_of_int x) = x"
  by (transfer, simp add: int_word_uint) 

function power_p32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" where
  "power_p32 x n = (if n = 0 then 1 else
    let rec = power_p32 (mult_p32 x x) (shiftr n 1) in
    if n AND 1 = 0 then rec else mult_p32 rec x)"
  by pat_completeness auto

termination 
proof -
  {
    fix n :: uint32
    assume "n \<noteq> 0" 
    with int_of_uint32_ge_0[of n] int_of_uint32_0_iff[of n] have "int_of_uint32 n > 0" by auto
    hence "0 < int_of_uint32 n" "int_of_uint32 n div 2 < int_of_uint32 n" by auto
  } note * = this
  show ?thesis
    by (relation "measure (\<lambda> (x,n). nat (int_of_uint32 n))", auto simp: int_of_uint32_shift *) 
qed

text \<open>In experiments with Berlekamp-factorization (where the prime $p$ is usually small),
  it turned out that taking the below implementation of inverse via exponentiation
  is faster than the one based on the extended Euclidean algorithm.\<close>

definition inverse_p32 :: "uint32 \<Rightarrow> uint32" where
  "inverse_p32 x = (if x = 0 then 0 else power_p32 x (p - 2))"

definition divide_p32 :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32"  where
  "divide_p32 x y = mult_p32 x (inverse_p32 y)"

definition finite_field_ops32 :: "uint32 arith_ops_record" where
  "finite_field_ops32 \<equiv> Arith_Ops_Record
      0
      1
      plus_p32
      mult_p32
      minus_p32
      uminus_p32
      divide_p32
      inverse_p32
      (\<lambda> x y . if y = 0 then x else 0)
      (\<lambda> x . if x = 0 then 0 else 1)
      (\<lambda> x . x)
      uint32_of_int
      int_of_uint32
      (\<lambda> x. 0 \<le> x \<and> x < p)"
end 

lemma shiftr_uint32_code [code_unfold]: "shiftr x 1 = (uint32_shiftr x 1)"
  unfolding shiftr_uint32_code using integer_of_nat_1 by auto

(* ******************************************************************************** *)
subsubsection \<open>Transfer Relation\<close>
locale mod_ring_locale =
  fixes p :: int and ty :: "'a :: nontriv itself"
  assumes p: "p = int CARD('a)"
begin
lemma nat_p: "nat p = CARD('a)" unfolding p by simp
lemma p2: "p \<ge> 2" unfolding p using nontriv[where 'a = 'a] by auto
lemma p2_ident: "int (CARD('a) - 2) = p - 2" using p2 unfolding p by simp

definition mod_ring_rel :: "int \<Rightarrow> 'a mod_ring \<Rightarrow> bool" where
  "mod_ring_rel x x' = (x = to_int_mod_ring x')"

(* domain transfer rules *)
lemma Domainp_mod_ring_rel [transfer_domain_rule]:
  "Domainp (mod_ring_rel) = (\<lambda> v. v \<in> {0 ..< p})"
proof -
  {
    fix v :: int
    assume *: "0 \<le> v" "v < p"
    have "Domainp mod_ring_rel v"
    proof
      show "mod_ring_rel v (of_int_mod_ring v)" unfolding mod_ring_rel_def using * p by auto
    qed
  } note * = this
  show ?thesis
    by (intro ext iffI, insert range_to_int_mod_ring[where 'a = 'a] *, auto simp: mod_ring_rel_def p)
qed

(* left/right/bi-unique *)
lemma bi_unique_mod_ring_rel [transfer_rule]:
  "bi_unique mod_ring_rel" "left_unique mod_ring_rel" "right_unique mod_ring_rel"
  unfolding mod_ring_rel_def bi_unique_def left_unique_def right_unique_def
  by auto

(* left/right-total *)
lemma right_total_mod_ring_rel [transfer_rule]: "right_total mod_ring_rel"
  unfolding mod_ring_rel_def right_total_def by simp


(* ************************************************************************************ *)
subsubsection \<open>Transfer Rules\<close>

(* 0 / 1 *)
lemma mod_ring_0[transfer_rule]: "mod_ring_rel 0 0" unfolding mod_ring_rel_def by simp
lemma mod_ring_1[transfer_rule]: "mod_ring_rel 1 1" unfolding mod_ring_rel_def by simp

(* addition *)
lemma plus_p_mod_def: assumes x: "x \<in> {0 ..< p}" and y: "y \<in> {0 ..< p}"
  shows "plus_p p x y = ((x + y) mod p)"
proof (cases "p \<le> x + y")
  case False
  thus ?thesis using x y unfolding plus_p_def Let_def by auto
next
  case True
  from True x y have *: "p > 0" "0 \<le> x + y - p" "x + y - p < p" by auto
  from True have id: "plus_p p x y = x + y - p" unfolding plus_p_def by auto
  show ?thesis unfolding id using * using mod_pos_pos_trivial by fastforce
qed

lemma mod_ring_plus[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel ===> mod_ring_rel) (plus_p p) (+)"
proof -
  {
    fix x y :: "'a mod_ring"
    have "plus_p p (to_int_mod_ring x) (to_int_mod_ring y) = to_int_mod_ring (x + y)"
      by (transfer, subst plus_p_mod_def, auto, auto simp: p)
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *)
qed

(* subtraction *)
lemma minus_p_mod_def: assumes x: "x \<in> {0 ..< p}" and y: "y \<in> {0 ..< p}"
  shows "minus_p p x y = ((x - y) mod p)"
proof (cases "x - y < 0")
  case False
  thus ?thesis using x y unfolding minus_p_def Let_def by auto
next
  case True
  from True x y have *: "p > 0" "0 \<le> x - y + p" "x - y + p < p" by auto
  from True have id: "minus_p p x y = x - y + p" unfolding minus_p_def by auto
  show ?thesis unfolding id using * using mod_pos_pos_trivial by fastforce
qed

lemma mod_ring_minus[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel ===> mod_ring_rel) (minus_p p) (-)"
proof -
  {
    fix x y :: "'a mod_ring"
    have "minus_p p (to_int_mod_ring x) (to_int_mod_ring y) = to_int_mod_ring (x - y)"
      by (transfer, subst minus_p_mod_def, auto simp: p)
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *)
qed

(* unary minus *)
lemma mod_ring_uminus[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel) (uminus_p p) uminus"
proof -
  {
    fix x :: "'a mod_ring"
    have "uminus_p p (to_int_mod_ring x) = to_int_mod_ring (uminus x)"
      by (transfer, auto simp: uminus_p_def p)
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *)
qed

(* multiplication *)
lemma mod_ring_mult[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel ===> mod_ring_rel) (mult_p p) ((*))"
proof -
  {
    fix x y :: "'a mod_ring"
    have "mult_p p (to_int_mod_ring x) (to_int_mod_ring y) = to_int_mod_ring (x * y)"
      by (transfer, auto simp: mult_p_def p)
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *)
qed

(* equality *)
lemma mod_ring_eq[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel ===> (=)) (=) (=)"
  by (intro rel_funI, auto simp: mod_ring_rel_def)

(* power *)
lemma mod_ring_power[transfer_rule]: "(mod_ring_rel ===> (=) ===> mod_ring_rel) (power_p p) (^)"
proof (intro rel_funI, clarify, unfold binary_power[symmetric], goal_cases)
  fix x y n
  assume xy: "mod_ring_rel x y"
  from xy show "mod_ring_rel (power_p p x n) (binary_power y n)"
  proof (induct y n arbitrary: x rule: binary_power.induct)
    case (1 x n y)
    note 1(2)[transfer_rule]
    show ?case
    proof (cases "n = 0")
      case True
      thus ?thesis by (simp add: mod_ring_1)
    next
      case False
      obtain d r where id: "Divides.divmod_nat n 2 = (d,r)" by force
      let ?int = "power_p p (mult_p p y y) d"
      let ?gfp = "binary_power (x * x) d"
      from False have id': "?thesis = (mod_ring_rel
         (if r = 0 then ?int else mult_p p ?int y)
         (if r = 0 then ?gfp else ?gfp * x))"
        unfolding power_p.simps[of _ _ n] binary_power.simps[of _ n] Let_def id split by simp
      have [transfer_rule]: "mod_ring_rel ?int ?gfp"
        by (rule 1(1)[OF False refl id[symmetric]], transfer_prover)
      show ?thesis unfolding id' by transfer_prover
    qed
  qed
qed

declare power_p.simps[simp del]

lemma ring_finite_field_ops_int: "ring_ops (finite_field_ops_int p) mod_ring_rel"
  by (unfold_locales, auto simp:
  finite_field_ops_int_def
  bi_unique_mod_ring_rel
  right_total_mod_ring_rel
  mod_ring_plus
  mod_ring_minus
  mod_ring_uminus
  mod_ring_mult
  mod_ring_eq
  mod_ring_0
  mod_ring_1
  Domainp_mod_ring_rel)
end

locale prime_field = mod_ring_locale p ty for p and ty :: "'a :: prime_card itself"
begin

lemma prime: "prime p" unfolding p using prime_card[where 'a = 'a] by simp

(* mod *)
lemma mod_ring_mod[transfer_rule]:
 "(mod_ring_rel ===> mod_ring_rel ===> mod_ring_rel) ((\<lambda> x y. if y = 0 then x else 0)) (mod)"
proof -
  {
    fix x y :: "'a mod_ring"
    have "(if to_int_mod_ring y = 0 then to_int_mod_ring x else 0) = to_int_mod_ring (x mod y)"
      unfolding modulo_mod_ring_def by auto
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *[symmetric])
qed

(* normalize *)
lemma mod_ring_normalize[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel) ((\<lambda> x. if x = 0 then 0 else 1)) normalize"
proof -
  {
    fix x :: "'a mod_ring"
    have "(if to_int_mod_ring x = 0 then 0 else 1) = to_int_mod_ring (normalize x)"
      unfolding normalize_mod_ring_def by auto
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *[symmetric])
qed

(* unit_factor *)
lemma mod_ring_unit_factor[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel) (\<lambda> x. x) unit_factor"
proof -
  {
    fix x :: "'a mod_ring"
    have "to_int_mod_ring x = to_int_mod_ring (unit_factor x)"
      unfolding unit_factor_mod_ring_def by auto
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *[symmetric])
qed

(* inverse *)
lemma mod_ring_inverse[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel) (inverse_p p) inverse"
proof (intro rel_funI)
  fix x y
  assume [transfer_rule]: "mod_ring_rel x y"
  show "mod_ring_rel (inverse_p p x) (inverse y)"
    unfolding inverse_p_def inverse_mod_ring_def
    apply (transfer_prover_start)
    apply (transfer_step)+
    apply (unfold p2_ident)
    apply (rule refl)
    done
qed

(* division *)
lemma mod_ring_divide[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel ===> mod_ring_rel)
  (divide_p p) (/)"
  unfolding divide_p_def[abs_def] divide_mod_ring_def[abs_def] inverse_mod_ring_def[symmetric]
  by transfer_prover

lemma mod_ring_rel_unsafe: assumes "x < CARD('a)"
  shows "mod_ring_rel (int x) (of_nat x)" "0 < x \<Longrightarrow> of_nat x \<noteq> (0 :: 'a mod_ring)"
proof -
  have id: "of_nat x = (of_int (int x) :: 'a mod_ring)" by simp
  show "mod_ring_rel (int x) (of_nat x)" "0 < x \<Longrightarrow> of_nat x \<noteq> (0 :: 'a mod_ring)" unfolding id
  unfolding mod_ring_rel_def
  proof (auto simp add: assms of_int_of_int_mod_ring)
    assume "0 < x" with assms
    have "of_int_mod_ring (int x) \<noteq> (0 :: 'a mod_ring)"
      by (metis (no_types) less_imp_of_nat_less less_irrefl of_nat_0_le_iff of_nat_0_less_iff to_int_mod_ring_hom.hom_zero to_int_mod_ring_of_int_mod_ring)
    thus "of_int_mod_ring (int x) = (0 :: 'a mod_ring) \<Longrightarrow> False" by blast
  qed
qed

lemma finite_field_ops_int: "field_ops (finite_field_ops_int p) mod_ring_rel"
  by (unfold_locales, auto simp:
  finite_field_ops_int_def
  bi_unique_mod_ring_rel
  right_total_mod_ring_rel
  mod_ring_divide
  mod_ring_plus
  mod_ring_minus
  mod_ring_uminus
  mod_ring_inverse
  mod_ring_mod
  mod_ring_unit_factor
  mod_ring_normalize
  mod_ring_mult
  mod_ring_eq
  mod_ring_0
  mod_ring_1
  Domainp_mod_ring_rel)

end

text \<open>Once we have proven the soundness of the implementation, we do not care any longer
  that @{typ "'a mod_ring"} has been defined internally via lifting. Disabling the transfer-rules
  will hide the internal definition in further applications of transfer.\<close>
lifting_forget mod_ring.lifting

text \<open>For soundness of the 32-bit implementation, we mainly prove that this implementation
  implements the int-based implementation of the mod-ring.\<close>
context mod_ring_locale
begin

context fixes pp :: "uint32" 
  assumes ppp: "p = int_of_uint32 pp" 
  and small: "p \<le> 65535" 
begin

lemmas uint32_simps = 
  int_of_uint32_0
  int_of_uint32_plus 
  int_of_uint32_minus
  int_of_uint32_mult
  

definition urel32 :: "uint32 \<Rightarrow> int \<Rightarrow> bool" where "urel32 x y = (y = int_of_uint32 x \<and> y < p)" 

definition mod_ring_rel32 :: "uint32 \<Rightarrow> 'a mod_ring \<Rightarrow> bool" where
  "mod_ring_rel32 x y = (\<exists> z. urel32 x z \<and> mod_ring_rel z y)" 

lemma urel32_0: "urel32 0 0" unfolding urel32_def using p2 by (simp, transfer, simp)

lemma urel32_1: "urel32 1 1" unfolding urel32_def using p2 by (simp, transfer, simp)

lemma le_int_of_uint32: "(x \<le> y) = (int_of_uint32 x \<le> int_of_uint32 y)" 
  by (transfer, simp add: word_le_def)

lemma urel32_plus: assumes "urel32 x y" "urel32 x' y'"
  shows "urel32 (plus_p32 pp x x') (plus_p p y y')"
proof -    
  let ?x = "int_of_uint32 x" 
  let ?x' = "int_of_uint32 x'" 
  let ?p = "int_of_uint32 pp" 
  from assms int_of_uint32_ge_0 have id: "y = ?x" "y' = ?x'" 
    and rel: "0 \<le> ?x" "?x < p" 
      "0 \<le> ?x'" "?x' \<le> p" unfolding urel32_def by auto
  have le: "(pp \<le> x + x') = (?p \<le> ?x + ?x')" unfolding le_int_of_uint32
    using rel small by (auto simp: uint32_simps)
  show ?thesis
  proof (cases "?p \<le> ?x + ?x'")
    case True
    hence True: "(?p \<le> ?x + ?x') = True" by simp
    show ?thesis unfolding id 
      using small rel unfolding plus_p32_def plus_p_def Let_def urel32_def 
      unfolding ppp le True if_True
      using True by (auto simp: uint32_simps)
  next
    case False
    hence False: "(?p \<le> ?x + ?x') = False" by simp
    show ?thesis unfolding id 
      using small rel unfolding plus_p32_def plus_p_def Let_def urel32_def 
      unfolding ppp le False if_False
      using False by (auto simp: uint32_simps)
  qed
qed
  
lemma urel32_minus: assumes "urel32 x y" "urel32 x' y'"
  shows "urel32 (minus_p32 pp x x') (minus_p p y y')"
proof -    
  let ?x = "int_of_uint32 x" 
  let ?x' = "int_of_uint32 x'" 
  from assms int_of_uint32_ge_0 have id: "y = ?x" "y' = ?x'" 
    and rel: "0 \<le> ?x" "?x < p" 
      "0 \<le> ?x'" "?x' \<le> p" unfolding urel32_def by auto
  have le: "(x' \<le> x) = (?x' \<le> ?x)" unfolding le_int_of_uint32
    using rel small by (auto simp: uint32_simps)
  show ?thesis
  proof (cases "?x' \<le> ?x")
    case True
    hence True: "(?x' \<le> ?x) = True" by simp
    show ?thesis unfolding id 
      using small rel unfolding minus_p32_def minus_p_def Let_def urel32_def 
      unfolding ppp le True if_True
      using True by (auto simp: uint32_simps)
  next
    case False
    hence False: "(?x' \<le> ?x) = False" by simp
    show ?thesis unfolding id 
      using small rel unfolding minus_p32_def minus_p_def Let_def urel32_def 
      unfolding ppp le False if_False
      using False by (auto simp: uint32_simps)
  qed
qed

lemma urel32_uminus: assumes "urel32 x y"
  shows "urel32 (uminus_p32 pp x) (uminus_p p y)"
proof -    
  let ?x = "int_of_uint32 x"  
  from assms int_of_uint32_ge_0 have id: "y = ?x" 
    and rel: "0 \<le> ?x" "?x < p" 
      unfolding urel32_def by auto
  have le: "(x = 0) = (?x = 0)" unfolding int_of_uint32_0_iff
    using rel small by (auto simp: uint32_simps)
  show ?thesis
  proof (cases "?x = 0")
    case True
    hence True: "(?x = 0) = True" by simp
    show ?thesis unfolding id 
      using small rel unfolding uminus_p32_def uminus_p_def Let_def urel32_def 
      unfolding ppp le True if_True
      using True by (auto simp: uint32_simps)
  next
    case False
    hence False: "(?x = 0) = False" by simp
    show ?thesis unfolding id 
      using small rel unfolding uminus_p32_def uminus_p_def Let_def urel32_def 
      unfolding ppp le False if_False
      using False by (auto simp: uint32_simps)
  qed
qed

lemma urel32_mult: assumes "urel32 x y" "urel32 x' y'"
  shows "urel32 (mult_p32 pp x x') (mult_p p y y')"
proof -    
  let ?x = "int_of_uint32 x" 
  let ?x' = "int_of_uint32 x'" 
  from assms int_of_uint32_ge_0 have id: "y = ?x" "y' = ?x'" 
    and rel: "0 \<le> ?x" "?x < p" 
      "0 \<le> ?x'" "?x' < p" unfolding urel32_def by auto
  from rel have "?x * ?x' < p * p" by (metis mult_strict_mono') 
  also have "\<dots> \<le> 65536 * 65536"
    by (rule mult_mono, insert p2 small, auto)
  finally have le: "?x * ?x' < 4294967296" by simp
  show ?thesis unfolding id
      using small rel unfolding mult_p32_def mult_p_def Let_def urel32_def 
      unfolding ppp 
    by (auto simp: uint32_simps, unfold int_of_uint32_mod int_of_uint32_mult, 
        subst mod_pos_pos_trivial[of _ 4294967296], insert le, auto)
qed

lemma urel32_eq: assumes "urel32 x y" "urel32 x' y'" 
  shows "(x = x') = (y = y')" 
proof -    
  let ?x = "int_of_uint32 x" 
  let ?x' = "int_of_uint32 x'" 
  from assms int_of_uint32_ge_0 have id: "y = ?x" "y' = ?x'" 
    unfolding urel32_def by auto
  show ?thesis unfolding id by (transfer, auto)
qed

lemma urel32_normalize: 
assumes x: "urel32 x y"
shows "urel32 (if x = 0 then 0 else 1) (if y = 0 then 0 else 1)"
 unfolding urel32_eq[OF x urel32_0] using urel32_0 urel32_1 by auto

lemma urel32_mod: 
assumes x: "urel32 x x'" and y: "urel32 y y'" 
shows "urel32 (if y = 0 then x else 0) (if y' = 0 then x' else 0)"
  unfolding urel32_eq[OF y urel32_0] using urel32_0 x by auto 

lemma urel32_power: "urel32 x x' \<Longrightarrow> urel32 y (int y') \<Longrightarrow> urel32 (power_p32 pp x y) (power_p p x' y')"
proof (induct x' y' arbitrary: x y rule: power_p.induct[of _ p])
  case (1 x' y' x y)
  note x = 1(2) note y = 1(3)
  show ?case
  proof (cases "y' = 0")
    case True
    hence y: "y = 0" using urel32_eq[OF y urel32_0] by auto
    show ?thesis unfolding y True by (simp add: power_p.simps urel32_1)
  next
    case False
    hence id: "(y = 0) = False" "(y' = 0) = False" using urel32_eq[OF y urel32_0] by auto
    obtain d' r' where dr': "Divides.divmod_nat y' 2 = (d',r')" by force
    from divmod_nat_def[of y' 2, unfolded dr']
    have r': "r' = y' mod 2" and d': "d' = y' div 2" by auto
    have aux: "\<And> y'. int (y' mod 2) = int y' mod 2" by presburger
    have "urel32 (y AND 1) r'" unfolding r' using y unfolding urel32_def using small
      unfolding ppp by (transfer, auto simp: uint_and int_and_1, auto simp: aux) 
    from urel32_eq[OF this urel32_0]     
    have rem: "(y AND 1 = 0) = (r' = 0)" by simp
    have div: "urel32 (shiftr y 1) (int d')" unfolding d' using y unfolding urel32_def using small
      unfolding ppp 
      by (transfer, auto simp: shiftr_div_2n) 
    note IH = 1(1)[OF False refl dr'[symmetric] urel32_mult[OF x x] div]
    show ?thesis unfolding power_p.simps[of _ _ "y'"] power_p32.simps[of _ _ y] dr' id if_False rem
      using IH urel32_mult[OF IH x] by (auto simp: Let_def)
  qed
qed
  

lemma urel32_inverse: assumes x: "urel32 x x'" 
  shows "urel32 (inverse_p32 pp x) (inverse_p p x')" 
proof -
  have p: "urel32 (pp - 2) (int (nat (p - 2)))" using p2 small unfolding urel32_def unfolding ppp
    by (transfer, auto simp: uint_word_ariths)
  show ?thesis
    unfolding inverse_p32_def inverse_p_def urel32_eq[OF x urel32_0] using urel32_0 urel32_power[OF x p]
    by auto
qed

lemma mod_ring_0_32: "mod_ring_rel32 0 0"
  using urel32_0 mod_ring_0 unfolding mod_ring_rel32_def by blast

lemma mod_ring_1_32: "mod_ring_rel32 1 1"
  using urel32_1 mod_ring_1 unfolding mod_ring_rel32_def by blast

lemma mod_ring_uminus32: "(mod_ring_rel32 ===> mod_ring_rel32) (uminus_p32 pp) uminus"
  using urel32_uminus mod_ring_uminus unfolding mod_ring_rel32_def rel_fun_def by blast

lemma mod_ring_plus32: "(mod_ring_rel32 ===> mod_ring_rel32 ===> mod_ring_rel32) (plus_p32 pp) (+)"
  using urel32_plus mod_ring_plus unfolding mod_ring_rel32_def rel_fun_def by blast

lemma mod_ring_minus32: "(mod_ring_rel32 ===> mod_ring_rel32 ===> mod_ring_rel32) (minus_p32 pp) (-)"
  using urel32_minus mod_ring_minus unfolding mod_ring_rel32_def rel_fun_def by blast

lemma mod_ring_mult32: "(mod_ring_rel32 ===> mod_ring_rel32 ===> mod_ring_rel32) (mult_p32 pp) ((*))"
  using urel32_mult mod_ring_mult unfolding mod_ring_rel32_def rel_fun_def by blast

lemma mod_ring_eq32: "(mod_ring_rel32 ===> mod_ring_rel32 ===> (=)) (=) (=)" 
  using urel32_eq mod_ring_eq unfolding mod_ring_rel32_def rel_fun_def by blast

lemma urel32_inj: "urel32 x y \<Longrightarrow> urel32 x z \<Longrightarrow> y = z" 
  using urel32_eq[of x y x z] by auto

lemma urel32_inj': "urel32 x z \<Longrightarrow> urel32 y z \<Longrightarrow> x = y" 
  using urel32_eq[of x z y z] by auto

lemma bi_unique_mod_ring_rel32:
  "bi_unique mod_ring_rel32" "left_unique mod_ring_rel32" "right_unique mod_ring_rel32"
  using bi_unique_mod_ring_rel urel32_inj'
  unfolding mod_ring_rel32_def bi_unique_def left_unique_def right_unique_def
  by (auto simp: urel32_def)  

lemma right_total_mod_ring_rel32: "right_total mod_ring_rel32"
  unfolding mod_ring_rel32_def right_total_def
proof 
  fix y :: "'a mod_ring" 
  from right_total_mod_ring_rel[unfolded right_total_def, rule_format, of y]
  obtain z where zy: "mod_ring_rel z y" by auto  
  hence zp: "0 \<le> z" "z < p" unfolding mod_ring_rel_def p using range_to_int_mod_ring[where 'a = 'a] by auto
  hence "urel32 (uint32_of_int z) z" unfolding urel32_def using small unfolding ppp 
    by (auto simp: int_of_uint32_inv) 
  with zy show "\<exists> x z. urel32 x z \<and> mod_ring_rel z y" by blast
qed

lemma Domainp_mod_ring_rel32: "Domainp mod_ring_rel32 = (\<lambda>x. 0 \<le> x \<and> x < pp)"
proof 
  fix x
  show "Domainp mod_ring_rel32 x = (0 \<le> x \<and> x < pp)"   
    unfolding Domainp.simps
    unfolding mod_ring_rel32_def
  proof
    let ?i = "int_of_uint32" 
    assume *: "0 \<le> x \<and> x < pp"     
    hence "0 \<le> ?i x \<and> ?i x < p" using small unfolding ppp
      by (transfer, auto simp: word_less_def)
    hence "?i x \<in> {0 ..< p}" by auto
    with Domainp_mod_ring_rel
    have "Domainp mod_ring_rel (?i x)" by auto
    from this[unfolded Domainp.simps]
    obtain b where b: "mod_ring_rel (?i x) b" by auto
    show "\<exists>a b. x = a \<and> (\<exists>z. urel32 a z \<and> mod_ring_rel z b)" 
    proof (intro exI, rule conjI[OF refl], rule exI, rule conjI[OF _ b])
      show "urel32 x (?i x)" unfolding urel32_def using small * unfolding ppp
        by (transfer, auto simp: word_less_def)
    qed
  next
    assume "\<exists>a b. x = a \<and> (\<exists>z. urel32 a z \<and> mod_ring_rel z b)" 
    then obtain b z where xz: "urel32 x z" and zb: "mod_ring_rel z b" by auto
    hence "Domainp mod_ring_rel z"  by auto
    with Domainp_mod_ring_rel have "0 \<le> z" "z < p" by auto
    with xz show "0 \<le> x \<and> x < pp" unfolding urel32_def using small unfolding ppp
      by (transfer, auto simp: word_less_def)
  qed
qed

lemma ring_finite_field_ops32: "ring_ops (finite_field_ops32 pp) mod_ring_rel32"
  by (unfold_locales, auto simp:
  finite_field_ops32_def
  bi_unique_mod_ring_rel32
  right_total_mod_ring_rel32
  mod_ring_plus32
  mod_ring_minus32
  mod_ring_uminus32
  mod_ring_mult32
  mod_ring_eq32
  mod_ring_0_32
  mod_ring_1_32
  Domainp_mod_ring_rel32)
end
end

context prime_field
begin
context fixes pp :: "uint32" 
  assumes *: "p = int_of_uint32 pp" "p \<le> 65535" 
begin

lemma mod_ring_normalize32: "(mod_ring_rel32 ===> mod_ring_rel32) (\<lambda>x. if x = 0 then 0 else 1) normalize" 
  using urel32_normalize[OF *] mod_ring_normalize unfolding mod_ring_rel32_def[OF *] rel_fun_def by blast

lemma mod_ring_mod32: "(mod_ring_rel32 ===> mod_ring_rel32 ===> mod_ring_rel32) (\<lambda>x y. if y = 0 then x else 0) (mod)" 
  using urel32_mod[OF *] mod_ring_mod unfolding mod_ring_rel32_def[OF *] rel_fun_def by blast

lemma mod_ring_unit_factor32: "(mod_ring_rel32 ===> mod_ring_rel32) (\<lambda>x. x) unit_factor" 
  using mod_ring_unit_factor unfolding mod_ring_rel32_def[OF *] rel_fun_def by blast

lemma mod_ring_inverse32: "(mod_ring_rel32 ===> mod_ring_rel32) (inverse_p32 pp) inverse"
  using urel32_inverse[OF *] mod_ring_inverse unfolding mod_ring_rel32_def[OF *] rel_fun_def by blast

lemma mod_ring_divide32: "(mod_ring_rel32 ===> mod_ring_rel32 ===> mod_ring_rel32) (divide_p32 pp) (/)"
  using mod_ring_inverse32 mod_ring_mult32[OF *]
  unfolding divide_p32_def divide_mod_ring_def inverse_mod_ring_def[symmetric]
    rel_fun_def by blast

lemma finite_field_ops32: "field_ops (finite_field_ops32 pp) mod_ring_rel32"
  by (unfold_locales, insert ring_finite_field_ops32[OF *], auto simp:
  ring_ops_def
  finite_field_ops32_def
  mod_ring_divide32
  mod_ring_inverse32
  mod_ring_mod32
  mod_ring_normalize32)

end
end

(* now there is 64-bit time *)
context
  fixes p :: uint64
begin
definition plus_p64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" where
  "plus_p64 x y \<equiv> let z = x + y in if z \<ge> p then z - p else z"

definition minus_p64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" where
  "minus_p64 x y \<equiv> if y \<le> x then x - y else (x + p) - y"

definition uminus_p64 :: "uint64 \<Rightarrow> uint64" where
  "uminus_p64 x = (if x = 0 then 0 else p - x)"

definition mult_p64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" where
  "mult_p64 x y = (x * y mod p)"

lemma int_of_uint64_shift: "int_of_uint64 (shiftr n k) = (int_of_uint64 n) div (2 ^ k)" 
  by (transfer, rule shiftr_div_2n) 

lemma int_of_uint64_0_iff: "int_of_uint64 n = 0 \<longleftrightarrow> n = 0" 
  by (transfer, rule uint_0_iff)
  
lemma int_of_uint64_0: "int_of_uint64 0 = 0" unfolding int_of_uint64_0_iff by simp

lemma int_of_uint64_ge_0: "int_of_uint64 n \<ge> 0" 
  by (transfer, auto)

lemma two_64: "2 ^ LENGTH(64) = (18446744073709551616 :: int)" by simp

lemma int_of_uint64_plus: "int_of_uint64 (x + y) = (int_of_uint64 x + int_of_uint64 y) mod 18446744073709551616" 
  by (transfer, unfold uint_word_ariths two_64, rule refl)  

lemma int_of_uint64_minus: "int_of_uint64 (x - y) = (int_of_uint64 x - int_of_uint64 y) mod 18446744073709551616" 
  by (transfer, unfold uint_word_ariths two_64, rule refl)  

lemma int_of_uint64_mult: "int_of_uint64 (x * y) = (int_of_uint64 x * int_of_uint64 y) mod 18446744073709551616" 
  by (transfer, unfold uint_word_ariths two_64, rule refl)  

lemma int_of_uint64_mod: "int_of_uint64 (x mod y) = (int_of_uint64 x mod int_of_uint64 y)" 
  by (transfer, unfold uint_mod two_64, rule refl)  

lemma int_of_uint64_inv: "0 \<le> x \<Longrightarrow> x < 18446744073709551616 \<Longrightarrow> int_of_uint64 (uint64_of_int x) = x"
  by (transfer, simp add: int_word_uint) 

function power_p64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" where
  "power_p64 x n = (if n = 0 then 1 else
    let rec = power_p64 (mult_p64 x x) (shiftr n 1) in
    if n AND 1 = 0 then rec else mult_p64 rec x)"
  by pat_completeness auto

termination 
proof -
  {
    fix n :: uint64
    assume "n \<noteq> 0" 
    with int_of_uint64_ge_0[of n] int_of_uint64_0_iff[of n] have "int_of_uint64 n > 0" by auto
    hence "0 < int_of_uint64 n" "int_of_uint64 n div 2 < int_of_uint64 n" by auto
  } note * = this
  show ?thesis
    by (relation "measure (\<lambda> (x,n). nat (int_of_uint64 n))", auto simp: int_of_uint64_shift *) 
qed

text \<open>In experiments with Berlekamp-factorization (where the prime $p$ is usually small),
  it turned out that taking the below implementation of inverse via exponentiation
  is faster than the one based on the extended Euclidean algorithm.\<close>

definition inverse_p64 :: "uint64 \<Rightarrow> uint64" where
  "inverse_p64 x = (if x = 0 then 0 else power_p64 x (p - 2))"

definition divide_p64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64"  where
  "divide_p64 x y = mult_p64 x (inverse_p64 y)"

definition finite_field_ops64 :: "uint64 arith_ops_record" where
  "finite_field_ops64 \<equiv> Arith_Ops_Record
      0
      1
      plus_p64
      mult_p64
      minus_p64
      uminus_p64
      divide_p64
      inverse_p64
      (\<lambda> x y . if y = 0 then x else 0)
      (\<lambda> x . if x = 0 then 0 else 1)
      (\<lambda> x . x)
      uint64_of_int
      int_of_uint64
      (\<lambda> x. 0 \<le> x \<and> x < p)"
end 

lemma shiftr_uint64_code [code_unfold]: "shiftr x 1 = (uint64_shiftr x 1)"
  unfolding shiftr_uint64_code using integer_of_nat_1 by auto

text \<open>For soundness of the 64-bit implementation, we mainly prove that this implementation
  implements the int-based implementation of GF(p).\<close>
context mod_ring_locale
begin

context fixes pp :: "uint64" 
  assumes ppp: "p = int_of_uint64 pp" 
  and small: "p \<le> 4294967295" 
begin

lemmas uint64_simps = 
  int_of_uint64_0
  int_of_uint64_plus 
  int_of_uint64_minus
  int_of_uint64_mult
  

definition urel64 :: "uint64 \<Rightarrow> int \<Rightarrow> bool" where "urel64 x y = (y = int_of_uint64 x \<and> y < p)" 

definition mod_ring_rel64 :: "uint64 \<Rightarrow> 'a mod_ring \<Rightarrow> bool" where
  "mod_ring_rel64 x y = (\<exists> z. urel64 x z \<and> mod_ring_rel z y)" 

lemma urel64_0: "urel64 0 0" unfolding urel64_def using p2 by (simp, transfer, simp)

lemma urel64_1: "urel64 1 1" unfolding urel64_def using p2 by (simp, transfer, simp)

lemma le_int_of_uint64: "(x \<le> y) = (int_of_uint64 x \<le> int_of_uint64 y)" 
  by (transfer, simp add: word_le_def)

lemma urel64_plus: assumes "urel64 x y" "urel64 x' y'"
  shows "urel64 (plus_p64 pp x x') (plus_p p y y')"
proof -    
  let ?x = "int_of_uint64 x" 
  let ?x' = "int_of_uint64 x'" 
  let ?p = "int_of_uint64 pp" 
  from assms int_of_uint64_ge_0 have id: "y = ?x" "y' = ?x'" 
    and rel: "0 \<le> ?x" "?x < p" 
      "0 \<le> ?x'" "?x' \<le> p" unfolding urel64_def by auto
  have le: "(pp \<le> x + x') = (?p \<le> ?x + ?x')" unfolding le_int_of_uint64
    using rel small by (auto simp: uint64_simps)
  show ?thesis
  proof (cases "?p \<le> ?x + ?x'")
    case True
    hence True: "(?p \<le> ?x + ?x') = True" by simp
    show ?thesis unfolding id 
      using small rel unfolding plus_p64_def plus_p_def Let_def urel64_def 
      unfolding ppp le True if_True
      using True by (auto simp: uint64_simps)
  next
    case False
    hence False: "(?p \<le> ?x + ?x') = False" by simp
    show ?thesis unfolding id 
      using small rel unfolding plus_p64_def plus_p_def Let_def urel64_def 
      unfolding ppp le False if_False
      using False by (auto simp: uint64_simps)
  qed
qed
  
lemma urel64_minus: assumes "urel64 x y" "urel64 x' y'"
  shows "urel64 (minus_p64 pp x x') (minus_p p y y')"
proof -    
  let ?x = "int_of_uint64 x" 
  let ?x' = "int_of_uint64 x'" 
  from assms int_of_uint64_ge_0 have id: "y = ?x" "y' = ?x'" 
    and rel: "0 \<le> ?x" "?x < p" 
      "0 \<le> ?x'" "?x' \<le> p" unfolding urel64_def by auto
  have le: "(x' \<le> x) = (?x' \<le> ?x)" unfolding le_int_of_uint64
    using rel small by (auto simp: uint64_simps)
  show ?thesis
  proof (cases "?x' \<le> ?x")
    case True
    hence True: "(?x' \<le> ?x) = True" by simp
    show ?thesis unfolding id 
      using small rel unfolding minus_p64_def minus_p_def Let_def urel64_def 
      unfolding ppp le True if_True
      using True by (auto simp: uint64_simps)
  next
    case False
    hence False: "(?x' \<le> ?x) = False" by simp
    show ?thesis unfolding id 
      using small rel unfolding minus_p64_def minus_p_def Let_def urel64_def 
      unfolding ppp le False if_False
      using False by (auto simp: uint64_simps)
  qed
qed

lemma urel64_uminus: assumes "urel64 x y"
  shows "urel64 (uminus_p64 pp x) (uminus_p p y)"
proof -    
  let ?x = "int_of_uint64 x"  
  from assms int_of_uint64_ge_0 have id: "y = ?x" 
    and rel: "0 \<le> ?x" "?x < p" 
      unfolding urel64_def by auto
  have le: "(x = 0) = (?x = 0)" unfolding int_of_uint64_0_iff
    using rel small by (auto simp: uint64_simps)
  show ?thesis
  proof (cases "?x = 0")
    case True
    hence True: "(?x = 0) = True" by simp
    show ?thesis unfolding id 
      using small rel unfolding uminus_p64_def uminus_p_def Let_def urel64_def 
      unfolding ppp le True if_True
      using True by (auto simp: uint64_simps)
  next
    case False
    hence False: "(?x = 0) = False" by simp
    show ?thesis unfolding id 
      using small rel unfolding uminus_p64_def uminus_p_def Let_def urel64_def 
      unfolding ppp le False if_False
      using False by (auto simp: uint64_simps)
  qed
qed

lemma urel64_mult: assumes "urel64 x y" "urel64 x' y'"
  shows "urel64 (mult_p64 pp x x') (mult_p p y y')"
proof -    
  let ?x = "int_of_uint64 x" 
  let ?x' = "int_of_uint64 x'" 
  from assms int_of_uint64_ge_0 have id: "y = ?x" "y' = ?x'" 
    and rel: "0 \<le> ?x" "?x < p" 
      "0 \<le> ?x'" "?x' < p" unfolding urel64_def by auto
  from rel have "?x * ?x' < p * p" by (metis mult_strict_mono') 
  also have "\<dots> \<le> 4294967296 * 4294967296"
    by (rule mult_mono, insert p2 small, auto)
  finally have le: "?x * ?x' < 18446744073709551616" by simp
  show ?thesis unfolding id
      using small rel unfolding mult_p64_def mult_p_def Let_def urel64_def 
      unfolding ppp 
    by (auto simp: uint64_simps, unfold int_of_uint64_mod int_of_uint64_mult, 
        subst mod_pos_pos_trivial[of _ 18446744073709551616], insert le, auto)
qed

lemma urel64_eq: assumes "urel64 x y" "urel64 x' y'" 
  shows "(x = x') = (y = y')" 
proof -    
  let ?x = "int_of_uint64 x" 
  let ?x' = "int_of_uint64 x'" 
  from assms int_of_uint64_ge_0 have id: "y = ?x" "y' = ?x'" 
    unfolding urel64_def by auto
  show ?thesis unfolding id by (transfer, auto)
qed

lemma urel64_normalize: 
assumes x: "urel64 x y"
shows "urel64 (if x = 0 then 0 else 1) (if y = 0 then 0 else 1)"
 unfolding urel64_eq[OF x urel64_0] using urel64_0 urel64_1 by auto

lemma urel64_mod: 
assumes x: "urel64 x x'" and y: "urel64 y y'" 
shows "urel64 (if y = 0 then x else 0) (if y' = 0 then x' else 0)"
  unfolding urel64_eq[OF y urel64_0] using urel64_0 x by auto 

lemma urel64_power: "urel64 x x' \<Longrightarrow> urel64 y (int y') \<Longrightarrow> urel64 (power_p64 pp x y) (power_p p x' y')"
proof (induct x' y' arbitrary: x y rule: power_p.induct[of _ p])
  case (1 x' y' x y)
  note x = 1(2) note y = 1(3)
  show ?case
  proof (cases "y' = 0")
    case True
    hence y: "y = 0" using urel64_eq[OF y urel64_0] by auto
    show ?thesis unfolding y True by (simp add: power_p.simps urel64_1)
  next
    case False
    hence id: "(y = 0) = False" "(y' = 0) = False" using urel64_eq[OF y urel64_0] by auto
    obtain d' r' where dr': "Divides.divmod_nat y' 2 = (d',r')" by force
    from divmod_nat_def[of y' 2, unfolded dr']
    have r': "r' = y' mod 2" and d': "d' = y' div 2" by auto
    have aux: "\<And> y'. int (y' mod 2) = int y' mod 2" by presburger
    have "urel64 (y AND 1) r'" unfolding r' using y unfolding urel64_def using small
      unfolding ppp by (transfer, auto simp: uint_and int_and_1, auto simp: aux) 
    from urel64_eq[OF this urel64_0]     
    have rem: "(y AND 1 = 0) = (r' = 0)" by simp
    have div: "urel64 (shiftr y 1) (int d')" unfolding d' using y unfolding urel64_def using small
      unfolding ppp 
      by (transfer, auto simp: shiftr_div_2n) 
    note IH = 1(1)[OF False refl dr'[symmetric] urel64_mult[OF x x] div]
    show ?thesis unfolding power_p.simps[of _ _ "y'"] power_p64.simps[of _ _ y] dr' id if_False rem
      using IH urel64_mult[OF IH x] by (auto simp: Let_def)
  qed
qed
  

lemma urel64_inverse: assumes x: "urel64 x x'" 
  shows "urel64 (inverse_p64 pp x) (inverse_p p x')" 
proof -
  have p: "urel64 (pp - 2) (int (nat (p - 2)))" using p2 small unfolding urel64_def unfolding ppp
    by (transfer, auto simp: uint_word_ariths)
  show ?thesis
    unfolding inverse_p64_def inverse_p_def urel64_eq[OF x urel64_0] using urel64_0 urel64_power[OF x p]
    by auto
qed

lemma mod_ring_0_64: "mod_ring_rel64 0 0"
  using urel64_0 mod_ring_0 unfolding mod_ring_rel64_def by blast

lemma mod_ring_1_64: "mod_ring_rel64 1 1"
  using urel64_1 mod_ring_1 unfolding mod_ring_rel64_def by blast

lemma mod_ring_uminus64: "(mod_ring_rel64 ===> mod_ring_rel64) (uminus_p64 pp) uminus"
  using urel64_uminus mod_ring_uminus unfolding mod_ring_rel64_def rel_fun_def by blast

lemma mod_ring_plus64: "(mod_ring_rel64 ===> mod_ring_rel64 ===> mod_ring_rel64) (plus_p64 pp) (+)"
  using urel64_plus mod_ring_plus unfolding mod_ring_rel64_def rel_fun_def by blast

lemma mod_ring_minus64: "(mod_ring_rel64 ===> mod_ring_rel64 ===> mod_ring_rel64) (minus_p64 pp) (-)"
  using urel64_minus mod_ring_minus unfolding mod_ring_rel64_def rel_fun_def by blast

lemma mod_ring_mult64: "(mod_ring_rel64 ===> mod_ring_rel64 ===> mod_ring_rel64) (mult_p64 pp) ((*))"
  using urel64_mult mod_ring_mult unfolding mod_ring_rel64_def rel_fun_def by blast

lemma mod_ring_eq64: "(mod_ring_rel64 ===> mod_ring_rel64 ===> (=)) (=) (=)" 
  using urel64_eq mod_ring_eq unfolding mod_ring_rel64_def rel_fun_def by blast

lemma urel64_inj: "urel64 x y \<Longrightarrow> urel64 x z \<Longrightarrow> y = z" 
  using urel64_eq[of x y x z] by auto

lemma urel64_inj': "urel64 x z \<Longrightarrow> urel64 y z \<Longrightarrow> x = y" 
  using urel64_eq[of x z y z] by auto

lemma bi_unique_mod_ring_rel64:
  "bi_unique mod_ring_rel64" "left_unique mod_ring_rel64" "right_unique mod_ring_rel64"
  using bi_unique_mod_ring_rel urel64_inj'
  unfolding mod_ring_rel64_def bi_unique_def left_unique_def right_unique_def
  by (auto simp: urel64_def)  

lemma right_total_mod_ring_rel64: "right_total mod_ring_rel64"
  unfolding mod_ring_rel64_def right_total_def
proof 
  fix y :: "'a mod_ring" 
  from right_total_mod_ring_rel[unfolded right_total_def, rule_format, of y]
  obtain z where zy: "mod_ring_rel z y" by auto  
  hence zp: "0 \<le> z" "z < p" unfolding mod_ring_rel_def p using range_to_int_mod_ring[where 'a = 'a] by auto
  hence "urel64 (uint64_of_int z) z" unfolding urel64_def using small unfolding ppp 
    by (auto simp: int_of_uint64_inv) 
  with zy show "\<exists> x z. urel64 x z \<and> mod_ring_rel z y" by blast
qed

lemma Domainp_mod_ring_rel64: "Domainp mod_ring_rel64 = (\<lambda>x. 0 \<le> x \<and> x < pp)"
proof 
  fix x
  show "Domainp mod_ring_rel64 x = (0 \<le> x \<and> x < pp)"   
    unfolding Domainp.simps
    unfolding mod_ring_rel64_def
  proof
    let ?i = "int_of_uint64" 
    assume *: "0 \<le> x \<and> x < pp"     
    hence "0 \<le> ?i x \<and> ?i x < p" using small unfolding ppp
      by (transfer, auto simp: word_less_def)
    hence "?i x \<in> {0 ..< p}" by auto
    with Domainp_mod_ring_rel
    have "Domainp mod_ring_rel (?i x)" by auto
    from this[unfolded Domainp.simps]
    obtain b where b: "mod_ring_rel (?i x) b" by auto
    show "\<exists>a b. x = a \<and> (\<exists>z. urel64 a z \<and> mod_ring_rel z b)" 
    proof (intro exI, rule conjI[OF refl], rule exI, rule conjI[OF _ b])
      show "urel64 x (?i x)" unfolding urel64_def using small * unfolding ppp
        by (transfer, auto simp: word_less_def)
    qed
  next
    assume "\<exists>a b. x = a \<and> (\<exists>z. urel64 a z \<and> mod_ring_rel z b)" 
    then obtain b z where xz: "urel64 x z" and zb: "mod_ring_rel z b" by auto
    hence "Domainp mod_ring_rel z"  by auto
    with Domainp_mod_ring_rel have "0 \<le> z" "z < p" by auto
    with xz show "0 \<le> x \<and> x < pp" unfolding urel64_def using small unfolding ppp
      by (transfer, auto simp: word_less_def)
  qed
qed

lemma ring_finite_field_ops64: "ring_ops (finite_field_ops64 pp) mod_ring_rel64"
  by (unfold_locales, auto simp:
  finite_field_ops64_def
  bi_unique_mod_ring_rel64
  right_total_mod_ring_rel64
  mod_ring_plus64
  mod_ring_minus64
  mod_ring_uminus64
  mod_ring_mult64
  mod_ring_eq64
  mod_ring_0_64
  mod_ring_1_64
  Domainp_mod_ring_rel64)
end
end

context prime_field
begin
context fixes pp :: "uint64" 
  assumes *: "p = int_of_uint64 pp" "p \<le> 4294967295" 
begin

lemma mod_ring_normalize64: "(mod_ring_rel64 ===> mod_ring_rel64) (\<lambda>x. if x = 0 then 0 else 1) normalize" 
  using urel64_normalize[OF *] mod_ring_normalize unfolding mod_ring_rel64_def[OF *] rel_fun_def by blast

lemma mod_ring_mod64: "(mod_ring_rel64 ===> mod_ring_rel64 ===> mod_ring_rel64) (\<lambda>x y. if y = 0 then x else 0) (mod)" 
  using urel64_mod[OF *] mod_ring_mod unfolding mod_ring_rel64_def[OF *] rel_fun_def by blast

lemma mod_ring_unit_factor64: "(mod_ring_rel64 ===> mod_ring_rel64) (\<lambda>x. x) unit_factor" 
  using mod_ring_unit_factor unfolding mod_ring_rel64_def[OF *] rel_fun_def by blast

lemma mod_ring_inverse64: "(mod_ring_rel64 ===> mod_ring_rel64) (inverse_p64 pp) inverse"
  using urel64_inverse[OF *] mod_ring_inverse unfolding mod_ring_rel64_def[OF *] rel_fun_def by blast

lemma mod_ring_divide64: "(mod_ring_rel64 ===> mod_ring_rel64 ===> mod_ring_rel64) (divide_p64 pp) (/)"
  using mod_ring_inverse64 mod_ring_mult64[OF *]
  unfolding divide_p64_def divide_mod_ring_def inverse_mod_ring_def[symmetric]
    rel_fun_def by blast

lemma finite_field_ops64: "field_ops (finite_field_ops64 pp) mod_ring_rel64"
  by (unfold_locales, insert ring_finite_field_ops64[OF *], auto simp:
  ring_ops_def
  finite_field_ops64_def
  mod_ring_divide64
  mod_ring_inverse64
  mod_ring_mod64
  mod_ring_normalize64)
end
end

(* and a final implementation via integer *)
context
  fixes p :: integer
begin
definition plus_p_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "plus_p_integer x y \<equiv> let z = x + y in if z \<ge> p then z - p else z"

definition minus_p_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "minus_p_integer x y \<equiv> if y \<le> x then x - y else (x + p) - y"

definition uminus_p_integer :: "integer \<Rightarrow> integer" where
  "uminus_p_integer x = (if x = 0 then 0 else p - x)"

definition mult_p_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "mult_p_integer x y = (x * y mod p)"

lemma int_of_integer_0_iff: "int_of_integer n = 0 \<longleftrightarrow> n = 0"
  using integer_eqI by auto
  
lemma int_of_integer_0: "int_of_integer 0 = 0" unfolding int_of_integer_0_iff by simp

lemma int_of_integer_plus: "int_of_integer (x + y) = (int_of_integer x + int_of_integer y)" 
  by simp

lemma int_of_integer_minus: "int_of_integer (x - y) = (int_of_integer x - int_of_integer y)"
  by simp

lemma int_of_integer_mult: "int_of_integer (x * y) = (int_of_integer x * int_of_integer y)" 
  by simp  

lemma int_of_integer_mod: "int_of_integer (x mod y) = (int_of_integer x mod int_of_integer y)" 
  by simp  

lemma int_of_integer_inv: "int_of_integer (integer_of_int x) = x" by simp

lemma int_of_integer_shift: "int_of_integer (shiftr n k) = (int_of_integer n) div (2 ^ k)" 
  by (simp add: shiftr_int_def shiftr_integer.rep_eq)


function power_p_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "power_p_integer x n = (if n \<le> 0 then 1 else
    let rec = power_p_integer (mult_p_integer x x) (shiftr n 1) in
    if n AND 1 = 0 then rec else mult_p_integer rec x)"
  by pat_completeness auto

termination 
proof -
  {
    fix n :: integer
    assume "\<not> (n \<le> 0)" 
    hence "n > 0" by auto
    hence "int_of_integer n > 0"
      by (simp add: less_integer.rep_eq)
    hence "0 < int_of_integer n" "int_of_integer n div 2 < int_of_integer n" by auto
  } note * = this
  show ?thesis
    by (relation "measure (\<lambda> (x,n). nat (int_of_integer n))", auto simp: * int_of_integer_shift) 
qed

text \<open>In experiments with Berlekamp-factorization (where the prime $p$ is usually small),
  it turned out that taking the below implementation of inverse via exponentiation
  is faster than the one based on the extended Euclidean algorithm.\<close>

definition inverse_p_integer :: "integer \<Rightarrow> integer" where
  "inverse_p_integer x = (if x = 0 then 0 else power_p_integer x (p - 2))"

definition divide_p_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer"  where
  "divide_p_integer x y = mult_p_integer x (inverse_p_integer y)"

definition finite_field_ops_integer :: "integer arith_ops_record" where
  "finite_field_ops_integer \<equiv> Arith_Ops_Record
      0
      1
      plus_p_integer
      mult_p_integer
      minus_p_integer
      uminus_p_integer
      divide_p_integer
      inverse_p_integer
      (\<lambda> x y . if y = 0 then x else 0)
      (\<lambda> x . if x = 0 then 0 else 1)
      (\<lambda> x . x)
      integer_of_int
      int_of_integer
      (\<lambda> x. 0 \<le> x \<and> x < p)"
end 

lemma shiftr_integer_code [code_unfold]: "shiftr x 1 = (integer_shiftr x 1)"
  unfolding shiftr_integer_code using integer_of_nat_1 by auto

text \<open>For soundness of the integer implementation, we mainly prove that this implementation
  implements the int-based implementation of GF(p).\<close>
context mod_ring_locale
begin

context fixes pp :: "integer" 
  assumes ppp: "p = int_of_integer pp" 
begin

lemmas integer_simps = 
  int_of_integer_0
  int_of_integer_plus 
  int_of_integer_minus
  int_of_integer_mult
  

definition urel_integer :: "integer \<Rightarrow> int \<Rightarrow> bool" where "urel_integer x y = (y = int_of_integer x \<and> y \<ge> 0 \<and> y < p)" 

definition mod_ring_rel_integer :: "integer \<Rightarrow> 'a mod_ring \<Rightarrow> bool" where
  "mod_ring_rel_integer x y = (\<exists> z. urel_integer x z \<and> mod_ring_rel z y)" 

lemma urel_integer_0: "urel_integer 0 0" unfolding urel_integer_def using p2 by simp

lemma urel_integer_1: "urel_integer 1 1" unfolding urel_integer_def using p2 by simp

lemma le_int_of_integer: "(x \<le> y) = (int_of_integer x \<le> int_of_integer y)" 
  by (rule less_eq_integer.rep_eq)

lemma urel_integer_plus: assumes "urel_integer x y" "urel_integer x' y'"
  shows "urel_integer (plus_p_integer pp x x') (plus_p p y y')"
proof -    
  let ?x = "int_of_integer x" 
  let ?x' = "int_of_integer x'" 
  let ?p = "int_of_integer pp" 
  from assms have id: "y = ?x" "y' = ?x'" 
    and rel: "0 \<le> ?x" "?x < p" 
      "0 \<le> ?x'" "?x' \<le> p" unfolding urel_integer_def by auto
  have le: "(pp \<le> x + x') = (?p \<le> ?x + ?x')" unfolding le_int_of_integer
    using rel by auto
  show ?thesis
  proof (cases "?p \<le> ?x + ?x'")
    case True
    hence True: "(?p \<le> ?x + ?x') = True" by simp
    show ?thesis unfolding id 
      using rel unfolding plus_p_integer_def plus_p_def Let_def urel_integer_def 
      unfolding ppp le True if_True
      using True by auto
  next
    case False
    hence False: "(?p \<le> ?x + ?x') = False" by simp
    show ?thesis unfolding id 
      using rel unfolding plus_p_integer_def plus_p_def Let_def urel_integer_def 
      unfolding ppp le False if_False
      using False by auto
  qed
qed
  
lemma urel_integer_minus: assumes "urel_integer x y" "urel_integer x' y'"
  shows "urel_integer (minus_p_integer pp x x') (minus_p p y y')"
proof -    
  let ?x = "int_of_integer x" 
  let ?x' = "int_of_integer x'" 
  from assms have id: "y = ?x" "y' = ?x'" 
    and rel: "0 \<le> ?x" "?x < p" 
      "0 \<le> ?x'" "?x' \<le> p" unfolding urel_integer_def by auto
  have le: "(x' \<le> x) = (?x' \<le> ?x)" unfolding le_int_of_integer
    using rel by auto
  show ?thesis
  proof (cases "?x' \<le> ?x")
    case True
    hence True: "(?x' \<le> ?x) = True" by simp
    show ?thesis unfolding id 
      using rel unfolding minus_p_integer_def minus_p_def Let_def urel_integer_def 
      unfolding ppp le True if_True
      using True by auto
  next
    case False
    hence False: "(?x' \<le> ?x) = False" by simp
    show ?thesis unfolding id 
      using rel unfolding minus_p_integer_def minus_p_def Let_def urel_integer_def 
      unfolding ppp le False if_False
      using False by auto
  qed
qed

lemma urel_integer_uminus: assumes "urel_integer x y"
  shows "urel_integer (uminus_p_integer pp x) (uminus_p p y)"
proof -    
  let ?x = "int_of_integer x"  
  from assms have id: "y = ?x" 
    and rel: "0 \<le> ?x" "?x < p" 
      unfolding urel_integer_def by auto
  have le: "(x = 0) = (?x = 0)" unfolding int_of_integer_0_iff
    using rel by auto
  show ?thesis
  proof (cases "?x = 0")
    case True
    hence True: "(?x = 0) = True" by simp
    show ?thesis unfolding id 
      using rel unfolding uminus_p_integer_def uminus_p_def Let_def urel_integer_def 
      unfolding ppp le True if_True
      using True by auto
  next
    case False
    hence False: "(?x = 0) = False" by simp
    show ?thesis unfolding id 
      using rel unfolding uminus_p_integer_def uminus_p_def Let_def urel_integer_def 
      unfolding ppp le False if_False
      using False by auto
  qed
qed

lemma pp_pos: "int_of_integer pp > 0" 
  using ppp nontriv[where 'a = 'a]  unfolding p
  by (simp add: less_integer.rep_eq)

lemma urel_integer_mult: assumes "urel_integer x y" "urel_integer x' y'"
  shows "urel_integer (mult_p_integer pp x x') (mult_p p y y')"
proof -    
  let ?x = "int_of_integer x" 
  let ?x' = "int_of_integer x'" 
  from assms  have id: "y = ?x" "y' = ?x'" 
    and rel: "0 \<le> ?x" "?x < p" 
      "0 \<le> ?x'" "?x' < p" unfolding urel_integer_def by auto
  from rel(1,3) have xx: "0 \<le> ?x * ?x'" by simp
  show ?thesis unfolding id
    using rel unfolding mult_p_integer_def mult_p_def Let_def urel_integer_def     
    unfolding ppp mod_nonneg_pos_int[OF xx pp_pos] using xx pp_pos by simp        
qed

lemma urel_integer_eq: assumes "urel_integer x y" "urel_integer x' y'" 
  shows "(x = x') = (y = y')" 
proof -    
  let ?x = "int_of_integer x" 
  let ?x' = "int_of_integer x'" 
  from assms have id: "y = ?x" "y' = ?x'" 
    unfolding urel_integer_def by auto
  show ?thesis unfolding id integer_eq_iff ..
qed

lemma urel_integer_normalize: 
assumes x: "urel_integer x y"
shows "urel_integer (if x = 0 then 0 else 1) (if y = 0 then 0 else 1)"
 unfolding urel_integer_eq[OF x urel_integer_0] using urel_integer_0 urel_integer_1 by auto

lemma urel_integer_mod: 
assumes x: "urel_integer x x'" and y: "urel_integer y y'" 
shows "urel_integer (if y = 0 then x else 0) (if y' = 0 then x' else 0)"
  unfolding urel_integer_eq[OF y urel_integer_0] using urel_integer_0 x by auto 

lemma urel_integer_power: "urel_integer x x' \<Longrightarrow> urel_integer y (int y') \<Longrightarrow> urel_integer (power_p_integer pp x y) (power_p p x' y')"
proof (induct x' y' arbitrary: x y rule: power_p.induct[of _ p])
  case (1 x' y' x y)
  note x = 1(2) note y = 1(3)
  show ?case
  proof (cases "y' \<le> 0")
    case True
    hence y: "y = 0" "y' = 0" using urel_integer_eq[OF y urel_integer_0] by auto
    show ?thesis unfolding y True by (simp add: power_p.simps urel_integer_1)
  next
    case False
    hence id: "(y \<le> 0) = False" "(y' = 0) = False" using False y unfolding urel_integer_def
      by ((metis eq_iff nat_int nat_of_integer.rep_eq nat_of_integer_code)+)
    obtain d' r' where dr': "Divides.divmod_nat y' 2 = (d',r')" by force
    from divmod_nat_def[of y' 2, unfolded dr']
    have r': "r' = y' mod 2" and d': "d' = y' div 2" by auto
    have aux: "\<And> y'. int (y' mod 2) = int y' mod 2" by presburger
    have "urel_integer (y AND 1) r'" unfolding r' using y unfolding urel_integer_def 
      unfolding ppp
      by (smt aux bitAND_int_code int_and_1 mod2_gr_0 of_nat_0_le_iff of_nat_0_less_iff of_nat_1 one_integer.rep_eq p2 ppp) 
    from urel_integer_eq[OF this urel_integer_0]     
    have rem: "(y AND 1 = 0) = (r' = 0)" by simp
    have div: "urel_integer (shiftr y 1) (int d')" unfolding d' using y unfolding urel_integer_def
      unfolding ppp shiftr_integer_conv_div_pow2 by auto
    from id have "y' \<noteq> 0" by auto
    note IH = 1(1)[OF this refl dr'[symmetric] urel_integer_mult[OF x x] div]
    show ?thesis unfolding power_p.simps[of _ _ "y'"] power_p_integer.simps[of _ _ y] dr' id if_False rem
      using IH urel_integer_mult[OF IH x] by (auto simp: Let_def)
  qed
qed
  

lemma urel_integer_inverse: assumes x: "urel_integer x x'" 
  shows "urel_integer (inverse_p_integer pp x) (inverse_p p x')" 
proof -
  have p: "urel_integer (pp - 2) (int (nat (p - 2)))" using p2 unfolding urel_integer_def unfolding ppp
    by auto
  show ?thesis
    unfolding inverse_p_integer_def inverse_p_def urel_integer_eq[OF x urel_integer_0] using urel_integer_0 urel_integer_power[OF x p]
    by auto
qed

lemma mod_ring_0__integer: "mod_ring_rel_integer 0 0"
  using urel_integer_0 mod_ring_0 unfolding mod_ring_rel_integer_def by blast

lemma mod_ring_1__integer: "mod_ring_rel_integer 1 1"
  using urel_integer_1 mod_ring_1 unfolding mod_ring_rel_integer_def by blast

lemma mod_ring_uminus_integer: "(mod_ring_rel_integer ===> mod_ring_rel_integer) (uminus_p_integer pp) uminus"
  using urel_integer_uminus mod_ring_uminus unfolding mod_ring_rel_integer_def rel_fun_def by blast

lemma mod_ring_plus_integer: "(mod_ring_rel_integer ===> mod_ring_rel_integer ===> mod_ring_rel_integer) (plus_p_integer pp) (+)"
  using urel_integer_plus mod_ring_plus unfolding mod_ring_rel_integer_def rel_fun_def by blast

lemma mod_ring_minus_integer: "(mod_ring_rel_integer ===> mod_ring_rel_integer ===> mod_ring_rel_integer) (minus_p_integer pp) (-)"
  using urel_integer_minus mod_ring_minus unfolding mod_ring_rel_integer_def rel_fun_def by blast

lemma mod_ring_mult_integer: "(mod_ring_rel_integer ===> mod_ring_rel_integer ===> mod_ring_rel_integer) (mult_p_integer pp) ((*))"
  using urel_integer_mult mod_ring_mult unfolding mod_ring_rel_integer_def rel_fun_def by blast

lemma mod_ring_eq_integer: "(mod_ring_rel_integer ===> mod_ring_rel_integer ===> (=)) (=) (=)" 
  using urel_integer_eq mod_ring_eq unfolding mod_ring_rel_integer_def rel_fun_def by blast

lemma urel_integer_inj: "urel_integer x y \<Longrightarrow> urel_integer x z \<Longrightarrow> y = z" 
  using urel_integer_eq[of x y x z] by auto

lemma urel_integer_inj': "urel_integer x z \<Longrightarrow> urel_integer y z \<Longrightarrow> x = y" 
  using urel_integer_eq[of x z y z] by auto

lemma bi_unique_mod_ring_rel_integer:
  "bi_unique mod_ring_rel_integer" "left_unique mod_ring_rel_integer" "right_unique mod_ring_rel_integer"
  using bi_unique_mod_ring_rel urel_integer_inj'
  unfolding mod_ring_rel_integer_def bi_unique_def left_unique_def right_unique_def
  by (auto simp: urel_integer_def)  

lemma right_total_mod_ring_rel_integer: "right_total mod_ring_rel_integer"
  unfolding mod_ring_rel_integer_def right_total_def
proof 
  fix y :: "'a mod_ring" 
  from right_total_mod_ring_rel[unfolded right_total_def, rule_format, of y]
  obtain z where zy: "mod_ring_rel z y" by auto  
  hence zp: "0 \<le> z" "z < p" unfolding mod_ring_rel_def p using range_to_int_mod_ring[where 'a = 'a] by auto
  hence "urel_integer (integer_of_int z) z" unfolding urel_integer_def unfolding ppp 
    by auto 
  with zy show "\<exists> x z. urel_integer x z \<and> mod_ring_rel z y" by blast
qed

lemma Domainp_mod_ring_rel_integer: "Domainp mod_ring_rel_integer = (\<lambda>x. 0 \<le> x \<and> x < pp)"
proof 
  fix x
  show "Domainp mod_ring_rel_integer x = (0 \<le> x \<and> x < pp)"   
    unfolding Domainp.simps
    unfolding mod_ring_rel_integer_def
  proof
    let ?i = "int_of_integer" 
    assume *: "0 \<le> x \<and> x < pp"     
    hence "0 \<le> ?i x \<and> ?i x < p" unfolding ppp 
      by (simp add: le_int_of_integer less_integer.rep_eq)
    hence "?i x \<in> {0 ..< p}" by auto
    with Domainp_mod_ring_rel
    have "Domainp mod_ring_rel (?i x)" by auto
    from this[unfolded Domainp.simps]
    obtain b where b: "mod_ring_rel (?i x) b" by auto
    show "\<exists>a b. x = a \<and> (\<exists>z. urel_integer a z \<and> mod_ring_rel z b)" 
    proof (intro exI, rule conjI[OF refl], rule exI, rule conjI[OF _ b])
      show "urel_integer x (?i x)" unfolding urel_integer_def using * unfolding ppp
        by (simp add: le_int_of_integer less_integer.rep_eq)
    qed
  next
    assume "\<exists>a b. x = a \<and> (\<exists>z. urel_integer a z \<and> mod_ring_rel z b)" 
    then obtain b z where xz: "urel_integer x z" and zb: "mod_ring_rel z b" by auto
    hence "Domainp mod_ring_rel z"  by auto
    with Domainp_mod_ring_rel have "0 \<le> z" "z < p" by auto
    with xz show "0 \<le> x \<and> x < pp" unfolding urel_integer_def unfolding ppp
      by (simp add: le_int_of_integer less_integer.rep_eq)
  qed
qed

lemma ring_finite_field_ops_integer: "ring_ops (finite_field_ops_integer pp) mod_ring_rel_integer"
  by (unfold_locales, auto simp:
  finite_field_ops_integer_def
  bi_unique_mod_ring_rel_integer
  right_total_mod_ring_rel_integer
  mod_ring_plus_integer
  mod_ring_minus_integer
  mod_ring_uminus_integer
  mod_ring_mult_integer
  mod_ring_eq_integer
  mod_ring_0__integer
  mod_ring_1__integer
  Domainp_mod_ring_rel_integer)
end
end

context prime_field
begin
context fixes pp :: "integer" 
  assumes *: "p = int_of_integer pp"  
begin

lemma mod_ring_normalize_integer: "(mod_ring_rel_integer ===> mod_ring_rel_integer) (\<lambda>x. if x = 0 then 0 else 1) normalize" 
  using urel_integer_normalize[OF *] mod_ring_normalize unfolding mod_ring_rel_integer_def[OF *] rel_fun_def by blast

lemma mod_ring_mod_integer: "(mod_ring_rel_integer ===> mod_ring_rel_integer ===> mod_ring_rel_integer) (\<lambda>x y. if y = 0 then x else 0) (mod)" 
  using urel_integer_mod[OF *] mod_ring_mod unfolding mod_ring_rel_integer_def[OF *] rel_fun_def by blast

lemma mod_ring_unit_factor_integer: "(mod_ring_rel_integer ===> mod_ring_rel_integer) (\<lambda>x. x) unit_factor" 
  using mod_ring_unit_factor unfolding mod_ring_rel_integer_def[OF *] rel_fun_def by blast

lemma mod_ring_inverse_integer: "(mod_ring_rel_integer ===> mod_ring_rel_integer) (inverse_p_integer pp) inverse"
  using urel_integer_inverse[OF *] mod_ring_inverse unfolding mod_ring_rel_integer_def[OF *] rel_fun_def by blast

lemma mod_ring_divide_integer: "(mod_ring_rel_integer ===> mod_ring_rel_integer ===> mod_ring_rel_integer) (divide_p_integer pp) (/)"
  using mod_ring_inverse_integer mod_ring_mult_integer[OF *]
  unfolding divide_p_integer_def divide_mod_ring_def inverse_mod_ring_def[symmetric]
    rel_fun_def by blast

lemma finite_field_ops_integer: "field_ops (finite_field_ops_integer pp) mod_ring_rel_integer"
  by (unfold_locales, insert ring_finite_field_ops_integer[OF *], auto simp:
  ring_ops_def
  finite_field_ops_integer_def
  mod_ring_divide_integer
  mod_ring_inverse_integer
  mod_ring_mod_integer
  mod_ring_normalize_integer)
end
end

context prime_field
begin
 (* four implementations of modular integer arithmetic for finite fields *)
thm 
  finite_field_ops64
  finite_field_ops32
  finite_field_ops_integer
  finite_field_ops_int
end

context mod_ring_locale
begin
 (* four implementations of modular integer arithmetic for finite rings *)
thm 
  ring_finite_field_ops64
  ring_finite_field_ops32
  ring_finite_field_ops_integer
  ring_finite_field_ops_int
end

no_notation shiftr (infixl ">>" 55) (* to avoid conflict with bind *)
end
