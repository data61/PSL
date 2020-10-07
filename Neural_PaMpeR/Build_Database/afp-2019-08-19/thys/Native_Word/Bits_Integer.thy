(*  Title:      Bits_Integer.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Bit operations for target language integers\<close>

theory Bits_Integer imports
  More_Bits_Int
  Code_Symbolic_Bits_Int
begin

lemmas [transfer_rule] =
  identity_quotient
  fun_quotient
  Quotient_integer[folded integer.pcr_cr_eq]

lemma undefined_transfer:
  assumes "Quotient R Abs Rep T"
  shows "T (Rep undefined) undefined"
using assms unfolding Quotient_alt_def by blast

bundle undefined_transfer = undefined_transfer[transfer_rule]

section \<open>More lemmas about @{typ integer}s\<close>

context
includes integer.lifting
begin

lemma bitval_integer_transfer [transfer_rule]:
  "(rel_fun (=) pcr_integer) of_bool of_bool"
by(auto simp add: of_bool_def integer.pcr_cr_eq cr_integer_def)

lemma integer_of_nat_less_0_conv [simp]: "\<not> integer_of_nat n < 0"
by(transfer) simp

lemma int_of_integer_pow: "int_of_integer (x ^ n) = int_of_integer x ^ n"
by(induct n) simp_all

lemma pow_integer_transfer [transfer_rule]:
  "(rel_fun pcr_integer (rel_fun (=) pcr_integer)) (^) (^)"
by(auto 4 3 simp add: integer.pcr_cr_eq cr_integer_def int_of_integer_pow)

lemma sub1_lt_0_iff [simp]: "Code_Numeral.sub n num.One < 0 \<longleftrightarrow> False"
by(cases n)(simp_all add: Code_Numeral.sub_code)

lemma nat_of_integer_numeral [simp]: "nat_of_integer (numeral n) = numeral n"
by transfer simp

lemma nat_of_integer_sub1_conv_pred_numeral [simp]:
  "nat_of_integer (Code_Numeral.sub n num.One) = pred_numeral n"
by(cases n)(simp_all add: Code_Numeral.sub_code)

lemma nat_of_integer_1 [simp]: "nat_of_integer 1 = 1"
by transfer simp

lemma dup_1 [simp]: "Code_Numeral.dup 1 = 2"
by transfer simp


section \<open>Bit operations on @{typ integer}\<close>

text \<open>Bit operations on @{typ integer} are the same as on @{typ int}\<close>

lift_definition bin_rest_integer :: "integer \<Rightarrow> integer" is bin_rest .
lift_definition bin_last_integer :: "integer \<Rightarrow> bool" is bin_last .
lift_definition Bit_integer :: "integer \<Rightarrow> bool \<Rightarrow> integer" is Bit .

end

instantiation integer :: bit_operations begin
context includes integer.lifting begin

lift_definition bitAND_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" is "bitAND" .
lift_definition bitOR_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" is "bitOR" .
lift_definition bitXOR_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer" is "bitXOR" .
lift_definition bitNOT_integer :: "integer \<Rightarrow> integer" is "bitNOT" .

lift_definition test_bit_integer :: "integer \<Rightarrow> nat \<Rightarrow> bool" is test_bit .
lift_definition lsb_integer :: "integer \<Rightarrow> bool" is lsb .
lift_definition set_bit_integer :: "integer \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> integer" is set_bit .
lift_definition shiftl_integer :: "integer \<Rightarrow> nat \<Rightarrow> integer" is shiftl .
lift_definition shiftr_integer :: "integer \<Rightarrow> nat \<Rightarrow> integer" is shiftr .

lift_definition msb_integer :: "integer \<Rightarrow> bool" is msb .
instance ..
end
end

abbreviation (input) wf_set_bits_integer
where "wf_set_bits_integer \<equiv> wf_set_bits_int"


section \<open>Target language implementations\<close>

text \<open>
  Unfortunately, this is not straightforward,
  because these API functions have different signatures and preconditions on the parameters:

  \begin{description}
  \item[Standard ML] Shifts in IntInf are given as word, but not IntInf.
  \item[Haskell] In the Data.Bits.Bits type class, shifts and bit indices are given as Int rather than Integer.
  \end{description}

  Additional constants take only parameters of type @{typ integer} rather than @{typ nat}
  and check the preconditions as far as possible (e.g., being non-negative) in a portable way.
  Manual implementations inside code\_printing perform the remaining range checks and convert 
  these @{typ integer}s into the right type.

  For normalisation by evaluation, we derive custom code equations, because NBE
  does not know these code\_printing serialisations and would otherwise loop.
\<close>

code_identifier code_module Bits_Integer \<rightharpoonup>
  (SML) Bits_Int and (OCaml) Bits_Int and (Haskell) Bits_Int and (Scala) Bits_Int

code_printing code_module Bits_Integer \<rightharpoonup> (SML)
\<open>structure Bits_Integer : sig
  val set_bit : IntInf.int -> IntInf.int -> bool -> IntInf.int
  val shiftl : IntInf.int -> IntInf.int -> IntInf.int
  val shiftr : IntInf.int -> IntInf.int -> IntInf.int
  val test_bit : IntInf.int -> IntInf.int -> bool
end = struct

val maxWord = IntInf.pow (2, Word.wordSize);

fun set_bit x n b =
  if n < maxWord then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun shiftl x n =
  if n < maxWord then IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

end; (*struct Bits_Integer*)\<close>
code_reserved SML Bits_Integer

code_printing code_module Bits_Integer \<rightharpoonup> (OCaml)
\<open>module Bits_Integer : sig
  val shiftl : Z.t -> Z.t -> Z.t
  val shiftr : Z.t -> Z.t -> Z.t
  val test_bit : Z.t -> Z.t -> bool
end = struct

(* We do not need an explicit range checks here,
   because Big_int.int_of_big_int raises Failure 
   if the argument does not fit into an int. *)
let shiftl x n = Z.shift_left x (Z.to_int n);;

let shiftr x n = Z.shift_right x (Z.to_int n);;

let test_bit x n =  Z.testbit x (Z.to_int n);;

end;; (*struct Bits_Integer*)\<close>
code_reserved OCaml Bits_Integer

code_printing code_module Data_Bits \<rightharpoonup> (Haskell)
\<open>
module Data_Bits where {

import qualified Data.Bits;

{-
  The ...Bounded functions assume that the Integer argument for the shift 
  or bit index fits into an Int, is non-negative and (for types of fixed bit width)
  less than bitSize
-}

infixl 7 .&.;
infixl 6 `xor`;
infixl 5 .|.;

(.&.) :: Data.Bits.Bits a => a -> a -> a;
(.&.) = (Data.Bits..&.);

xor :: Data.Bits.Bits a => a -> a -> a;
xor = Data.Bits.xor;

(.|.) :: Data.Bits.Bits a => a -> a -> a;
(.|.) = (Data.Bits..|.);

complement :: Data.Bits.Bits a => a -> a;
complement = Data.Bits.complement;

testBitUnbounded :: Data.Bits.Bits a => a -> Integer -> Bool;
testBitUnbounded x b
  | b <= toInteger (Prelude.maxBound :: Int) = Data.Bits.testBit x (fromInteger b)
  | otherwise = error ("Bit index too large: " ++ show b)
;

testBitBounded :: Data.Bits.Bits a => a -> Integer -> Bool;
testBitBounded x b = Data.Bits.testBit x (fromInteger b);

setBitUnbounded :: Data.Bits.Bits a => a -> Integer -> Bool -> a;
setBitUnbounded x n b
  | n <= toInteger (Prelude.maxBound :: Int) = 
    if b then Data.Bits.setBit x (fromInteger n) else Data.Bits.clearBit x (fromInteger n)
  | otherwise = error ("Bit index too large: " ++ show n)
;

setBitBounded :: Data.Bits.Bits a => a -> Integer -> Bool -> a;
setBitBounded x n True = Data.Bits.setBit x (fromInteger n);
setBitBounded x n False = Data.Bits.clearBit x (fromInteger n);

shiftlUnbounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftlUnbounded x n 
  | n <= toInteger (Prelude.maxBound :: Int) = Data.Bits.shiftL x (fromInteger n)
  | otherwise = error ("Shift operand too large: " ++ show n)
;

shiftlBounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftlBounded x n = Data.Bits.shiftL x (fromInteger n);

shiftrUnbounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftrUnbounded x n 
  | n <= toInteger (Prelude.maxBound :: Int) = Data.Bits.shiftR x (fromInteger n)
  | otherwise = error ("Shift operand too large: " ++ show n)
;

shiftrBounded :: (Ord a, Data.Bits.Bits a) => a -> Integer -> a;
shiftrBounded x n = Data.Bits.shiftR x (fromInteger n);

}\<close>

  and \<comment> \<open>@{theory HOL.Quickcheck_Narrowing} maps @{typ integer} to 
            Haskell's Prelude.Int type instead of Integer. For compatibility
            with the Haskell target, we nevertheless provide bounded and 
            unbounded functions.\<close>
  (Haskell_Quickcheck)
\<open>
module Data_Bits where {

import qualified Data.Bits;

{-
  The functions assume that the Int argument for the shift or bit index is 
  non-negative and (for types of fixed bit width) less than bitSize
-}

infixl 7 .&.;
infixl 6 `xor`;
infixl 5 .|.;

(.&.) :: Data.Bits.Bits a => a -> a -> a;
(.&.) = (Data.Bits..&.);

xor :: Data.Bits.Bits a => a -> a -> a;
xor = Data.Bits.xor;

(.|.) :: Data.Bits.Bits a => a -> a -> a;
(.|.) = (Data.Bits..|.);

complement :: Data.Bits.Bits a => a -> a;
complement = Data.Bits.complement;

testBitUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool;
testBitUnbounded = Data.Bits.testBit;

testBitBounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool;
testBitBounded = Data.Bits.testBit;

setBitUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool -> a;
setBitUnbounded x n True = Data.Bits.setBit x n;
setBitUnbounded x n False = Data.Bits.clearBit x n;

setBitBounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool -> a;
setBitBounded x n True = Data.Bits.setBit x n;
setBitBounded x n False = Data.Bits.clearBit x n;

shiftlUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> a;
shiftlUnbounded = Data.Bits.shiftL;

shiftlBounded :: Data.Bits.Bits a => a -> Prelude.Int -> a;
shiftlBounded = Data.Bits.shiftL;

shiftrUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> a;
shiftrUnbounded = Data.Bits.shiftR;

shiftrBounded :: (Ord a, Data.Bits.Bits a) => a -> Prelude.Int -> a;
shiftrBounded = Data.Bits.shiftR;

}\<close>
code_reserved Haskell Data_Bits

code_printing code_module Bits_Integer \<rightharpoonup> (Scala)
\<open>object Bits_Integer {

def setBit(x: BigInt, n: BigInt, b: Boolean) : BigInt =
  if (n.isValidInt)
    if (b)
      x.setBit(n.toInt)
    else
      x.clearBit(n.toInt)
  else
    sys.error("Bit index too large: " + n.toString)

def shiftl(x: BigInt, n: BigInt) : BigInt =
  if (n.isValidInt)
    x << n.toInt
  else
    sys.error("Shift index too large: " + n.toString)

def shiftr(x: BigInt, n: BigInt) : BigInt =
  if (n.isValidInt)
    x << n.toInt
  else
    sys.error("Shift index too large: " + n.toString)

def testBit(x: BigInt, n: BigInt) : Boolean =
  if (n.isValidInt)
    x.testBit(n.toInt) 
  else
    sys.error("Bit index too large: " + n.toString)

} /* object Bits_Integer */\<close>

code_printing
  constant "bitAND :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup>
  (SML) "IntInf.andb ((_),/ (_))" and
  (OCaml) "Z.logand" and
  (Haskell) "((Data'_Bits..&.) :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "((Data'_Bits..&.) :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) infixl 3 "&"
| constant "bitOR :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup>
  (SML) "IntInf.orb ((_),/ (_))" and
  (OCaml) "Z.logor" and
  (Haskell) "((Data'_Bits..|.) :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "((Data'_Bits..|.) :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) infixl 1 "|"
| constant "bitXOR :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup>
  (SML) "IntInf.xorb ((_),/ (_))" and
  (OCaml) "Z.logxor" and
  (Haskell) "(Data'_Bits.xor :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.xor :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) infixl 2 "^"
| constant "bitNOT :: integer \<Rightarrow> integer" \<rightharpoonup>
  (SML) "IntInf.notb" and
  (OCaml) "Z.lognot" and
  (Haskell) "(Data'_Bits.complement :: Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.complement :: Prelude.Int -> Prelude.Int)" and
  (Scala) "_.unary'_~"

code_printing constant bin_rest_integer \<rightharpoonup>
  (SML) "IntInf.div ((_), 2)" and
  (OCaml) "Z.shift'_right/ _/ 1" and
  (Haskell) "(Data'_Bits.shiftrUnbounded _ 1 :: Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.shiftrUnbounded _ 1 :: Prelude.Int)" and
  (Scala) "_ >> 1"

context
includes integer.lifting
begin

lemma bitNOT_integer_code [code]:
  fixes i :: integer shows
  "NOT i = - i - 1"
by transfer(simp add: int_not_def)

lemma bin_rest_integer_code [code nbe]:
  "bin_rest_integer i = i div 2"
by transfer(simp add: bin_rest_def)

lemma bin_last_integer_code [code]:
  "bin_last_integer i \<longleftrightarrow> i AND 1 \<noteq> 0"
by transfer(rule bin_last_conv_AND)

lemma bin_last_integer_nbe [code nbe]:
  "bin_last_integer i \<longleftrightarrow> i mod 2 \<noteq> 0"
by transfer(simp add: bin_last_def)

lemma bitval_bin_last_integer [code_unfold]:
  "of_bool (bin_last_integer i) = i AND 1"
by transfer(rule bitval_bin_last)

end

definition integer_test_bit :: "integer \<Rightarrow> integer \<Rightarrow> bool"
  where "integer_test_bit x n = (if n < 0 then undefined x n else x !! nat_of_integer n)"

lemma test_bit_integer_code [code]:
  "x !! n \<longleftrightarrow> integer_test_bit x (integer_of_nat n)"
by(simp add: integer_test_bit_def)

lemma integer_test_bit_code [code]:
  "integer_test_bit x (Code_Numeral.Neg n) = undefined x (Code_Numeral.Neg n)"
  "integer_test_bit 0 0 = False"
  "integer_test_bit 0 (Code_Numeral.Pos n) = False"
  "integer_test_bit (Code_Numeral.Pos num.One)      0 = True"
  "integer_test_bit (Code_Numeral.Pos (num.Bit0 n)) 0 = False"
  "integer_test_bit (Code_Numeral.Pos (num.Bit1 n)) 0 = True"
  "integer_test_bit (Code_Numeral.Pos num.One)      (Code_Numeral.Pos n') = False"
  "integer_test_bit (Code_Numeral.Pos (num.Bit0 n)) (Code_Numeral.Pos n') =
   integer_test_bit (Code_Numeral.Pos n) (Code_Numeral.sub n' num.One)"
  "integer_test_bit (Code_Numeral.Pos (num.Bit1 n)) (Code_Numeral.Pos n') =
   integer_test_bit (Code_Numeral.Pos n) (Code_Numeral.sub n' num.One)"
  "integer_test_bit (Code_Numeral.Neg num.One)      0 = True"
  "integer_test_bit (Code_Numeral.Neg (num.Bit0 n)) 0 = False"
  "integer_test_bit (Code_Numeral.Neg (num.Bit1 n)) 0 = True"
  "integer_test_bit (Code_Numeral.Neg num.One)      (Code_Numeral.Pos n') = True"
  "integer_test_bit (Code_Numeral.Neg (num.Bit0 n)) (Code_Numeral.Pos n') =
   integer_test_bit (Code_Numeral.Neg n) (Code_Numeral.sub n' num.One)"
  "integer_test_bit (Code_Numeral.Neg (num.Bit1 n)) (Code_Numeral.Pos n') =
   integer_test_bit (Code_Numeral.Neg (n + num.One)) (Code_Numeral.sub n' num.One)"
by(simp_all add: integer_test_bit_def test_bit_integer_def)

code_printing constant integer_test_bit \<rightharpoonup>
  (SML) "Bits'_Integer.test'_bit" and
  (OCaml) "Bits'_Integer.test'_bit" and
  (Haskell) "(Data'_Bits.testBitUnbounded :: Integer -> Integer -> Bool)" and
  (Haskell_Quickcheck) "(Data'_Bits.testBitUnbounded :: Prelude.Int -> Prelude.Int -> Bool)" and
  (Scala) "Bits'_Integer.testBit"

context
includes integer.lifting
begin

lemma lsb_integer_code [code]:
  fixes x :: integer shows
  "lsb x = x !! 0"
by transfer(simp add: lsb_int_def)

definition integer_set_bit :: "integer \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> integer"
where [code del]: "integer_set_bit x n b = (if n < 0 then undefined x n b else set_bit x (nat_of_integer n) b)"

lemma set_bit_integer_code [code]:
  "set_bit x i b = integer_set_bit x (integer_of_nat i) b"
by(simp add: integer_set_bit_def)

lemma set_bit_integer_conv_masks: 
  fixes x :: integer shows
  "set_bit x i b = (if b then x OR (1 << i) else x AND NOT (1 << i))"
by transfer(simp add: int_set_bit_conv_ops)

end

code_printing constant integer_set_bit \<rightharpoonup>
  (SML) "Bits'_Integer.set'_bit" and
  (Haskell) "(Data'_Bits.setBitUnbounded :: Integer -> Integer -> Bool -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.setBitUnbounded :: Prelude.Int -> Prelude.Int -> Bool -> Prelude.Int)" and
  (Scala) "Bits'_Integer.setBit"

text \<open>
  OCaml.Big\_int does not have a method for changing an individual bit, so we emulate that with masks.
  We prefer an Isabelle implementation, because this then takes care of the signs for AND and OR.
\<close>
lemma integer_set_bit_code [code]:
  "integer_set_bit x n b =
  (if n < 0 then undefined x n b else
   if b then x OR (1 << nat_of_integer n)
   else x AND NOT (1 << nat_of_integer n))"
by(auto simp add: integer_set_bit_def set_bit_integer_conv_masks)

definition integer_shiftl :: "integer \<Rightarrow> integer \<Rightarrow> integer"
where [code del]: "integer_shiftl x n = (if n < 0 then undefined x n else x << nat_of_integer n)"

lemma shiftl_integer_code [code]: 
  fixes x :: integer shows
  "x << n = integer_shiftl x (integer_of_nat n)"
by(auto simp add: integer_shiftl_def)

context
includes integer.lifting
begin

lemma shiftl_integer_conv_mult_pow2:
  fixes x :: integer shows
  "x << n = x * 2 ^ n"
by transfer(simp add: shiftl_int_def)

lemma integer_shiftl_code [code]:
  "integer_shiftl x (Code_Numeral.Neg n) = undefined x (Code_Numeral.Neg n)"
  "integer_shiftl x 0 = x"
  "integer_shiftl x (Code_Numeral.Pos n) = integer_shiftl (Code_Numeral.dup x) (Code_Numeral.sub n num.One)"
  "integer_shiftl 0 (Code_Numeral.Pos n) = 0"
  by (simp_all add: integer_shiftl_def shiftl_integer_def shiftl_int_def numeral_eq_Suc)
    (transfer, simp)

end

code_printing constant integer_shiftl \<rightharpoonup>
  (SML) "Bits'_Integer.shiftl" and
  (OCaml) "Bits'_Integer.shiftl" and
  (Haskell) "(Data'_Bits.shiftlUnbounded :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.shiftlUnbounded :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) "Bits'_Integer.shiftl"

definition integer_shiftr :: "integer \<Rightarrow> integer \<Rightarrow> integer"
where [code del]: "integer_shiftr x n = (if n < 0 then undefined x n else x >> nat_of_integer n)"

lemma shiftr_integer_conv_div_pow2: 
  includes integer.lifting fixes x :: integer shows
  "x >> n = x div 2 ^ n"
by transfer(simp add: shiftr_int_def)

lemma shiftr_integer_code [code]:
  fixes x :: integer shows
  "x >> n = integer_shiftr x (integer_of_nat n)"
by(auto simp add: integer_shiftr_def)

code_printing constant integer_shiftr \<rightharpoonup>
  (SML) "Bits'_Integer.shiftr" and
  (OCaml) "Bits'_Integer.shiftr" and
  (Haskell) "(Data'_Bits.shiftrUnbounded :: Integer -> Integer -> Integer)" and
  (Haskell_Quickcheck) "(Data'_Bits.shiftrUnbounded :: Prelude.Int -> Prelude.Int -> Prelude.Int)" and
  (Scala) "Bits'_Integer.shiftr"

lemma integer_shiftr_code [code]:
  "integer_shiftr x (Code_Numeral.Neg n) = undefined x (Code_Numeral.Neg n)"
  "integer_shiftr x 0 = x"
  "integer_shiftr 0 (Code_Numeral.Pos n) = 0"
  "integer_shiftr (Code_Numeral.Pos num.One) (Code_Numeral.Pos n) = 0"
  "integer_shiftr (Code_Numeral.Pos (num.Bit0 n')) (Code_Numeral.Pos n) = 
   integer_shiftr (Code_Numeral.Pos n') (Code_Numeral.sub n num.One)"
  "integer_shiftr (Code_Numeral.Pos (num.Bit1 n')) (Code_Numeral.Pos n) = 
   integer_shiftr (Code_Numeral.Pos n') (Code_Numeral.sub n num.One)"
  "integer_shiftr (Code_Numeral.Neg num.One) (Code_Numeral.Pos n) = -1"
  "integer_shiftr (Code_Numeral.Neg (num.Bit0 n')) (Code_Numeral.Pos n) = 
   integer_shiftr (Code_Numeral.Neg n') (Code_Numeral.sub n num.One)"
  "integer_shiftr (Code_Numeral.Neg (num.Bit1 n')) (Code_Numeral.Pos n) = 
   integer_shiftr (Code_Numeral.Neg (Num.inc n')) (Code_Numeral.sub n num.One)"
by(simp_all add: integer_shiftr_def shiftr_integer_def)

context
includes integer.lifting
begin

lemma Bit_integer_code [code]:
  "Bit_integer i False = i << 1"
  "Bit_integer i True = (i << 1) + 1"
by(transfer, simp add: Bit_def shiftl_int_def)+

lemma msb_integer_code [code]:
  "msb (x :: integer) \<longleftrightarrow> x < 0"
by transfer(simp add: msb_int_def)

end

context
includes integer.lifting natural.lifting
begin

lemma bitAND_integer_unfold [code]:
  "x AND y =
   (if x = 0 then 0
    else if x = - 1 then y
    else Bit_integer (bin_rest_integer x AND bin_rest_integer y) (bin_last_integer x \<and> bin_last_integer y))"
  by transfer (fact bitAND_int.simps)

lemma bitOR_integer_unfold [code]:
  "x OR y =
   (if x = 0 then y
    else if x = - 1 then - 1
    else Bit_integer (bin_rest_integer x OR bin_rest_integer y) (bin_last_integer x \<or> bin_last_integer y))"
proof transfer
  fix x y :: int
  from int_or_Bits [of "bin_rest x" "bin_last x" "bin_rest y" "bin_last y"]
  have "(bin_rest x OR bin_rest y) BIT (bin_last x \<or> bin_last y) = x OR y"
    by simp
  then show "x OR y =
    (if x = 0 then y
     else if x = - 1 then - 1
     else Bit (bin_rest x OR bin_rest y) (bin_last x \<or> bin_last y))"
    by simp
qed

lemma bitXOR_integer_unfold [code]:
  "x XOR y =
   (if x = 0 then y
    else if x = - 1 then NOT y
    else Bit_integer (bin_rest_integer x XOR bin_rest_integer y)
      (\<not> bin_last_integer x \<longleftrightarrow> bin_last_integer y))"
proof transfer
  fix x y :: int
  from int_xor_Bits [of "bin_rest x" "bin_last x" "bin_rest y" "bin_last y"]
  have "(bin_rest x XOR bin_rest y) BIT
    ((bin_last x \<or> bin_last y) \<and> (bin_last x \<longrightarrow> \<not> bin_last y)) = x XOR y"
    by simp
  also have "(bin_last x \<or> bin_last y) \<and> (bin_last x \<longrightarrow> \<not> bin_last y) \<longleftrightarrow> (\<not> bin_last x \<longleftrightarrow> bin_last y)"
    by auto
  finally show "x XOR y =
   (if x = 0 then y
    else if x = - 1 then NOT y
    else Bit (bin_rest x XOR bin_rest y)
      (\<not> bin_last x \<longleftrightarrow> bin_last y))"
    by simp
qed

end


section \<open>Test code generator setup\<close>

definition bit_integer_test :: "bool" where
  "bit_integer_test =
  (([ -1 AND 3, 1 AND -3, 3 AND 5, -3 AND (- 5)
    , -3 OR 1, 1 OR -3, 3 OR 5, -3 OR (- 5)
    , NOT 1, NOT (- 3)
    , -1 XOR 3, 1 XOR (- 3), 3 XOR 5, -5 XOR (- 3)
    , set_bit 5 4 True, set_bit (- 5) 2 True, set_bit 5 0 False, set_bit (- 5) 1 False
    , 1 << 2, -1 << 3
    , 100 >> 3, -100 >> 3] :: integer list)
  = [ 3, 1, 1, -7
    , -3, -3, 7, -1
    , -2, 2
    , -4, -4, 6, 6
    , 21, -1, 4, -7
    , 4, -8
    , 12, -13] \<and>
    [ (5 :: integer) !! 4, (5 :: integer) !! 2, (-5 :: integer) !! 4, (-5 :: integer) !! 2
    , lsb (5 :: integer), lsb (4 :: integer), lsb (-1 :: integer), lsb (-2 :: integer), 
      msb (5 :: integer), msb (0 :: integer), msb (-1 :: integer), msb (-2 :: integer)]
  = [ False, True, True, False,
      True, False, True, False,
      False, False, True, True])"

export_code bit_integer_test checking SML Haskell? Haskell_Quickcheck? OCaml? Scala

notepad begin
have bit_integer_test by eval
have bit_integer_test by normalization
have bit_integer_test by code_simp
end
ML_val \<open>val true = @{code bit_integer_test}\<close>

lemma "x AND y = x OR (y :: integer)"
quickcheck[random, expect=counterexample]
quickcheck[exhaustive, expect=counterexample]
oops

lemma "(x :: integer) AND x = x OR x"
quickcheck[narrowing, expect=no_counterexample]
oops

lemma "(f :: integer \<Rightarrow> unit) = g"
quickcheck[narrowing, size=3, expect=no_counterexample]
by(simp add: fun_eq_iff)

hide_const bit_integer_test
hide_fact bit_integer_test_def

end
