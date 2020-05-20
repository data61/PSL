(*  Title:      Uint64.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Unsigned words of 64 bits\<close>

theory Uint64 imports
  Code_Target_Word_Base
begin

text \<open>
  PolyML (in version 5.7) provides a Word64 structure only when run in 64-bit mode.
  Therefore, we by default provide an implementation of 64-bit words using \verb$IntInf.int$ and
  masking. The code target \texttt{SML\_word} replaces this implementation and maps the operations
  directly to the \verb$Word64$ structure provided by the Standard ML implementations.

  The \verb$Eval$ target used by @{command value} and @{method eval} dynamically tests at
  runtime for the version of PolyML and uses PolyML's Word64 structure if it detects a 64-bit 
  version which does not suffer from a division bug found in PolyML 5.6.
\<close>

declare prod.Quotient[transfer_rule]

section \<open>Type definition and primitive operations\<close>

typedef uint64 = "UNIV :: 64 word set" .. 

setup_lifting type_definition_uint64

text \<open>Use an abstract type for code generation to disable pattern matching on @{term Abs_uint64}.\<close>
declare Rep_uint64_inverse[code abstype]

declare Quotient_uint64[transfer_rule]

instantiation uint64 :: "{neg_numeral, modulo, comm_monoid_mult, comm_ring}" begin
lift_definition zero_uint64 :: uint64 is "0 :: 64 word" .
lift_definition one_uint64 :: uint64 is "1" .
lift_definition plus_uint64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" is "(+) :: 64 word \<Rightarrow> _" .
lift_definition minus_uint64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" is "(-)" .
lift_definition uminus_uint64 :: "uint64 \<Rightarrow> uint64" is uminus .
lift_definition times_uint64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" is "(*)" .
lift_definition divide_uint64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" is "(div)" .
lift_definition modulo_uint64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" is "(mod)" .
instance by standard (transfer, simp add: algebra_simps)+
end

instantiation uint64 :: linorder begin
lift_definition less_uint64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> bool" is "(<)" .
lift_definition less_eq_uint64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> bool" is "(\<le>)" .
instance by standard (transfer, simp add: less_le_not_le linear)+
end

lemmas [code] = less_uint64.rep_eq less_eq_uint64.rep_eq

instantiation uint64 :: bit_operations begin
lift_definition bitNOT_uint64 :: "uint64 \<Rightarrow> uint64" is bitNOT .
lift_definition bitAND_uint64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" is bitAND .
lift_definition bitOR_uint64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" is bitOR .
lift_definition bitXOR_uint64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" is bitXOR .
lift_definition test_bit_uint64 :: "uint64 \<Rightarrow> nat \<Rightarrow> bool" is test_bit .
lift_definition set_bit_uint64 :: "uint64 \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> uint64" is set_bit .
lift_definition lsb_uint64 :: "uint64 \<Rightarrow> bool" is lsb .
lift_definition shiftl_uint64 :: "uint64 \<Rightarrow> nat \<Rightarrow> uint64" is shiftl .
lift_definition shiftr_uint64 :: "uint64 \<Rightarrow> nat \<Rightarrow> uint64" is shiftr .
lift_definition msb_uint64 :: "uint64 \<Rightarrow> bool" is msb .
instance ..
end

instantiation uint64 :: bit_comprehension begin
lift_definition set_bits_uint64 :: "(nat \<Rightarrow> bool) \<Rightarrow> uint64" is "set_bits" .
instance ..
end

lemmas [code] = test_bit_uint64.rep_eq lsb_uint64.rep_eq msb_uint64.rep_eq

instantiation uint64 :: equal begin
lift_definition equal_uint64 :: "uint64 \<Rightarrow> uint64 \<Rightarrow> bool" is "equal_class.equal" .
instance by standard (transfer, simp add: equal_eq)
end

lemmas [code] = equal_uint64.rep_eq

instantiation uint64 :: size begin
lift_definition size_uint64 :: "uint64 \<Rightarrow> nat" is "size" .
instance ..
end

lemmas [code] = size_uint64.rep_eq

lift_definition sshiftr_uint64 :: "uint64 \<Rightarrow> nat \<Rightarrow> uint64" (infixl ">>>" 55) is sshiftr .

lift_definition uint64_of_int :: "int \<Rightarrow> uint64" is "word_of_int" .

definition uint64_of_nat :: "nat \<Rightarrow> uint64"
where "uint64_of_nat = uint64_of_int \<circ> int"

lift_definition int_of_uint64 :: "uint64 \<Rightarrow> int" is "uint" .
lift_definition nat_of_uint64 :: "uint64 \<Rightarrow> nat" is "unat" .

definition integer_of_uint64 :: "uint64 \<Rightarrow> integer"
where "integer_of_uint64 = integer_of_int o int_of_uint64"

lemma bitval_integer_transfer [transfer_rule]:
  "(rel_fun (=) pcr_integer) of_bool of_bool"
by(auto simp add: of_bool_def integer.pcr_cr_eq cr_integer_def split: bit.split)

text \<open>Use pretty numerals from integer for pretty printing\<close>

context includes integer.lifting begin

lift_definition Uint64 :: "integer \<Rightarrow> uint64" is "word_of_int" .

lemma Rep_uint64_numeral [simp]: "Rep_uint64 (numeral n) = numeral n"
by(induction n)(simp_all add: one_uint64_def Abs_uint64_inverse numeral.simps plus_uint64_def)

lemma numeral_uint64_transfer [transfer_rule]:
  "(rel_fun (=) cr_uint64) numeral numeral"
by(auto simp add: cr_uint64_def)

lemma numeral_uint64 [code_unfold]: "numeral n = Uint64 (numeral n)"
by transfer simp

lemma Rep_uint64_neg_numeral [simp]: "Rep_uint64 (- numeral n) = - numeral n"
by(simp only: uminus_uint64_def)(simp add: Abs_uint64_inverse)

lemma neg_numeral_uint64 [code_unfold]: "- numeral n = Uint64 (- numeral n)"
by transfer(simp add: cr_uint64_def)

end

lemma Abs_uint64_numeral [code_post]: "Abs_uint64 (numeral n) = numeral n"
by(induction n)(simp_all add: one_uint64_def numeral.simps plus_uint64_def Abs_uint64_inverse)

lemma Abs_uint64_0 [code_post]: "Abs_uint64 0 = 0"
by(simp add: zero_uint64_def)

lemma Abs_uint64_1 [code_post]: "Abs_uint64 1 = 1"
by(simp add: one_uint64_def)

section \<open>Code setup\<close>

text \<open> For SML, we generate an implementation of unsigned 64-bit words using \verb$IntInf.int$.
  If @{ML "LargeWord.wordSize > 63"} of the Isabelle/ML runtime environment holds, then we assume
  that there is also a \<open>Word64\<close> structure available and accordingly replace the implementation
  for the target \verb$Eval$.
\<close>
code_printing code_module "Uint64" \<rightharpoonup> (SML) \<open>(* Test that words can handle numbers between 0 and 63 *)
val _ = if 6 <= Word.wordSize then () else raise (Fail ("wordSize less than 6"));

structure Uint64 : sig
  eqtype uint64;
  val zero : uint64;
  val one : uint64;
  val fromInt : IntInf.int -> uint64;
  val toInt : uint64 -> IntInf.int;
  val toLarge : uint64 -> LargeWord.word;
  val fromLarge : LargeWord.word -> uint64
  val plus : uint64 -> uint64 -> uint64;
  val minus : uint64 -> uint64 -> uint64;
  val times : uint64 -> uint64 -> uint64;
  val divide : uint64 -> uint64 -> uint64;
  val modulus : uint64 -> uint64 -> uint64;
  val negate : uint64 -> uint64;
  val less_eq : uint64 -> uint64 -> bool;
  val less : uint64 -> uint64 -> bool;
  val notb : uint64 -> uint64;
  val andb : uint64 -> uint64 -> uint64;
  val orb : uint64 -> uint64 -> uint64;
  val xorb : uint64 -> uint64 -> uint64;
  val shiftl : uint64 -> IntInf.int -> uint64;
  val shiftr : uint64 -> IntInf.int -> uint64;
  val shiftr_signed : uint64 -> IntInf.int -> uint64;
  val set_bit : uint64 -> IntInf.int -> bool -> uint64;
  val test_bit : uint64 -> IntInf.int -> bool;
end = struct

type uint64 = IntInf.int;

val mask = 0xFFFFFFFFFFFFFFFF : IntInf.int;

val zero = 0 : IntInf.int;

val one = 1 : IntInf.int;

fun fromInt x = IntInf.andb(x, mask);

fun toInt x = x

fun toLarge x = LargeWord.fromLargeInt (IntInf.toLarge x);

fun fromLarge x = IntInf.fromLarge (LargeWord.toLargeInt x);

fun plus x y = IntInf.andb(IntInf.+(x, y), mask);

fun minus x y = IntInf.andb(IntInf.-(x, y), mask);

fun negate x = IntInf.andb(IntInf.~(x), mask);

fun times x y = IntInf.andb(IntInf.*(x, y), mask);

fun divide x y = IntInf.div(x, y);

fun modulus x y = IntInf.mod(x, y);

fun less_eq x y = IntInf.<=(x, y);

fun less x y = IntInf.<(x, y);

fun notb x = IntInf.andb(IntInf.notb(x), mask);

fun orb x y = IntInf.orb(x, y);

fun andb x y = IntInf.andb(x, y);

fun xorb x y = IntInf.xorb(x, y);

val maxWord = IntInf.pow (2, Word.wordSize);

fun shiftl x n = 
  if n < maxWord then IntInf.andb(IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n)), mask)
  else 0;

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else 0;

val msb_mask = 0x8000000000000000 : IntInf.int;

fun shiftr_signed x i =
  if IntInf.andb(x, msb_mask) = 0 then shiftr x i
  else if i >= 64 then 0xFFFFFFFFFFFFFFFF
  else let
    val x' = shiftr x i
    val m' = IntInf.andb(IntInf.<<(mask, Word.max(0w64 - Word.fromLargeInt (IntInf.toLarge i), 0w0)), mask)
  in IntInf.orb(x', m') end;

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else false;

fun set_bit x n b =
  if n < 64 then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else x;

end
\<close>
code_reserved SML Uint64

setup \<open>
let
  val polyml64 = LargeWord.wordSize > 63;
  (* PolyML 5.6 has bugs in its Word64 implementation. We test for one such bug and refrain
     from using Word64 in that case. Testing is done with dynamic code evaluation such that
     the compiler does not choke on the Word64 structure, which need not be present in a 32bit
     environment. *)
  val error_msg = "Buggy Word64 structure";
  val test_code = 
   "val _ = if Word64.div (0w18446744073709551611 : Word64.word, 0w3) = 0w6148914691236517203 then ()\n" ^
   "else raise (Fail \"" ^ error_msg ^ "\");";
  val f = Exn.interruptible_capture (fn () => ML_Compiler.eval ML_Compiler.flags Position.none (ML_Lex.tokenize test_code))
  val use_Word64 = polyml64 andalso
    (case f () of 
       Exn.Res _ => true
     | Exn.Exn (e as ERROR m) => if String.isSuffix error_msg m then false else Exn.reraise e
     | Exn.Exn e => Exn.reraise e)
    ;

  val newline = "\n";
  val content = 
    "structure Uint64 : sig" ^ newline ^
    "  eqtype uint64;" ^ newline ^
    "  val zero : uint64;" ^ newline ^
    "  val one : uint64;" ^ newline ^
    "  val fromInt : IntInf.int -> uint64;" ^ newline ^
    "  val toInt : uint64 -> IntInf.int;" ^ newline ^
    "  val toLarge : uint64 -> LargeWord.word;" ^ newline ^
    "  val fromLarge : LargeWord.word -> uint64" ^ newline ^
    "  val plus : uint64 -> uint64 -> uint64;" ^ newline ^
    "  val minus : uint64 -> uint64 -> uint64;" ^ newline ^
    "  val times : uint64 -> uint64 -> uint64;" ^ newline ^
    "  val divide : uint64 -> uint64 -> uint64;" ^ newline ^
    "  val modulus : uint64 -> uint64 -> uint64;" ^ newline ^
    "  val negate : uint64 -> uint64;" ^ newline ^
    "  val less_eq : uint64 -> uint64 -> bool;" ^ newline ^
    "  val less : uint64 -> uint64 -> bool;" ^ newline ^
    "  val notb : uint64 -> uint64;" ^ newline ^
    "  val andb : uint64 -> uint64 -> uint64;" ^ newline ^
    "  val orb : uint64 -> uint64 -> uint64;" ^ newline ^
    "  val xorb : uint64 -> uint64 -> uint64;" ^ newline ^
    "  val shiftl : uint64 -> IntInf.int -> uint64;" ^ newline ^
    "  val shiftr : uint64 -> IntInf.int -> uint64;" ^ newline ^
    "  val shiftr_signed : uint64 -> IntInf.int -> uint64;" ^ newline ^
    "  val set_bit : uint64 -> IntInf.int -> bool -> uint64;" ^ newline ^
    "  val test_bit : uint64 -> IntInf.int -> bool;" ^ newline ^
    "end = struct" ^ newline ^
    "" ^ newline ^
    "type uint64 = Word64.word;" ^ newline ^
    "" ^ newline ^
    "val zero = (0wx0 : uint64);" ^ newline ^
    "" ^ newline ^
    "val one = (0wx1 : uint64);" ^ newline ^
    "" ^ newline ^
    "fun fromInt x = Word64.fromLargeInt (IntInf.toLarge x);" ^ newline ^
    "" ^ newline ^
    "fun toInt x = IntInf.fromLarge (Word64.toLargeInt x);"  ^ newline ^
    "" ^ newline ^
    "fun fromLarge x = Word64.fromLarge x;" ^ newline ^
    "" ^ newline ^
    "fun toLarge x = Word64.toLarge x;"  ^ newline ^
    "" ^ newline ^
    "fun plus x y = Word64.+(x, y);" ^ newline ^
    "" ^ newline ^
    "fun minus x y = Word64.-(x, y);" ^ newline ^
    "" ^ newline ^
    "fun negate x = Word64.~(x);" ^ newline ^
    "" ^ newline ^
    "fun times x y = Word64.*(x, y);" ^ newline ^
    "" ^ newline ^
    "fun divide x y = Word64.div(x, y);" ^ newline ^
    "" ^ newline ^
    "fun modulus x y = Word64.mod(x, y);" ^ newline ^
    "" ^ newline ^
    "fun less_eq x y = Word64.<=(x, y);" ^ newline ^
    "" ^ newline ^
    "fun less x y = Word64.<(x, y);" ^ newline ^
    "" ^ newline ^
    "fun set_bit x n b =" ^ newline ^
    "  let val mask = Word64.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))" ^ newline ^
    "  in if b then Word64.orb (x, mask)" ^ newline ^
    "     else Word64.andb (x, Word64.notb mask)" ^ newline ^
    "  end" ^ newline ^
    "" ^ newline ^
    "fun shiftl x n =" ^ newline ^
    "  Word64.<< (x, Word.fromLargeInt (IntInf.toLarge n))" ^ newline ^
    "" ^ newline ^
    "fun shiftr x n =" ^ newline ^
    "  Word64.>> (x, Word.fromLargeInt (IntInf.toLarge n))" ^ newline ^
    "" ^ newline ^
    "fun shiftr_signed x n =" ^ newline ^
    "  Word64.~>> (x, Word.fromLargeInt (IntInf.toLarge n))" ^ newline ^
    "" ^ newline ^
    "fun test_bit x n =" ^ newline ^
    "  Word64.andb (x, Word64.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word64.fromInt 0" ^ newline ^
    "" ^ newline ^
    "val notb = Word64.notb" ^ newline ^
    "" ^ newline ^
    "fun andb x y = Word64.andb(x, y);" ^ newline ^
    "" ^ newline ^
    "fun orb x y = Word64.orb(x, y);" ^ newline ^
    "" ^ newline ^
    "fun xorb x y = Word64.xorb(x, y);" ^ newline ^
    "" ^ newline ^
    "end (*struct Uint64*)"
  val target_SML64 = "SML_word";
in
  (if use_Word64 then Code_Target.set_printings (Code_Symbol.Module ("Uint64", [(Code_Runtime.target, SOME (content, []))])) else I)
  #> Code_Target.set_printings (Code_Symbol.Module ("Uint64", [(target_SML64, SOME (content, []))]))
end
\<close>

code_printing code_module Uint64 \<rightharpoonup> (Haskell)
 \<open>module Uint64(Int64, Word64) where

  import Data.Int(Int64)
  import Data.Word(Word64)\<close>
code_reserved Haskell Uint64

text \<open>
  OCaml and Scala provide only signed 64bit numbers, so we use these and 
  implement sign-sensitive operations like comparisons manually.
\<close>
code_printing code_module "Uint64" \<rightharpoonup> (OCaml)
\<open>module Uint64 : sig
  val less : int64 -> int64 -> bool
  val less_eq : int64 -> int64 -> bool
  val set_bit : int64 -> Z.t -> bool -> int64
  val shiftl : int64 -> Z.t -> int64
  val shiftr : int64 -> Z.t -> int64
  val shiftr_signed : int64 -> Z.t -> int64
  val test_bit : int64 -> Z.t -> bool
end = struct

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if Int64.compare x Int64.zero < 0 then
    Int64.compare y Int64.zero < 0 && Int64.compare x y < 0
  else Int64.compare y Int64.zero < 0 || Int64.compare x y < 0;;

let less_eq x y =
  if Int64.compare x Int64.zero < 0 then
    Int64.compare y Int64.zero < 0 && Int64.compare x y <= 0
  else Int64.compare y Int64.zero < 0 || Int64.compare x y <= 0;;

let set_bit x n b =
  let mask = Int64.shift_left Int64.one (Z.to_int n)
  in if b then Int64.logor x mask
     else Int64.logand x (Int64.lognot mask);;

let shiftl x n = Int64.shift_left x (Z.to_int n);;

let shiftr x n = Int64.shift_right_logical x (Z.to_int n);;

let shiftr_signed x n = Int64.shift_right x (Z.to_int n);;

let test_bit x n =
  Int64.compare 
    (Int64.logand x (Int64.shift_left Int64.one (Z.to_int n)))
    Int64.zero
  <> 0;;

end;; (*struct Uint64*)\<close>
code_reserved OCaml Uint64

code_printing code_module Uint64 \<rightharpoonup> (Scala)
\<open>object Uint64 {

def less(x: Long, y: Long) : Boolean =
  if (x < 0) y < 0 && x < y
  else y < 0 || x < y

def less_eq(x: Long, y: Long) : Boolean =
  if (x < 0) y < 0 && x <= y
  else y < 0 || x <= y

def set_bit(x: Long, n: BigInt, b: Boolean) : Long =
  if (b)
    x | (1L << n.intValue)
  else
    x & (1L << n.intValue).unary_~

def shiftl(x: Long, n: BigInt) : Long = x << n.intValue

def shiftr(x: Long, n: BigInt) : Long = x >>> n.intValue

def shiftr_signed(x: Long, n: BigInt) : Long = x >> n.intValue

def test_bit(x: Long, n: BigInt) : Boolean =
  (x & (1L << n.intValue)) != 0

} /* object Uint64 */\<close>
code_reserved Scala Uint64

text \<open>
  OCaml's conversion from Big\_int to int64 demands that the value fits int a signed 64-bit integer.
  The following justifies the implementation.
\<close>

definition Uint64_signed :: "integer \<Rightarrow> uint64" 
where "Uint64_signed i = (if i < -(0x8000000000000000) \<or> i \<ge> 0x8000000000000000 then undefined Uint64 i else Uint64 i)"

lemma Uint64_code [code]:
  "Uint64 i = 
  (let i' = i AND 0xFFFFFFFFFFFFFFFF
   in if i' !! 63 then Uint64_signed (i' - 0x10000000000000000) else Uint64_signed i')"
including undefined_transfer integer.lifting unfolding Uint64_signed_def
by transfer(rule word_of_int_via_signed, simp_all add: bin_mask_numeral)

lemma Uint64_signed_code [code abstract]:
  "Rep_uint64 (Uint64_signed i) = 
  (if i < -(0x8000000000000000) \<or> i \<ge> 0x8000000000000000 then Rep_uint64 (undefined Uint64 i) else word_of_int (int_of_integer_symbolic i))"
unfolding Uint64_signed_def Uint64_def int_of_integer_symbolic_def word_of_integer_def
by(simp add: Abs_uint64_inverse)

text \<open>
  Avoid @{term Abs_uint64} in generated code, use @{term Rep_uint64'} instead. 
  The symbolic implementations for code\_simp use @{term Rep_uint64}.

  The new destructor @{term Rep_uint64'} is executable.
  As the simplifier is given the [code abstract] equations literally, 
  we cannot implement @{term Rep_uint64} directly, because that makes code\_simp loop.

  If code generation raises Match, some equation probably contains @{term Rep_uint64} 
  ([code abstract] equations for @{typ uint64} may use @{term Rep_uint64} because
  these instances will be folded away.)

  To convert @{typ "64 word"} values into @{typ uint64}, use @{term "Abs_uint64'"}.
\<close>

definition Rep_uint64' where [simp]: "Rep_uint64' = Rep_uint64"

lemma Rep_uint64'_transfer [transfer_rule]:
  "rel_fun cr_uint64 (=) (\<lambda>x. x) Rep_uint64'"
unfolding Rep_uint64'_def by(rule uint64.rep_transfer)

lemma Rep_uint64'_code [code]: "Rep_uint64' x = (BITS n. x !! n)"
by transfer simp

lift_definition Abs_uint64' :: "64 word \<Rightarrow> uint64" is "\<lambda>x :: 64 word. x" .

lemma Abs_uint64'_code [code]:
  "Abs_uint64' x = Uint64 (integer_of_int (uint x))"
including integer.lifting by transfer simp

declare [[code drop: "term_of_class.term_of :: uint64 \<Rightarrow> _"]]

lemma term_of_uint64_code [code]:
  defines "TR \<equiv> typerep.Typerep" and "bit0 \<equiv> STR ''Numeral_Type.bit0''" 
  shows
  "term_of_class.term_of x = 
   Code_Evaluation.App (Code_Evaluation.Const (STR ''Uint64.uint64.Abs_uint64'') (TR (STR ''fun'') [TR (STR ''Word.word'') [TR bit0 [TR bit0 [TR bit0 [TR bit0 [TR bit0 [TR bit0 [TR (STR ''Numeral_Type.num1'') []]]]]]]], TR (STR ''Uint64.uint64'') []]))
       (term_of_class.term_of (Rep_uint64' x))"
by(simp add: term_of_anything)

code_printing
  type_constructor uint64 \<rightharpoonup>
  (SML) "Uint64.uint64" and
  (Haskell) "Uint64.Word64" and
  (OCaml) "int64" and
  (Scala) "Long"
| constant Uint64 \<rightharpoonup>
  (SML) "Uint64.fromInt" and
  (Haskell) "(Prelude.fromInteger _ :: Uint64.Word64)" and
  (Haskell_Quickcheck) "(Prelude.fromInteger (Prelude.toInteger _) :: Uint64.Word64)" and
  (Scala) "_.longValue"
| constant Uint64_signed \<rightharpoonup>
  (OCaml) "Z.to'_int64"
| constant "0 :: uint64" \<rightharpoonup>
  (SML) "Uint64.zero" and
  (Haskell) "(0 :: Uint64.Word64)" and
  (OCaml) "Int64.zero" and
  (Scala) "0"
| constant "1 :: uint64" \<rightharpoonup>
  (SML) "Uint64.one" and
  (Haskell) "(1 :: Uint64.Word64)" and
  (OCaml) "Int64.one" and
  (Scala) "1"
| constant "plus :: uint64 \<Rightarrow> _ " \<rightharpoonup>
  (SML) "Uint64.plus" and
  (Haskell) infixl 6 "+" and
  (OCaml) "Int64.add" and
  (Scala) infixl 7 "+"
| constant "uminus :: uint64 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Uint64.negate" and
  (Haskell) "negate" and
  (OCaml) "Int64.neg" and
  (Scala) "!(- _)"
| constant "minus :: uint64 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Uint64.minus" and
  (Haskell) infixl 6 "-" and
  (OCaml) "Int64.sub" and
  (Scala) infixl 7 "-"
| constant "times :: uint64 \<Rightarrow> _ \<Rightarrow> _" \<rightharpoonup>
  (SML) "Uint64.times" and
  (Haskell) infixl 7 "*" and
  (OCaml) "Int64.mul" and
  (Scala) infixl 8 "*"
| constant "HOL.equal :: uint64 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "!((_ : Uint64.uint64) = _)" and
  (Haskell) infix 4 "==" and
  (OCaml) "(Int64.compare _ _ = 0)" and
  (Scala) infixl 5 "=="
| class_instance uint64 :: equal \<rightharpoonup>
  (Haskell) -
| constant "less_eq :: uint64 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Uint64.less'_eq" and
  (Haskell) infix 4 "<=" and
  (OCaml) "Uint64.less'_eq" and
  (Scala) "Uint64.less'_eq"
| constant "less :: uint64 \<Rightarrow> _ \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Uint64.less" and
  (Haskell) infix 4 "<" and
  (OCaml) "Uint64.less" and
  (Scala) "Uint64.less"
| constant "bitNOT :: uint64 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Uint64.notb" and
  (Haskell) "Data'_Bits.complement" and
  (OCaml) "Int64.lognot" and
  (Scala) "_.unary'_~"
| constant "bitAND :: uint64 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Uint64.andb" and
  (Haskell) infixl 7 "Data_Bits..&." and
  (OCaml) "Int64.logand" and
  (Scala) infixl 3 "&"
| constant "bitOR :: uint64 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Uint64.orb" and
  (Haskell) infixl 5 "Data_Bits..|." and
  (OCaml) "Int64.logor" and
  (Scala) infixl 1 "|"
| constant "bitXOR :: uint64 \<Rightarrow> _" \<rightharpoonup>
  (SML) "Uint64.xorb" and
  (Haskell) "Data'_Bits.xor" and
  (OCaml) "Int64.logxor" and
  (Scala) infixl 2 "^"

definition uint64_divmod :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64 \<times> uint64" where
  "uint64_divmod x y = 
  (if y = 0 then (undefined ((div) :: uint64 \<Rightarrow> _) x (0 :: uint64), undefined ((mod) :: uint64 \<Rightarrow> _) x (0 :: uint64)) 
  else (x div y, x mod y))"

definition uint64_div :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" 
where "uint64_div x y = fst (uint64_divmod x y)"

definition uint64_mod :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64" 
where "uint64_mod x y = snd (uint64_divmod x y)"

lemma div_uint64_code [code]: "x div y = (if y = 0 then 0 else uint64_div x y)"
including undefined_transfer unfolding uint64_divmod_def uint64_div_def
by transfer (simp add: word_div_def)

lemma mod_uint64_code [code]: "x mod y = (if y = 0 then x else uint64_mod x y)"
including undefined_transfer unfolding uint64_mod_def uint64_divmod_def
by transfer (simp add: word_mod_def)

definition uint64_sdiv :: "uint64 \<Rightarrow> uint64 \<Rightarrow> uint64"
where [code del]:
  "uint64_sdiv x y =
   (if y = 0 then undefined ((div) :: uint64 \<Rightarrow> _) x (0 :: uint64)
    else Abs_uint64 (Rep_uint64 x sdiv Rep_uint64 y))"

definition div0_uint64 :: "uint64 \<Rightarrow> uint64"
where [code del]: "div0_uint64 x = undefined ((div) :: uint64 \<Rightarrow> _) x (0 :: uint64)"
declare [[code abort: div0_uint64]]

definition mod0_uint64 :: "uint64 \<Rightarrow> uint64"
where [code del]: "mod0_uint64 x = undefined ((mod) :: uint64 \<Rightarrow> _) x (0 :: uint64)"
declare [[code abort: mod0_uint64]]

lemma uint64_divmod_code [code]:
  "uint64_divmod x y =
  (if 0x8000000000000000 \<le> y then if x < y then (0, x) else (1, x - y)
   else if y = 0 then (div0_uint64 x, mod0_uint64 x)
   else let q = (uint64_sdiv (x >> 1) y) << 1;
            r = x - q * y
        in if r \<ge> y then (q + 1, r - y) else (q, r))"
including undefined_transfer unfolding uint64_divmod_def uint64_sdiv_def div0_uint64_def mod0_uint64_def
by transfer(simp add: divmod_via_sdivmod)

lemma uint64_sdiv_code [code abstract]:
  "Rep_uint64 (uint64_sdiv x y) =
   (if y = 0 then Rep_uint64 (undefined ((div) :: uint64 \<Rightarrow> _) x (0 :: uint64))
    else Rep_uint64 x sdiv Rep_uint64 y)"
unfolding uint64_sdiv_def by(simp add: Abs_uint64_inverse)

text \<open>
  Note that we only need a translation for signed division, but not for the remainder
  because @{thm uint64_divmod_code} computes both with division only.
\<close>

code_printing
  constant uint64_div \<rightharpoonup>
  (SML) "Uint64.divide" and
  (Haskell) "Prelude.div"
| constant uint64_mod \<rightharpoonup>
  (SML) "Uint64.modulus" and
  (Haskell) "Prelude.mod"
| constant uint64_divmod \<rightharpoonup>
  (Haskell) "divmod"
| constant uint64_sdiv \<rightharpoonup>
  (OCaml) "Int64.div" and
  (Scala) "_ '/ _"

definition uint64_test_bit :: "uint64 \<Rightarrow> integer \<Rightarrow> bool"
where [code del]:
  "uint64_test_bit x n =
  (if n < 0 \<or> 63 < n then undefined (test_bit :: uint64 \<Rightarrow> _) x n
   else x !! (nat_of_integer n))"

lemma test_bit_uint64_code [code]:
  "test_bit x n \<longleftrightarrow> n < 64 \<and> uint64_test_bit x (integer_of_nat n)"
including undefined_transfer integer.lifting unfolding uint64_test_bit_def
by transfer(auto cong: conj_cong dest: test_bit_size simp add: word_size)

lemma uint64_test_bit_code [code]:
  "uint64_test_bit w n =
  (if n < 0 \<or> 63 < n then undefined (test_bit :: uint64 \<Rightarrow> _) w n else Rep_uint64 w !! nat_of_integer n)"
unfolding uint64_test_bit_def
by(simp add: test_bit_uint64.rep_eq)

code_printing constant uint64_test_bit \<rightharpoonup>
  (SML) "Uint64.test'_bit" and
  (Haskell) "Data'_Bits.testBitBounded" and
  (OCaml) "Uint64.test'_bit" and
  (Scala) "Uint64.test'_bit" and
  (Eval) "(fn x => fn i => if i < 0 orelse i >= 64 then raise (Fail \"argument to uint64'_test'_bit out of bounds\") else Uint64.test'_bit x i)"

definition uint64_set_bit :: "uint64 \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> uint64"
where [code del]:
  "uint64_set_bit x n b =
  (if n < 0 \<or> 63 < n then undefined (set_bit :: uint64 \<Rightarrow> _) x n b
   else set_bit x (nat_of_integer n) b)"

lemma set_bit_uint64_code [code]:
  "set_bit x n b = (if n < 64 then uint64_set_bit x (integer_of_nat n) b else x)"
including undefined_transfer integer.lifting unfolding uint64_set_bit_def
by(transfer)(auto cong: conj_cong simp add: not_less set_bit_beyond word_size)

lemma uint64_set_bit_code [code abstract]:
  "Rep_uint64 (uint64_set_bit w n b) = 
  (if n < 0 \<or> 63 < n then Rep_uint64 (undefined (set_bit :: uint64 \<Rightarrow> _) w n b)
   else set_bit (Rep_uint64 w) (nat_of_integer n) b)"
including undefined_transfer unfolding uint64_set_bit_def by transfer simp

code_printing constant uint64_set_bit \<rightharpoonup>
  (SML) "Uint64.set'_bit" and
  (Haskell) "Data'_Bits.setBitBounded" and
  (OCaml) "Uint64.set'_bit" and
  (Scala) "Uint64.set'_bit" and
  (Eval) "(fn x => fn i => fn b => if i < 0 orelse i >= 64 then raise (Fail \"argument to uint64'_set'_bit out of bounds\") else Uint64.set'_bit x i b)"

lift_definition uint64_set_bits :: "(nat \<Rightarrow> bool) \<Rightarrow> uint64 \<Rightarrow> nat \<Rightarrow> uint64" is set_bits_aux .

lemma uint64_set_bits_code [code]:
  "uint64_set_bits f w n =
  (if n = 0 then w 
   else let n' = n - 1 in uint64_set_bits f ((w << 1) OR (if f n' then 1 else 0)) n')"
by(transfer fixing: n)(cases n, simp_all)

lemma set_bits_uint64 [code]:
  "(BITS n. f n) = uint64_set_bits f 0 64"
by transfer(simp add: set_bits_conv_set_bits_aux)


lemma lsb_code [code]: fixes x :: uint64 shows "lsb x = x !! 0"
by transfer(simp add: word_lsb_def word_test_bit_def)


definition uint64_shiftl :: "uint64 \<Rightarrow> integer \<Rightarrow> uint64"
where [code del]:
  "uint64_shiftl x n = (if n < 0 \<or> 64 \<le> n then undefined (shiftl :: uint64 \<Rightarrow> _) x n else x << (nat_of_integer n))"

lemma shiftl_uint64_code [code]: "x << n = (if n < 64 then uint64_shiftl x (integer_of_nat n) else 0)"
including undefined_transfer integer.lifting unfolding uint64_shiftl_def
by transfer(simp add: not_less shiftl_zero_size word_size)

lemma uint64_shiftl_code [code abstract]:
  "Rep_uint64 (uint64_shiftl w n) =
  (if n < 0 \<or> 64 \<le> n then Rep_uint64 (undefined (shiftl :: uint64 \<Rightarrow> _) w n) else Rep_uint64 w << (nat_of_integer n))"
including undefined_transfer unfolding uint64_shiftl_def by transfer simp

code_printing constant uint64_shiftl \<rightharpoonup>
  (SML) "Uint64.shiftl" and
  (Haskell) "Data'_Bits.shiftlBounded" and
  (OCaml) "Uint64.shiftl" and
  (Scala) "Uint64.shiftl" and
  (Eval) "(fn x => fn i => if i < 0 orelse i >= 64 then raise (Fail \"argument to uint64'_shiftl out of bounds\") else Uint64.shiftl x i)"


definition uint64_shiftr :: "uint64 \<Rightarrow> integer \<Rightarrow> uint64"
where [code del]:
  "uint64_shiftr x n = (if n < 0 \<or> 64 \<le> n then undefined (shiftr :: uint64 \<Rightarrow> _) x n else x >> (nat_of_integer n))"

lemma shiftr_uint64_code [code]: "x >> n = (if n < 64 then uint64_shiftr x (integer_of_nat n) else 0)"
including undefined_transfer integer.lifting unfolding uint64_shiftr_def
by transfer(simp add: not_less shiftr_zero_size word_size)

lemma uint64_shiftr_code [code abstract]:
  "Rep_uint64 (uint64_shiftr w n) =
  (if n < 0 \<or> 64 \<le> n then Rep_uint64 (undefined (shiftr :: uint64 \<Rightarrow> _) w n) else Rep_uint64 w >> nat_of_integer n)"
including undefined_transfer unfolding uint64_shiftr_def by transfer simp

code_printing constant uint64_shiftr \<rightharpoonup>
  (SML) "Uint64.shiftr" and
  (Haskell) "Data'_Bits.shiftrBounded" and
  (OCaml) "Uint64.shiftr" and
  (Scala) "Uint64.shiftr" and
  (Eval) "(fn x => fn i => if i < 0 orelse i >= 64 then raise (Fail \"argument to uint64'_shiftr out of bounds\") else Uint64.shiftr x i)"


definition uint64_sshiftr :: "uint64 \<Rightarrow> integer \<Rightarrow> uint64"
where [code del]:
  "uint64_sshiftr x n =
  (if n < 0 \<or> 64 \<le> n then undefined sshiftr_uint64 x n else sshiftr_uint64 x (nat_of_integer n))"

lemma sshiftr_beyond: fixes x :: "'a :: len word" shows
  "size x \<le> n \<Longrightarrow> x >>> n = (if x !! (size x - 1) then -1 else 0)"
by(rule word_eqI)(simp add: nth_sshiftr word_size)

lemma sshiftr_uint64_code [code]:
  "x >>> n = 
  (if n < 64 then uint64_sshiftr x (integer_of_nat n) else if x !! 63 then -1 else 0)"
including undefined_transfer integer.lifting unfolding uint64_sshiftr_def
by transfer(simp add: not_less sshiftr_beyond word_size)

lemma uint64_sshiftr_code [code abstract]:
  "Rep_uint64 (uint64_sshiftr w n) =
  (if n < 0 \<or> 64 \<le> n then Rep_uint64 (undefined sshiftr_uint64 w n) else Rep_uint64 w >>> (nat_of_integer n))"
including undefined_transfer unfolding uint64_sshiftr_def by transfer simp

code_printing constant uint64_sshiftr \<rightharpoonup>
  (SML) "Uint64.shiftr'_signed" and
  (Haskell) 
    "(Prelude.fromInteger (Prelude.toInteger (Data'_Bits.shiftrBounded (Prelude.fromInteger (Prelude.toInteger _) :: Uint64.Int64) _)) :: Uint64.Word64)" and
  (OCaml) "Uint64.shiftr'_signed" and
  (Scala) "Uint64.shiftr'_signed" and
  (Eval) "(fn x => fn i => if i < 0 orelse i >= 64 then raise (Fail \"argument to uint64'_shiftr'_signed out of bounds\") else Uint64.shiftr'_signed x i)"


lemma uint64_msb_test_bit: "msb x \<longleftrightarrow> (x :: uint64) !! 63"
by transfer(simp add: msb_nth)

lemma msb_uint64_code [code]: "msb x \<longleftrightarrow> uint64_test_bit x 63"
by(simp add: uint64_test_bit_def uint64_msb_test_bit)

lemma uint64_of_int_code [code]: "uint64_of_int i = Uint64 (integer_of_int i)"
including integer.lifting by transfer simp

lemma int_of_uint64_code [code]:
  "int_of_uint64 x = int_of_integer (integer_of_uint64 x)"
by(simp add: integer_of_uint64_def)

lemma nat_of_uint64_code [code]:
  "nat_of_uint64 x = nat_of_integer (integer_of_uint64 x)"
unfolding integer_of_uint64_def including integer.lifting by transfer (simp add: unat_def)

definition integer_of_uint64_signed :: "uint64 \<Rightarrow> integer"
where
  "integer_of_uint64_signed n = (if n !! 63 then undefined integer_of_uint64 n else integer_of_uint64 n)"

lemma integer_of_uint64_signed_code [code]:
  "integer_of_uint64_signed n =
  (if n !! 63 then undefined integer_of_uint64 n else integer_of_int (uint (Rep_uint64' n)))"
unfolding integer_of_uint64_signed_def integer_of_uint64_def
including undefined_transfer by transfer simp

lemma integer_of_uint64_code [code]:
  "integer_of_uint64 n =
  (if n !! 63 then integer_of_uint64_signed (n AND 0x7FFFFFFFFFFFFFFF) OR 0x8000000000000000 else integer_of_uint64_signed n)"
unfolding integer_of_uint64_def integer_of_uint64_signed_def o_def
including undefined_transfer integer.lifting
by transfer(auto simp add: word_ao_nth uint_and_mask_or_full mask_numeral mask_Suc_0 intro!: uint_and_mask_or_full[symmetric])

code_printing
  constant "integer_of_uint64" \<rightharpoonup>
  (SML) "Uint64.toInt" and
  (Haskell) "Prelude.toInteger"
| constant "integer_of_uint64_signed" \<rightharpoonup>
  (OCaml) "Z.of'_int64" and
  (Scala) "BigInt"

section \<open>Quickcheck setup\<close>

definition uint64_of_natural :: "natural \<Rightarrow> uint64"
where "uint64_of_natural x \<equiv> Uint64 (integer_of_natural x)"

instantiation uint64 :: "{random, exhaustive, full_exhaustive}" begin
definition "random_uint64 \<equiv> qc_random_cnv uint64_of_natural"
definition "exhaustive_uint64 \<equiv> qc_exhaustive_cnv uint64_of_natural"
definition "full_exhaustive_uint64 \<equiv> qc_full_exhaustive_cnv uint64_of_natural"
instance ..
end

instantiation uint64 :: narrowing begin

interpretation quickcheck_narrowing_samples
  "\<lambda>i. let x = Uint64 i in (x, 0xFFFFFFFFFFFFFFFF - x)" "0"
  "Typerep.Typerep (STR ''Uint64.uint64'') []" .

definition "narrowing_uint64 d = qc_narrowing_drawn_from (narrowing_samples d) d"
declare [[code drop: "partial_term_of :: uint64 itself \<Rightarrow> _"]]
lemmas partial_term_of_uint64 [code] = partial_term_of_code

instance ..
end

no_notation sshiftr_uint64 (infixl ">>>" 55)

end
