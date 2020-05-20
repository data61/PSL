(*  Title:      Native_Cast.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Conversions between unsigned words and between char\<close>

theory Native_Cast
  imports
  Uint8
  Uint16
  Uint32
  Uint64
begin

text \<open>Auxiliary stuff\<close>

lemma integer_of_char_char_of_integer [simp]:
  "integer_of_char (char_of_integer x) = x mod 256"
  by (simp add: integer_of_char_def char_of_integer_def)

lemma char_of_integer_integer_of_char [simp]:
  "char_of_integer (integer_of_char x) = x"
  by (simp add: integer_of_char_def char_of_integer_def)

lemma int_lt_numeral [simp]: "int x < numeral n \<longleftrightarrow> x < numeral n"
by (metis nat_numeral zless_nat_eq_int_zless)

lemma int_of_integer_ge_0: "0 \<le> int_of_integer x \<longleftrightarrow> 0 \<le> x"
including integer.lifting by transfer simp

lemma integer_of_char_ge_0 [simp]: "0 \<le> integer_of_char x"
  including integer.lifting unfolding integer_of_char_def
  by transfer (simp add: of_char_def)


section \<open>Conversion between native words\<close>

lift_definition uint8_of_uint16 :: "uint16 \<Rightarrow> uint8" is ucast .
lift_definition uint8_of_uint32 :: "uint32 \<Rightarrow> uint8" is ucast .
lift_definition uint8_of_uint64 :: "uint64 \<Rightarrow> uint8" is ucast .

lift_definition uint16_of_uint8 :: "uint8 \<Rightarrow> uint16" is ucast .
lift_definition uint16_of_uint32 :: "uint32 \<Rightarrow> uint16" is ucast .
lift_definition uint16_of_uint64 :: "uint64 \<Rightarrow> uint16" is ucast .

lift_definition uint32_of_uint8 :: "uint8 \<Rightarrow> uint32" is ucast .
lift_definition uint32_of_uint16 :: "uint16 \<Rightarrow> uint32" is ucast .
lift_definition uint32_of_uint64 :: "uint64 \<Rightarrow> uint32" is ucast .

lift_definition uint64_of_uint8 :: "uint8 \<Rightarrow> uint64" is ucast .
lift_definition uint64_of_uint16 :: "uint16 \<Rightarrow> uint64" is ucast .
lift_definition uint64_of_uint32 :: "uint32 \<Rightarrow> uint64" is ucast .

definition mask where "mask = (0xFFFFFFFF :: integer)"

code_printing
  constant uint8_of_uint16 \<rightharpoonup>
  (SML_word) "Word8.fromLarge (Word16.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint8.Word8)" and
  (Scala) "_.toByte"
| constant uint8_of_uint32 \<rightharpoonup>
  (SML) "Word8.fromLarge (Word32.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint8.Word8)" and
  (Scala) "_.toByte"
| constant uint8_of_uint64 \<rightharpoonup>
  (SML) "Word8.fromLarge (Uint64.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint8.Word8)" and
  (Scala) "_.toByte"
| constant uint16_of_uint8 \<rightharpoonup>
  (SML_word) "Word16.fromLarge (Word8.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint16.Word16)" and
  (Scala) "((_).toInt & 0xFF).toChar"
| constant uint16_of_uint32 \<rightharpoonup>
  (SML_word) "Word16.fromLarge (Word32.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint16.Word16)" and
  (Scala) "_.toChar"
| constant uint16_of_uint64 \<rightharpoonup>
  (SML_word) "Word16.fromLarge (Uint64.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint16.Word16)" and
  (Scala) "_.toChar"
| constant uint32_of_uint8 \<rightharpoonup>
  (SML) "Word32.fromLarge (Word8.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint32.Word32)" and
  (Scala) "((_).toInt & 0xFF)"
| constant uint32_of_uint16 \<rightharpoonup>
  (SML_word) "Word32.fromLarge (Word16.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint32.Word32)" and
  (Scala) "(_).toInt"
| constant uint32_of_uint64 \<rightharpoonup>
  (SML_word) "Word32.fromLarge (Uint64.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint32.Word32)" and
  (Scala) "(_).toInt" and
  (OCaml) "Int64.to'_int32"
| constant uint64_of_uint8 \<rightharpoonup>
  (SML_word) "Word64.fromLarge (Word8.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint64.Word64)" and
  (Scala) "((_).toLong & 0xFF)"
| constant uint64_of_uint16 \<rightharpoonup>
  (SML_word) "Word64.fromLarge (Word16.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint64.Word64)" and
  (Scala) "_.toLong"
| constant uint64_of_uint32 \<rightharpoonup>
  (SML_word) "Word64.fromLarge (Word32.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint64.Word64)" and
  (Scala) "((_).toLong & 0xFFFFFFFFL)" and
  (OCaml) "Int64.logand (Int64.of'_int32 _) (Int64.of'_string \"4294967295\")"

text \<open>
  Use @{const Abs_uint8'} etc. instead of @{const Rep_uint8} in code equations
  for conversion functions to avoid exceptions during code generation when the
  target language provides only some of the uint types.
\<close>

lemma uint8_of_uint16_code [code]:
  "uint8_of_uint16 x = Abs_uint8' (ucast (Rep_uint16' x))"
by transfer simp

lemma uint8_of_uint32_code [code]:
  "uint8_of_uint32 x = Abs_uint8' (ucast (Rep_uint32' x))"
by transfer simp

lemma uint8_of_uint64_code [code]:
  "uint8_of_uint64 x = Abs_uint8' (ucast (Rep_uint64' x))"
by transfer simp

lemma uint16_of_uint8_code [code]:
  "uint16_of_uint8 x = Abs_uint16' (ucast (Rep_uint8' x))"
by transfer simp

lemma uint16_of_uint32_code [code]:
  "uint16_of_uint32 x = Abs_uint16' (ucast (Rep_uint32' x))"
by transfer simp

lemma uint16_of_uint64_code [code]:
  "uint16_of_uint64 x = Abs_uint16' (ucast (Rep_uint64' x))"
by transfer simp

lemma uint32_of_uint8_code [code]:
  "uint32_of_uint8 x = Abs_uint32' (ucast (Rep_uint8' x))"
by transfer simp

lemma uint32_of_uint16_code [code]:
  "uint32_of_uint16 x = Abs_uint32' (ucast (Rep_uint16' x))"
by transfer simp

lemma uint32_of_uint64_code [code]:
  "uint32_of_uint64 x = Abs_uint32' (ucast (Rep_uint64' x))"
by transfer simp

lemma uint64_of_uint8_code [code]:
  "uint64_of_uint8 x = Abs_uint64' (ucast (Rep_uint8' x))"
by transfer simp

lemma uint64_of_uint16_code [code]:
  "uint64_of_uint16 x = Abs_uint64' (ucast (Rep_uint16' x))"
by transfer simp

lemma uint64_of_uint32_code [code]:
  "uint64_of_uint32 x = Abs_uint64' (ucast (Rep_uint32' x))"
by transfer simp

end
