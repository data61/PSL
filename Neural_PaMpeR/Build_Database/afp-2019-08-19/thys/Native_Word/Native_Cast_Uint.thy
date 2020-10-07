(*  Title:      Native_Cast_Uint.thy
    Author:     Andreas Lochbihler, Digital Asset
*)

theory Native_Cast_Uint imports
  Native_Cast
  Uint
begin

lift_definition uint_of_uint8 :: "uint8 \<Rightarrow> uint" is ucast .
lift_definition uint_of_uint16 :: "uint16 \<Rightarrow> uint" is ucast .
lift_definition uint_of_uint32 :: "uint32 \<Rightarrow> uint" is ucast .
lift_definition uint_of_uint64 :: "uint64 \<Rightarrow> uint" is ucast .

lift_definition uint8_of_uint :: "uint \<Rightarrow> uint8" is ucast .
lift_definition uint16_of_uint :: "uint \<Rightarrow> uint16" is ucast .
lift_definition uint32_of_uint :: "uint \<Rightarrow> uint32" is ucast .
lift_definition uint64_of_uint :: "uint \<Rightarrow> uint64" is ucast .

code_printing
  constant uint_of_uint8 \<rightharpoonup>
  (SML) "Word.fromLarge (Word8.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint.Word)" and
  (Scala) "((_).toInt & 0xFF)"
| constant uint_of_uint16 \<rightharpoonup>
  (SML_word) "Word.fromLarge (Word16.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint.Word)" and
  (Scala) "(_).toInt"
| constant uint_of_uint32 \<rightharpoonup>
  (SML) "Word.fromLarge (Word32.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint.Word)" and
  (Scala) "_" and
  (OCaml) "(Int32.to'_int _) land Uint.int'_mask"
| constant uint_of_uint64 \<rightharpoonup>
  (SML) "Word.fromLarge (Uint64.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint.Word)" and
  (Scala) "(_).toInt" and
  (OCaml) "Int64.to'_int"
| constant uint8_of_uint \<rightharpoonup>
  (SML) "Word8.fromLarge (Word.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint8.Word8)" and
  (Scala) "(_).toByte"
| constant uint16_of_uint \<rightharpoonup>
  (SML_word) "Word16.fromLarge (Word.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint16.Word16)" and
  (Scala) "(_).toChar"
| constant uint32_of_uint \<rightharpoonup>
  (SML) "Word32.fromLarge (Word.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint32.Word32)" and
  (Scala) "_" and
  (OCaml) "Int32.logand (Int32.of'_int _) Uint.int32'_mask"
| constant uint64_of_uint \<rightharpoonup>
  (SML) "Uint64.fromLarge (Word.toLarge _)" and
  (Haskell) "(Prelude.fromIntegral _ :: Uint64.Word64)" and
  (Scala) "((_).toLong & 0xFFFFFFFFL)" and
  (OCaml) "Int64.logand (Int64.of'_int _) Uint.int64'_mask"

lemma uint8_of_uint_code [code]:
  "uint8_of_uint x = Abs_uint8' (ucast (Rep_uint' x))"
  unfolding Rep_uint'_def by transfer simp

lemma uint16_of_uint_code [code]:
  "uint16_of_uint x = Abs_uint16' (ucast (Rep_uint' x))"
  unfolding Rep_uint'_def by transfer simp

lemma uint32_of_uint_code [code]:
  "uint32_of_uint x = Abs_uint32' (ucast (Rep_uint' x))"
  unfolding Rep_uint'_def by transfer simp

lemma uint64_of_uint_code [code]:
  "uint64_of_uint x = Abs_uint64' (ucast (Rep_uint' x))"
  unfolding Rep_uint'_def by transfer simp

lemma uint_of_uint8_code [code]:
  "uint_of_uint8 x = Abs_uint' (ucast (Rep_uint8' x))"
  by transfer simp

lemma uint_of_uint16_code [code]:
  "uint_of_uint16 x = Abs_uint' (ucast (Rep_uint16' x))"
  by transfer simp

lemma uint_of_uint32_code [code]:
  "uint_of_uint32 x = Abs_uint' (ucast (Rep_uint32' x))"
  by transfer simp

lemma uint_of_uint64_code [code]:
  "uint_of_uint64 x = Abs_uint' (ucast (Rep_uint64' x))"
  by transfer simp

end