(*  Title:      Native_Word_Test_Emu.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_Emu imports
  Native_Word_Test
  Code_Target_Bits_Int
begin

section \<open>Test cases for emulation of native words\<close>

subsection \<open>Tests for @{typ uint16}\<close>

text \<open>
  Test that @{typ uint16} is emulated for PolyML and OCaml via @{typ "16 word"} 
  if @{theory Native_Word.Code_Target_Bits_Int} is imported.
\<close>

definition test_uint16_emulation :: bool where
  "test_uint16_emulation \<longleftrightarrow> (0xFFFFF - 0x1000 = (0xEFFF :: uint16))"

export_code test_uint16_emulation checking SML OCaml?
  \<comment> \<open>test the other target languages as well\<close> Haskell? Scala

notepad begin
have test_uint16 by eval
have test_uint16_emulation by eval
have test_uint16_emulation by normalization
have test_uint16_emulation by code_simp
end

ML_val \<open>
  val true = @{code test_uint16};
  val true = @{code test_uint16_emulation};
\<close>

lemma "x AND y = x OR (y :: uint16)"
quickcheck[random, expect=counterexample]
quickcheck[exhaustive, expect=counterexample]
oops

subsection \<open>Tests for @{typ uint8}\<close>

text \<open>
  Test that @{typ uint8} is emulated for OCaml via @{typ "8 word"} 
  if @{theory Native_Word.Code_Target_Bits_Int} is imported.
\<close>

definition test_uint8_emulation :: bool where
  "test_uint8_emulation \<longleftrightarrow> (0xFFF - 0x10 = (0xEF :: uint8))"

export_code test_uint8_emulation checking OCaml?
  \<comment> \<open>test the other target languages as well\<close> SML Haskell? Scala

end
