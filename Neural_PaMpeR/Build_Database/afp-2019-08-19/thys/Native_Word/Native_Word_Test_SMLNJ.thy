(*  Title:      Native_Word_Test_SMLNJ.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_SMLNJ imports
  Native_Word_Test
begin

section \<open>Test with SML/NJ\<close>

test_code
  test_uint64 "test_uint64' = 0x12"
  test_uint32 "test_uint32' = 0x12"
  test_uint8 "test_uint8' = 0x12"
  test_uint
  test_casts
  test_casts''
  test_casts_uint
  test_casts_uint''
in SMLNJ

text \<open>SMLNJ provides a \texttt{Word64} structure. To test it in the
  SML\_word target, we have to associate a driver with the combination.
  As SMLNj does not implement a Word16 structure, we remove the code module
  that refers to it. After this, @{typ uint16} no longer works in the target
  \texttt{SML\_word} as intended!
\<close>

setup \<open>Code_Test.add_driver ("SMLNJ_word", (Code_Test.evaluate_in_smlnj, "SML_word"))\<close>
code_printing code_module Uint16 \<rightharpoonup> (SML_word) \<open>\<close>

test_code
  test_uint64 "test_uint64' = 0x12"
  test_uint32 "test_uint32' = 0x12"
  test_uint8 "test_uint8' = 0x12"
  test_uint
  \<comment> \<open>The cast operations for @{typ uint64} use \texttt{Word64.fromLarge} and
      \texttt{Word64.toLarge}, which are unimplemented in SMLNJ's \texttt{Word64} structure.\<close>
  (* test_casts test_casts'' 
  test_casts_uint *)
  test_casts_uint''
in SMLNJ_word

end
