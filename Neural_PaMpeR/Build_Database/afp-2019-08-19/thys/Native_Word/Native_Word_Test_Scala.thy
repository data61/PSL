(*  Title:      Native_Word_Test_Scala.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_Scala imports
  Native_Word_Test
begin

section \<open>Test with Scala\<close>

text \<open>
  In Scala, @{typ uint} and @{typ uint32} are both implemented as type \texttt{Int}.
  When they are used in the same generated program, we have to suppress the type class
  instances for one of them.
\<close>
code_printing class_instance uint32 :: equal \<rightharpoonup> (Scala) -

test_code
  test_uint64 "test_uint64' = 0x12"
  test_uint32 "test_uint32' = 0x12"
  test_uint16
  test_uint8 "test_uint8' = 0x12" 
  test_uint
  test_casts test_casts' test_casts''
  test_casts_uint test_casts_uint' test_casts_uint''
in Scala

end
