(*  Title:      Native_Word_Test_MLton2.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_OCaml imports
  Native_Word_Test
begin

section \<open>Test with OCaml\<close>

test_code
  test_uint64 "test_uint64' = 0x12"
  test_uint32 "test_uint32' = 0x12"
  test_uint
  test_casts''
  test_casts_uint
in OCaml

end
