(*  Title:      Native_Word_Test_PolyML.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_PolyML imports
  Native_Word_Test
begin

section \<open>Test with PolyML\<close>

test_code
  test_uint64 "test_uint64' = 0x12"
  test_uint32 "test_uint32' = 0x12"
  test_uint8 "test_uint8' = 0x12"
  test_uint
  test_casts test_casts''
  test_casts_uint test_casts_uint''
in PolyML

end
