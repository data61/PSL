(*  Title:      Native_Word_Test_PolYML64.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_PolyML64 imports
  Native_Word_Test
begin

test_code "test_uint64' = 0x12"
in PolyML

ML \<open>
  if ML_System.platform_is_64 then
    ML \<open>\<^assert> (\<^code>\<open>test_uint64'\<close> = 0wx12)\<close>
  else ()
\<close>

end
