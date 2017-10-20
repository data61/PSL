(*  Title:      Native_Word_Test_PolYML64.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Native_Word_Test_PolyML64 imports
  Native_Word_Test
begin

test_code "test_uint64' = 0x12"
in PolyML

(* Does not work for PolyML 5.6 
ML {* val 0wx12 = @{code test_uint64'} *} *)

end
