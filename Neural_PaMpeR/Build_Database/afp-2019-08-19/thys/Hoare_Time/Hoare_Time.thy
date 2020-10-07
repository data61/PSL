theory Hoare_Time imports

  (* Interesting theories.
     In Isabelle/jEdit ctrl+click on them to browse them,
     Use green arrow at top bar to navigate back *)

  (* Nielson System *)
  Nielson_Hoare         (* formalizes the Hoare logic *)
  Nielson_VCG           (* the VCG for Nielson system *)
  Nielson_VCGi          (* the improved VCG for Nielson system *)
  Nielson_VCGi_complete (* completeness of improved VCG*)
  Nielson_Examples      (* some small examples *)
  Nielson_Sqrt          (* Example proving logarithmic time bound for 
                            an Algorithm for Discrete Square Root by Binary Search *)

  (* simple quantitative Hoare logic *)
  Quant_Hoare           (* formalizes the simple quantitative Hoare logic *)
  Quant_VCG             (* the VCG for that system *)
  Quant_Examples        (* some examples *)

  (* "bigO-style" quantitative Hoare logic *)
  QuantK_Hoare          (* formalizes the "big-O style" quantitative Hoare logic *) 
  QuantK_VCG            (* the VCG for that system *)
  QuantK_Examples       (* some examples *)
  QuantK_Sqrt

  (* Separation Logic with Time Credits *)
  SepLog_Hoare          (* formalizes the Hoare logic based on Separation Logic and
                            Time Credits *)
  SepLog_Examples        (* some examples *)
  SepLogK_Hoare         (* big-O style Hoare logic using Separation Logic ... *)
  SepLogK_VCG           (* ... and its VCGen *)

  (* Discussion *)
  Discussion           (* Discussion and Reduction Proofs for exact style *)
  DiscussionO            (* Discussion and Reduction Proofs for big-O style *)

begin end