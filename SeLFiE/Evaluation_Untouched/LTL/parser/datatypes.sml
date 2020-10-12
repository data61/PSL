structure Ltl_Dt : 
  sig 
    datatype 'a ltlc = True_ltlc 
      | False_ltlc 
      | Prop_ltlc of 'a 
      | Not_ltlc of 'a ltlc
      | And_ltlc of 'a ltlc * 'a ltlc 
      | Or_ltlc of 'a ltlc * 'a ltlc 
      | Implies_ltlc of 'a ltlc * 'a ltlc 
      | Next_ltlc of 'a ltlc 
      | Final_ltlc of 'a ltlc 
      | Global_ltlc of 'a ltlc 
      | Until_ltlc of 'a ltlc * 'a ltlc 
      | Release_ltlc of 'a ltlc * 'a ltlc
      | WeakUntil_ltlc of 'a ltlc * 'a ltlc
      | StrongRelease_ltlc of 'a ltlc * 'a ltlc
    val iff_ltlc : 'a ltlc -> 'a ltlc -> 'a ltlc
   end = 
struct
  open LTL;
end;
