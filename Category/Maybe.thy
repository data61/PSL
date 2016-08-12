(* This file instantiates the type constructor option as a member of monad-zero-plus.  *)
theory Maybe (* The theory name "Option" is already taken.*)
imports Category
begin

ML{* structure Option_M0P_Min : MONAD_0PLUS_MIN =
struct
  type 'a monad       = 'a Option.option;
  val return          = Option.SOME;
  fun bind  NONE      _    = NONE
   |  bind (SOME sth) func = func sth;
  val mzero           = Option.NONE;
  fun mplus (NONE, r) = r
   |  mplus (left, _) = left;
end;
*}

ML{* structure Option_M0P = mk_Monad_0Plus (Option_M0P_Min); *}

end