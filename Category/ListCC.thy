(* This file instantiates the type constructor list as a member of monad-zero-plus.  *)
theory ListCC
imports Category
begin

ML{* structure List_M0P_Min : MONAD_0PLUS_MIN =
struct
  type 'a monad     = 'a list;
  fun return x      = [x];
  fun bind seq func = flat (map func seq);
  val mzero         = [];
  fun mplus (f, s)  = f @ s;
end;

structure ListCC = mk_Monad_0Plus (List_M0P_Min);
*}

end