(* This file instantiates the type constructor Seq.seq as a member of monad-zero-plus.  *)
theory Seq
imports Category
begin

ML{* structure Seq_M0P_Min : MONAD_0PLUS_MIN =
struct
  type 'a monad     = 'a Seq.seq;
  val return        = Seq.single;
  fun bind seq func = Seq.flat (Seq.map func seq);
  val mzero         = Seq.empty;
  fun mplus (f, s)  = Seq.append f s;
end;
*}

ML{* structure Seq_M0P = mk_Monad_0Plus (Seq_M0P_Min); *}

end