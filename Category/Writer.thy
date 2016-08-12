(* This file provides the definition of writer monad transformer as ML functor.
 * This implementation is following the style of
 *  package/transformers-0.5.1.0/docs/src/Control-Monad-Trans-Writer-Lazy.html *)
theory Writer
imports Category
begin

ML{* functor mk_writerMT_M0P_Core (structure Mono:MONOID; structure Base:MONAD_0PLUS_MIN) 
 : TMONAD_0PLUS_MIN =
(* Poly/ML does not accept HO functor. Therefore, I have to pass a monoid explicitly.*)
struct
    open Mono;
    structure Base = Base;
    type 'a monad  = (monoid * 'a) Base.monad;
    (* MONAD_CORE *)
    fun return (m:'a) = Base.return (mempty, m) : 'a monad;
    fun bind (m:'a monad) (func: 'a -> 'b monad) : 'b monad =
          Base.bind    m          (fn (log1, res1) =>
          Base.bind   (func res1) (fn (log2, res2) =>
          Base.return (mappend log1 log2, res2)));
    (* MONAD_0PLUS_CORE *)
    val mzero = Base.mzero;
    val mplus = Base.mplus;
    (* MONADT*)
    fun lift (bm:'a Base.monad) =
          Base.bind bm (fn bm_res =>
          Base.return (mempty, bm_res)) : (monoid * 'a) Base.monad;
end;
*}

ML{* functor mk_writerMT_M0P (structure Mono:MONOID; structure Base:MONAD_0PLUS_MIN):TMONAD_0PLUS =
struct
  structure WMT_M0P_Core = mk_writerMT_M0P_Core (struct structure Mono = Mono; structure Base = Base end);
  structure WMT_M0P = mk_TMonad_0Plus (WMT_M0P_Core);
  open WMT_M0P;
end;
*}

end