(* This file provides the definition of state monad transformer as ML functor.  *)
(* The implementation of the state monad tansformer is inspired by the          *)
(* corresponding functions used in the Haskell community.                       *)
theory State
imports Category Strings Seq
begin

ML{* functor mk_stateMT_M0P_Min (structure State : TYP; structure Base : MONAD_0PLUS_MIN) : TMONAD_0PLUS_MIN =
struct
  structure Base = Base;
  type 'a monad = State.typ -> (State.typ * 'a) Base.monad;
  (* MONAD_CORE *)
  fun return valu = fn state => Base.return (state, valu);
  fun bind st_trans bfun = fn state0 => 
    Base.bind (st_trans state0) (fn (state1, result1) => bfun result1 state1);
  (* MONADT *)
  fun lift m  = fn state => Base.bind m (fn result => Base.return (state, result));
  (* MONAD_0PLUS_CORE *)
  val mzero = fn _(*state*) => Base.mzero
  fun mplus (reader1, reader2) = fn state => Base.mplus (reader1 state, reader2 state);
end
*}

ML{* functor mk_state_M0PT (structure Log : TYP; structure Base : MONAD_0PLUS_MIN): TMONAD_0PLUS =
let
  structure SMT_M0P_Core = mk_stateMT_M0P_Min(struct structure State = Log; structure Base = Base end);
  structure SMT_M0P = mk_TMonad_0Plus(SMT_M0P_Core);
in
  SMT_M0P
end;
*}

ML{* functor mk_StateM_Min (State : TYP) : MONAD_MIN =
struct
  type 'a monad = State.typ -> ('a * State.typ);
  fun return v = fn s => (v, s);
  fun bind st f = fn s => let val (v, s') = st s in f v s' end;
end;
*}

ML{* functor mk_StateM (State : TYP) : MONAD =
struct
  structure StateM_Min = mk_StateM_Min (State);
  structure StateM = mk_Monad (StateM_Min);
  open StateM;
end;
*}

ML{* signature TSTATE_MONAD_0PLUS_MIN =
sig
  include TMONAD_0PLUS;
  val update : ('s -> 's) -> 's -> ('s * 's) Base.monad;
end;
*}

ML{* signature TSTATE_MONAD_0PLUS =
sig
  include TMONAD_0PLUS;
  val update : ('s -> 's) -> 's -> ('s * 's) Base.monad;
  val set    : 's -> 's -> ('s * 's) Base.monad;
  val fetch  : 's -> ('s * 's) Base.monad;
end;
*}

ML{* functor tM0p_Min_to_State_Monad_0Plus (structure State : TYP; structure Base : MONAD_0PLUS_MIN)
 : TSTATE_MONAD_0PLUS_MIN =
struct
  structure State_M0pt = mk_state_M0PT (struct structure Log = State; structure Base = Base end);
  open State_M0pt;
  fun update f = fn s => Base.return (s, f s)
end;
*}

ML{* functor mk_TState_Monad_0Plus_Min (structure State : TYP; structure Base : MONAD_0PLUS_MIN) =
struct
  structure TState_M0p = mk_state_M0PT (struct structure Log = State; structure Base = Base end);
  open TState_M0p;
  fun update f = fn state => Base.return (state, f state);
end : TSTATE_MONAD_0PLUS_MIN;
*}

ML{* functor mk_TState_Monad_0Plus (structure State : TYP; structure Base : MONAD_0PLUS_MIN) =
struct
  structure TState_M0p_Min = mk_TState_Monad_0Plus_Min (struct structure State = State; structure Base = Base end);
  structure TState_M0P = mk_TMonad_0Plus (TState_M0p_Min);
  open TState_M0P;
  val update = TState_M0p_Min.update;
  fun set s   = update (fn _ => s);
  fun fetch s = update I s;
end : TSTATE_MONAD_0PLUS;
*}

end