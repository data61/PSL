(*  Title:      Constructor_Class.ML
    Author:     Yutaka Nagashima, Data61, CSIRO

This file provides various instances of constructor classes.
The implementation is inspired by the corresponding formalisation used in the Haskell community.
*)

(** Seq **)
structure Seq_M0P_Min : MONAD_0PLUS_MIN =
struct
  type 'a monad     = 'a Seq.seq;
  val return        = Seq.single;
  fun bind seq func = Seq.flat (Seq.map func seq);
  val mzero         = Seq.empty;
  fun mplus (f, s)  = Seq.append f s;
end;

structure Seq_M0P = mk_Monad_0Plus (Seq_M0P_Min);

(** List **)
structure List_M0P_Min : MONAD_0PLUS_MIN =
struct
  type 'a monad     = 'a list;
  fun return x      = [x];
  fun bind seq func = flat (map func seq);
  val mzero         = [];
  fun mplus (f, s)  = f @ s;
end;

structure ListCC = mk_Monad_0Plus (List_M0P_Min);

(** Maybe **)
structure Option_M0P_Min : MONAD_0PLUS_MIN =
struct
  type 'a monad       = 'a Option.option;
  val return          = Option.SOME;
  fun bind  NONE      _    = NONE
   |  bind (SOME sth) func = func sth;
  val mzero           = Option.NONE;
  fun mplus (NONE, r) = r
   |  mplus (left, _) = left;
end;

structure Option_M0P = mk_Monad_0Plus (Option_M0P_Min);

(** Strings as Monoid **)
structure Strings_Min : MONOID_MIN =
struct
  type monoid_min = string list;
  val mempty = [];
  fun mappend src1 src2 = src1 @ src2;
end;

structure Strings = mk_Monoid (Strings_Min) : MONOID;

(** Cons Prod **)
(*
 * We have to define CONS_PROD because Standard ML cannot handle
 * ML{* type ('f, 'g, 'p) cons_prod = ('p 'f) * ('p 'g); *}  
 *)
signature CONS_PROD =
sig
  (* Is this a valid specification for constructor products (:*:)? *)
  type 'a left_cons;
  type 'a right_cons;
  type 'a cons_prod = 'a left_cons * 'a right_cons;
end;

functor mk_ConsProdMonadMin(structure Left:MONAD_MIN; structure Right:MONAD_MIN) =
struct
  type 'a monad      = 'a Left.monad * 'a Right.monad;
  fun return valu    = (Left.return valu, Right.return valu) : 'a monad;
  fun bind ((m, n):'a monad) (func:('a -> 'b Left.monad * 'b Right.monad)) =
       ((Left.bind  m (fn a => fst (func a))),
        (Right.bind n (fn a => snd (func a)))) : 'b monad;
end : MONAD_MIN;

(* Example of mk_ConsProdMonadMin's use case. *)
structure ListOptionConsProdMonadMin:MONAD_MIN = mk_ConsProdMonadMin(
  struct
         structure Left  = List_M0P_Min;
         structure Right = Option_M0P_Min
  end):MONAD_MIN;

structure ListOptionConsProdMonad = mk_Monad(ListOptionConsProdMonadMin);

ListOptionConsProdMonadMin.return "foo";

(** State **)
functor mk_stateMT_M0P_Min (structure State : TYP; structure Base : MONAD_0PLUS_MIN) : TMONAD_0PLUS_MIN =
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

functor mk_state_M0PT (structure Log : TYP; structure Base : MONAD_0PLUS_MIN): TMONAD_0PLUS =
let
  structure SMT_M0P_Core = mk_stateMT_M0P_Min(struct structure State = Log; structure Base = Base end);
  structure SMT_M0P = mk_TMonad_0Plus(SMT_M0P_Core);
in
  SMT_M0P
end;

functor mk_StateM_Min (State : TYP) : MONAD_MIN =
struct
  type 'a monad = State.typ -> ('a * State.typ);
  fun return v = fn s => (v, s);
  fun bind st f = fn s => let val (v, s') = st s in f v s' end;
end;

functor mk_StateM (State : TYP) : MONAD =
struct
  structure StateM_Min = mk_StateM_Min (State);
  structure StateM = mk_Monad (StateM_Min);
  open StateM;
end;

signature TSTATE_MONAD_0PLUS_MIN =
sig
  include TMONAD_0PLUS;
  val update : ('s -> 's) -> 's -> ('s * 's) Base.monad;
end;

signature TSTATE_MONAD_0PLUS =
sig
  include TMONAD_0PLUS;
  val update : ('s -> 's) -> 's -> ('s * 's) Base.monad;
  val set    : 's -> 's -> ('s * 's) Base.monad;
  val fetch  : 's -> ('s * 's) Base.monad;
end;

functor tM0p_Min_to_State_Monad_0Plus (structure State : TYP; structure Base : MONAD_0PLUS_MIN)
 : TSTATE_MONAD_0PLUS_MIN =
struct
  structure State_M0pt = mk_state_M0PT (struct structure Log = State; structure Base = Base end);
  open State_M0pt;
  fun update f = fn s => Base.return (s, f s)
end;

functor mk_TState_Monad_0Plus_Min (structure State : TYP; structure Base : MONAD_0PLUS_MIN) =
struct
  structure TState_M0p = mk_state_M0PT (struct structure Log = State; structure Base = Base end);
  open TState_M0p;
  fun update f = fn state => Base.return (state, f state);
end : TSTATE_MONAD_0PLUS_MIN;

functor mk_TState_Monad_0Plus (structure State : TYP; structure Base : MONAD_0PLUS_MIN) =
struct
  structure TState_M0p_Min = mk_TState_Monad_0Plus_Min (struct structure State = State;
                                                               structure Base = Base end);
  structure TState_M0P = mk_TMonad_0Plus (TState_M0p_Min);
  open TState_M0P;
  val update = TState_M0p_Min.update;
  fun set s   = update (fn _ => s);
  fun fetch s = update I s;
end : TSTATE_MONAD_0PLUS;