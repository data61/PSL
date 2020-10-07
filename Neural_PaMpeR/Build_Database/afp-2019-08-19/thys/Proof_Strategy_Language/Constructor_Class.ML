(*  Title:      Constructor_Class.ML
    Author:     Yutaka Nagashima, Data61, CSIRO

This file contains the hierarchical formalisation of modular constructor classes.
One has to provide minimal definitions to instantiate these classes.
The underlying concepts are explained in the following short paper:
 Close Encounters of the Higher Kind Emulating Constructor Classes in Standard ML
 available at https://arxiv.org/abs/1608.03350

This file is following the style of the Base package of Haskell.
This file uses the ML keyword "open" many times to encode the dependency among classes, while
keeping the code base small and clean.
*)

(** TYP **)
signature TYP =
sig
  type typ
end;

(** MONOID_MIN **)
signature MONOID_MIN =
sig
  type monoid_min;
  val mempty : monoid_min;
  val mappend : monoid_min -> monoid_min -> monoid_min;
end;

(** MONOID **)
signature MONOID =
sig
  type monoid;
  include TYP MONOID_MIN;
  sharing type monoid = typ;
  sharing type monoid = monoid_min;
  val mconcad : monoid list -> monoid;
end;

(** mk_Monoid **)
functor mk_Monoid (Min:MONOID_MIN) : MONOID =
struct
  open Min;
  type typ    = Min.monoid_min;
  type monoid = Min.monoid_min;
  val mconcad = List.foldr (uncurry mappend) mempty;
end;

(** FUNCTOR_MIN **)
signature FUNCTOR_MIN =
sig
  type 'a functo;
  val fmap : ('a -> 'b) -> 'a functo -> 'b functo;
end;

(** FUNCTOR **)
signature FUNCTOR =
sig
  include FUNCTOR_MIN;
  val <$  :  'a * 'b functo -> 'a functo;
  val <$> : ('a -> 'b) * 'a functo -> 'b functo;
  val void: 'a functo -> unit functo;
end;

(** mk_Functor **)
functor mk_Functor (Min:FUNCTOR_MIN) : FUNCTOR =
struct
  (* FUNCTOR_Min *)
  open Min;
  infix 0 <$ <$>;
  fun x <$ f  = (fmap o K) x f;
  fun x <$> f = fmap x f;
  fun void x  = () <$ x;
end;

(** APPLICATIVE_MIN **)
signature APPLICATIVE_MIN =
sig
  type 'a applicative;
  val pure : 'a -> 'a applicative;
  (* Sequential application. *)
  val <*> : ('a -> 'b) applicative * 'a applicative -> 'b applicative;
end;

(** applicative_Min_to_Functor_Min **)
functor applicative_Min_to_Functor_Min (Min:APPLICATIVE_MIN) : FUNCTOR_MIN =
struct
  open Min;
  infix <*>;
  type 'a functo = 'a applicative;
  fun fmap f xs = pure f <*> xs;
end;

(** APPLICATIVE **)
signature APPLICATIVE =
sig
  include APPLICATIVE_MIN FUNCTOR;
  sharing type applicative = functo;
  (* Sequence actions, discarding the value of the first argument. *)
  val *> : 'a applicative * 'b applicative -> 'b applicative;
  (* Sequence actions, discarding the value of the second argument. *)
  val <* : 'a applicative * 'b applicative -> 'a applicative;
  val <**>   : ('a applicative * ('a -> 'b) applicative) -> 'b applicative;
  val liftA  : ('a -> 'b) -> 'a applicative -> 'b applicative;
  val liftA2 : ('a -> 'b -> 'c) -> 'a applicative -> 'b applicative -> 'c applicative;
  val liftA3 : ('a -> 'b -> 'c -> 'd) -> 'a applicative -> 'b applicative -> 'c applicative -> 'd applicative;
end;

(** mk_Applicative **)
functor mk_Applicative (Min:APPLICATIVE_MIN) : APPLICATIVE =
struct
  type 'a applicative = 'a Min.applicative;
  (* FUNCTOR  *)
  structure Functor_Core = applicative_Min_to_Functor_Min (Min);
  structure Functor = mk_Functor (Functor_Core);
  open Functor Min;
  (* APPLICATIVE_AUX *)
  infix <*> *> <* <**>;
  fun u *> v = pure (K I) <*> u <*> v;
  fun u <* v = pure K <*> u <*> v;
  fun liftA f a = pure f <*> a;
  fun liftA2 f a b = fmap f a <*> b;
  fun liftA3 f a b c = fmap f a <*> b <*> c;
  fun m <**> f = f <*> m;
end;

(** MONAD_MIN **)
signature MONAD_MIN =
sig
  type 'a monad;
  val return : 'a -> 'a monad;
  val bind : 'a monad -> ('a -> 'b monad) -> 'b monad;
end;

(** monad_Min_to_Applicative_Min **)
functor monad_Min_to_Applicative_Min (Min:MONAD_MIN) : APPLICATIVE_MIN =
struct
  open Min;
  type 'a applicative = 'a monad;
  val pure = return;
  fun <*> (fs, xs) = bind fs (fn fs' => bind xs (fn xs' => return (fs' xs')));
end;

(** MONAD **)
signature MONAD =
sig
  include APPLICATIVE MONAD_MIN;
  sharing type monad = applicative;

  val >>=    : 'a monad * ('a -> 'b monad) -> 'b monad;
  val fail   : string -> 'a monad;
  val >>     : 'a monad * 'b monad -> 'b monad;
  val =<<    : ('a -> 'b monad) * 'a monad -> 'b monad;
  val comp   : ('a -> 'b monad) -> ('b -> 'c monad) -> 'a -> 'c monad;
  val >=>    : ('a -> 'b monad) * ('b -> 'c monad) -> 'a -> 'c monad;
  val <=<    : ('b -> 'c monad) * ('a -> 'b monad) -> 'a -> 'c monad;
  val forever: 'a monad -> 'b monad;  
  val liftM  : ('a -> 'b) -> ('a monad -> 'b monad);
  val join   : 'a monad monad -> 'a monad;
  (* mapM, mapM_, forM, forM_, sequence, sequence_, foldM, and foldM here,
   * have additional type class constraints (Traversable and Foldable).
   * One can define them polymorphically using the ML keyword functor. *)
  val filterM: ('a -> bool monad) -> 'a list -> 'a list monad;
end;

(** mk_Monad **)
functor mk_Monad (Min : MONAD_MIN): MONAD =
struct
  type 'a monad = 'a Min.monad;
  (* APPLICATIVE *)
  structure Applicative_Min = monad_Min_to_Applicative_Min (Min);
  structure Applicative = mk_Applicative (Applicative_Min);
  open Applicative;
  (* MONAD_MIN *)
  open Min;
  (* MONAD_AUX *)
  fun comp f g  = fn x => bind (f x) g;
  infix >>=  >=> <=< >> =<<;
  fun m >>= f   = bind m f;
  fun f =<< m   = bind m f;
  fun f >=> g   = comp f g;
  fun g <=< f   = comp f g;
  fun m1 >> m2  = bind m1 (fn _ => m2);
  fun fail s    = error s;
  fun liftM f m = bind m (fn m' => return (f m'));
  fun join n    = bind n I;
  fun forever a = let fun get_a' a' = a >> get_a' a' in get_a' a end;
  fun filterM prop =
    let
      fun swap_args f x y = f y x;
      fun foldr' f = Library.foldr (uncurry f) |> curry |> swap_args;
      fun go x ret =
        prop x >>= (fn flg =>
        ret    >>= (fn ys  =>
        return (if flg then x::ys else ys)));
    in
      foldr' go (return [])
    end;
end;

(** ALTERNATIVE_MIN **)
signature ALTERNATIVE_MIN =
sig
  type 'a alternative;
  val empty   : 'a alternative;
  val <|>     : 'a alternative * 'a alternative -> 'a alternative;
  val alt_pure: 'a -> 'a alternative;
  val alt_seq : ('a -> 'b) alternative * 'a alternative -> 'b alternative;
end;

(** alternative_Min_to_Applictive_Min **)
functor alternative_Min_to_Applictive_Min (Alternative_Min:ALTERNATIVE_MIN) : APPLICATIVE_MIN =
struct
  open Alternative_Min;
  type 'a applicative = 'a alternative;
  val pure = alt_pure;
  val <*>  = alt_seq;
end;

(** ALTERNATIVE **)
signature ALTERNATIVE =
sig
  include APPLICATIVE ALTERNATIVE_MIN;
  sharing type alternative = applicative;
  (* methods *)
  val some : 'a alternative -> 'a list alternative;
  val many : 'a alternative -> 'a list alternative;
  (* utility functions *)
  val optional : 'a alternative -> 'a Option.option alternative;
end;

(** mk_Alternative **)
functor mk_Alternative (Alternative_Core:ALTERNATIVE_MIN) : ALTERNATIVE =
struct
  structure Applicative_Min  = alternative_Min_to_Applictive_Min (Alternative_Core);
  structure Applicative      = mk_Applicative (Applicative_Min);
  open Applicative Alternative_Core;
  infix <$> <*> <|>;
  fun some     (v:'a alternative) = curry (op ::) <$> v <*> many v : 'a list alternative
  and many     (v:'a alternative) = some v <|> pure [] : 'a list alternative;
  fun optional (v:'a alternative) = SOME <$> v <|> pure NONE;
end;

(** MONAD_0PLUS_MIN **)
signature MONAD_0PLUS_MIN =
sig
  type 'a monad;
  val return : 'a -> 'a monad;
  val bind : 'a monad -> ('a -> 'b monad) -> 'b monad;
  val mzero : 'a monad;
  val mplus : ('a monad * 'a  monad) -> 'a monad;
end;

(** monad0plus_Min_to_Alternative_min **)
functor monad0plus_Min_to_Alternative_min(M0p_Min:MONAD_0PLUS_MIN) : ALTERNATIVE_MIN =
struct
  open M0p_Min;
  type 'a alternative = 'a monad;
  val empty            = mzero;
  val <|>              = mplus;
  val alt_pure         = return;
  fun alt_seq (fs, xs) = bind fs (fn fs' => bind xs (fn xs' => return (fs' xs')));
end;

(** MONAD_0PLUS **)
signature MONAD_0PLUS =
sig
  include MONAD;
  (* Do not "include" ALTERNATIVE to avoid name conflicts. *)
  val mzero : 'a monad;
  val mplus : ('a monad * 'a  monad) -> 'a monad;

  (* auxiliary functions for 0PLUS *)
  val msum  : 'a monad Seq.seq -> 'a monad;
  val guard : bool -> unit monad;

  (* ALTERNATIVE_MIN *)
  include ALTERNATIVE_MIN;
  (* ALTERNATIVE: we cannot use the keyword "include" to avoid the collision of Applicatives 
   * from Monad and Alternative. *)
  sharing type alternative = applicative;
  (* methods *)
  val some : 'a alternative -> 'a list alternative;
  val many : 'a alternative -> 'a list alternative;
  (* utility functions *)
  val optional : 'a alternative -> 'a Option.option alternative;
end;

(** mk_Monad_0Plus **)
functor mk_Monad_0Plus (Min : MONAD_0PLUS_MIN) : MONAD_0PLUS =
struct
  type 'a monad = 'a Min.monad;
  (* MONAD *)
  structure Monad = mk_Monad (Min : MONAD_MIN);
  open Monad;
  (* MONAD_0PLUS_MIN *)
  open Min;
  (* MONAD0PLUS_AUX  *)
  fun msum xs = Seq2.foldr mplus mzero xs : 'a monad
  fun guard true = pure ()
    | guard _ = mzero;

  (* ALTERNATIVE *)
  structure Alternative_Min = monad0plus_Min_to_Alternative_min(Min);
  structure Alternative     = mk_Alternative(Alternative_Min);
  open Alternative;
end;

(** TMONAD_MIN **)
signature TMONAD_MIN =
sig
  include MONAD_MIN;
  structure Base: MONAD_MIN;
  val lift : 'a Base.monad -> 'a monad;
end;

(** TMONAD **)
signature TMONAD = 
(* The signature of transformed monad (= the return type of monad transformer). *)
sig
  include MONAD;
  structure Base : MONAD;
  val lift : 'a Base.monad -> 'a monad;
end;

(** mk_TMonad **)
functor mk_TMonad (Min : TMONAD_MIN) : TMONAD =
struct
  structure Monad = mk_Monad (Min : MONAD_MIN);
  open Monad;
  structure Base = mk_Monad (Min.Base : MONAD_MIN);
  val lift = Min.lift;
end;

(** TMONAD_0PLUS_MIN **)
signature TMONAD_0PLUS_MIN =
sig
  include MONAD_0PLUS_MIN;
  structure Base: MONAD_0PLUS_MIN;
  val lift : 'a Base.monad -> 'a monad;
end;

(** TMONAD_0PLUS **)
signature TMONAD_0PLUS =
sig
  include MONAD_0PLUS;
  structure Base : MONAD_0PLUS;
  val lift : 'a Base.monad -> 'a monad;
end;

(** mk_TMonad_0Plus **)
functor mk_TMonad_0Plus (Min : TMONAD_0PLUS_MIN) : TMONAD_0PLUS =
struct
  structure Monad0Plus = mk_Monad_0Plus (Min : MONAD_0PLUS_MIN);
  open Monad0Plus;
  structure Base = mk_Monad_0Plus (Min.Base : MONAD_0PLUS_MIN);
  val lift = Min.lift;
end;