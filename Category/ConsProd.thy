theory ConsProd
imports ListCC Maybe
begin

(*
 * We have to define CONS_PROD because Standard ML cannot handle
 * ML{* type ('f, 'g, 'p) cons_prod = ('p 'f) * ('p 'g); *}  
 *)

ML{* signature CONS_PROD =
sig
  (* Is this a valid specification for constructor products (:*:)? *)
  type 'a left_cons;
  type 'a right_cons;
  type 'a cons_prod = 'a left_cons * 'a right_cons;
end;
*}

ML{* functor mk_ConsProdMonadMin(structure Left:MONAD_MIN; structure Right:MONAD_MIN) =
struct
  type 'a monad      = 'a Left.monad * 'a Right.monad;
  fun return valu    = (Left.return valu, Right.return valu) : 'a monad;
  fun bind ((m, n):'a monad) (func:('a -> 'b Left.monad * 'b Right.monad)) =
       ((Left.bind  m (fn a => fst (func a))),
        (Right.bind n (fn a => snd (func a)))) : 'b monad;
end : MONAD_MIN;
*}

(* test mk_ConsProdMonadMin *)
ML{* structure ListOptionConsProdMonadMin:MONAD_MIN = mk_ConsProdMonadMin(
  struct
         structure Left  = List_M0P_Min;
         structure Right = Option_M0P_Min
  end):MONAD_MIN;

structure ListOptionConsProdMonad = mk_Monad(ListOptionConsProdMonadMin);
*}

ML{* ListOptionConsProdMonadMin.return "foo" *}

end