infix 1 THEN_CONTEXT
infix 1 THEN_ALL_NEW_FWD

signature BASIC_UTIL =
sig
  val INTERVAL_FWD: (int -> tactic) -> int -> int -> tactic
  val REPEAT_ALL_NEW_FWD: (int -> tactic) -> int -> tactic
  val THEN_CONTEXT: tactic * context_tactic -> context_tactic;
  val THEN_ALL_NEW_FWD: (int -> tactic) * (int -> tactic) -> int -> tactic
end


signature UTIL =
sig
  include BASIC_UTIL
  val appair: ('a -> 'c) -> ('b -> 'd) -> ('a * 'b) -> ('c * 'd)

  val infst: ('a -> 'b -> 'c * 'b) -> 'a * 'e -> 'b -> ('c * 'e) * 'b

  val fst_ord: ('a * 'a -> order) -> ('a * 'b) * ('a * 'b) -> order
  val snd_ord: ('b * 'b -> order) -> ('a * 'b) * ('a * 'b) -> order
  val none_inf_ord: ('a * 'a -> order) -> ('a option * 'a option) -> order

  val dest_bool: term -> bool
  val dest_option: term -> term option
  val dest_pair: term -> term * term
  val dest_tuple: term -> term list

  val SIMPLE_METHOD_CASES: context_tactic -> Method.method

end

structure Util : UTIL =
 struct

fun (tac1 THEN_CONTEXT tac2) : context_tactic =
  fn (ctxt, st) => st |> tac1 |> Seq.maps (pair ctxt #> tac2);

fun appair f g (x, y) = (f x, g y)

fun infst f (x,y) c = let val (x',c') = f x c in ((x',y), c') end

fun fst_ord ord ((x, _), (x', _)) = ord (x, x')
fun snd_ord ord ((_, y), (_, y')) = ord (y, y')

fun none_inf_ord ord (SOME x, SOME y) = ord (x, y)
  | none_inf_ord _ (NONE, NONE) = EQUAL
  | none_inf_ord _ (NONE, SOME _) = GREATER
  | none_inf_ord _ (SOME _, NONE) = LESS;


fun dest_option (Const (@{const_name "None"}, _)) = NONE
  | dest_option (Const (@{const_name "Some"}, _) $ t) = SOME t
  | dest_option t = raise TERM ("dest_option", [t])

fun dest_bool @{const "True"} = true
  | dest_bool @{const "False"} = false
  | dest_bool t = raise TERM ("dest_bool", [t])

fun dest_pair (Const (@{const_name "Pair"}, _) $ t $ u) = (t,u)
  | dest_pair t = raise TERM ("dest_pair", [t])

fun dest_tuple (Const (@{const_name Pair}, _) $ t1 $ t2) =
      t1 :: dest_tuple t2
  | dest_tuple t = [t]



fun SIMPLE_METHOD_CASES tac =
  CONTEXT_METHOD (fn facts => fn (ctxt, st) =>
    (ctxt, st) |> (ALLGOALS (Method.insert_tac ctxt facts) THEN_CONTEXT tac));

(* Apply tactic to subgoals in interval, in a forward manner, skipping over
  emerging subgoals *)
fun INTERVAL_FWD tac l u st =
  if l>u then all_tac st
  else (tac l THEN (fn st' => let
      val ofs = Thm.nprems_of st' - Thm.nprems_of st;
    in
      if ofs < ~1 then raise THM (
        "INTERVAL_FWD: Tac solved more than one goal",~1,[st,st'])
      else INTERVAL_FWD tac (l+1+ofs) (u+ofs) st'
    end)) st;

(* Apply tac2 to all subgoals emerged from tac1, in forward manner. *)
fun (tac1 THEN_ALL_NEW_FWD tac2) i st =
  (tac1 i
    THEN (fn st' => INTERVAL_FWD tac2 i (i + Thm.nprems_of st' - Thm.nprems_of st) st')
  ) st;

fun REPEAT_ALL_NEW_FWD tac =
  tac THEN_ALL_NEW_FWD (TRY o (fn i => REPEAT_ALL_NEW_FWD tac i));


end

structure Basic_Util: BASIC_UTIL = Util
open Basic_Util
