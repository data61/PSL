(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: TotalRecall.ML                                                       *)
(* Authors: Simon Foster & Frank Zeyda (University of York, UK)               *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)

(* An improvement may be to respectively collect no_syntax and no_notation
   items into a single undecl_item as part of the execute_all function. This
   may result in a more efficient execution of undeclarations. A known issue
   is that we have no guarantee that an undeclaration will still be correctly
   parsed and executed in a sub-theory: there ought to be some error-catching
   and reporting mechanism at least (a more robust approach could replaced
   names i.e. for constants and types by their full-qualified names). *)

(* Signature ORDERS *)

signature ORDERS =
sig
  val triple_ord : ('a * 'b -> order) -> ('c * 'd -> order) ->
    ('e * 'f -> order) -> ('a * 'c * 'e) * ('b * 'd * 'f) -> order
  val mode_ord : (string * bool) * (string * bool) -> order
  val source_ord : Input.source * Input.source -> order
  val input_ord : string * string -> order
  val mixfix_ord : mixfix * mixfix -> order
end

(* Structure Orders *)

structure Orders : ORDERS =
struct
  fun triple_ord f g h ((x1, y1, z1), (x2, y2, z2)) =
    (prod_ord f (prod_ord g h)) ((x1, (y1, z1)), (x2, (y2, z2)));

  val mode_ord = prod_ord string_ord bool_ord;
  val source_ord = string_ord o (apply2 (Input.source_content #> fst));
  val input_ord = source_ord o (apply2 Syntax.read_input);

  local
  val mixfix_ctor_ord =
    let fun mixfix_ctor_num NoSyn = 0
    | mixfix_ctor_num (Mixfix _) = 1
    | mixfix_ctor_num (Infix _) = 2
    | mixfix_ctor_num (Infixl _) = 3
    | mixfix_ctor_num (Infixr _) = 4
    | mixfix_ctor_num (Binder _) = 5
    | mixfix_ctor_num (Structure _) = 6
    in int_ord o (apply2 mixfix_ctor_num) end;
  in
  fun mixfix_ord (Mixfix (sy, ps, p, _), Mixfix (sy', ps', p', _)) =
    (prod_ord source_ord (prod_ord (list_ord int_ord) int_ord))
      ((sy, (ps, p)), (sy', (ps', p')))
  | mixfix_ord (Infix (sy, p, _), Infix (sy', p', _)) =
      (prod_ord source_ord int_ord) ((sy, p), (sy', p'))
  | mixfix_ord (Infixl (sy, p, _), Infixl (sy', p', _)) =
      (prod_ord source_ord int_ord) ((sy, p), (sy', p'))
  | mixfix_ord (Infixr (sy, p, _), Infixr (sy', p', _)) =
      (prod_ord source_ord int_ord) ((sy, p), (sy', p'))
  | mixfix_ord (Binder (sy, p, q, _), Binder (sy', p', q', _)) =
    (prod_ord source_ord (prod_ord int_ord int_ord))
      ((sy, (p, q)), (sy', (p', q')))
  | mixfix_ord (m1, m2) = mixfix_ctor_ord (m1, m2);
  end;
end;

(* Signature STRINGOF *)

signature STRINGOF =
sig
  val list : string * string * string -> ('a -> string) -> 'a list -> string
  val mode : string * bool -> string
  val input : string -> string
  val mixfix : mixfix -> string
end

(* Structure StringOf *)

structure StringOf : STRINGOF =
struct
  fun list (left_delim, sep, right_delim) string_of_item list =
    let fun string_of_list_rec [] = ""
    | string_of_list_rec [x] = (string_of_item x)
    | string_of_list_rec (h :: t) =
        (string_of_item h) ^ sep ^ (string_of_list_rec t) in
      left_delim ^ (string_of_list_rec list) ^ right_delim
    end;

  fun mode (mode as (prmode, both)) =
    if mode = Syntax.mode_default then ""
    else (if mode = Syntax.mode_input then "(input)"
    else "(" ^ prmode ^ (if both then "" else " output") ^ ")");

  val input = ((Input.source_content #> fst) o Syntax.read_input);
  val mixfix = (Pretty.string_of o Mixfix.pretty_mixfix);
end;

(* Signature TOTALRECALL *)

signature TOTALRECALL =
sig
  val record_no_syntax : Syntax.mode ->
    (string * string * mixfix) list -> theory -> theory
  val record_no_notation : Syntax.mode ->
    (string * mixfix) list -> theory -> theory
  val execute_all : theory -> theory
end;

(* Structure TotalRecall *)

structure TotalRecall : TOTALRECALL =
struct
  open Orders;

  datatype undecl_item =
    no_syntax of Syntax.mode * (string * string * mixfix) list
  | no_notation of Syntax.mode * (string * mixfix) list;

  (* fun flatten_undecl_item (no_syntax (mode, args)) =
    map (fn arg => no_syntax (mode, [arg])) args
  | flatten_undecl_item (no_notation (mode, args)) =
    map (fn arg => no_notation (mode, [arg])) args; *)

  (* An order on undecl_item is needed for efficient storage using Ord_List. *)

  local
  val undecl_item_ctor_ord =
    let fun undecl_item_ctor_num (no_syntax _) = 0
    | undecl_item_ctor_num (no_notation _) = 1
    in int_ord o (apply2 undecl_item_ctor_num) end;
  in
  fun undecl_item_ord (no_syntax args, no_syntax args') =
    (prod_ord mode_ord (list_ord
      (triple_ord string_ord input_ord mixfix_ord))) (args, args')
  | undecl_item_ord (no_notation args, no_notation args') =
    (prod_ord mode_ord
      (list_ord (prod_ord input_ord mixfix_ord))) (args, args')
  | undecl_item_ord (r1, r2) = undecl_item_ctor_ord (r1, r2);
  end;

  local
  fun space s = (if s = "" then "" else " " ^ s);
  fun quote s = ("\"" ^ s ^ "\"");
  in
  fun string_of_undecl_item item =
    (case item of
      no_syntax (mode, args) => "no_syntax" ^ space(StringOf.mode mode) ^
      (StringOf.list ("\n ", "\n ", "\n")
        (fn (syntax, typ, mixfix) =>
          space(quote(syntax)) ^ " :: " ^ quote(StringOf.input typ) ^
          space(StringOf.mixfix mixfix))) args
    | no_notation (mode, args) => "no_notation" ^ space(StringOf.mode mode) ^
      (StringOf.list ("\n ", " and\n ", "\n")
        (fn (const, mixfix) =>
          space(const) ^
          space(StringOf.mixfix mixfix))) args);
  end;

  (* Theory Data *)

  structure Undecl_Data = Theory_Data (
    type T = undecl_item Ord_List.T;
    val empty = [];
    val extend = I;
    val merge = uncurry (Ord_List.union undecl_item_ord);
  );

  fun insert_undecl_item item =
    (Undecl_Data.map (Ord_List.insert undecl_item_ord(*'*) item));

  fun record_no_syntax mode args =
    insert_undecl_item (no_syntax (mode, args));

  fun record_no_notation mode args =
    insert_undecl_item (no_notation (mode, args));

  (* We collapse similar-type items for efficiency reasons since execution can
     become very slow with a lot of individual no_syntax and no_notation items.
     We get away with the simple code since the items are lexically ordered. *)

  fun collaps_items
    (no_syntax (m1, args1) :: no_syntax (m2, args2) :: t) =
      (if m1 = m2 then
        (collaps_items (no_syntax (m1, args1 @ args2) :: t))
      else no_syntax (m1, args1) ::
        (collaps_items ((no_syntax (m2, args2)) :: t)))
  | collaps_items
    (no_notation (m1, args1) :: no_notation (m2, args2) :: t) =
      (if m1 = m2 then
        (collaps_items (no_notation (m1, args1 @ args2) :: t))
      else no_notation (m1, args1) ::
        (collaps_items ((no_notation (m2, args2)) :: t)))
  | collaps_items (h :: t) = h :: (collaps_items t)
  | collaps_items [] = [];

  fun execute_one item =
    (Output.writeln (string_of_undecl_item item);
    (case item of
      (no_syntax (mode, args)) =>
        (Sign.del_syntax_cmd mode args)
    | (no_notation (mode, args)) =>
        (Named_Target.theory_map
          (Specification.notation_cmd false mode args))));

  fun execute_all thy =
    (Output.writeln "Restoring purged notations and syntax...\n";
      (fold execute_one (collaps_items (Undecl_Data.get thy)) thy));
end;