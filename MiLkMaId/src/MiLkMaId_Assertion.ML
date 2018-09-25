(*  Title:      MiLkMaId/MiLkMaId_Assertion.ML
    Author:     Yutaka Nagashima, CIIRC, CTU

This file defines functions to convert proof obligations to a simpler format,
so that machine learning algorithms can effectively recommend which arguments to use to
apply mathematical induction in Isabelle/HOL.
*)

(** Utility functions **)

(* How to check if a constant is recursively defined. *)
fun is_recursive (cname:string) (_ $ (Term.Const ("HOL.eq",_) $ A $ B)) =
(* TODO: remove code-duplication with PaMpeR/Assertion.ML *)
  let
     val cname_is_in_lhs = Term.exists_Const (fn (s,_) => cname = s) A;
     val cname_is_in_rhs = Term.exists_Const (fn (s,_) => cname = s) B;
  in cname_is_in_lhs andalso cname_is_in_rhs end
 |  is_recursive _ _ = false;
fun check_thm_list (thms:thm list) (cname:string) = List.exists (is_recursive cname o Thm.concl_of) thms;
fun exist_related_rsimp  []             = false
 |  exist_related_rsimp (cname::cnames) = 
     (check_thm_list (Proof_Context.get_thms @{context} (cname^".simps")) cname handle ERROR _ =>
      exist_related_rsimp cnames);

fun has_related_rsimp (Const (c, _)) = exist_related_rsimp [c]
 |  has_related_rsimp _ = false;

(* How to get the number of recursive functions in a term? *)
fun count_recursive_consts trm = fold_aterms (fn Const (cname, _) => (fn n =>
  if exist_related_rsimp [cname] then n + 1 else n) | _ => I) trm 0;

(* Utilty functions *)
infix 1 >>= <$>;
val _ = Option.map;
fun (m >>= f) = Option.mapPartial f m;
fun (m <$> f) = Option.map f m;

(** MILKMAID_ASSERTION **)
(*MILKMAID_ASSERTION exposes many functions that are not meant to be used by other users
 *because unit tests using @{assert} in MiLkMaId_Test.thy require them to be accessible.*)
signature MILKMAID_ASSERTION =
sig

(* types *)
datatype uterm =
  UConst of string * typ |
  UFree  of string * typ |
  UVar   of indexname * typ |
  UBound of int |
  UAbs   of string * typ * uterm |(*TODO: maybe we also apply un-currying to lambda abstraction.*)
  UApp   of (uterm * uterm list);
datatype utyp = UC (*UConst*) | UF (*UFree*) | UV (*UVar*) | UB (*UBound*) | UAb (*UAbs*) | UAp (*UAp*);
datatype pattern = Full | Partial | Var | Abstract | Other;
type point =
  {name: string,
   utyp : utyp,
   level: int};
type ancestor =
  {point  : point,
   nth_arg: int};
type ancestors  = ancestor list;
type datum =
  {point    : point,
   ancestors: ancestors};
type data = datum list;
type ancestor_with_pattern =
  {point  : point,
   nth_arg: int,
   pattern: pattern};
type ancestors_with_pattern = ancestor_with_pattern list;
type datum_with_pattern =
  {point    : point,
   ancestors: ancestors_with_pattern};
type data_with_pattern = datum_with_pattern list;
type 'a matrix = 'a list list;
datatype command = Definition | Fun | Function | Inductive | Primrec | Unknown;

(* operations about command *)
type suffixes = (string list * string list);
val check_suffix            : Proof.context -> string -> suffixes -> bool;
val suffix_for_definition   : suffixes;
val suffix_for_primrec      : suffixes;
val suffix_for_fun          : suffixes;
val suffix_for_function     : suffixes;
val suffix_for_inductive    : suffixes;
val suffix_for_inductive_set: suffixes;
val get_command             : string -> Proof.context -> command; (*code duplication with PaMpeR?*)

(* operations on term *)
val flatten           : term -> term list -> term list;
val get_left          : term -> term option;
val get_many          : Proof.context -> string -> (term -> term option) -> term list;
val get_lefts         : Proof.context -> string -> term list;
val is_head_Const     : term -> bool;
val are_Consts        : term -> bool list;
val get_cncl          : term -> term option;
val get_left_in_concl : term -> term option;
val get_left_in_concls: Proof.context -> string -> term list;

(* operations on uterm *)
val map_types'           : (typ -> typ) -> uterm -> uterm;
val uncurry              : term -> uterm;
val get_name             : uterm -> string;
val uncurried_trm_to_data: uterm -> data;
val uterm_to_level       : string -> uterm -> int;

(* operations on matrix *)
val get_elem_in_matrix: 'a matrix -> int * int (*(nth column, nth row) start at 0*) -> 'a option;
val is_regular_matrix : bool matrix -> bool;
val get_nth_column    : bool matrix -> int -> bool list;
val transpose         : bool matrix -> bool list list option;
val classify          : bool matrix -> pattern list option;

(* mk_parameter_matrix *)
val mk_parameter_matrix_for_primrec   : Proof.context -> string -> bool matrix;
val mk_parameter_matrix_for_fun       : Proof.context -> string -> bool matrix;
val mk_parameter_matrix_for_function  : Proof.context -> string -> bool matrix;
val mk_parameter_matrix_for_inductive : Proof.context -> string -> bool matrix;
val mk_parameter_matrix               : Proof.context -> string -> bool matrix;

(* operations about pattern *)
val get_pattern : Proof.context -> string -> int -> pattern;
val data_to_data_with_pattern: Proof.context -> data -> data_with_pattern;

end;

(** MiLkMaId_Assertion **)
structure MiLkMaId_Assertion : MILKMAID_ASSERTION =
struct

(* un-curried syntax tree *)
datatype uterm =
  UConst of string * typ |
  UFree  of string * typ |
  UVar   of indexname * typ |
  UBound of int |
  UAbs   of string * typ * uterm |
  UApp   of (uterm * uterm list);

(* map_types' *)
fun map_types' f =
  let
    fun map_aux' (UConst (a, T))  = UConst (a, f T)
      | map_aux' (UFree (a, T))   = UFree (a, f T)
      | map_aux' (UVar (v, T))    = UVar (v, f T)
      | map_aux' (UBound i)       = UBound i
      | map_aux' (UAbs (a, T, t)) = UAbs (a, f T, map_aux' t)
      | map_aux' (UApp (t, u))    = UApp (map_aux' t, (map map_aux' u));
  in map_aux' : (uterm -> uterm) end;

(* flatten purposefully ignores the nested applications on the right-hand-side of $. *)
fun flatten (trm1 $ trm2) acc = flatten trm1 (trm2 :: acc)
 |  flatten trm acc = trm :: acc;

(* uncurry *)
fun uncurry (Const c) = UConst c
  | uncurry (Free f)  = UFree f
  | uncurry (Var v)   = UVar v
  | uncurry (Bound i) = UBound i
  | uncurry (Abs (name, typ, trm)) = UAbs (name, typ, uncurry trm)
  | uncurry (trm1 $ trm2) =
    let
      val xs = flatten (trm1 $ trm2) [];
    in
      UApp (uncurry (hd xs), map uncurry (tl xs))
    end;

(* get_name *)
fun get_name (UConst  (name, _))        = name
 |  get_name (UFree   (name, _))        = name
 |  get_name (UVar   ((name, numb), _)) = name ^ Int.toString numb
 |  get_name (UBound   numb)            = Int.toString numb
 |  get_name (UAbs    (name, _, _))     = name
 |  get_name (UApp    _)                = error "get_name failed! The argument is UApp.";

(* How to get left-hand-sides of rules from a proof context and their names? *)
(* TODO: improve it with a monad transformer for Option here. *)
fun get_left (trm:term) =
    try HOLogic.dest_Trueprop trm
>>= try HOLogic.dest_eq
>>= try fst

fun get_many (ctxt:Proof.context) (name:string) (getter:term -> term option) =
   try (Proof_Context.get_thms ctxt) name
|> these
|> map Thm.prop_of
|> map getter
|> Utils.somes;

fun get_lefts (ctxt:Proof.context) (name:string) = get_many ctxt name get_left;

(* How to check which terms in a function application are constants. *)
fun is_head_Const (Const _)  = true
 |  is_head_Const (trm1 $ _) = is_head_Const trm1
 |  is_head_Const _          = false

fun are_Consts' (acc:bool list) (trm1 $ trm2:term) = are_Consts' (is_head_Const trm2 :: acc) trm1
 |  are_Consts' (acc:bool list) (trm:term)         = is_head_Const trm :: acc;

val are_Consts = are_Consts' [];

(* type and functions about command *)
datatype command = Definition | Fun | Function | Inductive | Primrec | Unknown;

fun has_rule_with_suffix (ctxt:Proof.context) (cnst_name:string) (suffix:string) =
  can (Proof_Context.get_thms ctxt) (cnst_name ^ "." ^ suffix);

fun has_no_rule_with_suffix (ctxt:Proof.context) (cnst_name:string) (suffix:string) =
  can (Proof_Context.get_thms ctxt) (cnst_name ^ "." ^ suffix) |> not;

(*TODO*)val suffix_for_definition = (["_def"], ["cases", "elims", "induct", "simps", "intros"]);
val suffix_for_fun =       (["cases", "elims", "induct", "pelims", "simps"], ["inducts", "intros"]);(*The "fun" keyword produces psimps.*)
val suffix_for_function =  (["cases", "pelims", "psimps"], ["elims", "simps", "intros"]);
val suffix_for_primrec =   (["simps"], ["cases", "pelims", "psimps","elims", "intros"]);
val suffix_for_inductive = (["cases", "induct", "inducts", "intros", "simps"], ["pelims", "elims"]);
(*TODO*)val suffix_for_inductive_set = suffix_for_inductive;
(* Note that the "inductive_set" keyword creates "_eq" as well. But it is computationally expensive
 * to check the existence of this sort of derived lemma because we have to use regular expression.
 * Instead of this, we should check the type of this constant. *)

type suffixes = (string list * string list);

fun check_suffix (ctxt:Proof.context) (cnst_name:string) ((haves, donts): suffixes) =
 (map (has_rule_with_suffix ctxt cnst_name) haves @  (map (has_no_rule_with_suffix ctxt cnst_name) donts))
|> filter_out I
|> null;

fun get_command (trm_name:string) (ctxt:Proof.context) =
let
  val check_suffix  = check_suffix ctxt trm_name;
  val is_fun        = check_suffix suffix_for_fun;
  val is_function   = check_suffix suffix_for_function;
  val is_primrec    = check_suffix suffix_for_primrec;
  val is_inductive  = check_suffix suffix_for_inductive;
  val checks = [is_primrec, is_fun, is_function, is_inductive]: bool list;
in
  (if checks = [true,  false, false, false] then Primrec else
   if checks = [false, true,  false, false] then Fun else
   if checks = [false, false, true,  false] then Function else
   if checks = [false, false, false, true ] then Inductive else 
   Unknown)
end;

(* How to express matrix as a list of lists. *)
type 'a matrix = 'a list list;
datatype pattern =
   Full     (* Pattern-matching for this parameter is complete. *)
 | Partial  (* Pattern-matching for this parameter is not complete, but some clauses are pattern-matched. *)
 | Var      (* This parameter is a variable in all clauses. *)
 | Abstract (* This parameter is a function body of a lambda abstracted term. *)
 | Other;

fun get_elem_in_matrix (matrix: 'a matrix) (row:int, column:int) =
  let
    val the_row = try (nth matrix) row;
    fun get_column (r:'a list) = try (nth r) column;
  in
    the_row >>= get_column
  end;

(* How to check if a matrix is regular or not. *)
fun is_regular_matrix (matrix:'a matrix) =
let
  val lengs = map length matrix;
  fun are_same_ints (x::xs) = forall (curry (op =) x) xs
   |  are_same_ints []      = true (*TODO double-check*);
in
  are_same_ints lengs
end;

(* How to get nth row in a matrix. *)
fun get_nth_column (m: 'a matrix) (n:int) = map (fn mat => nth mat n) m;

(* How to transpose a matrix. *)
fun transpose ([]:'a matrix)     = NONE(*TODO: double check*)
 |  transpose ([[]]:'a matrix)   = NONE
 |  transpose (matrix:'a matrix) =
  if is_regular_matrix matrix andalso (not (length (hd matrix) = 0))
  then
    let
      val row_leng = length (hd matrix);
    in
      SOME (List.tabulate (row_leng, get_nth_column matrix))
    end
  else NONE;

(* How to classify parameters based on a parameter matrix. *)
fun classify ([]: bool matrix)     = NONE (* should it throw an exception? *)
 |  classify ([[]]: bool matrix)   = NONE
 |  classify (matrix: bool matrix) =
let
  val arg_typ_matrix = transpose matrix: bool matrix option;
  fun judge_one_row row = if forall I row then Full else if exists I row then Partial else Var; 
  val result = arg_typ_matrix <$> map judge_one_row
in
  result
end;

(* mk_parameter_matrix_for_function *)
fun mk_parameter_matrix_for_function (ctxt:Proof.context) (cname:string) =
  try (Proof_Context.get_thms ctxt) (cname ^ ".intros") |> these
|> map Thm.prop_of
|> map Logic.strip_imp_concl
|> map get_left
|> Utils.somes
|> map are_Consts;

(* mk_parameter_matrix_for_primrec *)
fun mk_parameter_matrix_for_primrec (ctxt:Proof.context) (cname:string) =
  get_lefts ctxt (cname ^ ".simps") |> map are_Consts;

(* mk_parameter_matrix_for_fun *)
fun mk_parameter_matrix_for_fun (ctxt:Proof.context) (cname:string) = mk_parameter_matrix_for_primrec ctxt cname;

(* How to produce parameter-matrix for constants defined with "induct". *)
(* Probably intros-rules are good target: focus on the conclusions.  *)
fun get_cncl (trm:term) =
    try Logic.strip_imp_concl trm
>>= try HOLogic.dest_Trueprop

(* mk_parameter_matrix_for_induct *)
fun mk_parameter_matrix_for_inductive (ctxt:Proof.context) (cname:string) =
  try (Proof_Context.get_thms ctxt) (cname ^ ".intros") |> these
|> map Thm.prop_of
|> map Logic.strip_imp_concl
|> map HOLogic.dest_Trueprop
|> map are_Consts;

(* mk_parameter_matrix *)
fun mk_parameter_matrix (ctxt:Proof.context) (cname:string) =
let
  val command = get_command cname ctxt: command;
  val result = case command of
  Primrec =>   mk_parameter_matrix_for_primrec ctxt cname
| Fun =>       mk_parameter_matrix_for_fun ctxt cname
| Function =>  mk_parameter_matrix_for_function ctxt cname
| Inductive => mk_parameter_matrix_for_inductive ctxt cname
| _ => [[(*This includes the cases where cname is not a name of a constant.*)]] (*TODO*)
in
  result
end;

fun get_left_in_concl (trm:term) =
    try Logic.strip_imp_concl trm
>>= try HOLogic.dest_Trueprop
>>= try HOLogic.dest_eq
>>= try fst;

fun get_left_in_concls (ctxt:Proof.context) (name:string) =
  get_many ctxt name get_left_in_concl;

fun mk_parameter_matrix_for_function (ctxt:Proof.context) (cname:string) =
  get_left_in_concls ctxt (cname ^ ".psimps") |> map are_Consts;

(* data-point *)
datatype utyp = UC (*UConst*) | UF (*UFree*) | UV (*UVar*) | UB (*UBound*) | UAb (*UAbs*) | UAp (*UAp*);

fun get_utyp (UConst _) = UC
 |  get_utyp (UFree  _) = UF
 |  get_utyp (UVar   _) = UV
 |  get_utyp (UBound _) = UB
 |  get_utyp (UAbs   _) = UAb
 |  get_utyp (UApp   _) = UAp;

type point =
  {name : string,
   utyp : utyp,
   level: int};

(* We should tag each ancestor with the information that says that point is the nth argument
 * of the ancestor. Why?
 * - Because we want to deal with only one task at one step. When constructing a table from a proof
 *   goal, it is already one task. We should have a separate step for checking the completeness of
 *   pattern-match.
 * - Because we are not sure if checking the completeness of pattern-match is enough or not. Knowing
 *   the location of the current point with regards to the constant name provides more information.
 *   And we can infer the information about pattern-matching from the location of the current point
 *   in terms of each constant. *)
(*For "fun p x y", "x" is the first argument and "y" is the second argument.*)
type ancestor =
  {point  : point,
   nth_arg: int};
type ancestors = ancestor list;

type datum =
  {point    : point,
   ancestors: ancestors};

type data = datum list;

fun uc_trm_to_points' (UAbs (name, _, utrm):uterm) (old_level:int) (old_data:data) (old_ancestors:ancestors) =
  let
    val new_level     = old_level + 1                                 : int;
    val new_point     = {name = name, utyp = UAb, level = new_level}  : point;
    val new_datum     = {point = new_point, ancestors = old_ancestors}: datum;
    val new_data      = new_datum :: old_data                         : data;
    (*So far, lambda abstraction takes only 1 variable.
     *TODO: probably we also apply un-currying to lambda abstraction.*)
    val new_ancestors = {point = new_point, nth_arg = 1} :: old_ancestors : ancestors;
  in
    uc_trm_to_points' utrm new_level new_data new_ancestors:data
  end
  | uc_trm_to_points' (UApp (func, args):uterm) (old_level:int) (old_data:data) (old_ancestors:ancestors) =
  let
    val new_level      = old_level + 1: int;
    val new_point      = {name = get_name func, utyp = get_utyp func, level = new_level}: point;
    val new_datum      = {point = new_point, ancestors = old_ancestors}: datum;
    val new_ancestorss = List.tabulate (length args, fn n => ({point = new_point, nth_arg = n + 1}::old_ancestors))
                       : ancestors list;
    val new_nodes = args ~~ new_ancestorss: (uterm * ancestors) list;
    val results   = map (fn (utrm:uterm, ans:ancestors) => uc_trm_to_points' utrm new_level [] ans) new_nodes;
    val result    = new_datum :: flat results @ old_data: data;
  in
    result:data
  end                                                                                                                    
  | uc_trm_to_points' (utrm:uterm) (old_level:int) (old_data:data) (old_ancestors:ancestors) =
  let
    val new_level = old_level + 1                                                    : int;
    val new_point = {name = get_name utrm, utyp = get_utyp utrm, level = new_level} : point;
    val new_datum = {point = new_point, ancestors = old_ancestors}                   : datum;
    val new_data  = new_datum :: old_data                                            : data;
  in
    new_data:data
  end;

fun uncurried_trm_to_data (utrm:uterm) = uc_trm_to_points' utrm 0 [] [];

fun get_pattern (ctxt:Proof.context) (cname:string) (nth_arg:int) =
  mk_parameter_matrix ctxt cname
|> (classify: bool matrix -> pattern list option)
>>= (fn patterns => try (nth patterns) nth_arg)
|> (fn res => Option.getOpt (res, Other));

(* data with pattern *)
type ancestor_with_pattern =
  {point  : point,
   nth_arg: int,
   pattern: pattern};
type ancestors_with_pattern = ancestor_with_pattern list;
type datum_with_pattern =
  {point    : point,
   ancestors: ancestors_with_pattern};
type data_with_pattern = datum_with_pattern list;

fun ancestor_to_ancestor_with_pattern (ctxt:Proof.context) ({point = point as {name, ...}, nth_arg = nth_arg}:ancestor) =
  let
    val pattern = get_pattern ctxt name nth_arg
  in
    {point = point, nth_arg = nth_arg, pattern = pattern}: ancestor_with_pattern
  end;

fun ancestors_to_ancestors_with_pattern (ctxt:Proof.context) (ancestors:ancestors) =
  map (ancestor_to_ancestor_with_pattern ctxt) ancestors: ancestors_with_pattern;

fun datum_to_datum_with_pattern (ctxt:Proof.context) ({point, ancestors}:datum) =
  let
    val ancestors_with_pattern = ancestors_to_ancestors_with_pattern ctxt ancestors;
  in
    {point = point, ancestors = ancestors_with_pattern}: datum_with_pattern
  end;

fun data_to_data_with_pattern (ctxt:Proof.context) (data:data) =
  map (datum_to_datum_with_pattern ctxt) data: data_with_pattern;

(*TODO*)
fun uterm_to_level (name:string) (utrm:uterm) =
  let
    val data = uncurried_trm_to_data utrm:data;
    val points = map #point data: point list;
  in
    1
  end;

fun get_innermost_const_with_fun (ctxt:Proof.context) (data:data) =
  let
    fun point_with_fun (p:point) = [];
    val consts_with_fun = [];
  in
    []
  end;

fun is_arg_of_full_pttrn_match ancestors () =();

fun is_always_argument_of_complete_pattern_matching (ctxt:Proof.context) (data:data) (name:string) =
  let
    val _ = true;
    val _ = false;
  in
    []
  end;

end;