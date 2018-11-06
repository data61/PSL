(*  Title:      MiLkMaId/MiLkMaId_Util.ML
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
fun exist_related_rsimp (_   :Proof.context)  []             = false
 |  exist_related_rsimp (ctxt:Proof.context) (cname::cnames) =
     (check_thm_list (Proof_Context.get_thms ctxt (cname^".simps")) cname handle ERROR _ =>
      exist_related_rsimp ctxt cnames);
fun has_related_rsimp (ctxt:Proof.context) (Const (c, _)) = exist_related_rsimp ctxt [c]
 |  has_related_rsimp (_:Proof.context)     _             = false;
(* How to get the number of recursive functions in a term? *)
fun count_recursive_consts (ctxt:Proof.context) trm = fold_aterms (fn Const (cname, _) => (fn n =>
  if exist_related_rsimp ctxt [cname] then n + 1 else n) | _ => I) trm 0;

(* Utilty functions *)
infix 1 >>= <$> <|>;
val _ = Option.map;
fun (m >>= f) = Option.mapPartial f m;
fun (m <$> f) = Option.map f m;
fun (NONE   <|> NONE  ) = NONE
  | (NONE   <|> SOME x) = SOME x
  | (SOME x <|> NONE  ) = SOME x
  | (SOME x <|> SOME _) = SOME x

(** MILKMAID_TABLE **)
(*MILKMAID_TABLE exposes many functions that are not meant to be used by other users
 *because unit tests using @{assert} in MiLkMaId_Test.thy require them to be accessible.*)
signature MILKMAID_TABLE =
sig

(* uterm and utyp *)
datatype uterm =
  UConst of string * typ |
  UFree  of string * typ |
  UVar   of indexname * typ |
  UBound of int |
  UAbs   of string * typ * uterm |(*TODO: maybe we also apply un-currying to lambda abstraction.*)
  UApp   of (uterm * uterm list);
datatype utyp = UC (*UConst*) | UF (*UFree*) | UV (*UVar*) | UB (*UBound*) | UAb (*UAbs*) | UAp (*UAp*);

(* data *)
type point =
  {name : string,
   utyp : utyp,
   level: int(*The level of the root is 1.*)};
type ancestor =
  {point  : point,
   nth_arg: int};
type ancestors  = ancestor list;
type datum =
  {point    : point,
   ancestors: ancestors};
type data = datum list;

(* data_with_pattern *)
datatype pattern = Full | Partial | Var | Abstract | Other;
type patterns = pattern list;
type ancestor_with_pattern =
  {point  : point,
   nth_arg: int,
   pattern: pattern};
type ancestors_with_pattern = ancestor_with_pattern list;
type datum_with_pattern =
  {point    : point,
   ancestors: ancestors_with_pattern};
type data_with_pattern = datum_with_pattern list;

(* kind *)
(* note that kind here is the pair of the command name used to define each constant and a tag
   that indicates if the constant is defined recursively or not. *)
datatype command = Definition | Fun | Function | Inductive | Primrec | Unknown;
type recursive   = bool option;

(* data_with_pattern_and_kind *)
type point_w_kind =
  {name : string,
   utyp : utyp,
   level: int(*The level of the root is 1.*),
   cmmnd: command,
   rcrsv: recursive};
type ancestor_w_pattern_n_kind =
  {point  : point_w_kind,
   nth_arg: int,
   pattern: pattern};
type ancestors_w_pattern_n_kind = ancestor_w_pattern_n_kind list;
type datum_w_pattern_n_kind =
  {point    : point_w_kind,
   ancestors: ancestors_w_pattern_n_kind};
type data_w_pattern_n_kind = datum_w_pattern_n_kind list;

(* matrix *)
type 'a matrix = 'a list list;

val datum_to_level             : datum -> int;
val filter_data                : (datum -> bool) -> data -> data;
val filter_data_with_point_name: data -> string -> data;
val filter_data_wo_point_name  : data -> string -> data;

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
val map_types'    : (typ -> typ) -> uterm -> uterm;
val trm_to_utrm   : term -> uterm;
val utrm_to_trm   : uterm -> term;
val get_name      : uterm -> string;
val utrm_to_data  : uterm -> data;

(* operations on matrix *)
val get_elem_in_matrix: 'a matrix -> int * int (*(nth column, nth row) start at 0*) -> 'a option;
val is_regular_matrix : bool matrix -> bool;
val get_nth_column    : bool matrix -> int -> bool list;
val transpose         : bool matrix -> bool matrix option;
val classify          : bool matrix -> patterns option;

(* mk_parameter_matrix *)
val mk_parameter_matrix_for_primrec   : Proof.context -> string -> bool matrix;
val mk_parameter_matrix_for_fun       : Proof.context -> string -> bool matrix;
val mk_parameter_matrix_for_function  : Proof.context -> string -> bool matrix;
val mk_parameter_matrix_for_inductive : Proof.context -> string -> bool matrix;
val mk_parameter_matrix               : Proof.context -> string -> bool matrix;

(* operations about pattern and kind *)
val get_nth_pattern                           : Proof.context -> string -> int -> pattern;
val get_patterns                              : Proof.context -> string -> patterns option;
val data_to_data_with_pattern                 : Proof.context -> data -> data_with_pattern;
val data_with_pattern_to_data_w_pattern_n_kind: Proof.context -> data_with_pattern -> data_w_pattern_n_kind;

(* utility functions for assertions *)
type ufun_n_args = {level: int(*The level of the root is 1.*),
                    ufun : uterm,
                    uargs: uterm list};
type ufun_n_argss = ufun_n_args list;
val utrm_to_ufun_n_argss                                    : uterm -> ufun_n_argss;
val utrm_to_innermost_ufun_n_argss                          : uterm -> ufun_n_argss;(*Be aware of possible encounter with nested applications of \<Longrightarrow>*)
val ufun_n_argss_to_ufun_defined_w_fun_command_n_argss      : Proof.context -> ufun_n_argss -> ufun_n_argss;
val ufun_n_argss_to_ufun_defined_w_inductive_command_n_argss: Proof.context -> ufun_n_argss -> ufun_n_argss;
val ufun_n_argss_to_ufun_w_induct_rule_n_argss              : Proof.context -> ufun_n_argss -> ufun_n_argss;
val ufun_n_argss_to_var_namess                              : ufun_n_argss -> strings list;
val ufun_n_argss_to_cname_n_vnames_pairs                    : ufun_n_argss -> (string option * strings) list;
val ufun_n_args_to_vnames_only_full                         : Proof.context -> ufun_n_args -> strings;

end;

(** MiLkMaId_Table **)
structure MiLkMaId_Table : MILKMAID_TABLE =
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
fun trm_to_utrm (Const c) = UConst c
  | trm_to_utrm (Free f)  = UFree f
  | trm_to_utrm (Var v)   = UVar v
  | trm_to_utrm (Bound i) = UBound i
  | trm_to_utrm (Abs (name, typ, trm)) = UAbs (name, typ, trm_to_utrm trm)
  | trm_to_utrm (trm1 $ trm2) =
    let
      val xs = flatten (trm1 $ trm2) [];
    in
      UApp (trm_to_utrm (hd xs), map trm_to_utrm (tl xs))
    end;

(* curry: necessary to produce string representations for sub-terms. *)
fun utrm_to_trm (UConst c) = Const c
  | utrm_to_trm (UFree f)  = Free f
  | utrm_to_trm (UVar v)   = Var v
  | utrm_to_trm (UBound i) = Bound i
  | utrm_to_trm (UAbs (name, typ, utrm)) = Abs (name, typ, utrm_to_trm utrm)
  | utrm_to_trm (UApp (_, [])) = error "utrm_to_trm failed at UApp (utrm, [])"
  | utrm_to_trm (UApp (utrm, [uarg])) = utrm_to_trm utrm $ utrm_to_trm uarg
  | utrm_to_trm (UApp (utrm, uargs)) =
    let
      val init_uargs = Utils.init uargs: uterm list;
      val last_uarg  = Utils.last uargs: uterm;
    in
      utrm_to_trm (UApp (utrm, init_uargs)) $ utrm_to_trm last_uarg
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
type patterns = pattern list;

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
|> (fn these_list => (length these_list |> Int.toString |> tracing; these_list))
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
    val new_point      = {name = get_name func, utyp = UAp, level = new_level}: point;
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
    val new_level = old_level + 1                                                  : int;
    val new_point = {name = get_name utrm, utyp = get_utyp utrm, level = new_level}: point;
    val new_datum = {point = new_point, ancestors = old_ancestors}                 : datum;
    val new_data  = new_datum :: old_data                                          : data;
  in
    new_data:data
  end;

fun utrm_to_data (utrm:uterm) = uc_trm_to_points' utrm 0 [] [];

fun get_patterns (ctxt:Proof.context) (cname:string): patterns option =
  let
    val pmatrix  = mk_parameter_matrix ctxt cname: bool matrix;
    val patterns = classify pmatrix              : patterns option;
  in
    patterns
  end;

fun get_nth_pattern (ctxt:Proof.context) (cname:string) (nth_arg:int) =
  get_patterns ctxt cname
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

fun datum_to_level ({point,...}:datum) = #level point        : int;
fun filter_data (f:datum -> bool) (data:data) = filter f data: data;
fun filter_data_with_point_name (data:data) (pname:string) =
  filter_data (fn {point,...} => #name point = pname) data   : data;
fun filter_data_wo_point_name (data:data) (pname:string) =
  filter_out (fn {point,...} => #name point = pname) data    : data;

fun ancestor_to_ancestor_with_pattern (ctxt:Proof.context) ({point = point as {name, ...}, nth_arg = nth_arg}:ancestor) =
  let
    val pattern = get_nth_pattern ctxt name nth_arg
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

type recursive   = bool option;

type point_w_kind =
  {name : string,
   utyp : utyp,
   level: int(*The level of the root is 1.*),
   cmmnd: command,
   rcrsv: recursive};
type ancestor_w_pattern_n_kind =
  {point  : point_w_kind,
   nth_arg: int,
   pattern: pattern};
type ancestors_w_pattern_n_kind = ancestor_w_pattern_n_kind list;
type datum_w_pattern_n_kind =
  {point    : point_w_kind,
   ancestors: ancestors_w_pattern_n_kind};
type data_w_pattern_n_kind = datum_w_pattern_n_kind list;

fun point_to_point_w_kind ({name, utyp, level}:point) =
  {name = name, utyp = utyp, level = level, cmmnd = Unknown, rcrsv = NONE};(*TODO*)

fun ancestor_w_pattern_to_ancestor_w_pattern_n_kind (ctxt:Proof.context) ({point = point, nth_arg = nth_arg, pattern = pattern}:ancestor_with_pattern) =
  let
    val point_w_kind = point_to_point_w_kind point: point_w_kind;
  in
    {point = point_w_kind, nth_arg = nth_arg, pattern = pattern}: ancestor_w_pattern_n_kind
  end;

fun ancestors_with_pattern_to_ancestors_w_pattern_n_kind (ctxt:Proof.context) (ancestors_w_pattern:ancestors_with_pattern) =
  map (ancestor_w_pattern_to_ancestor_w_pattern_n_kind ctxt) ancestors_w_pattern: ancestors_w_pattern_n_kind;

fun datum_with_pattern_to_datum_w_pattern_n_kind (ctxt:Proof.context) ({point, ancestors}:datum_with_pattern) =
  let
    val ancestors_w_pattern_n_kind = ancestors_with_pattern_to_ancestors_w_pattern_n_kind ctxt ancestors: ancestors_w_pattern_n_kind;
    val {name, utyp, level}        = point                                                              : point;
    val command                    = get_command name ctxt                                              : command;
    val resursive                  = if command = Definition orelse command = Unknown
                                     then NONE else SOME (exist_related_rsimp ctxt [name])              : bool option;
    val point_w_kind               = {name = name, utyp = utyp, level = level, cmmnd = command, rcrsv = resursive}: point_w_kind;
  in
    {point = point_w_kind, ancestors = ancestors_w_pattern_n_kind}: datum_w_pattern_n_kind
  end;

fun data_with_pattern_to_data_w_pattern_n_kind (ctxt:Proof.context) (data:data_with_pattern) =
  map (datum_with_pattern_to_datum_w_pattern_n_kind ctxt) data: data_w_pattern_n_kind;

type ufun_n_args = {
  level: int(*The level of the root is 1.*),
  ufun:  uterm,
  uargs: uterm list};
type ufun_n_argss = ufun_n_args list;

fun get_max_level xs = fold (fn x:ufun_n_args => fn acc:int =>
  if #level x > acc then #level x else acc) xs 0;

fun get_cons_n_argss_of_level (level:int) (xs:ufun_n_argss) = fold (fn x:ufun_n_args => fn acc:ufun_n_argss =>
  if #level x = level then x::acc else acc) xs [];

fun eq_args (trip1:ufun_n_args, trip2:ufun_n_args) : bool =
  let
    val uargs1 = #uargs trip1: uterm list;
    val uargs2 = #uargs trip2: uterm list;
  in
    uargs1 = uargs2
  end;

(*utrm_to_ufun_n_argss produces the pairs of function and arguments.*)
fun utrm_to_ufun_n_argss (utrm:uterm) =
  let
    fun tail_rec (acc:ufun_n_argss) (level:int) (UAbs (_, _, utrm):uterm) =
        tail_rec (acc:ufun_n_argss) (level + 1)  utrm
      | tail_rec (acc:ufun_n_argss) (level:int) (UApp (UConst body, uargs):uterm) =
        let
          (*The computation of all requires a large memory.*)
          val mapped  = tail_rec [{level = level, ufun = UConst body, uargs = uargs}] (level + 1): uterm -> ufun_n_args list;
          val all     = flat (map mapped uargs) @ acc                                            : ufun_n_argss;
          val wo_dups = distinct eq_args all                                                     : ufun_n_argss;
        in
          wo_dups
        end
      | tail_rec (acc:ufun_n_argss) _ _ = acc: ufun_n_argss
  in
    tail_rec [] 1 utrm
  end;

(*utrm_to_innermost_ufun_n_argss produces the pairs of function and arguments on the lowest level of the given syntax tree.*)
fun utrm_to_innermost_ufun_n_argss (utrm:uterm) =
  let
    fun tail_rec (acc:ufun_n_argss) (level:int) (UAbs (_, _, utrm):uterm) =
        tail_rec (acc:ufun_n_argss) (level + 1)  utrm
      | tail_rec (acc:ufun_n_argss) (level:int) (UApp (UConst body, uargs):uterm) =
        let
          (*The computation of all requires a large memory.*)
          val mapped        = tail_rec [{level = level, ufun = UConst body, uargs = uargs}] (level + 1): uterm -> ufun_n_argss;
          val all           = map mapped uargs |> flat                                                 : ufun_n_argss;
          val deepest_level = get_max_level all                                                        : int;
          val deepests      = get_cons_n_argss_of_level deepest_level all                              : ufun_n_argss
          val result        = if null deepests then acc else deepests                                  : ufun_n_argss;
        in
          distinct eq_args result: ufun_n_argss
        end
      | tail_rec (acc:ufun_n_argss) _ _ = acc: ufun_n_argss
  in
    tail_rec [] 1 utrm
  end;

fun ufun_n_argss_to_ufun_defined_w_certain_command_n_argss  (ctxt:Proof.context) (pairs:ufun_n_args list) (cmmd:command) =
  filter (fn {ufun, ...} => case ufun of
    UConst (cname, _) => get_command cname ctxt = cmmd
  | _                 => false) pairs;

fun ufun_n_argss_to_ufun_defined_w_fun_command_n_argss (ctxt:Proof.context) (pairs:ufun_n_args list) =
  ufun_n_argss_to_ufun_defined_w_certain_command_n_argss ctxt pairs Fun;

fun ufun_n_argss_to_ufun_defined_w_inductive_command_n_argss (ctxt:Proof.context) (pairs:ufun_n_args list) =
  ufun_n_argss_to_ufun_defined_w_certain_command_n_argss ctxt pairs Inductive;

fun ufun_n_argss_to_ufun_w_induct_rule_n_argss (ctxt:Proof.context) (pairs:ufun_n_args list) =
 (ufun_n_argss_to_ufun_defined_w_certain_command_n_argss ctxt pairs Fun @
  ufun_n_argss_to_ufun_defined_w_certain_command_n_argss ctxt pairs Inductive)
|> distinct (op =);

fun ufun_n_args_to_cname_n_vnames ({ufun, uargs,...}:ufun_n_args) =
  ((fn UConst (name, _) => SOME name | _ => NONE) ufun,
   map (fn UFree (name, _) => [name] | _ => []) uargs |> flat: strings): (string option * strings);

fun ufun_n_argss_to_var_namess (pairs:ufun_n_argss) = map (snd o ufun_n_args_to_cname_n_vnames) pairs
  : strings list;

fun ufun_n_argss_to_cname_n_vnames_pairs (pairs:ufun_n_argss) = map ufun_n_args_to_cname_n_vnames pairs
  : (string option * strings) list;

fun is_Full (Full:pattern) = true
  | is_Full  _             = false;

fun is_Fulls (patterns:patterns) = drop 1 patterns |> map is_Full: bool list;

fun is_not_Fulls (patterns: patterns) = is_Fulls patterns |> map not: bool list;

fun thin_out (xs:'a list) (bs:bool list) = bs ~~ xs |> filter_out fst |> map snd;

fun ufun_n_args_to_vnames_only_full (ctxt:Proof.context) ({ufun, uargs, level}:ufun_n_args) =
  let
    val cname_ufun = case ufun of
        UConst (cname, _) => SOME cname
      | _                 => NONE                                 : string option;
    val patterns       = cname_ufun >>= get_patterns ctxt         : patterns option;
    val not_fulls      = patterns <$> is_not_Fulls                : bool list option;
    (*TODO: why does thin_out fail sometimes?*)
    val full_args      = (*not_full_args*)not_fulls  >>= try (thin_out uargs) |> these(*uargs*): uterm list;
    val vnames_of_full = ufun_n_args_to_cname_n_vnames {ufun=ufun, uargs=full_args, level=level} |> snd: strings;
  in
    vnames_of_full: strings
  end;

end;