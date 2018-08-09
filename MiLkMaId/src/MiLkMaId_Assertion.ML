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

(* test *)
@{assert} (exist_related_rsimp ["TIP_prop_01.drop"]);
@{assert} (exist_related_rsimp ["identity"] = false);

(* How to get the number of recursive functions in a term? *)
fun count_recursive_consts trm = fold_aterms (fn Const (cname, _) => (fn n =>
  if exist_related_rsimp [cname] then n + 1 else n) | _ => I) trm 0;

(* test *)
@{assert} (count_recursive_consts @{term "x (take n xs) (drop n xs) = x xs (take n xs)"} = 5);

(* Utilty functions *)
infix >>= <$>;
val _ = Option.map;
fun (m >>= f) = Option.mapPartial f m;
fun (m <$> f) = Option.map f m;

(** MILKMAID_ASSERTION **)
signature MILKMAID_ASSERTION =
sig

datatype uterm =
  UConst of string * typ |
  UFree  of string * typ |
  UVar   of indexname * typ |
  UBound of int |
  UAbs   of string * typ * uterm |
  UApp   of (uterm * uterm list);
datatype utyp = UC (*UConst*) | UF (*UFree*) | UV (*UVar*) | UB (*UBound*) | UAb (*UAbs*) | UAp (*UAp*);
datatype pattern = Full | Partial | Var;
type point =
  {cname: string,
   utyp : utyp,
   level: int};
type ancestors = (point * pattern) list;
type datum =
  {point    : point,
   ancestors: ancestors};
type data = datum list;
type 'a matrix = 'a list list;
datatype command = Definition | Fun | Function | Inductive | Other;

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

(* operations on matrix *)
val get_elem_in_matrix: 'a matrix -> int * int (*(nth column, nth row) start at 0*) -> 'a option;
val is_regular_matrix : bool matrix -> bool;
val get_nth_column    : bool matrix -> int -> bool list;
val transpose         : bool matrix -> bool list list option;
val classify          : bool matrix -> pattern list option;

(* mk_parameter_matrix *)
val mk_parameter_matrix_for_fun     : Proof.context -> string -> bool list list;
val mk_parameter_matrix_for_intros  : Proof.context -> string -> bool list list;
val mk_parameter_matrix_for_function: Proof.context -> string -> bool list list;
end;

(** MiLkMaId_Assertion  **)

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
fun get_left (_ $ (Term.Const ("HOL.eq",_) $ left $ _):term) = SOME left
 |  get_left  _                                              = NONE;

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

(* How to express matrix as a list of lists. *)
type 'a matrix = 'a list list;
datatype pattern = Full | Partial | Var;

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

(* mk_parameter_matrix_for_fun *)
fun mk_parameter_matrix_for_fun (ctxt:Proof.context) (cname:string) =
  get_lefts ctxt (cname ^ ".simps") |> map are_Consts;

(* How to produce parameter-matrix for constants defined with "induct". *)
(* Probably intros-rules are good target: focus on the conclusions.  *)
fun get_cncl (trm:term) =
    try HOLogic.dest_Trueprop trm
>>= try Logic.strip_imp_concl;

(* mk_parameter_matrix_for_induct *)
fun mk_parameter_matrix_for_intros (ctxt:Proof.context) (cname:string) =
  try (Proof_Context.get_thms ctxt) (cname ^ ".intros") |> these
|> map Thm.prop_of
|> map Logic.strip_imp_concl
|> map HOLogic.dest_Trueprop
|> map are_Consts;

(* What should I do for constants defined with "function"? psimp? pinduct? 
 \<rightarrow> The premise of psimp seems more suitable.*)

fun get_left_in_concl (trm:term) =
    try Logic.strip_imp_concl trm
>>= try HOLogic.dest_Trueprop
>>= try HOLogic.dest_eq
>>= try fst;

fun get_left_in_concls (ctxt:Proof.context) (name:string) =
  get_many ctxt name get_left_in_concl;

fun mk_parameter_matrix_for_function (ctxt:Proof.context) (cname:string) =
  get_left_in_concls ctxt (cname ^ ".psimps") |> map are_Consts;


(* How to tell if a constant is defined with the "fun"/"function"/"inductive" keyword? *)
(*
definition    \<rightarrow> _def (* no cases, no elims, no induct, no simps *)
fun           \<rightarrow> cases, elims, induct, pelims, simps (* no _def, no pinduct, no psimps *)
function      \<rightarrow> cases, pelims, pinduct, psimps (* no _def, no induct, no simps *)
inductive     \<rightarrow> cases, induct, inducts, intros, simps, \<dots> (* no _def, no pelims, no elims *)
inductive_set \<rightarrow> cases, induct, inducts, intros, simps, step_set, zero_set, _def, cases induct, \<dots>
*)

(* data-point *)
datatype utyp = UC (*UConst*) | UF (*UFree*) | UV (*UVar*) | UB (*UBound*) | UAb (*UAbs*) | UAp (*UAp*);

fun get_utyp (UConst _) = UC
 |  get_utyp (UFree  _) = UF
 |  get_utyp (UVar   _) = UV
 |  get_utyp (UBound _) = UB
 |  get_utyp (UAbs   _) = UAb
 |  get_utyp (UApp   _) = UAp;

type point =
  {cname: string,
   utyp : utyp,
   level: int};

(* TODO: ancestors should also talk about types of pattern-matching. *)
type ancestors = (point * pattern) list;

type datum =
  {point    : point,
   ancestors: ancestors};

type data = datum list;

fun uc_trm_to_points' (UAbs (name, _, utrm):uterm) (old_level:int) (old_data:data) (old_ancestors:ancestors) =
  let
    val new_level     = old_level + 1                                 : int;
    val new_point     = {cname = name, utyp = UAb, level = new_level} : point;
    val new_datum     = {point = new_point, ancestors = old_ancestors}: datum;
    val new_data      = new_datum :: old_data                         : data;
    val new_ancestors = (new_point, Full(*TODO*)) :: old_ancestors    : ancestors;
  in
    uc_trm_to_points' utrm new_level new_data new_ancestors:data
  end
  | uc_trm_to_points' (UApp (func, args):uterm) (old_level:int) (old_data:data) (old_ancestors:ancestors) =
  let
    val new_level      = old_level + 1: int;
    val new_point      = {cname = get_name func, utyp = get_utyp func, level = new_level}: point;
    val new_datum      = {point = new_point, ancestors = old_ancestors}: datum;
    val new_ancestorss = List.tabulate (length args, K ((new_point, Full(*TODO*))::old_ancestors))
                       : ancestors list;
    val xs = args ~~ new_ancestorss: (uterm * ancestors) list;
    val results = map (fn (utrm:uterm, ans:ancestors) => uc_trm_to_points' utrm new_level [] ans) xs;
    val result = new_datum :: flat results @ old_data: data;
  in
    result:data
  end                                                                                                                    
  | uc_trm_to_points' (utrm:uterm) (old_level:int) (old_data:data) (old_ancestors:ancestors) =
  let
    val new_level = old_level + 1                                                    : int;
    val new_point = {cname = get_name utrm, utyp = get_utyp utrm, level = new_level} : point;
    val new_datum = {point = new_point, ancestors = old_ancestors}                   : datum;
    val new_data  = new_datum :: old_data                                            : data;
  in
    new_data:data
  end;

fun uncurried_trm_to_data (utrm:uterm) = uc_trm_to_points' utrm 0 [] [];

datatype command = Definition | Fun | Function | Inductive | Other;

end;

structure MiLkMaId_Assertion_Test =
struct
open MiLkMaId_Assertion

(* test *)
val test_data =
 [[true, false, true, false],
  [true, false, true, false],
  [true, false, true, true ]]: bool list list;

val _ = @{assert} (get_elem_in_matrix test_data (1,3) = SOME false);
val _ = @{assert} (get_elem_in_matrix test_data (2,3) = SOME true);
val _ = @{assert} (get_elem_in_matrix test_data (3,2) = NONE);
val _ = @{assert} (get_elem_in_matrix test_data (2,3) = SOME true);

val test_data2 =
 [[true, false, true, false],
  [true, true, false],
  [true, false, true, true ]]: bool list list;

val _ = @{assert} (is_regular_matrix test_data2 = false);

(* test *)
val _ = @{assert} (get_lefts @{context} "MyTrue2_def" = []); (*TODO: This is probably wrong. Double-check. *)

val _ = @{assert} (transpose test_data = SOME
  [[true,  true,  true],
   [false, false, false],
   [true,  true,  true],
   [false, false, true]]);

val test_data3 = [[], [], [], []];

val _ = @{assert} (transpose test_data3 = NONE);
val _ = @{assert} (classify test_data  = SOME [Full, Var, Full, Partial]);
val _ = @{assert} (classify test_data2 = NONE);
val _ = @{assert} (classify test_data3 = NONE);


(*
(* How to produce parameter-matrix from a constant name. *)
(* simps, psimps, coinduction? inductive? fun function definition *)
(* We can use get_lefts and are_Consts for constants defined with "fun". *)
Proof_Context.get_thms @{context} "filter.simps";
get_lefts @{context} "filter.simps";
get_lefts @{context} "filter.simps" |> map are_Consts;

(* test *)
mk_parameter_matrix_for_fun @{context} "Assertion.filter" |> classify;
mk_parameter_matrix_for_fun @{context} "identity" |> classify;

get_many @{context} "evn.intros" get_cncl;

try (Proof_Context.get_thms @{context}) "evn.intros" |> these |> map Thm.prop_of;


(* test *)
@{assert} ((mk_parameter_matrix_for_intros @{context} "evn" |> classify)
= (SOME [Full, Full, Var]: pattern list option));


get_left_in_concls @{context} "even.psimps";
try (Proof_Context.get_thms @{context}) "even.psimps"
|> these
|> map Thm.prop_of
|> map get_left_in_concl
|> Utils.somes;

(* test *)
@{assert} 
  (mk_parameter_matrix_for_function @{context} "even" = [[true, true], [true, true]]);
@{assert}
 ((mk_parameter_matrix_for_function @{context} "even" |> classify) = SOME [Full, Full]);
@{assert}
 (mk_parameter_matrix_for_function @{context} "nubBy" = [[true, false, true], [true, false, true]]);
@{assert}
 ((mk_parameter_matrix_for_function @{context} "nubBy" |> classify) = SOME [Full, Var, Full]);

@{term "(A B (identity G)) (D (\<lambda>E. F E))"} |> uncurry;

(* test *)
@{assert} ((@{term "(A B (identity G)) (D (\<lambda>E. F E))"} |> uncurry |> uncurried_trm_to_data) =
( [{point = {cname = "A", level = 1, utyp = UF},
      ancestors = []},
   {point = {cname = "B", level = 2, utyp = UF},
      ancestors = [({cname = "A", level = 1, utyp = UF}, Full)]},
   {point = {cname = "MiLkMaId_Example.identity", level = 2, utyp = UC},
     ancestors = [({cname = "A", level = 1, utyp = UF}, Full)]},
   {point = {cname = "G", level = 3, utyp = UF},
     ancestors = [({cname = "MiLkMaId_Example.identity", level = 2, utyp = UC}, Full),
                  ({cname = "A", level = 1, utyp = UF}, Full)]},
   {point = {cname = "D", level = 2, utyp = UF},
     ancestors = [({cname = "A", level = 1, utyp = UF}, Full)]},
   {point = {cname = "F", level = 4, utyp = UF},
      ancestors = [({cname = "E", level = 3, utyp = UAb}, Full),
                   ({cname = "D", level = 2, utyp = UF},  Full),
                   ({cname = "A", level = 1, utyp = UF},  Full)]},
   {point = {cname = "0", level = 5, utyp = UB},
      ancestors = [({cname = "F", level = 4, utyp = UF},  Full),
                   ({cname = "E", level = 3, utyp = UAb}, Full),
                   ({cname = "D", level = 2, utyp = UF},  Full),
                   ({cname = "A", level = 1, utyp = UF},  Full)]},
   {point = {cname = "E", level = 3, utyp = UAb},
      ancestors = [({cname = "D", level = 2, utyp = UF}, Full),
                   ({cname = "A", level = 1, utyp = UF}, Full)]}]: data));

@{assert}
((@{term "(\<lambda>E. F E)"} |> uncurry |> uncurried_trm_to_data) =
 [{point = {cname = "F", level = 2, utyp = UF},  ancestors = [({cname = "E", level = 1, utyp = UAb}, Full)]},
  {point = {cname = "0", level = 3, utyp = UB},  ancestors = [({cname = "F", level = 2, utyp = UF},  Full),
                                                              ({cname = "E", level = 1, utyp = UAb}, Full)]},
  {point = {cname = "E", level = 1, utyp = UAb}, ancestors = []}]);


(* test *)
@{term "even n = odd (Suc n)"} |> uncurry;
@{term "even n = odd (Suc n)"} |> uncurry |> uncurried_trm_to_data;

@{assert}(
 (@{term "even n = odd (Suc n)"} |> uncurry |> uncurried_trm_to_data) =
 [{point = {cname = "HOL.eq", level = 1, utyp = UC},
   ancestors = []},
  {point = {cname = "MiLkMaId_Example.even",       level = 2, utyp = UC},
   ancestors = [({cname = "HOL.eq",                level = 1, utyp = UC}, Full)]},
  {point = {cname = "n", level = 3, utyp = UF},
   ancestors = [({cname = "MiLkMaId_Example.even", level = 2, utyp = UC}, Full),
                ({cname = "HOL.eq",                level = 1, utyp = UC}, Full)]},
  {point = {cname = "MiLkMaId_Example.odd", level = 2, utyp = UC},
   ancestors = [({cname = "HOL.eq",                level = 1, utyp = UC}, Full)]},
  {point = {cname = "Nat.Suc", level = 3, utyp = UC},
   ancestors = [({cname = "MiLkMaId_Example.odd",  level = 2, utyp = UC}, Full),
                ({cname = "HOL.eq",                level = 1, utyp = UC}, Full)]},
  {point = {cname = "n", level = 4, utyp = UF},
   ancestors = [({cname = "Nat.Suc",               level = 3, utyp = UC}, Full),
                ({cname = "MiLkMaId_Example.odd",  level = 2, utyp = UC}, Full),
                ({cname = "HOL.eq",                level = 1, utyp = UC}, Full)]}]);

(* test *)
@{term "filter (\<lambda> _. True) xs = xs"} |> uncurry;
(@{term "filter (\<lambda> _. True) xs = xs"} |> uncurry |> uncurried_trm_to_data) =
[{point = {cname = "HOL.eq", level = 1, utyp = UC},
  ancestors = []},
 {point = {cname = "MiLkMaId_Example.filter", level = 2, utyp = UC},
  ancestors = [({cname = "HOL.eq",                  level = 1, utyp = UC}, Full)]},
 {point = {cname = "HOL.True", level = 4, utyp = UC},
  ancestors = [({cname = "uu_",                     level = 3, utyp = UAb}, Full),
               ({cname = "MiLkMaId_Example.filter", level = 2, utyp = UC},  Full(*TODO: This should not be Full.*)),
               ({cname = "HOL.eq",                  level = 1, utyp = UC},  Full)]},
 {point = {cname = "uu_", level = 3, utyp = UAb},
  ancestors = [({cname = "MiLkMaId_Example.filter", level = 2, utyp = UC}, Full),
               ({cname = "HOL.eq",                  level = 1, utyp = UC}, Full)]},
 {point = {cname = "xs", level = 3, utyp = UF},
  ancestors = [({cname = "MiLkMaId_Example.filter", level = 2, utyp = UC}, Full),
               ({cname = "HOL.eq",                  level = 1, utyp = UC}, Full)]},
 {point = {cname = "xs", level = 2, utyp = UF},
  ancestors = [({cname = "HOL.eq",                  level = 1, utyp = UC}, Full)]}];


(* test *)
uncurry @{term "even 1"};
uncurry @{term "\<lambda> B. C B (\<lambda>E. F E B)"};
uncurry @{term "\<forall>x. P x y x"};
uncurry @{term "\<And>x. P x y x"};
*)

end;