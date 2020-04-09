(*  Title:      PSL/SeLFiE/src/Preprocessor/Unique_Node.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The conversion to transform term to a format more amenable to LiFtEr.
The overall work-flow is:
Proof.state            ==== pst_to_lifter_pst ================================================>                      (* in Term_Table  *)
   (Proof.state & term     ==== pst_n_trm_to_one_term ========================================>                      (* in Term_Table  *)
       (term                    ==== trm_to_trm_w_prnt =======================================>                      (* in Unique_Node *)
        trm_w_prnt              ==== trm_w_prnt_to_utrm_w_prnt ===============================>                      (* in Unique_Node *)
        utrm_w_prnt             ==== utrm_w_prnt_to_futrm_w_prnt =============================>                      (* in Unique_Node *)
        futrm_w_prnt            ==== futrm_w_prnt_to_futrm_w_prnt_n_path =====================>                      (* in Unique_Node *)
        futrm_w_prnt_n_inner_path    ==== futrm_w_prnt_to_futrm_w_prnt_n_inner_path ==========>                      (* in Unique_Node *)
        unodes                  ==== unodes_to_unode_table ===================================>                      (* in Term_Table  *)
        path_to_unode_table     ==== path_to_unode_table_to_path_to_unode_aux_table ==========>                      (* in Term_Table  *)
           (unode                    ==== unode_n_pst_to_unode_w_aux =========================> unode_w_aux          (* in Unique_Node *))
        path_to_unode_aux_table ==== path_to_unode_aux_table_to_one_term =====================>                      (* in Term_Table  *)
           (path_to_unode_aux_table  ==== path_to_unode_aux_table_to_print_to_paths_table ====> print_to_paths_table (* in Term_Table  *))
        one_term)
    one_term)
lifter_pst
*)

(*** signature UNIQUE_NODE ***)
signature UNIQUE_NODE =
sig

(** term as syntax tree **)

(* trm_w_prnt: term with print *)
datatype trm_w_prnt =  
  C_Prnt of string     * typ              * string (*Const*)
| F_Prnt of string     * typ              * string (*Free*)
| V_Prnt of indexname  * typ              * string (*Var*)
| B_Prnt of int        * typ              * string (*Bound*)
| L_Prnt of string     * typ * trm_w_prnt * string (*Abs (Lambda Abstraction)*)
| A_Prnt of trm_w_prnt * trm_w_prnt       * string;(*$   (Application)*)

(* trm_to_trm_w_prnt *)
val trm_to_trm_w_prnt: Proof.context -> term -> trm_w_prnt;

(* utrm_w_prnt: un-curried term with string *)
datatype utrm_w_prnt =
  UC_Prnt of string      * typ               * string
| UF_Prnt of string      * typ               * string
| UV_Prnt of indexname   * typ               * string
| UB_Prnt of int         * typ               * string
| UL_Prnt of string      * typ * utrm_w_prnt * string
| UA_Prnt of utrm_w_prnt * utrm_w_prnt list  * string;

(* utrms_w_prnt *)
type utrms_w_prnt = utrm_w_prnt list;

(* trm_w_prnt_to_utrm_w_prnt *)
val trm_w_prnt_to_utrm_w_prnt: trm_w_prnt -> utrm_w_prnt;

(* 
 * Isabelle's functions for Hereditary Harrop Formula, such as Drule.norm_hhf, are not helpful here:
 * Hereditary Harrop Formula still involve possibly nested applications of binary meta-implications,
 * thus introducing the un-fair depth measure among premises of meta-implications.
 * We should flatten terms after introducing uncurrying forms because flattening nested pure-implications
 * requires uncurried terms.
 *)

(* futrm_w_prnt: un-curried folded term with string *)
datatype futrm_w_prnt =
  FUC_Prnt of string       * typ                 * string
| FUF_Prnt of string       * typ                 * string
| FUV_Prnt of indexname    * typ                 * string
| FUB_Prnt of int          * typ                 * string
| FUL_Prnt of string       * typ  * futrm_w_prnt * string
| FUA_Prnt of futrm_w_prnt * futrm_w_prnt list   * string;

(* utrm_w_prnt_to_futrm_w_prnt *)
val utrm_w_prnt_to_futrm_w_prnt: utrm_w_prnt -> futrm_w_prnt;

(* path *)
type inner_path = ints;

val  inner_path_to_string        : inner_path -> string;

val are_same_inner_path: inner_path -> inner_path -> bool;

val inner_path1_is_above_inner_path2: inner_path -> inner_path -> bool;

val have_same_ancestors_only: inner_path -> inner_path -> bool;

val is_nth_arg_of: inner_path -> int -> inner_path -> bool;

(* inner_paths *)
type inner_paths = inner_path list;

(* inner_path_ord *)
val inner_path_ord: (inner_path * inner_path) -> order;

(* futrm_w_prnt_n_inner_path: un-curried folded term with string and inner_path to each node *)
datatype futrm_w_prnt_n_inner_path =
  UFC_Prnt_n_Path of (string    * typ                                           ) * string * inner_path
| UFF_Prnt_n_Path of (string    * typ                                           ) * string * inner_path
| UFV_Prnt_n_Path of (indexname * typ                                           ) * string * inner_path
| UFB_Prnt_n_Path of (int       * typ                                           ) * string * inner_path
| UFL_Prnt_n_Path of (string    * typ           * futrm_w_prnt_n_inner_path     ) * string * inner_path
| UFA_Prnt_n_Path of (futrm_w_prnt_n_inner_path * futrm_w_prnt_n_inner_path list) * string * inner_path;

(* futrm_w_prnt_to_futrm_w_prnt_n_inner_path *)
val futrm_w_prnt_to_futrm_w_prnt_n_inner_path: futrm_w_prnt -> futrm_w_prnt_n_inner_path;

(* node: un-curried folded term without string. This constitutes a part of unode (unique_node). *)
datatype node =
  NC of (string    * typ * Pattern.command) (*Const*)
| NF of (string    * typ)                   (*Free*)
| NV of (indexname * typ)                   (*Var*)
| NB of (int       * typ)                   (*Bound*)
| NL of (string    * typ)                   (*Abs (Lambda Abstraction)*)
| NA                                        (*$   (Application)*)

datatype node_typ = Node_Typ_NC | Node_Typ_NF | Node_Typ_NV | Node_Typ_NB | Node_Typ_NL | Node_Typ_NA;

val is_NC: node -> bool;
val is_NF: node -> bool;
val is_NV: node -> bool;
val is_NB: node -> bool;
val is_NL: node -> bool;
val is_NA: node -> bool;
val is_defined_by: node -> Pattern.command -> bool;

val dest_NC: node -> (string    * typ * Pattern.command) option;
val dest_NF: node -> (string    * typ) option;
val dest_NV: node -> (indexname * typ) option;
val dest_NB: node -> (int       * typ) option;
val dest_NL: node -> (string    * typ) option;

val node_to_atoms_typ: node -> typ option;

val node_typ_to_checker: node_typ -> node-> bool;

val node_to_node_typ_str: node -> string;

(* unode: unode has inner_path inside for better performance *)
type unode =
  {node       : node,
   print      : string,
   inner_path : inner_path};

val unode_to_depth: unode -> int;
val is_nth_child  : unode -> int option;

(* unodes *)
type unodes = unode list;

(* futrm_w_prnt_n_inner_path_n_ctxt_to_unodes *)
val futrm_w_prnt_n_inner_path_n_ctxt_to_unodes: futrm_w_prnt_n_inner_path -> Proof.context -> unodes;

end;

(*** structure: Unique_Node ***)
structure Unique_Node: UNIQUE_NODE  =
struct

open SeLFiE_Util;

(* trm_w_prnt: term with string *)
datatype trm_w_prnt =  
  C_Prnt of string     * typ              * string (*Const*)
| F_Prnt of string     * typ              * string (*Free*)
| V_Prnt of indexname  * typ              * string (*Var*)
| B_Prnt of int        * typ              * string (*Bound*)
| L_Prnt of string     * typ * trm_w_prnt * string (*Abs (Lambda Abstraction)*)
| A_Prnt of trm_w_prnt * trm_w_prnt       * string;(*$   (Application)*)

type trm_w_prnts = trm_w_prnt list;

(* tricky cases
 * trm_to_string @{context} (Term.Bound 3);
 * trm_to_string @{context} @{term "s (\<lambda>x. t x u)"}
 *)

(* trm_to_trm_w_prnt *)
fun trm_to_trm_w_prnt (ctxt:Proof.context) (trm:term) =
  let
    val trm_to_string' = Isabelle_Utils.trm_to_string ctxt;
    fun trm_to_trm_w_prnt' (Const _) (trm_wo_bound as Const (name,     typ)) = (C_Prnt (name,     typ, trm_to_string' trm_wo_bound))
      | trm_to_trm_w_prnt' (Free  _) (trm_wo_bound as Free  (name,     typ)) = (F_Prnt (name,     typ, trm_to_string' trm_wo_bound))
      | trm_to_trm_w_prnt' (Var   _) (trm_wo_bound as Var   (idx_name, typ)) = (V_Prnt (idx_name, typ, trm_to_string' trm_wo_bound))
      | trm_to_trm_w_prnt' (Bound i) (trm_wo_bound as Free  (_,        typ)) = (B_Prnt (i,        typ, trm_to_string' trm_wo_bound))
      | trm_to_trm_w_prnt' (Abs   _) (Abs (trip as (name, typ, subtrm))) =
        let
          (*Note that Term.dest_abs replaces the outermost (Bound i) with a free variable.*)
          val (_, abs_free_subtrm) = Term.dest_abs trip                       : (string * term);
          val print                = trm_to_string' (Abs trip)                : string;
          val subtrm_w_print       = trm_to_trm_w_prnt' subtrm abs_free_subtrm: trm_w_prnt;
        in
          L_Prnt (name, typ, subtrm_w_print, print)
        end
      | trm_to_trm_w_prnt' (orig_trm1 $ orig_trm2) (trm1_w_less_bound $ trm2_w_less_bound) =
        let
          val trm1_w_print = trm_to_trm_w_prnt' orig_trm1 trm1_w_less_bound: trm_w_prnt;
          val trm2_w_print = trm_to_trm_w_prnt' orig_trm2 trm2_w_less_bound: trm_w_prnt;
          val print        = trm_to_string' (trm1_w_less_bound $ trm2_w_less_bound);
        in
          A_Prnt (trm1_w_print, trm2_w_print, print)
        end
      | trm_to_trm_w_prnt' _ _ = error "trm_to_trm_w_print failed. Undesirable combination."
  in
    trm_to_trm_w_prnt' trm trm
  end;

(* utrm_w_prnt: un-curried term with print *)
datatype utrm_w_prnt =
  UC_Prnt of string      * typ               * string
| UF_Prnt of string      * typ               * string
| UV_Prnt of indexname   * typ               * string
| UB_Prnt of int         * typ               * string
| UL_Prnt of string      * typ * utrm_w_prnt * string
| UA_Prnt of utrm_w_prnt * utrm_w_prnt list  * string;

type utrms_w_prnt = utrm_w_prnt list;

(* trm_w_prnt_to_utrm_w_prnt *)

(*flattenflatten_trm_w_prnt' purposefully ignores the nested applications on the right-hand-side of $.*)
fun flatten_trm_w_prnt' (A_Prnt (trm1, trm2, _)) acc = flatten_trm_w_prnt' trm1 (trm2 :: acc)
 |  flatten_trm_w_prnt'  trm                     acc = trm :: acc;

fun flatten_trm_w_prnt trm = flatten_trm_w_prnt' trm [];

fun trm_w_prnt_to_utrm_w_prnt (C_Prnt  c : trm_w_prnt                 ) = UC_Prnt c
  | trm_w_prnt_to_utrm_w_prnt (F_Prnt  f                              ) = UF_Prnt f
  | trm_w_prnt_to_utrm_w_prnt (V_Prnt  v                              ) = UV_Prnt v
  | trm_w_prnt_to_utrm_w_prnt (B_Prnt  i                              ) = UB_Prnt i
  | trm_w_prnt_to_utrm_w_prnt (L_Prnt (name, typ, trm_w_prnt, prnt   )) = UL_Prnt (name, typ, trm_w_prnt_to_utrm_w_prnt trm_w_prnt, prnt)
  | trm_w_prnt_to_utrm_w_prnt (A_Prnt (trm_w_prnt1, trm_w_prnt2, prnt)) =
    let
      val trm_w_prnts = flatten_trm_w_prnt (A_Prnt (trm_w_prnt1, trm_w_prnt2, prnt)): trm_w_prnts;
    in
      UA_Prnt (trm_w_prnt_to_utrm_w_prnt (hd trm_w_prnts), map trm_w_prnt_to_utrm_w_prnt (tl trm_w_prnts), prnt)
    end: utrm_w_prnt;

(*
 * Isabelle's functions for Hereditary Harrop Formula, such as Drule.norm_hhf, are not helpful here:
 * Hereditary Harrop Formula still involve possibly nested applications of binary meta-implications,
 * thus introducing the un-fair depth measure among premises of meta-implications.
 * We should flatten terms after introducing uncurrying forms because flattening nested pure-implications
 * requires uncurried terms.
 *)
(* futrm_w_prnt: un-curried folded term with print *)
datatype futrm_w_prnt =
  FUC_Prnt of string       * typ                 * string
| FUF_Prnt of string       * typ                 * string
| FUV_Prnt of indexname    * typ                 * string
| FUB_Prnt of int          * typ                 * string
| FUL_Prnt of string       * typ  * futrm_w_prnt * string
| FUA_Prnt of futrm_w_prnt * futrm_w_prnt list   * string;

(* utrm_w_prnt_to_futrm_w_prnt *)
local

fun utrm_w_prnt_to_prnt (UC_Prnt (_, _,    print)) = print
  | utrm_w_prnt_to_prnt (UF_Prnt (_, _,    print)) = print
  | utrm_w_prnt_to_prnt (UV_Prnt (_, _,    print)) = print
  | utrm_w_prnt_to_prnt (UB_Prnt (_, _,    print)) = print
  | utrm_w_prnt_to_prnt (UL_Prnt (_, _, _, print)) = print
  | utrm_w_prnt_to_prnt (UA_Prnt (_, _,    print)) = print;

fun map_fs_xs ([]      :('a -> 'b) list) ([]       :'a list) = []
  | map_fs_xs (f::funcs:('a -> 'b) list) (arg::args:'a list) = f arg :: map_fs_xs funcs args
  | map_fs_xs  _                          _                  = error "map_fs_xs failed";

type utrms_w_prnt = utrm_w_prnt list;

fun helper (_    :string) (_:utrms_w_prnt) (UC_Prnt content) = FUC_Prnt content
 |  helper (_    :string) (_:utrms_w_prnt) (UF_Prnt content) = FUF_Prnt content
 |  helper (_    :string) (_:utrms_w_prnt) (UV_Prnt content) = FUV_Prnt content
 |  helper (_    :string) (_:utrms_w_prnt) (UB_Prnt content) = FUB_Prnt content
 |  helper (_    :string) (_:utrms_w_prnt) (UL_Prnt (name, typ, utrm_w_prnt, print)) =
      FUL_Prnt (name, typ, helper (utrm_w_prnt_to_prnt utrm_w_prnt) [] utrm_w_prnt, print)
 |  helper (imp_p: string) (acc:utrms_w_prnt) (UA_Prnt ((UC_Prnt ("Pure.imp", name, typ)), [premise, conclusion], _)) =
    let
      val one_more_imp = case conclusion of UA_Prnt (UC_Prnt ("Pure.imp", _, _), _, _) => true | _ => false;
      val result = if one_more_imp
        then helper imp_p (acc @ [premise]) conclusion
        else
          let
            val args            = acc @ [premise, conclusion] : utrm_w_prnt list;
            val prints_for_args = map utrm_w_prnt_to_prnt args: strings;
            val helpers         = map helper prints_for_args  : (utrm_w_prnt list -> utrm_w_prnt -> futrm_w_prnt) list;
            val helpers'        = Utils.map_arg [] helpers    : (utrm_w_prnt -> futrm_w_prnt) list;
            val futrm_w_prnts   = map_fs_xs helpers' args     : futrm_w_prnt list;
          in
            FUA_Prnt ((FUC_Prnt ("Pure.imp", name, typ)), futrm_w_prnts, imp_p)
          end;
    in
      result
    end
 |  helper (cnj_p: string) (acc:utrms_w_prnt) (UA_Prnt ((UC_Prnt ("Pure.conjunction", name, typ)), [left, right], _)) =
    let
      (*For the moment, I ignore nested calls of &&& on the left hand side of a &&&.
        Intuitively, ignoring such &&&s is okay because they do not really appear in practice.
        If it does occur, proof authors probably introduce such nested calls for a reason.
        So, I should not rewrite it without knowing the reason.*)
      val right_is_cnjnction = case right of UA_Prnt (UC_Prnt ("Pure.conjunction", _, _), _, _) => true | _ => false;
      val result = if right_is_cnjnction
        then helper cnj_p (acc @ [left]) right
        else
          let
            val args            = acc @ [left, right]         : utrm_w_prnt list;
            val prints_for_args = map utrm_w_prnt_to_prnt args: strings;
            val helpers         = map helper prints_for_args  : (utrm_w_prnt list -> utrm_w_prnt -> futrm_w_prnt) list;
            val helpers'        = Utils.map_arg [] helpers    : (utrm_w_prnt -> futrm_w_prnt) list;
            val futrm_w_prnts   = map_fs_xs helpers' args     : futrm_w_prnt list;
          in
            FUA_Prnt ((FUC_Prnt ("Pure.conjunction", name, typ)), futrm_w_prnts, cnj_p)
          end;
    in
      result
    end
 |  helper (_    : string) (_:utrms_w_prnt) (UA_Prnt (func, args, print)) =
      FUA_Prnt (helper print [] func, map (helper print []) args, print);

in

fun utrm_w_prnt_to_futrm_w_prnt (utrm_w_prnt) = helper (utrm_w_prnt_to_prnt utrm_w_prnt) [] utrm_w_prnt: futrm_w_prnt;

end;

(* inner_path *)

type inner_path   = ints;
fun path_to_string'  []               (acc:string) = acc
  | path_to_string' (step::path:ints) (acc:string)= path_to_string' path (acc ^ "," ^ Int.toString step);

fun inner_path_to_string  []               = ""
  | inner_path_to_string (step::path:ints) = "Path is " ^ Int.toString step ^ path_to_string' path "";

fun are_same_inner_path (inner_path1:inner_path) (inner_path2:inner_path) = forall (op =) (inner_path1 ~~ inner_path2);

fun inner_path1_is_above_inner_path2 (x::xs:inner_path) (y::ys:inner_path) = if x = y then inner_path1_is_above_inner_path2 xs ys else false
  | inner_path1_is_above_inner_path2 ([]   :inner_path) (_::_ :inner_path) = true
  | inner_path1_is_above_inner_path2   _                 _                 = false;

fun have_same_ancestors_only     []      []  = false
  | have_same_ancestors_only    [x]     [y]  = x = y
  | have_same_ancestors_only (x::xs) (y::ys) = x = y andalso have_same_ancestors_only xs ys
  | have_same_ancestors_only      _       _  = false;

fun is_nth_arg_of (inner_path1:inner_path) (n:int) (inner_path2) =
  if   have_same_ancestors_only inner_path1 inner_path2 andalso (not o null) inner_path1 andalso (not o null) inner_path2
  then Utils.last inner_path1 = 0 andalso Utils.last inner_path2 = n
  else false;

(* inner_paths *)
type inner_paths = inner_path list;

(* inner_path_ord *)
fun inner_path_ord (xs, ys) =
  let
    fun ints_compare'  []     (_::_)  EQUAL = GREATER
      | ints_compare' (_::_)   []     EQUAL = LESS
      | ints_compare' (x::xs) (y::ys) EQUAL = ints_compare' xs ys (Int.compare (x, y))
      | ints_compare'  _       _      ord   = ord;
  in
    ints_compare' xs ys EQUAL: order
  end;

(* futrm_w_prnt_n_inner_path: un-curried folded term with print and inner_path to each node*)
datatype futrm_w_prnt_n_inner_path =
  UFC_Prnt_n_Path of (string    * typ                                           ) * string * inner_path
| UFF_Prnt_n_Path of (string    * typ                                           ) * string * inner_path
| UFV_Prnt_n_Path of (indexname * typ                                           ) * string * inner_path
| UFB_Prnt_n_Path of (int       * typ                                           ) * string * inner_path
| UFL_Prnt_n_Path of (string    * typ * futrm_w_prnt_n_inner_path               ) * string * inner_path
| UFA_Prnt_n_Path of (futrm_w_prnt_n_inner_path * futrm_w_prnt_n_inner_path list) * string * inner_path;

type futrms_w_prnt_n_inner_path = futrm_w_prnt_n_inner_path list;

(* futrm_w_prnt_to_futrm_w_prnt_n_inner_path *)
local

fun helper (FUC_Prnt (name, typ,      print)) (inner_path:inner_path) = UFC_Prnt_n_Path ((name, typ), print, inner_path)
  | helper (FUF_Prnt (name, typ,      print)) (inner_path:inner_path) = UFF_Prnt_n_Path ((name, typ), print, inner_path)
  | helper (FUV_Prnt (idx,  typ,      print)) (inner_path:inner_path) = UFV_Prnt_n_Path ((idx,  typ), print, inner_path)
  | helper (FUB_Prnt (i,    typ,      print)) (inner_path:inner_path) = UFB_Prnt_n_Path ((i,    typ), print, inner_path)
  | helper (FUL_Prnt (name, typ, trm, print)) (inner_path:inner_path) =
    let
      val inner = helper trm (inner_path @ [0]);
    in
      UFL_Prnt_n_Path ((name, typ, inner), print, inner_path)
    end
  | helper (FUA_Prnt (func, args, print)) (inner_path:inner_path) =
    let
      val arg_len         = length args                                                  : int;
      val arg_numbs       = List.tabulate (arg_len, curry (op +) 1)                      : ints;
      val arg_inner_paths = map (fn numb => (inner_path @ [numb])) arg_numbs: inner_paths: inner_paths;
      val func'           = helper func (inner_path @ [0])                               : futrm_w_prnt_n_inner_path;
      val args'           = map (uncurry helper) (args ~~ arg_inner_paths)               : futrms_w_prnt_n_inner_path;
    in
      UFA_Prnt_n_Path ((func', args'), print, inner_path)
    end;

in

fun futrm_w_prnt_to_futrm_w_prnt_n_inner_path t  = helper t []

end;

(** term as Table  **)
datatype node =
  NC of (string    * typ * Pattern.command) (*Const*)
| NF of (string    * typ)                   (*Free*)
| NV of (indexname * typ)                   (*Var*)
| NB of (int       * typ)                   (*Bound*)
| NL of (string    * typ)                   (*Abs (Lambda Abstraction)*)
| NA                                        (*$   (Application)*)

datatype node_typ = Node_Typ_NC | Node_Typ_NF | Node_Typ_NV | Node_Typ_NB | Node_Typ_NL | Node_Typ_NA;

fun is_NC (NC _) = true | is_NC _ = false;
fun is_NF (NF _) = true | is_NF _ = false;
fun is_NV (NV _) = true | is_NV _ = false;
fun is_NB (NB _) = true | is_NB _ = false;
fun is_NL (NL _) = true | is_NL _ = false;
fun is_NA (NA  ) = true | is_NA _ = false;

fun is_defined_by (NC (_,_,Pattern.Definition)) Pattern.Definition = true
  | is_defined_by (NC (_,_,Pattern.Fun       )) Pattern.Fun = true
  | is_defined_by (NC (_,_,Pattern.Function  )) Pattern.Function = true
  | is_defined_by (NC (_,_,Pattern.Inductive )) Pattern.Inductive = true
  | is_defined_by (NC (_,_,Pattern.Primrec   )) Pattern.Primrec = true
  | is_defined_by (NC (_,_,Pattern.Unknown   )) Pattern.Unknown = true
  | is_defined_by _ _ = false;

fun dest_NC (NC (name, typ, cmd)) = SOME (name, typ, cmd)
  | dest_NC  _                    = NONE;
fun dest_NF (NF (name, typ     )) = SOME (name, typ)
  | dest_NF  _                    = NONE;
fun dest_NV (NV (name, typ     )) = SOME (name, typ)
  | dest_NV  _                    = NONE;
fun dest_NB (NB (int,  typ     )) = SOME (int,  typ)
  | dest_NB  _                    = NONE;
fun dest_NL (NL (name, typ     )) = SOME (name, typ)
  | dest_NL  _                    = NONE;

fun node_to_atoms_typ (NC (_, typ, _)) = SOME typ
  | node_to_atoms_typ (NF (_, typ   )) = SOME typ
  | node_to_atoms_typ (NV (_, typ   )) = SOME typ
  | node_to_atoms_typ (NB (_, typ   )) = SOME typ
  | node_to_atoms_typ  _               = NONE

fun node_typ_to_checker Node_Typ_NC = is_NC
  | node_typ_to_checker Node_Typ_NF = is_NF
  | node_typ_to_checker Node_Typ_NV = is_NV
  | node_typ_to_checker Node_Typ_NB = is_NB
  | node_typ_to_checker Node_Typ_NL = is_NL
  | node_typ_to_checker Node_Typ_NA = is_NA;

fun node_to_node_typ_str (NC _) = "NC"
  | node_to_node_typ_str (NF _) = "NF"
  | node_to_node_typ_str (NV _) = "NV"
  | node_to_node_typ_str (NB _) = "NB"
  | node_to_node_typ_str (NL _) = "NL"
  | node_to_node_typ_str  NA    = "NA";

(* unode *)
type unode =
  {node       : node,
   print      : string,
   inner_path : inner_path};

fun unode_to_depth (unode:unode) = unode |>  #inner_path |> length: int;

fun is_nth_child (unode:unode) = unode |> #inner_path |> try Utils.last: int option;

(* unodes *)
type unodes = unode list;

(* futrm_w_prnt_n_inner_path_to_unodes *)
fun futrm_w_prnt_n_inner_path_n_ctxt_to_unodes (UFC_Prnt_n_Path ((cname,typ), prnt, inner_path)) (ctxt:Proof.context) = [{node = NC (cname, typ, Pattern.get_command ctxt cname), print = prnt, inner_path = inner_path}]
  | futrm_w_prnt_n_inner_path_n_ctxt_to_unodes (UFF_Prnt_n_Path (ctnt, prnt, inner_path)) _ = [{node = NF ctnt, print = prnt, inner_path = inner_path}]
  | futrm_w_prnt_n_inner_path_n_ctxt_to_unodes (UFV_Prnt_n_Path (ctnt, prnt, inner_path)) _ = [{node = NV ctnt, print = prnt, inner_path = inner_path}]
  | futrm_w_prnt_n_inner_path_n_ctxt_to_unodes (UFB_Prnt_n_Path (ctnt, prnt, inner_path)) _ = [{node = NB ctnt, print = prnt, inner_path = inner_path}]
  | futrm_w_prnt_n_inner_path_n_ctxt_to_unodes (UFL_Prnt_n_Path ((name, typ, trm), prnt, inner_path)) ctxt =
      {node = NL (name, typ), print = prnt, inner_path = inner_path} :: futrm_w_prnt_n_inner_path_n_ctxt_to_unodes trm ctxt
  | futrm_w_prnt_n_inner_path_n_ctxt_to_unodes (UFA_Prnt_n_Path ((func, args), prnt, inner_path)) ctxt =
    {node = NA, print = prnt, inner_path = inner_path} ::
    futrm_w_prnt_n_inner_path_n_ctxt_to_unodes func ctxt @ maps (fn arg => futrm_w_prnt_n_inner_path_n_ctxt_to_unodes arg ctxt) args;

end;

structure UN = Unique_Node;