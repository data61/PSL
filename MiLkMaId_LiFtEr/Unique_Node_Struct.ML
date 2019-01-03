(*  Title:      PSL/Unique_Node_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The conversion to transform term to a format more amenable to LiFtEr.
The overall work-flow is:
  term                              === trm_w_prnt_to_utrm_w_prnt ==================> (* in this file *)
  trm_w_prnt                        === utrm_w_prnt_to_utrm_w_prnt =================> (* in this file *)
  utrm_w_prnt                       === utrm_w_prnt_to_utrm_w_prnt =================> (* in this file *)
  futrm_w_prnt                      === futrm_w_prnt_to_futrm_w_prnt_n_path ========> (* in this file *)
  futrm_w_prnt_n_path               === futrm_w_prnt_n_path_to_unique_nodes ========> (* in this file *)
  unique_nodes                      === unique_nodes_to_unique_nodes_w_auxiliary ===> (* Term_Table_Struct.ML *)
  nodes_w_auxiliary                                                                   (* Term_Table_Struct.ML *)
*)

(*** Unique_Node ***)
structure Unique_Node: UNIQUE_NODE  =
struct

(* print: the printed format of a sub-tree in the syntax tree of a term. *)
datatype print = Print of string;

(* trm_w_prnt: term with print *)
datatype trm_w_prnt =
  C_Prnt of string * typ              * print (*Const*)
| F_Prnt of string * typ              * print (*Free*)
| V_Prnt of indexname * typ           * print (*Var*)
| B_Prnt of int                       * print (*Bound*)
| L_Prnt of string * typ * trm_w_prnt * print (*Abs (Lambda Abstraction)*)
| A_Prnt of trm_w_prnt * trm_w_prnt   * print;(*$   (Application)*)

type trm_w_prnts = trm_w_prnt list;

(* tricky cases
 * trm_to_string @{context} (Term.Bound 3);
 * trm_to_string @{context} @{term "s (\<lambda>x. t x u)"}
 *)

(* trm_to_trm_w_prnt *)
fun trm_to_trm_w_prnt (ctxt:Proof.context) (trm:term) =
  let
    val trm_to_string' = Print o Isabelle_Utils.trm_to_string ctxt;
    fun trm_to_trm_w_prnt' (Const _) (trm_wo_bound as Const (name,     typ)) = (C_Prnt (name,     typ, trm_to_string' trm_wo_bound))
      | trm_to_trm_w_prnt' (Free  _) (trm_wo_bound as Free  (name,     typ)) = (F_Prnt (name,     typ, trm_to_string' trm_wo_bound))
      | trm_to_trm_w_prnt' (Var   _) (trm_wo_bound as Var   (idx_name, typ)) = (V_Prnt (idx_name, typ, trm_to_string' trm_wo_bound))
      | trm_to_trm_w_prnt' (Bound i) (trm_wo_bound as Free   _             ) = (B_Prnt (i,             trm_to_string' trm_wo_bound))
      | trm_to_trm_w_prnt' (Abs   _) (Abs (trip as (name, typ, subtrm))) =
        let
          val (_, abs_free_subtrm) = Term.dest_abs trip                       : (string * term);
          val print                = trm_to_string' (Abs trip)                : print;
          val new_subtrm           = trm_to_trm_w_prnt' subtrm abs_free_subtrm: trm_w_prnt;
        in
          L_Prnt (name, typ, new_subtrm, print)
        end
      | trm_to_trm_w_prnt' (_ $ _) (trm1 $ trm2) =
        let
          val new_trm1 = trm_to_trm_w_prnt' trm1 trm1: trm_w_prnt;
          val new_trm2 = trm_to_trm_w_prnt' trm1 trm1: trm_w_prnt;
          val print    = trm_to_string' (trm1 $ trm2);
        in
          A_Prnt (new_trm1, new_trm2, print)
        end
      | trm_to_trm_w_prnt' _ _ = error "trm_to_trm_w_print failed. Undesirable combination."
  in
    trm_to_trm_w_prnt' trm trm
  end;

(* test: trm_to_trm_w_prnt *)
fun dest_Print (Print p) = p;

fun trm_w_prnt_to_prnt (C_Prnt (_, _,     print)) = print
  | trm_w_prnt_to_prnt (F_Prnt (_, _,     print)) = print
  | trm_w_prnt_to_prnt (V_Prnt (_, _,     print)) = print
  | trm_w_prnt_to_prnt (B_Prnt (_,        print)) = print
  | trm_w_prnt_to_prnt (L_Prnt (_, _ , _, print)) = print
  | trm_w_prnt_to_prnt (A_Prnt (_, _ ,    print)) = print;

val _ = @{assert} ("s (\<lambda>x. f x y)" = (@{term "s (\<lambda>x. f x y)"} |> trm_to_trm_w_prnt @{context} |> trm_w_prnt_to_prnt |> dest_Print));

(* utrm_w_prnt: un-curried term with print *)
datatype utrm_w_prnt =
  UC_Prnt of string * typ                   * print
| UF_Prnt of string * typ                   * print
| UV_Prnt of indexname * typ                * print
| UB_Prnt of int                            * print
| UL_Prnt of string * typ * utrm_w_prnt     * print
| UA_Prnt of utrm_w_prnt * utrm_w_prnt list * print;

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

(* futrm_w_prnt: un-curried flattened term with print *)
datatype futrm_w_prnt =
  FUC_Prnt of string * typ                     * print
| FUF_Prnt of string * typ                     * print
| FUV_Prnt of indexname * typ                  * print
| FUB_Prnt of int                              * print
| FUL_Prnt of string * typ * futrm_w_prnt      * print
| FUA_Prnt of futrm_w_prnt * futrm_w_prnt list * print;

(* utrm_w_prnt_to_utrm_w_prnt *)
val utrm_w_prnt_to_futrm_w_prnt = undefined: utrm_w_prnt -> futrm_w_prnt;

(* path *)
datatype path  = Path of ints;

(* paths *)
type     paths = path list;

(* path_ord *)
val path_ord = undefined: (path * path) -> order;

(* futrm_w_prnt_n_path: un-curried flattened term with print and path to each node*)
datatype futrm_w_prnt_n_path =
  UFC_Prnt_n_Path of (string * typ                             ) * print * path
| UFF_Prnt_n_Path of (string * typ                             ) * print * path
| UFV_Prnt_n_Path of (indexname * typ                          ) * print * path
| UFB_Prnt_n_Path of  int                                        * print * path
| UFL_Prnt_n_Path of (string * typ * futrm_w_prnt_n_path       ) * print * path
| UFA_Prnt_n_Path of (futrm_w_prnt_n_path * futrm_w_prnt_n_path) * print * path;

(* futrm_w_prnt_to_futrm_w_prnt_n_path *)
val futrm_w_prnt_to_futrm_w_prnt_n_path = undefined: futrm_w_prnt -> futrm_w_prnt_n_path;

(** term as Table  **)
datatype node =
  NC of (string * typ)    (*Const*)
| NF of (string * typ)    (*Free*)
| NV of (indexname * typ) (*Var*)
| NB of  int              (*Bound*)
| NL of (string * typ)    (*Abs (Lambda Abstraction)*)
| NA                      (*$   (Application)*)

(* unique_node *)
type unique_node =
  {node : node,
   print: print,
   path : path};

(* unique_nodes *)
type unique_nodes = unique_node list;

(* futrm_w_prnt_n_path_to_unique_nodes *)
val futrm_w_prnt_n_path_to_unique_nodes = undefined: futrm_w_prnt_n_path -> unique_nodes;

end;