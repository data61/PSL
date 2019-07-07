(*  Title:      PSL/LiFtEr/src/Unique_Node_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The conversion to transform term to a format more amenable to LiFtEr.
The overall work-flow is:
Proof.state            ==== pst_to_lifter_pst ================================================>                      (* in Term_Table *)
   (Proof.state & term     ==== pst_n_trm_to_one_term ========================================>                      (* in Term_Table *)
       (term                    ==== trm_to_trm_w_prnt =======================================>                      (* in Unique_Node *)
        trm_w_prnt              ==== trm_w_prnt_to_utrm_w_prnt ===============================>                      (* in Unique_Node *)
        utrm_w_prnt             ==== utrm_w_prnt_to_futrm_w_prnt =============================>                      (* in Unique_Node *)
        futrm_w_prnt            ==== futrm_w_prnt_to_futrm_w_prnt_n_path =====================>                      (* in Unique_Node *)
        futrm_w_prnt_n_path     ==== futrm_w_prnt_n_path_to_unodes ===========================>                      (* in Unique_Node *)
        unodes                  ==== unodes_to_unode_table ===================================>                      (* in Term_Table  *)
        path_to_unode_table     ==== path_to_unode_table_to_path_to_unode_aux_table ==========>                      (* in Term_Table  *)
           (unode                    ==== unode_n_pst_to_unode_w_aux =========================> unode_w_aux          (* in Unique_Node *))
        path_to_unode_aux_table ==== path_to_unode_aux_table_to_one_term =====================>                      (* in Term_Table  *)
           (path_to_unode_aux_table  ==== path_to_unode_aux_table_to_print_to_paths_table ====> print_to_paths_table (* in Term_Table  *))
        one_term)
    one_term)
lifter_pst
*)

(*** Unique_Node ***)
structure Unique_Node: UNIQUE_NODE  =
struct

(* print: the printed format of a sub-tree in the syntax tree of a term. *)
type print = LiFtEr_Util.print;
open LiFtEr_Util;

(* dest_print *)
fun dest_Print (Print str) = str;

fun is_subprint_of (Print p1) (Print p2) = String.isSubstring p1 p2;

fun same_prints    (Print p1) (Print p2) = p1 = p2;

(* trm_w_prnt: term with print *)
datatype trm_w_prnt =  
  C_Prnt of string     * typ              * print (*Const*)
| F_Prnt of string     * typ              * print (*Free*)
| V_Prnt of indexname  * typ              * print (*Var*)
| B_Prnt of int        * typ              * print (*Bound*)
| L_Prnt of string     * typ * trm_w_prnt * print (*Abs (Lambda Abstraction)*)
| A_Prnt of trm_w_prnt * trm_w_prnt       * print;(*$   (Application)*)

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
      | trm_to_trm_w_prnt' (Bound i) (trm_wo_bound as Free  (_,        typ)) = (B_Prnt (i,        typ, trm_to_string' trm_wo_bound))
      | trm_to_trm_w_prnt' (Abs   _) (Abs (trip as (name, typ, subtrm))) =
        let
          (*Note that Term.dest_abs replaces the outermost (Bound i) with a free variable.*)
          val (_, abs_free_subtrm) = Term.dest_abs trip                       : (string * term);
          val print                = trm_to_string' (Abs trip)                : print;
          val subtrm_w_print       = trm_to_trm_w_prnt' subtrm abs_free_subtrm: trm_w_prnt;
        in
          L_Prnt (name, typ, subtrm_w_print, print)
        end
      | trm_to_trm_w_prnt' (orig_trm1 $ orig_trm2) (trm1_w_less_bound $ trm2_w_less_bound) =
        let
          val trm1_w_print = trm_to_trm_w_prnt' orig_trm1 trm1_w_less_bound: trm_w_prnt;
          val trm2_w_print = trm_to_trm_w_prnt' orig_trm2 trm2_w_less_bound: trm_w_prnt;
          val print    = trm_to_string' (trm1_w_less_bound $ trm2_w_less_bound);
        in
          A_Prnt (trm1_w_print, trm2_w_print, print)
        end
      | trm_to_trm_w_prnt' _ _ = error "trm_to_trm_w_print failed. Undesirable combination."
  in
    trm_to_trm_w_prnt' trm trm
  end;

(* utrm_w_prnt: un-curried term with print *)
datatype utrm_w_prnt =
  UC_Prnt of string      * typ               * print
| UF_Prnt of string      * typ               * print
| UV_Prnt of indexname   * typ               * print
| UB_Prnt of int         * typ               * print
| UL_Prnt of string      * typ * utrm_w_prnt * print
| UA_Prnt of utrm_w_prnt * utrm_w_prnt list  * print;

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
  FUC_Prnt of string       * typ                 * print
| FUF_Prnt of string       * typ                 * print
| FUV_Prnt of indexname    * typ                 * print
| FUB_Prnt of int          * typ                 * print
| FUL_Prnt of string       * typ  * futrm_w_prnt * print
| FUA_Prnt of futrm_w_prnt * futrm_w_prnt list   * print;

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

fun helper (_    : print) (_:utrms_w_prnt) (UC_Prnt content) = FUC_Prnt content
 |  helper (_    : print) (_:utrms_w_prnt) (UF_Prnt content) = FUF_Prnt content
 |  helper (_    : print) (_:utrms_w_prnt) (UV_Prnt content) = FUV_Prnt content
 |  helper (_    : print) (_:utrms_w_prnt) (UB_Prnt content) = FUB_Prnt content
 |  helper (_    : print) (_:utrms_w_prnt) (UL_Prnt (name, typ, utrm_w_prnt, print)) =
      FUL_Prnt (name, typ, helper (utrm_w_prnt_to_prnt utrm_w_prnt) [] utrm_w_prnt, print)
 |  helper (imp_p: print) (acc:utrms_w_prnt) (UA_Prnt ((UC_Prnt ("Pure.imp", name, typ)), [premise, conclusion], _)) =
    let
      val one_more_imp = case conclusion of UA_Prnt (UC_Prnt ("Pure.imp", _, _), _, _) => true | _ => false;
      val result = if one_more_imp
        then helper imp_p (acc @ [premise]) conclusion
        else
          let
            val args            = acc @ [premise, conclusion] : utrm_w_prnt list;
            val prints_for_args = map utrm_w_prnt_to_prnt args: print list;
            val helpers         = map helper prints_for_args  : (utrm_w_prnt list -> utrm_w_prnt -> futrm_w_prnt) list;
            val helpers'        = Utils.map_arg [] helpers    : (utrm_w_prnt -> futrm_w_prnt) list;
            val futrm_w_prnts   = map_fs_xs helpers' args     : futrm_w_prnt list;
          in
            FUA_Prnt ((FUC_Prnt ("Pure.imp", name, typ)), futrm_w_prnts, imp_p)
          end;
    in
      result
    end
 |  helper (cnj_p: print) (acc:utrms_w_prnt) (UA_Prnt ((UC_Prnt ("Pure.conjunction", name, typ)), [left, right], _)) =
    let
      (*TODO: double-check if we should ignore recursive calls of &&& on the left hand side of a &&&.
              Intuitively, ignoring such &&&s is okay because they do not really appear in practice.*)
      (*If I should flatten nexted &&&s on the left hand side of a &&&, I should do so before applying trm_to_trm_w_prnt*)
      val right_is_cnjnction = case right of UA_Prnt (UC_Prnt ("Pure.conjunction", _, _), _, _) => true | _ => false;
      val result = if right_is_cnjnction
        then helper cnj_p (acc @ [left]) right
        else
          let
            val args            = acc @ [left, right]         : utrm_w_prnt list;
            val prints_for_args = map utrm_w_prnt_to_prnt args: print list;
            val helpers         = map helper prints_for_args  : (utrm_w_prnt list -> utrm_w_prnt -> futrm_w_prnt) list;
            val helpers'        = Utils.map_arg [] helpers    : (utrm_w_prnt -> futrm_w_prnt) list;
            val futrm_w_prnts   = map_fs_xs helpers' args     : futrm_w_prnt list;
          in
            FUA_Prnt ((FUC_Prnt ("Pure.conjunction", name, typ)), futrm_w_prnts, cnj_p)
          end;
    in
      result
    end
 |  helper (_    : print) (_:utrms_w_prnt) (UA_Prnt (func, args, print)) =
      FUA_Prnt (helper print [] func, map (helper print []) args, print);

in

fun utrm_w_prnt_to_futrm_w_prnt (utrm_w_prnt) = helper (utrm_w_prnt_to_prnt utrm_w_prnt) [] utrm_w_prnt: futrm_w_prnt;

end;

(* path *)
type path  = LiFtEr_Util.path;

fun are_same_path (path1:path) (path2:path) = forall (op =) (path1 ~~ path2);

fun path1_is_above_path2 (x::xs:path) (y::ys:path) = if x = y then path1_is_above_path2 xs ys else false
  | path1_is_above_path2 ([]   :path) (_::_ :path) = true
  | path1_is_above_path2  _            _           = false;

(* paths *)
type paths = path list;

(* path_ord *)(*TODO*)
fun path_ord (xs, ys) =
  let
    fun ints_compare'  []     (_::_)  EQUAL = GREATER
      | ints_compare' (_::_)   []     EQUAL = LESS
      | ints_compare' (x::xs) (y::ys) EQUAL = ints_compare' xs ys (Int.compare (x, y))
      | ints_compare'  _       _      ord   = ord;
  in
    ints_compare' xs ys EQUAL: order
  end;

(* futrm_w_prnt_n_path: un-curried folded term with print and path to each node*)
datatype futrm_w_prnt_n_path =
  UFC_Prnt_n_Path of (string    * typ                               ) * print * path
| UFF_Prnt_n_Path of (string    * typ                               ) * print * path
| UFV_Prnt_n_Path of (indexname * typ                               ) * print * path
| UFB_Prnt_n_Path of (int       * typ                               ) * print * path
| UFL_Prnt_n_Path of (string    * typ * futrm_w_prnt_n_path         ) * print * path
| UFA_Prnt_n_Path of (futrm_w_prnt_n_path * futrm_w_prnt_n_path list) * print * path;

type futrms_w_prnt_n_path = futrm_w_prnt_n_path list;

(* futrm_w_prnt_to_futrm_w_prnt_n_path *)
local

fun helper (FUC_Prnt (name, typ,      print)) (path:path) = UFC_Prnt_n_Path ((name, typ), print, path)
  | helper (FUF_Prnt (name, typ,      print)) (path:path) = UFF_Prnt_n_Path ((name, typ), print, path)
  | helper (FUV_Prnt (idx,  typ,      print)) (path:path) = UFV_Prnt_n_Path ((idx,  typ), print, path)
  | helper (FUB_Prnt (i,    typ,      print)) (path:path) = UFB_Prnt_n_Path ((i,    typ), print, path)
  | helper (FUL_Prnt (name, typ, trm, print)) (path:path) =
    let
      val inner = helper trm (path @ [0]);
    in
      UFL_Prnt_n_Path ((name, typ, inner), print, path)
    end
  | helper (FUA_Prnt (func, args, print)) (path:path) =
    (*TODO: FIXME: Probably the rank of "fun" should be higher than those of "args" by one.*)
    let
      val arg_len = length  args                                : int;
      val arg_numbs = List.tabulate (arg_len, curry (op +) 1)   : ints;
      (*TODO: Should "arg_paths" be "map (fn numb => (path @ [0] @ [numb])) arg_numbs"?                                     *)
      (*      I think "func" is always atomic because of Isabelle's automatic beta-reduction and "trm_w_prnt_to_utrm_w_prnt"*)
      (*      In that case, "arg_numbs" should be "List.tabulate (arg_len, curry (op +) 0)   : ints;"                       *)
      (*      Probably I should not do this change:                                                                         *)
      (*      Function application ($) already made the corresponding path longer by one.                                   *)
      val arg_paths = map (fn numb => (path @ [numb])) arg_numbs: paths: paths;
      val func'     = helper func (path @ [0])                         : futrm_w_prnt_n_path;
      val args'     = map (uncurry helper) (args ~~ arg_paths)         : futrms_w_prnt_n_path;
    in
      UFA_Prnt_n_Path ((func', args'), print, path)
    end;

in

fun futrm_w_prnt_to_futrm_w_prnt_n_path t  = helper t []

end;

(** term as Table  **)
datatype node =
  NC of (string    * typ) (*Const*)
| NF of (string    * typ) (*Free*)
| NV of (indexname * typ) (*Var*)
| NB of (int       * typ) (*Bound*)
| NL of (string    * typ) (*Abs (Lambda Abstraction)*)
| NA                      (*$   (Application)*)

datatype node_typ = Node_Typ_NC | Node_Typ_NF | Node_Typ_NV | Node_Typ_NB | Node_Typ_NL | Node_Typ_NA;

fun is_NC (NC _) = true | is_NC _ = false;
fun is_NF (NF _) = true | is_NF _ = false;
fun is_NV (NV _) = true | is_NV _ = false;
fun is_NB (NB _) = true | is_NB _ = false;
fun is_NL (NL _) = true | is_NL _ = false;
fun is_NA (NA  ) = true | is_NA _ = false;

fun dest_NC (NC (name, typ)) = SOME (name, typ)
  | dest_NC  _               = NONE;
fun dest_NF (NF (name, typ)) = SOME (name, typ)
  | dest_NF  _               = NONE;
fun dest_NV (NV (name, typ)) = SOME (name, typ)
  | dest_NV  _               = NONE;
fun dest_NB (NB (int,  typ)) = SOME (int,  typ)
  | dest_NB  _               = NONE;
fun dest_NL (NL (name, typ)) = SOME (name, typ)
  | dest_NL  _               = NONE;

fun node_to_atoms_typ (NC (_, typ)) = SOME typ
  | node_to_atoms_typ (NF (_, typ)) = SOME typ
  | node_to_atoms_typ (NV (_, typ)) = SOME typ
  | node_to_atoms_typ (NB (_, typ)) = SOME typ
  | node_to_atoms_typ  _            = NONE

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
  {node : node,
   print: print,
   path : path};

(* unodes *)
type unodes = unode list;

(* futrm_w_prnt_n_path_to_unodes *)
fun futrm_w_prnt_n_path_to_unodes (UFC_Prnt_n_Path (ctnt, prnt, path)) = [{node = NC ctnt, print = prnt, path = path}]
  | futrm_w_prnt_n_path_to_unodes (UFF_Prnt_n_Path (ctnt, prnt, path)) = [{node = NF ctnt, print = prnt, path = path}]
  | futrm_w_prnt_n_path_to_unodes (UFV_Prnt_n_Path (ctnt, prnt, path)) = [{node = NV ctnt, print = prnt, path = path}]
  | futrm_w_prnt_n_path_to_unodes (UFB_Prnt_n_Path (ctnt, prnt, path)) = [{node = NB ctnt, print = prnt, path = path}]
  | futrm_w_prnt_n_path_to_unodes (UFL_Prnt_n_Path ((name, typ, trm), prnt, path)) =
      {node = NL (name, typ), print = prnt, path = path} :: futrm_w_prnt_n_path_to_unodes trm
  | futrm_w_prnt_n_path_to_unodes (UFA_Prnt_n_Path ((func, args), prnt, path)) =
    {node = NA, print = prnt, path = path} ::
    futrm_w_prnt_n_path_to_unodes func @ maps futrm_w_prnt_n_path_to_unodes args;

fun node_to_const_name (NC (cname, _)) = SOME (cname:string)
  | node_to_const_name  _              = NONE;

fun pst_n_node_to_rcsv  (pst:Proof.state) (node:node) =
  let
    val ctxt             = Proof.context_of pst                                                      : Proof.context;
    val cname_option     = dest_NC node <$> fst                                                      : string option;
    val recursive_option = cname_option <$> Pattern.has_recursive_simp_or_psimp_about_const_name ctxt: bool option;
  in recursive_option end;

fun pst_n_node_to_pttrn (pst:Proof.state) (node:node) =
  node_to_const_name node <$>
  Pattern.ctxt_n_cname_to_pattern_of_a_const (Proof.context_of pst);

fun pst_n_node_to_cmmnd (pst:Proof.state) (node:node) =
  let
    val ctxt           = Proof.context_of pst                     : Proof.context;
    val cname_option   = node_to_const_name node                  : string option;
    val command_otpion = cname_option <$> Pattern.get_command ctxt: Pattern.command option;
  in
    command_otpion
  end;

(* unode_w_aux *)
type unode_w_aux =
 {node : node,
  print: print,
  path : path,
  rcsv : bool option,
  pttrn: Pattern.pattern_of_a_const option,
  cmmnd: Pattern.command option};

(* unode_to_unode_w_aux: TODO *)
fun unode_n_pst_to_unode_w_aux ({node, print, path}:unode) (pst:Proof.state) =
 {node = node                        :node,
  print= print                       :print,
  path = path                        :path,
  rcsv = pst_n_node_to_rcsv  pst node:bool option,
  pttrn= pst_n_node_to_pttrn pst node:Pattern.pattern_of_a_const option,
  cmmnd= pst_n_node_to_cmmnd pst node:Pattern.command option};

end;