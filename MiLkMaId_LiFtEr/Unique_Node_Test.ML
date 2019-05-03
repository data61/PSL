(*  Title:      PSL/MiLkMaId_LiFtEr/Unique_Node_Test.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The conversion to transform term to a format more amenable to LiFtEr.
The overall work-flow is:
  term                   ==== trm_to_trm_w_prnt ============================>              (* in Unique_Node *)
  trm_w_prnt             ==== trm_w_prnt_to_utrm_w_prnt ====================>              (* in Unique_Node *)
  utrm_w_prnt            ==== utrm_w_prnt_to_futrm_w_prnt ==================>              (* in Unique_Node *)
  futrm_w_prnt           ==== futrm_w_prnt_to_futrm_w_prnt_n_path ==========>              (* in Unique_Node *)
  futrm_w_prnt_n_path    ==== futrm_w_prnt_n_path_to_unique_nodes ==========>              (* in Unique_Node *)
  unique_nodes           ==== unique_nodes_to_unode_table ==================>              (* in Term_Table  *)
  unode_table            ==== unode_table_to_unode_aux_table ===============>              (* in Term_Table  *)
   (unique_node_wo_path    ==== unique_node_wo_path_to_unique_node_w_aux =====> unique_node_w_aux      (* in Unique_Node *))
  unode_aux_table        ==== unode_aux_table_to_unode_aux_n_path_table ====>              (* in Term_Table  *)
   (unode_aux_table        ==== unode_aux_table_to_print_paths_table =========> paths_table            (* in Term_Table  *)
    unode_aux_table        ==== unode_aux_table_to_unode_aux_n_path_table ===>  unode_aux_n_path_table (* in Term_Table  *))
  unode_aux_n_path_table

  Proof.state * term     ==== pst_n_trm_to_unode_aux_n_path_table ==========> unode_aux_n_path_table  (* in Term_Table *)
  Proof.state            ==== pst_to_pst_to_abs_pstate_w_aux ===============> pst_to_abs_pstate_w_aux (* in Term_Table *)
*)

(*** Unique_Node ***)
structure Unique_Node_Test (*:UNIQUE_NODE*) =
struct

open Unique_Node;
open LiFtEr_Util;
open Test_LiFtEr;

(** test: trm_to_trm_w_prnt **)

fun trm_w_prnt_to_prnt (C_Prnt (_, _,     print)) = print
  | trm_w_prnt_to_prnt (F_Prnt (_, _,     print)) = print
  | trm_w_prnt_to_prnt (V_Prnt (_, _,     print)) = print
  | trm_w_prnt_to_prnt (B_Prnt (_, _,     print)) = print
  | trm_w_prnt_to_prnt (L_Prnt (_, _ , _, print)) = print
  | trm_w_prnt_to_prnt (A_Prnt (_, _ ,    print)) = print;

val _ = @{assert} ("s (\<lambda>x. f x y)" = (@{term "s (\<lambda>x. f x y)"} |> trm_to_trm_w_prnt @{context} |> trm_w_prnt_to_prnt |> dest_print));

(** test trm_w_prnt_to_utrm_w_prnt **)
(*Function application associates to the right.*)
local
  val f_x_y_1 = (Free ("f", dummyT) $  Free ("x", dummyT)) $ Free ("y", dummyT): term;
  val f_x_y_2 =  Free ("f", dummyT) $  Free ("x", dummyT)  $ Free ("y", dummyT): term;
  val f_x_y_3 =  Free ("f", dummyT) $ (Free ("x", dummyT)  $ Free ("y", dummyT)): term;
in
  val _ = @{assert} (f_x_y_1 = f_x_y_2);
  val _ = @{assert} (not (f_x_y_1 = f_x_y_3));
end;

local
(*
 *     $         $
 *    / \       / \
 *   $   y     f [x,y]
 *  / \    ==>
 * f   x
 *)
val p_foo     = F_Prnt ("foo",   dummyT, Print "print_foo");
val p_x       = F_Prnt ("x",     dummyT, Print "print_x");
val p_y       = F_Prnt ("y",     dummyT, Print "print_y");
val p_foo_x   = A_Prnt (p_foo,   p_x,    Print "print_foo_x");
val p_foo_x_y = A_Prnt (p_foo_x, p_y,    Print "print_foo_x_y");

val up_foo     = UF_Prnt ("foo",  dummyT,       Print "print_foo");
val up_x       = UF_Prnt ("x",    dummyT,       Print "print_x");
val up_y       = UF_Prnt ("y",    dummyT,       Print "print_y");
val up_foo_x_y = UA_Prnt (up_foo, [up_x, up_y], Print "print_foo_x_y");
in
  val _ = @{assert} (trm_w_prnt_to_utrm_w_prnt p_foo_x_y = up_foo_x_y);
end;

local
(*
 *       $            $
 *      / \          / \
 *     $   z        f  |
 *    / \     ==>   [$,  z]
 *   f   $          / \
 *      / \        x  |
 *     x   y         [y]
 *)
val p_foo       = F_Prnt ("foo",     dummyT, Print "print_foo");
val p_x         = F_Prnt ("x",       dummyT, Print "print_x");
val p_y         = F_Prnt ("y",       dummyT, Print "print_y");
val p_z         = F_Prnt ("z",       dummyT, Print "print_z");
val p_x_y       = A_Prnt (p_x,       p_y,    Print "print_x_y");
val p_foo_x_y   = A_Prnt (p_foo,     p_x_y,  Print "print_foo_x_y");
val p_foo_x_y_z = A_Prnt (p_foo_x_y, p_z,    Print "print_foo_x_y_z");

val up_foo       = UF_Prnt ("foo",  dummyT,         Print "print_foo");
val up_x         = UF_Prnt ("x",    dummyT,         Print "print_x");
val up_y         = UF_Prnt ("y",    dummyT,         Print "print_y");
val up_z         = UF_Prnt ("z",    dummyT,         Print "print_z");
val up_x_y       = UA_Prnt (up_x,   [up_y],         Print "print_x_y");
val up_foo_x_y_z = UA_Prnt (up_foo, [up_x_y, up_z], Print "print_foo_x_y_z");
in
  val _ = @{assert} (trm_w_prnt_to_utrm_w_prnt p_foo_x_y_z = up_foo_x_y_z)
end;

end;